/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A5Header.h"

using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // Worklist to hold nodes that need processing
    WorkList<SVF::NodeID> worklist;

    // 1. Initialize (Address Rule)
    // Iterate over all nodes in the constraint graph to find Address edges.
    // Rule: o -Address-> p  =>  pts(p) = {o}
    for (auto const& nodeIt : *consg)
    {
        SVF::ConstraintNode* node = nodeIt.second;
        // In SVF, an Addr edge goes from the Object (src) to the Pointer (dst).
        for (SVF::ConstraintEdge* edge : node->getDirectOutEdges())
        {
            if (edge->isAddr())
            {
                SVF::NodeID p = edge->getDstID(); // The pointer
                SVF::NodeID o = edge->getSrcID(); // The object address
                
                // Add o to pts(p) and push p to worklist if changed
                if (pts[p].insert(o).second)
                {
                    worklist.push(p);
                }
            }
        }
    }

    // 2. Solver Loop
    while (!worklist.empty())
    {
        SVF::NodeID p = worklist.pop();
        SVF::ConstraintNode* node = consg->getConstraintNode(p);

        // Optimization: Get the points-to set reference
        const auto& p_pts = pts[p];

        // --- Store and Load Rules (depend on o in pts(p)) ---
        for (SVF::NodeID o : p_pts)
        {
            // Store Rule: q -Store-> p  =>  q -Copy-> o
            // In SVF, Store edge direction is Value(q) -> Pointer(p)
            for (SVF::ConstraintEdge* edge : node->getDirectInEdges())
            {
                if (edge->isStore())
                {
                    SVF::NodeID q = edge->getSrcID();
                    // Add Copy edge: q -> o
                    // addConstraintEdge returns true if the edge did not exist and was added
                    if (consg->addConstraintEdge(q, o, SVF::ConstraintEdge::Copy))
                    {
                        worklist.push(q); // Push q to propagate its points-to set along the new edge
                    }
                }
            }

            // Load Rule: p -Load-> r  =>  o -Copy-> r
            // In SVF, Load edge direction is Pointer(p) -> Value(r)
            for (SVF::ConstraintEdge* edge : node->getDirectOutEdges())
            {
                if (edge->isLoad())
                {
                    SVF::NodeID r = edge->getDstID();
                    // Add Copy edge: o -> r
                    if (consg->addConstraintEdge(o, r, SVF::ConstraintEdge::Copy))
                    {
                        worklist.push(o); // Push o to propagate its points-to set along the new edge
                    }
                }
            }
        }

        // --- Copy and GEP Rules (outgoing edges from p) ---
        for (SVF::ConstraintEdge* edge : node->getDirectOutEdges())
        {
            // Copy Rule: p -Copy-> x  =>  pts(x) U= pts(p)
            if (edge->isCopy())
            {
                SVF::NodeID x = edge->getDstID();
                bool changed = false;
                for (SVF::NodeID o : p_pts)
                {
                    if (pts[x].insert(o).second)
                        changed = true;
                }
                if (changed)
                    worklist.push(x);
            }
            // Gep Rule: p -Gep-> x  =>  pts(x) U= { o + offset | o in pts(p) }
            else if (edge->isGep())
            {
                SVF::NodeID x = edge->getDstID();
                // Dynamically cast to GepCGEdge to access the offset/field index
                if (auto gepEdge = llvm::dyn_cast<SVF::GepCGEdge>(edge))
                {
                    u32_t offset = gepEdge->getConstantFieldIdx();
                    bool changed = false;
                    for (SVF::NodeID o : p_pts)
                    {
                        // In SVF PAG, field nodes are typically indexed relative to the base object
                        if (pts[x].insert(o + offset).second)
                            changed = true;
                    }
                    if (changed)
                        worklist.push(x);
                }
            }
        }
    }
}
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
    // consg->dump(); // Removed to prevent linker error

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

    // -------------------------------------------------------
    // 1. Initialize WorkList (Address Rule)
    // -------------------------------------------------------
    // Rule: o -Address-> p  =>  pts(p) = pts(p) U {o}
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        SVF::ConstraintNode* node = it->second;
        for (auto edge : node->getOutEdges())
        {
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Addr)
            {
                SVF::NodeID o = edge->getSrcID();
                SVF::NodeID p = edge->getDstID();
                if (pts[p].insert(o).second)
                    worklist.push(p);
            }
        }
    }

    // -------------------------------------------------------
    // 2. Main Worklist Loop
    // -------------------------------------------------------
    while (!worklist.empty())
    {
        SVF::NodeID p = worklist.pop();
        SVF::ConstraintNode* pNode = consg->getConstraintNode(p);

        // Iterate over all objects 'o' that 'p' points to
        for (SVF::NodeID o : pts[p])
        {
            // ---------------------
            // Store Rule
            // ---------------------
            // q -Store-> p  =>  q -Copy-> o
            for (auto edge : pNode->getInEdges())
            {
                if (edge->getEdgeKind() == SVF::ConstraintEdge::Store)
                {
                    SVF::NodeID q = edge->getSrcID();
                    if (consg->addCopyCGEdge(q, o))
                        worklist.push(q);
                }
            }

            // ---------------------
            // Load Rule
            // ---------------------
            // p -Load-> r  =>  o -Copy-> r
            for (auto edge : pNode->getOutEdges())
            {
                if (edge->getEdgeKind() == SVF::ConstraintEdge::Load)
                {
                    SVF::NodeID r = edge->getDstID();
                    if (consg->addCopyCGEdge(o, r))
                        worklist.push(o);
                }
            }

            // ---------------------
            // Gep Rule
            // ---------------------
            // p -Gep-> x
            for (auto edge : pNode->getOutEdges())
            {
                // Case 1: Constant Offset (NormalGep)
                // pts(x) = pts(x) U {o + offset}
                if (edge->getEdgeKind() == SVF::ConstraintEdge::NormalGep)
                {
                    if (auto gepEdge = llvm::dyn_cast<SVF::NormalGepCGEdge>(edge))
                    {
                        SVF::NodeID x = edge->getDstID();
                        SVF::NodeID field = o + gepEdge->getConstantFieldIdx();
                        if (pts[x].insert(field).second)
                            worklist.push(x);
                    }
                }
                // Case 2: Variable Index (VariantGep)
                // pts(x) = pts(x) U {o}  (Array insensitive: points to base)
                else if (edge->getEdgeKind() == SVF::ConstraintEdge::VariantGep)
                {
                    if (auto gepEdge = llvm::dyn_cast<SVF::VariantGepCGEdge>(edge))
                    {
                        SVF::NodeID x = edge->getDstID();
                        if (pts[x].insert(o).second)
                            worklist.push(x);
                    }
                }
            }
        }

        // ---------------------
        // Copy Rule
        // ---------------------
        // p -Copy-> x  =>  pts(x) = pts(x) U pts(p)
        for (auto edge : pNode->getOutEdges())
        {
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Copy)
            {
                SVF::NodeID x = edge->getDstID();
                bool changed = false;
                for (SVF::NodeID o : pts[p])
                {
                    if (pts[x].insert(o).second)
                        changed = true;
                }
                if (changed)
                    worklist.push(x);
            }
        }
    }
}
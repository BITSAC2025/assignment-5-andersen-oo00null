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
    WorkList<SVF::NodeID> worklist;

    // -------------------------------------------------------
    // 1. Initialize WorkList (Processing Address Edges)
    // -------------------------------------------------------
    // Rule: o -Address-> p  =>  pts(p) = pts(p) U {o}
    for (auto const& iter : *consg)
    {
        SVF::ConstraintNode* node = iter.second;
        for (auto edge : node->getOutEdges())
        {
            // Fix: Check directly to avoid type mismatch error
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Addr)
            {
                SVF::NodeID o = edge->getSrcID();
                SVF::NodeID p = edge->getDstID();
                if (pts[p].insert(o).second)
                {
                    worklist.push(p);
                }
            }
        }
    }

    // -------------------------------------------------------
    // 2. Main Solver Loop
    // -------------------------------------------------------
    while (!worklist.empty())
    {
        SVF::NodeID p = worklist.pop();
        SVF::ConstraintNode* pNode = consg->getConstraintNode(p);
        auto& pts_p = pts[p];

        // ---------------------
        // Handle Store Edges (Incoming)
        // ---------------------
        // q -Store-> p  =>  q -Copy-> o
        for (auto edge : pNode->getInEdges())
        {
            if (edge->getEdgeKind() == SVF::ConstraintEdge::Store)
            {
                SVF::NodeID q = edge->getSrcID();
                for (SVF::NodeID o : pts_p)
                {
                    if (consg->addCopyCGEdge(q, o))
                        worklist.push(q);
                }
            }
        }

        // ---------------------
        // Handle Outgoing Edges (Copy, Load, Gep)
        // ---------------------
        for (auto edge : pNode->getOutEdges())
        {
            // Fix: Use 'auto' to let compiler deduce 'long long int' type safely
            auto edgeKind = edge->getEdgeKind();

            // Copy Rule: p -Copy-> x
            if (edgeKind == SVF::ConstraintEdge::Copy)
            {
                SVF::NodeID x = edge->getDstID();
                auto& pts_x = pts[x];
                
                size_t oldSize = pts_x.size();
                pts_x.insert(pts_p.begin(), pts_p.end());

                if (pts_x.size() != oldSize)
                    worklist.push(x);
            }
            // Load Rule: p -Load-> r
            else if (edgeKind == SVF::ConstraintEdge::Load)
            {
                SVF::NodeID r = edge->getDstID();
                for (SVF::NodeID o : pts_p)
                {
                    if (consg->addCopyCGEdge(o, r))
                        worklist.push(o);
                }
            }
            // Gep Rule: p -Gep-> x
            else if (edgeKind == SVF::ConstraintEdge::NormalGep || 
                     edgeKind == SVF::ConstraintEdge::VariantGep)
            {
                // Dyn_cast works because NormalGepCGEdge and VariantGepCGEdge 
                // both inherit from GepCGEdge
                if (auto gepEdge = llvm::dyn_cast<SVF::GepCGEdge>(edge))
                {
                    SVF::NodeID x = edge->getDstID();
                    auto& pts_x = pts[x];
                    size_t oldSize = pts_x.size();

                    for (SVF::NodeID o : pts_p)
                    {
                        // Helper handles both constant offsets and variable indices
                        SVF::NodeID fieldObj = consg->getGepObjVar(o, gepEdge);
                        pts_x.insert(fieldObj);
                    }

                    if (pts_x.size() != oldSize)
                        worklist.push(x);
                }
            }
        }
    }
}
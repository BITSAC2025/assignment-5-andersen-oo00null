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
    (void)consg;

    Andersen andersen(consg);

    // TODO: complete the following method
    andersen.runPointerAnalysis();

    andersen.dumpResult();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


/ Implementation of the Andersen's Inclusion-based Pointer Analysis
void Andersen::runPointerAnalysis()
{
    auto pag = SVF::PAG::getPAG();

    // ===========================================================
    // Phase 1: Addr (y = &x) - Initial Constraints
    // Rule: {x} subset of pts(y)
    // ===========================================================
    for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Addr))
    {
        unsigned address = edge->getSrcID(); // x (Address node ID/Allocation site)
        unsigned pointer = edge->getDstID(); // y (Pointer variable ID)
        
        // Add x to y's points-to set: pts[y] <- pts[y] U {x}
        pts[pointer].insert(address); 
    }

    // ===========================================================
    // Phase 2: Fixed-point Iteration (Iteratively Propagate Constraints)
    // ===========================================================
    bool changed = true;
    while (changed)
    {
        changed = false;

        // --- Group 1: Simple Subset Propagation (pts(src) subset of pts(dst)) ---
        // Applies to: Copy (y=x), Gep (y=&x->f), Call (param passing), Ret (return value), 
        //             ThreadFork, ThreadJoin.
        
        // 定义所有遵循简单子集规则的边类型
        const std::vector<SVF::PAGEdge::PAGEdgeType> simpleSubsetTypes = {
            SVF::PAGEdge::Copy,
            SVF::PAGEdge::Gep,
            SVF::PAGEdge::Call,
            SVF::PAGEdge::Ret,
            SVF::PAGEdge::ThreadFork,
            SVF::PAGEdge::ThreadJoin
        };
        
        for (SVF::PAGEdge::PAGEdgeType type : simpleSubsetTypes)
        {
            for (SVF::PAGEdge *edge : pag->getSVFStmtSet(type))
            {
                unsigned src = edge->getSrcID();
                unsigned dst = edge->getDstID();
                
                // pts[dst] <- pts[dst] U pts[src]
                for (auto p : pts[src])
                {
                    if (pts[dst].insert(p).second)
                        changed = true;
                }
            }
        }
        
        // --- Group 2: Control Flow Constraints (Phi/Select) ---
        // These are conceptually similar to Copy but require iterating over operands.

        // Phi (y = phi(x1, x2, ...)): operand -> result
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Phi))
        {
            const SVF::PhiStmt *phi = SVF::SVFUtil::cast<SVF::PhiStmt>(edge);
            unsigned res = phi->getResID(); 
            for (const auto opVar : phi->getOpndVars()) 
            {
                unsigned op = opVar->getId();
                // pts[res] <- pts[res] U pts[op]
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
        
        // Select (y = select(cond, x1, x2)): operand -> result
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Select))
        {
            const SVF::SelectStmt *sel = SVF::SVFUtil::cast<SVF::SelectStmt>(edge);
            unsigned res = sel->getResID(); 
            for (const auto opVar : sel->getOpndVars()) 
            {
                unsigned op = opVar->getId();
                // pts[res] <- pts[res] U pts[op]
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }


        // --- Group 3: Indirect Memory Access Rules (The Core Propagation) ---

        // Load (y = *x)
        // Rule: If a in pts(x), then pts(a) subset of pts(y)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Load))
        {
            unsigned x = edge->getSrcID(); // x: pointer (operand)
            unsigned y = edge->getDstID(); // y: variable receiving the value (*x)

            for (auto a : pts[x]) // 'a' is an address node ID (target of x)
            {
                // Propagate the points-to set of the memory location 'a' to the variable 'y'
                for (auto v : pts[a]) // 'v' is an address pointed to by 'a'
                {
                    if (pts[y].insert(v).second) 
                        changed = true;
                }
            }
        }

        // Store (*x = y)
        // Rule: If a in pts(x), then pts(y) subset of pts(a)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Store))
        {
            unsigned y = edge->getSrcID(); // y: value (operand)
            unsigned x = edge->getDstID(); // x: pointer to memory location (operand)

            for (auto a : pts[x]) // 'a' is an address node ID (target of x)
            {
                // Propagate the points-to set of 'y' to the memory location 'a'
                for (auto v : pts[y]) // 'v' is an address pointed to by 'y'
                {
                    if (pts[a].insert(v).second) 
                        changed = true;
                }
            }
        }
    } // End while (changed)
}
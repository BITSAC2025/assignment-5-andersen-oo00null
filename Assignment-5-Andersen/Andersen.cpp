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


// Implementation of the Andersen's Inclusion-based Pointer Analysis
void Andersen::runPointerAnalysis()
{
    auto pag = SVF::PAG::getPAG();

    // -----------------------------------------------------------
    // Phase 1: Initialize Points-to Sets (Initial Constraints)
    // -----------------------------------------------------------
    
    // Principle: Handle the Address-of (&) Operator (y = &x).
    // This is the fundamental source of all address information. The pointer 'y' 
    // receives the *address* of memory location 'x'. This creates a hard constraint.
    // Constraint: {x} subset of pts(y)
    // Implementation: Directly insert the address node ID (x) into the points-to set of the pointer variable node ID (y).
    for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Addr))
    {
        // Addr edge: SrcID is the Address node (x), DstID is the Pointer variable (y).
        unsigned address = edge->getSrcID(); // x (memory location/allocation site)
        unsigned pointer = edge->getDstID(); // y (pointer variable)
        
        // pts[y] <- pts[y] U {x}
        pts[pointer].insert(address); 
    }

    // -----------------------------------------------------------
    // Phase 2: Iteratively Propagate Constraints (Fixed-Point Iteration)
    // -----------------------------------------------------------
    bool changed = true;
    while (changed)
    {
        changed = false;

        // --- Group 1: Simple Subset Constraints (Strong Copies: pts[src] subset of pts[dst]) ---
        // Principle: If pointer y gets its value directly from pointer x, then y must
        // point to everything x points to. This applies to simple assignments,
        // control flow merges, type casts, address arithmetic, and parameter passing.
        
        
        // 1. Copy (and implicitly Cast/CopyAddr): y = x or y = (Type)x
        // Note: The problematic 'Cast' and 'CopyAddr' edge types are typically 
        // covered by the generic 'Copy' edge in simplified SVF PAG generation for 
        // field-insensitive analysis. We rely on 'Copy' to handle these simple 
        // pointer value movements.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Copy))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        
        // 2. Gep: y = GetElementPtr(x, ...) (Address of Array/Struct Element)
        // Principle: In Field-Insensitive Andersen, address arithmetic (Gep) results in simple 
        // subset propagation, as we ignore the specific field/offset.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Gep))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }

        // 3. Interprocedural Flow (Call/Ret)
        // Principle: Parameter passing (Call) and return value handling (Ret) are forms 
        // of simple value flow, leading to subset constraints.
        // Call: actual parameter (src) -> formal parameter (dst)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Call))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        // Ret: return value (src) -> result variable (dst)
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Ret))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        
        // 4. Control Flow (Phi/Select)
        // Principle: At control flow join points (Phi) or conditional assignments (Select), 
        // the result pointer must point to the union of all possible input pointers.
        // Phi: operand (src) -> result (dst) at control flow join points.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Phi))
        {
            const SVF::PhiStmt *phi = SVF::SVFUtil::cast<SVF::PhiStmt>(edge);
            unsigned res = phi->getResID(); 
            for (const auto opVar : phi->getOpndVars()) 
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }
        // Select: operand (src) -> result (dst) at conditional merge.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Select))
        {
            const SVF::SelectStmt *sel = SVF::SVFUtil::cast<SVF::SelectStmt>(edge);
            unsigned res = sel->getResID(); 
            for (const auto opVar : sel->getOpndVars()) 
            {
                unsigned op = opVar->getId();
                for (auto p : pts[op])
                {
                    if (pts[res].insert(p).second)
                        changed = true;
                }
            }
        }

        // 5. Threading (ThreadFork/Join)
        // Principle: Flow of pointers between threads (e.g., passing variables to a new thread)
        // also represents a simple subset constraint.
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::ThreadFork))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
            }
        }
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::ThreadJoin))
        {
            unsigned src = edge->getSrcID();
            unsigned dst = edge->getDstID();
            for (auto p : pts[src])
            {
                if (pts[dst].insert(p).second)
                    changed = true;
                }
            }


        // --- Group 2: Indirect Memory Access Rules (The Core Propagation) ---

        // 6. Load: y = *x
        // Principle: The value stored at the memory locations pointed to by 'x' flows into 'y'.
        // Constraint: If a in pts(x), then pts(a) subset of pts(y).
        // Implementation: Iterate over pts(x). For each address 'a', propagate pts(a) to pts(y).
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Load))
        {
            unsigned x = edge->getSrcID(); // x: pointer (operand)
            unsigned y = edge->getDstID(); // y: variable receiving the value (*x)

            for (auto a : pts[x]) // 'a' is an address node ID
            {
                for (auto v : pts[a]) // 'v' is an address pointed to by 'a'
                {
                    if (pts[y].insert(v).second) 
                        changed = true;
                }
            }
        }

        // 7. Store: *x = y
        // Principle: The value of 'y' flows into the memory locations pointed to by 'x'.
        // Constraint: If a in pts(x), then pts(y) subset of pts(a).
        // Implementation: Iterate over pts(x). For each address 'a', propagate pts(y) to pts(a).
        for (SVF::PAGEdge *edge : pag->getSVFStmtSet(SVF::PAGEdge::Store))
        {
            unsigned y = edge->getSrcID(); // y: value (operand)
            unsigned x = edge->getDstID(); // x: pointer to memory location (operand)

            for (auto a : pts[x]) // 'a' is an address node ID
            {
                for (auto v : pts[y]) // 'v' is an address pointed to by 'y'
                {
                    if (pts[a].insert(v).second) 
                        changed = true;
                }
            }
        }
    } // End while (changed)
}
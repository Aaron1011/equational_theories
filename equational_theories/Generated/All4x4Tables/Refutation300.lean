
import equational_theories.Equations.All
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang

/-!
This file is generated from the following operator table:
[[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]
-/

set_option linter.unusedVariables false

/-! The magma definition -/
def «FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]» : Magma (Fin 4) where
  op := memoFinOp fun x y => [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]][x.val]![y.val]!

/-! The facts -/
@[equational_result]
theorem «Facts from FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]» :
  ∃ (G : Type) (_ : Magma G), Facts G [1445] [151, 1427, 1428, 1429, 1435, 1442, 1444, 1629] :=
    ⟨Fin 4, «FinitePoly [[2,3,1,1],[3,0,0,0],[0,0,0,0],[1,3,0,0]]», by decideFin!⟩

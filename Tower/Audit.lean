import Tower.TangentLine.ModP
import Tower.TangentLine.NonTorsion

/-!
# Axiom audit

`#print axioms` for the headline theorems.  The build log shows, for each, the axioms its proof
depends on.  The standard for this repository is that only `propext`, `Classical.choice` and
`Quot.sound` appear (no `sorryAx`, no `Lean.ofReduceBool`).
-/

#print axioms Tower.TangentLine.elimination
#print axioms Tower.TangentLine.res_factor
#print axioms Tower.TangentLine.tangent_through_node
#print axioms Tower.TangentLine.Q4_roots_103
#print axioms Tower.TangentLine.four_mul_sq_of_link
#print axioms Tower.TangentLine.equation_of_link
#print axioms Tower.TangentLine.dQ4_eq_zero
#print axioms Tower.TangentLine.P103.Q4_roots
#print axioms Tower.TangentLine.P373.Q4_roots
#print axioms Tower.TangentLine.P499.Q4_roots
#print axioms Tower.TangentLine.P103.P1_addOrderOf
#print axioms Tower.TangentLine.P103.P2_addOrderOf
#print axioms Tower.TangentLine.P103.P3_addOrderOf
#print axioms Tower.TangentLine.P103.P4_addOrderOf
#print axioms Tower.TangentLine.P373.P1_addOrderOf
#print axioms Tower.TangentLine.P373.P2_addOrderOf
#print axioms Tower.TangentLine.P373.P3_addOrderOf
#print axioms Tower.TangentLine.P373.P4_addOrderOf
#print axioms Tower.TangentLine.P499.P1_addOrderOf
#print axioms Tower.TangentLine.P499.P2_addOrderOf
#print axioms Tower.TangentLine.P499.P3_addOrderOf
#print axioms Tower.TangentLine.P499.P4_addOrderOf
#print axioms Tower.EC.addOrderOf_eq_zero_of_two_reductions
#print axioms Tower.TangentLine.P103.red_eq
#print axioms Tower.TangentLine.P103.red_sub_order
#print axioms Tower.TangentLine.P499.red_sub_order
#print axioms Tower.TangentLine.addOrderOf_eq_zero_of_reductions
#print axioms Tower.TangentLine.sub_addOrderOf_eq_zero_of_reductions

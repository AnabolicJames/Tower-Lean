import Tower.TangentLine.ModP
import Tower.TangentLine.NonTorsion
import Tower.RV6.Ladder
import Tower.RV6.BesselAlgebra
import Tower.RV6.Swap
import Tower.RV6.Lambert
import Tower.RV6.Ladder2
import Tower.RV6.EisAxis
import Tower.RV6.QSeries
import Tower.RV6.Regroup
import Tower.RV6.Arith
import Tower.RV6.Dirichlet
import Tower.RV6.Fricke6

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
#print axioms Tower.RV6.rungA_of
#print axioms Tower.RV6.rungC_of
#print axioms Tower.RV6.mu6_eq_Lambda5
#print axioms Tower.RV6.rv6_of_rungs
#print axioms Tower.RV6.sixteen_mul_pow_six
#print axioms Tower.RV6.hasDerivAt_pow_mul_pow_of_wronskian
#print axioms Tower.RV6.Phi_scale
#print axioms Tower.RV6.Phi_swap
#print axioms Tower.RV6.summable_Ecal_terms
#print axioms Tower.RV6.summable_DEcal_terms
#print axioms Tower.RV6.integral_qseries
#print axioms Tower.RV6.lambdaPsi5_eq
#print axioms Tower.RV6.rv6_psi_of_rungs
#print axioms Tower.RV6.rv6_of_rungs'
#print axioms Tower.RV6.E4im_inv
#print axioms Tower.RV6.E2im_inv
#print axioms Tower.RV6.qa_dilate
#print axioms Tower.RV6.qa_comb4
#print axioms Tower.RV6.qa_mul
#print axioms Tower.RV6.integral_qa
#print axioms Tower.RV6.tsum_prod_eq_tsum_divisorsAntidiagonal
#print axioms Tower.RV6.conv_sig_identity
#print axioms Tower.RV6.tsum_sig3_div_pow5
#print axioms Tower.RV6.tsum_sig1_div_pow5
#print axioms Tower.RV6.g4E_fricke
#print axioms Tower.RV6.Gcal_fricke

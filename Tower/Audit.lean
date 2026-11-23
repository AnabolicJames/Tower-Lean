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
import Tower.RV6.PhiKernel
import Tower.RV6.Interchange
import Tower.RV6.Eichler
import Tower.RV6.Bilin
import Tower.RV6.Eichler2
import Tower.RV6.C4
import Tower.RV6.RungC1
import Tower.RV6.QCalc
import Tower.RV6.DEInv
import Tower.RV6.PsiW
import Tower.RV6.RungC2
import Tower.RV6.Ladder3
import Tower.RV6.Ser
import Tower.RV6.Level6
import Tower.RV6.Ramanujan
import Tower.RV6.EtaRec
import Tower.RV6.BesselI
import Tower.RV6.BesselK
import Tower.RV6.BesselW
import Tower.RV6.BesselR
import Tower.RV6.BesselJ
import Tower.RV6.Laplace
import Tower.RV6.LogInt
import Tower.RV6.BesselInt
import Tower.RV6.CharFun
import Tower.RV6.CubeLog
import Tower.RV6.RungA1
import Tower.RV6.KZero
import Tower.RV6.LadderA2
import Tower.RV6.TrigA2
import Tower.RV6.MellinU
import Tower.RV6.RungA2P
import Tower.RV6.PoleM
import Tower.RV6.RungA2M
import Tower.RV6.RungA2N
import Tower.RV6.CKernel
import Tower.RV6.CJSeries
import Tower.RV6.CKZero
import Tower.RV6.HAgree
import Tower.RV6.GPoly
import Tower.RV6.RotRect
import Tower.RV6.RotSides
import Tower.RV6.RungA2R
import Tower.RV6.LadderB
import Tower.RV6.AxisEv
import Tower.RV6.ModAxis
import Tower.RV6.QTail
import Tower.RV6.EtaForm
import Tower.RV6.FrickeAx
import Tower.RV6.XMod
import Tower.RV6.BMReduce
import Tower.RV6.BMBounds
import Tower.RV6.LimBM
import Tower.RV6.BesselL5
import Tower.RV6.HankelDom
import Tower.RV6.HankelDomF
import Tower.RV6.HankelIBP
import Tower.RV6.HankelRelF
import Tower.RV6.HankelDeriv
import Tower.RV6.HankelODEF

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
#print axioms Tower.RV6.PhiN_le
#print axioms Tower.RV6.PhiN_scale
#print axioms Tower.RV6.PhiN_pos
#print axioms Tower.RV6.integral_qa_mul
#print axioms Tower.RV6.integral_qa_mul_regroup
#print axioms Tower.RV6.swap_qa
#print axioms Tower.RV6.integrable_qa_mul
#print axioms Tower.RV6.interchange_three
#print axioms Tower.RV6.interchange_four
#print axioms Tower.RV6.integral_Ioi_exp_mul_id
#print axioms Tower.RV6.Tint_eq
#print axioms Tower.RV6.integral_inv_subst
#print axioms Tower.RV6.Tint_inv
#print axioms Tower.RV6.integral_bilin_gen
#print axioms Tower.RV6.A1E_direct
#print axioms Tower.RV6.A1E_fricke
#print axioms Tower.RV6.integral_sq_mul_Tint
#print axioms Tower.RV6.integral_Tint_fricke
#print axioms Tower.RV6.D01E_eq
#print axioms Tower.RV6.c4_eq
#print axioms Tower.RV6.g4_eq_g4E
#print axioms Tower.RV6.rungC1
#print axioms Tower.RV6.integrable_qa_pow
#print axioms Tower.RV6.hasDerivAt_qa
#print axioms Tower.RV6.qa_conv
#print axioms Tower.RV6.conv_poly_bound
#print axioms Tower.RV6.conv_mul_index
#print axioms Tower.RV6.DEq_inv
#print axioms Tower.RV6.DGcal_fricke
#print axioms Tower.RV6.fricke_subst
#print axioms Tower.RV6.integral_qa_scale
#print axioms Tower.RV6.Fcal_eq_qa
#print axioms Tower.RV6.DFcal_eq_qa
#print axioms Tower.RV6.M2F_eq
#print axioms Tower.RV6.L5F_eq
#print axioms Tower.RV6.M5F_eq
#print axioms Tower.RV6.lambdaPsiW5_eq
#print axioms Tower.RV6.lambdaPsiW5_split
#print axioms Tower.RV6.J2_eq_moments
#print axioms Tower.RV6.J1_eq_moments
#print axioms Tower.RV6.rungC2W
#print axioms Tower.RV6.D01_eq_modular
#print axioms Tower.RV6.rv6_psiW_of_bessel
#print axioms Tower.RV6.rv6_of_bessel_and_E
#print axioms Tower.RV6.theta_mul
#print axioms Tower.RV6.rel_all_zero
#print axioms Tower.RV6.thetaGam_scaled
#print axioms Tower.RV6.qa_coeff_unique
#print axioms Tower.RV6.D_axis
#print axioms Tower.RV6.E6_axis
#print axioms Tower.RV6.c2_zero
#print axioms Tower.RV6.c6_zero
#print axioms Tower.RV6.ram6
#print axioms Tower.RV6.Rf9_eq_zero
#print axioms Tower.RV6.theta_PsiS
#print axioms Tower.RV6.rec_psi
#print axioms Tower.RV6.theta_HN
#print axioms Tower.RV6.rec_HN
#print axioms Tower.RV6.rungEW
#print axioms Tower.RV6.rv6_of_bessel
#print axioms Tower.RV6.hasDerivAt_besselI0
#print axioms Tower.RV6.hasDerivAt_mul_besselI1
#print axioms Tower.RV6.hasDerivAt_besselK0
#print axioms Tower.RV6.hasDerivAt_mul_besselK1
#print axioms Tower.RV6.mul_besselK1_le_one
#print axioms Tower.RV6.exp_neg_le_mul_besselK1
#print axioms Tower.RV6.wronskian
#print axioms Tower.RV6.besselI0_le_cosh
#print axioms Tower.RV6.besselI1_le_sinh
#print axioms Tower.RV6.besselK0_pos
#print axioms Tower.RV6.besselK0_le_exp_mul_sqrt
#print axioms Tower.RV6.besselK0_le_one_add_log
#print axioms Tower.RV6.integrableOn_R62_integrand
#print axioms Tower.RV6.R62_pos
#print axioms Tower.RV6.hasDerivAt_besselJ0
#print axioms Tower.RV6.hasDerivAt_mul_besselJ1
#print axioms Tower.RV6.hasDerivAt_besselJ1
#print axioms Tower.RV6.besselJ_sq_le_one
#print axioms Tower.RV6.besselJ0_sq_le
#print axioms Tower.RV6.integrableOn_walk_integrand
#print axioms Tower.RV6.lapl_ibp
#print axioms Tower.RV6.hasDerivAt_lapl
#print axioms Tower.RV6.lapl_J_ode
#print axioms Tower.RV6.laplS_eq_one
#print axioms Tower.RV6.lapl_besselJ0
#print axioms Tower.RV6.hasDerivAt_logInt
#print axioms Tower.RV6.logInt_eq
#print axioms Tower.RV6.hasDerivAt_besG
#print axioms Tower.RV6.hasDerivAt_mul_besH
#print axioms Tower.RV6.bessel_system_zero
#print axioms Tower.RV6.besselJ0_eq_besG
#print axioms Tower.RV6.besselJ1_eq_besH
#print axioms Tower.RV6.besselJ0_mul_norm
#print axioms Tower.RV6.cube_restrict
#print axioms Tower.RV6.integral_cube_prod
#print axioms Tower.RV6.integral_cube_cos
#print axioms Tower.RV6.integral_cube_besselJ0
#print axioms Tower.RV6.integral_cube_logG
#print axioms Tower.RV6.integrable_of_antitone_of_tendsto
#print axioms Tower.RV6.tendsto_walk_damped
#print axioms Tower.RV6.ae_cubeX_ne_zero
#print axioms Tower.RV6.rungA1
#print axioms Tower.RV6.rv6_of_A2_B
#print axioms Tower.RV6.expE_sub_besselK0_le
#print axioms Tower.RV6.hasDerivAt_expE
#print axioms Tower.RV6.expE_add_log
#print axioms Tower.RV6.abs_besselK0_add_log_le
#print axioms Tower.RV6.expE_one
#print axioms Tower.RV6.subrung_identity
#print axioms Tower.RV6.rungA2_of_subrungs
#print axioms Tower.RV6.rv6_of_A2sub_B
#print axioms Tower.RV6.trigN_lower
#print axioms Tower.RV6.trigT_abs_le
#print axioms Tower.RV6.rungA2T
#print axioms Tower.RV6.rv6_of_A2RNMP_B
#print axioms Tower.RV6.integrable_mul_exp_of_bounds
#print axioms Tower.RV6.integrable_besselIK_exp
#print axioms Tower.RV6.integrable_besselIK_cube_exp
#print axioms Tower.RV6.integrable_besselP_exp
#print axioms Tower.RV6.integrable_besselJ0_pow_six_exp
#print axioms Tower.RV6.hasDerivAt_phi35
#print axioms Tower.RV6.mellM24_eq
#print axioms Tower.RV6.tendsto_mellP
#print axioms Tower.RV6.rungA2P
#print axioms Tower.RV6.rv6_of_A2RNM_B
#print axioms Tower.RV6.integral_pow_mul_exp_neg
#print axioms Tower.RV6.abs_besselIK_sub_pow_le
#print axioms Tower.RV6.besselIK_mul_exp_le_of_nonpos
#print axioms Tower.RV6.besselIK_le_inv_pow
#print axioms Tower.RV6.mellM_sub_pole_bounded
#print axioms Tower.RV6.rungA2M
#print axioms Tower.RV6.rv6_of_A2RN_B
#print axioms Tower.RV6.mellN_sub_inv_eq
#print axioms Tower.RV6.tendsto_integral_Iic_besselJ0
#print axioms Tower.RV6.tendsto_integral_Ioi_besselJ0
#print axioms Tower.RV6.integral_one_sub_exp_neg_exp_Iic
#print axioms Tower.RV6.walk_AB_eq
#print axioms Tower.RV6.rungA2N
#print axioms Tower.RV6.rv6_of_A2R_B
#print axioms Tower.RV6.hasDerivAt_integral_cexp_mul
#print axioms Tower.RV6.differentiable_kerA
#print axioms Tower.RV6.differentiable_cJ0
#print axioms Tower.RV6.norm_cJ0_le
#print axioms Tower.RV6.cJ0_eq_integral
#print axioms Tower.RV6.integral_sin_pow_even_half
#print axioms Tower.RV6.hasSum_integral_cos_mul_sin
#print axioms Tower.RV6.cJ0_eq_tsum
#print axioms Tower.RV6.cJ0_ofReal
#print axioms Tower.RV6.cJ0_I_mul
#print axioms Tower.RV6.differentiableAt_cK0
#print axioms Tower.RV6.norm_cK0_le
#print axioms Tower.RV6.cK0_ofReal
#print axioms Tower.RV6.differentiableAt_kerB
#print axioms Tower.RV6.differentiableAt_hE
#print axioms Tower.RV6.hE_ofReal_re
#print axioms Tower.RV6.differentiableAt_hK
#print axioms Tower.RV6.norm_hK_le
#print axioms Tower.RV6.hK_I_mul
#print axioms Tower.RV6.re_mul_sinh_side_le
#print axioms Tower.RV6.tendsto_side_integral
#print axioms Tower.RV6.rect_cexp_mul_sinh
#print axioms Tower.RV6.cK0_neg_I_mul_eq
#print axioms Tower.RV6.hE_eq_hK
#print axioms Tower.RV6.gpoly_ofReal_add
#print axioms Tower.RV6.gpoly_re
#print axioms Tower.RV6.gpoly_I_axis_mul
#print axioms Tower.RV6.gpoly_I_axis_mul_re
#print axioms Tower.RV6.norm_gpoly_le
#print axioms Tower.RV6.gpoly_bound_mono
#print axioms Tower.RV6.norm_ccos_le
#print axioms Tower.RV6.integral_cosh_mul_sin_eq
#print axioms Tower.RV6.norm_cJ0_le_besselI0
#print axioms Tower.RV6.norm_gpoly_cJ0_hK_le
#print axioms Tower.RV6.exists_besselIK_exp_le
#print axioms Tower.RV6.sidePhi_exp_le
#print axioms Tower.RV6.sidePhi_side_le
#print axioms Tower.RV6.re_add_mul_I
#print axioms Tower.RV6.im_add_mul_I
#print axioms Tower.RV6.cexp_add_mul_I_re
#print axioms Tower.RV6.cexp_add_mul_I_im
#print axioms Tower.RV6.differentiableAt_gpoly_mul
#print axioms Tower.RV6.differentiableAt_rotE
#print axioms Tower.RV6.differentiableAt_rotK
#print axioms Tower.RV6.rotE_eq_rotK
#print axioms Tower.RV6.rect_rotE
#print axioms Tower.RV6.rect_rotK
#print axioms Tower.RV6.rect_rot
#print axioms Tower.RV6.exists_norm_rotK_side_le
#print axioms Tower.RV6.norm_side_integral_le
#print axioms Tower.RV6.exists_norm_sideInt_le
#print axioms Tower.RV6.tendsto_zero_of_norm_le_exp
#print axioms Tower.RV6.tendsto_sideInt_atTop
#print axioms Tower.RV6.tendsto_sideInt_neg
#print axioms Tower.RV6.re_intervalIntegral
#print axioms Tower.RV6.continuous_comp_line
#print axioms Tower.RV6.continuous_rotE_bottom
#print axioms Tower.RV6.rotE_bottom_re
#print axioms Tower.RV6.continuous_rotK_top
#print axioms Tower.RV6.cexp_add_half_pi_mul_I
#print axioms Tower.RV6.cexp_mul_add_half_pi_mul_I
#print axioms Tower.RV6.rotK_top_re
#print axioms Tower.RV6.topRe_eq
#print axioms Tower.RV6.integrable_topRe
#print axioms Tower.RV6.integral_topRe
#print axioms Tower.RV6.rot_real_identity
#print axioms Tower.RV6.rungA2R
#print axioms Tower.RV6.rv6_of_B
#print axioms Tower.RV6.rungA2
#print axioms Tower.RV6.rungA
#print axioms Tower.RV6.mu6_eq_bessel
#print axioms Tower.RV6.rungB_of_PM
#print axioms Tower.RV6.rv6_of_PM
#print axioms Tower.RV6.evA_qform
#print axioms Tower.RV6.axis_Rf1
#print axioms Tower.RV6.axis_Rf2
#print axioms Tower.RV6.axis_Rf3
#print axioms Tower.RV6.axis_Rf4
#print axioms Tower.RV6.axis_Rf9
#print axioms Tower.RV6.Pax_sq
#print axioms Tower.RV6.hasDerivAt_Zax
#print axioms Tower.RV6.hasDerivAt_Uax
#print axioms Tower.RV6.hasDerivAt_Eax
#print axioms Tower.RV6.g4_eq_UP
#print axioms Tower.RV6.qa_abs_le_tail
#print axioms Tower.RV6.tendsto_qa_atTop
#print axioms Tower.RV6.tendsto_exp_mul_qa_atTop
#print axioms Tower.RV6.hasDerivAt_lgZ
#print axioms Tower.RV6.hasDerivAt_lgU
#print axioms Tower.RV6.tendsto_E2im_atTop
#print axioms Tower.RV6.tendsto_Zax_atTop
#print axioms Tower.RV6.tendsto_exp_mul_Uax_atTop
#print axioms Tower.RV6.Zax_eq_exp
#print axioms Tower.RV6.Uax_eq_exp
#print axioms Tower.RV6.Zax_pos
#print axioms Tower.RV6.Uax_pos
#print axioms Tower.RV6.Zax_fricke
#print axioms Tower.RV6.Uax_fricke
#print axioms Tower.RV6.Pax_fricke
#print axioms Tower.RV6.tendsto_Pax_atTop
#print axioms Tower.RV6.Pax_ne_zero
#print axioms Tower.RV6.Pax_pos
#print axioms Tower.RV6.xm_pos
#print axioms Tower.RV6.xm_sq
#print axioms Tower.RV6.log_xm
#print axioms Tower.RV6.hasDerivAt_xm
#print axioms Tower.RV6.xm_mul_fricke
#print axioms Tower.RV6.strictAntiOn_xm
#print axioms Tower.RV6.tendsto_exp_mul_xm
#print axioms Tower.RV6.tendsto_xm_atTop
#print axioms Tower.RV6.tendsto_xm_zero
#print axioms Tower.RV6.image_xm
#print axioms Tower.RV6.pairS_eq_JS
#print axioms Tower.RV6.integral_exp_div_pow_six
#print axioms Tower.RV6.pole_eq
#print axioms Tower.RV6.rungBM_of_zhou
#print axioms Tower.RV6.rv6_of_zhou
#print axioms Tower.RV6.qa_abs_le_tail_at
#print axioms Tower.RV6.abs_Wq_le
#print axioms Tower.RV6.log_xm_fricke
#print axioms Tower.RV6.inv_xm_le
#print axioms Tower.RV6.abs_g4_le
#print axioms Tower.RV6.abs_A1_le
#print axioms Tower.RV6.rpow_neg_le
#print axioms Tower.RV6.abs_expm1_le_mul
#print axioms Tower.RV6.pow_six_exp_le
#print axioms Tower.RV6.pole_part_le
#print axioms Tower.RV6.continuousAt_FS
#print axioms Tower.RV6.tendsto_FS
#print axioms Tower.RV6.FS_bound_Ioc
#print axioms Tower.RV6.FS_bound_Ioi
#print axioms Tower.RV6.integrableOn_f0
#print axioms Tower.RV6.tendsto_int_Ioc
#print axioms Tower.RV6.tendsto_int_Ioi1
#print axioms Tower.RV6.JS_sub_poleS
#print axioms Tower.RV6.D01_split
#print axioms Tower.RV6.limBM
#print axioms Tower.RV6.rungBM_of_zhou2
#print axioms Tower.RV6.rv6_of_zhou2
#print axioms Tower.RV6.hasDerivAt_prod4
#print axioms Tower.RV6.hasDerivAt_sqx
#print axioms Tower.RV6.hasDerivAt_powfour
#print axioms Tower.RV6.hasDerivAt_ldF0
#print axioms Tower.RV6.hasDerivAt_ldF1
#print axioms Tower.RV6.hasDerivAt_ldF2
#print axioms Tower.RV6.hasDerivAt_ldF3
#print axioms Tower.RV6.hasDerivAt_ldF4
#print axioms Tower.RV6.hasDerivAt_thF0
#print axioms Tower.RV6.hasDerivAt_thF1
#print axioms Tower.RV6.hasDerivAt_thF2
#print axioms Tower.RV6.hasDerivAt_thF3
#print axioms Tower.RV6.hasDerivAt_thF4
#print axioms Tower.RV6.L5_thF
#print axioms Tower.RV6.thF0_eq_fB
#print axioms Tower.RV6.l5_fB
#print axioms Tower.RV6.hasDerivAt_ldG0
#print axioms Tower.RV6.hasDerivAt_ldG1
#print axioms Tower.RV6.hasDerivAt_ldG2
#print axioms Tower.RV6.hasDerivAt_ldG3
#print axioms Tower.RV6.hasDerivAt_ldG4
#print axioms Tower.RV6.hasDerivAt_thG0
#print axioms Tower.RV6.hasDerivAt_thG1
#print axioms Tower.RV6.hasDerivAt_thG2
#print axioms Tower.RV6.hasDerivAt_thG3
#print axioms Tower.RV6.hasDerivAt_thG4
#print axioms Tower.RV6.L5_thG
#print axioms Tower.RV6.thG0_eq_gB
#print axioms Tower.RV6.l5_gB
#print axioms Tower.RV6.besselK1_le_of_one_le
#print axioms Tower.RV6.sqrt_mul_one_add_log_cube_le
#print axioms Tower.RV6.sinh_le_exp_self
#print axioms Tower.RV6.kapK_nonneg
#print axioms Tower.RV6.ity_besselI0
#print axioms Tower.RV6.ity_mul_besselI1
#print axioms Tower.RV6.kty_besselK0
#print axioms Tower.RV6.kty_mul_besselK1
#print axioms Tower.RV6.abs_mul4_le
#print axioms Tower.RV6.hdom_prod4
#print axioms Tower.RV6.hdom_add
#print axioms Tower.RV6.hdom_const_mul
#print axioms Tower.RV6.hdom_pow_mul
#print axioms Tower.RV6.pow_mul_exp_neg_le
#print axioms Tower.RV6.integrableOn_hdom
#print axioms Tower.RV6.tendsto_hdom_zero
#print axioms Tower.RV6.tendsto_hdom_atTop
#print axioms Tower.RV6.integral_Ioi_deriv_eq_zero
#print axioms Tower.RV6.hdom_ldF0
#print axioms Tower.RV6.hdom_ldF1
#print axioms Tower.RV6.hdom_ldF2
#print axioms Tower.RV6.hdom_ldF3
#print axioms Tower.RV6.hdom_ldF4
#print axioms Tower.RV6.hdom_thF0
#print axioms Tower.RV6.hdom_thF1
#print axioms Tower.RV6.hdom_thF2
#print axioms Tower.RV6.hdom_thF3
#print axioms Tower.RV6.hdom_thF4
#print axioms Tower.RV6.hdom_thF5
#print axioms Tower.RV6.hjF_eq_hk
#print axioms Tower.RV6.continuousOn_besselJ0_mul
#print axioms Tower.RV6.continuousOn_mul_besselJ1_mul
#print axioms Tower.RV6.abs_besselJ0_mul_le
#print axioms Tower.RV6.abs_mul_besselJ1_mul_le
#print axioms Tower.RV6.integrableOn_hk
#print axioms Tower.RV6.hk_add
#print axioms Tower.RV6.hk_const_mul
#print axioms Tower.RV6.hk_add_cmul
#print axioms Tower.RV6.hk_congr
#print axioms Tower.RV6.hk_zero
#print axioms Tower.RV6.hchain_add
#print axioms Tower.RV6.hchain_const_mul
#print axioms Tower.RV6.hchain_tsq
#print axioms Tower.RV6.hk_ibpA
#print axioms Tower.RV6.hk_ibpB
#print axioms Tower.RV6.hk_theta2
#print axioms Tower.RV6.hchain_thF0
#print axioms Tower.RV6.hchain_thF1
#print axioms Tower.RV6.hchain_thF2
#print axioms Tower.RV6.hchain_thF3
#print axioms Tower.RV6.hchain_thF4
#print axioms Tower.RV6.hk_rel_a0
#print axioms Tower.RV6.hk_rel_a1
#print axioms Tower.RV6.hk_rel_a2
#print axioms Tower.RV6.hk_rel_a3
#print axioms Tower.RV6.hk_rel_b0
#print axioms Tower.RV6.hk_rel_b1
#print axioms Tower.RV6.hk_rel_L5
#print axioms Tower.RV6.hk_relation_F
#print axioms Tower.RV6.hasDerivAt_hk
#print axioms Tower.RV6.hasDerivAt_hk_thF0
#print axioms Tower.RV6.hasDerivAt_hk_thF1
#print axioms Tower.RV6.hasDerivAt_hk_thF2
#print axioms Tower.RV6.hasDerivAt_hk_thF3
#print axioms Tower.RV6.hasDerivAt_hk_thF4
#print axioms Tower.RV6.eq_one_of_hasDerivAt_zero
#print axioms Tower.RV6.ode_theta_two
#print axioms Tower.RV6.ode_theta_two_log
#print axioms Tower.RV6.hasDerivAt_quart
#print axioms Tower.RV6.hasDerivAt_uF
#print axioms Tower.RV6.hasDerivAt_wF
#print axioms Tower.RV6.uF_ode
#print axioms Tower.RV6.wF_ode
#print axioms Tower.RV6.uF_eq

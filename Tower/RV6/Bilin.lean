import Mathlib

/-!
# Linearity of the integral in the shapes used for the Fricke split

* `integral_lin3`, `integral_lin4`: the integral of a combination of three or four integrable
  functions.
* `integral_bilin_gen`: the integral of a product of two finite combinations, divided by a weight,
  is the double sum of the integrals of the pairs, and the integrand is integrable when every
  pair is.

Nothing here is specific to the six-step Mahler measure.
-/

namespace Tower.RV6

open MeasureTheory

theorem integral_lin3 {μ : Measure ℝ} {f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (c₁ c₂ c₃ : ℝ) :
    ∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) ∂μ
      = c₁ * (∫ x, f₁ x ∂μ) + c₂ * (∫ x, f₂ x ∂μ) + c₃ * (∫ x, f₃ x ∂μ) := by
  have i₁ : Integrable (fun x => c₁ * f₁ x) μ := h₁.const_mul c₁
  have i₂ : Integrable (fun x => c₂ * f₂ x) μ := h₂.const_mul c₂
  have i₃ : Integrable (fun x => c₃ * f₃ x) μ := h₃.const_mul c₃
  have i₁₂ : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x) μ := i₁.add i₂
  have e₂ : ∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) ∂μ
      = (∫ x, (c₁ * f₁ x + c₂ * f₂ x) ∂μ) + ∫ x, c₃ * f₃ x ∂μ := integral_add i₁₂ i₃
  have e₃ : ∫ x, (c₁ * f₁ x + c₂ * f₂ x) ∂μ
      = (∫ x, c₁ * f₁ x ∂μ) + ∫ x, c₂ * f₂ x ∂μ := integral_add i₁ i₂
  have m₁ : ∫ x, c₁ * f₁ x ∂μ = c₁ * ∫ x, f₁ x ∂μ := integral_const_mul c₁ f₁
  have m₂ : ∫ x, c₂ * f₂ x ∂μ = c₂ * ∫ x, f₂ x ∂μ := integral_const_mul c₂ f₂
  have m₃ : ∫ x, c₃ * f₃ x ∂μ = c₃ * ∫ x, f₃ x ∂μ := integral_const_mul c₃ f₃
  rw [e₂, e₃, m₁, m₂, m₃]

theorem integrable_lin3 {μ : Measure ℝ} {f₁ f₂ f₃ : ℝ → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (c₁ c₂ c₃ : ℝ) :
    Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) μ := by
  have i₁ : Integrable (fun x => c₁ * f₁ x) μ := h₁.const_mul c₁
  have i₂ : Integrable (fun x => c₂ * f₂ x) μ := h₂.const_mul c₂
  have i₃ : Integrable (fun x => c₃ * f₃ x) μ := h₃.const_mul c₃
  have i₁₂ : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x) μ := i₁.add i₂
  exact i₁₂.add i₃

theorem integral_lin4 {μ : Measure ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (c₁ c₂ c₃ c₄ : ℝ) :
    ∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x) ∂μ
      = c₁ * (∫ x, f₁ x ∂μ) + c₂ * (∫ x, f₂ x ∂μ) + c₃ * (∫ x, f₃ x ∂μ)
        + c₄ * (∫ x, f₄ x ∂μ) := by
  have i₁₂₃ : Integrable (fun x => c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) μ :=
    integrable_lin3 h₁ h₂ h₃ c₁ c₂ c₃
  have i₄ : Integrable (fun x => c₄ * f₄ x) μ := h₄.const_mul c₄
  have e₁ : ∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x) ∂μ
      = (∫ x, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x) ∂μ) + ∫ x, c₄ * f₄ x ∂μ :=
    integral_add i₁₂₃ i₄
  have m₄ : ∫ x, c₄ * f₄ x ∂μ = c₄ * ∫ x, f₄ x ∂μ := integral_const_mul c₄ f₄
  rw [e₁, integral_lin3 h₁ h₂ h₃ c₁ c₂ c₃, m₄]

/-- The integral of a product of two finite combinations, divided by a weight. -/
theorem integral_bilin_gen {μ : Measure ℝ} {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (X : ι → ℝ → ℝ) (Y : κ → ℝ → ℝ) (w : ℝ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (hint : ∀ k ∈ s, ∀ l ∈ t, Integrable (fun y => X k y * Y l y / w y) μ) :
    Integrable (fun y => (∑ k ∈ s, a k * X k y) * (∑ l ∈ t, b l * Y l y) / w y) μ
      ∧ ∫ y, (∑ k ∈ s, a k * X k y) * (∑ l ∈ t, b l * Y l y) / w y ∂μ
        = ∑ k ∈ s, ∑ l ∈ t, a k * b l * ∫ y, X k y * Y l y / w y ∂μ := by
  have hpt : ∀ y : ℝ, (∑ k ∈ s, a k * X k y) * (∑ l ∈ t, b l * Y l y) / w y
      = ∑ k ∈ s, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) := by
    intro y
    rw [Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  have hF : ∀ k ∈ s, ∀ l ∈ t,
      Integrable (fun y => a k * b l * (X k y * Y l y / w y)) μ :=
    fun k hk l hl => (hint k hk l hl).const_mul (a k * b l)
  have hG : ∀ k ∈ s, Integrable (fun y => ∑ l ∈ t, a k * b l * (X k y * Y l y / w y)) μ :=
    fun k hk => integrable_finsetSum t (fun l hl => hF k hk l hl)
  have hH : Integrable (fun y => ∑ k ∈ s, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y)) μ :=
    integrable_finsetSum s hG
  have hfun : (fun y => (∑ k ∈ s, a k * X k y) * (∑ l ∈ t, b l * Y l y) / w y)
      = fun y => ∑ k ∈ s, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) := funext hpt
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hH
  · have e₁ : ∫ y, (∑ k ∈ s, a k * X k y) * (∑ l ∈ t, b l * Y l y) / w y ∂μ
        = ∫ y, ∑ k ∈ s, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    have e₂ : ∫ y, ∑ k ∈ s, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) ∂μ
        = ∑ k ∈ s, ∫ y, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) ∂μ :=
      integral_finsetSum s hG
    rw [e₁, e₂]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have e₃ : ∫ y, ∑ l ∈ t, a k * b l * (X k y * Y l y / w y) ∂μ
        = ∑ l ∈ t, ∫ y, a k * b l * (X k y * Y l y / w y) ∂μ :=
      integral_finsetSum t (fun l hl => hF k hk l hl)
    rw [e₃]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    exact integral_const_mul (a k * b l) (fun y => X k y * Y l y / w y)

/-- A finite combination of integrable functions, with its integral. -/
theorem integral_lin_gen {μ : Measure ℝ} {ι : Type*} (s : Finset ι) (X : ι → ℝ → ℝ)
    (a : ι → ℝ) (hint : ∀ k ∈ s, Integrable (X k) μ) :
    Integrable (fun y => ∑ k ∈ s, a k * X k y) μ
      ∧ ∫ y, ∑ k ∈ s, a k * X k y ∂μ = ∑ k ∈ s, a k * ∫ y, X k y ∂μ := by
  have hF : ∀ k ∈ s, Integrable (fun y => a k * X k y) μ :=
    fun k hk => (hint k hk).const_mul (a k)
  refine ⟨integrable_finsetSum s hF, ?_⟩
  have e₁ : ∫ y, ∑ k ∈ s, a k * X k y ∂μ = ∑ k ∈ s, ∫ y, a k * X k y ∂μ :=
    integral_finsetSum s hF
  rw [e₁]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact integral_const_mul (a k) (X k)

end Tower.RV6

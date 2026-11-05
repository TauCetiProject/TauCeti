/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Sobolev

/-!
# The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for coefficients of small oscillation

Let `0 < n` and `1 < p < ∞`. For `u ∈ W^{2,p}(ℝⁿ)` write `D²u` for its weak Hessian
`TauCeti.Wkp.iteratedGradient 1 u`, an `Lᵖ` field of endomorphisms of `ℝⁿ`, so that
`⟪D²u(x) eᵢ, eⱼ⟫` is the weak second derivative `∂ᵢ∂ⱼu`. This file proves the strong-solution
estimate for the non-divergence-form operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` with coefficients of small
oscillation
(`TauCeti.PDE.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le`).
There are `C` and `δ > 0`, depending only on `n` and `p`, with the following property. Let `A` be a
matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `s` be closed, and let `a` be a matrix-valued
coefficient with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε ≤ δ λ` for almost every `x ∈ s`. Then every
`u ∈ W^{2,p}(ℝⁿ)` vanishing outside `s` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere satisfies
`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`. No regularity of `a` is assumed.

## The argument

Freeze the coefficients at `A`:
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = f + ∑ᵢⱼ (Aᵢⱼ - aᵢⱼ) ∂ᵢ∂ⱼu`. Outside `s` the weak Hessian vanishes
(`TauCeti.Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero`), and on `s` the error term is at
most `n² ε ‖D²u‖` pointwise (`Matrix.abs_contraction_le`). The constant-coefficient
estimate (`TauCeti.exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq`) gives
`‖D²u‖ ≤ (C₀ / λ) (‖f‖ + n² ε ‖D²u‖)`, and the choice of `δ` makes the coefficient of `‖D²u‖`
on the right at most `1 / 2`, so it is absorbed on the left
(`TauCeti.PDE.le_two_mul_div_mul_of_le_div_mul_of_le_add`). This is the step of the `W^{2,p}`
theory for continuous coefficients that is applied, after a partition of unity, on each ball small
enough that the oscillation of the coefficients is below `δ λ`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (freezing the coefficients and absorbing the error).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The absorption step of the perturbation argument for coefficients of small oscillation: if
`d ≤ (C / μ) g` and `g ≤ f + N ε d`, where `0 ≤ d` and `ε ≤ μ / (2 (C + 1) N)`, then
`d ≤ (2 C / μ) f`. The choice of `ε` makes the error coefficient `C N ε / μ` at most `1 / 2`. -/
theorem le_two_mul_div_mul_of_le_div_mul_of_le_add {C N ε μ d g f : ℝ} (hμ : 0 < μ)
    (hC : 0 ≤ C) (hN : 0 < N) (hε : ε ≤ 1 / (2 * (C + 1) * N) * μ) (hd : 0 ≤ d)
    (hdg : d ≤ C / μ * g) (hg : g ≤ f + N * ε * d) : d ≤ 2 * C / μ * f := by
  have hK : C / μ * (N * ε) ≤ 1 / 2 := by
    calc C / μ * (N * ε) ≤ C / μ * (N * (1 / (2 * (C + 1) * N) * μ)) := by gcongr
      _ = C / (2 * (C + 1)) := by field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) two_pos]
          linarith
  have habs : d ≤ C / μ * f + 1 / 2 * d := by
    calc d ≤ C / μ * g := hdg
      _ ≤ C / μ * (f + N * ε * d) := by gcongr
      _ = C / μ * f + C / μ * (N * ε) * d := by ring
      _ ≤ C / μ * f + 1 / 2 * d := by gcongr
  have h2 : 2 * C / μ * f = 2 * (C / μ * f) := by ring
  linarith

/-- **The Calderón–Zygmund estimate in `W^{2,p}(ℝⁿ)` for coefficients of small oscillation.**
Let `0 < n` and `1 < p < ∞`. There are constants `C` and `δ > 0`, depending only on `n` and `p`,
with the following property. Let `A` be a matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ` and `0 < λ`, let `s` be a
closed set, and let `a` be a matrix-valued coefficient with `|aᵢⱼ(x) - Aᵢⱼ| ≤ ε` for almost every
`x ∈ s`, where `ε ≤ δ λ`. Then every `u ∈ W^{2,p}(ℝⁿ)` vanishing almost everywhere outside `s`
and solving `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` almost everywhere, with `f ∈ Lᵖ(ℝⁿ)`, satisfies

`‖D²u‖_{Lᵖ} ≤ (C / λ) ‖f‖_{Lᵖ}`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No measurability or continuity
of `a` is assumed. -/
theorem exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq_of_abs_sub_le (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
        {s : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}, IsClosed s → ε ≤ δ * lam →
        (∀ᵐ x, x ∈ s → ∀ i j, |a x i j - A i j| ≤ ε) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) ⊤ p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (⊤ : Opens (EuclideanSpace ℝ (Fin n))))),
        (∀ᵐ x, x ∉ s → Wkp.value 2 u x = 0) →
        (∀ᵐ x, ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
        ‖Wkp.iteratedGradient 1 u‖ ≤ C / lam * ‖f‖ := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedGradient_le_mul_norm_of_sum_mul_inner_eq hp hp_top
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨2 * C, 1 / (2 * (C + 1) * n ^ 2), by positivity,
    fun {A lam} hlam hA {a s ε} hs hε ha u f hu hf => ?_⟩
  set H := Wkp.iteratedGradient 1 u
  set T := Matrix.contraction A with hT
  set g := T.compLpL p _ H
  have htop :
      MeasurableSet ((⊤ : Opens (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))) :=
    (⊤ : Opens (EuclideanSpace ℝ (Fin n))).isOpen.measurableSet
  have hg : ∀ᵐ x, g x = T (H x) := by
    filter_upwards [(ae_restrict_iff' htop).1 (T.coeFn_compLpL H)] with x hx using hx (by simp)
  -- The weak Hessian vanishes outside `s`, where `u` does.
  have hH0 : ∀ᵐ x, x ∉ s → H x = 0 := by
    simpa using Wkp.iteratedGradient_ae_eq_zero_of_value_ae_eq_zero_of_isOpen 1 u hs.isOpen_compl
      (by simpa using hu)
  -- The constant-coefficient estimate, applied to the frozen operator.
  have hHg : ‖H‖ ≤ C / lam * ‖g‖ :=
    hC hlam hA u g (by filter_upwards [hg] with x hx; rw [hx, Matrix.contraction_apply])
  -- The error of freezing is at most `n² ε |D²u|` pointwise.
  have hgf : ‖g - f‖ ≤ n ^ 2 * ε * ‖H‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub g f, ae_restrict_of_ae hg, ae_restrict_of_ae hf,
      ae_restrict_of_ae ha, ae_restrict_of_ae hH0] with x hsub hgx hfx hax hHx
    by_cases hxs : x ∈ s
    · -- On `s`, the difference is the contraction of the weak Hessian with `A - a(x)`.
      have hdiff : g x - f x = Matrix.contraction (A - a x) (H x) := by
        rw [hgx, ← hfx, hT, Matrix.contraction_sub, sub_apply,
          Matrix.contraction_apply (a x)]
      rw [hsub, Pi.sub_apply, hdiff, Real.norm_eq_abs]
      exact Matrix.abs_contraction_le (fun i j => by
        rw [Matrix.sub_apply, abs_sub_comm]
        exact hax hxs i j) (H x)
    · rw [hsub, Pi.sub_apply, hgx, ← hfx, hHx hxs]
      simp
  rw [NNReal.coe_mul, NNReal.coe_ofNat]
  exact le_two_mul_div_mul_of_le_div_mul_of_le_add hlam C.coe_nonneg (pow_pos hn0 2) hε
    (norm_nonneg _) hHg (by linarith [norm_sub_norm_le g f])

end PDE

end TauCeti

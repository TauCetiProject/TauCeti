/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Supersolution.Basic

/-!
# Lower bounds from small negative powers of supersolutions

A positive weak supersolution of `-div(a ∇u) ≥ 0` satisfies the local estimate

`u⁻¹ ≤ D R^{-n/p} (∫_{B(x₀, R)} u⁻ᵖ)^{1/p}` on `B(x₀, R/2)`, for every `0 < p ≤ 2`.

The constant depends on the ellipticity constants, the dimension, the exponent and the
normalization of Haar measure, but not on the positive lower bound assumed for `u`.
This is the negative-power input to the weak Harnack inequality: a crossover estimate for
positive and negative powers can combine this lower bound with reverse Hölder estimates.

The more general Sobolev-inequality form is also provided. Both results use local boundedness
of subsolutions and the convex reciprocal approximations from
`TauCeti.PDE.UniformlyEllipticOn.ae_inv_value_le_mul_setIntegral_rpow`.

## References

* J. Moser, *On Harnack's theorem for elliptic differential equations*, Comm. Pure Appl. Math.
  **14** (1961), 577–591.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.6, the proof of Theorem 8.18.
-/

public section

noncomputable section

open MeasureTheory Matrix Metric Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {lam Lam : ℝ}

/-- **Lower bound from negative powers under a Sobolev inequality.** Suppose every ball in `Ω`
satisfies `‖v‖_q ≤ S ‖∇v‖₂` for `v ∈ W^{1,2}_0`, where `q > 2`. For `0 < p ≤ 2`, a positive
weak supersolution satisfies
`u⁻¹ ≤ D R^{-2/(αp)} (∫_{B(x₀, R)} u⁻ᵖ)^{1/p}` on the half ball, with `α = 1 - 2/q`.
The constant is independent of the domain, the solution and its positive lower bound. -/
theorem exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow_of_forall_eLpNorm_le
    {q : ℝ≥0∞} (hq : 2 < q) (S : ℝ≥0) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ y s, ball y s ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∀ v ∈ w1p0Submodule mu ⟨ball y s, isOpen_ball⟩ 2,
          eLpNorm (W1p.value v) q (mu.restrict (ball y s)) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        (W1p.value u x)⁻¹ ≤ D * R ^ (-(2 * (1 - 2 / q.toReal)⁻¹ / p)) *
          (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_eLpNorm_le
      (mu := mu) (lam := lam) (Lam := Lam) hq S hp hp2
  refine ⟨D, hD, fun h ha hS hu hm hum hR hball => ?_⟩
  exact h.ae_inv_value_le_mul_setIntegral_rpow ha hu hm hum hR hball (by positivity) hp
    fun w hw => by simpa only [sub_zero, zero_add] using hbound (u := w) (k := 0) h ha hS hw hball

/-- **Moser's lower bound from small negative powers.** For every `0 < p ≤ 2` and every
positive weak supersolution in any dimension `n ≥ 1`,
`u⁻¹ ≤ D R^{-n/p} (∫_{B(x₀, R)} u⁻ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.
The constant depends only on `λ`, `Λ`, `p`, the dimension and Haar normalization, not on the
positive lower bound for `u`. No boundary regularity is required. -/
theorem exists_ae_inv_value_le_mul_rpow_mul_setIntegral_rpow [Nonempty ι] {p : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {m : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          0 ≤ energyFormH1 a 0 0 u (v : W1p mu Omega 2)) →
      0 < m → (∀ᵐ x ∂mu.restrict Omega, m ≤ W1p.value u x) →
      0 < R → ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (ball x₀ (R / 2)),
        (W1p.value u x)⁻¹ ≤ D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in ball x₀ R, (W1p.value u x)⁻¹ ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ := exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow
    (mu := mu) (lam := lam) (Lam := Lam) hp hp2
  refine ⟨D, hD, fun h ha hu hm hum hR hball => ?_⟩
  exact h.ae_inv_value_le_mul_setIntegral_rpow ha hu hm hum hR hball (by positivity) hp
    fun w hw => by simpa only [sub_zero, zero_add] using hbound (u := w) (k := 0) h ha hw hball

end TauCeti.PDE

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.InitialTrace
import TauCeti.Analysis.Matrix.Contraction

/-!
# Attainment of the initial data in a weighted uniform norm

On the slab `Q = [0, T] × ℝⁿ`, with `ℝⁿ = EuclideanSpace ℝ ι`, consider the parabolic operator

`P u = ∂ₜu - ∑ᵢⱼ aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

with coefficients that, for `0 < t < T`, satisfy `0 ≤ ξᵀ a(t, x) ξ`, `|aⁱʲ(t, x)| ≤ Λ`,
`‖b(t, x)‖ ≤ β` and `|c(t, x)| ≤ γ`, and let `w = exp ∘ ℓ` be a positive time-independent spatial
weight whose logarithm has bounded first and second derivatives, `‖Dℓ‖ ≤ L₁` and `‖D²ℓ‖ ≤ L₂`.
The logarithm itself may be unbounded, so `w` may grow or decay exponentially at infinity, and
the solutions considered here are those of finite weighted uniform norm `sup |u / w|`.

This file proves that such a classical solution approaches its initial data `g = u(0, ·)` in the
weighted uniform norm at a rate governed by a modulus of continuity `ω` of `g / w` alone: there
is a constant `C`, depending only on `ι`, `T`, `Λ`, `β`, `γ`, `L₁` and `L₂`, such that

`|u(t, x) - g(x)| ≤ C w(x) (ω(√t) + t (sup |g / w| + sup |P u / w|))`

for `0 < t ≤ T`. Here `ω` is nondecreasing on `[0, ∞)` and
`|g(x) / w(x) - g(y) / w(y)| ≤ ω(‖x - y‖)`. Consequently a family of solutions whose weighted
data `g / w` share one modulus `ω` with `ω(r) → 0` as `r → 0⁺`, and whose weighted data and
forcing are uniformly bounded, attains its initial data in the weighted uniform norm uniformly
over the whole family. For `w = 1` this is the unweighted estimate of
`TauCeti.Analysis.PDE.MaximumPrinciple.Parabolic.InitialTrace`,
`exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le`,
from which it is derived.

## The argument

For `u = w v`, the product rule gives `D_x u = w (D_x v + Dℓ ⊗ v)` and

`D_x² u (h, k) = w (D_x² v (h, k) + Dℓ h D_x v k + Dℓ k D_x v h + (D²ℓ (h, k) + Dℓ h Dℓ k) v)`,

so that `P u = w P_w v`, where `P_w` has the same second-order coefficients `aⁱʲ` and the
lower-order coefficients

* `b_w = b + ∑ᵢ (∑ⱼ (aⁱʲ + aʲⁱ) ∂ⱼℓ) eᵢ`;
* `c_w = c + ∑ᵢⱼ aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ⟪Dℓ, b⟫`

(`TauCeti.PDE.exp_mul_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq` in
`TauCeti.Analysis.PDE.MaximumPrinciple.NonDivergence`). These are bounded in terms of
`Λ`, `β`, `γ`, `L₁` and `L₂`, so the unweighted estimate applies to the bounded solution
`v = u / w` of `P_w v = P u / w`.

## Main declarations

All declarations are in the `TauCeti.PDE` namespace.

* `exists_abs_sub_le_mul_exp_mul_add_mul_of_abs_deriv_sub_le_mul_exp`:
  **the weighted modulus estimate**.
* `tendstoUniformly_exp_neg_mul_of_abs_deriv_sub_le_mul_exp`: a
  family of solutions with a common weighted modulus attains its initial data uniformly in the
  weighted norm.

## References

* A. Friedman, *Partial Differential Equations of Parabolic Type*, Chapter 2 (the
  substitution `u = w v` by a positive weight, transforming a parabolic equation into one of the
  same type).
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes (2004),
  Chapter 4 (the Cauchy problem with uniformly continuous initial data).
-/

public section

noncomputable section

open Set Filter Function Topology Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The drift `b + ∑ᵢ (∑ⱼ (Aⁱʲ + Aʲⁱ) ∂ⱼℓ) eᵢ` of the conjugated operator is bounded by
`β + (card ι)² · 2 |Λ| L₁` when `‖b‖ ≤ β`, `|Aⁱʲ| ≤ Λ` and `‖Dℓ‖ ≤ L₁`. -/
private theorem norm_add_sum_smul_single_le {A : Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι}
    {D : EuclideanSpace ℝ ι →L[ℝ] ℝ} {Lam β L₁ : ℝ} (hA : ∀ i j, |A i j| ≤ Lam) (hb : ‖b‖ ≤ β)
    (hD : ‖D‖ ≤ L₁) :
    ‖b + ∑ i, (∑ j, (A i j + A j i) * D (EuclideanSpace.single j 1)) •
        EuclideanSpace.single i (1 : ℝ)‖ ≤
      β + Fintype.card ι ^ 2 * (2 * |Lam| * L₁) := by
  have hDj (j : ι) : |D (EuclideanSpace.single j 1)| ≤ L₁ := by
    simpa [Real.norm_eq_abs] using D.le_of_opNorm_le hD (EuclideanSpace.single j (1 : ℝ))
  have hAij (i j : ι) : |A i j + A j i| ≤ 2 * |Lam| := by
    have := abs_add_le (A i j) (A j i)
    linarith [hA i j, hA j i, le_abs_self Lam]
  have hsum (i : ι) : |∑ j, (A i j + A j i) * D (EuclideanSpace.single j 1)| ≤
      Fintype.card ι * (2 * |Lam| * L₁) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |(A i j + A j i) * D (EuclideanSpace.single j 1)| ≤
        ∑ _j : ι, 2 * |Lam| * L₁ := Finset.sum_le_sum fun j _ ↦ by
          rw [abs_mul]
          exact mul_le_mul (hAij i j) (hDj j) (abs_nonneg _) (by positivity)
      _ = _ := by simp
  calc _ ≤ ‖b‖ + ‖∑ i, (∑ j, (A i j + A j i) * D (EuclideanSpace.single j 1)) •
        EuclideanSpace.single i (1 : ℝ)‖ := norm_add_le _ _
    _ ≤ β + ∑ _i : ι, Fintype.card ι * (2 * |Lam| * L₁) := by
      gcongr
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      simpa [norm_smul] using hsum i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- The zeroth-order coefficient `c + ∑ᵢⱼ Aⁱʲ (∂ᵢ∂ⱼℓ + ∂ᵢℓ ∂ⱼℓ) + ∂_b ℓ` of the conjugated
operator is bounded by `γ + (card ι)² |Λ| (L₂ + L₁²) + L₁ β` when `|c| ≤ γ`, `|Aⁱʲ| ≤ Λ`,
`‖b‖ ≤ β`, `‖Dℓ‖ ≤ L₁` and `‖D²ℓ‖ ≤ L₂`. -/
private theorem abs_add_sum_sum_mul_add_le {A : Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι} {c : ℝ}
    {D : EuclideanSpace ℝ ι →L[ℝ] ℝ} {D₂ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ}
    {Lam β γ L₁ L₂ : ℝ} (hA : ∀ i j, |A i j| ≤ Lam) (hb : ‖b‖ ≤ β) (hc : |c| ≤ γ)
    (hD : ‖D‖ ≤ L₁) (hD₂ : ‖D₂‖ ≤ L₂) :
    |c + ∑ i, ∑ j, A i j * (D₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        D (EuclideanSpace.single i 1) * D (EuclideanSpace.single j 1)) + D b| ≤
      γ + Fintype.card ι ^ 2 * |Lam| * (L₂ + L₁ ^ 2) + L₁ * β := by
  have hL₁ : 0 ≤ L₁ := (norm_nonneg D).trans hD
  -- The middle term is a contraction of `A` with the bilinear form `D² ℓ + Dℓ ⊗ Dℓ`.
  set B := D₂ + D.smulRight D
  have hB : ‖B‖ ≤ L₂ + L₁ ^ 2 := by
    have hDD : ‖D.smulRight D‖ ≤ L₁ ^ 2 := by
      rw [ContinuousLinearMap.norm_smulRight_apply, sq]
      exact mul_le_mul hD hD (norm_nonneg _) hL₁
    linarith [norm_add_le D₂ (D.smulRight D)]
  have hsum : ∑ i, ∑ j, A i j * (D₂ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      D (EuclideanSpace.single i 1) * D (EuclideanSpace.single j 1)) =
      ∑ i, ∑ j, A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    simp [B]
  have hmid : |∑ i, ∑ j, A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤
      Fintype.card ι ^ 2 * |Lam| * (L₂ + L₁ ^ 2) :=
    (Matrix.abs_sum_sum_mul_apply_single_single_le (fun i j ↦ (hA i j).trans (le_abs_self Lam))
      B).trans (by gcongr)
  have hDb : |D b| ≤ L₁ * β := by
    rw [← Real.norm_eq_abs]
    exact (D.le_of_opNorm_le hD b).trans (mul_le_mul_of_nonneg_left hb hL₁)
  rw [hsum]
  calc _ ≤ |c| + |∑ i, ∑ j, A i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| +
        |D b| := abs_add_three _ _ _
    _ ≤ _ := by gcongr

/-- **The conjugated equation.** If `u` is `C²` in space at `y` and differentiable in time at `t`,
and `P u` is at most `F exp (ℓ y)` in absolute value at `(t, y)`, then the quotient
`v = exp (-ℓ) * u` satisfies `|P_w v| ≤ F` at `(t, y)`, where `P_w` is the operator conjugated by
the weight `exp ℓ` (`exp_mul_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq`). -/
private theorem abs_deriv_sub_exp_neg_mul_le {A : Matrix ι ι ℝ} {b : EuclideanSpace ℝ ι} {c : ℝ}
    {u : ℝ → EuclideanSpace ℝ ι → ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ} {t F : ℝ}
    {y : EuclideanSpace ℝ ι} (hℓ : ContDiff ℝ 2 ℓ) (hcd : ContDiffAt ℝ 2 (u t) y)
    (hdiff : DifferentiableAt ℝ (fun s ↦ u s y) t)
    (hP : |deriv (fun s ↦ u s y) t - (∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ (u t)) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ (u t) y b +
        c * u t y)| ≤ F * Real.exp (ℓ y)) :
    |deriv (fun s ↦ Real.exp (-ℓ y) * u s y) t -
      (∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-ℓ z) * u t z) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ (fun z ↦ Real.exp (-ℓ z) * u t z) y (b + ∑ i, (∑ j, (A i j + A j i) *
        fderiv ℝ ℓ y (EuclideanSpace.single j 1)) • EuclideanSpace.single i 1) +
      (c + ∑ i, ∑ j, A i j * (fderiv ℝ (fderiv ℝ ℓ) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) +
        fderiv ℝ ℓ y (EuclideanSpace.single i 1) * fderiv ℝ ℓ y (EuclideanSpace.single j 1)) +
        fderiv ℝ ℓ y b) * (Real.exp (-ℓ y) * u t y))| ≤ F := by
  have huv (s : ℝ) (z : EuclideanSpace ℝ ι) :
      u s z = Real.exp (ℓ z) * (Real.exp (-ℓ z) * u s z) := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hdt : deriv (fun s ↦ u s y) t =
      Real.exp (ℓ y) * deriv (fun s ↦ Real.exp (-ℓ y) * u s y) t := by
    conv_lhs => rw [show (fun s ↦ u s y) = fun s ↦ Real.exp (ℓ y) * (Real.exp (-ℓ y) * u s y) from
      funext fun s ↦ huv s y]
    exact deriv_const_mul _ (hdiff.const_mul _)
  have hconj := exp_mul_sum_mul_fderiv_fderiv_add_fderiv_add_mul_eq A b c hℓ.contDiffAt
    (hℓ.contDiffAt.neg.exp.mul hcd)
  rw [hdt, show u t = fun z ↦ Real.exp (ℓ z) * (Real.exp (-ℓ z) * u t z) from funext (huv t),
    ← hconj, ← mul_sub, abs_mul, Real.abs_exp, mul_comm F] at hP
  exact le_of_mul_le_mul_left hP (Real.exp_pos _)

/-- **The weighted modulus estimate.** There is a constant `C`,
depending only on `ι`, `T`, `Λ`, `β`, `γ`, `L₁` and `L₂`, with the following property. Let the
coefficients satisfy, for `0 < t < T`, `0 ≤ ξᵀ a(t, x) ξ`, `|aⁱʲ(t, x)| ≤ Λ`, `‖b(t, x)‖ ≤ β` and
`|c(t, x)| ≤ γ`, and let `ℓ` be `C²` with `‖Dℓ‖ ≤ L₁` and `‖D²ℓ‖ ≤ L₂`. Let `u` be continuous on
`[0, T] × ℝⁿ` with `u / exp ℓ` bounded there, `C²` in space and differentiable in time for
`0 < t < T`, with `|P u| ≤ F exp ℓ` there and `|u(0, ·)| ≤ M exp ℓ`. Let `ω` be nondecreasing on
`[0, ∞)` and a modulus of continuity of `u(0, ·) / exp ℓ`. Then for `0 < t ≤ T`,

`|u(t, x) - u(0, x)| ≤ C exp (ℓ x) (ω(√t) + t (M + F))`. -/
theorem exists_abs_sub_le_mul_exp_mul_add_mul_of_abs_deriv_sub_le_mul_exp
    (T Lam β γ L₁ L₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a : ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : ℝ → EuclideanSpace ℝ ι → ℝ}
      {u : ℝ → EuclideanSpace ℝ ι → ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ} {ω : ℝ → ℝ} {M F : ℝ},
      ContDiff ℝ 2 ℓ → (∀ x, ‖fderiv ℝ ℓ x‖ ≤ L₁) → (∀ x, ‖fderiv ℝ (fderiv ℝ ℓ) x‖ ≤ L₂) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a t x).toQuadraticForm' ξ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a t x i j| ≤ Lam) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b t x‖ ≤ β) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c t x| ≤ γ) →
      ContinuousOn (uncurry u) (Icc 0 T ×ˢ univ) →
      Bornology.IsBounded
        ((fun p : ℝ × EuclideanSpace ℝ ι ↦ Real.exp (-ℓ p.2) * u p.1 p.2) '' Icc 0 T ×ˢ univ) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u t) x) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u s x) t) →
      (∀ ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u s x) t -
        (∑ i, ∑ j, a t x i j * fderiv ℝ (fderiv ℝ (u t)) x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) + fderiv ℝ (u t) x (b t x) + c t x * u t x)| ≤
            F * Real.exp (ℓ x)) →
      (∀ x, |u 0 x| ≤ M * Real.exp (ℓ x)) → MonotoneOn ω (Ici 0) →
      (∀ x y, |Real.exp (-ℓ x) * u 0 x - Real.exp (-ℓ y) * u 0 y| ≤ ω (dist x y)) →
      ∀ ⦃t⦄, t ∈ Ioc 0 T → ∀ x,
        |u t x - u 0 x| ≤ C * Real.exp (ℓ x) * (ω (√t) + t * (M + F)) := by
  obtain ⟨C, hC, hest⟩ :=
    exists_abs_sub_le_mul_add_mul_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
      (ι := ι) T Lam (β + Fintype.card ι ^ 2 * (2 * |Lam| * L₁))
      (γ + Fintype.card ι ^ 2 * |Lam| * (L₂ + L₁ ^ 2) + L₁ * β)
  refine ⟨C, hC, fun {a b c u ℓ ω M F} hℓ hL₁ hL₂ ha haLam hb hc hcont hbdd hcd hdiff hP hM hωm hω
    t₀ ht₀ x ↦ ?_⟩
  -- The unweighted estimate applies to the bounded quotient `exp (-ℓ) * u`, which solves the
  -- conjugated equation.
  have hv := hest (u := fun t y ↦ Real.exp (-ℓ y) * u t y) ha haLam
    (fun _ ht y ↦ norm_add_sum_smul_single_le (haLam ht y) (hb ht y) (hL₁ y))
    (fun _ ht y ↦ abs_add_sum_sum_mul_add_le (haLam ht y) (hb ht y) (hc ht y) (hL₁ y) (hL₂ y))
    (((hℓ.continuous.comp continuous_snd).neg.rexp.continuousOn).mul hcont) hbdd
    (fun _ ht y ↦ hℓ.contDiffAt.neg.exp.mul (hcd ht y)) (fun _ ht y ↦ (hdiff ht y).const_mul _)
    (fun _ ht y ↦ abs_deriv_sub_exp_neg_mul_le hℓ (hcd ht y) (hdiff ht y) (hP ht y))
    (fun y ↦ by
      rw [abs_mul, Real.abs_exp, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
      exact hM y) hωm hω ht₀ x
  rw [← mul_sub, abs_mul, Real.abs_exp, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)] at hv
  linarith

/-- **A family of solutions attains its initial data uniformly in a weighted norm.** Let `u k`,
for `k : κ`, be classical solutions on `[0, T] × ℝⁿ`, `0 < T`, as in
`exists_abs_sub_le_mul_exp_mul_add_mul_of_abs_deriv_sub_le_mul_exp`,
with coefficients `a k`, `b k`, `c k` obeying common bounds `Λ`, `β`, `γ`, weighted by a common
`exp ℓ` with `‖Dℓ‖ ≤ L₁` and `‖D²ℓ‖ ≤ L₂`, with `|P (u k)| ≤ F exp ℓ` and
`|u k (0, ·)| ≤ M exp ℓ`. If the weighted initial data `u k (0, ·) / exp ℓ` share a modulus of
continuity `ω`, nondecreasing on `[0, ∞)` with `ω(r) → 0` as `r → 0⁺`, then
`u k (t, x) / exp (ℓ x) → u k (0, x) / exp (ℓ x)` as `t → 0⁺`, uniformly in `k` and `x`. -/
theorem tendstoUniformly_exp_neg_mul_of_abs_deriv_sub_le_mul_exp
    {κ : Type*} {a : κ → ℝ → EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    {b : κ → ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : κ → ℝ → EuclideanSpace ℝ ι → ℝ}
    {u : κ → ℝ → EuclideanSpace ℝ ι → ℝ} {ℓ : EuclideanSpace ℝ ι → ℝ} {ω : ℝ → ℝ}
    {T Lam β γ L₁ L₂ M F : ℝ} (hT : 0 < T) (hℓ : ContDiff ℝ 2 ℓ)
    (hL₁ : ∀ x, ‖fderiv ℝ ℓ x‖ ≤ L₁) (hL₂ : ∀ x, ‖fderiv ℝ (fderiv ℝ ℓ) x‖ ≤ L₂)
    (ha : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x (ξ : EuclideanSpace ℝ ι), 0 ≤ (a k t x).toQuadraticForm' ξ)
    (haLam : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x i j, |a k t x i j| ≤ Lam)
    (hb : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ‖b k t x‖ ≤ β)
    (hc : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |c k t x| ≤ γ)
    (hcont : ∀ k, ContinuousOn (uncurry (u k)) (Icc 0 T ×ˢ univ))
    (hbdd : ∀ k, Bornology.IsBounded
      ((fun p : ℝ × EuclideanSpace ℝ ι ↦ Real.exp (-ℓ p.2) * u k p.1 p.2) '' Icc 0 T ×ˢ univ))
    (hcd : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, ContDiffAt ℝ 2 (u k t) x)
    (hdiff : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, DifferentiableAt ℝ (fun s ↦ u k s x) t)
    (hP : ∀ k ⦃t⦄, t ∈ Ioo 0 T → ∀ x, |deriv (fun s ↦ u k s x) t -
      (∑ i, ∑ j, a k t x i j * fderiv ℝ (fderiv ℝ (u k t)) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) + fderiv ℝ (u k t) x (b k t x) + c k t x * u k t x)| ≤
          F * Real.exp (ℓ x))
    (hM : ∀ k x, |u k 0 x| ≤ M * Real.exp (ℓ x)) (hωm : MonotoneOn ω (Ici 0))
    (hω : ∀ k x y, |Real.exp (-ℓ x) * u k 0 x - Real.exp (-ℓ y) * u k 0 y| ≤ ω (dist x y))
    (hω0 : Tendsto ω (𝓝[>] 0) (𝓝 0)) :
    TendstoUniformly (fun t (q : κ × EuclideanSpace ℝ ι) ↦ Real.exp (-ℓ q.2) * u q.1 t q.2)
      (fun q ↦ Real.exp (-ℓ q.2) * u q.1 0 q.2) (𝓝[>] 0) :=
  -- The unweighted statement applies to the bounded quotients `exp (-ℓ) * u k`, which solve the
  -- conjugated equations.
  tendstoUniformly_of_abs_deriv_sub_sum_mul_fderiv_fderiv_add_fderiv_add_mul_le
    (u := fun k t y ↦ Real.exp (-ℓ y) * u k t y) hT ha haLam
    (fun k _ ht y ↦ norm_add_sum_smul_single_le (haLam k ht y) (hb k ht y) (hL₁ y))
    (fun k _ ht y ↦ abs_add_sum_sum_mul_add_le (haLam k ht y) (hb k ht y) (hc k ht y) (hL₁ y)
      (hL₂ y))
    (fun k ↦ ((hℓ.continuous.comp continuous_snd).neg.rexp.continuousOn).mul (hcont k)) hbdd
    (fun k _ ht y ↦ hℓ.contDiffAt.neg.exp.mul (hcd k ht y))
    (fun k _ ht y ↦ (hdiff k ht y).const_mul _)
    (fun k _ ht y ↦ abs_deriv_sub_exp_neg_mul_le hℓ (hcd k ht y) (hdiff k ht y) (hP k ht y))
    (fun k y ↦ by
      rw [abs_mul, Real.abs_exp, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
      exact hM k y) hωm hω hω0

end PDE

end TauCeti

end

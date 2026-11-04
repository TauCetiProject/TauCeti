/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator

/-!
# Freezing the coefficients of a parabolic operator

Let `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` have coefficient fields in `C_b^{α,α/2}` on the slab
`E × [t₀, t₁]`, and freeze its principal part at a point `z₀` of the slab: `P_{z₀} u = ∂ₜu -
A(z₀)·D_x²u`. The time derivatives cancel in `P u - P_{z₀} u`, and the remainder consists of the
coefficient error `(A(z₀) - A)·D_x²u` and the lower-order terms. This file estimates it in
`C_b^{α,α/2}` for `u` in `C_b^{2+α,1+α/2}`.

The coefficient error is small in `C_b^{α,α/2}` when `D_x²u` is supported near `z₀`, because the
size of `A - A(z₀)` enters only on that support. Precisely, if `‖A p - A(z₀)‖ ≤ δ` wherever
`D_x²u (p) ≠ 0`, then

`‖P u - P_{z₀} u‖_{α,par} ≤ δ ‖D_x²u‖_{α,par} + [A]_{α,par} ‖D_x²u‖_∞ + ‖B‖ ‖D_xu‖_{α,par} +
  ‖C‖ ‖u‖_{α,par}`

(`ParabolicC2HolderSpace.norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le`). When
`D_x²u` vanishes outside the closed parabolic ball of radius `r` about `z₀`, the Hölder continuity
of `A` gives `δ = [A]_{α,par} r^α`. For `0 < α < 1`, interpolation then absorbs every term except
the first into an arbitrarily small multiple of the order-two norm plus a multiple of `‖u‖_∞`:

`‖P u - P_{z₀} u‖_{α,par} ≤ (L r^α + η) ‖u‖_{2+α,par} + K ‖u‖_∞`,

where `L` bounds `[A]_{α,par}`, and `K` depends only on `α`, `η`, `L` and a bound `M` for
`‖B‖ + ‖C‖`; this is
`ParabolicC2HolderSpace.exists_norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le`.
The constant is uniform over the slab, the coefficients, the point `z₀` and the radius `r`. On
`ℝⁿ` with scalar coefficients `aⁱʲ`, `bⁱ`, `c`, the frozen operator is the constant-coefficient
operator `∂ₜ - aⁱʲ(z₀) ∂ᵢ∂ⱼ`, and `L`, `M` bound `∑ᵢⱼ [aⁱʲ]_{α,par}` and `∑ᵢ ‖bⁱ‖ + ‖c‖`
(`exists_norm_euclideanParabolicOperatorL_sub_euclideanParabolicOperatorL_const_apply_le`).
No ellipticity, symmetry or sign condition is used. This is the freezing step of the Schauder a
priori estimate for variable coefficients: applied to a function localized near `z₀` by a cutoff,
it reduces the estimate for `P` to the one for the constant-coefficient operator `P_{z₀}`, with an
error that is absorbed once `r` is small.

## References

* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Hölder Spaces*, Graduate
  Studies in Mathematics 12, AMS, 1996 (Schauder estimates for parabolic equations with
  variable coefficients, by freezing the coefficients at a point).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Theorem 6.2 (the elliptic freezing argument).
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {t₀ t₁ : ℝ} {ht : t₀ < t₁}

/-- A local shortcut for the norm on Hessians, needed for the coefficient space of the
second-order term for the reason explained in `TauCeti.Analysis.PDE.Parabolic.Holder.Operator`. -/
local instance instNormedAddCommGroupHessian :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance instNormedSpaceHessian :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- **The freezing estimate.** Freeze the principal part of `P = ∂ₜ - A·D_x² - B·D_x - C` at
`z₀`. If `‖A p - A(z₀)‖ ≤ δ` wherever the Hessian `D_x²u (p)` is nonzero, then

`‖P u - P_{z₀} u‖ ≤ δ ‖D_x²u‖ + [A]_α ‖D_x²u‖_∞ + ‖B‖ ‖D_xu‖ + ‖C‖ ‖u‖`

in `C_b^{α,α/2}`, where `P_{z₀} = ∂ₜ - A(z₀)·D_x²`. -/
theorem norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
    (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F))
    (u : ParabolicC2HolderSpace α E F ht) (z₀ : slab (E := E) t₀ t₁) {δ : ℝ}
    (hδ : ∀ p, spatialSecondFDerivL u p ≠ 0 → ‖A p - A z₀‖ ≤ δ) :
    ‖parabolicOperatorL hα A B C u - parabolicOperatorL hα (HolderSpace.const (A z₀)) 0 0 u‖ ≤
      δ * ‖spatialSecondFDerivL u‖ +
        nnHolderNorm α ⇑A * ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ +
        ‖B‖ * ‖spatialFDerivHolderL hα u‖ + ‖C‖ * ‖valueHolderL hα u‖ := by
  -- The time derivatives cancel, leaving the coefficient error and the lower-order terms.
  have heq : parabolicOperatorL hα A B C u -
      parabolicOperatorL hα (HolderSpace.const (A z₀)) 0 0 u =
      (ContinuousLinearMap.id ℝ _).compHolder₂ (HolderSpace.const (A z₀) - A)
          (spatialSecondFDerivL u) -
        ((ContinuousLinearMap.id ℝ _).compHolder₂ B (spatialFDerivHolderL hα u) +
          (ContinuousLinearMap.id ℝ _).compHolder₂ C (valueHolderL hα u)) := by
    ext p
    simp only [HolderSpace.sub_apply, parabolicOperatorL_apply, HolderSpace.const_apply,
      HolderSpace.zero_apply, _root_.zero_apply, add_zero,
      ContinuousLinearMap.compHolder₂_apply, ContinuousLinearMap.id_apply,
      _root_.sub_apply, HolderSpace.add_apply, spatialFDerivHolderL_apply,
      valueHolderL_apply]
    abel
  have hA : HolderWith (nnHolderNorm α ⇑A) α
      (HolderSpace.const (A z₀) - A : HolderSpace α (slab (E := E) t₀ t₁) _) := by
    have h : HolderWith (nnHolderNorm α ⇑A) α ⇑A := by simpa using A.memHolder.holderWith
    intro x y
    simpa only [HolderSpace.sub_apply, HolderSpace.const_apply, edist_sub_left] using h x y
  have hfrozen := ContinuousLinearMap.norm_compHolder₂_apply_le_of_norm_le
    (ContinuousLinearMap.id ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)) hA (g := spatialSecondFDerivL u)
      (δ := δ) (fun p hp ↦ by
        simpa only [HolderSpace.sub_apply, HolderSpace.const_apply, norm_sub_rev] using hδ p hp)
  -- The bound for the coefficient error is nonnegative: `δ ≥ 0` unless the Hessian vanishes.
  have hnonneg : 0 ≤ δ * ‖spatialSecondFDerivL u‖ +
      nnHolderNorm α ⇑A * ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ := by
    by_cases h : spatialSecondFDerivL u = 0
    · simp [h]
    obtain ⟨p, hp⟩ : ∃ p, spatialSecondFDerivL u p ≠ 0 := by
      by_contra! h'
      exact h (HolderSpace.ext fun p ↦ by simpa using h' p)
    have := (norm_nonneg _).trans (hδ p hp)
    positivity
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((hfrozen.trans (mul_le_of_le_one_left hnonneg
    ContinuousLinearMap.norm_id_le))) ((norm_add_le _ _).trans (add_le_add
      (ContinuousLinearMap.norm_id_compHolder₂_apply_le B _)
      (ContinuousLinearMap.norm_id_compHolder₂_apply_le C _)))).trans_eq ?_
  ring

/-- Where the Hessian of `u` does not vanish, the coefficient `A` is within `L r^α` of `A(z₀)`,
if the Hessian vanishes outside the closed parabolic ball of radius `r` about `z₀` and `L`
bounds `[A]_α`. -/
private theorem norm_sub_le_of_spatialSecondFDerivL_eq_zero
    (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F)) {L : ℝ}
    (hA : (nnHolderNorm α ⇑A : ℝ) ≤ L) (u : ParabolicC2HolderSpace α E F ht)
    (z₀ : slab (E := E) t₀ t₁) {r : ℝ}
    (hu : ∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) (p : slab (E := E) t₀ t₁)
    (hp : spatialSecondFDerivL u p ≠ 0) : ‖A p - A z₀‖ ≤ L * r ^ (α : ℝ) := by
  have h : HolderWith (nnHolderNorm α ⇑A) α ⇑A := by simpa using A.memHolder.holderWith
  have hpr : dist p z₀ ≤ r := not_lt.1 fun h ↦ hp (hu p h)
  rw [← dist_eq_norm]
  exact (h.dist_le p z₀).trans (mul_le_mul hA
    (Real.rpow_le_rpow dist_nonneg hpr α.2) (by positivity) ((NNReal.coe_nonneg _).trans hA))

/-- **The absorbed freezing estimate.** Let `0 < α < 1` and `η > 0`. There is `K`, depending only
on `α`, `η`, `L` and `M`, with the following property. Let `[A]_α ≤ L` and `‖B‖ + ‖C‖ ≤ M`, and
let the Hessian of `u` vanish outside the closed parabolic ball of radius `r` about `z₀`. Then,
with `P_{z₀} = ∂ₜ - A(z₀)·D_x²`,

`‖P u - P_{z₀} u‖_{α,par} ≤ (L r^α + η) ‖u‖_{2+α,par} + K ‖u‖_∞`.

The constant does not depend on the slab, the coefficients, the point `z₀` or the radius `r`. -/
theorem exists_norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le (hα₀ : 0 < α)
    (hα : α < 1) {L M η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁}
      (A : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
      (B : HolderSpace α (slab (E := E) t₀ t₁) ((E →L[ℝ] F) →L[ℝ] F))
      (C : HolderSpace α (slab (E := E) t₀ t₁) (F →L[ℝ] F)),
      (nnHolderNorm α ⇑A : ℝ) ≤ L → ‖B‖ + ‖C‖ ≤ M →
      ∀ (u : ParabolicC2HolderSpace α E F ht) (z₀ : slab (E := E) t₀ t₁) {r : ℝ}, 0 ≤ r →
        (∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) →
        ‖parabolicOperatorL hα.le A B C u -
            parabolicOperatorL hα.le (HolderSpace.const (A z₀)) 0 0 u‖ ≤
          (L * r ^ (α : ℝ) + η) * ‖u‖ + K * ‖valueL u‖ := by
  set L' := max L 0
  set M' := max M 0
  -- The lower-order terms: absorption with the small factor `η / (2 (M' + 1))`.
  obtain ⟨C₁, hC₁⟩ := exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le (E := E) (F := F)
    hα (η := η / (2 * (M' + 1))) (by positivity)
  -- The supremum of the Hessian: interpolation at the scale `ε` with `2 L' ε^α ≤ η / 2`.
  set ε : ℝ := (η / (4 * (L' + 1))) ^ (α : ℝ)⁻¹
  have hε : 0 < ε := by positivity
  have hεα : ε ^ (α : ℝ) = η / (4 * (L' + 1)) :=
    Real.rpow_inv_rpow (by positivity) (by exact_mod_cast hα₀.ne')
  refine ⟨32 * L' / ε ^ 2 + M' * max C₁ 0, fun A B C hAL hBC u z₀ r hr hu ↦ ?_⟩
  have hL' : 0 ≤ L' := le_max_right _ _
  have hM' : 0 ≤ M' := le_max_right _ _
  have hAL' : (nnHolderNorm α ⇑A : ℝ) ≤ L' := hAL.trans (le_max_left _ _)
  have hL : 0 ≤ L := (NNReal.coe_nonneg _).trans hAL
  have hD2 := norm_spatialSecondFDerivL_le u
  have hu₀ := norm_valueL_le u
  have hsemi := (spatialSecondFDerivL u).nnHolderNorm_le
  have hsup := norm_toBoundedContinuousFunction_spatialSecondFDerivL_le u hε
  have hfreeze := norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le hα.le A B C u z₀
    (norm_sub_le_of_spatialSecondFDerivL_eq_zero A hAL u z₀ hu)
  -- The three error terms, each against its share of the right-hand side.
  have h₁ : L * r ^ (α : ℝ) * ‖spatialSecondFDerivL u‖ ≤ L * r ^ (α : ℝ) * ‖u‖ := by
    gcongr
  have h₂ : nnHolderNorm α ⇑A * ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ ≤
      η / 2 * ‖u‖ + 32 * L' / ε ^ 2 * ‖valueL u‖ := by
    have hsup' : ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ ≤
        32 * ‖valueL u‖ / ε ^ 2 + 2 * ‖u‖ * ε ^ (α : ℝ) :=
      hsup.trans (by gcongr; exact hsemi.trans hD2)
    have hsmall : L' * (2 * ‖u‖ * ε ^ (α : ℝ)) ≤ η / 2 * ‖u‖ := by
      rw [hεα, show L' * (2 * ‖u‖ * (η / (4 * (L' + 1)))) = L' / (L' + 1) * (η / 2 * ‖u‖) by
        field_simp; ring]
      exact mul_le_of_le_one_left (by positivity)
        ((div_le_one (by positivity)).2 (by linarith))
    calc _ ≤ L' * ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ := by gcongr
      _ ≤ L' * (32 * ‖valueL u‖ / ε ^ 2 + 2 * ‖u‖ * ε ^ (α : ℝ)) := by gcongr
      _ ≤ _ := by rw [mul_add]; linarith [show L' * (32 * ‖valueL u‖ / ε ^ 2) =
            32 * L' / ε ^ 2 * ‖valueL u‖ by ring]
  have h₃ : ‖B‖ * ‖spatialFDerivHolderL hα.le u‖ + ‖C‖ * ‖valueHolderL hα.le u‖ ≤
      η / 2 * ‖u‖ + M' * max C₁ 0 * ‖valueL u‖ := by
    have hlow := hC₁ u
    have hX : 0 ≤ ‖valueHolderL hα.le u‖ + ‖spatialFDerivHolderL hα.le u‖ := by positivity
    have hBC' : ‖B‖ + ‖C‖ ≤ M' := hBC.trans (le_max_left _ _)
    calc _ ≤ (‖B‖ + ‖C‖) * (‖valueHolderL hα.le u‖ + ‖spatialFDerivHolderL hα.le u‖) := by
          nlinarith [norm_nonneg B, norm_nonneg C, norm_nonneg (valueHolderL hα.le u),
            norm_nonneg (spatialFDerivHolderL hα.le u)]
      _ ≤ M' * (η / (2 * (M' + 1)) * ‖u‖ + C₁ * ‖valueL u‖) :=
          mul_le_mul hBC' hlow hX hM'
      _ ≤ M' * (η / (2 * (M' + 1)) * ‖u‖ + max C₁ 0 * ‖valueL u‖) := by
          gcongr
          exact le_max_left _ _
      _ ≤ _ := by
          have : M' * (η / (2 * (M' + 1))) ≤ η / 2 := by
            rw [show M' * (η / (2 * (M' + 1))) = M' / (M' + 1) * (η / 2) by field_simp]
            exact mul_le_of_le_one_left (by positivity)
              ((div_le_one (by positivity)).2 (by linarith))
          nlinarith [norm_nonneg u, norm_nonneg (valueL u)]
  linarith

/-! ### Scalar coefficients on Euclidean space -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The absorbed freezing estimate for scalar coefficients on `ℝⁿ`.** Let `0 < α < 1` and
`η > 0`. There is `K`, depending only on `α`, `η`, `L`, `M` and `ι`, with the following property.
Let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` have coefficients in `C_b^{α,α/2}(ℝⁿ × [t₀, t₁])`
with `∑ᵢⱼ [aⁱʲ]_α ≤ L` and `∑ᵢ ‖bⁱ‖ + ‖c‖ ≤ M`, and let the Hessian of `u` vanish outside the
closed parabolic ball of radius `r` about `z₀`. Then, with the constant-coefficient operator
`P_{z₀} u = ∂ₜu - aⁱʲ(z₀) ∂ᵢ∂ⱼu`,

`‖P u - P_{z₀} u‖_{α,par} ≤ (L r^α + η) ‖u‖_{2+α,par} + K ‖u‖_∞`. -/
theorem exists_norm_euclideanParabolicOperatorL_sub_euclideanParabolicOperatorL_const_apply_le
    (hα₀ : 0 < α) (hα : α < 1) {L M η : ℝ} (hη : 0 < η) :
    ∃ K : ℝ, ∀ {t₀ t₁ : ℝ} {ht : t₀ < t₁}
      (a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
      (b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ)
      (c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) t₀ t₁) ℝ),
      ∑ i, ∑ j, (nnHolderNorm α ⇑(a i j) : ℝ) ≤ L → ∑ i, ‖b i‖ + ‖c‖ ≤ M →
      ∀ (u : ParabolicC2HolderSpace α (EuclideanSpace ℝ ι) ℝ ht)
        (z₀ : slab (E := EuclideanSpace ℝ ι) t₀ t₁) {r : ℝ}, 0 ≤ r →
        (∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) →
        ‖euclideanParabolicOperatorL hα.le a b c u -
            euclideanParabolicOperatorL hα.le (fun i j ↦ HolderSpace.const (a i j z₀)) 0 0 u‖ ≤
          (L * r ^ (α : ℝ) + η) * ‖u‖ + K * ‖valueL u‖ := by
  obtain ⟨K, hK⟩ := exists_norm_parabolicOperatorL_sub_parabolicOperatorL_const_apply_le
    (E := EuclideanSpace ℝ ι) (F := ℝ) hα₀ hα (L := L) (M := M) hη
  refine ⟨K, fun {t₀ t₁ ht} a b c ha hbc u z₀ r hr hu ↦ ?_⟩
  -- The operator frozen at `z₀` is the one with the frozen coefficient field.
  have hfrozen : euclideanParabolicOperatorL (ht := ht) hα.le
      (fun i j ↦ HolderSpace.const (a i j z₀)) 0 0 =
      parabolicOperatorL hα.le (HolderSpace.const (euclideanSecondOrderCoeff a z₀)) 0 0 :=
    ContinuousLinearMap.ext fun v ↦ HolderSpace.ext fun p ↦ by
      simp [euclideanParabolicOperatorL_apply, parabolicOperatorL_apply]
  have hA : (nnHolderNorm α ⇑(euclideanSecondOrderCoeff a) : ℝ) ≤ L := by
    refine (NNReal.coe_le_coe.2 (holderWith_euclideanSecondOrderCoeff a).nnholderNorm_le).trans ?_
    simpa only [NNReal.coe_sum] using ha
  rw [hfrozen, euclideanParabolicOperatorL_def]
  exact hK _ _ _ hA ((add_le_add (norm_euclideanFirstOrderCoeff_le b)
    (norm_euclideanZerothOrderCoeff_le c)).trans hbc) u z₀ hr hu

end Euclidean

end TauCeti.ParabolicC2HolderSpace

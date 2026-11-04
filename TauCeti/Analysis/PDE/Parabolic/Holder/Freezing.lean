/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Operator

/-!
# Freezing the principal coefficient of a parabolic operator

Let `A` be a principal coefficient field in the bounded parabolic Hölder space `C_b^{α,α/2}` on
the slab `E × [a, b]`, with values in the continuous linear maps on Hessians, and let `u` be in
the order-two space `C_b^{2+α,1+α/2}`. Freezing `A` at a constant `A₀` changes the parabolic
operator `P u = ∂ₜu - A·D_x²u - B·D_xu - C·u` by the principal error `(A - A₀)·D_x²u`, which is
`spatialOperatorL hα (A - A₀) 0 0 u` (see `parabolicOperatorL_sub_parabolicOperatorL`). This file
bounds that error in the norm of `C_b^{α,α/2}`.

If `‖A - A₀‖ ≤ δ` wherever `D_x²u` does not vanish, then

`‖(A - A₀)·D_x²u‖_{α,par} ≤ δ ‖D_x²u‖_{α,par} + [A]_{α,par} ‖D_x²u‖_∞`.

When `D_x²u` vanishes outside the closed parabolic ball of radius `r` about `z₀` and `A` is frozen
at `A₀ = A(z₀)`, the Hölder bound on `A` gives `δ = [A]_{α,par} r^α`. Combined with the
interpolation inequality for the Hessian, for every `ε > 0` this becomes

`‖(A - A(z₀))·D_x²u‖_{α,par} ≤ [A]_{α,par} ((r^α + 2 ε^α) ‖u‖ + 32 ε⁻² ‖u‖_∞)`,

where `‖u‖` is the order-two norm. Hence for `α > 0`, every bound `K` on `[A]_{α,par}` and every
`η > 0` there are a radius `r₀ > 0` and a constant `C`, depending only on `α`, `K` and `η`, such
that the frozen error is at most `η ‖u‖ + C ‖u‖_∞` whenever `r ≤ r₀`. The constants are independent
of the centre `z₀`, the slab and the spaces `E` and `F`. This is the freezing step of the
localization argument for parabolic Schauder estimates with variable coefficients: the
constant-coefficient estimate is applied to `u` localized near `z₀`, and the frozen error is
absorbed.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.norm_spatialOperatorL_sub_const_le`: the error of freezing a
  coefficient of small oscillation on the support of the Hessian.
* `TauCeti.ParabolicC2HolderSpace.norm_spatialOperatorL_sub_const_apply_le` and
  `TauCeti.ParabolicC2HolderSpace.norm_spatialOperatorL_sub_const_apply_le_add`: the error of
  freezing at the centre of a parabolic ball containing the support of the Hessian, before and
  after interpolation.
* `TauCeti.ParabolicC2HolderSpace.exists_norm_spatialOperatorL_sub_const_apply_le`: the absorbable
  form, with a radius and constant uniform in the centre and the slab.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (freezing the coefficients in the interior Schauder estimate).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A local shortcut for the norm on Hessians. Without it, instance search for the operator norm on
`(E →L[ℝ] E →L[ℝ] F) →L[ℝ] F`, the coefficient space of the second-order term, fails: the norm
instance on its domain only arises as a nested instance problem during unification. -/
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on Hessians, needed for the same reason. -/
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- With vanishing lower-order coefficients the spatial operator is its principal part. -/
private theorem spatialOperatorL_zero_zero (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (u : ParabolicC2HolderSpace α E F hab) :
    spatialOperatorL hα A 0 0 u =
      (ContinuousLinearMap.id ℝ _).compHolder₂ A (spatialSecondFDerivL u) := by
  ext p
  simp

/-- **Freezing a coefficient of small oscillation.** If `‖A - A₀‖ ≤ δ` wherever the Hessian of
`u` does not vanish, then
`‖(A - A₀)·D_x²u‖_{α,par} ≤ δ ‖D_x²u‖_{α,par} + [A]_{α,par} ‖D_x²u‖_∞`. -/
theorem norm_spatialOperatorL_sub_const_le (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (A₀ : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F) (u : ParabolicC2HolderSpace α E F hab) {δ : ℝ≥0}
    (hδ : ∀ p, spatialSecondFDerivL u p ≠ 0 → ‖A p - A₀‖ ≤ δ) :
    ‖spatialOperatorL hα (A - HolderSpace.const A₀) 0 0 u‖ ≤
      δ * ‖spatialSecondFDerivL u‖ + nnHolderNorm α (A : slab (E := E) a b → _) *
        ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖ := by
  rw [spatialOperatorL_zero_zero]
  have h := ContinuousLinearMap.norm_compHolder₂_apply_le_of_eq_zero (ContinuousLinearMap.id ℝ _)
    (A - HolderSpace.const A₀) (spatialSecondFDerivL u)
    (s := {p | spatialSecondFDerivL u p ≠ 0}) (δ := δ) (fun p hp ↦ by simpa using hδ p hp)
    (fun p hp ↦ by simpa using hp)
  -- Subtracting a constant does not change the Hölder seminorm.
  have hA : nnHolderNorm α ((A - HolderSpace.const A₀ : HolderSpace α _ _) :
      slab (E := E) a b → _) ≤ nnHolderNorm α (A : slab (E := E) a b → _) :=
    HolderWith.nnholderNorm_le fun p q ↦ by
      simpa [edist_sub_right] using A.memHolder.holderWith p q
  refine h.trans ?_
  calc
    _ ≤ 1 * (δ * ‖spatialSecondFDerivL u‖ + nnHolderNorm α (A : slab (E := E) a b → _) *
          ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖) := by
      gcongr
      exact ContinuousLinearMap.norm_id_le
    _ = _ := one_mul _

/-- **Freezing at the centre of a parabolic ball.** If the Hessian of `u` vanishes outside the
closed parabolic ball of radius `r` about `z₀`, then
`‖(A - A(z₀))·D_x²u‖_{α,par} ≤ [A]_{α,par} (r^α ‖D_x²u‖_{α,par} + ‖D_x²u‖_∞)`. -/
theorem norm_spatialOperatorL_sub_const_apply_le (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (z₀ : slab (E := E) a b) (u : ParabolicC2HolderSpace α E F hab) {r : ℝ}
    (hu : ∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) :
    ‖spatialOperatorL hα (A - HolderSpace.const (A z₀)) 0 0 u‖ ≤
      nnHolderNorm α (A : slab (E := E) a b → _) * (r ^ (α : ℝ) * ‖spatialSecondFDerivL u‖ +
        ‖(spatialSecondFDerivL u).toBoundedContinuousFunction‖) := by
  rcases lt_or_ge r 0 with hr | hr
  · -- For a negative radius the Hessian vanishes identically.
    have h0 : spatialSecondFDerivL u = 0 :=
      HolderSpace.ext fun p ↦ hu p (hr.trans_le dist_nonneg)
    simp [spatialOperatorL_zero_zero, h0]
  have hrα : ((r.toNNReal ^ (α : ℝ) : ℝ≥0) : ℝ) = r ^ (α : ℝ) := by
    rw [NNReal.coe_rpow, Real.coe_toNNReal r hr]
  refine (norm_spatialOperatorL_sub_const_le hα A (A z₀) u
    (δ := nnHolderNorm α (A : slab (E := E) a b → _) * r.toNNReal ^ (α : ℝ))
    fun p hp ↦ ?_).trans_eq ?_
  · have hd : dist p z₀ ≤ r := not_lt.1 fun h ↦ hp (hu p h)
    have hA := A.memHolder.holderWith.dist_le p z₀
    simp only [HolderSpace.coe_toBoundedContinuousFunction,
      HolderSpace.toBoundedContinuousFunction_apply] at hA
    rw [← dist_eq_norm, NNReal.coe_mul, hrα]
    exact hA.trans (by gcongr)
  · rw [NNReal.coe_mul, hrα]
    ring

/-- **Freezing at the centre of a parabolic ball, after interpolation.** If the Hessian of `u`
vanishes outside the closed parabolic ball of radius `r` about `z₀`, then for every `ε > 0`
`‖(A - A(z₀))·D_x²u‖_{α,par} ≤ [A]_{α,par} ((r^α + 2 ε^α) ‖u‖ + 32 ε⁻² ‖u‖_∞)`. -/
theorem norm_spatialOperatorL_sub_const_apply_le_add (hα : α ≤ 1)
    (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
    (z₀ : slab (E := E) a b) (u : ParabolicC2HolderSpace α E F hab) {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) {ε : ℝ} (hε : 0 < ε) :
    ‖spatialOperatorL hα (A - HolderSpace.const (A z₀)) 0 0 u‖ ≤
      nnHolderNorm α (A : slab (E := E) a b → _) *
        ((r ^ (α : ℝ) + 2 * ε ^ (α : ℝ)) * ‖u‖ + 32 * ‖valueL u‖ / ε ^ 2) := by
  have hH := norm_spatialSecondFDerivL_le u
  have hsemi := (HolderSpace.nnHolderNorm_le (spatialSecondFDerivL u)).trans hH
  have hsup := norm_toBoundedContinuousFunction_spatialSecondFDerivL_le u hε
  refine (norm_spatialOperatorL_sub_const_apply_le hα A z₀ u hu).trans ?_
  have hrα : 0 ≤ r ^ (α : ℝ) := by positivity
  have hεα : 0 ≤ ε ^ (α : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left hH hrα, mul_le_mul_of_nonneg_left hsemi hεα]

/-- **Absorbable freezing error.** For `0 < α ≤ 1`, a bound `K` on the Hölder seminorm of the
principal coefficient and every `η > 0`, there are a radius `r₀ > 0` and a constant `C`, depending
only on `α`, `K` and `η`, with the following property. On every slab, for every coefficient field
`A` with `[A]_{α,par} ≤ K`, every centre `z₀` and every `u` whose Hessian vanishes outside the
closed parabolic ball of radius `r ≤ r₀` about `z₀`,
`‖(A - A(z₀))·D_x²u‖_{α,par} ≤ η ‖u‖ + C ‖u‖_∞`. -/
theorem exists_norm_spatialOperatorL_sub_const_apply_le (hα₀ : 0 < α) (hα : α ≤ 1) (K : ℝ≥0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r₀ > 0, ∃ C : ℝ, ∀ {a b : ℝ} {hab : a < b}
      (A : HolderSpace α (slab (E := E) a b) ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] F))
      (z₀ : slab (E := E) a b) (u : ParabolicC2HolderSpace α E F hab) {r : ℝ},
      nnHolderNorm α (A : slab (E := E) a b → _) ≤ K → 0 ≤ r → r ≤ r₀ →
      (∀ p, r < dist p z₀ → spatialSecondFDerivL u p = 0) →
      ‖spatialOperatorL hα (A - HolderSpace.const (A z₀)) 0 0 u‖ ≤
        η * ‖u‖ + C * ‖valueL u‖ := by
  have hα₀' : (0 : ℝ) < α := by exact_mod_cast hα₀
  -- Take `r₀ = ε = t` with `3 K t^α ≤ η`.
  set t := (η / (3 * (K + 1))) ^ (α : ℝ)⁻¹ with ht_def
  have ht : 0 < t := by positivity
  have htα : t ^ (α : ℝ) = η / (3 * (K + 1)) := by
    rw [ht_def, Real.rpow_inv_rpow (by positivity) hα₀'.ne']
  refine ⟨t, ht, K * 32 / t ^ 2, fun A z₀ u r hA hr hrt hu ↦ ?_⟩
  refine (norm_spatialOperatorL_sub_const_apply_le_add hα A z₀ u hr hu ht).trans ?_
  have hrα : r ^ (α : ℝ) ≤ t ^ (α : ℝ) := by gcongr
  have hK : (K : ℝ) * (3 * t ^ (α : ℝ)) ≤ η := by
    rw [htα, mul_div_assoc', mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [K.coe_nonneg]
  have hu₀ := norm_nonneg u
  have hv₀ := norm_nonneg (valueL u)
  have hA' := NNReal.coe_le_coe.2 hA
  calc
    _ ≤ (K : ℝ) * ((t ^ (α : ℝ) + 2 * t ^ (α : ℝ)) * ‖u‖ + 32 * ‖valueL u‖ / t ^ 2) := by
      gcongr
    _ = (K : ℝ) * (3 * t ^ (α : ℝ)) * ‖u‖ + K * 32 / t ^ 2 * ‖valueL u‖ := by ring
    _ ≤ η * ‖u‖ + K * 32 / t ^ 2 * ‖valueL u‖ := by gcongr

end TauCeti.ParabolicC2HolderSpace

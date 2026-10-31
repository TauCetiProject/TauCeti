/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Two
public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Interpolation

/-!
# Interpolation and absorption in order-two parabolic Hölder spaces

For `u` in the bounded order-two parabolic Hölder space `ParabolicC2HolderSpace α E F hab` on the
slab `E × [a, b]`, this file proves the supremum-norm interpolation inequalities

* `‖D_x u‖_∞ ≤ 2 ε⁻¹ ‖u‖_∞ + ε ‖D_x² u‖_∞` for every `ε > 0`;
* `‖D_x² u‖_∞ ≤ 32 ε⁻² ‖u‖_∞ + 2 ε^α [D_x² u]_{α,par}` for every `ε > 0`;
* `‖∂ₜ u‖_∞ ≤ 2 ε⁻² ‖u‖_∞ + ε^α [∂ₜ u]_{α,par}` for every `ε > 0` with `2 ε² ≤ b - a`.

The first two are the whole-space spatial interpolation inequalities applied to each time slice,
using that at a common time the parabolic distance is the spatial distance. The third is the
interpolation inequality on the interval `[a, b]` applied to each spatial position, with the
temporal step `ε²`, using that at a common position the parabolic `α`-seminorm controls the
temporal `α / 2`-seminorm.

For `α ≤ 1`, the value `u` and the spatial gradient `D_x u` are parabolically `α`-Hölder, so they
define bounded linear maps `valueHolderL` and `spatialFDerivHolderL` into the bounded parabolic
Hölder space `C_b^{α,α/2}`. Their norms satisfy the absorption inequality

`‖u‖_{α,par} + ‖D_x u‖_{α,par} ≤ 7 ε^(1 - α) ‖u‖ + 17 ε^(-(1 + α)) ‖u‖_∞`

for `0 < ε ≤ 1`, where `‖u‖` is the order-two norm. For `α < 1` this gives, for every `η > 0`,
`‖u‖_{α,par} + ‖D_x u‖_{α,par} ≤ η ‖u‖ + C ‖u‖_∞` with `C` depending only on `α` and `η`. All
constants are independent of the spaces `E`, `F` and of the slab. These are the estimates used to
absorb lower-order terms in parabolic Schauder estimates.

## Main declarations

* `TauCeti.ParabolicC2HolderSpace.norm_spatialFDerivL_le`,
  `TauCeti.ParabolicC2HolderSpace.norm_toBoundedContinuousFunction_spatialSecondFDerivL_le` and
  `TauCeti.ParabolicC2HolderSpace.norm_toBoundedContinuousFunction_timeDerivL_le`: the three
  interpolation inequalities.
* `TauCeti.ParabolicC2HolderSpace.valueHolderL` and
  `TauCeti.ParabolicC2HolderSpace.spatialFDerivHolderL`: the value and the spatial gradient as
  continuous linear maps into the bounded parabolic Hölder space.
* `TauCeti.ParabolicC2HolderSpace.norm_valueHolderL_add_norm_spatialFDerivHolderL_le` and
  `TauCeti.ParabolicC2HolderSpace.exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le`:
  the absorption of the lower-order parabolic Hölder norms.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ParabolicC2HolderSpace

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-! ### Supremum-norm interpolation -/

/-- **Interpolation inequality for the spatial gradient.** For every `ε > 0`,
`‖D_x u‖_∞ ≤ 2 ‖u‖_∞ / ε + ‖D_x² u‖_∞ ε`. -/
theorem norm_spatialFDerivL_le (f : ParabolicC2HolderSpace α E F hab) {ε : ℝ} (hε : 0 < ε) :
    ‖spatialFDerivL f‖ ≤
      2 * ‖valueL f‖ / ε + ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ * ε := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- Each gradient slice is Lipschitz, with the supremum of the Hessian as constant.
  have hlip : HolderWith ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖₊ 1
      fun y ↦ spatialFDerivL f (slabMk y t) := by
    refine holderWith_one.2 (lipschitzWith_of_nnnorm_fderiv_le
      (fun y ↦ (f.hasSpatialSecondFDerivAt t y).differentiableAt) fun y ↦ ?_)
    rw [f.fderiv_spatialFDeriv_eq, ← HolderSpace.toBoundedContinuousFunction_apply]
    exact BoundedContinuousFunction.nnnorm_coe_le_nnnorm _ _
  simpa using hlip.norm_le_of_hasFDerivAt (f.hasSpatialFDerivAt t)
    (fun y ↦ (valueL f).norm_coe_le_norm (slabMk y t)) hε x

/-- **Interpolation inequality for the spatial Hessian.** For every `ε > 0`,
`‖D_x² u‖_∞ ≤ 32 ‖u‖_∞ / ε² + 2 [D_x² u]_{α,par} ε^α`. -/
theorem norm_toBoundedContinuousFunction_spatialSecondFDerivL_le
    (f : ParabolicC2HolderSpace α E F hab) {ε : ℝ} (hε : 0 < ε) :
    ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ ≤ 32 * ‖valueL f‖ / ε ^ 2 +
      2 * nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) *
        ε ^ (α : ℝ) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- Each time slice is `C²`, with the gradient and Hessian fields as derivatives.
  have hf : ContDiff ℝ 2 fun y ↦ f (slabMk y t) := by
    refine (contDiff_succ_iff_hasFDerivAt (n := 1)).2
      ⟨fun y ↦ spatialFDerivL f (slabMk y t), ?_, f.hasSpatialFDerivAt t⟩
    refine (contDiff_succ_iff_hasFDerivAt (n := 0)).2
      ⟨fun y ↦ spatialSecondFDerivL f (slabMk y t), ?_, f.hasSpatialSecondFDerivAt t⟩
    exact contDiff_zero.2 ((spatialSecondFDerivL f).continuous.comp
      (continuous_slabMk.comp (continuous_id.prodMk continuous_const)))
  -- At a common time the parabolic distance is the spatial one, so the second iterated
  -- derivative of each slice is `α`-Hölder with the parabolic seminorm as constant.
  have hH : HolderWith (nnHolderNorm α
      ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _)) α
      (iteratedFDeriv ℝ 2 fun y ↦ f (slabMk y t)) := by
    let e := (continuousMultilinearCurryFin1 ℝ E (E →L[ℝ] F)).symm.trans
      (continuousMultilinearCurryRightEquiv' ℝ 1 E F).symm
    have he : (iteratedFDeriv ℝ 2 fun y ↦ f (slabMk y t)) =
        fun y ↦ e (spatialSecondFDerivL f (slabMk y t)) := by
      funext y
      ext m
      simp [e, f.iteratedFDeriv_two_apply, Fin.init]
    rw [he]
    intro y z
    simpa [edist_slabMk] using
      (spatialSecondFDerivL f).memHolder.holderWith (slabMk y t) (slabMk z t)
  -- The absorbed whole-space interpolation inequality for the slice.
  have h := hH.norm_iteratedFDeriv_add_two_le_of_norm_le (k := 0) hf
    (fun y ↦ by simpa using (valueL f).norm_coe_le_norm (slabMk y t))
    ⟨‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖, by
      rintro _ ⟨y, rfl⟩
      -- Normalize the derivative order `0 + 2` to `2` (definitionally, since the order occurs
      -- in the type of the multilinear map and cannot be rewritten) so that
      -- `norm_iteratedFDeriv_two` applies.
      change ‖iteratedFDeriv ℝ 2 _ y‖ ≤ _
      rw [f.norm_iteratedFDeriv_two, ← HolderSpace.toBoundedContinuousFunction_apply]
      exact BoundedContinuousFunction.norm_coe_le_norm _ _⟩ hε x
  -- As above, normalize `0 + 2` to `2` so that `norm_iteratedFDeriv_two` rewrites the
  -- slice Hessian to the spatial second derivative.
  change ‖iteratedFDeriv ℝ 2 _ x‖ ≤ _ at h
  rwa [f.norm_iteratedFDeriv_two, ← HolderSpace.toBoundedContinuousFunction_apply] at h

/-- **Interpolation inequality for the time derivative.** For every `ε > 0` with
`2 ε² ≤ b - a`, that is `ε ≤ √((b - a) / 2)`,
`‖∂ₜ u‖_∞ ≤ 2 ‖u‖_∞ / ε² + [∂ₜ u]_{α,par} ε^α`. -/
theorem norm_toBoundedContinuousFunction_timeDerivL_le (f : ParabolicC2HolderSpace α E F hab)
    {ε : ℝ} (hε : 0 < ε) (hεab : 2 * ε ^ 2 ≤ b - a) :
    ‖(timeDerivL f).toBoundedContinuousFunction‖ ≤ 2 * ‖valueL f‖ / ε ^ 2 +
      nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _) * ε ^ (α : ℝ) := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  -- At a common position the parabolic `α`-seminorm controls the temporal `α / 2`-seminorm.
  have hH : HolderOnWith (nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _))
      (α / 2) (timeExtension hab.le (timeDerivL f) x) (Icc a b) := fun s hs s' hs' ↦ by
    have h := (timeDerivL f).memHolder.holderWith (slabMk x ⟨s, hs⟩) (slabMk x ⟨s', hs'⟩)
    rw [edist_slabMk_same_space_rpow] at h
    simpa [timeExtension_def, projIcc_of_mem hab.le hs, projIcc_of_mem hab.le hs'] using h
  have hderiv : ∀ s ∈ Icc a b, HasDerivWithinAt (timeExtension hab.le f x)
      (timeExtension hab.le (timeDerivL f) x s) (Icc a b) s := fun s hs ↦ by
    simpa [timeExtension_def, projIcc_of_mem hab.le hs] using f.hasTimeDerivWithinAt x ⟨s, hs⟩
  have hM : ∀ s ∈ Icc a b, ‖timeExtension hab.le f x s‖ ≤ ‖valueL f‖ := fun s _ ↦ by
    rw [timeExtension_def]
    exact (valueL f).norm_coe_le_norm _
  -- Interpolate in time with the step `ε²`.
  have h := hH.norm_le_of_hasDerivWithinAt_Icc hderiv hM (by positivity) hεab t.2
  have hpow : (ε ^ 2) ^ ((α / 2 : ℝ≥0) : ℝ) = ε ^ (α : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  rwa [hpow, timeExtension_of_mem, ← HolderSpace.toBoundedContinuousFunction_apply] at h

/-! ### Lower-order parabolic Hölder norms -/

/-- The parabolic seminorms of the value and of the spatial gradient, bounded by the existing
absorption estimate on slabs. -/
private theorem eHolderNorm_valueL_add_eHolderNorm_spatialFDerivL_le (hα : α ≤ 1)
    (f : ParabolicC2HolderSpace α E F hab) {ε : ℝ≥0} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    eHolderNorm α (valueL f : slab (E := E) a b → F) +
        eHolderNorm α (spatialFDerivL f : slab (E := E) a b → E →L[ℝ] F) ≤
      ↑(6 * ε ^ (1 - (α : ℝ)) *
          (‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖₊ +
            ‖(timeDerivL f).toBoundedContinuousFunction‖₊ +
            nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) +
            nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _)) +
        14 * ε ^ (-(1 + (α : ℝ))) * ‖valueL f‖₊) := by
  have hx : ∀ t ∈ Icc a b, ∀ y,
      HasFDerivAt (fun z ↦ timeExtension hab.le f z t)
        (timeExtension hab.le (spatialFDerivL f) y t) y := by
    intro t ht y
    simpa [timeExtension_def, projIcc_of_mem hab.le ht] using f.hasSpatialFDerivAt ⟨t, ht⟩ y
  have hxx : ∀ t ∈ Icc a b, ∀ y,
      HasFDerivAt (fun z ↦ timeExtension hab.le (spatialFDerivL f) z t)
        (timeExtension hab.le (spatialSecondFDerivL f) y t) y := by
    intro t ht y
    simpa [timeExtension_def, projIcc_of_mem hab.le ht] using
      f.hasSpatialSecondFDerivAt ⟨t, ht⟩ y
  have ht : ∀ y, ∀ t ∈ Icc a b,
      HasDerivWithinAt (timeExtension hab.le f y)
        (timeExtension hab.le (timeDerivL f) y t) (Icc a b) t := by
    intro y t ht
    simpa [timeExtension_def, projIcc_of_mem hab.le ht] using f.hasTimeDerivWithinAt y ⟨t, ht⟩
  have h := ParabolicSpaceTime.eHolderNorm_add_eHolderNorm_le hα hε hε₁ hx hxx ht
    (M₀ := ‖valueL f‖₊) (M₂ := ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖₊)
    (Mₜ := ‖(timeDerivL f).toBoundedContinuousFunction‖₊)
    (H₂ := nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _))
    (Hₜ := nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _))
    (fun y t _ ↦ by
      rw [timeExtension_def, coe_nnnorm]
      exact (valueL f).norm_coe_le_norm _)
    (fun y t _ ↦ by
      simpa only [timeExtension_def, HolderSpace.toBoundedContinuousFunction_apply, coe_nnnorm]
        using (spatialSecondFDerivL f).toBoundedContinuousFunction.norm_coe_le_norm _)
    (fun y t _ ↦ by
      simpa only [timeExtension_def, HolderSpace.toBoundedContinuousFunction_apply, coe_nnnorm]
        using (timeDerivL f).toBoundedContinuousFunction.norm_coe_le_norm _)
    (by
      rw [timeExtension_space_slabTime, ← HolderSpace.coe_toBoundedContinuousFunction,
        (spatialSecondFDerivL f).memHolder.coe_nnHolderNorm_eq_eHolderNorm])
    (by
      rw [timeExtension_space_slabTime, ← HolderSpace.coe_toBoundedContinuousFunction,
        (timeDerivL f).memHolder.coe_nnHolderNorm_eq_eHolderNorm])
  rwa [timeExtension_space_slabTime, timeExtension_space_slabTime] at h

/-- For `α ≤ 1`, the value of a bounded order-two parabolic Hölder map is parabolically
`α`-Hölder. -/
theorem memHolder_valueL (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab) :
    MemHolder α (valueL f : slab (E := E) a b → F) := by
  have h := eHolderNorm_valueL_add_eHolderNorm_spatialFDerivL_le hα f one_pos le_rfl
  exact eHolderNorm_lt_top.1 ((le_self_add.trans h).trans_lt ENNReal.coe_lt_top)

/-- For `α ≤ 1`, the spatial gradient of a bounded order-two parabolic Hölder map is
parabolically `α`-Hölder. -/
theorem memHolder_spatialFDerivL (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab) :
    MemHolder α (spatialFDerivL f : slab (E := E) a b → E →L[ℝ] F) := by
  have h := eHolderNorm_valueL_add_eHolderNorm_spatialFDerivL_le hα f one_pos le_rfl
  exact eHolderNorm_lt_top.1 ((le_add_self.trans h).trans_lt ENNReal.coe_lt_top)

/-- The absorption estimate written with the explicit lower-order norms
`‖u‖_∞ + [u]_{α,par} + ‖D_x u‖_∞ + [D_x u]_{α,par}`. -/
private theorem norm_valueL_add_nnHolderNorm_add_le (hα : α ≤ 1)
    (f : ParabolicC2HolderSpace α E F hab) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ‖valueL f‖ + nnHolderNorm α (valueL f : slab (E := E) a b → F) +
        (‖spatialFDerivL f‖ +
          nnHolderNorm α (spatialFDerivL f : slab (E := E) a b → E →L[ℝ] F)) ≤
      7 * ε ^ (1 - (α : ℝ)) * ‖f‖ + 17 * ε ^ (-(1 + (α : ℝ))) * ‖valueL f‖ := by
  lift ε to ℝ≥0 using hε.le
  have hε' : 0 < ε := NNReal.coe_pos.1 hε
  have h := eHolderNorm_valueL_add_eHolderNorm_spatialFDerivL_le hα f hε' hε₁
  rw [← (memHolder_valueL hα f).coe_nnHolderNorm_eq_eHolderNorm,
    ← (memHolder_spatialFDerivL hα f).coe_nnHolderNorm_eq_eHolderNorm, ← ENNReal.coe_add,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe] at h
  push_cast at h
  -- The top-order quantities and the Hessian supremum are bounded by the order-two norm.
  have hN : ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ +
      ‖(timeDerivL f).toBoundedContinuousFunction‖ +
      nnHolderNorm α ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _) +
      nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _) ≤ ‖f‖ := by
    rw [norm_def]
    linarith [norm_nonneg (valueL f), norm_nonneg (spatialFDerivL f)]
  have hM₂ : ‖(spatialSecondFDerivL f).toBoundedContinuousFunction‖ ≤ ‖f‖ :=
    le_trans (by linarith [NNReal.coe_nonneg (nnHolderNorm α
      ((spatialSecondFDerivL f).toBoundedContinuousFunction : _ → _)),
      NNReal.coe_nonneg (nnHolderNorm α ((timeDerivL f).toBoundedContinuousFunction : _ → _)),
      norm_nonneg (timeDerivL f).toBoundedContinuousFunction]) hN
  have hD := f.norm_spatialFDerivL_le hε
  -- Compare the powers of `ε ≤ 1`.
  have hε₁' : (ε : ℝ) ≤ 1 := hε₁
  have hpow₁ : (ε : ℝ) ≤ ε ^ (1 - (α : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε hε₁' (by linarith [α.coe_nonneg] :
      1 - (α : ℝ) ≤ 1)
  have hpow₂ : (ε : ℝ)⁻¹ ≤ ε ^ (-(1 + (α : ℝ))) := by
    simpa [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_ge hε hε₁'
      (by linarith [α.coe_nonneg] : -(1 + (α : ℝ)) ≤ -1)
  have hpow₃ : (1 : ℝ) ≤ ε ^ (-(1 + (α : ℝ))) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε₁' (by linarith [α.coe_nonneg])
  have hM₀ := norm_nonneg (valueL f)
  have hf := norm_nonneg f
  have hP : (0 : ℝ) ≤ ε ^ (1 - (α : ℝ)) := by positivity
  have hdiv : 2 * ‖valueL f‖ / ε = 2 * (ε : ℝ)⁻¹ * ‖valueL f‖ := by ring
  rw [hdiv] at hD
  nlinarith [mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 6 * ε ^ (1 - (α : ℝ))),
    mul_le_mul_of_nonneg_right hpow₂ hM₀, mul_le_mul_of_nonneg_right hpow₃ hM₀,
    mul_le_mul hpow₁ hM₂ (norm_nonneg _) hP]

/-- For `α ≤ 1`, the inclusion of the value into the bounded parabolic Hölder space
`C_b^{α,α/2}` on the slab, as a continuous linear map. -/
def valueHolderL (hα : α ≤ 1) :
    ParabolicC2HolderSpace α E F hab →L[ℝ] HolderSpace α (slab (E := E) a b) F :=
  LinearMap.mkContinuous
    { toFun f := HolderSpace.ofBoundedContinuousFunction (valueL f) (memHolder_valueL hα f)
      map_add' f g := HolderSpace.ext fun p ↦ by simp [HolderSpace.add_apply]
      map_smul' c f := HolderSpace.ext fun p ↦ by simp [HolderSpace.smul_apply] }
    24 fun f ↦ by
      have h := norm_valueL_add_nnHolderNorm_add_le hα f one_pos le_rfl
      have hD := add_nonneg (norm_nonneg (spatialFDerivL f)) (NNReal.coe_nonneg
        (nnHolderNorm α (spatialFDerivL f : slab (E := E) a b → E →L[ℝ] F)))
      have hv := norm_valueL_le f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, HolderSpace.norm_def,
        HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
      simp only [Real.one_rpow] at h
      linarith

/-- For `α ≤ 1`, the inclusion of the spatial gradient into the bounded parabolic Hölder space
`C_b^{α,α/2}` on the slab, as a continuous linear map. -/
def spatialFDerivHolderL (hα : α ≤ 1) :
    ParabolicC2HolderSpace α E F hab →L[ℝ] HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) :=
  LinearMap.mkContinuous
    { toFun f := HolderSpace.ofBoundedContinuousFunction (spatialFDerivL f)
        (memHolder_spatialFDerivL hα f)
      map_add' f g := HolderSpace.ext fun p ↦ by simp [HolderSpace.add_apply]
      map_smul' c f := HolderSpace.ext fun p ↦ by simp [HolderSpace.smul_apply] }
    24 fun f ↦ by
      have h := norm_valueL_add_nnHolderNorm_add_le hα f one_pos le_rfl
      have hV := add_nonneg (norm_nonneg (valueL f)) (NNReal.coe_nonneg
        (nnHolderNorm α (valueL f : slab (E := E) a b → F)))
      have hv := norm_valueL_le f
      simp only [LinearMap.coe_mk, AddHom.coe_mk, HolderSpace.norm_def,
        HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction]
      simp only [Real.one_rpow] at h
      linarith

@[simp]
theorem toBoundedContinuousFunction_valueHolderL (hα : α ≤ 1)
    (f : ParabolicC2HolderSpace α E F hab) :
    (valueHolderL hα f).toBoundedContinuousFunction = valueL f := by
  simp [valueHolderL]

@[simp]
theorem valueHolderL_apply (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : valueHolderL hα f p = f p := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply, toBoundedContinuousFunction_valueHolderL,
    valueL_apply]

@[simp]
theorem toBoundedContinuousFunction_spatialFDerivHolderL (hα : α ≤ 1)
    (f : ParabolicC2HolderSpace α E F hab) :
    (spatialFDerivHolderL hα f).toBoundedContinuousFunction = spatialFDerivL f := by
  simp [spatialFDerivHolderL]

@[simp]
theorem spatialFDerivHolderL_apply (hα : α ≤ 1) (f : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : spatialFDerivHolderL hα f p = spatialFDerivL f p := by
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_spatialFDerivHolderL]

/-- **Absorption of the lower-order parabolic Hölder norms.** For `α ≤ 1` and `0 < ε ≤ 1`,

`‖u‖_{α,par} + ‖D_x u‖_{α,par} ≤ 7 ε^(1 - α) ‖u‖ + 17 ε^(-(1 + α)) ‖u‖_∞`,

where the left side uses the supremum-plus-Hölder norms of `C_b^{α,α/2}` and `‖u‖` is the
order-two norm. The constants depend neither on the spaces nor on the slab. -/
theorem norm_valueHolderL_add_norm_spatialFDerivHolderL_le (hα : α ≤ 1)
    (f : ParabolicC2HolderSpace α E F hab) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ‖valueHolderL hα f‖ + ‖spatialFDerivHolderL hα f‖ ≤
      7 * ε ^ (1 - (α : ℝ)) * ‖f‖ + 17 * ε ^ (-(1 + (α : ℝ))) * ‖valueL f‖ := by
  rw [HolderSpace.norm_def, HolderSpace.norm_def, toBoundedContinuousFunction_valueHolderL,
    toBoundedContinuousFunction_spatialFDerivHolderL, add_assoc]
  exact (add_assoc _ _ _).symm.trans_le (norm_valueL_add_nnHolderNorm_add_le hα f hε hε₁)

/-- **Absorption with a prescribed small constant.** For `α < 1` and every `η > 0` there is a
constant `C`, depending only on `α` and `η`, such that on every slab
`‖u‖_{α,par} + ‖D_x u‖_{α,par} ≤ η ‖u‖ + C ‖u‖_∞`. -/
theorem exists_norm_valueHolderL_add_norm_spatialFDerivHolderL_le (hα : α < 1) {η : ℝ}
    (hη : 0 < η) : ∃ C : ℝ, ∀ {a b : ℝ} {hab : a < b} (f : ParabolicC2HolderSpace α E F hab),
      ‖valueHolderL hα.le f‖ + ‖spatialFDerivHolderL hα.le f‖ ≤ η * ‖f‖ + C * ‖valueL f‖ := by
  have hα' : 0 < 1 - (α : ℝ) := sub_pos.2 (by exact_mod_cast hα)
  -- Choose `ε ≤ 1` with `7 ε^(1 - α) ≤ η`.
  set ε := min 1 ((η / 7) ^ (1 - (α : ℝ))⁻¹) with hε_def
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hpow : 7 * ε ^ (1 - (α : ℝ)) ≤ η := by
    have h := Real.rpow_le_rpow hε.le (min_le_right _ _) hα'.le
    rw [Real.rpow_inv_rpow (by positivity) hα'.ne'] at h
    linarith
  refine ⟨17 * ε ^ (-(1 + (α : ℝ))), fun f ↦ ?_⟩
  refine (norm_valueHolderL_add_norm_spatialFDerivHolderL_le hα.le f hε
    (min_le_left _ _)).trans ?_
  gcongr

end ParabolicC2HolderSpace

end TauCeti

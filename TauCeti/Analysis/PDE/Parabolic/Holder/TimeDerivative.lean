/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Time differentiation in the parabolic Hölder scale

Time differentiation is a contraction from `C_{par,b}^{k+2+α}` to `C_{par,b}^{k+α}` on a
nondegenerate closed slab. It shifts the mixed derivative fields by one time derivative and
preserves both the top-order parabolic Hölder bounds and the uniform temporal Hölder bounds
one order below the top. At the endpoints the derivative is taken within the closed interval.

The operator `TauCeti.ParabolicCkHolderSpace.timeDerivL` supplies the time-differentiation
step in higher-order parabolic regularity. Its characteristic lemmas describe all three
families of derivative data, without unfolding the derivative-graph construction.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004,
  Chapter 3 (parabolic Hölder spaces).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped ENNReal NNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

private def timeDeriv (f : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL (r + 1) m f)
    (fun r m h t x ↦ hasFDerivAt_mixedDerivL f (by omega) t x)
    (fun r m h x t ↦ hasDerivWithinAt_mixedDerivL f (by omega) x t)
    (fun r m h ↦ ⟨‖timeSliceL (r + 1) m f‖₊, fun x ↦ by
      have hnorm : ‖timeSliceL (r + 1) m f x‖₊ ≤ ‖timeSliceL (r + 1) m f‖₊ := by
        exact_mod_cast lp.norm_apply_le_norm ENNReal.top_ne_zero (timeSliceL (r + 1) m f) x
      have H := (timeSliceL (r + 1) m f x).holderWith_nnnorm.mono hnorm
      intro t s
      simpa only [timeSliceL_apply f (r := r + 1) (m := m) (by omega)] using H t s⟩)
    (fun r m h ↦ memHolder_mixedDerivL f (by omega))

private theorem mixedDerivL_timeDeriv (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (r m : ℕ) : mixedDerivL r m (timeDeriv f) = mixedDerivL (r + 1) m f := by
  by_cases h : 2 * r + m ≤ k
  · exact mixedDerivL_mk _ _ _ _ h
  · rw [mixedDerivL_of_lt (by omega), mixedDerivL_of_lt (by omega)]
    rfl

private theorem mixedDerivHolderL_timeDeriv (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (r m : ℕ) : mixedDerivHolderL r m (timeDeriv f) = mixedDerivHolderL (r + 1) m f := by
  by_cases h : 2 * r + m = k
  · apply HolderSpace.ext
    intro p
    have H := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL (timeDeriv f) h)
    have H' := congrArg (fun g ↦ g p)
      (toBoundedContinuousFunction_mixedDerivHolderL f (r := r + 1) (m := m) (by omega))
    rw [mixedDerivL_timeDeriv] at H
    simpa only [HolderSpace.toBoundedContinuousFunction_apply] using H.trans H'.symm
  · rw [mixedDerivHolderL_of_ne h, mixedDerivHolderL_of_ne (by omega)]
    rfl

private theorem timeSliceL_timeDeriv (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (r m : ℕ) : timeSliceL r m (timeDeriv f) = timeSliceL (r + 1) m f := by
  by_cases h : 2 * r + m + 1 = k
  · apply lp.ext
    funext x
    apply HolderSpace.ext
    intro t
    rw [timeSliceL_apply _ h, mixedDerivL_timeDeriv,
      timeSliceL_apply f (r := r + 1) (m := m) (by omega)]
  · rw [timeSliceL_of_ne h, timeSliceL_of_ne (by omega)]
    rfl

private theorem norm_timeDeriv_le (f : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ‖timeDeriv f‖ ≤ ‖f‖ := by
  rw [norm_eq, norm_eq]
  simp only [mixedDerivL_timeDeriv, timeSliceL_timeDeriv, mixedDerivHolderL_timeDeriv]
  apply Finset.sum_le_sum_of_injOn (fun p : ℕ × ℕ ↦ (p.1 + 1, p.2))
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    exact Prod.ext (by omega) hpq.2
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    simp only [mem_parabolicDerivPairs] at hq ⊢
    omega
  · intro p _
    exact le_rfl
  · intro p _ _
    positivity

private theorem timeDeriv_apply (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) : timeDeriv f p = (mixedDerivL 1 0 f p).curry0 := by
  rw [← mixedDerivL_zero_zero_apply (timeDeriv f) p 0, mixedDerivL_timeDeriv,
    ContinuousMultilinearMap.curry0_apply]

/-- Time differentiation `C_{par,b}^{k+2+α} → C_{par,b}^{k+α}` on the same closed slab.
Its operator norm is at most one; the endpoint derivatives are one-sided. -/
def timeDerivL : ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ]
    ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := timeDeriv
      map_add' := fun f g ↦ by
        apply ext
        intro p
        simp only [timeDeriv_apply, coe_add, Pi.add_apply, map_add,
          ContinuousMultilinearMap.curry0_apply, add_apply]
      map_smul' := fun c f ↦ by
        apply ext
        intro p
        simp only [timeDeriv_apply, coe_smul, Pi.smul_apply, map_smul,
          ContinuousMultilinearMap.curry0_apply, smul_apply, RingHom.id_apply] }
    1 (fun f ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      exact norm_timeDeriv_le f)

/-- Time differentiation shifts every mixed derivative field by one time derivative. -/
@[simp]
theorem mixedDerivL_timeDerivL (f : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    mixedDerivL r m (timeDerivL f) = mixedDerivL (r + 1) m f :=
  mixedDerivL_timeDeriv f r m

/-- The top-order parabolic Hölder field of the time derivative is the shifted field. -/
@[simp]
theorem mixedDerivHolderL_timeDerivL (f : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (timeDerivL f) = mixedDerivHolderL (r + 1) m f :=
  mixedDerivHolderL_timeDeriv f r m

/-- The uniform temporal Hölder slices of the time derivative are the shifted slices. -/
@[simp]
theorem timeSliceL_timeDerivL (f : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    timeSliceL r m (timeDerivL f) = timeSliceL (r + 1) m f :=
  timeSliceL_timeDeriv f r m

/-- Evaluation of time differentiation in terms of the recorded first time derivative. -/
@[simp]
theorem timeDerivL_apply (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) : timeDerivL f p = (mixedDerivL 1 0 f p).curry0 :=
  timeDeriv_apply f p

/-- The time extension is differentiable within the slab, with derivative `timeDerivL`.
This includes the continuous one-sided derivatives at both endpoints. -/
theorem hasDerivWithinAt_timeDerivL (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le f x)
      (timeDerivL f (slabMk x t)) (Icc a b) t := by
  have H := HasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    ((continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv :
      (E [×0]→L[ℝ] F) →L[ℝ] F).hasFDerivAt
    (hasDerivWithinAt_mixedDerivL f (r := 0) (m := 0) (by omega) x t)
  simpa only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, continuousMultilinearCurryFin0_apply,
    ParabolicC2HolderSpace.timeExtension_def, ContinuousMultilinearMap.curry0_apply,
    mixedDerivL_zero_zero_apply, timeDerivL_apply] using H

/-- The value of `timeDerivL` is the derivative within the closed time interval, including
its one-sided endpoint values. -/
theorem timeDerivL_slabMk (f : ParabolicCkHolderSpace (k + 2) α E F hab)
    (x : E) (t : Icc a b) : timeDerivL f (slabMk x t) =
      derivWithin (ParabolicC2HolderSpace.timeExtension hab.le f x) (Icc a b) t :=
  ((hasDerivWithinAt_timeDerivL f x t).derivWithin
    (uniqueDiffOn_Icc hab t t.2)).symm

/-- Time differentiation does not increase the full parabolic Hölder norm. -/
theorem norm_timeDerivL_le (f : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ‖timeDerivL f‖ ≤ ‖f‖ :=
  norm_timeDeriv_le f

/-- The operator norm of time differentiation is at most one. -/
theorem norm_timeDerivL_le_one :
    ‖timeDerivL (k := k) (α := α) (E := E) (F := F) (hab := hab)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end TauCeti.ParabolicCkHolderSpace

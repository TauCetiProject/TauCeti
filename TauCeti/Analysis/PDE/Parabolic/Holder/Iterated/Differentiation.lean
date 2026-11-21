/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Normed.Module.Multilinear.Curry

/-!
# Spatial and time derivatives on parabolic Hölder spaces of every order

In the parabolic scaling a spatial derivative has order one and a time derivative has order two.
This file shows that differentiation lowers the order of the bounded parabolic Hölder spaces
`C_{par,b}^{k+α}` (`TauCeti.ParabolicCkHolderSpace`) accordingly: the spatial derivative
`u ↦ D_x u` is a continuous linear map

`C_{par,b}^{(k+1)+α}(E × [a, b], F) → C_{par,b}^{k+α}(E × [a, b], E →L[ℝ] F)`

and the time derivative `u ↦ ∂ₜu`, taken within `[a, b]` and so one-sided at the endpoints, is a
continuous linear map

`C_{par,b}^{(k+2)+α}(E × [a, b], F) → C_{par,b}^{k+α}(E × [a, b], F)`,

both of operator norm at most one. The two derivatives commute on `C_{par,b}^{(k+3)+α}`. These
maps are the setting for the induction on the order in the Schauder theory of parabolic
equations, where an equation for `u` in `C_{par,b}^{(k+3)+α}` is differentiated in space to give
an equation for `D_x u` one order lower, and the equation itself recovers `∂ₜu`.

The fields of `D_x u` are those of `u` with one more spatial derivative: the field
`D_t^r D_x^m (D_x u)` is `D_t^r D_x^(m+1) u` with its last argument separated, by Mathlib's
`ContinuousMultilinearMap.curryRight`
(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_spatialFDerivL_apply`). The fields of `∂ₜu` are those
of `u` with one more time derivative, `D_t^r D_x^m (∂ₜu) = D_t^(r+1) D_x^m u`
(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_timeDerivL`). The Hölder fields of top order and the
Hölder time slices one order below are carried along in the same way.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.spatialFDerivL`: the spatial derivative, with
  `TauCeti.ParabolicCkHolderSpace.hasSpatialFDerivAt` identifying its values as the Fréchet
  derivative on each time slice.
* `TauCeti.ParabolicCkHolderSpace.timeDerivL`: the time derivative, with
  `TauCeti.ParabolicCkHolderSpace.hasTimeDerivWithinAt` identifying its values as the derivative
  within `[a, b]`.
* `TauCeti.ParabolicCkHolderSpace.norm_spatialFDerivL_le_one` and
  `TauCeti.ParabolicCkHolderSpace.norm_timeDerivL_le_one`: both have operator norm at most one.
* `TauCeti.ParabolicCkHolderSpace.timeDerivL_spatialFDerivL`: the two derivatives commute.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

namespace ParabolicCkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- Comparing the norms of two elements term by term: if each term `(r, m)` of the norm of `g` is
at most the term `e (r, m)` of the norm of `f`, for an injective reindexing `e` of the pairs of
order at most `k` into those of order at most `k'`, then `‖g‖ ≤ ‖f‖`. -/
private theorem norm_le_norm_of_injective {k' : ℕ} {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] (g : ParabolicCkHolderSpace k α E F' hab)
    (f : ParabolicCkHolderSpace k' α E F hab) (e : ℕ × ℕ → ℕ × ℕ)
    (he : Function.Injective e) (hk : ∀ p, 2 * p.1 + p.2 ≤ k → 2 * (e p).1 + (e p).2 ≤ k')
    (hfield : ∀ p, ‖mixedDerivL p.1 p.2 g‖ ≤ ‖mixedDerivL (e p).1 (e p).2 f‖)
    (hslice : ∀ p, ‖timeSliceL p.1 p.2 g‖ ≤ ‖timeSliceL (e p).1 (e p).2 f‖)
    (hholder : ∀ p, ‖mixedDerivHolderL p.1 p.2 g‖ ≤ ‖mixedDerivHolderL (e p).1 (e p).2 f‖) :
    ‖g‖ ≤ ‖f‖ := by
  rw [norm_eq g, norm_eq f]
  refine Finset.sum_le_sum_of_injOn e he.injOn (fun q hq ↦ ?_)
    (fun p _ ↦ add_le_add (hfield p) (add_le_add (hslice p) (hholder p)))
    (fun q _ _ ↦ by positivity)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
  exact mem_parabolicDerivPairs.2 (hk p (mem_parabolicDerivPairs.1 hp))

/-! ### The time derivative -/

section Time

/-- The time derivative of `u ∈ C_{par,b}^{(k+2)+α}`, built from the fields `D_t^(r+1) D_x^m u`;
`timeDerivL` is its bundled form. -/
private def timeDeriv (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL (r + 1) m u)
    (fun _ _ h t x ↦ hasFDerivAt_mixedDerivL u (by omega) t x)
    (fun _ _ h x t ↦ hasDerivWithinAt_mixedDerivL u (by omega) x t)
    (fun _ _ h ↦ ⟨_, holderWith_mixedDerivL_slabMk u (by omega)⟩)
    (fun _ _ h ↦ memHolder_mixedDerivL u (by omega))

private theorem mixedDerivL_timeDeriv (u : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    mixedDerivL r m (timeDeriv u) = mixedDerivL (r + 1) m u := by
  by_cases h : 2 * r + m ≤ k
  · exact mixedDerivL_mk _ _ _ _ h
  · rw [mixedDerivL_of_lt (by omega), mixedDerivL_of_lt (by omega), zero_apply, zero_apply]

private theorem timeSliceL_timeDeriv (u : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    timeSliceL r m (timeDeriv u) = timeSliceL (r + 1) m u := by
  by_cases h : 2 * r + m + 1 = k
  · refine lp.ext (funext fun x ↦ HolderSpace.ext fun t ↦ ?_)
    rw [timeSliceL_apply _ h, timeSliceL_apply u (by omega), mixedDerivL_timeDeriv]
  · rw [timeSliceL_of_ne h, timeSliceL_of_ne (by omega), zero_apply, zero_apply]

private theorem mixedDerivHolderL_timeDeriv (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (r m : ℕ) : mixedDerivHolderL r m (timeDeriv u) = mixedDerivHolderL (r + 1) m u := by
  by_cases h : 2 * r + m = k
  · refine HolderSpace.ext fun p ↦ ?_
    rw [← HolderSpace.toBoundedContinuousFunction_apply,
      toBoundedContinuousFunction_mixedDerivHolderL (timeDeriv u) h,
      ← HolderSpace.toBoundedContinuousFunction_apply,
      toBoundedContinuousFunction_mixedDerivHolderL u (show 2 * (r + 1) + m = k + 2 by omega),
      mixedDerivL_timeDeriv]
  · rw [mixedDerivHolderL_of_ne h, mixedDerivHolderL_of_ne (by omega), zero_apply, zero_apply]

private theorem timeDeriv_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab)
    (p : slab (E := E) a b) : timeDeriv u p = mixedDerivL 1 0 u p 0 := by
  rw [← mixedDerivL_zero_zero_apply (timeDeriv u) p 0, mixedDerivL_timeDeriv]

private theorem norm_timeDeriv_le (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ‖timeDeriv u‖ ≤ ‖u‖ := by
  refine norm_le_norm_of_injective (timeDeriv u) u (fun p ↦ (p.1 + 1, p.2))
    (fun p q h ↦ ?_) (fun p h ↦ by dsimp only; omega)
    (fun p ↦ (congrArg norm (mixedDerivL_timeDeriv u p.1 p.2)).le)
    (fun p ↦ (congrArg norm (timeSliceL_timeDeriv u p.1 p.2)).le)
    (fun p ↦ (congrArg norm (mixedDerivHolderL_timeDeriv u p.1 p.2)).le)
  simp only [Prod.mk.injEq, add_left_inj] at h
  exact Prod.ext h.1 h.2

variable (k α E F hab) in
/-- **The time derivative** `u ↦ ∂ₜu` from `C_{par,b}^{(k+2)+α}` to `C_{par,b}^{k+α}`, taken
within `[a, b]`, so one-sided at the endpoints (`ParabolicCkHolderSpace.timeDerivL_slabMk`). Its
fields are those of `u` with one more time derivative
(`ParabolicCkHolderSpace.mixedDerivL_timeDerivL`), and its operator norm is at most one
(`ParabolicCkHolderSpace.norm_timeDerivL_le_one`). -/
def timeDerivL :
    ParabolicCkHolderSpace (k + 2) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := timeDeriv
      map_add' u v := ext fun p ↦ by simp [timeDeriv_apply]
      map_smul' c u := ext fun p ↦ by simp [timeDeriv_apply] }
    1 fun u ↦ by
      rw [one_mul]
      exact norm_timeDeriv_le u

/-- The fields of the time derivative are those of `u` with one more time derivative:
`D_t^r D_x^m (∂ₜu) = D_t^(r+1) D_x^m u`. -/
@[simp]
theorem mixedDerivL_timeDerivL (u : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    mixedDerivL r m (timeDerivL k α E F hab u) = mixedDerivL (r + 1) m u :=
  mixedDerivL_timeDeriv u r m

/-- The Hölder time slices of the time derivative are those of `u` with one more time
derivative. -/
@[simp]
theorem timeSliceL_timeDerivL (u : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    timeSliceL r m (timeDerivL k α E F hab u) = timeSliceL (r + 1) m u :=
  timeSliceL_timeDeriv u r m

/-- The Hölder fields of top order of the time derivative are those of `u` with one more time
derivative. -/
@[simp]
theorem mixedDerivHolderL_timeDerivL (u : ParabolicCkHolderSpace (k + 2) α E F hab) (r m : ℕ) :
    mixedDerivHolderL r m (timeDerivL k α E F hab u) = mixedDerivHolderL (r + 1) m u :=
  mixedDerivHolderL_timeDeriv u r m

/-- The values of the time derivative are those of the field `D_t u`. -/
@[simp]
theorem timeDerivL_apply (u : ParabolicCkHolderSpace (k + 2) α E F hab) (p : slab (E := E) a b) :
    timeDerivL k α E F hab u p = mixedDerivL 1 0 u p 0 :=
  timeDeriv_apply u p

/-- The values of the time derivative are the derivatives of the time slices of `u` within
`[a, b]`, one-sided at the endpoints. -/
theorem timeDerivL_slabMk (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E) (t : Icc a b) :
    timeDerivL k α E F hab u (slabMk x t) =
      derivWithin (ParabolicC2HolderSpace.timeExtension hab.le u x) (Icc a b) t := by
  rw [← iteratedDerivWithin_one, ← curry0_mixedDerivL_slabMk u (by omega),
    ContinuousMultilinearMap.curry0_apply]
  exact timeDerivL_apply u _

/-- The time slices of `u` have derivative `∂ₜu` within `[a, b]`, one-sided at the endpoints. -/
theorem hasTimeDerivWithinAt (u : ParabolicCkHolderSpace (k + 2) α E F hab) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le u x)
      (timeDerivL k α E F hab u (slabMk x t)) (Icc a b) t := by
  have hd := HasFDerivAt.comp_hasDerivWithinAt (x := (t : ℝ))
    (continuousMultilinearCurryFin0 ℝ E F).hasFDerivAt
    (hasDerivWithinAt_mixedDerivL u (r := 0) (m := 0) (by omega) x t)
  rw [timeDerivL_slabMk]
  refine DifferentiableWithinAt.hasDerivWithinAt ?_
  simpa only [ParabolicC2HolderSpace.timeExtension_def, Function.comp_def,
    continuousMultilinearCurryFin0_apply, mixedDerivL_zero_zero_apply]
    using hd.differentiableWithinAt

/-- The time derivative has operator norm at most one. -/
theorem norm_timeDerivL_le_one : ‖timeDerivL k α E F hab‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The time derivative of `u` has norm at most `‖u‖`. -/
theorem norm_timeDerivL_le (u : ParabolicCkHolderSpace (k + 2) α E F hab) :
    ‖timeDerivL k α E F hab u‖ ≤ ‖u‖ :=
  norm_timeDeriv_le u

end Time

/-! ### The spatial derivative -/

section Space

/-- A local shortcut for the norm on operator-valued fields. Without it and the following
shortcuts, the multilinear operator-valued fields `E [×m]→L[ℝ] E →L[ℝ] F` of the spatial derivative
receive the seminormed structure of Mathlib's currying isometry instead of the normed one of the
target space, and the two fail to unify. -/
local instance : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on operator-valued fields. -/
local instance : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
/-- A local shortcut for the norm on multilinear operator-valued fields. -/
local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] E →L[ℝ] F) := inferInstance
/-- A local shortcut for scalar operations on multilinear operator-valued fields. -/
local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] E →L[ℝ] F) := inferInstance

/-- Separating the last argument of an `(m + 1)`-multilinear map, as a continuous linear map. -/
private abbrev curryRightCLM (m : ℕ) :
    (E [×(m + 1)]→L[ℝ] F) →L[ℝ] (E [×m]→L[ℝ] E →L[ℝ] F) :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).toContinuousLinearEquiv.toContinuousLinearMap

private theorem curryRightCLM_apply (m : ℕ) (f : E [×(m + 1)]→L[ℝ] F) :
    curryRightCLM m f = f.curryRight :=
  (rfl)

/-- The field `D_t^r D_x^(m+1) u` with its last argument separated. -/
private def curryRightField (u : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] E →L[ℝ] F) :=
  (curryRightCLM m).compLeftContinuousBounded _ (mixedDerivL r (m + 1) u)

private theorem curryRightField_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ)
    (p : slab (E := E) a b) :
    curryRightField u r m p = (mixedDerivL r (m + 1) u p).curryRight := by
  rw [curryRightField, ContinuousLinearMap.compLeftContinuousBounded_apply, curryRightCLM_apply]

/-- The spatial derivative of `curryRightField u r m` is `curryRightField u r (m + 1)`, curried on
the left. -/
private theorem hasFDerivAt_curryRightField (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ curryRightField u r m (slabMk y t))
      (curryRightField u r (m + 1) (slabMk x t)).curryLeft x := by
  -- `curryRightField u r m` is `D_t^r D_x^(m+1) u` followed by `curryRightCLM m`.
  have hd := (ContinuousLinearMap.hasFDerivAt (f := curryRightCLM m)).comp x
    (hasFDerivAt_mixedDerivL u (r := r) (m := m + 1) (by omega) t x)
  have heq : (curryRightCLM m).comp (mixedDerivL r (m + 1 + 1) u (slabMk x t)).curryLeft =
      (curryRightField u r (m + 1) (slabMk x t)).curryLeft := by
    ext h' v w
    simp only [ContinuousLinearMap.comp_apply, curryRightCLM_apply, curryRightField_apply,
      ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.curryRight_apply,
      Fin.cons_snoc_eq_snoc_cons]
  rw [heq] at hd
  exact hd

/-- The time derivative of `curryRightField u r m` within `[a, b]` is `curryRightField u (r + 1) m`.
-/
private theorem hasDerivWithinAt_curryRightField (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (curryRightField u r m) x)
      (curryRightField u (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hd := HasFDerivAt.comp_hasDerivWithinAt (x := (t : ℝ))
    (ContinuousLinearMap.hasFDerivAt (f := curryRightCLM m))
    (hasDerivWithinAt_mixedDerivL u (r := r) (m := m + 1) (by omega) x t)
  simpa only [ParabolicC2HolderSpace.timeExtension_def, Function.comp_def, curryRightField_apply,
    curryRightCLM_apply] using hd

/-- The spatial derivative of `u ∈ C_{par,b}^{(k+1)+α}`, built from the fields
`D_t^r D_x^(m+1) u` with their last argument separated; `spatialFDerivL` is its bundled form. -/
private def spatialFDeriv (u : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E (E →L[ℝ] F) hab :=
  mk (curryRightField u) (fun _ _ h t x ↦ hasFDerivAt_curryRightField u h t x)
    (fun _ _ h x t ↦ hasDerivWithinAt_curryRightField u h x t)
    -- Separating the last argument preserves distances, so it preserves Hölder bounds.
    (fun r m h ↦ ⟨‖timeSliceL r (m + 1) u‖₊, fun x t s ↦ by
      dsimp only
      rw [curryRightField_apply, curryRightField_apply, ContinuousMultilinearMap.edist_curryRight]
      exact holderWith_mixedDerivL_slabMk u (r := r) (m := m + 1) (by omega) x t s⟩)
    (fun r m h ↦ by
      obtain ⟨C, hC⟩ := memHolder_mixedDerivL u (r := r) (m := m + 1) (by omega)
      exact ⟨C, fun p q ↦ by
        rw [curryRightField_apply, curryRightField_apply, ContinuousMultilinearMap.edist_curryRight]
        exact hC p q⟩)

private theorem mixedDerivL_spatialFDeriv_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivL r m (spatialFDeriv u) p = (mixedDerivL r (m + 1) u p).curryRight := by
  by_cases h : 2 * r + m ≤ k
  · exact (DFunLike.congr_fun (mixedDerivL_mk (D := curryRightField u) _ _ _ _ h) p).trans
      (curryRightField_apply u r m p)
  · rw [mixedDerivL_of_lt (k := k) (α := α) (F := E →L[ℝ] F) (hab := hab) (by omega),
      mixedDerivL_of_lt (k := k + 1) (α := α) (F := F) (hab := hab) (r := r) (m := m + 1)
        (by omega)]
    simp only [zero_apply, ContinuousMultilinearMap.curryRight_zero]

private theorem spatialFDeriv_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : spatialFDeriv u p = (mixedDerivL 0 1 u p).curryRight 0 := by
  rw [← mixedDerivL_zero_zero_apply (spatialFDeriv u) p 0, mixedDerivL_spatialFDeriv_apply]

private theorem timeSliceL_spatialFDeriv_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) (t : Icc a b) :
    timeSliceL r m (spatialFDeriv u) x t = (timeSliceL r (m + 1) u x t).curryRight := by
  by_cases h : 2 * r + m + 1 = k
  · rw [timeSliceL_apply (spatialFDeriv u) h x t,
      timeSliceL_apply u (show 2 * r + (m + 1) + 1 = k + 1 by omega) x t,
      mixedDerivL_spatialFDeriv_apply]
  · rw [timeSliceL_of_ne (k := k) (α := α) (F := E →L[ℝ] F) (hab := hab) h,
      timeSliceL_of_ne (k := k + 1) (α := α) (F := F) (hab := hab) (r := r) (m := m + 1)
        (by omega)]
    simp only [zero_apply, lp.coeFn_zero, Pi.zero_apply, HolderSpace.zero_apply,
      ContinuousMultilinearMap.curryRight_zero]

private theorem mixedDerivHolderL_spatialFDeriv_apply
    (u : ParabolicCkHolderSpace (k + 1) α E F hab) (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivHolderL r m (spatialFDeriv u) p = (mixedDerivHolderL r (m + 1) u p).curryRight := by
  by_cases h : 2 * r + m = k
  · rw [← HolderSpace.toBoundedContinuousFunction_apply,
      toBoundedContinuousFunction_mixedDerivHolderL (spatialFDeriv u) h,
      ← HolderSpace.toBoundedContinuousFunction_apply,
      toBoundedContinuousFunction_mixedDerivHolderL u (show 2 * r + (m + 1) = k + 1 by omega),
      mixedDerivL_spatialFDeriv_apply]
  · rw [mixedDerivHolderL_of_ne (k := k) (α := α) (F := E →L[ℝ] F) (hab := hab) h,
      mixedDerivHolderL_of_ne (k := k + 1) (α := α) (F := F) (hab := hab) (r := r) (m := m + 1)
        (by omega)]
    simp only [zero_apply, HolderSpace.zero_apply, ContinuousMultilinearMap.curryRight_zero]

private theorem norm_spatialFDeriv_le (u : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖spatialFDeriv u‖ ≤ ‖u‖ := by
  refine norm_le_norm_of_injective (F' := E →L[ℝ] F) (spatialFDeriv u) u (fun p ↦ (p.1, p.2 + 1))
    (fun p q h ↦ ?_) (fun p h ↦ by dsimp only; omega) (fun p ↦ ?_) (fun p ↦ ?_) (fun p ↦ ?_)
  · simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2
  · refine (BoundedContinuousFunction.norm_le
      (norm_nonneg (mixedDerivL p.1 (p.2 + 1) u))).2 fun q ↦ ?_
    rw [mixedDerivL_spatialFDeriv_apply, ContinuousMultilinearMap.curryRight_norm]
    exact (mixedDerivL p.1 (p.2 + 1) u).norm_coe_le_norm q
  · refine lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦ ?_
    exact (HolderSpace.norm_le_norm_of_apply_eq_comp
      (ContinuousMultilinearMap.lipschitzWith_curryRight (Ei := fun _ ↦ E))
      (fun g ↦ (g.curryRight_norm).le)
      (timeSliceL_spatialFDeriv_apply u p.1 p.2 x)).trans
      (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x)
  · exact HolderSpace.norm_le_norm_of_apply_eq_comp
      (ContinuousMultilinearMap.lipschitzWith_curryRight (Ei := fun _ ↦ E))
      (fun g ↦ (g.curryRight_norm).le)
      (mixedDerivHolderL_spatialFDeriv_apply u p.1 p.2)

variable (k α E F hab) in
/-- **The spatial derivative** `u ↦ D_x u` from `C_{par,b}^{(k+1)+α}` to `C_{par,b}^{k+α}` with
values in `E →L[ℝ] F`: on each time slice it is the Fréchet derivative
(`ParabolicCkHolderSpace.spatialFDerivL_slabMk`). Its fields are those of `u` with one more
spatial derivative, the last argument separated
(`ParabolicCkHolderSpace.mixedDerivL_spatialFDerivL_apply`), and its operator norm is at most
one (`ParabolicCkHolderSpace.norm_spatialFDerivL_le_one`). -/
def spatialFDerivL :
    ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E (E →L[ℝ] F) hab :=
  LinearMap.mkContinuous
    { toFun := spatialFDeriv
      map_add' u v := ext fun p ↦ ContinuousLinearMap.ext fun w ↦ by simp [spatialFDeriv_apply]
      map_smul' c u := ext fun p ↦ ContinuousLinearMap.ext fun w ↦ by
        simp [spatialFDeriv_apply] }
    1 fun u ↦ by
      rw [one_mul]
      exact norm_spatialFDeriv_le u

/-- The fields of the spatial derivative are those of `u` with one more spatial derivative,
the last argument separated: `D_t^r D_x^m (D_x u) (v₁, …, vₘ) w = D_t^r D_x^(m+1) u (v₁, …, vₘ, w)`.
-/
@[simp]
theorem mixedDerivL_spatialFDerivL_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivL r m (spatialFDerivL k α E F hab u) p = (mixedDerivL r (m + 1) u p).curryRight :=
  mixedDerivL_spatialFDeriv_apply u r m p

/-- The Hölder time slices of the spatial derivative are those of `u` with one more spatial
derivative, the last argument separated. -/
@[simp]
theorem timeSliceL_spatialFDerivL_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (x : E) (t : Icc a b) :
    timeSliceL r m (spatialFDerivL k α E F hab u) x t = (timeSliceL r (m + 1) u x t).curryRight :=
  timeSliceL_spatialFDeriv_apply u r m x t

/-- The Hölder fields of top order of the spatial derivative are those of `u` with one more
spatial derivative, the last argument separated. -/
@[simp]
theorem mixedDerivHolderL_spatialFDerivL_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    mixedDerivHolderL r m (spatialFDerivL k α E F hab u) p =
      (mixedDerivHolderL r (m + 1) u p).curryRight :=
  mixedDerivHolderL_spatialFDeriv_apply u r m p

/-- The values of the spatial derivative are those of the field `D_x u`, read as a linear map. -/
@[simp]
theorem spatialFDerivL_apply (u : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) :
    spatialFDerivL k α E F hab u p = (mixedDerivL 0 1 u p).curryRight 0 :=
  spatialFDeriv_apply u p

/-- The values of the spatial derivative are the Fréchet derivatives of `u` on its time slices. -/
theorem spatialFDerivL_slabMk (u : ParabolicCkHolderSpace (k + 1) α E F hab) (x : E)
    (t : Icc a b) :
    spatialFDerivL k α E F hab u (slabMk x t) = fderiv ℝ (fun y ↦ u (slabMk y t)) x := by
  rw [← mixedDerivL_zero_zero_apply _ _ 0, mixedDerivL_spatialFDerivL_apply,
    mixedDerivL_zero_slabMk u (by omega)]
  ext w
  simp [iteratedFDeriv_one_apply]

/-- The time slices of `u` have Fréchet derivative `D_x u`. -/
theorem hasSpatialFDerivAt (u : ParabolicCkHolderSpace (k + 1) α E F hab) (t : Icc a b)
    (x : E) :
    HasFDerivAt (fun y ↦ u (slabMk y t)) (spatialFDerivL k α E F hab u (slabMk x t)) x := by
  have hd := (continuousMultilinearCurryFin0 ℝ E F).hasFDerivAt.comp x
    (hasFDerivAt_mixedDerivL u (r := 0) (m := 0) (by omega) t x)
  rw [spatialFDerivL_slabMk]
  refine DifferentiableAt.hasFDerivAt ?_
  simpa only [Function.comp_def, continuousMultilinearCurryFin0_apply,
    mixedDerivL_zero_zero_apply] using hd.differentiableAt

/-- The spatial derivative has operator norm at most one. -/
theorem norm_spatialFDerivL_le_one : ‖spatialFDerivL k α E F hab‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The spatial derivative of `u` has norm at most `‖u‖`. -/
theorem norm_spatialFDerivL_le (u : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖spatialFDerivL k α E F hab u‖ ≤ ‖u‖ :=
  norm_spatialFDeriv_le u

/-- **The spatial and time derivatives commute**: `∂ₜ (D_x u) = D_x (∂ₜu)` for
`u ∈ C_{par,b}^{(k+3)+α}`. -/
theorem timeDerivL_spatialFDerivL (u : ParabolicCkHolderSpace (k + 3) α E F hab) :
    timeDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 2) α E F hab u) =
      spatialFDerivL k α E F hab (timeDerivL (k + 1) α E F hab u) := by
  ext p
  rw [← mixedDerivL_zero_zero_apply
      (timeDerivL k α E (E →L[ℝ] F) hab (spatialFDerivL (k + 2) α E F hab u)) p 0,
    ← mixedDerivL_zero_zero_apply
      (spatialFDerivL k α E F hab (timeDerivL (k + 1) α E F hab u)) p 0,
    mixedDerivL_timeDerivL, mixedDerivL_spatialFDerivL_apply, mixedDerivL_spatialFDerivL_apply,
    mixedDerivL_timeDerivL]

end Space

end ParabolicCkHolderSpace

end TauCeti

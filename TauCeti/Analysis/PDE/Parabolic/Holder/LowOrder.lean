/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated
public import TauCeti.Analysis.PDE.Parabolic.Holder.One
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Bounded parabolic Hölder spaces of order at most two

The general parabolic Hölder scale `ParabolicCkHolderSpace k α E F hab` exists at every order
`k : ℕ` on a nondegenerate closed slab `E × [a, b]`, storing continuous multilinear mixed
derivatives `D_t^r D_x^m u` for `2 r + m ≤ k` together with `α`-Hölder top-order fields
(`2 r + m = k`) and uniform `(1 + α) / 2`-Hölder time slices one order below (`2 r + m = k - 1`).
At orders `k = 0`, `k = 1` and `k = 2`, the low-order spaces `HolderSpace α (slab a b) F`,
`ParabolicC1HolderSpace α E F a b` and `ParabolicC2HolderSpace α E F hab` describe the same
functions using curried Fréchet derivatives.

This file constructs the continuous linear equivalences between `ParabolicCkHolderSpace k` for
`k ≤ 2` and these three low-order spaces, preserving the underlying function and all recorded
derivative fields, and proves the exact norm identities and sharp norm-equivalence bounds:

* At order `k = 0`, `ParabolicCkHolderSpace 0` counts `‖u‖_∞` in both the `(0, 0)` bounded field
  and the `(0, 0)` Hölder field: `‖f‖ = ‖valueL f‖ + ‖equivHolderSpace f‖`, giving sharp bounds
  `‖equivHolderSpace f‖ ≤ ‖f‖ ≤ 2 * ‖equivHolderSpace f‖` (attained at `2` on nonzero constants).
* At order `k = 1`, `ParabolicCkHolderSpace 1` records `(0, 1)` both as a bounded field and as a
  Hölder field while matching the `(0, 0)` time-slice norm:
  `‖f‖ = ‖equivParabolicC1HolderSpace f‖ + ‖spatialFDerivBCF f‖`, with sharp bounds `1` and `2`
  against both the Banach norm and `ParabolicC1HolderSpace.fullNorm`.
* At order `k = 2`, `ParabolicCkHolderSpace 2` adds the `(0, 1)` gradient time slices and the
  `(0, 2)` and `(1, 0)` supremum norms: `‖f‖ = ‖equivParabolicC2HolderSpace f‖ +
  ‖timeSliceL 0 1 f‖ + ‖mixedDerivL 0 2 f‖ + ‖mixedDerivL 1 0 f‖`. Controlling the temporal
  `(1 + α) / 2`-seminorm of `D_x u` via `ParabolicC2HolderSpace.timeEHolderNorm_spatialFDeriv_le`
  yields sharp bounds `1` and `2` against both the reduced norm and
  `ParabolicC2HolderSpace.fullNorm` (approached at `2` on `u(x, t) = t - a` as `b → a⁺`).

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.equivHolderSpace`: continuous linear equivalence
  `ParabolicCkHolderSpace 0 α E F hab ≃L[ℝ] HolderSpace α (slab (E := E) a b) F`.
* `TauCeti.ParabolicCkHolderSpace.equivParabolicC1HolderSpace`: continuous linear equivalence
  `ParabolicCkHolderSpace 1 α E F hab ≃L[ℝ] ParabolicC1HolderSpace α E F a b`.
* `TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace`: continuous linear equivalence
  `ParabolicCkHolderSpace 2 α E F hab ≃L[ℝ] ParabolicC2HolderSpace α E F hab`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

namespace ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-! ### Currying helpers for Hölder and bounded continuous fields -/

private def uncurry0BCF (u : slab (E := E) a b →ᵇ F) :
    slab (E := E) a b →ᵇ (E [×0]→L[ℝ] F) :=
  (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
    |>.compLeftContinuousBounded (slab (E := E) a b) u

private def uncurry1BCF (ux : slab (E := E) a b →ᵇ (E →L[ℝ] F)) :
    slab (E := E) a b →ᵇ (E [×1]→L[ℝ] F) :=
  (continuousMultilinearCurryFin1 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
    |>.compLeftContinuousBounded (slab (E := E) a b) ux

private def uncurry0Holder (u : HolderSpace α (slab (E := E) a b) F) :
    HolderSpace α (slab (E := E) a b) (E [×0]→L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap u

private def uncurry1Holder (ux : HolderSpace α (slab (E := E) a b) (E →L[ℝ] F)) :
    HolderSpace α (slab (E := E) a b) (E [×1]→L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin1 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap ux

private def uncurry2Holder (uxx : HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F)) :
    HolderSpace α (slab (E := E) a b) (E [×2]→L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin2 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap uxx

private theorem hasFDerivAt_uncurry0_slabMk {u : slab (E := E) a b →ᵇ F}
    {ux : slab (E := E) a b → E →L[ℝ] F} {t : Icc a b} {x : E}
    (h : HasFDerivAt (fun y ↦ u (slabMk y t)) (ux (slabMk x t)) x) :
    HasFDerivAt (fun y ↦ uncurry0BCF u (slabMk y t))
      ((continuousMultilinearCurryFin1 ℝ E F).symm (ux (slabMk x t))).curryLeft x := by
  let L : F →L[ℝ] (E [×0]→L[ℝ] F) :=
    (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp x h
  have hfun : (L ∘ fun y ↦ u (slabMk y t)) = fun y ↦ uncurry0BCF u (slabMk y t) :=
    funext fun y ↦ by simp [L, uncurry0BCF]
  have hlin : L.comp (ux (slabMk x t)) =
      ((continuousMultilinearCurryFin1 ℝ E F).symm (ux (slabMk x t))).curryLeft := by
    ext v w
    simp [L, ContinuousMultilinearMap.curryLeft_apply, Subsingleton.elim w 0]
  rwa [hfun, hlin] at hd

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem timeEHolderNorm_comp_isometry {γ : ℝ≥0} {G G' : Type*}
    [PseudoEMetricSpace G] [PseudoEMetricSpace G'] {e : G → G'} (he : Isometry e)
    (v : slab (E := E) a b → G) :
    timeEHolderNorm γ (e ∘ v) = timeEHolderNorm γ v := by
  refine le_antisymm (timeEHolderNorm_le_iff.2 fun x t s ↦ ?_)
    (timeEHolderNorm_le_iff.2 fun x t s ↦ ?_)
  · simpa only [Function.comp_apply, he.edist_eq] using
      timeEHolderNorm_le_iff.1 (le_refl (timeEHolderNorm γ v)) x t s
  · simpa only [Function.comp_apply, ← he.edist_eq] using
      timeEHolderNorm_le_iff.1 (le_refl (timeEHolderNorm γ (e ∘ v))) x t s

private theorem timeEHolderNorm_eq_mixedDerivL_zero_zero {k : ℕ}
    (f : ParabolicCkHolderSpace k α E F hab) :
    timeEHolderNorm ((1 + α) / 2) (f : slab (E := E) a b → F) =
      timeEHolderNorm ((1 + α) / 2)
        (mixedDerivL 0 0 f : slab (E := E) a b → E [×0]→L[ℝ] F) := by
  have heq : (f : slab (E := E) a b → F) =
      continuousMultilinearCurryFin0 ℝ E F ∘ mixedDerivL 0 0 f :=
    funext fun p ↦ by simp
  rw [heq, timeEHolderNorm_comp_isometry (LinearIsometryEquiv.isometry _)]

/-! ### Order zero -/

private def toHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    HolderSpace α (slab (E := E) a b) F :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 0 0 f)

private theorem toHolderSpace_apply (f : ParabolicCkHolderSpace 0 α E F hab)
    (p : slab (E := E) a b) : toHolderSpace f p = f p := by
  rw [toHolderSpace, HolderSpace.compLeftL_apply, ← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL f rfl]
  simp

private def ofHolderSpaceFields (g : HolderSpace α (slab (E := E) a b) F) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => (uncurry0Holder g).toBoundedContinuousFunction
  | _, _ => 0

private def ofHolderSpace (g : HolderSpace α (slab (E := E) a b) F) :
    ParabolicCkHolderSpace 0 α E F hab :=
  mk (ofHolderSpaceFields g)
    (fun _ _ h ↦ absurd h (by omega))
    (fun _ _ h ↦ absurd h (by omega))
    (fun _ _ h ↦ absurd h (by omega))
    fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
      exact (uncurry0Holder g).memHolder

private theorem ofHolderSpace_apply (g : HolderSpace α (slab (E := E) a b) F)
    (p : slab (E := E) a b) : ofHolderSpace (hab := hab) g p = g p := by
  rw [ofHolderSpace, mk_apply]
  simp [ofHolderSpaceFields, uncurry0Holder, ContinuousMultilinearMap.curry0_apply]

private theorem norm_eq_toHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ = ‖valueL f‖ + ‖toHolderSpace f‖ := by
  have hs : timeSliceL 0 0 f = 0 := by
    rw [timeSliceL_of_ne (by omega), zero_apply]
  have hn : ‖toHolderSpace f‖ = ‖mixedDerivHolderL 0 0 f‖ :=
    HolderSpace.norm_compLeftL_linearIsometry _ _
  rw [norm_eq, parabolicDerivPairs_zero, Finset.sum_singleton]
  dsimp only
  rw [hs, norm_zero, zero_add, ← norm_valueL, ← hn]

private theorem toBoundedContinuousFunction_toHolderSpace
    (f : ParabolicCkHolderSpace 0 α E F hab) :
    (toHolderSpace f).toBoundedContinuousFunction = valueL f :=
  DFunLike.ext _ _ fun p ↦ by
    rw [HolderSpace.toBoundedContinuousFunction_apply, toHolderSpace_apply, valueL_apply]

private theorem norm_toHolderSpace_le (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖toHolderSpace f‖ ≤ ‖f‖ := by
  rw [norm_eq_toHolderSpace]
  exact le_add_of_nonneg_left (norm_nonneg (valueL f))

private theorem norm_le_two_mul_toHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ ≤ 2 * ‖toHolderSpace f‖ := by
  rw [norm_eq_toHolderSpace, ← toBoundedContinuousFunction_toHolderSpace, two_mul]
  exact add_le_add_left (toHolderSpace f).norm_toBoundedContinuousFunction_le _

private theorem norm_ofHolderSpace_le (g : HolderSpace α (slab (E := E) a b) F) :
    ‖ofHolderSpace (hab := hab) g‖ ≤ 2 * ‖g‖ := by
  have hg : toHolderSpace (ofHolderSpace (hab := hab) g) = g :=
    HolderSpace.ext fun p ↦ by rw [toHolderSpace_apply, ofHolderSpace_apply]
  simpa only [hg] using norm_le_two_mul_toHolderSpace (ofHolderSpace (hab := hab) g)

/-- Bounded parabolic Hölder maps of order zero are the bounded parabolically `α`-Hölder maps on
the slab. The equivalence preserves the underlying map, with exact norm relation
`ParabolicCkHolderSpace.norm_eq_norm_valueL_add_norm_equivHolderSpace` and sharp constants `1` and
`2`. -/
def equivHolderSpace :
    ParabolicCkHolderSpace 0 α E F hab ≃L[ℝ] HolderSpace α (slab (E := E) a b) F :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toHolderSpace
      invFun := ofHolderSpace
      map_add' f g := HolderSpace.ext fun p ↦ by simp [toHolderSpace_apply]
      map_smul' c f := HolderSpace.ext fun p ↦ by simp [toHolderSpace_apply]
      left_inv f := ext fun p ↦ by rw [ofHolderSpace_apply, toHolderSpace_apply]
      right_inv g := HolderSpace.ext fun p ↦ by rw [toHolderSpace_apply, ofHolderSpace_apply] }
    1 2 (fun f ↦ by simpa using norm_toHolderSpace_le f) norm_ofHolderSpace_le

/-- The order-zero equivalence preserves the underlying map. -/
@[simp]
theorem equivHolderSpace_apply (f : ParabolicCkHolderSpace 0 α E F hab) (p : slab (E := E) a b) :
    equivHolderSpace f p = f p :=
  toHolderSpace_apply f p

/-- The inverse order-zero equivalence preserves the underlying map. -/
@[simp]
theorem coe_equivHolderSpace_symm (g : HolderSpace α (slab (E := E) a b) F) :
    ⇑((equivHolderSpace (hab := hab)).symm g) = g :=
  funext (ofHolderSpace_apply g)

/-- The underlying bounded continuous function of `equivHolderSpace f` is `valueL f`. -/
@[simp]
theorem toBoundedContinuousFunction_equivHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    (equivHolderSpace f).toBoundedContinuousFunction = valueL f :=
  toBoundedContinuousFunction_toHolderSpace f

/-- The value field of `(equivHolderSpace).symm g` is `g.toBoundedContinuousFunction`. -/
@[simp]
theorem valueL_equivHolderSpace_symm (g : HolderSpace α (slab (E := E) a b) F) :
    valueL ((equivHolderSpace (hab := hab)).symm g) = g.toBoundedContinuousFunction :=
  DFunLike.ext _ _ fun p ↦ by simp

/-- At order zero, the `ParabolicCkHolderSpace` norm equals `‖valueL f‖ + ‖equivHolderSpace f‖`,
counting the supremum norm twice and the parabolic `α`-Hölder seminorm once. -/
theorem norm_eq_norm_valueL_add_norm_equivHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ = ‖valueL f‖ + ‖equivHolderSpace f‖ :=
  norm_eq_toHolderSpace f

/-- The `HolderSpace` norm is bounded by the order-zero `ParabolicCkHolderSpace` norm. -/
theorem norm_equivHolderSpace_le (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖equivHolderSpace f‖ ≤ ‖f‖ :=
  norm_toHolderSpace_le f

/-- The order-zero `ParabolicCkHolderSpace` norm is at most twice the `HolderSpace` norm. -/
theorem norm_le_two_mul_norm_equivHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ ≤ 2 * ‖equivHolderSpace f‖ :=
  norm_le_two_mul_toHolderSpace f

/-- The inverse order-zero equivalence has norm bound `2`. -/
theorem norm_equivHolderSpace_symm_le (g : HolderSpace α (slab (E := E) a b) F) :
    ‖(equivHolderSpace (hab := hab)).symm g‖ ≤ 2 * ‖g‖ :=
  norm_ofHolderSpace_le g

/-! ### Order one -/

private def spatialFDerivHolder (f : ParabolicCkHolderSpace 1 α E F hab) :
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 0 1 f)

private theorem spatialFDerivHolder_apply (f : ParabolicCkHolderSpace 1 α E F hab)
    (p : slab (E := E) a b) : spatialFDerivHolder f p = spatialFDerivBCF f p := by
  rw [spatialFDerivHolder, HolderSpace.compLeftL_apply,
    ← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL f rfl, spatialFDerivBCF_apply]
  rfl

private def toParabolicC1HolderSpace (f : ParabolicCkHolderSpace 1 α E F hab) :
    ParabolicC1HolderSpace α E F a b :=
  ParabolicC1HolderSpace.mk (valueL f) (spatialFDerivHolder f)
    (fun t x ↦ by
      rw [spatialFDerivHolder_apply]
      simpa only [valueL_apply] using hasFDerivAt_spatialSlice f t x)
    (by
      rw [coe_valueL, timeEHolderNorm_eq_mixedDerivL_zero_zero]
      exact timeEHolderNorm_mixedDerivL_lt_top f rfl)

private theorem toParabolicC1HolderSpace_apply (f : ParabolicCkHolderSpace 1 α E F hab)
    (p : slab (E := E) a b) : toParabolicC1HolderSpace f p = f p := by
  rw [toParabolicC1HolderSpace, ParabolicC1HolderSpace.mk_apply, valueL_apply]

private def ofParabolicC1HolderSpaceFields (g : ParabolicC1HolderSpace α E F a b) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => uncurry0BCF (ParabolicC1HolderSpace.valueL g)
  | 0, 1 => (uncurry1Holder (ParabolicC1HolderSpace.spatialFDerivL g)).toBoundedContinuousFunction
  | _, _ => 0

private def ofParabolicC1HolderSpace (g : ParabolicC1HolderSpace α E F a b) :
    ParabolicCkHolderSpace 1 α E F hab :=
  mk (ofParabolicC1HolderSpaceFields g)
    (fun r m h t x ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
      have hd := hasFDerivAt_uncurry0_slabMk (ParabolicC1HolderSpace.hasSpatialFDerivAt g t x)
      have hlin : (continuousMultilinearCurryFin1 ℝ E F).symm
            (ParabolicC1HolderSpace.spatialFDerivL g (slabMk x t)) =
          ofParabolicC1HolderSpaceFields g 0 1 (slabMk x t) := by
        simp [ofParabolicC1HolderSpaceFields, uncurry1Holder]
      simpa only [ofParabolicC1HolderSpaceFields, hlin] using hd)
    (fun _ _ h ↦ absurd h (by omega))
    (fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
      refine ⟨‖g‖₊, fun x t s ↦ ?_⟩
      simpa only [ofParabolicC1HolderSpaceFields, uncurry0BCF,
        ContinuousLinearMap.compLeftContinuousBounded_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        LinearIsometryEquiv.edist_map, ParabolicC1HolderSpace.valueL_apply] using
        timeEHolderNorm_le_iff.1 (ParabolicC1HolderSpace.timeEHolderNorm_le_nnnorm g) x t s)
    fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 1 := by omega
      exact (uncurry1Holder (ParabolicC1HolderSpace.spatialFDerivL g)).memHolder

private theorem ofParabolicC1HolderSpace_apply (g : ParabolicC1HolderSpace α E F a b)
    (p : slab (E := E) a b) : ofParabolicC1HolderSpace (hab := hab) g p = g p := by
  rw [ofParabolicC1HolderSpace, mk_apply]
  simp [ofParabolicC1HolderSpaceFields, uncurry0BCF, ContinuousMultilinearMap.curry0_apply]

private theorem norm_timeSliceL_toParabolicC1HolderSpace
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖ParabolicC1HolderSpace.timeSliceL (toParabolicC1HolderSpace f)‖ = ‖timeSliceL 0 0 f‖ := by
  have hx : ∀ x : E, ‖ParabolicC1HolderSpace.timeSliceL (toParabolicC1HolderSpace f) x‖ =
      ‖timeSliceL 0 0 f x‖ := fun x ↦ by
    have heq : ParabolicC1HolderSpace.timeSliceL (toParabolicC1HolderSpace f) x =
        HolderSpace.compLeftL
          (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
          (timeSliceL 0 0 f x) :=
      HolderSpace.ext fun t ↦ by
        rw [ParabolicC1HolderSpace.timeSliceL_apply, toParabolicC1HolderSpace_apply,
          HolderSpace.compLeftL_apply, timeSliceL_apply f rfl]
        simp
    rw [heq, HolderSpace.norm_compLeftL_linearIsometry]
  refine le_antisymm
    (lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦
      (hx x).trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x))
    (lp.norm_le_of_forall_le (norm_nonneg _) fun x ↦
      (hx x).symm.trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero _ x))

private theorem norm_eq_toParabolicC1HolderSpace (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖f‖ = ‖toParabolicC1HolderSpace f‖ + ‖spatialFDerivBCF f‖ := by
  have hh0 : mixedDerivHolderL 0 0 f = 0 := by
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply]
  have hs1 : timeSliceL 0 1 f = 0 := by
    rw [timeSliceL_of_ne (by omega), zero_apply]
  have hn1 : ‖spatialFDerivHolder f‖ = ‖mixedDerivHolderL 0 1 f‖ :=
    HolderSpace.norm_compLeftL_linearIsometry _ _
  rw [norm_eq, parabolicDerivPairs_one, Finset.sum_insert (by simp), Finset.sum_singleton]
  dsimp only
  simp only [hh0, hs1, norm_zero, ← norm_valueL, ← norm_spatialFDerivBCF,
    ← norm_timeSliceL_toParabolicC1HolderSpace, ← hn1, ParabolicC1HolderSpace.norm_eq,
    toParabolicC1HolderSpace, ParabolicC1HolderSpace.valueL_mk,
    ParabolicC1HolderSpace.spatialFDerivL_mk]
  ring

private theorem toBoundedContinuousFunction_spatialFDerivHolder
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    (spatialFDerivHolder f).toBoundedContinuousFunction = spatialFDerivBCF f :=
  DFunLike.ext _ _ fun p ↦ by
    rw [HolderSpace.toBoundedContinuousFunction_apply, spatialFDerivHolder_apply]

private theorem norm_toParabolicC1HolderSpace_le (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖toParabolicC1HolderSpace f‖ ≤ ‖f‖ := by
  rw [norm_eq_toParabolicC1HolderSpace]
  exact le_add_of_nonneg_right (norm_nonneg (spatialFDerivBCF f))

private theorem norm_le_two_mul_fullNorm_toParabolicC1HolderSpace
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖f‖ ≤ 2 * ParabolicC1HolderSpace.fullNorm (toParabolicC1HolderSpace f) := by
  have hS : ‖ParabolicC1HolderSpace.timeSliceL (toParabolicC1HolderSpace f)‖ ≤ ‖valueL f‖ +
      (timeEHolderNorm ((1 + α) / 2) (valueL f : slab (E := E) a b → F)).toReal := by
    rw [norm_timeSliceL_toParabolicC1HolderSpace, norm_valueL, coe_valueL,
      timeEHolderNorm_eq_mixedDerivL_zero_zero]
    exact norm_timeSliceL_le_norm_mixedDerivL_add_timeEHolderNorm f 0 0
  have hG : ‖spatialFDerivBCF f‖ ≤ ‖spatialFDerivHolder f‖ := by
    rw [← toBoundedContinuousFunction_spatialFDerivHolder]
    exact (spatialFDerivHolder f).norm_toBoundedContinuousFunction_le
  have hv : ParabolicC1HolderSpace.valueL (toParabolicC1HolderSpace f) = valueL f := by
    simp [toParabolicC1HolderSpace]
  have hx : ParabolicC1HolderSpace.spatialFDerivL (toParabolicC1HolderSpace f) =
      spatialFDerivHolder f := by
    simp [toParabolicC1HolderSpace]
  rw [norm_eq_toParabolicC1HolderSpace, ParabolicC1HolderSpace.norm_eq,
    ParabolicC1HolderSpace.fullNorm_def, hv, hx]
  linarith [ENNReal.toReal_nonneg
    (a := timeEHolderNorm ((1 + α) / 2) (valueL f : slab (E := E) a b → F))]

private theorem norm_ofParabolicC1HolderSpace_le (g : ParabolicC1HolderSpace α E F a b) :
    ‖ofParabolicC1HolderSpace (hab := hab) g‖ ≤ 2 * ‖g‖ := by
  set f := ofParabolicC1HolderSpace (hab := hab) g
  have hg : toParabolicC1HolderSpace f = g :=
    ParabolicC1HolderSpace.ext fun p ↦ by
      rw [toParabolicC1HolderSpace_apply, ofParabolicC1HolderSpace_apply]
  have h := (norm_le_two_mul_fullNorm_toParabolicC1HolderSpace f).trans
    (mul_le_mul_of_nonneg_left
      (ParabolicC1HolderSpace.fullNorm_le_norm_le (toParabolicC1HolderSpace f)).1 zero_le_two)
  rwa [hg] at h

/-- Bounded parabolic Hölder maps of order one in `ParabolicCkHolderSpace` are the elements of
`ParabolicC1HolderSpace`. The equivalence preserves the underlying map and spatial gradient, with
exact norm identity `norm_eq_norm_equivParabolicC1HolderSpace_add_norm_spatialFDerivBCF` and sharp
constants `1` and `2`. -/
def equivParabolicC1HolderSpace :
    ParabolicCkHolderSpace 1 α E F hab ≃L[ℝ] ParabolicC1HolderSpace α E F a b :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toParabolicC1HolderSpace
      invFun := ofParabolicC1HolderSpace
      map_add' f g := ParabolicC1HolderSpace.ext fun p ↦ by simp [toParabolicC1HolderSpace_apply]
      map_smul' c f := ParabolicC1HolderSpace.ext fun p ↦ by simp [toParabolicC1HolderSpace_apply]
      left_inv f := ext fun p ↦ by
        rw [ofParabolicC1HolderSpace_apply, toParabolicC1HolderSpace_apply]
      right_inv g := ParabolicC1HolderSpace.ext fun p ↦ by
        rw [toParabolicC1HolderSpace_apply, ofParabolicC1HolderSpace_apply] }
    1 2 (fun f ↦ by simpa using norm_toParabolicC1HolderSpace_le f) norm_ofParabolicC1HolderSpace_le

private theorem equivParabolicC1HolderSpace_eq (f : ParabolicCkHolderSpace 1 α E F hab) :
    equivParabolicC1HolderSpace f = toParabolicC1HolderSpace f :=
  rfl

/-- The order-one equivalence preserves the underlying map. -/
theorem equivParabolicC1HolderSpace_apply (f : ParabolicCkHolderSpace 1 α E F hab)
    (p : slab (E := E) a b) : equivParabolicC1HolderSpace f p = f p :=
  toParabolicC1HolderSpace_apply f p

/-- The inverse order-one equivalence preserves the underlying map. -/
@[simp]
theorem coe_equivParabolicC1HolderSpace_symm (g : ParabolicC1HolderSpace α E F a b) :
    ⇑((equivParabolicC1HolderSpace (hab := hab)).symm g) = g :=
  funext (ofParabolicC1HolderSpace_apply g)

/-- The order-one equivalence preserves the bounded continuous value field. -/
@[simp]
theorem valueL_equivParabolicC1HolderSpace (f : ParabolicCkHolderSpace 1 α E F hab) :
    ParabolicC1HolderSpace.valueL (equivParabolicC1HolderSpace f) = valueL f := by
  rw [equivParabolicC1HolderSpace_eq, toParabolicC1HolderSpace, ParabolicC1HolderSpace.valueL_mk]

/-- The inverse order-one equivalence preserves the bounded continuous value field. -/
@[simp]
theorem valueL_equivParabolicC1HolderSpace_symm (g : ParabolicC1HolderSpace α E F a b) :
    valueL ((equivParabolicC1HolderSpace (hab := hab)).symm g) = ParabolicC1HolderSpace.valueL g :=
  DFunLike.ext _ _ fun p ↦ by simp

/-- The order-one equivalence maps `spatialFDerivBCF` to `ParabolicC1HolderSpace.spatialFDerivL`. -/
theorem spatialFDerivL_equivParabolicC1HolderSpace_apply (f : ParabolicCkHolderSpace 1 α E F hab)
    (p : slab (E := E) a b) :
    ParabolicC1HolderSpace.spatialFDerivL (equivParabolicC1HolderSpace f) p =
      spatialFDerivBCF f p := by
  rw [equivParabolicC1HolderSpace_eq, toParabolicC1HolderSpace,
    ParabolicC1HolderSpace.spatialFDerivL_mk, spatialFDerivHolder_apply]

/-- Forgetting the Hölder bound on the gradient of `equivParabolicC1HolderSpace f` recovers
`spatialFDerivBCF f`. -/
@[simp]
theorem toBoundedContinuousFunction_spatialFDerivL_equivParabolicC1HolderSpace
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    (ParabolicC1HolderSpace.spatialFDerivL (equivParabolicC1HolderSpace f)
      |>.toBoundedContinuousFunction) = spatialFDerivBCF f :=
  DFunLike.ext _ _ fun p ↦ by
    rw [HolderSpace.toBoundedContinuousFunction_apply,
      spatialFDerivL_equivParabolicC1HolderSpace_apply]

/-- The curried gradient field of `(equivParabolicC1HolderSpace).symm g` is the underlying bounded
continuous function of `ParabolicC1HolderSpace.spatialFDerivL g`. -/
@[simp]
theorem spatialFDerivBCF_equivParabolicC1HolderSpace_symm (g : ParabolicC1HolderSpace α E F a b) :
    spatialFDerivBCF ((equivParabolicC1HolderSpace (hab := hab)).symm g) =
      (ParabolicC1HolderSpace.spatialFDerivL g).toBoundedContinuousFunction := by
  have h := toBoundedContinuousFunction_spatialFDerivL_equivParabolicC1HolderSpace
    ((equivParabolicC1HolderSpace (hab := hab)).symm g)
  rwa [ContinuousLinearEquiv.apply_symm_apply, eq_comm] at h

/-- The `ℓ^∞` norm of the family of Hölder time slices agrees across the order-one equivalence. -/
theorem norm_timeSliceL_equivParabolicC1HolderSpace (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖ParabolicC1HolderSpace.timeSliceL (equivParabolicC1HolderSpace f)‖ = ‖timeSliceL 0 0 f‖ := by
  rw [equivParabolicC1HolderSpace_eq]; exact norm_timeSliceL_toParabolicC1HolderSpace f

/-- At order one, the `ParabolicCkHolderSpace` norm exceeds the `ParabolicC1HolderSpace` norm by
the supremum norm of the spatial gradient. -/
theorem norm_eq_norm_equivParabolicC1HolderSpace_add_norm_spatialFDerivBCF
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖f‖ = ‖equivParabolicC1HolderSpace f‖ + ‖spatialFDerivBCF f‖ := by
  rw [equivParabolicC1HolderSpace_eq]; exact norm_eq_toParabolicC1HolderSpace f

/-- The `ParabolicC1HolderSpace` norm is at most the order-one `ParabolicCkHolderSpace` norm. -/
theorem norm_equivParabolicC1HolderSpace_le (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖equivParabolicC1HolderSpace f‖ ≤ ‖f‖ := by
  rw [equivParabolicC1HolderSpace_eq]; exact norm_toParabolicC1HolderSpace_le f

/-- The full order-one parabolic norm is at most the `ParabolicCkHolderSpace 1` norm. -/
theorem fullNorm_equivParabolicC1HolderSpace_le (f : ParabolicCkHolderSpace 1 α E F hab) :
    ParabolicC1HolderSpace.fullNorm (equivParabolicC1HolderSpace f) ≤ ‖f‖ :=
  (ParabolicC1HolderSpace.fullNorm_le_norm_le (equivParabolicC1HolderSpace f)).1.trans
    (norm_equivParabolicC1HolderSpace_le f)

/-- The `ParabolicCkHolderSpace 1` norm is at most twice `ParabolicC1HolderSpace.fullNorm`. -/
theorem norm_le_two_mul_fullNorm_equivParabolicC1HolderSpace
    (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖f‖ ≤ 2 * ParabolicC1HolderSpace.fullNorm (equivParabolicC1HolderSpace f) := by
  rw [equivParabolicC1HolderSpace_eq]; exact norm_le_two_mul_fullNorm_toParabolicC1HolderSpace f

/-- The `ParabolicCkHolderSpace 1` norm is at most twice the `ParabolicC1HolderSpace` norm. -/
theorem norm_le_two_mul_norm_equivParabolicC1HolderSpace (f : ParabolicCkHolderSpace 1 α E F hab) :
    ‖f‖ ≤ 2 * ‖equivParabolicC1HolderSpace f‖ :=
  (norm_le_two_mul_fullNorm_equivParabolicC1HolderSpace f).trans
    (mul_le_mul_of_nonneg_left
      (ParabolicC1HolderSpace.fullNorm_le_norm_le (equivParabolicC1HolderSpace f)).1 zero_le_two)

/-- The inverse order-one equivalence has norm bound `2` against `ParabolicC1HolderSpace.fullNorm`.
-/
theorem norm_equivParabolicC1HolderSpace_symm_le_two_mul_fullNorm
    (g : ParabolicC1HolderSpace α E F a b) :
    ‖(equivParabolicC1HolderSpace (hab := hab)).symm g‖ ≤
      2 * ParabolicC1HolderSpace.fullNorm g := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    norm_le_two_mul_fullNorm_equivParabolicC1HolderSpace
      ((equivParabolicC1HolderSpace (hab := hab)).symm g)

/-- The inverse order-one equivalence has norm bound `2`. -/
theorem norm_equivParabolicC1HolderSpace_symm_le (g : ParabolicC1HolderSpace α E F a b) :
    ‖(equivParabolicC1HolderSpace (hab := hab)).symm g‖ ≤ 2 * ‖g‖ :=
  norm_ofParabolicC1HolderSpace_le g

/-! ### Order two -/

private def spatialSecondFDerivHolder (f : ParabolicCkHolderSpace 2 α E F hab) :
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin2 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 0 2 f)

private def timeDerivHolder (f : ParabolicCkHolderSpace 2 α E F hab) :
    HolderSpace α (slab (E := E) a b) F :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 1 0 f)

private theorem spatialSecondFDerivHolder_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) :
    spatialSecondFDerivHolder f p = continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 f p) := by
  rw [spatialSecondFDerivHolder, HolderSpace.compLeftL_apply,
    ← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL f rfl]
  rfl

private theorem timeDerivHolder_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) :
    timeDerivHolder f p = (mixedDerivL 1 0 f p).curry0 := by
  rw [timeDerivHolder, HolderSpace.compLeftL_apply,
    ← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL f rfl]
  rfl

private theorem hasFDerivAt_spatialFDerivBCF (f : ParabolicCkHolderSpace 2 α E F hab)
    (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ spatialFDerivBCF f (slabMk y t))
      (spatialSecondFDerivHolder f (slabMk x t)) x := by
  let L : (E [×1]→L[ℝ] F) →L[ℝ] (E →L[ℝ] F) :=
    (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp x (hasFDerivAt_mixedDerivL f (r := 0) (m := 1) (by omega) t x)
  have hfun : (L ∘ fun y ↦ mixedDerivL 0 1 f (slabMk y t)) =
      fun y ↦ spatialFDerivBCF f (slabMk y t) :=
    funext fun y ↦ (spatialFDerivBCF_apply f (slabMk y t)).symm
  have hlin : L.comp (mixedDerivL 0 2 f (slabMk x t)).curryLeft =
      spatialSecondFDerivHolder f (slabMk x t) := by
    ext v w
    rw [spatialSecondFDerivHolder_apply, continuousMultilinearCurryFin2_apply]
    simp only [L, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.coe_toLinearIsometry, continuousMultilinearCurryFin1_apply,
      ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rwa [hfun, hlin] at hd

private theorem hasDerivWithinAt_valueL (f : ParabolicCkHolderSpace 2 α E F hab)
    (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (valueL f) x)
      (timeDerivHolder f (slabMk x t)) (Icc a b) t := by
  let L : (E [×0]→L[ℝ] F) →L[ℝ] F :=
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
  have hd := HasFDerivAt.comp_hasDerivWithinAt (t : ℝ) L.hasFDerivAt
    (hasDerivWithinAt_mixedDerivL f (r := 0) (m := 0) (by omega) x t)
  have hfun : (L ∘ ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL 0 0 f) x) =
      ParabolicC2HolderSpace.timeExtension hab.le (valueL f) x :=
    funext fun s ↦ by simp [L, ParabolicC2HolderSpace.timeExtension_def]
  have hval : L (mixedDerivL 1 0 f (slabMk x t)) = timeDerivHolder f (slabMk x t) :=
    (timeDerivHolder_apply f (slabMk x t)).symm
  rwa [hfun, hval] at hd

private def toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace α E F hab :=
  ParabolicC2HolderSpace.mk (valueL f) (spatialFDerivBCF f) (spatialSecondFDerivHolder f)
    (timeDerivHolder f)
    (fun t x ↦ by simpa only [valueL_apply] using hasFDerivAt_spatialSlice f t x)
    (hasFDerivAt_spatialFDerivBCF f)
    (hasDerivWithinAt_valueL f)

private theorem toParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) : toParabolicC2HolderSpace f p = f p := by
  rw [toParabolicC2HolderSpace, ParabolicC2HolderSpace.mk_apply, valueL_apply]

private def ofParabolicC2HolderSpaceFields (g : ParabolicC2HolderSpace α E F hab) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => uncurry0BCF (ParabolicC2HolderSpace.valueL g)
  | 0, 1 => uncurry1BCF (ParabolicC2HolderSpace.spatialFDerivL g)
  | 0, 2 =>
      (uncurry2Holder (ParabolicC2HolderSpace.spatialSecondFDerivL g)).toBoundedContinuousFunction
  | 1, 0 => (uncurry0Holder (ParabolicC2HolderSpace.timeDerivL g)).toBoundedContinuousFunction
  | _, _ => 0

private theorem hasFDerivAt_uncurry1_slabMk (g : ParabolicC2HolderSpace α E F hab)
    (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ uncurry1BCF (ParabolicC2HolderSpace.spatialFDerivL g) (slabMk y t))
      (ofParabolicC2HolderSpaceFields g 0 2 (slabMk x t)).curryLeft x := by
  let L : (E →L[ℝ] F) →L[ℝ] (E [×1]→L[ℝ] F) :=
    (continuousMultilinearCurryFin1 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp x (ParabolicC2HolderSpace.hasSpatialSecondFDerivAt g t x)
  have hfun : (L ∘ fun y ↦ ParabolicC2HolderSpace.spatialFDerivL g (slabMk y t)) =
      fun y ↦ uncurry1BCF (ParabolicC2HolderSpace.spatialFDerivL g) (slabMk y t) :=
    funext fun y ↦ by simp [L, uncurry1BCF]
  have hlin : L.comp (ParabolicC2HolderSpace.spatialSecondFDerivL g (slabMk x t)) =
      (ofParabolicC2HolderSpaceFields g 0 2 (slabMk x t)).curryLeft := by
    ext v w
    simp [L, ofParabolicC2HolderSpaceFields, uncurry2Holder,
      ContinuousMultilinearMap.curryLeft_apply]
  rwa [hfun, hlin] at hd

private theorem holderWith_ofParabolicC2HolderSpaceFields_zero_one
    (g : ParabolicC2HolderSpace α E F hab) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2)
      fun t : Icc a b ↦ ofParabolicC2HolderSpaceFields g 0 1 (slabMk x t) := by
  let C : ℝ≥0 := nnHolderNorm α
      ((ParabolicC2HolderSpace.spatialSecondFDerivL g).toBoundedContinuousFunction : _ → _) +
    nnHolderNorm α ((ParabolicC2HolderSpace.timeDerivL g).toBoundedContinuousFunction : _ → _)
  have hle := ParabolicC2HolderSpace.timeEHolderNorm_spatialFDeriv_le g
  rw [← (ParabolicC2HolderSpace.spatialSecondFDerivL g).memHolder.coe_nnHolderNorm_eq_eHolderNorm,
    ← (ParabolicC2HolderSpace.timeDerivL g).memHolder.coe_nnHolderNorm_eq_eHolderNorm,
    ← ENNReal.coe_add] at hle
  refine ⟨C, fun x t s ↦ ?_⟩
  simpa only [ofParabolicC2HolderSpaceFields, uncurry1BCF,
    ContinuousLinearMap.compLeftContinuousBounded_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.edist_map] using
    timeEHolderNorm_le_iff.1 hle x t s

private def ofParabolicC2HolderSpace (g : ParabolicC2HolderSpace α E F hab) :
    ParabolicCkHolderSpace 2 α E F hab :=
  mk (ofParabolicC2HolderSpaceFields g)
    (fun r m h t x ↦ by
      obtain ⟨rfl, rfl | rfl⟩ : r = 0 ∧ (m = 0 ∨ m = 1) := by omega
      · exact hasFDerivAt_uncurry0_slabMk (ParabolicC2HolderSpace.hasSpatialFDerivAt g t x)
      · exact hasFDerivAt_uncurry1_slabMk g t x)
    (fun r m h x t ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
      let L : F →L[ℝ] (E [×0]→L[ℝ] F) :=
        (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      have hd := HasFDerivAt.comp_hasDerivWithinAt (t : ℝ) L.hasFDerivAt
        (ParabolicC2HolderSpace.hasTimeDerivWithinAt g x t)
      have hfun : (L ∘ ParabolicC2HolderSpace.timeExtension hab.le g x) =
          ParabolicC2HolderSpace.timeExtension hab.le (ofParabolicC2HolderSpaceFields g 0 0) x :=
        funext fun s ↦ by simp [L, ofParabolicC2HolderSpaceFields, uncurry0BCF,
          ParabolicC2HolderSpace.timeExtension_def]
      have hval : L (ParabolicC2HolderSpace.timeDerivL g (slabMk x t)) =
          ofParabolicC2HolderSpaceFields g 1 0 (slabMk x t) := by
        simp [L, ofParabolicC2HolderSpaceFields, uncurry0Holder]
      rwa [hfun, hval] at hd)
    (fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 1 := by omega
      exact holderWith_ofParabolicC2HolderSpaceFields_zero_one g)
    fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (r = 0 ∧ m = 2) ∨ (r = 1 ∧ m = 0) := by omega
      · exact (uncurry2Holder (ParabolicC2HolderSpace.spatialSecondFDerivL g)).memHolder
      · exact (uncurry0Holder (ParabolicC2HolderSpace.timeDerivL g)).memHolder

private theorem ofParabolicC2HolderSpace_apply (g : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : ofParabolicC2HolderSpace g p = g p := by
  rw [ofParabolicC2HolderSpace, mk_apply]
  simp [ofParabolicC2HolderSpaceFields, uncurry0BCF, ContinuousMultilinearMap.curry0_apply]

private theorem norm_eq_toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ = ‖toParabolicC2HolderSpace f‖ + ‖timeSliceL 0 1 f‖ +
      ‖mixedDerivL 0 2 f‖ + ‖mixedDerivL 1 0 f‖ := by
  have hs00 : timeSliceL 0 0 f = 0 := by rw [timeSliceL_of_ne (by omega), zero_apply]
  have hh00 : mixedDerivHolderL 0 0 f = 0 := by
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply]
  have hh01 : mixedDerivHolderL 0 1 f = 0 := by
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply]
  have hs02 : timeSliceL 0 2 f = 0 := by rw [timeSliceL_of_ne (by omega), zero_apply]
  have hs10 : timeSliceL 1 0 f = 0 := by rw [timeSliceL_of_ne (by omega), zero_apply]
  have hn02 : ‖spatialSecondFDerivHolder f‖ = ‖mixedDerivHolderL 0 2 f‖ :=
    HolderSpace.norm_compLeftL_linearIsometry _ _
  have hn10 : ‖timeDerivHolder f‖ = ‖mixedDerivHolderL 1 0 f‖ :=
    HolderSpace.norm_compLeftL_linearIsometry _ _
  rw [norm_eq, parabolicDerivPairs_two, Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
  dsimp only
  simp only [hs00, hh00, hh01, hs02, hs10, norm_zero, ← norm_valueL, ← norm_spatialFDerivBCF,
    ← hn02, ← hn10, ParabolicC2HolderSpace.norm_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.valueL_mk, ParabolicC2HolderSpace.spatialFDerivL_mk,
    ParabolicC2HolderSpace.spatialSecondFDerivL_mk, ParabolicC2HolderSpace.timeDerivL_mk]
  ring

private theorem timeEHolderNorm_spatialFDerivBCF_eq {k : ℕ}
    (f : ParabolicCkHolderSpace k α E F hab) :
    timeEHolderNorm ((1 + α) / 2)
        (spatialFDerivBCF f : slab (E := E) a b → E →L[ℝ] F) =
      timeEHolderNorm ((1 + α) / 2)
        (mixedDerivL 0 1 f : slab (E := E) a b → E [×1]→L[ℝ] F) := by
  have heq : (spatialFDerivBCF f : slab (E := E) a b → E →L[ℝ] F) =
      continuousMultilinearCurryFin1 ℝ E F ∘ mixedDerivL 0 1 f :=
    funext (spatialFDerivBCF_apply f)
  rw [heq, timeEHolderNorm_comp_isometry (LinearIsometryEquiv.isometry _)]

private theorem fullNorm_toParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.fullNorm (toParabolicC2HolderSpace f) ≤ ‖f‖ := by
  have hgx : ParabolicC2HolderSpace.spatialFDerivL (toParabolicC2HolderSpace f) =
      spatialFDerivBCF f := by simp [toParabolicC2HolderSpace]
  have hT : (timeEHolderNorm ((1 + α) / 2)
      (ParabolicC2HolderSpace.spatialFDerivL (toParabolicC2HolderSpace f) : _ → _)).toReal ≤
      ‖timeSliceL 0 1 f‖ := by
    rw [hgx, timeEHolderNorm_spatialFDerivBCF_eq]
    simpa using ENNReal.toReal_mono ENNReal.coe_ne_top (timeEHolderNorm_mixedDerivL_le f rfl)
  rw [ParabolicC2HolderSpace.fullNorm_def, norm_eq_toParabolicC2HolderSpace]
  linarith [norm_nonneg (mixedDerivL 0 2 f), norm_nonneg (mixedDerivL 1 0 f)]

private theorem norm_toParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖toParabolicC2HolderSpace f‖ ≤ ‖f‖ :=
  (ParabolicC2HolderSpace.norm_le_fullNorm_le (toParabolicC2HolderSpace f)).1.trans
    (fullNorm_toParabolicC2HolderSpace_le f)

private theorem norm_le_two_mul_toParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ ≤ 2 * ‖toParabolicC2HolderSpace f‖ := by
  set g := toParabolicC2HolderSpace f
  have hgx : ParabolicC2HolderSpace.spatialFDerivL g = spatialFDerivBCF f := by
    simp [g, toParabolicC2HolderSpace]
  have hgxx : ParabolicC2HolderSpace.spatialSecondFDerivL g = spatialSecondFDerivHolder f := by
    simp [g, toParabolicC2HolderSpace]
  have hgt : ParabolicC2HolderSpace.timeDerivL g = timeDerivHolder f := by
    simp [g, toParabolicC2HolderSpace]
  have hS : ‖timeSliceL 0 1 f‖ ≤ ‖ParabolicC2HolderSpace.spatialFDerivL g‖ +
      (timeEHolderNorm ((1 + α) / 2) (ParabolicC2HolderSpace.spatialFDerivL g : _ → _)).toReal := by
    rw [hgx, norm_spatialFDerivBCF, timeEHolderNorm_spatialFDerivBCF_eq]
    exact norm_timeSliceL_le_norm_mixedDerivL_add_timeEHolderNorm f 0 1
  have hle := ParabolicC2HolderSpace.timeEHolderNorm_spatialFDeriv_le g
  rw [← (ParabolicC2HolderSpace.spatialSecondFDerivL g).memHolder.coe_nnHolderNorm_eq_eHolderNorm,
    ← (ParabolicC2HolderSpace.timeDerivL g).memHolder.coe_nnHolderNorm_eq_eHolderNorm,
    ← ENNReal.coe_add] at hle
  have hT := ENNReal.toReal_mono ENNReal.coe_ne_top hle
  rw [ENNReal.coe_toReal, NNReal.coe_add] at hT
  have h02 : ‖ParabolicC2HolderSpace.spatialSecondFDerivL g‖ = ‖mixedDerivL 0 2 f‖ +
      nnHolderNorm α ((ParabolicC2HolderSpace.spatialSecondFDerivL g).toBoundedContinuousFunction :
        _ → _) := by
    have hsup : ‖(spatialSecondFDerivHolder f).toBoundedContinuousFunction‖ =
        ‖mixedDerivL 0 2 f‖ := by
      simp only [BoundedContinuousFunction.norm_eq_iSup_norm,
        HolderSpace.toBoundedContinuousFunction_apply, spatialSecondFDerivHolder_apply,
        LinearIsometryEquiv.norm_map]
    rw [hgxx, HolderSpace.norm_def, hsup]
  have h10 : ‖ParabolicC2HolderSpace.timeDerivL g‖ = ‖mixedDerivL 1 0 f‖ +
      nnHolderNorm α
        ((ParabolicC2HolderSpace.timeDerivL g).toBoundedContinuousFunction : _ → _) := by
    have hsup : ‖(timeDerivHolder f).toBoundedContinuousFunction‖ = ‖mixedDerivL 1 0 f‖ := by
      simp only [BoundedContinuousFunction.norm_eq_iSup_norm,
        HolderSpace.toBoundedContinuousFunction_apply, timeDerivHolder_apply,
        ContinuousMultilinearMap.curry0_apply, ContinuousMultilinearMap.fin0_apply_norm]
    rw [hgt, HolderSpace.norm_def, hsup]
  have hg_eq := ParabolicC2HolderSpace.norm_eq g
  rw [norm_eq_toParabolicC2HolderSpace]
  linarith [norm_nonneg (ParabolicC2HolderSpace.valueL g)]

private theorem norm_ofParabolicC2HolderSpace_le (g : ParabolicC2HolderSpace α E F hab) :
    ‖ofParabolicC2HolderSpace g‖ ≤ 2 * ‖g‖ := by
  have hg : toParabolicC2HolderSpace (ofParabolicC2HolderSpace g) = g :=
    ParabolicC2HolderSpace.ext fun p ↦ by
      rw [toParabolicC2HolderSpace_apply, ofParabolicC2HolderSpace_apply]
  simpa only [hg] using norm_le_two_mul_toParabolicC2HolderSpace (ofParabolicC2HolderSpace g)

/-- Bounded parabolic Hölder maps of order two in `ParabolicCkHolderSpace` are the elements of
`ParabolicC2HolderSpace`. The equivalence preserves the underlying map and all spatial and temporal
derivative fields, with exact norm identity `norm_eq_norm_equivParabolicC2HolderSpace_add` and
sharp constants `1` and `2`. -/
def equivParabolicC2HolderSpace :
    ParabolicCkHolderSpace 2 α E F hab ≃L[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toParabolicC2HolderSpace
      invFun := ofParabolicC2HolderSpace
      map_add' f g := ParabolicC2HolderSpace.ext fun p ↦ by simp [toParabolicC2HolderSpace_apply]
      map_smul' c f := ParabolicC2HolderSpace.ext fun p ↦ by simp [toParabolicC2HolderSpace_apply]
      left_inv f := ext fun p ↦ by
        rw [ofParabolicC2HolderSpace_apply, toParabolicC2HolderSpace_apply]
      right_inv g := ParabolicC2HolderSpace.ext fun p ↦ by
        rw [toParabolicC2HolderSpace_apply, ofParabolicC2HolderSpace_apply] }
    1 2 (fun f ↦ by simpa using norm_toParabolicC2HolderSpace_le f) norm_ofParabolicC2HolderSpace_le

private theorem equivParabolicC2HolderSpace_eq (f : ParabolicCkHolderSpace 2 α E F hab) :
    equivParabolicC2HolderSpace f = toParabolicC2HolderSpace f :=
  rfl

/-- The order-two equivalence preserves the underlying map. -/
theorem equivParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) : equivParabolicC2HolderSpace f p = f p :=
  toParabolicC2HolderSpace_apply f p

/-- The inverse order-two equivalence preserves the underlying map. -/
@[simp]
theorem coe_equivParabolicC2HolderSpace_symm (g : ParabolicC2HolderSpace α E F hab) :
    ⇑(equivParabolicC2HolderSpace.symm g) = g :=
  funext (ofParabolicC2HolderSpace_apply g)

/-- The order-two equivalence preserves the bounded continuous value field. -/
@[simp]
theorem valueL_equivParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.valueL (equivParabolicC2HolderSpace f) = valueL f := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace, ParabolicC2HolderSpace.valueL_mk]

/-- The inverse order-two equivalence preserves the bounded continuous value field. -/
@[simp]
theorem valueL_equivParabolicC2HolderSpace_symm (g : ParabolicC2HolderSpace α E F hab) :
    valueL (equivParabolicC2HolderSpace.symm g) = ParabolicC2HolderSpace.valueL g :=
  DFunLike.ext _ _ fun p ↦ by simp

/-- The order-two equivalence maps `spatialFDerivBCF` to `ParabolicC2HolderSpace.spatialFDerivL`. -/
@[simp]
theorem spatialFDerivL_equivParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.spatialFDerivL (equivParabolicC2HolderSpace f) = spatialFDerivBCF f := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.spatialFDerivL_mk]

/-- The inverse order-two equivalence maps `ParabolicC2HolderSpace.spatialFDerivL` to
`spatialFDerivBCF`. -/
@[simp]
theorem spatialFDerivBCF_equivParabolicC2HolderSpace_symm (g : ParabolicC2HolderSpace α E F hab) :
    spatialFDerivBCF (equivParabolicC2HolderSpace.symm g) =
      ParabolicC2HolderSpace.spatialFDerivL g := by
  have h := spatialFDerivL_equivParabolicC2HolderSpace (equivParabolicC2HolderSpace.symm g)
  rwa [ContinuousLinearEquiv.apply_symm_apply, eq_comm] at h

/-- The spatial Hessian of `equivParabolicC2HolderSpace f` is the curried `(0, 2)` mixed
derivative field. -/
@[simp]
theorem spatialSecondFDerivL_equivParabolicC2HolderSpace_apply
    (f : ParabolicCkHolderSpace 2 α E F hab) (p : slab (E := E) a b) :
    ParabolicC2HolderSpace.spatialSecondFDerivL (equivParabolicC2HolderSpace f) p =
      continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 f p) := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.spatialSecondFDerivL_mk, spatialSecondFDerivHolder_apply]

/-- The `(0, 2)` mixed derivative field of `equivParabolicC2HolderSpace.symm g` is the uncurried
spatial Hessian of `g`. -/
@[simp]
theorem mixedDerivL_zero_two_equivParabolicC2HolderSpace_symm_apply
    (g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    mixedDerivL 0 2 (equivParabolicC2HolderSpace.symm g) p =
      (continuousMultilinearCurryFin2 ℝ E F).symm
        (ParabolicC2HolderSpace.spatialSecondFDerivL g p) := by
  have h := spatialSecondFDerivL_equivParabolicC2HolderSpace_apply
    (equivParabolicC2HolderSpace.symm g) p
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (LinearIsometryEquiv.eq_symm_apply _).2 h.symm

/-- The time derivative of `equivParabolicC2HolderSpace f` is the `(1, 0)` mixed derivative field
evaluated at `0`. -/
@[simp]
theorem timeDerivL_equivParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) :
    ParabolicC2HolderSpace.timeDerivL (equivParabolicC2HolderSpace f) p =
      mixedDerivL 1 0 f p 0 := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.timeDerivL_mk, timeDerivHolder_apply,
    ContinuousMultilinearMap.curry0_apply]

/-- Evaluating the `(1, 0)` mixed derivative field of `equivParabolicC2HolderSpace.symm g` gives
`ParabolicC2HolderSpace.timeDerivL g`. -/
@[simp]
theorem mixedDerivL_one_zero_equivParabolicC2HolderSpace_symm_apply
    (g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) (v : Fin 0 → E) :
    mixedDerivL 1 0 (equivParabolicC2HolderSpace.symm g) p v =
      ParabolicC2HolderSpace.timeDerivL g p := by
  have h := timeDerivL_equivParabolicC2HolderSpace_apply (equivParabolicC2HolderSpace.symm g) p
  rw [ContinuousLinearEquiv.apply_symm_apply, ← Subsingleton.elim v 0] at h
  exact h.symm

/-- The Hölder norm of the curried spatial Hessian agrees with `‖mixedDerivHolderL 0 2 f‖`. -/
theorem norm_spatialSecondFDerivL_equivParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖ParabolicC2HolderSpace.spatialSecondFDerivL (equivParabolicC2HolderSpace f)‖ =
      ‖mixedDerivHolderL 0 2 f‖ := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.spatialSecondFDerivL_mk]
  exact HolderSpace.norm_compLeftL_linearIsometry _ _

/-- The Hölder norm of the time derivative agrees with `‖mixedDerivHolderL 1 0 f‖`. -/
theorem norm_timeDerivL_equivParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖ParabolicC2HolderSpace.timeDerivL (equivParabolicC2HolderSpace f)‖ =
      ‖mixedDerivHolderL 1 0 f‖ := by
  rw [equivParabolicC2HolderSpace_eq, toParabolicC2HolderSpace,
    ParabolicC2HolderSpace.timeDerivL_mk]
  exact HolderSpace.norm_compLeftL_linearIsometry _ _

/-- At order two, the `ParabolicCkHolderSpace` norm equals the reduced `ParabolicC2HolderSpace`
norm plus the gradient time-slice norm and the supremum norms of the `(0, 2)` and `(1, 0)`
derivative fields. -/
theorem norm_eq_norm_equivParabolicC2HolderSpace_add (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ = ‖equivParabolicC2HolderSpace f‖ + ‖timeSliceL 0 1 f‖ +
      ‖mixedDerivL 0 2 f‖ + ‖mixedDerivL 1 0 f‖ := by
  rw [equivParabolicC2HolderSpace_eq]; exact norm_eq_toParabolicC2HolderSpace f

/-- The full order-two parabolic norm is at most the `ParabolicCkHolderSpace 2` norm. -/
theorem fullNorm_equivParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.fullNorm (equivParabolicC2HolderSpace f) ≤ ‖f‖ := by
  rw [equivParabolicC2HolderSpace_eq]; exact fullNorm_toParabolicC2HolderSpace_le f

/-- The reduced `ParabolicC2HolderSpace` norm is at most the `ParabolicCkHolderSpace 2` norm. -/
theorem norm_equivParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖equivParabolicC2HolderSpace f‖ ≤ ‖f‖ := by
  rw [equivParabolicC2HolderSpace_eq]; exact norm_toParabolicC2HolderSpace_le f

/-- The `ParabolicCkHolderSpace 2` norm is at most twice the reduced `ParabolicC2HolderSpace`
norm. -/
theorem norm_le_two_mul_norm_equivParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ ≤ 2 * ‖equivParabolicC2HolderSpace f‖ := by
  rw [equivParabolicC2HolderSpace_eq]; exact norm_le_two_mul_toParabolicC2HolderSpace f

/-- The `ParabolicCkHolderSpace 2` norm is at most twice `ParabolicC2HolderSpace.fullNorm`. -/
theorem norm_le_two_mul_fullNorm_equivParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ ≤ 2 * ParabolicC2HolderSpace.fullNorm (equivParabolicC2HolderSpace f) :=
  (norm_le_two_mul_norm_equivParabolicC2HolderSpace f).trans
    (mul_le_mul_of_nonneg_left
      (ParabolicC2HolderSpace.norm_le_fullNorm_le (equivParabolicC2HolderSpace f)).1 zero_le_two)

/-- The inverse order-two equivalence has norm bound `2` against the reduced norm. -/
theorem norm_equivParabolicC2HolderSpace_symm_le (g : ParabolicC2HolderSpace α E F hab) :
    ‖equivParabolicC2HolderSpace.symm g‖ ≤ 2 * ‖g‖ :=
  norm_ofParabolicC2HolderSpace_le g

/-- The full order-two norm of `g` is at most the norm of `equivParabolicC2HolderSpace.symm g`. -/
theorem fullNorm_le_norm_equivParabolicC2HolderSpace_symm (g : ParabolicC2HolderSpace α E F hab) :
    ParabolicC2HolderSpace.fullNorm g ≤ ‖equivParabolicC2HolderSpace.symm g‖ := by
  simpa using fullNorm_equivParabolicC2HolderSpace_le (equivParabolicC2HolderSpace.symm g)

end ParabolicCkHolderSpace

end TauCeti

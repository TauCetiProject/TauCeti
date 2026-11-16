/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded parabolic Hölder maps of orders zero and two

The bounded parabolic Hölder space `ParabolicCkHolderSpace k α E F hab`, the space
`C_{par,b}^{k+α}` on the slab `E × [a, b]`, exists for every order `k`. Its fields
`D_t^r D_x^m u` take values in continuous multilinear maps, and its norm is the sum of the supremum
norms of all fields of parabolic order `2 r + m ≤ k`, of the Hölder norms of the top-order fields
and of the uniform temporal `(1 + α) / 2`-Hölder norms of the fields one order below. At orders
zero and two the same functions are described by two carriers built separately, with curried
derivatives and fewer terms in the norm:

* the parabolic Hölder space `HolderSpace α (slab a b) F`, that is `C_b^{α,α/2}`, with the norm
  `‖u‖_∞ + [u]_{α,par}`;
* the space `ParabolicC2HolderSpace α E F hab`, that is `C_b^{2+α,1+α/2}`, with the reduced norm
  `‖u‖_∞ + ‖D_x u‖_∞ + ‖D_x² u‖_{α,par} + ‖∂ₜu‖_{α,par}`, in which the Hölder norms are
  supremum-plus-seminorm.

These two are the data space and the solution space of the parabolic Schauder theory of order
two (`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`), so the identifications below are
what lets the theory of every order start from the order-two theory.

This file identifies the two families, preserving the underlying function. At order zero the
norm of `ParabolicCkHolderSpace` counts the supremum norm twice, once for the field and once in
its Hölder norm. At order two it adds to the reduced norm the supremum norms of `D_x² u` and
`∂ₜu`, already counted in their Hölder norms, and the uniform temporal `(1 + α) / 2`-Hölder norm
of the gradient, whose temporal seminorm the Hölder norms of `D_x² u` and `∂ₜu` control
(`TauCeti.ParabolicC2HolderSpace.toReal_timeEHolderNorm_spatialFDeriv_le`), its supremum part
being `‖D_x u‖_∞`. So in both cases the norms are equivalent, with constants `1` and `2`,
respectively `1` and `3`.

The construction follows the whole-space comparison `TauCeti.CkHolderSpace.equivHolderSpace` and
`TauCeti.CkHolderSpace.equivC2HolderSpace` in `TauCeti.Analysis.Holder.LowOrder`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.equivHolderSpace`: the identification of
  `ParabolicCkHolderSpace 0 α E F hab` with `HolderSpace α (slab a b) F`, with the norm identity
  `TauCeti.ParabolicCkHolderSpace.norm_eq_norm_add_norm_equivHolderSpace` and the bounds
  `‖e f‖ ≤ ‖f‖ ≤ 2 ‖e f‖`.
* `TauCeti.ParabolicCkHolderSpace.equivParabolicC2HolderSpace`: the identification of
  `ParabolicCkHolderSpace 2 α E F hab` with `ParabolicC2HolderSpace α E F hab`, with the bounds
  `‖e f‖ ≤ ‖f‖ ≤ 3 ‖e f‖` and the gradient, Hessian and time derivative of `e f` read off from
  the fields of `f`
  (`TauCeti.ParabolicCkHolderSpace.spatialFDerivL_equivParabolicC2HolderSpace_apply` and its
  companions), and conversely the fields of `e.symm g` read off from `g`
  (`TauCeti.ParabolicCkHolderSpace.mixedDerivL_zero_one_equivParabolicC2HolderSpace_symm_apply`
  and its companions).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

namespace ParabolicCkHolderSpace

/-! ### Order zero -/

/-- An order-zero map as an element of the parabolic Hölder space. -/
private def toHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    HolderSpace α (slab (E := E) a b) F :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 0 0 f)

private theorem toHolderSpace_apply (f : ParabolicCkHolderSpace 0 α E F hab)
    (p : slab (E := E) a b) : toHolderSpace f p = f p := by
  rw [toHolderSpace, HolderSpace.compLeftL_apply, mixedDerivHolderL_apply f (r := 0) (m := 0) rfl]
  simp

/-- The fields of the order-zero map with value `u`: the value, read as a `0`-multilinear map,
and zero at every other pair. -/
private def zeroFields (u : slab (E := E) a b →ᵇ F) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.compLeftContinuousBounded _ u
  | _, _ => 0

/-- An element of the parabolic Hölder space as an order-zero map. -/
private def ofHolderSpace (g : HolderSpace α (slab (E := E) a b) F) :
    ParabolicCkHolderSpace 0 α E F hab :=
  mk (zeroFields g.toBoundedContinuousFunction) (fun _ _ h ↦ absurd h (by omega))
    (fun _ _ h ↦ absurd h (by omega)) (fun _ _ h ↦ absurd h (by omega)) fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
      obtain ⟨C, hC⟩ := g.memHolder
      exact ⟨C, (LinearIsometryEquiv.isometry _).comp_holderWith hC⟩

private theorem coe_ofHolderSpace (g : HolderSpace α (slab (E := E) a b) F) :
    ⇑(ofHolderSpace (hab := hab) g) = g := by
  ext p
  rw [ofHolderSpace, mk_apply]
  simp [zeroFields, HolderSpace.toBoundedContinuousFunction_apply]

/-- The norm of an order-zero map is the sum of the norm of its field and of its Hölder field. -/
private theorem norm_eq_zero (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ = ‖mixedDerivL 0 0 f‖ + ‖mixedDerivHolderL 0 0 f‖ := by
  have hp : parabolicDerivPairs 0 = {(0, 0)} := by
    ext ⟨r, m⟩
    simp only [mem_parabolicDerivPairs, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [norm_eq, hp, Finset.sum_singleton, timeSliceL_of_ne (by omega), zero_apply, norm_zero,
    zero_add]

private theorem norm_eq_toHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ = ‖(toHolderSpace f).toBoundedContinuousFunction‖ + ‖toHolderSpace f‖ := by
  rw [norm_eq_zero, toHolderSpace, HolderSpace.norm_compLeftL_linearIsometry,
    ← toBoundedContinuousFunction_mixedDerivHolderL f (r := 0) (m := 0) rfl]
  congr 1
  rw [← (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.norm_compLeftContinuousBounded]
  congr 1
  ext p
  simp [HolderSpace.toBoundedContinuousFunction_apply]

private theorem toHolderSpace_ofHolderSpace (g : HolderSpace α (slab (E := E) a b) F) :
    toHolderSpace (ofHolderSpace (hab := hab) g) = g :=
  HolderSpace.ext fun p ↦ by rw [toHolderSpace_apply, coe_ofHolderSpace]

private theorem norm_toHolderSpace_le (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖toHolderSpace f‖ ≤ ‖f‖ := by
  rw [norm_eq_toHolderSpace f]
  exact le_add_of_nonneg_left (norm_nonneg _)

private theorem norm_ofHolderSpace_le (g : HolderSpace α (slab (E := E) a b) F) :
    ‖ofHolderSpace (hab := hab) g‖ ≤ 2 * ‖g‖ := by
  rw [norm_eq_toHolderSpace, toHolderSpace_ofHolderSpace, two_mul]
  gcongr
  exact g.norm_toBoundedContinuousFunction_le

/-- The order-zero maps are the bounded parabolically `α`-Hölder maps. The identification
preserves the underlying function; the norm of `ParabolicCkHolderSpace` is `‖u‖_∞ + ‖u‖`, where
`‖u‖ = ‖u‖_∞ + [u]_{α,par}` is the norm of `HolderSpace`
(`ParabolicCkHolderSpace.norm_eq_norm_add_norm_equivHolderSpace`). -/
def equivHolderSpace : ParabolicCkHolderSpace 0 α E F hab ≃L[ℝ]
    HolderSpace α (slab (E := E) a b) F :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toHolderSpace
      invFun := ofHolderSpace
      map_add' f g := HolderSpace.ext fun p ↦ by
        simp [toHolderSpace_apply, HolderSpace.add_apply]
      map_smul' c f := HolderSpace.ext fun p ↦ by
        simp [toHolderSpace_apply, HolderSpace.smul_apply]
      left_inv f := ext fun p ↦ by rw [coe_ofHolderSpace, toHolderSpace_apply]
      right_inv := toHolderSpace_ofHolderSpace }
    1 2 (fun f ↦ by simpa using norm_toHolderSpace_le f) norm_ofHolderSpace_le

/-- The identification with the parabolic Hölder space preserves the underlying function. -/
@[simp]
theorem equivHolderSpace_apply (f : ParabolicCkHolderSpace 0 α E F hab) (p : slab (E := E) a b) :
    equivHolderSpace f p = f p :=
  toHolderSpace_apply f p

/-- The inverse identification with the parabolic Hölder space preserves the underlying
function. -/
@[simp]
theorem coe_equivHolderSpace_symm (g : HolderSpace α (slab (E := E) a b) F) :
    ⇑(equivHolderSpace (hab := hab) |>.symm g) = g :=
  coe_ofHolderSpace g

/-- The field of the inverse identification with the parabolic Hölder space is the value, read as
a `0`-multilinear map. -/
@[simp]
theorem mixedDerivL_equivHolderSpace_symm_apply (g : HolderSpace α (slab (E := E) a b) F)
    (p : slab (E := E) a b) :
    mixedDerivL 0 0 (equivHolderSpace (hab := hab) |>.symm g) p =
      (continuousMultilinearCurryFin0 ℝ E F).symm (g p) := by
  ext v
  simp

/-- The norm `‖D⁰u‖_∞ + ‖D⁰u‖_∞ + [D⁰u]_{α,par}` of an order-zero map is the supremum norm plus
its norm in `HolderSpace`. -/
theorem norm_eq_norm_add_norm_equivHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ = ‖(equivHolderSpace f).toBoundedContinuousFunction‖ + ‖equivHolderSpace f‖ :=
  norm_eq_toHolderSpace f

/-- The norm of `HolderSpace` is at most the norm of `ParabolicCkHolderSpace`. -/
theorem norm_equivHolderSpace_le (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖equivHolderSpace f‖ ≤ ‖f‖ := by
  rw [norm_eq_norm_add_norm_equivHolderSpace f]
  exact le_add_of_nonneg_left (norm_nonneg _)

/-- The norm of `ParabolicCkHolderSpace` is at most twice the norm of `HolderSpace`. -/
theorem norm_le_two_mul_norm_equivHolderSpace (f : ParabolicCkHolderSpace 0 α E F hab) :
    ‖f‖ ≤ 2 * ‖equivHolderSpace f‖ := by
  rw [norm_eq_norm_add_norm_equivHolderSpace f, two_mul]
  gcongr
  exact (equivHolderSpace f).norm_toBoundedContinuousFunction_le

/-! ### Order two -/

/-- The fields of the order-two map with value `u`, gradient `ux`, Hessian `uxx` and time
derivative `ut`, read as multilinear maps, and zero at every other pair. -/
private def twoFields (u : slab (E := E) a b →ᵇ F) (ux : slab (E := E) a b →ᵇ (E →L[ℝ] F))
    (uxx : HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F))
    (ut : HolderSpace α (slab (E := E) a b) F) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.compLeftContinuousBounded _ u
  | 0, 1 => (continuousMultilinearCurryFin1 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.compLeftContinuousBounded _ ux
  | 0, 2 => (HolderSpace.compLeftL
      (continuousMultilinearCurryFin2 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      uxx).toBoundedContinuousFunction
  | 1, 0 => (HolderSpace.compLeftL
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      ut).toBoundedContinuousFunction
  | _, _ => 0

/-- The fields of an element of `ParabolicC2HolderSpace`. -/
private abbrev fieldsOf (g : ParabolicC2HolderSpace α E F hab) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F) :=
  twoFields (ParabolicC2HolderSpace.valueL g) (ParabolicC2HolderSpace.spatialFDerivL g)
    (ParabolicC2HolderSpace.spatialSecondFDerivL g) (ParabolicC2HolderSpace.timeDerivL g)

/-- The time slices of the gradient of an element of `ParabolicC2HolderSpace` are uniformly
`(1 + α) / 2`-Hölder, with the temporal seminorm of the gradient as constant. -/
private theorem holderWith_fieldsOf_zero_one (g : ParabolicC2HolderSpace α E F hab) (x : E) :
    HolderWith (timeEHolderNorm ((1 + α) / 2)
        (ParabolicC2HolderSpace.spatialFDerivL g : slab (E := E) a b → E →L[ℝ] F)).toNNReal
      ((1 + α) / 2) fun t : Icc a b ↦ fieldsOf g 0 1 (slabMk x t) := by
  have h : HolderWith (timeEHolderNorm ((1 + α) / 2)
      (ParabolicC2HolderSpace.spatialFDerivL g : slab (E := E) a b → E →L[ℝ] F)).toNNReal
      ((1 + α) / 2) fun t : Icc a b ↦ ParabolicC2HolderSpace.spatialFDerivL g (slabMk x t) :=
    fun t s ↦ timeEHolderNorm_le_iff.1
      (ENNReal.coe_toNNReal g.timeEHolderNorm_spatialFDeriv_lt_top.ne).ge x t s
  exact (continuousMultilinearCurryFin1 ℝ E F).symm.isometry.comp_holderWith h

private theorem fieldsOf_zero_zero_apply (g : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) :
    fieldsOf g 0 0 p = (continuousMultilinearCurryFin0 ℝ E F).symm (g p) :=
  (rfl)

private theorem fieldsOf_zero_one_apply (g : ParabolicC2HolderSpace α E F hab)
    (p : slab (E := E) a b) : fieldsOf g 0 1 p =
      (continuousMultilinearCurryFin1 ℝ E F).symm (ParabolicC2HolderSpace.spatialFDerivL g p) :=
  (rfl)

private theorem coe_fieldsOf_zero_two (g : ParabolicC2HolderSpace α E F hab) :
    ⇑(fieldsOf g 0 2) = (continuousMultilinearCurryFin2 ℝ E F).symm ∘
      ⇑(ParabolicC2HolderSpace.spatialSecondFDerivL g).toBoundedContinuousFunction := by
  ext1 p
  simp [twoFields, HolderSpace.toBoundedContinuousFunction_apply]

private theorem coe_fieldsOf_one_zero (g : ParabolicC2HolderSpace α E F hab) :
    ⇑(fieldsOf g 1 0) = (continuousMultilinearCurryFin0 ℝ E F).symm ∘
      ⇑(ParabolicC2HolderSpace.timeDerivL g).toBoundedContinuousFunction := by
  ext1 p
  simp [twoFields, HolderSpace.toBoundedContinuousFunction_apply]

/-- The spatial derivative identities between the fields of an element of
`ParabolicC2HolderSpace`. -/
private theorem hasFDerivAt_fieldsOf (g : ParabolicC2HolderSpace α E F hab) (r m : ℕ)
    (h : 2 * r + m + 1 ≤ 2) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ fieldsOf g r m (slabMk y t)) (fieldsOf g r (m + 1) (slabMk x t)).curryLeft
      x := by
  obtain ⟨rfl, rfl | rfl⟩ : r = 0 ∧ (m = 0 ∨ m = 1) := by omega
  · rw [fieldsOf_zero_one_apply, curryLeft_continuousMultilinearCurryFin1_symm]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.hasFDerivAt).comp x (g.hasSpatialFDerivAt t x)
  · rw [coe_fieldsOf_zero_two, Function.comp_apply, HolderSpace.coe_toBoundedContinuousFunction,
      curryLeft_continuousMultilinearCurryFin2_symm]
    exact ((continuousMultilinearCurryFin1 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.hasFDerivAt).comp x (g.hasSpatialSecondFDerivAt t x)

/-- The time derivative identity between the fields of an element of `ParabolicC2HolderSpace`. -/
private theorem hasDerivWithinAt_fieldsOf (g : ParabolicC2HolderSpace α E F hab) (r m : ℕ)
    (h : 2 * r + m + 2 ≤ 2) (x : E) (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (fieldsOf g r m) x)
      (fieldsOf g (r + 1) m (slabMk x t)) (Icc a b) t := by
  obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 0 := by omega
  have he : ParabolicC2HolderSpace.timeExtension hab.le (fieldsOf g 0 0) x =
      (continuousMultilinearCurryFin0 ℝ E F).symm ∘
        ParabolicC2HolderSpace.timeExtension hab.le g x := by
    ext1 s
    simp only [ParabolicC2HolderSpace.timeExtension_def, fieldsOf_zero_zero_apply,
      Function.comp_apply]
  rw [he, coe_fieldsOf_one_zero, Function.comp_apply, HolderSpace.coe_toBoundedContinuousFunction]
  exact HasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt
    (g.hasTimeDerivWithinAt x t)

/-- The top-order fields of an element of `ParabolicC2HolderSpace` are parabolically
`α`-Hölder. -/
private theorem memHolder_fieldsOf (g : ParabolicC2HolderSpace α E F hab) (r m : ℕ)
    (h : 2 * r + m = 2) : MemHolder α (fieldsOf g r m : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (r = 0 ∧ m = 2) ∨ (r = 1 ∧ m = 0) := by omega
  · obtain ⟨C, hC⟩ := (ParabolicC2HolderSpace.spatialSecondFDerivL g).memHolder
    rw [coe_fieldsOf_zero_two]
    exact ⟨C, (continuousMultilinearCurryFin2 ℝ E F).symm.isometry.comp_holderWith hC⟩
  · obtain ⟨C, hC⟩ := (ParabolicC2HolderSpace.timeDerivL g).memHolder
    rw [coe_fieldsOf_one_zero]
    exact ⟨C, (continuousMultilinearCurryFin0 ℝ E F).symm.isometry.comp_holderWith hC⟩

/-- An element of `ParabolicC2HolderSpace` as an order-two map. -/
private def ofParabolicC2HolderSpace (g : ParabolicC2HolderSpace α E F hab) :
    ParabolicCkHolderSpace 2 α E F hab :=
  mk (fieldsOf g) (hasFDerivAt_fieldsOf g) (hasDerivWithinAt_fieldsOf g)
    (fun r m h ↦ by
      obtain ⟨rfl, rfl⟩ : r = 0 ∧ m = 1 := by omega
      exact ⟨_, holderWith_fieldsOf_zero_one g⟩)
    (memHolder_fieldsOf g)

private theorem mixedDerivL_ofParabolicC2HolderSpace (g : ParabolicC2HolderSpace α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ 2) :
    mixedDerivL r m (ofParabolicC2HolderSpace g) = fieldsOf g r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem coe_ofParabolicC2HolderSpace (g : ParabolicC2HolderSpace α E F hab) :
    ⇑(ofParabolicC2HolderSpace g) = g := by
  ext p
  rw [ofParabolicC2HolderSpace, mk_apply, fieldsOf_zero_zero_apply]
  simp

/-- The value of an order-two map, as a bounded continuous map. -/
private abbrev valueOf (f : ParabolicCkHolderSpace 2 α E F hab) : slab (E := E) a b →ᵇ F :=
  (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    |>.compLeftContinuousBounded _ (mixedDerivL 0 0 f)

/-- The spatial gradient of an order-two map, as a bounded continuous map. -/
private abbrev gradientOf (f : ParabolicCkHolderSpace 2 α E F hab) :
    slab (E := E) a b →ᵇ (E →L[ℝ] F) :=
  (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
    |>.compLeftContinuousBounded _ (mixedDerivL 0 1 f)

/-- The spatial Hessian of an order-two map, as a bounded Hölder map. -/
private abbrev hessianOf (f : ParabolicCkHolderSpace 2 α E F hab) :
    HolderSpace α (slab (E := E) a b) (E →L[ℝ] E →L[ℝ] F) :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin2 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 0 2 f)

/-- The time derivative of an order-two map, as a bounded Hölder map. -/
private abbrev timeDerivOf (f : ParabolicCkHolderSpace 2 α E F hab) :
    HolderSpace α (slab (E := E) a b) F :=
  HolderSpace.compLeftL
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    (mixedDerivHolderL 1 0 f)

private theorem hasFDerivAt_valueOf (f : ParabolicCkHolderSpace 2 α E F hab) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ valueOf f (slabMk y t)) (gradientOf f (slabMk x t)) x := by
  have hd := ((continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
    |>.hasFDerivAt).comp x (hasFDerivAt_mixedDerivL f (r := 0) (m := 0) (by norm_num) t x)
  rw [← (continuousMultilinearCurryFin1 ℝ E F).symm_apply_apply
    (mixedDerivL 0 1 f (slabMk x t)), curryLeft_continuousMultilinearCurryFin1_symm] at hd
  convert hd using 1
  · -- Postcomposing with the currying isometry, as a bounded map or pointwise, agrees.
    rfl
  · exact ContinuousLinearMap.ext fun v ↦ by simp

private theorem hasFDerivAt_gradientOf (f : ParabolicCkHolderSpace 2 α E F hab) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ gradientOf f (slabMk y t)) (hessianOf f (slabMk x t)) x := by
  have hd := ((continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
    |>.hasFDerivAt).comp x (hasFDerivAt_mixedDerivL f (r := 0) (m := 1) (by norm_num) t x)
  rw [← (continuousMultilinearCurryFin2 ℝ E F).symm_apply_apply
    (mixedDerivL 0 2 f (slabMk x t)), curryLeft_continuousMultilinearCurryFin2_symm] at hd
  rw [HolderSpace.compLeftL_apply, mixedDerivHolderL_apply f (r := 0) (m := 2) rfl]
  convert hd using 1
  · -- Postcomposing with the currying isometry, as a bounded map or pointwise, agrees.
    rfl
  · exact ContinuousLinearMap.ext fun v ↦ by simp

private theorem hasDerivWithinAt_valueOf (f : ParabolicCkHolderSpace 2 α E F hab) (x : E)
    (t : Icc a b) : HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (valueOf f) x)
      (timeDerivOf f (slabMk x t)) (Icc a b) t := by
  have he : ParabolicC2HolderSpace.timeExtension hab.le (valueOf f) x =
      (continuousMultilinearCurryFin0 ℝ E F) ∘
        ParabolicC2HolderSpace.timeExtension hab.le (mixedDerivL 0 0 f) x := by
    ext1 s
    simp only [ParabolicC2HolderSpace.timeExtension_def,
      ContinuousLinearMap.compLeftContinuousBounded_apply, Function.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
  rw [he, HolderSpace.compLeftL_apply, mixedDerivHolderL_apply f (r := 1) (m := 0) rfl]
  exact HasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap.hasFDerivAt
    (hasDerivWithinAt_mixedDerivL f (r := 0) (m := 0) (by norm_num) x t)

/-- An order-two map as an element of `ParabolicC2HolderSpace`. -/
private def toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace α E F hab :=
  ParabolicC2HolderSpace.mk (valueOf f) (gradientOf f) (hessianOf f) (timeDerivOf f)
    (hasFDerivAt_valueOf f) (hasFDerivAt_gradientOf f) (hasDerivWithinAt_valueOf f)

-- The four field lemmas are stated through `ParabolicC2HolderSpace.mk`'s own field lemmas,
-- applied by unification: the bounded continuous fields above are built on the topology of the
-- slab as seen from `ParabolicCkHolderSpace`, which `rw` does not match syntactically against the
-- statements of `ParabolicC2HolderSpace`.
private theorem valueL_toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.valueL (toParabolicC2HolderSpace f) =
      ContinuousLinearMap.compLeftContinuousBounded _
        (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
        (mixedDerivL 0 0 f) :=
  ParabolicC2HolderSpace.valueL_mk _ _ _ _ _ _ _

private theorem spatialFDerivL_toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.spatialFDerivL (toParabolicC2HolderSpace f) =
      ContinuousLinearMap.compLeftContinuousBounded _
        (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.toContinuousLinearMap
        (mixedDerivL 0 1 f) :=
  ParabolicC2HolderSpace.spatialFDerivL_mk _ _ _ _ _ _ _

private theorem spatialSecondFDerivL_toParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.spatialSecondFDerivL (toParabolicC2HolderSpace f) =
      HolderSpace.compLeftL
        (continuousMultilinearCurryFin2 ℝ E F).toLinearIsometry.toContinuousLinearMap
        (mixedDerivHolderL 0 2 f) :=
  ParabolicC2HolderSpace.spatialSecondFDerivL_mk _ _ _ _ _ _ _

private theorem timeDerivL_toParabolicC2HolderSpace (f : ParabolicCkHolderSpace 2 α E F hab) :
    ParabolicC2HolderSpace.timeDerivL (toParabolicC2HolderSpace f) =
      HolderSpace.compLeftL
        (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap
        (mixedDerivHolderL 1 0 f) :=
  ParabolicC2HolderSpace.timeDerivL_mk _ _ _ _ _ _ _

private theorem toParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) : toParabolicC2HolderSpace f p = f p := by
  rw [← ParabolicC2HolderSpace.valueL_apply, valueL_toParabolicC2HolderSpace]
  simp

/-- The norm of an order-two map: the supremum norms of the four fields `u`, `D_x u`, `D_x² u`
and `∂ₜu`, the norm of the family of time slices of `D_x u` and the Hölder norms of `D_x² u` and
`∂ₜu`. -/
private theorem norm_eq_two (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ = ‖mixedDerivL 0 0 f‖ + (‖mixedDerivL 0 1 f‖ + ‖timeSliceL 0 1 f‖) +
      (‖mixedDerivL 0 2 f‖ + ‖mixedDerivHolderL 0 2 f‖) +
      (‖mixedDerivL 1 0 f‖ + ‖mixedDerivHolderL 1 0 f‖) := by
  have hp : parabolicDerivPairs 2 = {(0, 0), (0, 1), (0, 2), (1, 0)} := by
    ext ⟨r, m⟩
    simp only [mem_parabolicDerivPairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [norm_eq, hp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [timeSliceL_of_ne (k := 2) (r := 0) (m := 0) (by omega),
    timeSliceL_of_ne (k := 2) (r := 0) (m := 2) (by omega),
    timeSliceL_of_ne (k := 2) (r := 1) (m := 0) (by omega),
    mixedDerivHolderL_of_ne (k := 2) (r := 0) (m := 0) (by omega),
    mixedDerivHolderL_of_ne (k := 2) (r := 0) (m := 1) (by omega), zero_apply, norm_zero]
  ring

private theorem norm_toParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖toParabolicC2HolderSpace f‖ ≤ ‖f‖ := by
  rw [ParabolicC2HolderSpace.norm_eq, norm_eq_two f, valueL_toParabolicC2HolderSpace,
    spatialFDerivL_toParabolicC2HolderSpace, spatialSecondFDerivL_toParabolicC2HolderSpace,
    timeDerivL_toParabolicC2HolderSpace, HolderSpace.norm_compLeftL_linearIsometry,
    HolderSpace.norm_compLeftL_linearIsometry,
    (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.norm_compLeftContinuousBounded,
    (continuousMultilinearCurryFin1 ℝ E F).toLinearIsometry.norm_compLeftContinuousBounded]
  linarith [norm_nonneg (timeSliceL 0 1 f), norm_nonneg (mixedDerivL 0 2 f),
    norm_nonneg (mixedDerivL 1 0 f)]

private theorem toParabolicC2HolderSpace_ofParabolicC2HolderSpace
    (g : ParabolicC2HolderSpace α E F hab) :
    toParabolicC2HolderSpace (ofParabolicC2HolderSpace g) = g :=
  ParabolicC2HolderSpace.ext fun p ↦ by
    rw [toParabolicC2HolderSpace_apply, coe_ofParabolicC2HolderSpace]

private theorem norm_ofParabolicC2HolderSpace_le (g : ParabolicC2HolderSpace α E F hab) :
    ‖ofParabolicC2HolderSpace g‖ ≤ 3 * ‖g‖ := by
  set f := ofParabolicC2HolderSpace g
  have hg := toParabolicC2HolderSpace_ofParabolicC2HolderSpace g
  -- The Hölder fields of `f` have the norms of the Hessian and the time derivative of `g`.
  have h₂ : ‖mixedDerivHolderL 0 2 f‖ = ‖ParabolicC2HolderSpace.spatialSecondFDerivL g‖ := by
    rw [← hg, spatialSecondFDerivL_toParabolicC2HolderSpace,
      HolderSpace.norm_compLeftL_linearIsometry]
  have hₜ : ‖mixedDerivHolderL 1 0 f‖ = ‖ParabolicC2HolderSpace.timeDerivL g‖ := by
    rw [← hg, timeDerivL_toParabolicC2HolderSpace, HolderSpace.norm_compLeftL_linearIsometry]
  have h₀ : ‖mixedDerivL 0 0 f‖ ≤ ‖ParabolicC2HolderSpace.valueL g‖ := by
    rw [mixedDerivL_ofParabolicC2HolderSpace g (by norm_num)]
    exact (LinearIsometry.norm_compLeftContinuousBounded _ _).le
  have h₁ : ‖mixedDerivL 0 1 f‖ ≤ ‖ParabolicC2HolderSpace.spatialFDerivL g‖ := by
    rw [mixedDerivL_ofParabolicC2HolderSpace g (by norm_num)]
    exact (LinearIsometry.norm_compLeftContinuousBounded _ _).le
  -- The time slices of the gradient are controlled by the top-order Hölder norms.
  have hs : ‖timeSliceL 0 1 f‖ ≤ ‖mixedDerivL 0 1 f‖ +
      (‖ParabolicC2HolderSpace.spatialSecondFDerivL g‖ +
        ‖ParabolicC2HolderSpace.timeDerivL g‖) := by
    refine (norm_timeSliceL_le_of_holderWith f (r := 0) (m := 1) rfl
      (C := (timeEHolderNorm ((1 + α) / 2)
        (ParabolicC2HolderSpace.spatialFDerivL g : slab (E := E) a b → E →L[ℝ] F)).toNNReal)
      fun x ↦ ?_).trans ?_
    · rw [mixedDerivL_ofParabolicC2HolderSpace g (by norm_num)]
      exact holderWith_fieldsOf_zero_one g x
    · rw [ENNReal.coe_toNNReal_eq_toReal]
      gcongr
      exact g.toReal_timeEHolderNorm_spatialFDeriv_le
  have h₂' := norm_mixedDerivL_le_norm_mixedDerivHolderL f (r := 0) (m := 2) rfl
  have hₜ' := norm_mixedDerivL_le_norm_mixedDerivHolderL f (r := 1) (m := 0) rfl
  rw [norm_eq_two f, ParabolicC2HolderSpace.norm_eq g]
  linarith [norm_nonneg (ParabolicC2HolderSpace.valueL g),
    norm_nonneg (ParabolicC2HolderSpace.spatialFDerivL g)]

/-- The order-two maps are the elements of `ParabolicC2HolderSpace`, the space
`C_b^{2+α,1+α/2}`. The identification preserves the underlying function; the norms are equivalent
by `ParabolicCkHolderSpace.norm_equivParabolicC2HolderSpace_le` and
`ParabolicCkHolderSpace.norm_le_three_mul_norm_equivParabolicC2HolderSpace`. -/
def equivParabolicC2HolderSpace :
    ParabolicCkHolderSpace 2 α E F hab ≃L[ℝ] ParabolicC2HolderSpace α E F hab :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toParabolicC2HolderSpace
      invFun := ofParabolicC2HolderSpace
      map_add' f g := ParabolicC2HolderSpace.ext fun p ↦ by
        simp [toParabolicC2HolderSpace_apply]
      map_smul' c f := ParabolicC2HolderSpace.ext fun p ↦ by
        simp [toParabolicC2HolderSpace_apply]
      left_inv f := ext fun p ↦ by
        rw [coe_ofParabolicC2HolderSpace, toParabolicC2HolderSpace_apply]
      right_inv := toParabolicC2HolderSpace_ofParabolicC2HolderSpace }
    1 3 (fun f ↦ by simpa using norm_toParabolicC2HolderSpace_le f)
    norm_ofParabolicC2HolderSpace_le

private theorem equivParabolicC2HolderSpace_eq (f : ParabolicCkHolderSpace 2 α E F hab) :
    equivParabolicC2HolderSpace f = toParabolicC2HolderSpace f :=
  (rfl)

/-- The identification with `ParabolicC2HolderSpace` preserves the underlying function. -/
@[simp]
theorem equivParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) : equivParabolicC2HolderSpace f p = f p :=
  toParabolicC2HolderSpace_apply f p

/-- The inverse identification with `ParabolicC2HolderSpace` preserves the underlying
function. -/
@[simp]
theorem coe_equivParabolicC2HolderSpace_symm (g : ParabolicC2HolderSpace α E F hab) :
    ⇑(equivParabolicC2HolderSpace.symm g) = g :=
  coe_ofParabolicC2HolderSpace g

private theorem equivParabolicC2HolderSpace_symm_eq (g : ParabolicC2HolderSpace α E F hab) :
    equivParabolicC2HolderSpace.symm g = ofParabolicC2HolderSpace g :=
  (rfl)

/-- The field `D_x u` of the inverse identification is the gradient, in uncurried form. -/
@[simp]
theorem mixedDerivL_zero_one_equivParabolicC2HolderSpace_symm_apply
    (g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    mixedDerivL 0 1 (equivParabolicC2HolderSpace.symm g) p =
      (continuousMultilinearCurryFin1 ℝ E F).symm (ParabolicC2HolderSpace.spatialFDerivL g p) := by
  rw [equivParabolicC2HolderSpace_symm_eq, mixedDerivL_ofParabolicC2HolderSpace g (by norm_num),
    fieldsOf_zero_one_apply]

/-- The field `D_x² u` of the inverse identification is the Hessian, in uncurried form. -/
@[simp]
theorem mixedDerivL_zero_two_equivParabolicC2HolderSpace_symm_apply
    (g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    mixedDerivL 0 2 (equivParabolicC2HolderSpace.symm g) p =
      (continuousMultilinearCurryFin2 ℝ E F).symm
        (ParabolicC2HolderSpace.spatialSecondFDerivL g p) := by
  rw [equivParabolicC2HolderSpace_symm_eq, mixedDerivL_ofParabolicC2HolderSpace g (by norm_num),
    coe_fieldsOf_zero_two, Function.comp_apply, HolderSpace.coe_toBoundedContinuousFunction]

/-- The field `D_t u` of the inverse identification is the time derivative, read as a
`0`-multilinear map. -/
@[simp]
theorem mixedDerivL_one_zero_equivParabolicC2HolderSpace_symm_apply
    (g : ParabolicC2HolderSpace α E F hab) (p : slab (E := E) a b) :
    mixedDerivL 1 0 (equivParabolicC2HolderSpace.symm g) p =
      (continuousMultilinearCurryFin0 ℝ E F).symm (ParabolicC2HolderSpace.timeDerivL g p) := by
  rw [equivParabolicC2HolderSpace_symm_eq, mixedDerivL_ofParabolicC2HolderSpace g (by norm_num),
    coe_fieldsOf_one_zero, Function.comp_apply, HolderSpace.coe_toBoundedContinuousFunction]

/-- The gradient of the identified map is the field `D_x u`, in curried form. -/
@[simp]
theorem spatialFDerivL_equivParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) :
    ParabolicC2HolderSpace.spatialFDerivL (equivParabolicC2HolderSpace f) p =
      continuousMultilinearCurryFin1 ℝ E F (mixedDerivL 0 1 f p) := by
  rw [equivParabolicC2HolderSpace_eq, spatialFDerivL_toParabolicC2HolderSpace,
    ContinuousLinearMap.compLeftContinuousBounded_apply]
  simp

/-- The Hessian of the identified map is the field `D_x² u`, in curried form. -/
@[simp]
theorem spatialSecondFDerivL_equivParabolicC2HolderSpace_apply
    (f : ParabolicCkHolderSpace 2 α E F hab) (p : slab (E := E) a b) :
    ParabolicC2HolderSpace.spatialSecondFDerivL (equivParabolicC2HolderSpace f) p =
      continuousMultilinearCurryFin2 ℝ E F (mixedDerivL 0 2 f p) := by
  rw [equivParabolicC2HolderSpace_eq, spatialSecondFDerivL_toParabolicC2HolderSpace,
    HolderSpace.compLeftL_apply, mixedDerivHolderL_apply f (r := 0) (m := 2) rfl]
  simp

/-- The time derivative of the identified map is the field `D_t u`, read as a value. -/
@[simp]
theorem timeDerivL_equivParabolicC2HolderSpace_apply (f : ParabolicCkHolderSpace 2 α E F hab)
    (p : slab (E := E) a b) :
    ParabolicC2HolderSpace.timeDerivL (equivParabolicC2HolderSpace f) p =
      continuousMultilinearCurryFin0 ℝ E F (mixedDerivL 1 0 f p) := by
  rw [equivParabolicC2HolderSpace_eq, timeDerivL_toParabolicC2HolderSpace,
    HolderSpace.compLeftL_apply, mixedDerivHolderL_apply f (r := 1) (m := 0) rfl]
  simp

/-- The norm of `ParabolicC2HolderSpace` is at most the norm of `ParabolicCkHolderSpace`. -/
theorem norm_equivParabolicC2HolderSpace_le (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖equivParabolicC2HolderSpace f‖ ≤ ‖f‖ := by
  rw [equivParabolicC2HolderSpace_eq]
  exact norm_toParabolicC2HolderSpace_le f

/-- The norm of `ParabolicCkHolderSpace` is at most three times the norm of
`ParabolicC2HolderSpace`. -/
theorem norm_le_three_mul_norm_equivParabolicC2HolderSpace
    (f : ParabolicCkHolderSpace 2 α E F hab) :
    ‖f‖ ≤ 3 * ‖equivParabolicC2HolderSpace f‖ := by
  have h := norm_ofParabolicC2HolderSpace_le (toParabolicC2HolderSpace f)
  have hf : ofParabolicC2HolderSpace (toParabolicC2HolderSpace f) = f :=
    ext fun p ↦ by rw [coe_ofParabolicC2HolderSpace, toParabolicC2HolderSpace_apply]
  rw [hf] at h
  rwa [equivParabolicC2HolderSpace_eq]

end ParabolicCkHolderSpace

end TauCeti

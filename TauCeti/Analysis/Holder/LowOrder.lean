/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import TauCeti.Analysis.Holder.Two
import TauCeti.Topology.MetricSpace.Holder

/-!
# The bounded `C^{k,α}` spaces of order at most two

The bounded `C^{k,α}` space `CkHolderSpace k α E F` exists for every order `k` and carries the sum
norm `∑_{i ≤ k} ‖D^i f‖_∞ + [D^k f]_α`, with derivatives taken as continuous multilinear maps. For
`k ≤ 2` the bounded Hölder spaces `HolderSpace`, `C1HolderSpace` and `C2HolderSpace` describe the
same functions, with derivatives taken in curried form and with the recursive maximum norms

* `‖f‖_∞ + [f]_α` for `HolderSpace`,
* `max ‖f‖_∞ (‖Df‖_∞ + [Df]_α)` for `C1HolderSpace`,
* `max ‖f‖_∞ (max ‖Df‖_∞ (‖D²f‖_∞ + [D²f]_α))` for `C2HolderSpace`.

This file identifies the two families, preserving the underlying function. At order zero the
two norms agree; at orders one and two the sum norm is the sum of the terms whose maximum is the
recursive norm, so the norms are equivalent with constants `1` and `k + 1`. They are not equal: at
order one the sum norm exceeds the maximum norm by the smaller of its two terms, which is
`‖sin‖_∞ = 1` for `f = sin` on `ℝ`.

## Main declarations

* `TauCeti.CkHolderSpace.equivHolderSpace`: the isometric identification of
  `CkHolderSpace 0 α E F` with `HolderSpace α E F`.
* `TauCeti.CkHolderSpace.equivC1HolderSpace`: the identification of `CkHolderSpace 1 α E F` with
  `C1HolderSpace α E F`, with the norm identity `CkHolderSpace.norm_eq_norm_add_norm_fderiv` and
  the bounds `‖e f‖ ≤ ‖f‖ ≤ 2 ‖e f‖`.
* `TauCeti.CkHolderSpace.equivC2HolderSpace`: the identification of `CkHolderSpace 2 α E F` with
  `C2HolderSpace α E F`, with the norm identity
  `CkHolderSpace.norm_eq_norm_add_norm_fderiv_add_norm_secondFDeriv` and the bounds
  `‖e f‖ ≤ ‖f‖ ≤ 3 ‖e f‖`.

## References

D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
Section 4.1.
-/

public section

noncomputable section

namespace TauCeti

namespace CkHolderSpace

open BoundedContinuousFunction
open scoped NNReal BoundedContinuousFunction

universe u v

variable {k : ℕ} {α : ℝ≥0} {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The underlying function of a bounded `C^{k,α}` map, as a bounded continuous function. -/
private def toBCF (f : CkHolderSpace k α E F) : E →ᵇ F :=
  ofNormedAddCommGroup f f.contDiff.continuous ‖f‖ f.norm_apply_le

private theorem coe_toBCF (f : CkHolderSpace k α E F) : ⇑(toBCF f) = f :=
  coe_ofNormedAddCommGroup ..

/-- The supremum norm of the underlying function is that of the order-zero derivative field. -/
private theorem norm_toBCF (f : CkHolderSpace k α E F) : ‖toBCF f‖ = ‖f.iteratedFDeriv 0‖ := by
  rw [norm_eq_iSup_norm, norm_eq_iSup_norm (f.iteratedFDeriv 0), coe_toBCF]
  congr 1 with x
  rw [← iteratedFDeriv_eq, Fin.val_zero, norm_iteratedFDeriv_zero]

/-- The derivative of a bounded `C^{k+1,α}` map, as a bounded continuous field. -/
private def fderivBCF (f : CkHolderSpace (k + 1) α E F) : E →ᵇ (E →L[ℝ] F) :=
  ofNormedAddCommGroup (fderiv ℝ f) (f.contDiff.continuous_fderiv (by simp)) ‖f‖ fun x ↦ by
    simpa using f.norm_iteratedFDeriv_apply_le (i := 1) (by omega) x

private theorem coe_fderivBCF (f : CkHolderSpace (k + 1) α E F) :
    ⇑(fderivBCF f) = fderiv ℝ f :=
  coe_ofNormedAddCommGroup ..

/-- The supremum norm of the derivative is that of the first derivative field. -/
private theorem norm_fderivBCF (f : CkHolderSpace (k + 1) α E F) :
    ‖fderivBCF f‖ = ‖f.iteratedFDeriv 1‖ := by
  rw [norm_eq_iSup_norm, norm_eq_iSup_norm (f.iteratedFDeriv 1), coe_fderivBCF]
  congr 1 with x
  rw [← iteratedFDeriv_eq, Fin.val_one, norm_iteratedFDeriv_one]

private theorem hasFDerivAt_fderiv (f : CkHolderSpace (k + 1) α E F) (x : E) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((f.contDiff.differentiable (by simp)) x).hasFDerivAt

/-! ### Order zero -/

/-- A bounded `C^{0,α}` map as an element of the bounded Hölder space. -/
private def toHolderSpace (f : CkHolderSpace 0 α E F) : HolderSpace α E F :=
  HolderSpace.ofBoundedContinuousFunction (toBCF f) <| by
    obtain ⟨C, hC⟩ := f.memHolder_iteratedFDeriv
    rw [iteratedFDeriv_zero_eq_comp] at hC
    exact ⟨C, (LinearIsometryEquiv.isometry _).holderWith_comp_iff.1 hC⟩

/-- An element of the bounded Hölder space as a bounded `C^{0,α}` map. -/
private def ofHolderSpace (g : HolderSpace α E F) : CkHolderSpace 0 α E F :=
  ofContDiff g (by simpa [contDiff_zero] using g.continuous)
    (fun i hi ↦ ⟨‖g‖, fun x ↦ by
      obtain rfl : i = 0 := by omega
      simpa using g.norm_apply_le x⟩) <| by
    obtain ⟨C, hC⟩ := g.memHolder
    rw [HolderSpace.coe_toBoundedContinuousFunction] at hC
    rw [iteratedFDeriv_zero_eq_comp]
    exact ⟨C, (LinearIsometryEquiv.isometry _).holderWith_comp_iff.2 hC⟩

private theorem toHolderSpace_apply (f : CkHolderSpace 0 α E F) (x : E) :
    toHolderSpace f x = f x := by
  rw [toHolderSpace, HolderSpace.ofBoundedContinuousFunction_apply, coe_toBCF]

private theorem coe_ofHolderSpace (g : HolderSpace α E F) : ⇑(ofHolderSpace g) = g := by
  rw [ofHolderSpace, coe_ofContDiff]

private theorem norm_toHolderSpace (f : CkHolderSpace 0 α E F) : ‖toHolderSpace f‖ = ‖f‖ := by
  rw [HolderSpace.norm_def, toHolderSpace,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction, norm_toBCF, coe_toBCF,
    norm_eq, Fin.sum_univ_one, iteratedFDeriv_zero_eq_comp,
    (LinearIsometryEquiv.isometry _).nnHolderNorm_comp]

/-- The bounded `C^{0,α}` maps are the bounded `α`-Hölder functions, and the sum norm
`‖D⁰f‖_∞ + [D⁰f]_α` is the supremum-plus-Hölder norm `‖f‖_∞ + [f]_α`. -/
def equivHolderSpace : CkHolderSpace 0 α E F ≃ₗᵢ[ℝ] HolderSpace α E F where
  toFun := toHolderSpace
  invFun := ofHolderSpace
  map_add' f g := HolderSpace.ext fun x ↦ by simp [toHolderSpace_apply]
  map_smul' c f := HolderSpace.ext fun x ↦ by simp [toHolderSpace_apply]
  left_inv f := ext fun x ↦ by simp [coe_ofHolderSpace, toHolderSpace_apply]
  right_inv g := HolderSpace.ext fun x ↦ by simp [coe_ofHolderSpace, toHolderSpace_apply]
  norm_map' := norm_toHolderSpace

/-- The identification with the bounded Hölder space preserves the underlying function. -/
@[simp]
theorem equivHolderSpace_apply (f : CkHolderSpace 0 α E F) (x : E) : equivHolderSpace f x = f x :=
  toHolderSpace_apply f x

/-- The inverse identification with the bounded Hölder space preserves the underlying
function. -/
@[simp]
theorem coe_equivHolderSpace_symm (g : HolderSpace α E F) :
    ⇑(equivHolderSpace.symm g) = g :=
  coe_ofHolderSpace g

/-! ### Order one -/

/-- The derivative of a bounded `C^{1,α}` map, as an element of the bounded Hölder space. -/
private def fderivHolder (f : CkHolderSpace 1 α E F) : HolderSpace α E (E →L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction (fderivBCF f) <| by
    obtain ⟨C, hC⟩ := f.memHolder_iteratedFDeriv
    rw [coe_fderivBCF, fderiv_eq_continuousMultilinearCurryFin1_comp]
    exact ⟨C, (LinearIsometryEquiv.isometry _).holderWith_comp_iff.2 hC⟩

private theorem fderivHolder_apply (f : CkHolderSpace 1 α E F) (x : E) :
    fderivHolder f x = fderiv ℝ f x := by
  rw [fderivHolder, HolderSpace.ofBoundedContinuousFunction_apply, coe_fderivBCF]

/-- The Hölder-space norm of the derivative is the sum of the supremum norm of the first
derivative field and the Hölder seminorm of the first iterated derivative. -/
private theorem norm_fderivHolder (f : CkHolderSpace 1 α E F) :
    ‖fderivHolder f‖ = ‖f.iteratedFDeriv 1‖ + nnHolderNorm α (_root_.iteratedFDeriv ℝ 1 f) := by
  rw [HolderSpace.norm_def, fderivHolder,
    HolderSpace.toBoundedContinuousFunction_ofBoundedContinuousFunction, norm_fderivBCF,
    coe_fderivBCF, fderiv_eq_continuousMultilinearCurryFin1_comp,
    (LinearIsometryEquiv.isometry _).nnHolderNorm_comp]

/-- A bounded `C^{1,α}` map, in the sum-norm space, as an element of `C1HolderSpace`. -/
private def toC1HolderSpace (f : CkHolderSpace 1 α E F) : C1HolderSpace α E F :=
  C1HolderSpace.mk (toBCF f) (fderivHolder f) fun x ↦ by
    rw [coe_toBCF, fderivHolder_apply]
    exact hasFDerivAt_fderiv f x

private theorem toC1HolderSpace_apply (f : CkHolderSpace 1 α E F) (x : E) :
    toC1HolderSpace f x = f x := by
  rw [← C1HolderSpace.toBoundedContinuousFunction_apply, toC1HolderSpace,
    C1HolderSpace.toBoundedContinuousFunction_mk, coe_toBCF]

/-- An element of `C1HolderSpace` as a bounded `C^{1,α}` map in the sum-norm space. -/
private def ofC1HolderSpace (g : C1HolderSpace α E F) : CkHolderSpace 1 α E F :=
  ofContDiff g (by exact_mod_cast g.contDiff_one)
    (fun i hi ↦ ⟨‖g‖, fun x ↦ by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      · rw [norm_iteratedFDeriv_zero, ← C1HolderSpace.toBoundedContinuousFunction_apply]
        exact (norm_coe_le_norm _ x).trans g.norm_toBoundedContinuousFunction_le
      · rw [norm_iteratedFDeriv_one, C1HolderSpace.fderiv_eq]
        exact ((C1HolderSpace.fderiv g).norm_apply_le x).trans g.norm_fderiv_le⟩) <| by
    obtain ⟨C, hC⟩ := g.memHolder_fderiv
    refine ⟨C, (continuousMultilinearCurryFin1 ℝ E F).isometry.holderWith_comp_iff.1 ?_⟩
    rw [← fderiv_eq_continuousMultilinearCurryFin1_comp]
    exact hC

private theorem coe_ofC1HolderSpace (g : C1HolderSpace α E F) : ⇑(ofC1HolderSpace g) = g := by
  rw [ofC1HolderSpace, coe_ofContDiff]

/-- The sum norm of a bounded `C^{1,α}` map is the sum of the two terms whose maximum is its
`C1HolderSpace` norm. -/
private theorem norm_eq_toC1HolderSpace (f : CkHolderSpace 1 α E F) :
    ‖f‖ = ‖C1HolderSpace.toBoundedContinuousFunction (toC1HolderSpace f)‖ +
      ‖C1HolderSpace.fderiv (toC1HolderSpace f)‖ := by
  rw [norm_eq, Fin.sum_univ_two, toC1HolderSpace, C1HolderSpace.toBoundedContinuousFunction_mk,
    C1HolderSpace.fderiv_mk, norm_toBCF, norm_fderivHolder, add_assoc]

private theorem ofC1HolderSpace_toC1HolderSpace (f : CkHolderSpace 1 α E F) :
    ofC1HolderSpace (toC1HolderSpace f) = f :=
  ext fun x ↦ by rw [coe_ofC1HolderSpace, toC1HolderSpace_apply]

private theorem toC1HolderSpace_ofC1HolderSpace (g : C1HolderSpace α E F) :
    toC1HolderSpace (ofC1HolderSpace g) = g :=
  C1HolderSpace.ext fun x ↦ by rw [toC1HolderSpace_apply, coe_ofC1HolderSpace]

private theorem norm_toC1HolderSpace_le (f : CkHolderSpace 1 α E F) :
    ‖toC1HolderSpace f‖ ≤ ‖f‖ := by
  rw [C1HolderSpace.norm_eq_max, norm_eq_toC1HolderSpace f]
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

private theorem norm_ofC1HolderSpace_le (g : C1HolderSpace α E F) :
    ‖ofC1HolderSpace g‖ ≤ 2 * ‖g‖ := by
  rw [norm_eq_toC1HolderSpace, toC1HolderSpace_ofC1HolderSpace, two_mul]
  exact add_le_add g.norm_toBoundedContinuousFunction_le g.norm_fderiv_le

/-- The bounded `C^{1,α}` maps of the sum-norm scale are the elements of `C1HolderSpace`. The
identification preserves the underlying function; the norms are equivalent by
`CkHolderSpace.norm_equivC1HolderSpace_le` and
`CkHolderSpace.norm_le_two_mul_norm_equivC1HolderSpace`. -/
def equivC1HolderSpace : CkHolderSpace 1 α E F ≃L[ℝ] C1HolderSpace α E F :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toC1HolderSpace
      invFun := ofC1HolderSpace
      map_add' f g := C1HolderSpace.ext fun x ↦ by simp [toC1HolderSpace_apply]
      map_smul' c f := C1HolderSpace.ext fun x ↦ by simp [toC1HolderSpace_apply]
      left_inv := ofC1HolderSpace_toC1HolderSpace
      right_inv := toC1HolderSpace_ofC1HolderSpace }
    1 2 (fun f ↦ by simpa using norm_toC1HolderSpace_le f) norm_ofC1HolderSpace_le

/-- The identification with `C1HolderSpace` preserves the underlying function. -/
@[simp]
theorem equivC1HolderSpace_apply (f : CkHolderSpace 1 α E F) (x : E) :
    equivC1HolderSpace f x = f x :=
  toC1HolderSpace_apply f x

/-- The inverse identification with `C1HolderSpace` preserves the underlying function. -/
@[simp]
theorem coe_equivC1HolderSpace_symm (g : C1HolderSpace α E F) :
    ⇑(equivC1HolderSpace.symm g) = g :=
  coe_ofC1HolderSpace g

/-- The sum norm `‖f‖_∞ + ‖Df‖_∞ + [Df]_α` of a bounded `C^{1,α}` map is the sum of the two
terms whose maximum is its `C1HolderSpace` norm. -/
theorem norm_eq_norm_add_norm_fderiv (f : CkHolderSpace 1 α E F) :
    ‖f‖ = ‖C1HolderSpace.toBoundedContinuousFunction (equivC1HolderSpace f)‖ +
      ‖C1HolderSpace.fderiv (equivC1HolderSpace f)‖ :=
  norm_eq_toC1HolderSpace f

/-- The `C1HolderSpace` norm is at most the sum norm. -/
theorem norm_equivC1HolderSpace_le (f : CkHolderSpace 1 α E F) :
    ‖equivC1HolderSpace f‖ ≤ ‖f‖ :=
  norm_toC1HolderSpace_le f

/-- The sum norm is at most twice the `C1HolderSpace` norm. -/
theorem norm_le_two_mul_norm_equivC1HolderSpace (f : CkHolderSpace 1 α E F) :
    ‖f‖ ≤ 2 * ‖equivC1HolderSpace f‖ := by
  have h := norm_ofC1HolderSpace_le (toC1HolderSpace f)
  rw [ofC1HolderSpace_toC1HolderSpace] at h
  exact h

/-! ### Order two -/

/-- The second derivative of a bounded `C^{2,α}` map, in curried form, as a bounded continuous
field. -/
private def secondFDerivBCF (f : CkHolderSpace 2 α E F) : E →ᵇ (E →L[ℝ] E →L[ℝ] F) :=
  ofNormedAddCommGroup (fderiv ℝ (fderiv ℝ f)) (f.contDiff_fderiv.continuous_fderiv (by simp))
    ‖f‖ fun x ↦ by
      simpa [fderiv_fderiv_eq_continuousMultilinearCurryFin2_comp,
        LinearIsometryEquiv.norm_map] using f.norm_iteratedFDeriv_apply_le le_rfl x

private theorem coe_secondFDerivBCF (f : CkHolderSpace 2 α E F) :
    ⇑(secondFDerivBCF f) = fderiv ℝ (fderiv ℝ f) :=
  coe_ofNormedAddCommGroup ..

/-- The second derivative of a bounded `C^{2,α}` map, in curried form, as an element of the
bounded Hölder space. -/
private def secondFDerivHolder (f : CkHolderSpace 2 α E F) :
    HolderSpace α E (E →L[ℝ] E →L[ℝ] F) :=
  HolderSpace.ofBoundedContinuousFunction (secondFDerivBCF f) <| by
    rw [coe_secondFDerivBCF]
    exact f.holderWith_fderiv_fderiv.memHolder

private theorem secondFDerivHolder_apply (f : CkHolderSpace 2 α E F) (x : E) :
    secondFDerivHolder f x = fderiv ℝ (fderiv ℝ f) x := by
  rw [secondFDerivHolder, HolderSpace.ofBoundedContinuousFunction_apply, coe_secondFDerivBCF]

/-- The Hölder-space norm of the curried second derivative is the sum of the supremum norm of
the second derivative field and the Hölder seminorm of the second iterated derivative. -/
private theorem norm_secondFDerivHolder (f : CkHolderSpace 2 α E F) :
    ‖secondFDerivHolder f‖ =
      ‖f.iteratedFDeriv 2‖ + nnHolderNorm α (_root_.iteratedFDeriv ℝ 2 f) := by
  have hcoe : ⇑(secondFDerivHolder f) = fderiv ℝ (fderiv ℝ f) :=
    funext (secondFDerivHolder_apply f)
  have hnorm (x : E) : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖f.iteratedFDeriv 2 x‖ := by
    rw [← iteratedFDeriv_eq, Fin.val_two, fderiv_fderiv_eq_continuousMultilinearCurryFin2_comp,
      Function.comp_apply, LinearIsometryEquiv.norm_map]
  rw [HolderSpace.norm_def, HolderSpace.coe_toBoundedContinuousFunction, hcoe,
    fderiv_fderiv_eq_continuousMultilinearCurryFin2_comp,
    (LinearIsometryEquiv.isometry _).nnHolderNorm_comp]
  -- The supremum norms are compared pointwise: instance search does not find the norm of bounded
  -- continuous fields valued in curried bilinear maps within the default limits, so that norm is
  -- only reached through the instance already present in the goal.
  congr 1
  refine le_antisymm ((norm_le (norm_nonneg (f.iteratedFDeriv 2))).2 fun x ↦ ?_)
    ((norm_le (norm_nonneg (secondFDerivHolder f).toBoundedContinuousFunction)).2 fun x ↦ ?_)
  · rw [HolderSpace.toBoundedContinuousFunction_apply, hcoe, hnorm]
    exact norm_coe_le_norm _ x
  · rw [← hnorm, ← hcoe, ← HolderSpace.toBoundedContinuousFunction_apply]
    exact norm_coe_le_norm _ x

/-- A bounded `C^{2,α}` map, in the sum-norm space, as an element of `C2HolderSpace`. -/
private def toC2HolderSpace (f : CkHolderSpace 2 α E F) : C2HolderSpace α E F :=
  C2HolderSpace.mk (toBCF f) (fderivBCF f) (secondFDerivHolder f)
    (fun x ↦ by
      rw [coe_toBCF, coe_fderivBCF]
      exact hasFDerivAt_fderiv f x)
    fun x ↦ by
      rw [coe_fderivBCF, secondFDerivHolder_apply]
      exact ((f.contDiff_fderiv.differentiable (by simp)) x).hasFDerivAt

private theorem toC2HolderSpace_apply (f : CkHolderSpace 2 α E F) (x : E) :
    toC2HolderSpace f x = f x := by
  rw [← C2HolderSpace.toBoundedContinuousFunction_apply, toC2HolderSpace,
    C2HolderSpace.toBoundedContinuousFunction_mk, coe_toBCF]

/-- An element of `C2HolderSpace` as a bounded `C^{2,α}` map in the sum-norm space. -/
private def ofC2HolderSpace (g : C2HolderSpace α E F) : CkHolderSpace 2 α E F :=
  ofContDiff g (by exact_mod_cast g.contDiff_two)
    (fun i hi ↦ ⟨‖g‖, fun x ↦ by
      obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      · rw [norm_iteratedFDeriv_zero, ← C2HolderSpace.toBoundedContinuousFunction_apply]
        exact (norm_coe_le_norm _ x).trans g.norm_toBoundedContinuousFunction_le
      · rw [norm_iteratedFDeriv_one, C2HolderSpace.fderiv_eq]
        exact (norm_coe_le_norm _ x).trans g.norm_fderiv_le
      · rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one, g.fderiv_eq_fderiv,
          C2HolderSpace.fderiv_fderiv_eq]
        exact (g.secondFDeriv.norm_apply_le x).trans g.norm_secondFDeriv_le⟩)
    g.memHolder_iteratedFDeriv_two

private theorem coe_ofC2HolderSpace (g : C2HolderSpace α E F) : ⇑(ofC2HolderSpace g) = g := by
  rw [ofC2HolderSpace, coe_ofContDiff]

/-- The sum norm of a bounded `C^{2,α}` map is the sum of the three terms whose maximum is its
`C2HolderSpace` norm. -/
private theorem norm_eq_toC2HolderSpace (f : CkHolderSpace 2 α E F) :
    ‖f‖ = ‖(toC2HolderSpace f).toBoundedContinuousFunction‖ + ‖(toC2HolderSpace f).fderiv‖ +
      ‖(toC2HolderSpace f).secondFDeriv‖ := by
  rw [norm_eq, Fin.sum_univ_three, toC2HolderSpace, C2HolderSpace.toBoundedContinuousFunction_mk,
    C2HolderSpace.fderiv_mk, C2HolderSpace.secondFDeriv_mk, norm_toBCF, norm_fderivBCF,
    norm_secondFDerivHolder, add_assoc]

private theorem ofC2HolderSpace_toC2HolderSpace (f : CkHolderSpace 2 α E F) :
    ofC2HolderSpace (toC2HolderSpace f) = f :=
  ext fun x ↦ by rw [coe_ofC2HolderSpace, toC2HolderSpace_apply]

private theorem toC2HolderSpace_ofC2HolderSpace (g : C2HolderSpace α E F) :
    toC2HolderSpace (ofC2HolderSpace g) = g :=
  C2HolderSpace.ext fun x ↦ by rw [toC2HolderSpace_apply, coe_ofC2HolderSpace]

private theorem norm_toC2HolderSpace_le (f : CkHolderSpace 2 α E F) :
    ‖toC2HolderSpace f‖ ≤ ‖f‖ := by
  rw [C2HolderSpace.norm_eq_max, norm_eq_toC2HolderSpace f]
  refine max_le ?_ (max_le ?_ ?_) <;>
    linarith [norm_nonneg (toC2HolderSpace f).toBoundedContinuousFunction,
      norm_nonneg (toC2HolderSpace f).fderiv, norm_nonneg (toC2HolderSpace f).secondFDeriv]

private theorem norm_ofC2HolderSpace_le (g : C2HolderSpace α E F) :
    ‖ofC2HolderSpace g‖ ≤ 3 * ‖g‖ := by
  rw [norm_eq_toC2HolderSpace, toC2HolderSpace_ofC2HolderSpace]
  linarith [g.norm_toBoundedContinuousFunction_le, g.norm_fderiv_le, g.norm_secondFDeriv_le]

/-- The bounded `C^{2,α}` maps of the sum-norm scale are the elements of `C2HolderSpace`. The
identification preserves the underlying function; the norms are equivalent by
`CkHolderSpace.norm_equivC2HolderSpace_le` and
`CkHolderSpace.norm_le_three_mul_norm_equivC2HolderSpace`. -/
def equivC2HolderSpace : CkHolderSpace 2 α E F ≃L[ℝ] C2HolderSpace α E F :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := toC2HolderSpace
      invFun := ofC2HolderSpace
      map_add' f g := C2HolderSpace.ext fun x ↦ by simp [toC2HolderSpace_apply]
      map_smul' c f := C2HolderSpace.ext fun x ↦ by simp [toC2HolderSpace_apply]
      left_inv := ofC2HolderSpace_toC2HolderSpace
      right_inv := toC2HolderSpace_ofC2HolderSpace }
    1 3 (fun f ↦ by simpa using norm_toC2HolderSpace_le f) norm_ofC2HolderSpace_le

/-- The identification with `C2HolderSpace` preserves the underlying function. -/
@[simp]
theorem equivC2HolderSpace_apply (f : CkHolderSpace 2 α E F) (x : E) :
    equivC2HolderSpace f x = f x :=
  toC2HolderSpace_apply f x

/-- The inverse identification with `C2HolderSpace` preserves the underlying function. -/
@[simp]
theorem coe_equivC2HolderSpace_symm (g : C2HolderSpace α E F) :
    ⇑(equivC2HolderSpace.symm g) = g :=
  coe_ofC2HolderSpace g

/-- The sum norm `‖f‖_∞ + ‖Df‖_∞ + ‖D²f‖_∞ + [D²f]_α` of a bounded `C^{2,α}` map is the sum of
the three terms whose maximum is its `C2HolderSpace` norm. -/
theorem norm_eq_norm_add_norm_fderiv_add_norm_secondFDeriv (f : CkHolderSpace 2 α E F) :
    ‖f‖ = ‖(equivC2HolderSpace f).toBoundedContinuousFunction‖ +
      ‖(equivC2HolderSpace f).fderiv‖ + ‖(equivC2HolderSpace f).secondFDeriv‖ :=
  norm_eq_toC2HolderSpace f

/-- The `C2HolderSpace` norm is at most the sum norm. -/
theorem norm_equivC2HolderSpace_le (f : CkHolderSpace 2 α E F) :
    ‖equivC2HolderSpace f‖ ≤ ‖f‖ :=
  norm_toC2HolderSpace_le f

/-- The sum norm is at most three times the `C2HolderSpace` norm. -/
theorem norm_le_three_mul_norm_equivC2HolderSpace (f : CkHolderSpace 2 α E F) :
    ‖f‖ ≤ 3 * ‖equivC2HolderSpace f‖ := by
  have h := norm_ofC2HolderSpace_le (toC2HolderSpace f)
  rw [ofC2HolderSpace_toC2HolderSpace] at h
  exact h

end CkHolderSpace

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic

/-!
# The order-zero Hölder space on an open set

For an open set `Ω` of a real normed space `E`, an element of `C^{0,α}(Ω, F)`
(`TauCeti.CkHolderSpaceOn 0 α Ω F`) is a single bounded `α`-Hölder field of `0`-multilinear
maps on `Ω`, with norm its supremum norm plus its Hölder seminorm. Identifying `0`-multilinear
maps with their values, this is exactly the bounded Hölder space `TauCeti.HolderSpace α Ω F` on
the subtype `Ω`, with the same norm. This file records that identification as a linear isometry
equivalence. It lets the pointwise operations on `HolderSpace` and on `CkHolderSpaceOn` be used
together, for instance to land in `C^{0,α}(Ω)` with `ContinuousLinearMap.compCkHolderOn₂`.

## Main declarations

* `TauCeti.CkHolderSpaceOn.zeroEquivHolderSpace`: the isometric identification
  `C^{0,α}(Ω, F) ≃ₗᵢ[ℝ] HolderSpace α Ω F`, which does not change values
  (`TauCeti.CkHolderSpaceOn.zeroEquivHolderSpace_apply`,
  `TauCeti.CkHolderSpaceOn.zeroEquivHolderSpace_symm_apply`).
-/

public noncomputable section

open TopologicalSpace
open scoped NNReal

namespace TauCeti.CkHolderSpaceOn

variable {α : ℝ≥0} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The values of an element of `C^{0,α}(Ω)`, as a bounded Hölder function on `Ω`. -/
private def toHolderSpaceL : CkHolderSpaceOn 0 α Ω F →L[ℝ] HolderSpace α Ω F :=
  HolderSpace.compLeftL
      (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap ∘L
    iteratedFDerivHolderL

private theorem toHolderSpaceL_apply (f : CkHolderSpaceOn 0 α Ω F) (x : Ω) :
    toHolderSpaceL f x = f x := by
  have h := f.iteratedFDeriv_eq f.extend_apply 0 x
  have h2 : f.extend x = continuousMultilinearCurryFin0 ℝ E F (f.iteratedFDeriv 0 x) :=
    (iteratedFDeriv_zero_apply (f := f.extend) (x := (x : E)) 0).symm.trans
      (congrArg (fun m : E [×0]→L[ℝ] F ↦ m 0) h)
  simp only [toHolderSpaceL, ContinuousLinearMap.comp_apply, HolderSpace.compLeftL_apply,
    iteratedFDerivHolderL_apply, coe_iteratedFDerivHolder]
  rw [← f.extend_apply x, h2]
  rfl

private theorem norm_toHolderSpaceL (f : CkHolderSpaceOn 0 α Ω F) :
    ‖toHolderSpaceL f‖ = ‖f‖ := by
  rw [toHolderSpaceL, ContinuousLinearMap.comp_apply, HolderSpace.norm_compLeftL_linearIsometry,
    iteratedFDerivHolderL_apply, HolderSpace.norm_def, norm_eq, Fin.sum_univ_one,
    toBoundedContinuousFunction_iteratedFDerivHolder]
  rfl

private theorem surjective_toHolderSpaceL :
    Function.Surjective (toHolderSpaceL (α := α) (Ω := Ω) (F := F)) := by
  intro f
  have hcont : ContinuousOn (Function.extend Subtype.val (f : Ω → F) 0) Ω := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert f.toBoundedContinuousFunction.continuous using 1
    funext x
    rw [HolderSpace.coe_toBoundedContinuousFunction]
    exact Subtype.val_injective.extend_apply (f : Ω → F) 0 x
  have hbdd : ∀ i ≤ 0, ∃ C, ∀ x : Ω,
      ‖_root_.iteratedFDeriv ℝ i (Function.extend Subtype.val (f : Ω → F) 0) x‖ ≤ C := by
    intro i hi
    obtain rfl := Nat.le_zero.1 hi
    exact ⟨‖f‖, fun x ↦ by
      rw [_root_.norm_iteratedFDeriv_zero, Subtype.val_injective.extend_apply]
      exact f.norm_apply_le x⟩
  have hholder : MemHolder α fun x : Ω ↦
      _root_.iteratedFDeriv ℝ 0 (Function.extend Subtype.val (f : Ω → F) 0) x := by
    obtain ⟨C, hC⟩ := f.memHolder
    simp only [HolderSpace.coe_toBoundedContinuousFunction] at hC
    refine ⟨C, fun x y ↦ ?_⟩
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.edist_map,
      Subtype.val_injective.extend_apply]
    exact hC x y
  exact ⟨ofContDiffOn (k := 0) (Function.extend Subtype.val (f : Ω → F) 0)
    (by exact_mod_cast contDiffOn_zero.2 hcont) hbdd hholder, HolderSpace.ext fun x ↦ by
      rw [toHolderSpaceL_apply, ofContDiffOn_apply, Subtype.val_injective.extend_apply]⟩

/-- The identification of `C^{0,α}(Ω, F)` with the bounded `α`-Hölder functions on `Ω`: an element
is sent to its values. It preserves the norm. -/
def zeroEquivHolderSpace : CkHolderSpaceOn 0 α Ω F ≃ₗᵢ[ℝ] HolderSpace α Ω F :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (toHolderSpaceL (α := α) (Ω := Ω) (F := F)).toLinearMap
      norm_map' := norm_toHolderSpaceL } surjective_toHolderSpaceL

/-- The identification `zeroEquivHolderSpace` does not change values. -/
@[simp]
theorem zeroEquivHolderSpace_apply (f : CkHolderSpaceOn 0 α Ω F) (x : Ω) :
    zeroEquivHolderSpace f x = f x :=
  toHolderSpaceL_apply f x

/-- The inverse of `zeroEquivHolderSpace` does not change values. -/
@[simp]
theorem zeroEquivHolderSpace_symm_apply (f : HolderSpace α Ω F) (x : Ω) :
    zeroEquivHolderSpace.symm f x = f x := by
  rw [← zeroEquivHolderSpace_apply, LinearIsometryEquiv.apply_symm_apply]

end TauCeti.CkHolderSpaceOn

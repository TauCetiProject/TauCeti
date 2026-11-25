/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.Normed.Operator.Banach
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Fredholm operators from finite-codimension restrictions

Let `T : E →L[𝕜] F` carry a closed finite-codimensional subspace `E₁` into a closed
finite-codimensional subspace `F₁`. Mathlib's `ContinuousLinearMap.IsFredholm.of_restrict` shows
that `T` is Fredholm when the induced operator `E₁ →L[𝕜] F₁` is. This file records the accompanying
index formula: the index of `T` is the index of the restriction plus `codim E₁ - codim F₁`. It is a
basic reduction, in particular when an operator is first controlled after discarding finitely many
modes.

## Main declarations

* `ContinuousLinearMap.index_restrict`: the index formula for the restriction of a
  continuous linear map to closed finite-codimensional subspaces.
* `ContinuousLinearMap.isInvertible_restrict_map_of_disjoint_ker`: a continuous linear map that is
  injective on a closed subspace `E₁` of a Banach space, with closed image, restricts to an
  invertible operator from `E₁` onto its image.

The finite-codimension reduction and index convention follow McDuff--Salamon,
*J-holomorphic Curves and Symplectic Topology*, Appendix A.1. The proof factors `T` through
the inclusions of the subspaces and applies Mathlib's composition formula for the index.
-/

public section

namespace ContinuousLinearMap

open Module

variable {K E F : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup F] [NormedSpace K F]
variable {T : E →L[K] F} {E₁ : Submodule K E} {F₁ : Submodule K F}


/-- The index of the restriction of a continuous linear map from `E` to `F` to closed
finite-codimensional subspaces `E₁` and `F₁` is the index of the full operator minus `codim E₁`
plus `codim F₁`. -/
@[simp]
theorem index_restrict (hE₁ : IsClosed (E₁ : Set E)) [E₁.CoFG]
    (hF₁ : IsClosed (F₁ : Set F)) [F₁.CoFG] (hT : Set.MapsTo T E₁ F₁)
    (hT₁ : IsFredholm (T.restrict hT)) :
    index (T.restrict hT) = index T -
      (finrank K (E ⧸ E₁) : ℤ) + finrank K (F ⧸ F₁) := by
  have hTfull := IsFredholm.of_restrict hE₁ hF₁ hT hT₁
  have hιE := Submodule.isFredholm_subtypeL hE₁
  have hιF := Submodule.isFredholm_subtypeL hF₁
  have hfactor : T.comp E₁.subtypeL = F₁.subtypeL.comp (T.restrict hT) := by
    ext x
    exact (congrArg Subtype.val (restrict_apply hT x)).symm
  have hdom : index (T.comp E₁.subtypeL) =
      index T + index E₁.subtypeL :=
    index_comp hTfull hιE
  have hcod : index (F₁.subtypeL.comp (T.restrict hT)) =
      index F₁.subtypeL + index (T.restrict hT) :=
    index_comp hιF hT₁
  have hEindex : index E₁.subtypeL = -(finrank K (E ⧸ E₁) : ℤ) := by
    rw [index_of_injective E₁.subtypeL Subtype.val_injective,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  have hFindex : index F₁.subtypeL = -(finrank K (F ⧸ F₁) : ℤ) := by
    rw [index_of_injective F₁.subtypeL Subtype.val_injective,
      Submodule.toLinearMap_subtypeL, Submodule.range_subtype]
  rw [hfactor, hcod, hEindex, hFindex] at hdom
  omega

omit [CompleteSpace K] in
/-- If a continuous linear map `T` between Banach spaces is injective on a closed subspace `E₁` and
`T(E₁)` is closed, then `T` restricts to an invertible operator from `E₁` onto `T(E₁)`. -/
theorem isInvertible_restrict_map_of_disjoint_ker [CompleteSpace E] [CompleteSpace F]
    (hE₁ : IsClosed (E₁ : Set E)) (hker : Disjoint E₁ T.ker)
    (hTE₁ : IsClosed (E₁.map (T : E →ₗ[K] F) : Set F)) :
    (T.restrict (fun _ hx ↦ Submodule.mem_map_of_mem hx :
      Set.MapsTo T E₁ (E₁.map (T : E →ₗ[K] F)))).IsInvertible := by
  have : CompleteSpace E₁ := hE₁.isComplete.completeSpace_coe
  have : CompleteSpace (E₁.map (T : E →ₗ[K] F)) := hTE₁.isComplete.completeSpace_coe
  refine isInvertible_iff_bijective.2 ⟨(injective_iff_map_eq_zero _).2 fun v h ↦ ?_,
    fun ⟨y, hy⟩ ↦ ?_⟩
  · have h' : T v = 0 := by simpa using congr(($h : F))
    exact Subtype.ext (Submodule.disjoint_def.mp hker v v.property (LinearMap.mem_ker.mpr h'))
  · obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
    exact ⟨⟨v, hv⟩, restrict_apply _ _⟩

end ContinuousLinearMap

end

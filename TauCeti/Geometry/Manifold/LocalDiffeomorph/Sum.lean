/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# The inclusions of a disjoint union are local diffeomorphisms

For manifolds `M` and `M'` modelled on the same space, Mathlib charts the disjoint union `M ⊕ M'`
by the charts of the two summands. Each inclusion `Sum.inl : M → M ⊕ M'` and
`Sum.inr : M' → M ⊕ M'` is then a `C^n` diffeomorphism onto its open range, whose inverse is
`Sum.elim id (fun _ ↦ x)`, respectively `Sum.elim (fun _ ↦ x) id`, for any point `x`. In
particular they are `C^n` local diffeomorphisms, so structures read through derivatives, such as
orientations, transfer from a space glued from two pieces to the pieces and back.

## Main results

* `TauCeti.isLocalDiffeomorph_sumInl`, `TauCeti.isLocalDiffeomorph_sumInr`: the inclusions of a
  disjoint union are `C^n` local diffeomorphisms.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']

/-- The left inclusion of a disjoint union of manifolds is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_sumInl : IsLocalDiffeomorph I I n (Sum.inl : M → M ⊕ M') := fun x ↦ by
  let Φ : PartialDiffeomorph I I M (M ⊕ M') n :=
    { toFun := Sum.inl
      invFun := Sum.elim id fun _ ↦ x
      source := univ
      target := range Sum.inl
      map_source' := fun y _ ↦ mem_range_self y
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := fun _ _ ↦ rfl
      right_inv' := by rintro _ ⟨y, rfl⟩; rfl
      open_source := isOpen_univ
      open_target := isOpen_range_inl
      contMDiffOn_toFun := ContMDiff.inl.contMDiffOn
      contMDiffOn_invFun := (contMDiff_id.sumElim contMDiff_const).contMDiffOn }
  exact Φ.isLocalDiffeomorphAt I I n (mem_univ x)

/-- The right inclusion of a disjoint union of manifolds is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_sumInr : IsLocalDiffeomorph I I n (Sum.inr : M' → M ⊕ M') := fun x ↦ by
  let Φ : PartialDiffeomorph I I M' (M ⊕ M') n :=
    { toFun := Sum.inr
      invFun := Sum.elim (fun _ ↦ x) id
      source := univ
      target := range Sum.inr
      map_source' := fun y _ ↦ mem_range_self y
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := fun _ _ ↦ rfl
      right_inv' := by rintro _ ⟨y, rfl⟩; rfl
      open_source := isOpen_univ
      open_target := isOpen_range_inr
      contMDiffOn_toFun := ContMDiff.inr.contMDiffOn
      contMDiffOn_invFun := (contMDiff_const.sumElim contMDiff_id).contMDiffOn }
  exact Φ.isLocalDiffeomorphAt I I n (mem_univ x)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Null
public import TauCeti.AlgebraicTopology.SimplicialComplex.Pure
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic
import TauCeti.Geometry.Manifold.SmoothTriangulation.Dimension
import TauCeti.Geometry.Manifold.SmoothTriangulation.LocallyFinite

/-!
# Smooth triangulations are pure

A smooth triangulation `κ : |K| ≃ₜ M` of a manifold modelled on a finite-dimensional real space
`E` is pure of dimension `dim E`: every simplex of `K` is a face of a simplex with `dim E + 1`
vertices (`TauCeti.IsSmoothTriangulation.isPure`).

The upper bound `|σ| ≤ dim E + 1` is `TauCeti.IsSmoothTriangulation.card_le`. For the lower bound,
a simplex lies in only finitely many simplices (local finiteness of `K`), so it lies in a maximal
simplex `τ`. The points of `|K|` whose carrier contains `τ` form an open set, the intersection of
the open stars of the vertices of `τ`, and by maximality they all lie in the closed simplex `τ`.
If `|τ| ≤ dim E`, its image under `κ` would be a nonempty open subset of the null set `κ(τ)`
(`TauCeti.IsSmoothTriangulation.isNullSet_image_range_faceInclusion`), which is impossible since
null sets have empty interior.

## Main results

* `TauCeti.IsSmoothTriangulation.isPure`: a smooth triangulation is pure of dimension `dim E`.
* `TauCeti.IsSmoothTriangulation.dimension_eq`: a smooth triangulation of a nonempty manifold has
  dimension `dim E`.
-/

public section

open Set Function Module AbstractSimplicialComplex TauCeti.SetLike

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : WithTop ℕ∞}
  {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}

/-- In a smooth triangulation of a manifold modelled on `E`, a maximal simplex has at least
`dim E + 1` vertices: otherwise the image of its open simplex would be a nonempty open null set. -/
private theorem IsSmoothTriangulation.finrank_lt_card_of_maximal
    (h : IsSmoothTriangulation I n κ) {τ : Finset ι} (hτ : Maximal (· ∈ K) τ) :
    finrank ℝ E < τ.card := by
  borelize E
  by_contra! hle
  -- The points whose carrier contains `τ`: the intersection of the open stars of its vertices.
  set O : Set (Realization K) := ⋂ v ∈ τ, K.openStarRealization v
  obtain ⟨x, hx⟩ := exists_support_eq hτ.prop
  have hxO : x ∈ O := K.mem_biInter_openStarRealization_iff.2 hx.ge
  -- By maximality, every such point lies in the closed simplex `τ`.
  have hsub : O ⊆ range (faceInclusion K ⟨τ, hτ.prop⟩) := fun y hy ↦
    (K.mem_range_faceInclusion_iff _ y).2
      (hτ.2 (support_mem K y) (K.mem_biInter_openStarRealization_iff.1 hy))
  have hint : κ '' O ⊆ interior (κ '' range (faceInclusion K ⟨τ, hτ.prop⟩)) :=
    interior_maximal (image_mono hsub) (κ.isOpenMap O (K.isOpen_biInter_openStarRealization τ))
  rw [(h.isNullSet_image_range_faceInclusion ⟨τ, hτ.prop⟩ hle).interior_eq_empty] at hint
  exact hint (mem_image_of_mem κ hxO)

/-- **Smooth triangulations are pure.** In a smooth triangulation of a manifold modelled on a
finite-dimensional space `E`, every simplex is a face of a simplex with `dim E + 1` vertices. -/
theorem IsSmoothTriangulation.isPure (h : IsSmoothTriangulation I n κ) :
    K.toPreAbstractSimplicialComplex.IsPure (finrank ℝ E) := by
  rw [PreAbstractSimplicialComplex.isPure_iff]
  intro σ hσ
  obtain ⟨v, hv⟩ := (K.isRelLowerSet_faces hσ).1
  -- Only finitely many simplices contain `σ`, so `σ` lies in a maximal one.
  have hfin : {τ : Finset ι | τ ∈ K ∧ σ ⊆ τ}.Finite :=
    (finite_setOf_mem_of_homeomorph_manifold I κ v).subset fun τ hτ ↦ ⟨hτ.1, hτ.2 hv⟩
  obtain ⟨τ, hτ⟩ := hfin.exists_maximal ⟨σ, hσ, subset_rfl⟩
  have hτK : Maximal (· ∈ K) τ :=
    ⟨hτ.prop.1, fun τ' hτ' hττ' ↦ hτ.2 ⟨hτ', hτ.prop.2.trans hττ'⟩ hττ'⟩
  exact ⟨τ, hτ.prop.1, hτ.prop.2,
    le_antisymm (h.card_le hτ.prop.1) (h.finrank_lt_card_of_maximal hτK)⟩

/-- A smooth triangulation of a nonempty manifold modelled on `E` has dimension `dim E`. -/
theorem IsSmoothTriangulation.dimension_eq [Nonempty M] (h : IsSmoothTriangulation I n κ) :
    K.dimension = (finrank ℝ E : WithBot ℕ∞) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  rw [← dimension_toPreAbstractSimplicialComplex]
  exact h.isPure.dimension_eq fun hK ↦ PreAbstractSimplicialComplex.notMem_bot
    (hK ▸ mem_toPreAbstractSimplicialComplex.2 (support_mem K (κ.symm x)))

end TauCeti

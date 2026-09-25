/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Diagram

/-!
# Pairwise overlaps of analytic affine toric charts

For two cones of a regular fan, the affine chart of their intersection embeds openly in
each cone chart. Its image is the overlap locus. Interchanging the cones gives a canonical
homeomorphism between the two overlap loci, obtained by passing through the intersection
chart. These are the open sets and transitions used in the gluing of the analytic fan.

The construction uses the diagram of affine complex points. In particular, the transition
is induced by restriction of characters and does not depend on generators chosen to present
the affine-point topologies.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- The cone common to two affine charts of a fan. -/
abbrev analyticOverlapCone (σ τ : Φ.cones) : Φ.cones :=
  ⟨σ.1 ⊓ τ.1, Φ.inf_mem σ.2 τ.2⟩

variable (hΦ : Φ.IsRegular)

/-- The open embedding of the common chart into the first chart. -/
noncomputable def analyticOverlapLeft (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (Φ.analyticOverlapCone σ τ) ⟶
      (Φ.analyticAffineChartDiagram hΦ).obj σ :=
  (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE (by
      -- The subtype order unfolds to the order on its cone carriers.
      change σ.1 ⊓ τ.1 ≤ σ.1
      exact inf_le_left))

/-- The open embedding of the common chart into the second chart. -/
noncomputable def analyticOverlapRight (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (Φ.analyticOverlapCone σ τ) ⟶
      (Φ.analyticAffineChartDiagram hΦ).obj τ :=
  (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE (by
      -- The subtype order unfolds to the order on its cone carriers.
      change σ.1 ⊓ τ.1 ≤ τ.1
      exact inf_le_right))

/-- The common chart embeds openly into the first chart. -/
theorem isOpenEmbedding_analyticOverlapLeft (σ τ : Φ.cones) :
    IsOpenEmbedding (Φ.analyticOverlapLeft hΦ σ τ) := by
  unfold analyticOverlapLeft
  exact Φ.isOpenEmbedding_analyticAffineChartDiagram_map hΦ _

/-- The common chart embeds openly into the second chart. -/
theorem isOpenEmbedding_analyticOverlapRight (σ τ : Φ.cones) :
    IsOpenEmbedding (Φ.analyticOverlapRight hΦ σ τ) := by
  unfold analyticOverlapRight
  exact Φ.isOpenEmbedding_analyticAffineChartDiagram_map hΦ _

/-- The open overlap locus in the first affine chart. -/
def analyticOverlap (σ τ : Φ.cones) : TopologicalSpace.Opens
    ((Φ.analyticAffineChartDiagram hΦ).obj σ) :=
  ⟨Set.range (Φ.analyticOverlapLeft hΦ σ τ),
    (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isOpen_range⟩

/-- Membership in the overlap means coming from a point of the intersection chart. -/
@[simp] theorem mem_analyticOverlap (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    x ∈ Φ.analyticOverlap hΦ σ τ ↔
      ∃ y, Φ.analyticOverlapLeft hΦ σ τ y = x :=
  Iff.rfl

/-- Interchanging the two cones gives an isomorphism of their intersection charts. -/
noncomputable def analyticOverlapSwapIso (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (Φ.analyticOverlapCone σ τ) ≅
      (Φ.analyticAffineChartDiagram hΦ).obj (Φ.analyticOverlapCone τ σ) where
  hom := (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE (by
      -- Expose the two carrier cones to apply commutativity of intersection.
      change σ.1 ⊓ τ.1 ≤ τ.1 ⊓ σ.1
      exact le_of_eq (inf_comm _ _)))
  inv := (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE (by
      -- Expose the two carrier cones to apply commutativity of intersection.
      change τ.1 ⊓ σ.1 ≤ σ.1 ⊓ τ.1
      exact le_of_eq (inf_comm _ _)))
  hom_inv_id := by
    rw [← Functor.map_comp]
    exact congrArg ((Φ.analyticAffineChartDiagram hΦ).map)
      (Subsingleton.elim _ (𝟙 _)) |>.trans ((Φ.analyticAffineChartDiagram hΦ).map_id _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    exact congrArg ((Φ.analyticAffineChartDiagram hΦ).map)
      (Subsingleton.elim _ (𝟙 _)) |>.trans ((Φ.analyticAffineChartDiagram hΦ).map_id _)

/-- The right overlap inclusion is the left inclusion after interchanging the cones. -/
theorem analyticOverlapRight_eq_swap_comp_left (σ τ : Φ.cones) :
    Φ.analyticOverlapRight hΦ σ τ =
      (Φ.analyticOverlapSwapIso hΦ σ τ).hom ≫
        Φ.analyticOverlapLeft hΦ τ σ := by
  unfold analyticOverlapRight analyticOverlapLeft analyticOverlapSwapIso
  rw [← Functor.map_comp]
  exact congrArg ((Φ.analyticAffineChartDiagram hΦ).map) (Subsingleton.elim _ _)

/-- The two orientations of the overlap have the same image in the second chart. -/
theorem range_analyticOverlapRight (σ τ : Φ.cones) :
    Set.range (Φ.analyticOverlapRight hΦ σ τ) =
      (Φ.analyticOverlap hΦ τ σ : Set _) := by
  rw [Φ.analyticOverlapRight_eq_swap_comp_left hΦ σ τ]
  -- `Set.range_comp` is stated for the underlying functions of the TopCat maps.
  change Set.range ((Φ.analyticOverlapLeft hΦ τ σ) ∘
    (Φ.analyticOverlapSwapIso hΦ σ τ).hom) = _
  rw [Set.range_comp]
  have hs : Function.Surjective (Φ.analyticOverlapSwapIso hΦ σ τ).hom :=
    (TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)).surjective
  rw [hs.range_eq]
  simp only [Set.image_univ]
  rfl

/-- The transition between the two open overlap loci, induced by their common chart. -/
noncomputable def analyticOverlapHomeomorph (σ τ : Φ.cones) :
    (Φ.analyticOverlap hΦ σ τ) ≃ₜ
      (Φ.analyticOverlap hΦ τ σ) :=
  (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph.symm |>.trans
    ((TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)).trans
      ((Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph))

/-- On a point represented by the intersection chart, the transition is the other
intersection-chart inclusion. -/
@[simp] theorem analyticOverlapHomeomorph_apply (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj (Φ.analyticOverlapCone σ τ)) :
    Φ.analyticOverlapHomeomorph hΦ σ τ
      ⟨Φ.analyticOverlapLeft hΦ σ τ x, by
        -- Membership in this open set is membership in the range of its inclusion.
        change (Φ.analyticOverlapLeft hΦ σ τ x) ∈
          Set.range (Φ.analyticOverlapLeft hΦ σ τ)
        exact ⟨x, rfl⟩⟩ =
      ⟨Φ.analyticOverlapRight hΦ σ τ x,
        by
          -- Use the range description of the opposite overlap.
          change (Φ.analyticOverlapRight hΦ σ τ x) ∈
            (Φ.analyticOverlap hΦ τ σ : Set _)
          rw [← Φ.range_analyticOverlapRight hΦ σ τ]
          exact ⟨x, rfl⟩⟩ := by
  apply Subtype.ext
  let eL := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph
  let eR := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph
  let s := TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)
  -- Expose the composite of homeomorphisms to apply its inverse law.
  change ((eL.symm.trans (s.trans eR))
    ⟨Φ.analyticOverlapLeft hΦ σ τ x, _⟩).1 = Φ.analyticOverlapRight hΦ σ τ x
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply]
  have hL : eL.symm ⟨Φ.analyticOverlapLeft hΦ σ τ x, by exact ⟨x, rfl⟩⟩ = x := by
    exact eL.symm_apply_apply x
  rw [hL]
  exact congrFun (congrArg (fun f : _ ⟶ _ ↦ (f : _ → _))
    (Φ.analyticOverlapRight_eq_swap_comp_left hΦ σ τ)) x |>.symm

end TauCeti.Toric.Fan

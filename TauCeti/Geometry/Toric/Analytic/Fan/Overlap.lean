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

variable (hΦ : Φ.IsRegular)

/-- The open embedding of the common chart into the first chart. -/
noncomputable def analyticOverlapLeft (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ) ⟶
      (Φ.analyticAffineChartDiagram hΦ).obj σ :=
  (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE inf_le_left)

/-- The left overlap inclusion is the diagram map for the meet inequality. -/
theorem analyticOverlapLeft_def (σ τ : Φ.cones) :
    Φ.analyticOverlapLeft hΦ σ τ =
      (Φ.analyticAffineChartDiagram hΦ).map (homOfLE inf_le_left) := (rfl)

/-- The open embedding of the common chart into the second chart. -/
noncomputable def analyticOverlapRight (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ) ⟶
      (Φ.analyticAffineChartDiagram hΦ).obj τ :=
  (Φ.analyticAffineChartDiagram hΦ).map
    (homOfLE inf_le_right)

/-- The right overlap inclusion is the diagram map for the meet inequality. -/
theorem analyticOverlapRight_def (σ τ : Φ.cones) :
    Φ.analyticOverlapRight hΦ σ τ =
      (Φ.analyticAffineChartDiagram hΦ).map (homOfLE inf_le_right) := (rfl)

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
def analyticOverlapOpens (σ τ : Φ.cones) : TopologicalSpace.Opens
    ((Φ.analyticAffineChartDiagram hΦ).obj σ) :=
  ⟨Set.range (Φ.analyticOverlapLeft hΦ σ τ),
    (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isOpen_range⟩

/-- The carrier of the overlap open set is the image of the left inclusion. -/
@[simp] theorem coe_analyticOverlapOpens (σ τ : Φ.cones) :
    (Φ.analyticOverlapOpens hΦ σ τ : Set _) =
      Set.range (Φ.analyticOverlapLeft hΦ σ τ) := (rfl)

/-- Membership in the overlap means coming from a point of the intersection chart. -/
@[simp] theorem mem_analyticOverlapOpens (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    x ∈ Φ.analyticOverlapOpens hΦ σ τ ↔
      ∃ y, Φ.analyticOverlapLeft hΦ σ τ y = x :=
  (Iff.rfl)

/-- A chart overlaps itself in the whole chart. -/
@[simp] theorem analyticOverlapOpens_self (σ : Φ.cones) :
    Φ.analyticOverlapOpens hΦ σ σ = ⊤ := by
  apply TopologicalSpace.Opens.ext
  rw [coe_analyticOverlapOpens, analyticOverlapLeft_def, TopologicalSpace.Opens.coe_top]
  have h : (homOfLE (inf_le_left : σ ⊓ σ ≤ σ) : σ ⊓ σ ⟶ σ) =
      eqToHom (inf_idem σ) := Subsingleton.elim _ _
  rw [h]
  exact Set.range_eq_univ.mpr
    (TopCat.homeoOfIso ((Φ.analyticAffineChartDiagram hΦ).mapIso
      (eqToIso (inf_idem σ)))).surjective

/-- Interchanging the two cones gives an isomorphism of their intersection charts. -/
noncomputable def analyticOverlapSwapIso (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ) ≅
      (Φ.analyticAffineChartDiagram hΦ).obj (τ ⊓ σ) :=
  (Φ.analyticAffineChartDiagram hΦ).mapIso (eqToIso (inf_comm σ τ))

/-- The forward swap is the chart diagram applied to the equality `σ ⊓ τ = τ ⊓ σ`. -/
@[simp] theorem analyticOverlapSwapIso_hom (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso hΦ σ τ).hom =
      (Φ.analyticAffineChartDiagram hΦ).map (eqToHom (inf_comm σ τ)) := (rfl)

/-- The inverse swap is the chart diagram applied to the equality `τ ⊓ σ = σ ⊓ τ`. -/
@[simp] theorem analyticOverlapSwapIso_inv (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso hΦ σ τ).inv =
      (Φ.analyticAffineChartDiagram hΦ).map (eqToHom (inf_comm σ τ).symm) := (rfl)

/-- Reversing the swap exchanges its two orientations. -/
@[simp] theorem analyticOverlapSwapIso_symm (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso hΦ σ τ).symm =
      Φ.analyticOverlapSwapIso hΦ τ σ := by
  apply Iso.ext
  rw [Iso.symm_hom, analyticOverlapSwapIso_inv, analyticOverlapSwapIso_hom]

/-- The right overlap inclusion is the left inclusion after interchanging the cones. -/
theorem analyticOverlapRight_eq_swap_comp_left (σ τ : Φ.cones) :
    Φ.analyticOverlapRight hΦ σ τ =
      (Φ.analyticOverlapSwapIso hΦ σ τ).hom ≫
        Φ.analyticOverlapLeft hΦ τ σ := by
  rw [analyticOverlapRight_def, analyticOverlapLeft_def, analyticOverlapSwapIso_hom]
  rw [← Functor.map_comp]
  exact congrArg ((Φ.analyticAffineChartDiagram hΦ).map) (Subsingleton.elim _ _)

/-- Pointwise, the right inclusion factors through the swapped left inclusion. -/
theorem analyticOverlapRight_apply_eq_left_swapIso_hom_apply (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ)) :
    Φ.analyticOverlapRight hΦ σ τ x =
      Φ.analyticOverlapLeft hΦ τ σ ((Φ.analyticOverlapSwapIso hΦ σ τ).hom x) :=
  ConcreteCategory.congr_hom (Φ.analyticOverlapRight_eq_swap_comp_left hΦ σ τ) x

/-- The two orientations of the overlap have the same image in the second chart. -/
theorem range_analyticOverlapRight (σ τ : Φ.cones) :
    Set.range (Φ.analyticOverlapRight hΦ σ τ) =
      (Φ.analyticOverlapOpens hΦ τ σ : Set _) := by
  rw [Φ.analyticOverlapRight_eq_swap_comp_left hΦ σ τ, TopCat.coe_comp]
  have hs : Function.Surjective (Φ.analyticOverlapSwapIso hΦ σ τ).hom :=
    (TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)).surjective
  rw [hs.range_comp, Φ.coe_analyticOverlapOpens]

/-- A point of the common chart maps into the first overlap open set. -/
theorem analyticOverlapLeft_mem (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ)) :
    Φ.analyticOverlapLeft hΦ σ τ x ∈ Φ.analyticOverlapOpens hΦ σ τ :=
  ⟨x, rfl⟩

/-- A point of the common chart maps into the opposite overlap open set. -/
theorem analyticOverlapRight_mem (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ)) :
    Φ.analyticOverlapRight hΦ σ τ x ∈ Φ.analyticOverlapOpens hΦ τ σ := by
  rw [Φ.analyticOverlapRight_apply_eq_left_swapIso_hom_apply hΦ σ τ]
  exact ⟨_, rfl⟩

/-- The transition between the two open overlap loci, induced by their common chart. -/
noncomputable def analyticOverlapHomeomorph (σ τ : Φ.cones) :
    (Φ.analyticOverlapOpens hΦ σ τ) ≃ₜ
      (Φ.analyticOverlapOpens hΦ τ σ) :=
  (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph.symm |>.trans
    ((TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)).trans
      ((Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph))

/-- On a point represented by the intersection chart, the transition is the other
intersection-chart inclusion. -/
@[simp] theorem analyticOverlapHomeomorph_apply (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj (σ ⊓ τ)) :
    Φ.analyticOverlapHomeomorph hΦ σ τ
      ⟨Φ.analyticOverlapLeft hΦ σ τ x, Φ.analyticOverlapLeft_mem hΦ σ τ x⟩ =
      ⟨Φ.analyticOverlapRight hΦ σ τ x,
        Φ.analyticOverlapRight_mem hΦ σ τ x⟩ := by
  apply Subtype.ext
  let eL := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph
  let eR := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph
  let s := TopCat.homeoOfIso (Φ.analyticOverlapSwapIso hΦ σ τ)
  -- The embedding homeomorphisms land in `Set.range`, which matches the overlap subtypes
  -- only after unfolding `analyticOverlapOpens`; restate the goal in the range subtypes.
  change ((eL.symm.trans (s.trans eR))
    ⟨Φ.analyticOverlapLeft hΦ σ τ x, _⟩).1 = Φ.analyticOverlapRight hΦ σ τ x
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, IsEmbedding.toHomeomorph_symm_apply]
  exact (Φ.analyticOverlapRight_apply_eq_left_swapIso_hom_apply hΦ σ τ x).symm

/-- Reversing an overlap transition is the transition in the opposite orientation. -/
@[simp] theorem analyticOverlapHomeomorph_symm (σ τ : Φ.cones) :
    (Φ.analyticOverlapHomeomorph hΦ σ τ).symm =
      Φ.analyticOverlapHomeomorph hΦ τ σ := by
  unfold analyticOverlapHomeomorph
  rw [← Φ.analyticOverlapSwapIso_symm hΦ σ τ]
  -- Closes definitionally: `Homeomorph.symm` of a composite unfolds to the reversed composite
  -- of inverses, and `TopCat.homeoOfIso f.symm` is `(TopCat.homeoOfIso f).symm` by definition.
  rfl

/-- The two overlap inclusions of a chart with itself coincide. -/
theorem analyticOverlapRight_self (σ : Φ.cones) :
    Φ.analyticOverlapRight hΦ σ σ = Φ.analyticOverlapLeft hΦ σ σ := by
  unfold analyticOverlapRight analyticOverlapLeft
  exact congrArg ((Φ.analyticAffineChartDiagram hΦ).map) (Subsingleton.elim _ _)

/-- The transition across the self-overlap is the identity. -/
@[simp] theorem analyticOverlapHomeomorph_self (σ : Φ.cones) :
    Φ.analyticOverlapHomeomorph hΦ σ σ = Homeomorph.refl _ := by
  ext ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := (Φ.mem_analyticOverlapOpens hΦ σ σ x).1 hx
  simp [analyticOverlapRight_self]

end TauCeti.Toric.Fan

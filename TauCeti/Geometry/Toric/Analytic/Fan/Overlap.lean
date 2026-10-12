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

/-- The inclusion of the common chart into the first chart. -/
noncomputable def analyticOverlapLeft (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ) ⟶
      (Φ.analyticAffineChartDiagram).obj σ :=
  (Φ.analyticAffineChartDiagram).map
    (homOfLE inf_le_left)

/-- The left overlap inclusion is the diagram map for the meet inequality. -/
theorem analyticOverlapLeft_def (σ τ : Φ.cones) :
    Φ.analyticOverlapLeft σ τ =
      (Φ.analyticAffineChartDiagram).map (homOfLE inf_le_left) := (rfl)

/-- The inclusion of the common chart into the second chart. -/
noncomputable def analyticOverlapRight (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ) ⟶
      (Φ.analyticAffineChartDiagram).obj τ :=
  (Φ.analyticAffineChartDiagram).map
    (homOfLE inf_le_right)

/-- The right overlap inclusion is the diagram map for the meet inequality. -/
theorem analyticOverlapRight_def (σ τ : Φ.cones) :
    Φ.analyticOverlapRight σ τ =
      (Φ.analyticAffineChartDiagram).map (homOfLE inf_le_right) := (rfl)

/-- The common chart embeds openly into the first chart. -/
theorem isOpenEmbedding_analyticOverlapLeft (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    IsOpenEmbedding (Φ.analyticOverlapLeft σ τ) := by
  unfold analyticOverlapLeft
  exact Φ.isOpenEmbedding_analyticAffineChartDiagram_map hΦ _

/-- The common chart embeds openly into the second chart. -/
theorem isOpenEmbedding_analyticOverlapRight (hΦ : Φ.IsRegular) (σ τ : Φ.cones) :
    IsOpenEmbedding (Φ.analyticOverlapRight σ τ) := by
  unfold analyticOverlapRight
  exact Φ.isOpenEmbedding_analyticAffineChartDiagram_map hΦ _

/-- The open overlap locus in the first affine chart. -/
def analyticOverlapOpens (σ τ : Φ.cones) : TopologicalSpace.Opens
    ((Φ.analyticAffineChartDiagram).obj σ) :=
  ⟨Set.range (Φ.analyticOverlapLeft σ τ),
    (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isOpen_range⟩

/-- The carrier of the overlap open set is the image of the left inclusion. -/
@[simp] theorem coe_analyticOverlapOpens (σ τ : Φ.cones) :
    (Φ.analyticOverlapOpens hΦ σ τ : Set _) =
      Set.range (Φ.analyticOverlapLeft σ τ) := (rfl)

/-- Membership in the overlap means coming from a point of the intersection chart. -/
@[simp] theorem mem_analyticOverlapOpens (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj σ) :
    x ∈ Φ.analyticOverlapOpens hΦ σ τ ↔
      ∃ y, Φ.analyticOverlapLeft σ τ y = x :=
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
    (TopCat.homeoOfIso ((Φ.analyticAffineChartDiagram).mapIso
      (eqToIso (inf_idem σ)))).surjective

/-- Interchanging the two cones gives an isomorphism of their intersection charts. -/
noncomputable def analyticOverlapSwapIso (σ τ : Φ.cones) :
    (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ) ≅
      (Φ.analyticAffineChartDiagram).obj (τ ⊓ σ) :=
  (Φ.analyticAffineChartDiagram).mapIso (eqToIso (inf_comm σ τ))

/-- The forward swap is the chart diagram applied to the equality `σ ⊓ τ = τ ⊓ σ`. -/
@[simp] theorem analyticOverlapSwapIso_hom (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso σ τ).hom =
      (Φ.analyticAffineChartDiagram).map (eqToHom (inf_comm σ τ)) := (rfl)

/-- The inverse swap is the chart diagram applied to the equality `τ ⊓ σ = σ ⊓ τ`. -/
@[simp] theorem analyticOverlapSwapIso_inv (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso σ τ).inv =
      (Φ.analyticAffineChartDiagram).map (eqToHom (inf_comm σ τ).symm) := (rfl)

/-- Reversing the swap exchanges its two orientations. -/
@[simp] theorem analyticOverlapSwapIso_symm (σ τ : Φ.cones) :
    (Φ.analyticOverlapSwapIso σ τ).symm =
      Φ.analyticOverlapSwapIso τ σ := by
  apply Iso.ext
  rw [Iso.symm_hom, analyticOverlapSwapIso_inv, analyticOverlapSwapIso_hom]

/-- The right overlap inclusion is the left inclusion after interchanging the cones. -/
theorem analyticOverlapRight_eq_swap_comp_left (σ τ : Φ.cones) :
    Φ.analyticOverlapRight σ τ =
      (Φ.analyticOverlapSwapIso σ τ).hom ≫
        Φ.analyticOverlapLeft τ σ := by
  rw [analyticOverlapRight_def, analyticOverlapLeft_def, analyticOverlapSwapIso_hom]
  rw [← Functor.map_comp]
  exact congrArg ((Φ.analyticAffineChartDiagram).map) (Subsingleton.elim _ _)

/-- Pointwise, the right inclusion factors through the swapped left inclusion. -/
theorem analyticOverlapRight_apply_eq_left_swapIso_hom_apply (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ)) :
    Φ.analyticOverlapRight σ τ x =
      Φ.analyticOverlapLeft τ σ ((Φ.analyticOverlapSwapIso σ τ).hom x) :=
  ConcreteCategory.congr_hom (Φ.analyticOverlapRight_eq_swap_comp_left σ τ) x

/-- The two orientations of the overlap have the same image in the second chart. -/
theorem range_analyticOverlapRight (σ τ : Φ.cones) :
    Set.range (Φ.analyticOverlapRight σ τ) =
      (Φ.analyticOverlapOpens hΦ τ σ : Set _) := by
  rw [Φ.analyticOverlapRight_eq_swap_comp_left σ τ, TopCat.coe_comp]
  have hs : Function.Surjective (Φ.analyticOverlapSwapIso σ τ).hom :=
    (TopCat.homeoOfIso (Φ.analyticOverlapSwapIso σ τ)).surjective
  rw [hs.range_comp, Φ.coe_analyticOverlapOpens]

/-- A point of the common chart maps into the first overlap open set. -/
theorem analyticOverlapLeft_mem (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ)) :
    Φ.analyticOverlapLeft σ τ x ∈ Φ.analyticOverlapOpens hΦ σ τ :=
  ⟨x, rfl⟩

/-- A point of the common chart maps into the opposite overlap open set. -/
theorem analyticOverlapRight_mem (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ)) :
    Φ.analyticOverlapRight σ τ x ∈ Φ.analyticOverlapOpens hΦ τ σ := by
  rw [Φ.analyticOverlapRight_apply_eq_left_swapIso_hom_apply σ τ]
  exact ⟨_, rfl⟩

/-- The transition between the two open overlap loci, induced by their common chart. -/
noncomputable def analyticOverlapHomeomorph (σ τ : Φ.cones) :
    (Φ.analyticOverlapOpens hΦ σ τ) ≃ₜ
      (Φ.analyticOverlapOpens hΦ τ σ) :=
  (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph.symm |>.trans
    ((TopCat.homeoOfIso (Φ.analyticOverlapSwapIso σ τ)).trans
      ((Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph))

/-- On a point represented by the intersection chart, the transition is the other
intersection-chart inclusion. -/
@[simp] theorem analyticOverlapHomeomorph_apply (σ τ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj (σ ⊓ τ)) :
    Φ.analyticOverlapHomeomorph hΦ σ τ
      ⟨Φ.analyticOverlapLeft σ τ x, Φ.analyticOverlapLeft_mem hΦ σ τ x⟩ =
      ⟨Φ.analyticOverlapRight σ τ x,
        Φ.analyticOverlapRight_mem hΦ σ τ x⟩ := by
  apply Subtype.ext
  let eL := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ σ τ).isEmbedding.toHomeomorph
  let eR := (Φ.isOpenEmbedding_analyticOverlapLeft hΦ τ σ).isEmbedding.toHomeomorph
  let s := TopCat.homeoOfIso (Φ.analyticOverlapSwapIso σ τ)
  -- The embedding homeomorphisms land in `Set.range`, which matches the overlap subtypes
  -- only after unfolding `analyticOverlapOpens`; restate the goal in the range subtypes.
  change ((eL.symm.trans (s.trans eR))
    ⟨Φ.analyticOverlapLeft σ τ x, _⟩).1 = Φ.analyticOverlapRight σ τ x
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, IsEmbedding.toHomeomorph_symm_apply]
  exact (Φ.analyticOverlapRight_apply_eq_left_swapIso_hom_apply σ τ x).symm

/-- Reversing an overlap transition is the transition in the opposite orientation. -/
@[simp] theorem analyticOverlapHomeomorph_symm (σ τ : Φ.cones) :
    (Φ.analyticOverlapHomeomorph hΦ σ τ).symm =
      Φ.analyticOverlapHomeomorph hΦ τ σ := by
  unfold analyticOverlapHomeomorph
  rw [← Φ.analyticOverlapSwapIso_symm σ τ]
  -- Closes definitionally: `Homeomorph.symm` of a composite unfolds to the reversed composite
  -- of inverses, and `TopCat.homeoOfIso f.symm` is `(TopCat.homeoOfIso f).symm` by definition.
  rfl

/-- The two overlap inclusions of a chart with itself coincide. -/
theorem analyticOverlapRight_self (σ : Φ.cones) :
    Φ.analyticOverlapRight σ σ = Φ.analyticOverlapLeft σ σ := by
  unfold analyticOverlapRight analyticOverlapLeft
  exact congrArg ((Φ.analyticAffineChartDiagram).map) (Subsingleton.elim _ _)

/-- The transition across the self-overlap is the identity. -/
@[simp] theorem analyticOverlapHomeomorph_self (σ : Φ.cones) :
    Φ.analyticOverlapHomeomorph hΦ σ σ = Homeomorph.refl _ := by
  ext ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := (Φ.mem_analyticOverlapOpens hΦ σ σ x).1 hx
  simp [analyticOverlapRight_self]

/-- A point coming from a common face belongs to the overlap of the two charts. -/
theorem mem_analyticOverlapOpens_of_le {γ σ τ : Φ.cones} (hγσ : γ ≤ σ)
    (hγτ : γ ≤ τ) (z : (Φ.analyticAffineChartDiagram).obj γ) :
    (Φ.analyticAffineChartDiagram).map (homOfLE hγσ) z ∈
      Φ.analyticOverlapOpens hΦ σ τ := by
  let hγ : γ ≤ σ ⊓ τ := le_inf hγσ hγτ
  apply (Φ.mem_analyticOverlapOpens hΦ σ τ _).2
  refine ⟨(Φ.analyticAffineChartDiagram).map (homOfLE hγ) z, ?_⟩
  rw [Φ.analyticOverlapLeft_def, Φ.analyticChartMap_comp]
  congr 1

/-- On a point from a common face, an overlap transition is the chart map into the
second cone. -/
theorem analyticOverlapHomeomorph_apply_of_le {γ σ τ : Φ.cones} (hγσ : γ ≤ σ)
    (hγτ : γ ≤ τ) (z : (Φ.analyticAffineChartDiagram).obj γ) :
    ((Φ.analyticOverlapHomeomorph hΦ σ τ)
      ⟨(Φ.analyticAffineChartDiagram).map (homOfLE hγσ) z,
        Φ.mem_analyticOverlapOpens_of_le hΦ hγσ hγτ z⟩).1 =
        (Φ.analyticAffineChartDiagram).map (homOfLE hγτ) z := by
  let hγ : γ ≤ σ ⊓ τ := le_inf hγσ hγτ
  have he : (Φ.analyticAffineChartDiagram).map (homOfLE hγσ) z =
      Φ.analyticOverlapLeft σ τ
        ((Φ.analyticAffineChartDiagram).map (homOfLE hγ) z) := by
    rw [Φ.analyticOverlapLeft_def, Φ.analyticChartMap_comp]
    congr 1
  have he' : (⟨_, Φ.mem_analyticOverlapOpens_of_le hΦ hγσ hγτ z⟩ :
      Φ.analyticOverlapOpens hΦ σ τ) =
      ⟨Φ.analyticOverlapLeft σ τ
        ((Φ.analyticAffineChartDiagram).map (homOfLE hγ) z),
        Φ.analyticOverlapLeft_mem hΦ σ τ _⟩ := Subtype.ext he
  rw [he', Φ.analyticOverlapHomeomorph_apply hΦ]
  -- Remove the subtype coercion before rewriting the map of the right overlap.
  change Φ.analyticOverlapRight σ τ
    ((Φ.analyticAffineChartDiagram).map (homOfLE hγ) z) = _
  rw [Φ.analyticOverlapRight_def, Φ.analyticChartMap_comp]
  congr 1

end TauCeti.Toric.Fan

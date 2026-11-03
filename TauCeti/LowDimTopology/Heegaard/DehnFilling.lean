/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
public import TauCeti.LowDimTopology.DehnSurgery.Unknot
public import TauCeti.LowDimTopology.Heegaard.FundamentalGroup

/-!
# Genus-one Heegaard splittings of Dehn fillings

A Dehn filling `Y` of a knot exterior `E` glues a solid torus `V = D² × S¹` to `E` along their
boundary tori (`TauCeti.DehnFilling`). When the exterior is itself a solid torus, the two pieces
`E` and `V` are handlebodies of genus one covering `Y` and meeting in their common boundary torus,
so they form a Heegaard splitting of genus one of `Y` (`TauCeti.DehnFilling.heegaardSplitting`).
Hence every such filling has Heegaard genus at most one
(`TauCeti.DehnFilling.heegaardGenus_le_one`).

The hypothesis on the exterior is that some homeomorphism `e : E ≃ₜ D² × S¹` carries the boundary
torus of `E` into the boundary torus `∂D² × S¹`. It is used to see that every point of the common
torus is a limit of points of `E` off the torus, so that the torus is the frontier of `V` in `Y`
as well as that of `E`. The exterior of the unknot in `S³` is such a solid torus
(`TauCeti.unknotExteriorHomeomorph`, which exchanges the circle factors on the boundary torus), so
every Dehn filling of the exterior of the unknot has Heegaard genus at most one
(`TauCeti.DehnFilling.heegaardGenus_le_one_of_unknot`). Classically these fillings are `S³`,
`S¹ × S²` and the lens spaces.

For the `0`-surgery on the unknot, `S¹ × S²` (`TauCeti.unknotZeroDehnFilling`), the splitting
consists of the solid tori `S¹ × D²₊` and `S¹ × D²₋` over the two closed hemispheres of `S²`. The
fundamental group of `S¹ × S²` is nontrivial, being the product of those of `S¹` and `S²`
(`TauCeti.FundamentalGroup.prodMulEquiv`), and its rank is at most the Heegaard genus
(`TauCeti.rank_fundamentalGroup_le_heegaardGenus`). So `S¹ × S²` has Heegaard genus exactly one
(`TauCeti.heegaardGenus_circle_prod_sphere`), equal to the rank of its fundamental group, as in
Waldhausen's rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`).

## Main definitions

* `TauCeti.DehnFilling.heegaardSplitting`: the genus-one Heegaard splitting of a Dehn filling of a
  knot exterior which is a solid torus, into the exterior and the filling solid torus.

## Main results

* `TauCeti.DehnFilling.heegaardGenus_le_one`: such a filling has Heegaard genus at most one.
* `TauCeti.DehnFilling.heegaardGenus_le_one_of_unknot`: every Dehn filling of the exterior of the
  unknot has Heegaard genus at most one.
* `TauCeti.heegaardGenus_circle_prod_sphere`: `S¹ × S²` has Heegaard genus one.
* `TauCeti.heegaardGenus_circle_prod_sphere_eq_rank`: the Heegaard genus of `S¹ × S²` is the rank
  of its fundamental group.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Chapter 9 (Dehn surgery on the unknot
  glues two solid tori, giving `S³`, `S¹ × S²` and the lens spaces).
* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Chapter 2 (Heegaard splittings; the closed `3`-manifolds of Heegaard genus at most one).
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti

namespace DehnFilling

variable {X : Type} [TopologicalSpace X] [T2Space X] {f : Circle → X} {Φ : SolidTorus → X}
  {h : IsSolidTorusNeighborhood f Φ} {s : Slope h.framedBoundaryTorus.H}
  {Y : Type*} [TopologicalSpace Y]

/-- Every point of the boundary torus of the filling solid torus is a limit of points of the
filling solid torus outside the exterior: the images of the points `‖w‖ < 1`. -/
private theorem inter_subset_closure_compl_range_exteriorEmbedding (F : DehnFilling h s Y) :
    range F.exteriorEmbedding ∩ range F.solidTorusEmbedding ⊆
      closure (range F.exteriorEmbedding)ᶜ := by
  rw [F.range_inter_range]
  rintro _ ⟨q, rfl⟩
  have hsub : F.solidTorusEmbedding '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} ⊆
      (range F.exteriorEmbedding)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ ⟨x, hx⟩
    obtain ⟨q', rfl, -⟩ := exteriorEmbedding_eq_solidTorusEmbedding_iff.1 hx
    simp at hp
  refine closure_mono hsub (image_closure_subset_closure_image
    F.isClosedEmbedding_solidTorusEmbedding.continuous ⟨_, ?_, rfl⟩)
  rw [SolidTorus.closure_setOf_norm_lt_one]
  exact mem_univ _

/-- If the exterior is a solid torus through a homeomorphism `e` carrying its boundary torus into
`∂D² × S¹`, every point of the boundary torus of the exterior is a limit of points of the exterior
outside the filling solid torus: the images under `e⁻¹` of the points `‖w‖ < 1`. -/
private theorem inter_subset_closure_compl_range_solidTorusEmbedding (F : DehnFilling h s Y)
    (e : knotExterior (Φ := Φ) ≃ₜ SolidTorus)
    (he : ∀ q, e (h.exteriorBoundaryInclusion q) ∈ range SolidTorus.boundaryInclusion) :
    range F.exteriorEmbedding ∩ range F.solidTorusEmbedding ⊆
      closure (range F.solidTorusEmbedding)ᶜ := by
  rw [F.range_inter_range]
  rintro _ ⟨q, rfl⟩
  have hsub : (F.exteriorEmbedding ∘ e.symm) '' {p : SolidTorus | ‖(p.1 : ℂ)‖ < 1} ⊆
      (range F.solidTorusEmbedding)ᶜ := by
    rintro _ ⟨p, hp, rfl⟩ ⟨p', hp'⟩
    obtain ⟨q', -, hq'⟩ := exteriorEmbedding_eq_solidTorusEmbedding_iff.1 hp'.symm
    have hmem := he (F.gluing q')
    rw [← hq', e.apply_symm_apply, SolidTorus.range_boundaryInclusion] at hmem
    exact (ne_of_lt hp) hmem
  have hq : F.solidTorusEmbedding (SolidTorus.boundaryInclusion q) =
      (F.exteriorEmbedding ∘ e.symm) (e (h.exteriorBoundaryInclusion (F.gluing q))) := by
    rw [Function.comp_apply, e.symm_apply_apply, F.exteriorEmbedding_exteriorBoundaryInclusion]
  rw [Function.comp_apply, hq]
  refine closure_mono hsub (image_closure_subset_closure_image
    (F.isClosedEmbedding_exteriorEmbedding.continuous.comp e.symm.continuous) ⟨_, ?_, rfl⟩)
  rw [SolidTorus.closure_setOf_norm_lt_one]
  exact mem_univ _

/-- **A Dehn filling of a solid torus is a genus-one Heegaard splitting.** If the knot exterior is
a solid torus, through a homeomorphism `e` carrying its boundary torus into the boundary torus
`∂D² × S¹`, then the exterior and the filling solid torus of a Dehn filling form a Heegaard
splitting of genus one of the filled space. -/
def heegaardSplitting (F : DehnFilling h s Y) (e : knotExterior (Φ := Φ) ≃ₜ SolidTorus)
    (he : ∀ q, e (h.exteriorBoundaryInclusion q) ∈ range SolidTorus.boundaryInclusion) :
    HeegaardSplitting Y :=
  HeegaardSplitting.ofIsClosed 1 F.isClosedEmbedding_exteriorEmbedding.isClosed_range
    F.isClosedEmbedding_solidTorusEmbedding.isClosed_range F.range_union_range
    F.inter_subset_closure_compl_range_exteriorEmbedding
    (F.inter_subset_closure_compl_range_solidTorusEmbedding e he)
    (nonempty_homeomorph_handlebody_one.map fun e₁ ↦
      (F.isClosedEmbedding_exteriorEmbedding.isEmbedding.toHomeomorph.symm.trans e).trans e₁.symm)
    (nonempty_homeomorph_handlebody_one.map fun e₁ ↦
      F.isClosedEmbedding_solidTorusEmbedding.isEmbedding.toHomeomorph.symm.trans e₁.symm)

variable (F : DehnFilling h s Y) (e : knotExterior (Φ := Φ) ≃ₜ SolidTorus)
  (he : ∀ q, e (h.exteriorBoundaryInclusion q) ∈ range SolidTorus.boundaryInclusion)

@[simp]
theorem heegaardSplitting_genus : (F.heegaardSplitting e he).genus = 1 := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsClosed_genus]

@[simp]
theorem heegaardSplitting_left : (F.heegaardSplitting e he).left = range F.exteriorEmbedding := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsClosed_left]

@[simp]
theorem heegaardSplitting_right :
    (F.heegaardSplitting e he).right = range F.solidTorusEmbedding := by
  rw [heegaardSplitting, HeegaardSplitting.ofIsClosed_right]

/-- A Dehn filling of a knot exterior which is a solid torus, with its boundary torus carried
into `∂D² × S¹`, has Heegaard genus at most one. -/
theorem heegaardGenus_le_one (F : DehnFilling h s Y) (e : knotExterior (Φ := Φ) ≃ₜ SolidTorus)
    (he : ∀ q, e (h.exteriorBoundaryInclusion q) ∈ range SolidTorus.boundaryInclusion)
    [Nonempty (HeegaardSplitting Y)] : heegaardGenus Y ≤ 1 :=
  (heegaardGenus_le (F.heegaardSplitting e he)).trans_eq (F.heegaardSplitting_genus e he)

/-- **Every Dehn filling of the exterior of the unknot has Heegaard genus at most one.** The
exterior of the standard solid torus neighbourhood of the unknot is the complementary solid torus
of `S³`, so it and the filling solid torus form a genus-one Heegaard splitting. -/
theorem heegaardGenus_le_one_of_unknot
    {s : Slope isSolidTorusNeighborhood_unknotSolidTorus.framedBoundaryTorus.H}
    (F : DehnFilling isSolidTorusNeighborhood_unknotSolidTorus s Y)
    [Nonempty (HeegaardSplitting Y)] : heegaardGenus Y ≤ 1 :=
  F.heegaardGenus_le_one unknotExteriorHomeomorph fun q ↦
    ⟨q.swap, (unknotExteriorHomeomorph_exteriorBoundaryInclusion q).symm⟩

end DehnFilling

/-! ### `S¹ × S²` -/

section CircleProdSphere

/-- `S¹ × S²` has a Heegaard splitting: the genus-one splitting into the solid tori `S¹ × D²₊` and
`S¹ × D²₋` of the `0`-surgery on the unknot. -/
instance : Nonempty (HeegaardSplitting (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨unknotZeroDehnFilling.heegaardSplitting unknotExteriorHomeomorph fun q ↦
    ⟨q.swap, (unknotExteriorHomeomorph_exteriorBoundaryInclusion q).symm⟩⟩

/-- The product atlas of `S¹ × S²`, read on the normed space `ℝ¹ × ℝ²` of dimension three, as
`TauCeti.rank_fundamentalGroup_le_heegaardGenus` asks for a model with a norm. Mathlib's product
atlas is valued in `ModelProd`, a type synonym for the product of the models. This is not an
instance, so that `S¹ × S²` keeps its single canonical atlas. -/
private abbrev circleProdSphereChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2))
      (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  prodChartedSpace _ _ _ _

/-- The fundamental group of `S¹ × S²` is finitely generated. -/
instance fg_fundamentalGroup_circle_prod_sphere
    (x : Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Group.FG (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) :=
  letI := circleProdSphereChartedSpace
  (Classical.arbitrary (HeegaardSplitting _)).fg_fundamentalGroup
    (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) (by simp) x

/-- The rank of the fundamental group of `S¹ × S²` is at most its Heegaard genus. -/
private theorem rank_fundamentalGroup_le_heegaardGenus_circle_prod_sphere
    (x : Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Group.rank (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) ≤
      heegaardGenus (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  letI := circleProdSphereChartedSpace
  rank_fundamentalGroup_le_heegaardGenus
    (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) (by simp) x

/-- The fundamental group of `S¹ × S²` has rank one: it is nontrivial, being the product of those
of `S¹` and `S²`, and its rank is at most the Heegaard genus, which is at most one. -/
theorem rank_fundamentalGroup_circle_prod_sphere
    (x : Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Group.rank (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) = 1 := by
  have := Circle.nontrivial_fundamentalGroup x.1
  have : Nontrivial (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) :=
    (FundamentalGroup.prodMulEquiv x.1 x.2).toEquiv.nontrivial
  have h0 : Group.rank (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) ≠
      0 := by
    rw [Ne, Group.rank_eq_zero_iff]
    exact not_subsingleton _
  have := rank_fundamentalGroup_le_heegaardGenus_circle_prod_sphere x
  have := unknotZeroDehnFilling.heegaardGenus_le_one_of_unknot
  omega

/-- **`S¹ × S²` has Heegaard genus one.** It has the genus-one splitting of the `0`-surgery on the
unknot, and none of genus zero, since its fundamental group has rank one while its rank is at most
the Heegaard genus. -/
theorem heegaardGenus_circle_prod_sphere :
    heegaardGenus (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) = 1 := by
  let x : Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    (1, ⟨EuclideanSpace.single 0 1, by simp⟩)
  exact le_antisymm unknotZeroDehnFilling.heegaardGenus_le_one_of_unknot
    ((rank_fundamentalGroup_circle_prod_sphere x).ge.trans
      (rank_fundamentalGroup_le_heegaardGenus_circle_prod_sphere x))

/-- **`S¹ × S²` satisfies Waldhausen's equation**: its Heegaard genus equals the rank of its
fundamental group, both being one. -/
theorem heegaardGenus_circle_prod_sphere_eq_rank
    (x : Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    heegaardGenus (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Group.rank (FundamentalGroup (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) x) := by
  rw [heegaardGenus_circle_prod_sphere, rank_fundamentalGroup_circle_prod_sphere]

end CircleProdSphere

end TauCeti

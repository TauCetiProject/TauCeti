/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData

/-!
# Maps and isomorphisms of open gluing data

Let `D` and `D'` be open gluing data, `a : D.J → D'.J` a map of indices, and `φ i` continuous
maps from the pieces of `D` to the pieces of `D'` indexed by `a`. If the maps agree on the
overlaps, that is, send points identified in `D` to points identified in `D'`, they glue to a
continuous map `TopCat.GlueData.gluedMap a φ hφ` of the existing glued spaces, through the
universal property of the multicoequalizer. Gluing piece maps is functorial (`gluedMap_id`,
`gluedMap_comp`).

If the piece maps are open and reflect identifications, the glued map is an open embedding
(`TopCat.GlueData.isOpenEmbedding_gluedMap`). In particular, an *isomorphism of gluing data*,
a surjective map of indices with homeomorphisms of the pieces under which two points are
identified in `D'` exactly when their preimages are identified in `D`, induces a homeomorphism
`TopCat.GlueData.gluedHomeomorph` of the glued spaces. The index map need not be injective:
repeated pieces are identified by the gluing relation.

Such an isomorphism matches the data entering the criteria of
`TauCeti.Topology.Category.TopCat.GlueData` for the glued space:

* the relations between corresponding charts correspond, so one is closed exactly when the
  other is (`TopCat.GlueData.isClosed_chartRel_iff_of_homeomorph`); this is the input of the
  Hausdorff criterion `TopCat.GlueData.t2Space_iff_isClosed_chartRel`;
* corresponding overlaps are nonempty together (`TopCat.GlueData.nonempty_V_iff_of_surjective`),
  so the overlap graphs controlling connectedness correspond;
* the glued spaces are homeomorphic, so separation, second countability, connectedness and
  properness of maps into or out of them, which are Mathlib's typeclasses and predicates,
  transfer along `gluedHomeomorph`.

## References

* N. Bourbaki, *General Topology*, Chapter I, §3 and §8.3 (quotient spaces and Hausdorff
  quotients).
* The glued carrier and its universal property are Mathlib's `TopCat.GlueData.glued` and
  `CategoryTheory.Limits.Multicoequalizer.desc`.
-/

public section

open CategoryTheory Limits Set Topology

namespace TopCat.GlueData

universe u

variable {D D' D'' : TopCat.GlueData.{u}}

/-- Maps of pieces which agree on every overlap send points identified in `D` to points
identified in `D'`. -/
theorem ι_apply_eq_ι_apply_of_ι_eq {a : D.J → D'.J} (f : ∀ i, D.U i → D'.U (a i))
    (hf : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (f i (D.f i j x)) =
      D'.toGlueData.ι (a j) (f j (D.f j i (D.t i j x))))
    {i j : D.J} {x : D.U i} {y : D.U j} (h : D.toGlueData.ι i x = D.toGlueData.ι j y) :
    D'.toGlueData.ι (a i) (f i x) = D'.toGlueData.ι (a j) (f j y) := by
  obtain ⟨z, rfl, rfl⟩ : ∃ z : D.V (i, j), D.f i j z = x ∧ D.f j i (D.t i j z) = y :=
    (D.ι_eq_iff_rel i j x y).1 h
  exact hf i j z

/-- Continuous maps of pieces which agree on every overlap glue to a continuous map of the glued
spaces. The index map need not be injective or surjective. -/
noncomputable def gluedMap (a : D.J → D'.J) (φ : ∀ i, C(D.U i, D'.U (a i)))
    (hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
      D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x)))) :
    D.toGlueData.glued ⟶ D'.toGlueData.glued :=
  Multicoequalizer.desc _ _ (fun i ↦ TopCat.ofHom (φ i) ≫ D'.toGlueData.ι (a i))
    (by rintro ⟨i, j⟩; ext x; exact hφ i j x)

section gluedMap

variable {a : D.J → D'.J} {φ : ∀ i, C(D.U i, D'.U (a i))}
  {hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
    D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x)))}

/-- The glued map is the prescribed piece map on each piece. -/
@[simp]
theorem gluedMap_ι (i : D.J) (x : D.U i) :
    gluedMap a φ hφ (D.toGlueData.ι i x) = D'.toGlueData.ι (a i) (φ i x) :=
  ConcreteCategory.congr_hom
    (Multicoequalizer.π_desc D.toGlueData.diagram _
      (fun i ↦ TopCat.ofHom (φ i) ≫ D'.toGlueData.ι (a i)) _ i) x

/-- A continuous map of glued spaces is determined by its values on all pieces. -/
theorem hom_ext_ι {X : TopCat.{u}} {g g' : D.toGlueData.glued ⟶ X}
    (h : ∀ i (x : D.U i), g (D.toGlueData.ι i x) = g' (D.toGlueData.ι i x)) : g = g' := by
  ext x
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact h i y

/-- The glued map is the only map of glued spaces that is the piece map on each piece. -/
theorem eq_gluedMap_iff (g : D.toGlueData.glued ⟶ D'.toGlueData.glued) :
    g = gluedMap a φ hφ ↔
      ∀ i (x : D.U i), g (D.toGlueData.ι i x) = D'.toGlueData.ι (a i) (φ i x) :=
  ⟨fun h i x ↦ h ▸ gluedMap_ι i x, fun h ↦ hom_ext_ι fun i x ↦ (h i x).trans (gluedMap_ι i x).symm⟩

variable (a φ hφ) in
/-- The range of the glued map is the union of the images of the piece maps. -/
theorem range_gluedMap :
    range (gluedMap a φ hφ) = ⋃ i, D'.toGlueData.ι (a i) '' range (φ i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
    exact mem_iUnion.2 ⟨i, φ i x, mem_range_self x, (gluedMap_ι i x).symm⟩
  · intro hy
    obtain ⟨i, _, ⟨x, rfl⟩, rfl⟩ := mem_iUnion.1 hy
    exact ⟨D.toGlueData.ι i x, gluedMap_ι i x⟩

/-- Piece maps that reflect identifications glue to an injective map. -/
theorem injective_gluedMap
    (h : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (φ i x) =
      D'.toGlueData.ι (a j) (φ j y) → D.toGlueData.ι i x = D.toGlueData.ι j y) :
    Function.Injective (gluedMap a φ hφ) := by
  intro x y hxy
  obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
  obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective y
  rw [gluedMap_ι, gluedMap_ι] at hxy
  exact h i j x y hxy

/-- Open piece maps glue to an open map. -/
theorem isOpenMap_gluedMap (h : ∀ i, IsOpenMap (φ i)) : IsOpenMap (gluedMap a φ hφ) := by
  -- Test openness after the open quotient map from the disjoint union of the pieces.
  refine IsOpenMap.of_comp (f := fun x : Σ i, D.U i ↦ D.toGlueData.ι x.1 x.2)
    D.isOpenQuotientMap_sigma_ι.continuous D.isOpenQuotientMap_sigma_ι.surjective ?_
  refine isOpenMap_sigma.2 fun i ↦ ?_
  simpa only [Function.comp_def, gluedMap_ι] using
    (D'.ι_isOpenEmbedding (a i)).isOpenMap.comp (h i)

/-- Open piece maps which reflect identifications glue to an open embedding. This generalizes the
inclusion `TopCat.GlueData.reindexMap` of a subfamily, whose piece maps are identities. -/
theorem isOpenEmbedding_gluedMap (hopen : ∀ i, IsOpenMap (φ i))
    (h : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (φ i x) =
      D'.toGlueData.ι (a j) (φ j y) → D.toGlueData.ι i x = D.toGlueData.ι j y) :
    IsOpenEmbedding (gluedMap a φ hφ) :=
  .of_continuous_injective_isOpenMap (gluedMap a φ hφ).hom.continuous (injective_gluedMap h)
    (isOpenMap_gluedMap hopen)

/-- Surjective piece maps over a surjective index map glue to a surjective map. -/
theorem surjective_gluedMap (ha : Function.Surjective a) (h : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (gluedMap a φ hφ) := by
  intro y
  obtain ⟨k, z, rfl⟩ := D'.ι_jointly_surjective y
  obtain ⟨i, rfl⟩ := ha k
  obtain ⟨x, rfl⟩ := h i z
  exact ⟨D.toGlueData.ι i x, gluedMap_ι i x⟩

end gluedMap

/-- Identity piece maps glue to the identity of the glued space. -/
@[simp]
theorem gluedMap_id (x : D.toGlueData.glued) :
    gluedMap id (fun i ↦ ContinuousMap.id (D.U i))
      (fun i j x ↦ (D.glue_condition_apply i j x).symm) x = x := by
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact gluedMap_ι i y

/-- Gluing composite piece maps gives the composite of the glued maps. -/
@[simp]
theorem gluedMap_comp {a : D.J → D'.J} (φ : ∀ i, C(D.U i, D'.U (a i)))
    (hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
      D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x))))
    {b : D'.J → D''.J} (ψ : ∀ j, C(D'.U j, D''.U (b j)))
    (hψ : ∀ i j (x : D'.V (i, j)), D''.toGlueData.ι (b i) (ψ i (D'.f i j x)) =
      D''.toGlueData.ι (b j) (ψ j (D'.f j i (D'.t i j x))))
    (x : D.toGlueData.glued) :
    gluedMap b ψ hψ (gluedMap a φ hφ x) =
      gluedMap (b ∘ a) (fun i ↦ (ψ (a i)).comp (φ i))
        (fun i j x ↦ ι_apply_eq_ι_apply_of_ι_eq (fun j ↦ ψ j) hψ (hφ i j x)) x := by
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  simp only [gluedMap_ι, ContinuousMap.comp_apply, Function.comp_apply]

/-! ### Isomorphisms of gluing data -/

section Criteria

variable {a : D.J → D'.J} (f : ∀ i, D.U i → D'.U (a i))
  (hf : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (f i x) =
    D'.toGlueData.ι (a j) (f j y) ↔ D.toGlueData.ι i x = D.toGlueData.ι j y)

include hf in
/-- Piece maps which preserve and reflect identifications identify the relation between two
charts with the preimage of the relation between the corresponding charts. -/
theorem chartRel_eq_preimage_prodMap (i j : D.J) :
    D.chartRel i j = Prod.map (f i) (f j) ⁻¹' D'.chartRel (a i) (a j) := by
  ext ⟨x, y⟩
  simp [hf]

include hf in
/-- Under surjective piece maps which preserve and reflect identifications, an overlap is
nonempty exactly when the corresponding overlap is. Thus the overlap graphs, which control
connectedness of the glued spaces (`TopCat.GlueData.connectedSpace_iff_reflTransGen`),
correspond. -/
theorem nonempty_V_iff_of_surjective (hsurj : ∀ i, Function.Surjective (f i)) (i j : D.J) :
    Nonempty (D'.V (a i, a j)) ↔ Nonempty (D.V (i, j)) := by
  simp only [← range_ι_inter_range_ι_nonempty_iff]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, y, hy⟩
    obtain ⟨x, rfl⟩ := hsurj i x
    obtain ⟨y, rfl⟩ := hsurj j y
    exact ⟨_, mem_range_self x, y, ((hf i j x y).1 hy.symm).symm⟩
  · rintro ⟨_, ⟨x, rfl⟩, y, hy⟩
    exact ⟨_, mem_range_self (f i x), f j y, ((hf i j x y).2 hy.symm).symm⟩

end Criteria

section Homeomorph

variable {σ : D.J → D'.J} (φ : ∀ i, D.U i ≃ₜ D'.U (σ i))
  (hφ : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (σ i) (φ i x) =
    D'.toGlueData.ι (σ j) (φ j y) ↔ D.toGlueData.ι i x = D.toGlueData.ι j y)

include hφ in
/-- Under an isomorphism of gluing data, the relation between two charts is closed exactly when
the relation between the corresponding charts is. These relations decide whether the glued space
is Hausdorff (`TopCat.GlueData.t2Space_iff_isClosed_chartRel`). -/
theorem isClosed_chartRel_iff_of_homeomorph (i j : D.J) :
    IsClosed (D'.chartRel (σ i) (σ j)) ↔ IsClosed (D.chartRel i j) := by
  rw [chartRel_eq_preimage_prodMap (fun i ↦ φ i) hφ, ← Homeomorph.coe_prodCongr,
    Homeomorph.isClosed_preimage]

/-- An isomorphism of gluing data, given by a surjective map of indices and homeomorphisms of the
pieces which preserve and reflect identifications, induces a homeomorphism of the glued spaces. -/
noncomputable def gluedHomeomorph (hσ : Function.Surjective σ) :
    D.toGlueData.glued ≃ₜ D'.toGlueData.glued :=
  (isOpenEmbedding_gluedMap (φ := fun i ↦ (φ i : C(D.U i, D'.U (σ i))))
    (hφ := fun i j x ↦ (hφ _ _ _ _).2 (D.glue_condition_apply i j x).symm)
    (fun i ↦ (φ i).isOpenMap) fun i j x y ↦ (hφ i j x y).1).isEmbedding.toHomeomorphOfSurjective
    (surjective_gluedMap hσ fun i ↦ (φ i).surjective)

/-- The homeomorphism induced by an isomorphism of gluing data is the glued map. -/
theorem coe_gluedHomeomorph (hσ : Function.Surjective σ) :
    ⇑(gluedHomeomorph φ hφ hσ) = gluedMap σ (fun i ↦ (φ i : C(D.U i, D'.U (σ i))))
      (fun i j x ↦ (hφ _ _ _ _).2 (D.glue_condition_apply i j x).symm) :=
  (rfl)

/-- The homeomorphism induced by an isomorphism of gluing data is the given homeomorphism on each
piece. -/
@[simp]
theorem gluedHomeomorph_ι (hσ : Function.Surjective σ) (i : D.J) (x : D.U i) :
    gluedHomeomorph φ hφ hσ (D.toGlueData.ι i x) = D'.toGlueData.ι (σ i) (φ i x) := by
  simp [coe_gluedHomeomorph]

/-- The inverse of the homeomorphism induced by an isomorphism of gluing data is the inverse of
the given homeomorphism on each piece. -/
@[simp]
theorem gluedHomeomorph_symm_ι (hσ : Function.Surjective σ) (i : D.J) (y : D'.U (σ i)) :
    (gluedHomeomorph φ hφ hσ).symm (D'.toGlueData.ι (σ i) y) =
      D.toGlueData.ι i ((φ i).symm y) := by
  rw [Homeomorph.symm_apply_eq, gluedHomeomorph_ι, Homeomorph.apply_symm_apply]

end Homeomorph

end TopCat.GlueData

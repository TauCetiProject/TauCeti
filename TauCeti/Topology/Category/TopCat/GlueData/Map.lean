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

The glued map is injective, open, an open embedding, or surjective exactly when the piece maps
reflect identifications, are open, are both, or have images covering the target
(`TopCat.GlueData.gluedMap_injective_iff`, `TopCat.GlueData.isOpenMap_gluedMap_iff`,
`TopCat.GlueData.isOpenEmbedding_gluedMap_iff`, `TopCat.GlueData.gluedMap_surjective_iff`).
In particular, an *isomorphism of gluing data*, a map of indices whose pieces cover the target
with homeomorphisms of the pieces under which two points are identified in `D'` exactly when
their preimages are identified in `D`, induces a homeomorphism
`TopCat.GlueData.gluedHomeomorph` of the glued spaces. The index map need be neither injective
nor surjective: repeated pieces are identified by the gluing relation, and pieces covered by
the others may be omitted.

Piece maps which preserve and reflect identifications match the data entering the criteria of
`TauCeti.Topology.Category.TopCat.GlueData` for the glued space:

* the relations between corresponding charts correspond, so for homeomorphisms of the pieces one
  is closed exactly when the other is (`TopCat.GlueData.isClosed_chartRel_iff_of_homeomorph`);
  this is the input of the Hausdorff criterion `TopCat.GlueData.t2Space_iff_isClosed_chartRel`;
* for surjective piece maps, corresponding overlaps are nonempty together
  (`TopCat.GlueData.nonempty_V_iff_of_surjective`), and for a surjective index map, chains of
  nonempty overlaps starting at a nonempty piece correspond
  (`TopCat.GlueData.reflTransGen_nonempty_V_iff_of_surjective`); these chains are the input of
  the connectedness criterion `TopCat.GlueData.connectedSpace_iff_reflTransGen`;
* under an isomorphism of gluing data the glued spaces are homeomorphic, so separation, second
  countability, connectedness and properness of maps into or out of them, which are Mathlib's
  typeclasses and predicates, transfer along `gluedHomeomorph`.

## References

* N. Bourbaki, *General Topology*, Chapter I, §3 and §8.3 (quotient spaces and Hausdorff
  quotients).
* The glued carrier and its universal property are Mathlib's `CategoryTheory.GlueData.glued`
  and `CategoryTheory.Limits.Multicoequalizer.desc`.
-/

public section

open CategoryTheory Limits Set Topology

namespace TopCat.GlueData

universe u v

variable {D : TopCat.GlueData.{u}}

/-- Functions on the pieces which agree on every overlap agree on all points identified in the
glued space. -/
theorem apply_eq_apply_of_ι_eq {α : Sort*} (g : ∀ i, D.U i → α)
    (hg : ∀ i j (x : D.V (i, j)), g i (D.f i j x) = g j (D.f j i (D.t i j x)))
    {i j : D.J} {x : D.U i} {y : D.U j} (h : D.toGlueData.ι i x = D.toGlueData.ι j y) :
    g i x = g j y := by
  obtain ⟨z, rfl, rfl⟩ : ∃ z : D.V (i, j), D.f i j z = x ∧ D.f j i (D.t i j z) = y :=
    (D.ι_eq_iff_rel i j x y).1 h
  exact hg i j z

/-- A continuous map out of a glued space is determined by its values on all pieces. -/
theorem hom_ext_ι {X : TopCat.{u}} {g g' : D.toGlueData.glued ⟶ X}
    (h : ∀ i (x : D.U i), g (D.toGlueData.ι i x) = g' (D.toGlueData.ι i x)) : g = g' := by
  ext x
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact h i y

section gluedMap

variable {D' D'' : TopCat.GlueData.{u}}

/-- Continuous maps of pieces which agree on every overlap glue to a continuous map of the glued
spaces. The index map need not be injective or surjective. -/
noncomputable def gluedMap (a : D.J → D'.J) (φ : ∀ i, C(D.U i, D'.U (a i)))
    (hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
      D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x)))) :
    D.toGlueData.glued ⟶ D'.toGlueData.glued :=
  Multicoequalizer.desc _ _ (fun i ↦ TopCat.ofHom (φ i) ≫ D'.toGlueData.ι (a i))
    (by rintro ⟨i, j⟩; ext x; exact hφ i j x)

variable {a : D.J → D'.J} {φ : ∀ i, C(D.U i, D'.U (a i))}
  {hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
    D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x)))}

/-- The glued map restricts on each piece to the prescribed piece map. -/
@[reassoc (attr := simp)]
theorem ι_gluedMap (i : D.J) :
    D.toGlueData.ι i ≫ gluedMap a φ hφ = TopCat.ofHom (φ i) ≫ D'.toGlueData.ι (a i) :=
  Multicoequalizer.π_desc D.toGlueData.diagram _
    (fun i ↦ TopCat.ofHom (φ i) ≫ D'.toGlueData.ι (a i)) _ i

/-- The glued map is the prescribed piece map on each piece. -/
@[simp]
theorem gluedMap_ι (i : D.J) (x : D.U i) :
    gluedMap a φ hφ (D.toGlueData.ι i x) = D'.toGlueData.ι (a i) (φ i x) :=
  ConcreteCategory.congr_hom (ι_gluedMap i) x

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

/-- The glued map is injective exactly when the piece maps reflect identifications. -/
theorem gluedMap_injective_iff :
    Function.Injective (gluedMap a φ hφ) ↔
      ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (φ i x) =
        D'.toGlueData.ι (a j) (φ j y) → D.toGlueData.ι i x = D.toGlueData.ι j y := by
  refine ⟨fun hinj i j x y hxy ↦ hinj ?_, fun h x y hxy ↦ ?_⟩
  · rw [gluedMap_ι, gluedMap_ι, hxy]
  · obtain ⟨i, x, rfl⟩ := D.ι_jointly_surjective x
    obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective y
    rw [gluedMap_ι, gluedMap_ι] at hxy
    exact h i j x y hxy

/-- The glued map is open exactly when all piece maps are open. -/
theorem isOpenMap_gluedMap_iff : IsOpenMap (gluedMap a φ hφ) ↔ ∀ i, IsOpenMap (φ i) := by
  refine ⟨fun h i ↦ (D'.ι_isOpenEmbedding (a i)).isOpenMap_iff.2 ?_, fun h ↦ ?_⟩
  · have : D'.toGlueData.ι (a i) ∘ φ i = gluedMap a φ hφ ∘ D.toGlueData.ι i :=
      funext fun x ↦ (gluedMap_ι i x).symm
    rw [this]
    exact h.comp (D.ι_isOpenEmbedding i).isOpenMap
  -- Test openness after the open quotient map from the disjoint union of the pieces.
  refine IsOpenMap.of_comp (f := fun x : Σ i, D.U i ↦ D.toGlueData.ι x.1 x.2)
    D.isOpenQuotientMap_sigma_ι.continuous D.isOpenQuotientMap_sigma_ι.surjective ?_
  refine isOpenMap_sigma.2 fun i ↦ ?_
  simpa only [Function.comp_def, gluedMap_ι] using
    (D'.ι_isOpenEmbedding (a i)).isOpenMap.comp (h i)

/-- The glued map is an open embedding exactly when the piece maps are open and reflect
identifications. -/
theorem isOpenEmbedding_gluedMap_iff :
    IsOpenEmbedding (gluedMap a φ hφ) ↔ (∀ i, IsOpenMap (φ i)) ∧
      ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (φ i x) =
        D'.toGlueData.ι (a j) (φ j y) → D.toGlueData.ι i x = D.toGlueData.ι j y := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap, gluedMap_injective_iff,
    isOpenMap_gluedMap_iff]
  exact ⟨fun h ↦ ⟨h.2.2, h.2.1⟩, fun h ↦ ⟨(gluedMap a φ hφ).hom.continuous, h.2, h.1⟩⟩

/-- The glued map is surjective exactly when the images of the piece maps cover the target. -/
theorem gluedMap_surjective_iff :
    Function.Surjective (gluedMap a φ hφ) ↔ ⋃ i, D'.toGlueData.ι (a i) '' range (φ i) = univ := by
  rw [← range_gluedMap, range_eq_univ]

/-- Surjective piece maps over a surjective index map glue to a surjective map. -/
theorem gluedMap_surjective (ha : Function.Surjective a) (h : ∀ i, Function.Surjective (φ i)) :
    Function.Surjective (gluedMap a φ hφ) := by
  refine gluedMap_surjective_iff.2 ?_
  simp only [(h _).range_eq, image_univ]
  exact (ha.iUnion_comp fun k ↦ range (D'.toGlueData.ι k)).trans D'.iUnion_range_ι

end gluedMap

/-- Identity piece maps glue to the identity of the glued space. -/
@[simp]
theorem gluedMap_id :
    gluedMap id (fun i ↦ ContinuousMap.id (D.U i))
      (fun i j x ↦ (D.glue_condition_apply i j x).symm) = 𝟙 D.toGlueData.glued :=
  hom_ext_ι fun i x ↦ (gluedMap_ι i x).trans (by simp)

/-- Gluing composite piece maps gives the composite of the glued maps. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
theorem gluedMap_comp {D' D'' : TopCat.GlueData.{u}} {a : D.J → D'.J}
    (φ : ∀ i, C(D.U i, D'.U (a i)))
    (hφ : ∀ i j (x : D.V (i, j)), D'.toGlueData.ι (a i) (φ i (D.f i j x)) =
      D'.toGlueData.ι (a j) (φ j (D.f j i (D.t i j x))))
    {b : D'.J → D''.J} (ψ : ∀ j, C(D'.U j, D''.U (b j)))
    (hψ : ∀ i j (x : D'.V (i, j)), D''.toGlueData.ι (b i) (ψ i (D'.f i j x)) =
      D''.toGlueData.ι (b j) (ψ j (D'.f j i (D'.t i j x)))) :
    gluedMap a φ hφ ≫ gluedMap b ψ hψ =
      gluedMap (b ∘ a) (fun i ↦ (ψ (a i)).comp (φ i))
        (fun i j x ↦ apply_eq_apply_of_ι_eq (fun k y ↦ D''.toGlueData.ι (b k) (ψ k y)) hψ
          (hφ i j x)) :=
  hom_ext_ι fun i x ↦ by simp

/-! ### Isomorphisms of gluing data -/

section Criteria

variable {D' : TopCat.GlueData.{v}} {a : D.J → D'.J} (f : ∀ i, D.U i → D'.U (a i))
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
nonempty exactly when the corresponding overlap is. -/
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

include hf in
/-- Under a surjective index map and surjective piece maps which preserve and reflect
identifications, an index with a nonempty piece is joined to another by a chain of nonempty
overlaps exactly when the corresponding indices are. Such chains decide connectedness of the
glued spaces (`TopCat.GlueData.connectedSpace_iff_reflTransGen`). -/
theorem reflTransGen_nonempty_V_iff_of_surjective (ha : Function.Surjective a)
    (hsurj : ∀ i, Function.Surjective (f i)) {i : D.J} (hi : Nonempty (D.U i)) (j : D.J) :
    Relation.ReflTransGen (fun k l ↦ Nonempty (D'.V (k, l))) (a i) (a j) ↔
      Relation.ReflTransGen (fun k l ↦ Nonempty (D.V (k, l))) i j := by
  refine ⟨fun h ↦ ?_, Relation.ReflTransGen.lift a
    (fun k l ↦ (nonempty_V_iff_of_surjective f hf hsurj k l).2) i j⟩
  -- Lift the chain step by step, choosing a preimage of each index along the way.
  suffices ∀ k, Relation.ReflTransGen (fun k l ↦ Nonempty (D'.V (k, l))) (a i) k →
      ∀ l, a l = k → Relation.ReflTransGen (fun k l ↦ Nonempty (D.V (k, l))) i l from
    this _ h j rfl
  intro k hk
  induction hk with
  | refl =>
    -- An index over the same piece as `i` meets it in the nonempty piece itself.
    intro l hl
    refine .single ((nonempty_V_iff_of_surjective f hf hsurj i l).1 ?_)
    rw [hl, ← range_ι_inter_range_ι_nonempty_iff, inter_self]
    exact ⟨_, mem_range_self (f i hi.some)⟩
  | @tail k _ _ hkl ih =>
    intro l hl
    obtain ⟨k, rfl⟩ := ha k
    exact (ih k rfl).tail ((nonempty_V_iff_of_surjective f hf hsurj k l).1 (hl ▸ hkl))

/-- Under homeomorphisms of the pieces which preserve and reflect identifications, the relation
between two charts is closed exactly when the relation between the corresponding charts is. These
relations decide whether the glued space is Hausdorff
(`TopCat.GlueData.t2Space_iff_isClosed_chartRel`). -/
theorem isClosed_chartRel_iff_of_homeomorph (φ : ∀ i, D.U i ≃ₜ D'.U (a i))
    (hφ : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (a i) (φ i x) =
      D'.toGlueData.ι (a j) (φ j y) ↔ D.toGlueData.ι i x = D.toGlueData.ι j y) (i j : D.J) :
    IsClosed (D'.chartRel (a i) (a j)) ↔ IsClosed (D.chartRel i j) := by
  rw [chartRel_eq_preimage_prodMap (fun i ↦ φ i) hφ, ← Homeomorph.coe_prodCongr,
    Homeomorph.isClosed_preimage]

end Criteria

section Homeomorph

variable {D' : TopCat.GlueData.{u}} {σ : D.J → D'.J} (φ : ∀ i, D.U i ≃ₜ D'.U (σ i))
  (hφ : ∀ i j (x : D.U i) (y : D.U j), D'.toGlueData.ι (σ i) (φ i x) =
    D'.toGlueData.ι (σ j) (φ j y) ↔ D.toGlueData.ι i x = D.toGlueData.ι j y)
  (hcover : ⋃ i, range (D'.toGlueData.ι (σ i)) = univ)

/-- An isomorphism of gluing data, given by a map of indices whose pieces cover the target and
homeomorphisms of the pieces which preserve and reflect identifications, induces a homeomorphism
of the glued spaces. -/
noncomputable def gluedHomeomorph : D.toGlueData.glued ≃ₜ D'.toGlueData.glued :=
  ((isOpenEmbedding_gluedMap_iff (φ := fun i ↦ (φ i : C(D.U i, D'.U (σ i))))
    (hφ := fun i j x ↦ (hφ _ _ _ _).2 (D.glue_condition_apply i j x).symm)).2
    ⟨fun i ↦ (φ i).isOpenMap, fun i j x y ↦ (hφ i j x y).1⟩).isEmbedding.toHomeomorphOfSurjective
    (gluedMap_surjective_iff.2 (by simpa using hcover))

/-- The homeomorphism induced by an isomorphism of gluing data is the glued map. -/
theorem coe_gluedHomeomorph :
    ⇑(gluedHomeomorph φ hφ hcover) = gluedMap σ (fun i ↦ (φ i : C(D.U i, D'.U (σ i))))
      (fun i j x ↦ (hφ _ _ _ _).2 (D.glue_condition_apply i j x).symm) :=
  funext fun x ↦ IsEmbedding.toHomeomorphOfSurjective_apply _ _ x

/-- The homeomorphism induced by an isomorphism of gluing data is the given homeomorphism on each
piece. -/
@[simp]
theorem gluedHomeomorph_ι (i : D.J) (x : D.U i) :
    gluedHomeomorph φ hφ hcover (D.toGlueData.ι i x) = D'.toGlueData.ι (σ i) (φ i x) := by
  simp [coe_gluedHomeomorph]

/-- The inverse of the homeomorphism induced by an isomorphism of gluing data is the inverse of
the given homeomorphism on each piece. -/
@[simp]
theorem gluedHomeomorph_symm_ι (i : D.J) (y : D'.U (σ i)) :
    (gluedHomeomorph φ hφ hcover).symm (D'.toGlueData.ι (σ i) y) =
      D.toGlueData.ι i ((φ i).symm y) := by
  rw [Homeomorph.symm_apply_eq, gluedHomeomorph_ι, Homeomorph.apply_symm_apply]

end Homeomorph

end TopCat.GlueData

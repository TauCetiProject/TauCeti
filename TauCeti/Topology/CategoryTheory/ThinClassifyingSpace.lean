/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThinRealization.Skeleton
public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict

/-!
# The thin classifying space of a topological category

For a category `C` whose total arrow type `Quiver.Total C` carries a topology, its *thin classifying
space* `TauCeti.thinClassifyingSpace C` is the full (thin) geometric realization
`TauCeti.thinRealization (TauCeti.topologicalNerve C)`, quotienting by both face and degeneracy
operators while retaining all isotropy arrows in `topologicalNerve C`.

Because `CategoryTheory.ComposableArrows` inherits `T₃` separation and second countability from
`Quiver.Total C` (`TauCeti.Topology.CategoryTheory.ComposableArrows`) and `TauCeti.thinRealization`
is `T₄`, paracompact, Lindelöf, and compactly generated whenever its levels are `T₃` and Lindelöf
(`TauCeti.AlgebraicTopology.ThinRealization.Skeleton`), typeclass search automatically synthesizes
`T4Space (thinClassifyingSpace C)`, `ParacompactSpace (thinClassifyingSpace C)`,
`LindelofSpace (thinClassifyingSpace C)`, and `UCompactlyGeneratedSpace (thinClassifyingSpace C)`
whenever `[T3Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)]`—in particular for
every Lie groupoid or topological groupoid whose total arrow space is second-countable and `T₃`. For
`σ`-compact or compact Hausdorff topological categories without second countability, combining
`CategoryTheory.ComposableArrows.sigmaCompactSpace` with `TauCeti.thinRealization.instT4Space`
supplies the same separation and paracompactness properties.

This module also provides:
* the natural quotient comparison map `TauCeti.fatToThinClassifyingSpace : fatClassifyingSpace C ⟶
  thinClassifyingSpace C` (`isQuotientMap_fatToThinClassifyingSpace`);
* functorial maps `TauCeti.thinClassifyingSpaceMap` and homotopies
  `TauCeti.thinClassifyingSpaceHomotopy` for continuous families of functors;
* the coarse projection `TauCeti.thinClassifyingSpace.coarseMap` of a topological groupoid,
  compatible with `fatClassifyingSpace.coarseMap` and proved to be a quotient map when units are
  continuous (`TauCeti.thinClassifyingSpace.isQuotientMap_coarseMap`);
* open and closed embeddings and coarse-preimage homeomorphisms for saturated open and closed full
  subgroupoids (`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`,
  `CategoryTheory.ObjectProperty.thinClassifyingSpaceClosedRestrictionHomeomorph`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology
open scoped Simplicial

namespace TauCeti

universe w v u

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The thin classifying space of a category whose total arrows carry a topology: the full geometric
realization of its topological nerve, quotienting by both faces and degeneracies. -/
@[expose]
def thinClassifyingSpace : TopCat.{max u v} :=
  thinRealization (topologicalNerve C)

instance thinClassifyingSpace.instLindelofSpace
    [∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌)] :
    LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (thinRealization (topologicalNerve C)))

instance thinClassifyingSpace.instUCompactlyGeneratedSpace
    [∀ n : ℕ, UCompactlyGeneratedSpace.{w}
      ((topologicalNerve C) _⦋n⦌ × SimplexCategory.toTop.{max u v}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{w} (thinRealization (topologicalNerve C)))

instance thinClassifyingSpace.instT4Space
    [∀ n : ℕ, T3Space ((topologicalNerve C) _⦋n⦌)]
    [∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌)] :
    T4Space (thinClassifyingSpace C) :=
  inferInstanceAs (T4Space (thinRealization (topologicalNerve C)))

/-- The canonical quotient comparison map from the fat classifying space to the thin classifying
space, collapsing degenerate simplices. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  thinRealization.fatToThin (topologicalNerve C)

/-- `fatToThinClassifyingSpace C` is a topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpace : IsQuotientMap (fatToThinClassifyingSpace C) :=
  thinRealization.isQuotientMap_fatToThin (topologicalNerve C)

variable {C}

/-- Two morphisms out of `thinClassifyingSpace C` agree once they agree on every simplex. -/
@[ext]
theorem thinClassifyingSpace.hom_ext {Z : TopCat.{max u v}} {g h : thinClassifyingSpace C ⟶ Z}
    (H : ∀ (n : SimplexCategory) (F : ComposableArrows C n.len)
      (t : SimplexCategory.toTop.obj n),
        g (thinRealization.ι (topologicalNerve C) n (F, t)) =
          h (thinRealization.ι (topologicalNerve C) n (F, t))) : g = h :=
  thinRealization.hom_ext (topologicalNerve C) H

@[simp↓]
theorem fatToThinClassifyingSpace_ι (m : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.obj m) :
    fatToThinClassifyingSpace C (fatRealization.ι _ m (F, t)) =
      thinRealization.ι (topologicalNerve C)
        (SemiSimplexCategory.toSimplexCategory.obj m) (F, t) :=
  thinRealization.fatToThin_ι (topologicalNerve C) m F t

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The map of thin classifying spaces induced by a functor continuous on total arrows. -/
def thinClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpace C ⟶ thinClassifyingSpace D :=
  thinRealization.map (topologicalNerveMap Φ hΦ)

theorem thinClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap Φ hΦ = thinRealization.map (topologicalNerveMap Φ hΦ) :=
  (rfl)

/-- `thinClassifyingSpaceMap` acts on characteristic maps by applying `Φ` to strings of composable
arrows. -/
theorem thinClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : SimplexCategory) (F : ComposableArrows C n.len) (t : SimplexCategory.toTop.obj n) :
    thinClassifyingSpaceMap Φ hΦ (thinRealization.ι (topologicalNerve C) n (F, t)) =
      thinRealization.ι (topologicalNerve D) n ((Φ.mapComposableArrows n.len).obj F, t) :=
  (thinRealization.map_ι (topologicalNerveMap Φ hΦ) n F t).trans
    (by rw [topologicalNerveMap_app_apply])

/-- Two functors that agree on strings of composable arrows induce the same map of thin classifying
spaces. -/
theorem thinClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    thinClassifyingSpaceMap Φ hΦ = thinClassifyingSpaceMap Ψ hΨ :=
  thinClassifyingSpace.hom_ext fun n F t ↦ (thinClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun F ↦ thinRealization.ι (topologicalNerve D) n (F, t)) (h n.len F)).trans
      (thinClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
@[simp]
theorem thinClassifyingSpaceMap_id :
    thinClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (thinClassifyingSpace C) :=
  (congrArg thinRealization.map (topologicalNerveMap_id C)).trans thinRealization.map_id

theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (congrArg thinRealization.map (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans
    (thinRealization.map_comp _ _)

/-- Naturality of `fatToThinClassifyingSpace` with respect to continuous functors. -/
theorem fatToThinClassifyingSpace_naturality (Φ : C ⥤ D)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ =
      fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D := by
  rw [fatToThinClassifyingSpace, fatToThinClassifyingSpace, thinClassifyingSpaceMap_eq,
    fatClassifyingSpaceMap_eq]
  exact (thinRealization.fatToThin_naturality (topologicalNerveMap Φ hΦ)).symm

/-- A family of functors `Φ s`, `s ∈ [0, 1]`, depending continuously on `s` and the total arrow,
induces a homotopy `(s, [F, t]) ↦ [Φ s ∘ F, t]` between the induced maps on thin classifying
spaces. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  thinRealization.homotopy
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun _ ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ).congr
      fun p ↦ (topologicalNerveMap_app_apply _ _ _ p.2).symm

theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : SimplexCategory) (F : ComposableArrows C n.len)
    (t : SimplexCategory.toTop.obj n) :
    thinClassifyingSpaceHomotopy Φ hΦ (s, thinRealization.ι (topologicalNerve C) n (F, t)) =
      thinRealization.ι (topologicalNerve D) n (((Φ s).mapComposableArrows n.len).obj F, t) :=
  (thinRealization.homotopy_apply_ι
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans
    (by rw [topologicalNerveMap_app_apply])

namespace thinClassifyingSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The simplicial coarse augmentation of `topologicalNerve C` sending a string of composable
arrows to the isomorphism class of its initial vertex. -/
def coarseAugmentation :
    topologicalNerve C ⟶ (Functor.const _).obj (TopCat.of (Quotient (isIsomorphicSetoid C))) where
  app _ := TopCat.ofHom ⟨fun F ↦ Quotient.mk _ (F.obj 0),
    continuous_quot_mk.comp (ComposableArrows.continuous_obj hs 0)⟩
  naturality _ _ f := by
    ext F
    exact F.quotient_mk_obj
      ((SimplexCategory.toCat.map f.unop).toFunctor.obj (0 : Fin (_ + 1)))

@[simp↓]
theorem coarseAugmentation_app_apply (Δ : SimplexCategoryᵒᵖ) (F : (topologicalNerve C).obj Δ) :
    (coarseAugmentation hs).app Δ F = Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (rfl)

/-- The coarse projection from the thin classifying space of a groupoid to its orbit space of
isomorphism classes. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  thinRealization.augment (coarseAugmentation hs)

theorem coarseMap_eq_augment :
    coarseMap hs = thinRealization.augment (coarseAugmentation hs) :=
  (rfl)

@[simp↓]
theorem coarseMap_ι (n : SimplexCategory) (F : ComposableArrows C n.len)
    (t : SimplexCategory.toTop.obj n) :
    coarseMap hs (thinRealization.ι (topologicalNerve C) n (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (thinRealization.augment_ι (coarseAugmentation hs) n F t).trans
    (coarseAugmentation_app_apply hs (op n) F)

/-- The fat coarse projection factors through `fatToThinClassifyingSpace` and the thin coarse
projection. -/
theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs :=
  fatClassifyingSpace.hom_ext fun m F t ↦
    (congrArg (coarseMap hs) (fatToThinClassifyingSpace_ι m F t)).trans <|
      (coarseMap_ι hs _ F t).trans (fatClassifyingSpace.coarseMap_ι hs m F t).symm

/-- Every orbit occurs in the image of the thin coarse projection. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) := by
  have heq : ⇑(coarseMap hs) ∘ ⇑(fatToThinClassifyingSpace C) =
      ⇑(fatClassifyingSpace.coarseMap hs) :=
    funext fun z ↦ ConcreteCategory.congr_hom (fatToThinClassifyingSpace_comp_coarseMap hs) z
  exact Function.Surjective.of_comp (heq.symm ▸ fatClassifyingSpace.coarseMap_surjective hs)

/-- With continuous units, the coarse projection from `thinClassifyingSpace C` to the orbit space
is a quotient map. -/
theorem isQuotientMap_coarseMap
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) := by
  have heq : ⇑(coarseMap hs) ∘ ⇑(fatToThinClassifyingSpace C) =
      ⇑(fatClassifyingSpace.coarseMap hs) :=
    funext fun z ↦ ConcreteCategory.congr_hom (fatToThinClassifyingSpace_comp_coarseMap hs) z
  exact IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous
    (coarseMap hs).hom.continuous (heq.symm ▸ fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

universe u

variable {C : Type u} [Category.{u} C] [IsGroupoid C]
  [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- In every simplicial degree, the nerve of a saturated full subgroupoid is the preimage under the
coarse augmentation of the corresponding subset of isomorphism classes. -/
theorem range_topologicalNerveMap_ι_simplex (Δ : SimplexCategoryᵒᵖ) :
    range ((TauCeti.topologicalNerveMap P.ι P.continuous_mapTotal_ι).app Δ) =
      (TauCeti.thinClassifyingSpace.coarseAugmentation hs).app Δ ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) := by
  rw [TauCeti.coe_topologicalNerveMap_app]
  refine (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms _).trans ?_
  ext F
  constructor
  · intro hF
    exact ⟨F.obj 0, hF,
      (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs Δ F).symm⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨e⟩ := Quotient.exact
      (h.trans (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs Δ F))
    exact P.prop_of_iso e hx

include hs in
/-- The inclusion of a saturated open full subgroupoid induces an open embedding on thin
classifying spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpaceMap_eq]
  refine TauCeti.thinRealization.isOpenEmbedding_map_of_range_eq_preimage
    (TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
    (fun Δ ↦ ?_) (P.range_topologicalNerveMap_ι_simplex hs)
  rw [TauCeti.coe_topologicalNerveMap_app]
  exact P.isOpenEmbedding_mapComposableArrows_ι hs hP Δ.unop.len

include hs in
/-- The inclusion of a saturated closed full subgroupoid induces a closed embedding on thin
classifying spaces. -/
theorem isClosedEmbedding_thinClassifyingSpaceMap_ι (hP : IsClosed {x | P x}) :
    IsClosedEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpaceMap_eq]
  refine TauCeti.thinRealization.isClosedEmbedding_map_of_range_eq_preimage
    (TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
    (fun Δ ↦ ?_) (P.range_topologicalNerveMap_ι_simplex hs)
  rw [TauCeti.coe_topologicalNerveMap_app]
  exact P.isClosedEmbedding_mapComposableArrows_ι hs hP Δ.unop.len

/-- The preimage of a saturated coarse subset under `thinClassifyingSpace.coarseMap` is the image
of the thin classifying space of its full restriction. -/
theorem preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι :
    TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpace.coarseMap_eq_augment, TauCeti.thinClassifyingSpaceMap_eq]
  exact TauCeti.thinRealization.preimage_augment_eq_range_map _ _
    (P.range_topologicalNerveMap_ι_simplex hs)

/-- The thin classifying space of a saturated open restriction is homeomorphic to the corresponding
coarse-map preimage, with its subspace topology. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

@[simp↓]
theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z :=
  (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).apply_symm_apply z)

/-- The thin classifying space of a saturated closed restriction is homeomorphic to the
corresponding coarse-map preimage, with its subspace topology. -/
def thinClassifyingSpaceClosedRestrictionHomeomorph (hP : IsClosed {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

@[simp↓]
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val (hP : IsClosed {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z :=
  (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceClosedRestrictionHomeomorph_symm_apply
    (hP : IsClosed {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val
    ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).apply_symm_apply z)

end CategoryTheory.ObjectProperty

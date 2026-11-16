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

For a category `C` with a topology on `Quiver.Total C`, its *thin classifying space*
`TauCeti.thinClassifyingSpace C` is `TauCeti.thinRealization (TauCeti.topologicalNerve C)`,
quotienting by both face and degeneracy operators while retaining all isotropy arrows.

Because `CategoryTheory.ComposableArrows` inherits `T₃` separation and second countability from
`Quiver.Total C`, `TauCeti.thinRealization` is `T₄`, paracompact, and Lindelöf for `T₃` Lindelöf
levels, and compactly generated whenever its cells `Xₙ × Δⁿ` are compactly generated (here via
first countability from second countability), typeclass search synthesizes `T4Space`,
`ParacompactSpace`, `LindelofSpace`, and `UCompactlyGeneratedSpace` on `thinClassifyingSpace C`
from `[T3Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)]`. For `σ`-compact
topological categories with `[T3Space (Quiver.Total C)] [T2Space C]` (or compact Hausdorff ones),
`ComposableArrows.sigmaCompactSpace` with `thinRealization.instT4Space` and `instLindelofSpace`
likewise gives `T₄`, Lindelöf, and paracompactness.

We also define the quotient comparison map `fatToThinClassifyingSpace`, functoriality
(`thinClassifyingSpaceMap`, `thinClassifyingSpaceHomotopy`), the groupoid coarse projection
`thinClassifyingSpace.coarseMap` (`isQuotientMap_coarseMap`), open/closed embeddings, and the
coarse-preimage restriction homeomorphism
(`ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), §4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology
open SimplexCategory (toTop)
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
  inferInstanceAs (LindelofSpace (thinRealization _))

instance thinClassifyingSpace.instUCompactlyGeneratedSpace
    [∀ n : ℕ, UCompactlyGeneratedSpace.{w} ((topologicalNerve C) _⦋n⦌ × toTop.{max u v}.obj ⦋n⦌)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{w} (thinRealization _))

instance thinClassifyingSpace.instT4Space [∀ n : ℕ, T3Space ((topologicalNerve C) _⦋n⦌)]
    [∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌)] :
    T4Space (thinClassifyingSpace C) :=
  inferInstanceAs (T4Space (thinRealization _))

/-- The canonical quotient comparison map from the fat to the thin classifying space. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  thinRealization.fatToThin (topologicalNerve C)

/-- `fatToThinClassifyingSpace C` is a topological quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpace : IsQuotientMap (fatToThinClassifyingSpace C) :=
  thinRealization.isQuotientMap_fatToThin (topologicalNerve C)

variable {C}

/-- Two morphisms out of `thinClassifyingSpace C` agree once they agree on every simplex. -/
@[ext]
theorem thinClassifyingSpace.hom_ext {Z : TopCat.{max u v}} {g h : thinClassifyingSpace C ⟶ Z}
    (H : ∀ (n : SimplexCategory) (F : ComposableArrows C n.len) (t : toTop.obj n),
      g (functorTensor.ι toTop (topologicalNerve C) n (F, t)) =
        h (functorTensor.ι toTop (topologicalNerve C) n (F, t))) : g = h :=
  functorTensor.hom_ext H

/-- `fatToThinClassifyingSpace` sends each fat characteristic simplex to the thin one. -/
-- Simplify before the functor-object types in the characteristic map are normalized.
@[simp↓]
theorem fatToThinClassifyingSpace_ι (m : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.obj m) :
    fatToThinClassifyingSpace C (functorTensor.ι SemiSimplexCategory.toTop _ m (F, t)) =
      functorTensor.ι toTop (topologicalNerve C) (SemiSimplexCategory.toSimplexCategory.obj m)
        (F, t) :=
  thinRealization.fatToThin_ι (topologicalNerve C) m F t

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The map of thin classifying spaces induced by a functor continuous on total arrows. -/
def thinClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpace C ⟶ thinClassifyingSpace D :=
  functorTensor.map toTop (topologicalNerveMap Φ hΦ)

/-- `thinClassifyingSpaceMap` is the `functorTensor.map` of `topologicalNerveMap`. -/
theorem thinClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap Φ hΦ = functorTensor.map toTop (topologicalNerveMap Φ hΦ) := (rfl)

/-- `thinClassifyingSpaceMap` acts on characteristic maps by applying `Φ` to composable arrows. -/
theorem thinClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : SimplexCategory) (F : ComposableArrows C n.len) (t : toTop.obj n) :
    thinClassifyingSpaceMap Φ hΦ (functorTensor.ι toTop (topologicalNerve C) n (F, t)) =
      functorTensor.ι toTop (topologicalNerve D) n ((Φ.mapComposableArrows n.len).obj F, t) :=
  (functorTensor.map_ι toTop (topologicalNerveMap Φ hΦ) n F t).trans
    (by rw [topologicalNerveMap_app_apply])

/-- Functors agreeing on strings of composable arrows induce the same classifying-space map. -/
theorem thinClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    thinClassifyingSpaceMap Φ hΦ = thinClassifyingSpaceMap Ψ hΨ :=
  thinClassifyingSpace.hom_ext fun n F t ↦ (thinClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun F ↦ functorTensor.ι toTop (topologicalNerve D) n (F, t)) (h n.len F)).trans
      (thinClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
/-- The identity functor induces the identity map on thin classifying spaces. -/
@[simp]
theorem thinClassifyingSpaceMap_id :
    thinClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (thinClassifyingSpace C) :=
  (congrArg (functorTensor.map toTop) (topologicalNerveMap_id C)).trans
    (functorTensor.map_id toTop _)

/-- Composition of continuous functors induces composition of maps on thin classifying spaces. -/
theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (congrArg (functorTensor.map toTop) (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans
    (functorTensor.map_comp toTop _ _)

/-- Naturality of `fatToThinClassifyingSpace` with respect to continuous functors. -/
theorem fatToThinClassifyingSpace_naturality (Φ : C ⥤ D)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ =
      fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D := by
  rw [fatClassifyingSpaceMap_eq]
  exact (thinRealization.fatToThin_naturality (topologicalNerveMap Φ hΦ)).symm

/-- A jointly continuous `[0, 1]`-family of functors `Φ s` induces a homotopy
`(s, [F, t]) ↦ [Φ s ∘ F, t]` between the induced maps on thin classifying spaces. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  functorTensor.homotopy toTop (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun _ ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ).congr
      fun p ↦ (topologicalNerveMap_app_apply _ _ _ p.2).symm

/-- Evaluation of `thinClassifyingSpaceHomotopy` on a characteristic simplex `(F, t)`. -/
theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : SimplexCategory) (F : ComposableArrows C n.len) (t : toTop.obj n) :
    thinClassifyingSpaceHomotopy Φ hΦ (s, functorTensor.ι toTop (topologicalNerve C) n (F, t)) =
      functorTensor.ι toTop (topologicalNerve D) n (((Φ s).mapComposableArrows n.len).obj F, t) :=
  (functorTensor.homotopy_apply_ι toTop
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans
    (by rw [topologicalNerveMap_app_apply])

namespace thinClassifyingSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The coarse projection from the thin classifying space of a groupoid to its orbit space. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  functorTensor.augment toTop (topologicalNerve.coarseAugmentation hs)

/-- `coarseMap` is induced by `topologicalNerve.coarseAugmentation`. -/
theorem coarseMap_eq_augment :
    coarseMap hs = functorTensor.augment toTop (topologicalNerve.coarseAugmentation hs) := (rfl)

/-- A point of a simplex projects to the isomorphism class of its initial vertex. -/
-- Simplify before the functor-object types in the characteristic map are normalized.
@[simp↓]
theorem coarseMap_ι (n : SimplexCategory) (F : ComposableArrows C n.len) (t : toTop.obj n) :
    coarseMap hs (functorTensor.ι toTop (topologicalNerve C) n (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (functorTensor.augment_ι toTop (topologicalNerve.coarseAugmentation hs) n F t).trans
    (topologicalNerve.coarseAugmentation_app_apply hs (op n) F)

/-- The fat coarse projection factors through `fatToThinClassifyingSpace` and `coarseMap`. -/
theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs := by
  rw [fatClassifyingSpace.coarseMap_eq_augment]
  exact thinRealization.fatToThin_comp_augment (topologicalNerve.coarseAugmentation hs)

/-- Underlying-function form of `fatToThinClassifyingSpace_comp_coarseMap`. -/
theorem coarseMap_comp_fatToThinClassifyingSpace :
    ⇑(coarseMap hs) ∘ ⇑(fatToThinClassifyingSpace C) = ⇑(fatClassifyingSpace.coarseMap hs) :=
  funext fun z ↦ ConcreteCategory.congr_hom (fatToThinClassifyingSpace_comp_coarseMap hs) z

/-- Every orbit occurs in the image of the thin coarse projection. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) :=
  Function.Surjective.of_comp ((coarseMap_comp_fatToThinClassifyingSpace hs).symm ▸
    fatClassifyingSpace.coarseMap_surjective hs)

/-- With continuous units, `coarseMap` is a topological quotient map. -/
theorem isQuotientMap_coarseMap (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) :=
  IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous (coarseMap hs).hom.continuous
    ((coarseMap_comp_fatToThinClassifyingSpace hs).symm ▸
      fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

open TauCeti

universe u

variable {C : Type u} [Category.{u} C] [IsGroupoid C]
  [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

include hs in
/-- The inclusion of a saturated open full subgroupoid induces an open embedding on thin
classifying spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  functorTensor.isOpenEmbedding_map_of_range_eq_preimage (topologicalNerve.coarseAugmentation hs)
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
    (fun Δ ↦ coe_topologicalNerveMap_app P.ι P.continuous_mapTotal_ι Δ ▸
      P.isOpenEmbedding_mapComposableArrows_ι hs hP Δ.unop.len)
    (P.range_topologicalNerveMap_ι hs)

include hs in
/-- The inclusion of a saturated closed full subgroupoid induces a closed embedding on thin
classifying spaces. -/
theorem isClosedEmbedding_thinClassifyingSpaceMap_ι (hP : IsClosed {x | P x}) :
    IsClosedEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  functorTensor.isClosedEmbedding_map_of_range_eq_preimage (topologicalNerve.coarseAugmentation hs)
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
    (fun Δ ↦ coe_topologicalNerveMap_app P.ι P.continuous_mapTotal_ι Δ ▸
      P.isClosedEmbedding_mapComposableArrows_ι hs hP Δ.unop.len)
    (P.range_topologicalNerveMap_ι hs)

/-- The preimage of a saturated coarse subset under `thinClassifyingSpace.coarseMap` is the image
of the thin classifying space of its full restriction. -/
theorem preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι :
    thinClassifyingSpace.coarseMap hs ⁻¹' (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  functorTensor.preimage_augment_eq_range_map _ (P.range_topologicalNerveMap_ι hs)

/-- Whenever the inclusion of a saturated full subgroupoid induces a topological embedding on thin
classifying spaces (for instance via `isOpenEmbedding_thinClassifyingSpaceMap_ι` or
`isClosedEmbedding_thinClassifyingSpaceMap_ι`), its thin classifying space is homeomorphic to the
corresponding coarse-map preimage with its subspace topology. -/
def thinClassifyingSpaceRestrictionHomeomorph
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι)) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹' (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  h.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

/-- Coercing `thinClassifyingSpaceRestrictionHomeomorph` to the ambient thin classifying space gives
`thinClassifyingSpaceMap P.ι`. -/
-- Rewrite before simplification normalizes the dependent TopCat carriers.
@[simp↓]
theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs h z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

/-- Applying `thinClassifyingSpaceMap P.ι` after the inverse of
`thinClassifyingSpaceRestrictionHomeomorph` recovers the ambient point. -/
-- The classifying-space map also has dependent TopCat carriers.
@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace.coarseMap hs ⁻¹' (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs h).symm z) = z.val :=
  congrArg Subtype.val ((P.thinClassifyingSpaceRestrictionHomeomorph hs h).apply_symm_apply z)

end CategoryTheory.ObjectProperty

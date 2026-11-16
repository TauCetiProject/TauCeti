/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThinRealization.Skeleton
public import TauCeti.Topology.CategoryTheory.CoarseSpace
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
public import TauCeti.Topology.CategoryTheory.Nerve.FullSubcategory

import Mathlib.Topology.Algebra.Group.Pointwise
import TauCeti.Topology.CategoryTheory.Latching

/-!
# The thin classifying space of a topological category or groupoid

Let `C` be a category whose total set of arrows `Quiver.Total C` carries a topology. Its *thin
classifying space* `TauCeti.thinClassifyingSpace C` is the thin geometric realization
`TauCeti.thinRealization (TauCeti.topologicalNerve C)`, collapsing both face and degeneracy
identifications of the topological nerve. Unlike `TauCeti.fatClassifyingSpace C`, it identifies
degenerate simplices along unit arrows; the canonical quotient comparison
`TauCeti.fatToThinClassifyingSpace C : fatClassifyingSpace C ⟶ thinClassifyingSpace C` relates
the two models naturally in continuous functors and commutes with their coarse projections.

For a groupoid `C` with continuous source, the coarse projection
`TauCeti.thinClassifyingSpace.coarseMap` descends from the nerve augmentation to the orbit space
`Quotient (isIsomorphicSetoid C)` and is a quotient map when units are continuous
(`TauCeti.thinClassifyingSpace.isQuotientMap_coarseMap`). For any isomorphism-invariant object
property `P` that is open or closed, the inclusion `P.FullSubcategory ⥤ C` induces an open or
closed embedding on thin classifying spaces whose image is precisely the coarse-map preimage of
the image of `P`
(`CategoryTheory.ObjectProperty.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι`),
identifying the preimage homeomorphically with `thinClassifyingSpace P.FullSubcategory`
(`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`,
`CategoryTheory.ObjectProperty.thinClassifyingSpaceClosedRestrictionHomeomorph`). The functorial,
coarse-projection, and restriction API parallels `TauCeti.fatClassifyingSpace`
(`TauCeti.Topology.CategoryTheory.Nerve`, `CoarseSpace`, and `CoarseSpace.Restrict`).

On the point-set side, `thinClassifyingSpace C` is compactly generated whenever `Quiver.Total C`
is first-countable (`TauCeti.thinClassifyingSpace.uCompactlyGeneratedSpace`) and Lindelöf whenever
`Quiver.Total C` is second-countable (`TauCeti.thinClassifyingSpace.lindelofSpace`), with no
closedness hypothesis on units. When the unit locus is closed in `Quiver.Total C` — which holds
both for Hausdorff topological categories with continuous source and units
(`TauCeti.isClosed_range_unit`, feeding `TauCeti.isClosedEmbedding_topologicalNerve_σ`), including
proper étale groupoids, and for one-object categories `SingleObj G` over `T1` monoids
(`TauCeti.thinClassifyingSpace.isClosed_range_unit_singleObj`) — every skeleton embeds as a closed
subspace, every compact subset lies in a finite skeleton, and if `Quiver.Total C` is `T3` and
second-countable then `thinClassifyingSpace C` is `T4` (normal and Hausdorff) and paracompact in
its raw weak realization topology. The `SingleObj G` specializations cover torus and Lie-group bar
spaces without any étaleness assumption.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

universe w v u

namespace TauCeti

section Basic

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The thin classifying space of a category whose total arrows carry a topology: the thin
geometric realization of its topological nerve. -/
@[expose] def thinClassifyingSpace : TopCat.{max u v} :=
  thinRealization (topologicalNerve C)

variable {C}

/-- Two maps out of the thin classifying space agree once they agree on every simplex. -/
@[ext]
theorem thinClassifyingSpace.hom_ext {Z : TopCat.{max u v}} {g h : thinClassifyingSpace C ⟶ Z}
    (H : ∀ (n : SimplexCategory) (F : ComposableArrows C n.len)
      (t : SimplexCategory.toTop.obj n),
        g (thinRealization.ι _ n (F, t)) = h (thinRealization.ι _ n (F, t))) : g = h :=
  thinRealization.hom_ext _ H

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The map of thin classifying spaces induced by a functor that is continuous on total arrows: the
thin realization of the induced map of topological nerves. -/
def thinClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpace C ⟶ thinClassifyingSpace D :=
  thinRealization.map (topologicalNerveMap Φ hΦ)

/-- The map of thin classifying spaces induced by a functor is the thin realization of the induced
map of topological nerves. -/
theorem thinClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap Φ hΦ = thinRealization.map (topologicalNerveMap Φ hΦ) :=
  (rfl)

/-- The map of thin classifying spaces induced by a functor applies the functor to the string of
composable arrows of each simplex. -/
theorem thinClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : SimplexCategory) (F : ComposableArrows C n.len)
    (t : SimplexCategory.toTop.obj n) :
    thinClassifyingSpaceMap Φ hΦ (thinRealization.ι _ n (F, t)) =
      thinRealization.ι _ n ((Φ.mapComposableArrows _).obj F, t) :=
  (thinRealization.map_ι (topologicalNerveMap Φ hΦ) n F t).trans <|
    congrArg (fun F ↦ thinRealization.ι _ n (F, t)) (topologicalNerveMap_app_apply Φ hΦ (op n) F)

/-- Two functors that agree on strings of composable arrows induce the same map of thin
classifying spaces. -/
theorem thinClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    thinClassifyingSpaceMap Φ hΦ = thinClassifyingSpaceMap Ψ hΨ :=
  thinClassifyingSpace.hom_ext fun n F t ↦ (thinClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun F ↦ thinRealization.ι _ n (F, t)) (h _ F)).trans
      (thinClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
@[simp]
theorem thinClassifyingSpaceMap_id :
    thinClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (thinClassifyingSpace C) :=
  (thinClassifyingSpaceMap_eq _ _).trans <|
    (congrArg thinRealization.map (topologicalNerveMap_id C)).trans thinRealization.map_id

theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (thinClassifyingSpaceMap_eq _ _).trans <|
    (congrArg thinRealization.map (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans <|
      (thinRealization.map_comp _ _).trans (rfl)

/-- A family of functors `Φ s`, `s ∈ [0, 1]`, depending continuously on `s` and the total arrow,
induces the homotopy `(s, [F, t]) ↦ [Φ s ∘ F, t]` from the map of thin classifying spaces induced
by `Φ 0` to that induced by `Φ 1`. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  thinRealization.homotopy (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun n ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ).congr fun p ↦
      (topologicalNerveMap_app_apply _ _ (op n) p.2).symm

theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : SimplexCategory) (F : ComposableArrows C n.len)
    (t : SimplexCategory.toTop.obj n) :
    thinClassifyingSpaceHomotopy Φ hΦ (s, thinRealization.ι _ n (F, t)) =
      thinRealization.ι _ n (((Φ s).mapComposableArrows _).obj F, t) :=
  (thinRealization.homotopy_apply_ι
      (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans <|
    congrArg (fun F ↦ thinRealization.ι _ n (F, t)) (topologicalNerveMap_app_apply _ _ (op n) F)

variable (C) in
/-- The canonical quotient comparison map from the fat classifying space to the thin classifying
space. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  thinRealization.fatToThin (topologicalNerve C)

theorem fatToThinClassifyingSpace_ι (n : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatToThinClassifyingSpace C (fatRealization.ι _ n (F, t)) =
      thinRealization.ι (topologicalNerve C) (SemiSimplexCategory.toSimplexCategory.obj n)
        (F, t) :=
  thinRealization.fatToThin_ι (topologicalNerve C) n F t

variable (C) in
/-- The comparison map from the fat classifying space to the thin classifying space is a quotient
map. -/
theorem isQuotientMap_fatToThinClassifyingSpace :
    IsQuotientMap (fatToThinClassifyingSpace C) :=
  thinRealization.isQuotientMap_fatToThin (topologicalNerve C)

variable (C) in
/-- The comparison map from the fat classifying space to the thin classifying space is
surjective. -/
theorem fatToThinClassifyingSpace_surjective :
    Function.Surjective (fatToThinClassifyingSpace C) :=
  thinRealization.fatToThin_surjective (topologicalNerve C)

/-- The comparison map from the fat classifying space to the thin classifying space is natural in
continuous functors. -/
@[reassoc (attr := simp)]
theorem fatToThinClassifyingSpace_naturality (Φ : C ⥤ D)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D =
      fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ :=
  fatClassifyingSpace.hom_ext fun n F t ↦
    (congrArg (fatToThinClassifyingSpace D) (fatClassifyingSpaceMap_ι Φ hΦ n F t)).trans <|
      (fatToThinClassifyingSpace_ι n ((Φ.mapComposableArrows _).obj F) t).trans <|
        (thinClassifyingSpaceMap_ι Φ hΦ _ F t).symm.trans <|
          (congrArg (thinClassifyingSpaceMap Φ hΦ) (fatToThinClassifyingSpace_ι n F t)).symm

end Basic

namespace thinClassifyingSpace

section Coarse

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The augmentation of the topological nerve by the isomorphism class of a vertex. Its continuity
uses only continuity of source on total arrows. -/
def coarseAugmentation :
    topologicalNerve C ⟶
      (Functor.const _).obj (TopCat.of (Quotient (isIsomorphicSetoid C))) where
  app _ := TopCat.ofHom ⟨fun F ↦ Quotient.mk _ (F.obj 0), by
    apply continuous_quot_mk.comp
    simpa only [Function.comp_def, ComposableArrows.totalArrow_left] using
      hs.comp (ComposableArrows.continuous_totalArrow 0 0 le_rfl)⟩
  naturality _ _ f := by
    ext F
    exact F.quotient_mk_obj
      ((SimplexCategory.toCat.map f.unop).toFunctor.obj (0 : Fin (_ + 1)))

/-- The coarse augmentation reads the isomorphism class of the first vertex. -/
@[simp↓]
theorem coarseAugmentation_app_apply (m : SimplexCategoryᵒᵖ)
    (F : (topologicalNerve C).obj m) :
    (coarseAugmentation hs).app m F = Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (rfl)

/-- The coarse projection from the thin classifying space to the orbit quotient of objects, with
its quotient topology. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  thinRealization.augment (coarseAugmentation hs)

/-- The coarse projection is induced by the coarse augmentation of the topological nerve. -/
theorem coarseMap_eq_augment :
    coarseMap hs = thinRealization.augment (coarseAugmentation hs) :=
  (rfl)

/-- A point of a simplex projects to the isomorphism class of its first vertex. -/
@[simp↓]
theorem coarseMap_ι (m : SimplexCategory) (F : ComposableArrows C m.len)
    (t : SimplexCategory.toTop.obj m) :
    coarseMap hs (thinRealization.ι _ m (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (thinRealization.augment_ι (coarseAugmentation hs) m F t).trans
    (coarseAugmentation_app_apply hs (op m) F)

/-- The canonical comparison from fat to thin classifying spaces commutes with their coarse
projections. -/
@[reassoc (attr := simp)]
theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs :=
  fatClassifyingSpace.hom_ext fun n F t ↦
    (congrArg (coarseMap hs) (fatToThinClassifyingSpace_ι n F t)).trans <|
      (coarseMap_ι hs _ F t).trans (fatClassifyingSpace.coarseMap_ι hs n F t).symm

/-- Every orbit occurs as the projection of a vertex in the thin classifying space. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) := fun y ↦
  let ⟨z, hz⟩ := fatClassifyingSpace.coarseMap_surjective hs y
  ⟨fatToThinClassifyingSpace C z,
    (ConcreteCategory.congr_hom (fatToThinClassifyingSpace_comp_coarseMap hs) z).trans hz⟩

/-- With continuous units, the coarse projection is a quotient map: the topology on the orbit space
is also the final topology for the projection from the thin classifying space. -/
theorem isQuotientMap_coarseMap
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) :=
  IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous (coarseMap hs).hom.continuous
    (by
      have h : (coarseMap hs) ∘ (fatToThinClassifyingSpace C) =
          fatClassifyingSpace.coarseMap hs :=
        funext fun z ↦ ConcreteCategory.congr_hom (fatToThinClassifyingSpace_comp_coarseMap hs) z
      exact h.symm ▸ fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

end Coarse

section Topology

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- When `Quiver.Total C` is first-countable, the thin classifying space `B_top(C)` is compactly
generated in its raw weak realization topology (for every test-space universe `w`). -/
theorem uCompactlyGeneratedSpace [FirstCountableTopology (Quiver.Total C)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  have : ∀ n, UCompactlyGeneratedSpace.{w} ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (UCompactlyGeneratedSpace.{w} (ComposableArrows C _))
  thinRealization.uCompactlyGeneratedSpace (topologicalNerve C)

/-- When `Quiver.Total C` is second-countable, the thin classifying space `B_top(C)` is Lindelöf in
its raw weak realization topology. -/
theorem lindelofSpace [SecondCountableTopology (Quiver.Total C)] :
    LindelofSpace (thinClassifyingSpace C) :=
  have : ∀ n, LindelofSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (LindelofSpace (ComposableArrows C _))
  thinRealization.lindelofSpace (topologicalNerve C)

section ClosedUnit

variable (hunit : IsClosed (range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)))
include hunit

/-- When the identity arrows form a closed subset of `Quiver.Total C`, every degeneracy of the
topological nerve has closed image. -/
theorem isClosed_range_σ (n : ℕ) (i : Fin (n + 1)) :
    IsClosed (range (SimplicialObject.σ (topologicalNerve C) i)) :=
  (isClosedEmbedding_topologicalNerve_σ hunit i).isClosed_range

/-- When the identity arrows form a closed subset of `Quiver.Total C`, every skeleton inclusion
`sk_k B_top(C) ⟶ B_top(C)` is a closed embedding. -/
theorem isClosedEmbedding_skeletonIncl (k : ℕ) :
    IsClosedEmbedding (thinRealization.skeletonIncl (topologicalNerve C) k) :=
  thinRealization.isClosedEmbedding_skeletonIncl (topologicalNerve C) (isClosed_range_σ hunit) k

/-- When the identity arrows form a closed subset of `Quiver.Total C` and `Quiver.Total C` is `T1`,
`B_top(C)` is `T1`. -/
theorem t1Space [T1Space (Quiver.Total C)] : T1Space (thinClassifyingSpace C) :=
  have : ∀ n, T1Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T1Space (ComposableArrows C _))
  thinRealization.t1Space (topologicalNerve C) (isClosed_range_σ hunit)

/-- **Finite-skeleton compactness.** When the identity arrows form a closed subset of
`Quiver.Total C` and `Quiver.Total C` is `T1`, every compact subset of `B_top(C)` lies in a finite
skeleton. -/
theorem exists_subset_range_skeletonIncl_of_isCompact [T1Space (Quiver.Total C)]
    {K : Set (thinClassifyingSpace C)} (hK : IsCompact K) :
    ∃ k, K ⊆ range (thinRealization.skeletonIncl (topologicalNerve C) k) :=
  have : ∀ n, T1Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T1Space (ComposableArrows C _))
  thinRealization.exists_subset_range_skeletonIncl_of_isCompact (topologicalNerve C)
    (isClosed_range_σ hunit) hK

/-- When the identity arrows form a closed subset of `Quiver.Total C` and `Quiver.Total C` is `T1`,
every continuous map from a compact space into `B_top(C)` factors continuously through a finite
skeleton. -/
theorem exists_lift_of_compactSpace [T1Space (Quiver.Total C)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinClassifyingSpace C)) :
    ∃ k, ∃ g' : C(K, thinRealization.skeleton (topologicalNerve C) k),
      (thinRealization.skeletonIncl (topologicalNerve C) k).hom.comp g' = g :=
  have : ∀ n, T1Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T1Space (ComposableArrows C _))
  thinRealization.exists_lift_of_compactSpace (topologicalNerve C) (isClosed_range_σ hunit) g

/-- When the identity arrows form a closed subset of `Quiver.Total C` and `Quiver.Total C` is
regular and second-countable, `B_top(C)` is normal. -/
theorem normalSpace [RegularSpace (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    NormalSpace (thinClassifyingSpace C) :=
  have : ∀ n, RegularSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (RegularSpace (ComposableArrows C _))
  have : ∀ n, LindelofSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (LindelofSpace (ComposableArrows C _))
  thinRealization.normalSpace (topologicalNerve C) (isClosed_range_σ hunit)

/-- **Normal Hausdorff thin classifying space.** When the identity arrows form a closed subset of
`Quiver.Total C` and `Quiver.Total C` is `T3` and second-countable, `B_top(C)` is `T4` (normal and
`T1`, hence Hausdorff). -/
theorem t4Space [T3Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) :=
  have : ∀ n, T3Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T3Space (ComposableArrows C _))
  have : ∀ n, LindelofSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (LindelofSpace (ComposableArrows C _))
  thinRealization.t4Space (topologicalNerve C) (isClosed_range_σ hunit)

/-- When the identity arrows form a closed subset of `Quiver.Total C` and `Quiver.Total C` is `T3`
and second-countable, `B_top(C)` is Hausdorff. -/
theorem t2Space [T3Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    T2Space (thinClassifyingSpace C) :=
  have : ∀ n, T3Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T3Space (ComposableArrows C _))
  have : ∀ n, LindelofSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (LindelofSpace (ComposableArrows C _))
  thinRealization.t2Space (topologicalNerve C) (isClosed_range_σ hunit)

/-- **Paracompact thin classifying space.** When the identity arrows form a closed subset of
`Quiver.Total C` and `Quiver.Total C` is `T3` and second-countable, `B_top(C)` is paracompact in
its raw weak realization topology. -/
theorem paracompactSpace [T3Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    ParacompactSpace (thinClassifyingSpace C) :=
  have : ∀ n, T3Space ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (T3Space (ComposableArrows C _))
  have : ∀ n, LindelofSpace ((topologicalNerve C).obj n) :=
    fun _ ↦ inferInstanceAs (LindelofSpace (ComposableArrows C _))
  thinRealization.paracompactSpace (topologicalNerve C) (isClosed_range_σ hunit)

end ClosedUnit

end Topology

section SingleObj

variable (G : Type u)

/-- In the one-object category `SingleObj G` over a `T1` monoid `G`, the unit locus is a singleton
and therefore closed in `Quiver.Total (SingleObj G)`. No étaleness assumption is needed. -/
theorem isClosed_range_unit_singleObj [Monoid G] [TopologicalSpace G] [T1Space G] :
    IsClosed (range fun x : SingleObj G ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (SingleObj G))) := by
  have : T1Space (Quiver.Total (SingleObj G)) :=
    (OneObjectGroupoid.arrowHomeomorph G).isEmbedding.t1Space
  have hrange : (range fun x : SingleObj G ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total (SingleObj G))) =
      {⟨SingleObj.star G, SingleObj.star G, 𝟙 (SingleObj.star G)⟩} := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      cases x
      rfl
    · rintro rfl
      exact ⟨SingleObj.star G, rfl⟩
  rw [hrange]
  exact isClosed_singleton

/-- The thin bar classifying space `B_top(SingleObj G)` of a first-countable monoid `G` is
compactly generated in its raw weak realization topology. -/
theorem uCompactlyGeneratedSpace_singleObj [Monoid G] [TopologicalSpace G]
    [FirstCountableTopology G] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace (SingleObj G)) :=
  have : FirstCountableTopology (Quiver.Total (SingleObj G)) :=
    (OneObjectGroupoid.arrowHomeomorph G).isInducing.firstCountableTopology
  uCompactlyGeneratedSpace

/-- Every compact subset of `B_top(SingleObj G)` lies in a finite skeleton whenever `G` is a `T1`
monoid. -/
theorem exists_subset_range_skeletonIncl_of_isCompact_singleObj [Monoid G] [TopologicalSpace G]
    [T1Space G] {K : Set (thinClassifyingSpace (SingleObj G))} (hK : IsCompact K) :
    ∃ k, K ⊆ range (thinRealization.skeletonIncl (topologicalNerve (SingleObj G)) k) :=
  have : T1Space (Quiver.Total (SingleObj G)) :=
    (OneObjectGroupoid.arrowHomeomorph G).isEmbedding.t1Space
  exists_subset_range_skeletonIncl_of_isCompact (isClosed_range_unit_singleObj G) hK

/-- The thin bar classifying space `B_top(SingleObj G)` of a second-countable `T1` topological
group `G` (for example a compact Lie group or torus) is `T4` (normal and Hausdorff). No étaleness
assumption is needed. -/
theorem t4Space_singleObj [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [SecondCountableTopology G] :
    T4Space (thinClassifyingSpace (SingleObj G)) :=
  have : T3Space G := {}
  have : T3Space (Quiver.Total (SingleObj G)) :=
    (OneObjectGroupoid.arrowHomeomorph G).isEmbedding.t3Space
  t4Space (isClosed_range_unit_singleObj G)

/-- The thin bar classifying space `B_top(SingleObj G)` of a second-countable `T1` topological
group `G` is Hausdorff. -/
theorem t2Space_singleObj [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [SecondCountableTopology G] :
    T2Space (thinClassifyingSpace (SingleObj G)) :=
  have := t4Space_singleObj G
  inferInstance

/-- **Paracompact torus and Lie-group bar space.** The thin bar classifying space
`B_top(SingleObj G)` of a second-countable `T1` topological group `G` is paracompact in its raw
weak realization topology. No étaleness assumption is needed. -/
theorem paracompactSpace_singleObj [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] [SecondCountableTopology G] :
    ParacompactSpace (thinClassifyingSpace (SingleObj G)) :=
  have : T3Space G := {}
  have : T3Space (Quiver.Total (SingleObj G)) :=
    (OneObjectGroupoid.arrowHomeomorph G).isEmbedding.t3Space
  paracompactSpace (isClosed_range_unit_singleObj G)

end SingleObj

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{u} C] [IsGroupoid C]
  [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The restricted nerve is exactly the part over the image of the saturated object set in the
coarse space, in each simplicial degree. -/
theorem range_topologicalNerveMap_ι_eq_preimage (m : SimplexCategoryᵒᵖ) :
    range ((TauCeti.topologicalNerveMap P.ι P.continuous_mapTotal_ι).app m) =
      (TauCeti.thinClassifyingSpace.coarseAugmentation hs).app m ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) := by
  rw [TauCeti.coe_topologicalNerveMap_app]
  refine (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms _).trans ?_
  ext F
  constructor
  · intro hF
    exact ⟨F.obj 0, hF,
      (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs m F).symm⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨e⟩ := _root_.Quotient.exact
      (h.trans (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs m F))
    exact P.prop_of_iso e hx

include hs in
/-- The inclusion of a saturated open full subgroupoid induces an open embedding on thin
classifying spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpaceMap_eq]
  apply TauCeti.thinRealization.isOpenEmbedding_map_of_range_eq_preimage
    (TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (V := _root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
  · intro m
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact P.isOpenEmbedding_mapComposableArrows_ι hs hP _
  · exact P.range_topologicalNerveMap_ι_eq_preimage hs

include hs in
/-- The inclusion of a saturated closed full subgroupoid induces a closed embedding on thin
classifying spaces. -/
theorem isClosedEmbedding_thinClassifyingSpaceMap_ι (hP : IsClosed {x | P x}) :
    IsClosedEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpaceMap_eq]
  apply TauCeti.thinRealization.isClosedEmbedding_map_of_range_eq_preimage
    (TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (V := _root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
  · intro m
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact P.isClosedEmbedding_mapComposableArrows_ι hs hP _
  · exact P.range_topologicalNerveMap_ι_eq_preimage hs

/-- **Exact coarse-map preimage.** The preimage of a saturated coarse subset under the thin
coarse projection `q : B_top(C) → |C|` is precisely the image of `B_top(C|P)`. -/
theorem preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι :
    TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpace.coarseMap_eq_augment, TauCeti.thinClassifyingSpaceMap_eq]
  exact TauCeti.thinRealization.preimage_augment_eq_range_map _
    (P.range_topologicalNerveMap_ι_eq_preimage hs)

/-- **Exact saturated open restriction `q⁻¹(V) ≃ₜ B_top(C|V)`.** The thin classifying space of a
saturated open restriction is homeomorphic to the coarse-map preimage with its subspace
topology. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

/-- The open restriction homeomorphism is induced by the inclusion functor. -/
@[simp↓]
theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z :=
  (rfl)

/-- Mapping the inverse open restriction homeomorphism back by inclusion recovers the given point
of the coarse-map preimage. -/
@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).apply_symm_apply z)

/-- **Exact saturated closed restriction `q⁻¹(F) ≃ₜ B_top(C|F)`.** The thin classifying space of a
saturated closed restriction is homeomorphic to the coarse-map preimage with its subspace
topology. -/
def thinClassifyingSpaceClosedRestrictionHomeomorph (hP : IsClosed {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

/-- The closed restriction homeomorphism is induced by the inclusion functor. -/
@[simp↓]
theorem thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val (hP : IsClosed {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z :=
  (rfl)

/-- Mapping the inverse closed restriction homeomorphism back by inclusion recovers the given point
of the coarse-map preimage. -/
@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceClosedRestrictionHomeomorph_symm_apply
    (hP : IsClosed {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val
    ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).apply_symm_apply z)

end CategoryTheory.ObjectProperty

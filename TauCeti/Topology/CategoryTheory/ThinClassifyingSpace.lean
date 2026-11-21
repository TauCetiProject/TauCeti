/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton
public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict
public import TauCeti.Topology.CategoryTheory.Latching
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Thin classifying spaces of topological categories and groupoids

For a category `C` whose total arrow type `Quiver.Total C` carries a topology, the thin classifying
space `TauCeti.thinClassifyingSpace C` is `(topologicalNerve C).geometricRealization`: the quotient
of `Σ n : ℕ, ComposableArrows C n × Δⁿ` by all face and degeneracy identifications, equipped with
its genuine colimit topology in `TopCat` (with no compactly-generated replacement).

Forgetting degeneracies gives the quotient map `TauCeti.fatToThinClassifyingSpace C`
(`TauCeti.isQuotientMap_fatToThinClassifyingSpace`). Adapting the fat-realization APIs of
`TauCeti.Topology.CategoryTheory.Nerve`, `TauCeti.Topology.CategoryTheory.CoarseSpace`, and
`TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict`, continuous functors and `[0, 1]`-families
induce `TauCeti.thinClassifyingSpaceMap` and `TauCeti.thinClassifyingSpaceHomotopy`; when the
source map `Quiver.Total.left : Quiver.Total C → C` is continuous, closed full subcategories induce
closed embeddings (`CategoryTheory.ObjectProperty.isClosedEmbedding_thinClassifyingSpaceMap_ι`) and
saturated open full subgroupoids induce open embeddings
(`CategoryTheory.ObjectProperty.isOpenEmbedding_thinClassifyingSpaceMap_ι`); and for groupoids with
continuous source, `TauCeti.thinClassifyingSpace.coarseMap` factors
`TauCeti.fatClassifyingSpace.coarseMap` and identifies coarse preimages of saturated open or closed
sets (`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding`,
`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`,
`CategoryTheory.ObjectProperty.thinClassifyingSpaceClosedRestrictionHomeomorph`).

Specializing the skeletal pushout and sequential-colimit theorems of
`TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton` proves that
`thinClassifyingSpace C` is `T4` (hence Hausdorff) in its colimit topology for:
* any category with a metrizable total arrow space (`TauCeti.thinClassifyingSpace.instT4Space`), and
  in particular any category with a second-countable regular `T0` total arrow space
  (`TauCeti.thinClassifyingSpace.instT4SpaceOfRegularSecondCountable`, covering Hausdorff orbifold
  and Lie groupoids, where second-countability also supplies `LindelofSpace`);
* any category with `T3` `Quiver.Total C` and Lindelöf nerve levels
  (`TauCeti.thinClassifyingSpace.instT4Space_of_t3Space_lindelofSpace`,
  `TauCeti.thinClassifyingSpace.instLindelofSpace_of_levels`), including `σ`-compact `T3`
  categories and groupoids (`TauCeti.thinClassifyingSpace.t4Space_of_sigmaCompactSpace`,
  `TauCeti.thinClassifyingSpace.lindelofSpace_of_sigmaCompactSpace`,
  `TauCeti.thinClassifyingSpace.instT4SpaceOfSigmaCompactSpace`,
  `TauCeti.thinClassifyingSpace.instLindelofSpaceOfSigmaCompactSpace`, hence paracompact);
* any category with compact Hausdorff `Quiver.Total C` and continuous source, target, units, and
  composition, where `thinClassifyingSpace C` is `T4`, Lindelöf, and compactly generated
  (`TauCeti.thinClassifyingSpace.t4Space_of_compactSpace`,
  `TauCeti.thinClassifyingSpace.lindelofSpace_of_compactSpace`,
  `TauCeti.thinClassifyingSpace.compactlyGeneratedSpace_of_compactSpace`), packaged as typeclass
  instances for compact Hausdorff topological groupoids (`IsTopologicalGroupoid C`:
  `TauCeti.thinClassifyingSpace.instT4SpaceOfCompactSpace`,
  `TauCeti.thinClassifyingSpace.instLindelofSpaceOfCompactSpace`,
  `TauCeti.thinClassifyingSpace.instCompactlyGeneratedSpaceOfCompactSpace`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Classifying spaces and classifying topoi*, LNM **1616**, Springer, 1995.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), 205–222.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial SimplicialObject Topology

universe w v u

namespace TauCeti

open SemiSimplexCategory (toSimplexCategory)
open SimplexCategory (toTop)

section Functoriality

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The thin classifying space of a category whose total arrows carry a topology: the thin geometric
realization of its topological nerve, modulo both face and degeneracy operators. -/
@[expose] def thinClassifyingSpace : TopCat.{max u v} := geometricRealization (topologicalNerve C)

/-- The canonical comparison morphism `fatClassifyingSpace C ⟶ thinClassifyingSpace C` collapsing
degenerate simplices. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  fatToGeometricRealization (topologicalNerve C)

theorem fatToThinClassifyingSpace_eq :
    fatToThinClassifyingSpace C = fatToGeometricRealization (topologicalNerve C) := (rfl)

/-- The comparison map `fatClassifyingSpace C ⟶ thinClassifyingSpace C` is surjective. -/
theorem fatToThinClassifyingSpace_surjective : Function.Surjective (fatToThinClassifyingSpace C) :=
  fatToGeometricRealization_surjective (topologicalNerve C)

/-- The comparison map `fatClassifyingSpace C ⟶ thinClassifyingSpace C` is a quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpace : IsQuotientMap (fatToThinClassifyingSpace C) :=
  isQuotientMap_fatToGeometricRealization (topologicalNerve C)

variable {C}

/-- Two morphisms out of `thinClassifyingSpace C` agree once they agree on every simplex. -/
@[ext] theorem thinClassifyingSpace.hom_ext {Z : TopCat.{max u v}}
    {g h : thinClassifyingSpace C ⟶ Z}
    (H : ∀ (n : ℕ) (F : ComposableArrows C n) (t : toTop.{max u v}.obj ⦋n⦌),
      g (geometricRealization.ι (topologicalNerve C) n (F, t)) =
        h (geometricRealization.ι (topologicalNerve C) n (F, t))) : g = h :=
  geometricRealization.hom_ext (topologicalNerve C) H

@[simp↓] theorem fatToThinClassifyingSpace_ι (m : SemiSimplexCategory)
    (F : ComposableArrows C (toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.{max u v}.obj m) :
    fatToThinClassifyingSpace C (fatRealization.ι _ m (F, t)) =
      geometricRealization.ι (topologicalNerve C) (toSimplexCategory.obj m).len (F, t) :=
  fatToGeometricRealization_ι (topologicalNerve C) m F t

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The morphism of thin classifying spaces induced by a functor continuous on total arrows. -/
def thinClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpace C ⟶ thinClassifyingSpace D :=
  geometricRealization.map (topologicalNerveMap Φ hΦ)

theorem thinClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap Φ hΦ = geometricRealization.map (topologicalNerveMap Φ hΦ) := (rfl)

/-- `thinClassifyingSpaceMap Φ hΦ` applies `Φ` to the composable arrows of each simplex. -/
@[simp] theorem thinClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : ℕ) (F : ComposableArrows C n) (t : toTop.{max u v}.obj ⦋n⦌) :
    thinClassifyingSpaceMap Φ hΦ (geometricRealization.ι (topologicalNerve C) n (F, t)) =
      geometricRealization.ι (topologicalNerve D) n ((Φ.mapComposableArrows n).obj F, t) :=
  (geometricRealization.map_ι (topologicalNerveMap Φ hΦ) n F t).trans
    (by rw [topologicalNerveMap_app_apply])

/-- Functors agreeing on strings of composable arrows induce the same morphism on
`thinClassifyingSpace C`. -/
theorem thinClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    thinClassifyingSpaceMap Φ hΦ = thinClassifyingSpaceMap Ψ hΨ :=
  thinClassifyingSpace.hom_ext fun n F t ↦ (thinClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun G ↦ geometricRealization.ι (topologicalNerve D) n (G, t)) (h n F)).trans
      (thinClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
@[simp] theorem thinClassifyingSpaceMap_id :
    thinClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (thinClassifyingSpace C) :=
  (congrArg geometricRealization.map (topologicalNerveMap_id C)).trans geometricRealization.map_id

theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ)
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (congrArg geometricRealization.map (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans
    (geometricRealization.map_comp _ _)

/-- The comparison `fatClassifyingSpace ⟶ thinClassifyingSpace` is natural in `C`. -/
@[reassoc (attr := simp)] theorem fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace
    (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D =
      fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ := by
  simp only [fatClassifyingSpaceMap_eq, fatToThinClassifyingSpace_eq, thinClassifyingSpaceMap_eq]
  exact fatRealization_map_comp_fatToGeometricRealization (topologicalNerveMap Φ hΦ)

/-- A `[0, 1]`-family of functors `Φ s` depending continuously on `(s, a)` induces a homotopy
between the maps of thin classifying spaces induced by `Φ 0` and `Φ 1`. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  geometricRealization.homotopy (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun _ ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ).congr fun _ ↦
      (topologicalNerveMap_app_apply _ _ _ _).symm

@[simp] theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : ℕ) (F : ComposableArrows C n) (t : toTop.{max u v}.obj ⦋n⦌) :
    thinClassifyingSpaceHomotopy Φ hΦ (s, geometricRealization.ι (topologicalNerve C) n (F, t)) =
      geometricRealization.ι (topologicalNerve D) n (((Φ s).mapComposableArrows n).obj F, t) :=
  (geometricRealization.homotopy_apply_ι
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans
    (by rw [topologicalNerveMap_app_apply])

end Functoriality

namespace thinClassifyingSpace

section CoarseSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The coarse projection from `thinClassifyingSpace C` to `Quotient (isIsomorphicSetoid C)`. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  geometricRealization.augment (topologicalNerve.coarseAugmentation hs)

theorem coarseMap_eq_augment :
    coarseMap hs = geometricRealization.augment (topologicalNerve.coarseAugmentation hs) := (rfl)

@[simp↓] theorem coarseMap_ι (n : ℕ) (F : ComposableArrows C n) (t : toTop.{u}.obj ⦋n⦌) :
    coarseMap hs (geometricRealization.ι (topologicalNerve C) n (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (geometricRealization.augment_ι (topologicalNerve.coarseAugmentation hs) n F t).trans
    (topologicalNerve.coarseAugmentation_app_apply hs (op ⦋n⦌) F)

/-- The coarse projection of `fatClassifyingSpace C` descends along `fatToThinClassifyingSpace`. -/
@[reassoc (attr := simp)] theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs := by
  rw [fatToThinClassifyingSpace_eq, coarseMap_eq_augment, fatClassifyingSpace.coarseMap_eq_augment]
  exact geometricRealization.fatToGeometricRealization_comp_augment _

/-- The coarse projection from `thinClassifyingSpace C` is surjective. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) :=
  .of_comp (g := fatToThinClassifyingSpace C) <| by
    rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
    exact fatClassifyingSpace.coarseMap_surjective hs

/-- With continuous units, `coarseMap` on `thinClassifyingSpace C` is a topological quotient map. -/
theorem isQuotientMap_coarseMap (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) :=
  IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous (coarseMap hs).hom.continuous
    (by rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
        exact fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

end CoarseSpace

section PointSetTopology

open geometricRealization (skeleton)

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

instance [SecondCountableTopology (Quiver.Total C)] : LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (geometricRealization (topologicalNerve C)))

/-- When every nerve level `ComposableArrows C n` is Lindelöf, `thinClassifyingSpace C` is
Lindelöf in its colimit topology. -/
instance (priority := 90) instLindelofSpace_of_levels
    [∀ n : ℕ, LindelofSpace (ComposableArrows C n)] : LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (geometricRealization (topologicalNerve C)))

instance [FirstCountableTopology (Quiver.Total C)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{w} (geometricRealization (topologicalNerve C)))

/-- When `Quiver.Total C` is `T1`, `thinClassifyingSpace C` is `T1` in its colimit topology. -/
instance instT1Space [T1Space (Quiver.Total C)] : T1Space (thinClassifyingSpace C) :=
  inferInstanceAs (T1Space (geometricRealization (topologicalNerve C)))

/-- When `Quiver.Total C` is `T1`, every compact subset of `thinClassifyingSpace C` lies in a single
skeleton stage. -/
theorem exists_subset_range_skeleton_toRealization_of_isCompact [T1Space (Quiver.Total C)]
    {K : Set (thinClassifyingSpace C)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Set.range (skeleton.toRealization (topologicalNerve C) n) :=
  geometricRealization.exists_subset_range_skeleton_toRealization_of_isCompact _ hK

/-- When the identity arrows are closed in `Quiver.Total C`, every skeletal stage inclusion into
`thinClassifyingSpace C` is a closed embedding. -/
theorem isClosedEmbedding_skeleton_toRealization
    (hunit : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsClosedEmbedding (skeleton.toRealization (topologicalNerve C) n) :=
  geometricRealization.isClosedEmbedding_skeleton_toRealization _
    (fun j ↦ isClosedEmbedding_topologicalNerve_σ hunit j) n

/-- When `Quiver.Total C` is Hausdorff, every skeletal stage inclusion into `thinClassifyingSpace C`
is a closed embedding, with no assumption on identity arrows. -/
theorem isClosedEmbedding_skeleton_toRealization_of_t2Space [T2Space (Quiver.Total C)] (n : ℕ) :
    IsClosedEmbedding (skeleton.toRealization (topologicalNerve C) n) :=
  geometricRealization.isClosedEmbedding_skeleton_toRealization _
    (fun j ↦ isClosedEmbedding_σ (topologicalNerve C) j) n

/-- When `Quiver.Total C` is `T1` and identity arrows are closed, continuous maps from compact
spaces into `thinClassifyingSpace C` factor continuously through a finite skeleton. -/
theorem exists_lift_skeleton_of_compactSpace [T1Space (Quiver.Total C)]
    (hunit : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)))
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinClassifyingSpace C)) :
    ∃ (n : ℕ) (g' : C(K, (skeleton (topologicalNerve C)).obj n)),
      (skeleton.toRealization (topologicalNerve C) n).hom.comp g' = g :=
  geometricRealization.exists_lift_skeleton_of_compactSpace _
    (fun j ↦ isClosedEmbedding_topologicalNerve_σ hunit j) g

/-- When `Quiver.Total C` is Hausdorff, continuous maps from compact spaces into
`thinClassifyingSpace C` factor continuously through a finite skeleton, with no assumption on
identity arrows. -/
theorem exists_lift_skeleton_of_compactSpace_of_t2Space [T2Space (Quiver.Total C)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinClassifyingSpace C)) :
    ∃ (n : ℕ) (g' : C(K, (skeleton (topologicalNerve C)).obj n)),
      (skeleton.toRealization (topologicalNerve C) n).hom.comp g' = g :=
  geometricRealization.exists_lift_skeleton_of_compactSpace _
    (fun j ↦ isClosedEmbedding_σ (topologicalNerve C) j) g

/-- **Separation of `thinClassifyingSpace C` for metrizable arrow spaces.** For any category whose
total arrow space is metrizable, `thinClassifyingSpace C` is `T4` (hence Hausdorff) in its colimit
topology. -/
instance instT4Space [TopologicalSpace.MetrizableSpace (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) :=
  inferInstanceAs (T4Space (geometricRealization (topologicalNerve C)))

/-- **Separation of `thinClassifyingSpace C` for second-countable regular arrow spaces.** For any
category whose total arrow space is `T0`, regular, and second-countable (covering Hausdorff orbifold
and Lie groupoids), `thinClassifyingSpace C` is `T4` (hence Hausdorff, and paracompact together with
the `LindelofSpace` instance from second-countability) in its colimit topology. -/
instance instT4SpaceOfRegularSecondCountable [T0Space (Quiver.Total C)]
    [RegularSpace (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) :=
  -- `Mathlib.Topology.Metrizable.Urysohn` is imported privately so downstream callers get this
  -- instance without importing Urysohn metrization.
  have : TopologicalSpace.MetrizableSpace (Quiver.Total C) := inferInstance
  instT4Space

/-- **Separation of `thinClassifyingSpace C` for `T3` categories with Lindelöf nerve levels.**
When `Quiver.Total C` is `T3` and every nerve level `ComposableArrows C n` is Lindelöf,
`thinClassifyingSpace C` is `T4` (hence Hausdorff and paracompact) in its colimit topology. -/
instance (priority := 90) instT4Space_of_t3Space_lindelofSpace [T3Space (Quiver.Total C)]
    [∀ n : ℕ, LindelofSpace (ComposableArrows C n)] : T4Space (thinClassifyingSpace C) :=
  inferInstanceAs (T4Space (geometricRealization (topologicalNerve C)))

section CompactCategory

variable [TopologicalSpace C] [CompactSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
  (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
  (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
  (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
    p.val.1.comp p.val.2 p.property)
include hs ht hu hc

private theorem compactSpace_composableArrows [T2Space C] :
    ∀ n : ℕ, CompactSpace (ComposableArrows C n) :=
  ComposableArrows.compactSpace_of_compactSpace hs hu
    (by simpa only [Quiver.Total.comp_def] using hc) ht

/-- **Separation of `thinClassifyingSpace C` for compact Hausdorff categories.** If `Quiver.Total C`
is compact Hausdorff and source, target, units, and composition are continuous, then
`thinClassifyingSpace C` is `T4` in its colimit topology. -/
theorem t4Space_of_compactSpace [T2Space (Quiver.Total C)] : T4Space (thinClassifyingSpace C) := by
  have : T2Space C := .of_injective_continuous (fun _ _ h ↦ congrArg Quiver.Total.left h) hu
  have := compactSpace_composableArrows hs ht hu hc
  exact inferInstanceAs (T4Space (geometricRealization (topologicalNerve C)))

/-- If `C` is Hausdorff, `Quiver.Total C` is compact, and source, target, units, and composition
are continuous, then `thinClassifyingSpace C` is Lindelöf in its colimit topology. -/
theorem lindelofSpace_of_compactSpace [T2Space C] : LindelofSpace (thinClassifyingSpace C) := by
  have := compactSpace_composableArrows hs ht hu hc
  exact inferInstanceAs (LindelofSpace (geometricRealization (topologicalNerve C)))

/-- If `Quiver.Total C` is compact Hausdorff and source, target, units, and composition are
continuous, then `thinClassifyingSpace C` is compactly generated in its colimit topology. -/
theorem compactlyGeneratedSpace_of_compactSpace [T2Space (Quiver.Total C)] :
    CompactlyGeneratedSpace (thinClassifyingSpace C) := by
  have : T2Space C := .of_injective_continuous (fun _ _ h ↦ congrArg Quiver.Total.left h) hu
  have := compactSpace_composableArrows hs ht hu hc
  exact inferInstanceAs (CompactlyGeneratedSpace (geometricRealization (topologicalNerve C)))

end CompactCategory

section SigmaCompactCategory

variable [TopologicalSpace C] [SigmaCompactSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
  (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
  (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
  (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.fst.right = p.snd.left} ↦
    p.val.fst.comp p.val.snd p.property)
include hs ht hu hc

private theorem sigmaCompactSpace_composableArrows [T2Space C] :
    ∀ n : ℕ, SigmaCompactSpace (ComposableArrows C n) :=
  ComposableArrows.sigmaCompactSpace hs hu
    (by simpa only [Quiver.Total.comp_def] using hc) ht

/-- If `C` is Hausdorff, `Quiver.Total C` is `σ`-compact, and source, target, units, and
composition are continuous, then `thinClassifyingSpace C` is Lindelöf in its colimit topology. -/
theorem lindelofSpace_of_sigmaCompactSpace [T2Space C] :
    LindelofSpace (thinClassifyingSpace C) := by
  have := sigmaCompactSpace_composableArrows hs ht hu hc
  exact inferInstanceAs (LindelofSpace (geometricRealization (topologicalNerve C)))

/-- **Separation of `thinClassifyingSpace C` for `σ`-compact `T3` categories.** If `Quiver.Total C`
is `σ`-compact and `T3`, and source, target, units, and composition are continuous, then
`thinClassifyingSpace C` is `T4` (hence Hausdorff and paracompact) in its colimit topology. -/
theorem t4Space_of_sigmaCompactSpace [T3Space (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) := by
  have : T2Space C := .of_injective_continuous (fun _ _ h ↦ congrArg Quiver.Total.left h) hu
  have := sigmaCompactSpace_composableArrows hs ht hu hc
  exact inferInstanceAs (T4Space (geometricRealization (topologicalNerve C)))

end SigmaCompactCategory

end PointSetTopology

section TopologicalGroupoidInstances

open IsTopologicalGroupoid

variable (C : Type u) [Category.{v} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

/-- The thin classifying space of any compact Hausdorff topological groupoid is `T4` in its colimit
topology, without second-countability or étaleness. -/
instance instT4SpaceOfCompactSpace [T2Space (Quiver.Total C)] [CompactSpace (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) :=
  t4Space_of_compactSpace continuous_source continuous_target continuous_unit continuous_comp

instance instLindelofSpaceOfCompactSpace [T2Space (Quiver.Total C)]
    [CompactSpace (Quiver.Total C)] : LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (geometricRealization (topologicalNerve C)))

instance instCompactlyGeneratedSpaceOfCompactSpace [T2Space (Quiver.Total C)]
    [CompactSpace (Quiver.Total C)] : CompactlyGeneratedSpace (thinClassifyingSpace C) :=
  compactlyGeneratedSpace_of_compactSpace continuous_source continuous_target continuous_unit
    continuous_comp

/-- The thin classifying space of any `σ`-compact Hausdorff topological groupoid is Lindelöf in its
colimit topology. -/
instance (priority := 90) instLindelofSpaceOfSigmaCompactSpace [T2Space (Quiver.Total C)]
    [SigmaCompactSpace (Quiver.Total C)] : LindelofSpace (thinClassifyingSpace C) :=
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  lindelofSpace_of_sigmaCompactSpace continuous_source continuous_target continuous_unit
    continuous_comp

/-- The thin classifying space of any `σ`-compact `T3` topological groupoid is `T4` (hence
Hausdorff and paracompact) in its colimit topology, without second-countability or étaleness. -/
instance (priority := 90) instT4SpaceOfSigmaCompactSpace [T3Space (Quiver.Total C)]
    [SigmaCompactSpace (Quiver.Total C)] : T4Space (thinClassifyingSpace C) :=
  t4Space_of_sigmaCompactSpace continuous_source continuous_target continuous_unit continuous_comp

end TopologicalGroupoidInstances

end thinClassifyingSpace

end TauCeti

namespace CategoryTheory.ObjectProperty

open TauCeti

section GeneralCategory

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C)

/-- Inclusion of any full subcategory induces an injection on thin classifying spaces. -/
theorem thinClassifyingSpaceMap_ι_injective :
    Function.Injective (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  geometricRealization.map_injective fun _ ↦ by
    rw [coe_topologicalNerveMap_app]
    exact (ComposableArrows.isEmbedding_mapComposableArrows_obj
      isEmbedding_total_fullSubcategory).injective

/-- When the source map `Quiver.Total.left : Quiver.Total C → C` is continuous, inclusion of a
closed full subcategory induces a closed embedding on thin classifying spaces. -/
theorem isClosedEmbedding_thinClassifyingSpaceMap_ι [TopologicalSpace C]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C)) (hP : IsClosed {x | P x}) :
    IsClosedEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  geometricRealization.isClosedEmbedding_map fun n ↦ by
    rw [coe_topologicalNerveMap_app]; exact P.isClosedEmbedding_mapComposableArrows_ι hs hP n

/-- For a groupoid with continuous source `Quiver.Total.left : Quiver.Total C → C`, the inclusion
of a saturated open full subgroupoid induces an open embedding on thin classifying spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι [IsGroupoid C] [TopologicalSpace C]
    [P.IsClosedUnderIsomorphisms]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C)) (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  geometricRealization.isOpenEmbedding_map
    (fun n ↦ by
      rw [coe_topologicalNerveMap_app]; exact P.isOpenEmbedding_mapComposableArrows_ι hs hP n)
    fun m n f (F : ComposableArrows C n) hF ↦ by
      rw [topologicalNerve_map_apply, coe_topologicalNerveMap_app] at hF
      have h0 : P (F.obj (f.toOrderHom 0)) := by
        rw [← nerve.map_obj f F 0]
        exact (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms m).subset hF
      rw [coe_topologicalNerveMap_app]
      exact (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms n).superset
        (P.prop_of_iso (asIso (F.map (homOfLE (Fin.zero_le _)))).symm h0)

end GeneralCategory

section SaturatedGroupoid

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The preimage of a saturated coarse subset in `thinClassifyingSpace C` is the image of the thin
classifying space of the corresponding full restriction. -/
theorem preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι :
    thinClassifyingSpace.coarseMap hs ⁻¹' (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  geometricRealization.preimage_augment_eq_range_map (ε := topologicalNerve.coarseAugmentation hs)
    (fun n ↦ P.range_topologicalNerveMap_ι hs (op ⦋n⦌))

/-- Whenever the inclusion of a saturated full subgroupoid induces a topological embedding on thin
classifying spaces (for instance via `isOpenEmbedding_thinClassifyingSpaceMap_ι` or
`isClosedEmbedding_thinClassifyingSpaceMap_ι`), its thin classifying space is homeomorphic to the
corresponding coarse-map preimage with its subspace topology. -/
def thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι)) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  h.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_coarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

@[simp↓] theorem thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_apply_val
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    (h : IsEmbedding (thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι))
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h).symm z) = z.val :=
  congrArg Subtype.val
    ((P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs h).apply_symm_apply z)

/-- The thin classifying space of a saturated open full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs
    (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding

@[simp↓] theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓] theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  P.thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    hs (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

/-- The thin classifying space of a saturated closed full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceClosedRestrictionHomeomorph (hP : IsClosed {x | P x}) :
    thinClassifyingSpace P.FullSubcategory ≃ₜ
      (thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  P.thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding hs
    (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding

@[simp↓] theorem thinClassifyingSpaceClosedRestrictionHomeomorph_apply_val (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP z).val =
      thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceClosedRestrictionHomeomorph_symm_apply
    (hP : IsClosed {x | P x})
    (z : thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceClosedRestrictionHomeomorph hs hP).symm z) = z.val :=
  P.thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorphOfIsEmbedding_symm_apply
    hs (P.isClosedEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding z

end SaturatedGroupoid

end CategoryTheory.ObjectProperty

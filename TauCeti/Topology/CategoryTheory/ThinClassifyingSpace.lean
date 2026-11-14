/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton
public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict
public import TauCeti.Topology.CategoryTheory.ComposableArrows
public import TauCeti.Topology.CategoryTheory.Groupoid.Examples
public import TauCeti.Topology.CategoryTheory.Latching

/-!
# Thin classifying spaces of topological categories and groupoids

For a category `C` whose total arrow type `Quiver.Total C` carries a topology, the thin classifying
space `TauCeti.thinClassifyingSpace C` is `(topologicalNerve C).geometricRealization`: the quotient
of `Σ n : ℕ, ComposableArrows C n × Δⁿ` by all face and degeneracy identifications, equipped with
its genuine colimit topology in `TopCat` (with no compactly-generated replacement).

Forgetting degeneracies gives the quotient map `TauCeti.fatToThinClassifyingSpace C`
(`TauCeti.isQuotientMap_fatToThinClassifyingSpace`). Continuous functors and `[0, 1]`-families
induce `TauCeti.thinClassifyingSpaceMap` and `TauCeti.thinClassifyingSpaceHomotopy`; closed full
subcategories induce closed embeddings
(`CategoryTheory.ObjectProperty.isClosedEmbedding_thinClassifyingSpaceMap_ι`); and for groupoids
with continuous source, `TauCeti.thinClassifyingSpace.coarseMap` factors
`TauCeti.fatClassifyingSpace.coarseMap` and restricts to open embeddings on saturated open full
subgroupoids (`CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`).

Specializing the skeletal pushout and sequential-colimit theorems of
`TauCeti.AlgebraicTopology.SimplicialObject.GeometricRealization.Skeleton` proves that
`thinClassifyingSpace C` is `T4` — hence Hausdorff and paracompact — in its colimit topology for:
* any category with a second-countable regular `T1` total arrow space
  (`TauCeti.thinClassifyingSpace.instT4Space`, covering orbifold and Lie groupoids);
* any category with compact Hausdorff `Quiver.Total C` and continuous source, target, units, and
  composition (`TauCeti.thinClassifyingSpace.t4Space_of_compactSpace`,
  `TauCeti.thinClassifyingSpace.instT4SpaceOfCompactSpace`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Classifying spaces and classifying topoi*, LNM **1616**, Springer, 1995.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Contemp. Math. **310** (2002), 205–222.
-/

public noncomputable section

open CategoryTheory Opposite Set Simplicial Topology

universe w v u

namespace TauCeti

section Functoriality

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- The thin classifying space of a category whose total arrows carry a topology: the thin geometric
realization of its topological nerve, modulo both face and degeneracy operators. -/
@[expose]
def thinClassifyingSpace : TopCat.{max u v} :=
  SimplicialObject.geometricRealization (topologicalNerve C)

/-- The canonical comparison morphism `fatClassifyingSpace C ⟶ thinClassifyingSpace C` collapsing
degenerate simplices. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  SimplicialObject.fatToGeometricRealization (topologicalNerve C)

theorem fatToThinClassifyingSpace_eq :
    fatToThinClassifyingSpace C = SimplicialObject.fatToGeometricRealization (topologicalNerve C) :=
  (rfl)

variable {C}

/-- Two morphisms out of `thinClassifyingSpace C` agree once they agree on every simplex. -/
@[ext]
theorem thinClassifyingSpace.hom_ext {Z : TopCat.{max u v}} {g h : thinClassifyingSpace C ⟶ Z}
    (H : ∀ (n : ℕ) (F : ComposableArrows C n) (t : SimplexCategory.toTop.{max u v}.obj ⦋n⦌),
      g (SimplicialObject.geometricRealization.ι (topologicalNerve C) n (F, t)) =
        h (SimplicialObject.geometricRealization.ι (topologicalNerve C) n (F, t))) : g = h :=
  SimplicialObject.geometricRealization.hom_ext (topologicalNerve C) H

@[simp↓]
theorem fatToThinClassifyingSpace_ι (m : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj m).len)
    (t : SemiSimplexCategory.toTop.{max u v}.obj m) :
    fatToThinClassifyingSpace C (fatRealization.ι _ m (F, t)) =
      SimplicialObject.geometricRealization.ι (topologicalNerve C)
        (SemiSimplexCategory.toSimplexCategory.obj m).len (F, t) :=
  SimplicialObject.geometricRealization.fatToGeometricRealization_ι (topologicalNerve C) m F t

/-- The comparison map `fatClassifyingSpace C ⟶ thinClassifyingSpace C` is surjective. -/
theorem fatToThinClassifyingSpace_surjective (C : Type u) [Category.{v} C]
    [TopologicalSpace (Quiver.Total C)] : Function.Surjective (fatToThinClassifyingSpace C) :=
  SimplicialObject.geometricRealization.fatToGeometricRealization_surjective (topologicalNerve C)

/-- The comparison map `fatClassifyingSpace C ⟶ thinClassifyingSpace C` is a quotient map. -/
theorem isQuotientMap_fatToThinClassifyingSpace (C : Type u) [Category.{v} C]
    [TopologicalSpace (Quiver.Total C)] : IsQuotientMap (fatToThinClassifyingSpace C) :=
  SimplicialObject.geometricRealization.isQuotientMap_fatToGeometricRealization (topologicalNerve C)

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The morphism of thin classifying spaces induced by a functor continuous on total arrows. -/
def thinClassifyingSpaceMap (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpace C ⟶ thinClassifyingSpace D :=
  SimplicialObject.geometricRealization.map (topologicalNerveMap Φ hΦ)

theorem thinClassifyingSpaceMap_eq (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap Φ hΦ =
      SimplicialObject.geometricRealization.map (topologicalNerveMap Φ hΦ) := (rfl)

/-- `thinClassifyingSpaceMap Φ hΦ` applies `Φ` to the composable arrows of each simplex. -/
theorem thinClassifyingSpaceMap_ι (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal)
    (n : ℕ) (F : ComposableArrows C n) (t : SimplexCategory.toTop.{max u v}.obj ⦋n⦌) :
    thinClassifyingSpaceMap Φ hΦ
        (SimplicialObject.geometricRealization.ι (topologicalNerve C) n (F, t)) =
      SimplicialObject.geometricRealization.ι (topologicalNerve D) n
        ((Φ.mapComposableArrows n).obj F, t) :=
  (SimplicialObject.geometricRealization.map_ι (topologicalNerveMap Φ hΦ) n F t).trans
    (by rw [topologicalNerveMap_app_apply])

/-- Functors agreeing on strings of composable arrows induce the same morphism on `BC`. -/
theorem thinClassifyingSpaceMap_eq_of_mapComposableArrows_obj {Φ Ψ : C ⥤ D}
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal)
    (h : ∀ n F, (Φ.mapComposableArrows n).obj F = (Ψ.mapComposableArrows n).obj F) :
    thinClassifyingSpaceMap Φ hΦ = thinClassifyingSpaceMap Ψ hΨ :=
  thinClassifyingSpace.hom_ext fun n F t ↦ (thinClassifyingSpaceMap_ι Φ hΦ n F t).trans <|
    (congrArg (fun G ↦ SimplicialObject.geometricRealization.ι (topologicalNerve D) n (G, t))
      (h n F)).trans (thinClassifyingSpaceMap_ι Ψ hΨ n F t).symm

variable (C) in
@[simp]
theorem thinClassifyingSpaceMap_id :
    thinClassifyingSpaceMap (𝟭 C) (Prefunctor.mapTotal_id (Q := C) ▸ continuous_id) =
      𝟙 (thinClassifyingSpace C) :=
  (congrArg SimplicialObject.geometricRealization.map (topologicalNerveMap_id C)).trans
    SimplicialObject.geometricRealization.map_id

theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ)
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (congrArg SimplicialObject.geometricRealization.map (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans
    (SimplicialObject.geometricRealization.map_comp _ _)

/-- The comparison `fatClassifyingSpace ⟶ thinClassifyingSpace` is natural in `C`. -/
@[reassoc (attr := simp)]
theorem fatClassifyingSpaceMap_comp_fatToThinClassifyingSpace
    (Φ : C ⥤ D) (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D =
      fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ := by
  rw [fatClassifyingSpaceMap_eq, fatToThinClassifyingSpace_eq, fatToThinClassifyingSpace_eq,
    thinClassifyingSpaceMap_eq]
  exact SimplicialObject.geometricRealization.map_comp_fatToGeometricRealization
    (topologicalNerveMap Φ hΦ)

/-- A `[0, 1]`-family of functors `Φ s` depending continuously on `(s, a)` induces a homotopy
between the maps of thin classifying spaces induced by `Φ 0` and `Φ 1`. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  SimplicialObject.geometricRealization.homotopy
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun _ ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj hΦ).congr fun _ ↦
      (topologicalNerveMap_app_apply _ _ _ _).symm

theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : ℕ) (F : ComposableArrows C n)
    (t : SimplexCategory.toTop.{max u v}.obj ⦋n⦌) :
    thinClassifyingSpaceHomotopy Φ hΦ
        (s, SimplicialObject.geometricRealization.ι (topologicalNerve C) n (F, t)) =
      SimplicialObject.geometricRealization.ι (topologicalNerve D) n
        (((Φ s).mapComposableArrows n).obj F, t) :=
  (SimplicialObject.geometricRealization.homotopy_apply_ι
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans
    (by rw [topologicalNerveMap_app_apply])

end Functoriality

namespace thinClassifyingSpace

section CoarseSpace

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The augmentation of the full topological nerve of a groupoid by vertex isomorphism classes. -/
def coarseAugmentation :
    topologicalNerve C ⟶ (Functor.const _).obj (TopCat.of (Quotient (isIsomorphicSetoid C))) where
  app _ := TopCat.ofHom ⟨fun F ↦ Quotient.mk _ (F.obj 0), continuous_quot_mk.comp <| by
    simpa only [Function.comp_def, ComposableArrows.totalArrow_left] using
      hs.comp (ComposableArrows.continuous_totalArrow 0 0 le_rfl)⟩
  naturality _ _ f := by
    ext F; exact F.quotient_mk_obj ((SimplexCategory.toCat.map f.unop).toFunctor.obj (0 : Fin _))

@[simp↓]
theorem coarseAugmentation_app_apply (Δ : SimplexCategoryᵒᵖ) (F : (topologicalNerve C).obj Δ) :
    (coarseAugmentation hs).app Δ F = Quotient.mk (isIsomorphicSetoid C) (F.obj 0) := (rfl)

/-- The coarse projection from `thinClassifyingSpace C` to `Quotient (isIsomorphicSetoid C)`. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  SimplicialObject.geometricRealization.augment (coarseAugmentation hs)

theorem coarseMap_eq_augment :
    coarseMap hs = SimplicialObject.geometricRealization.augment (coarseAugmentation hs) := (rfl)

@[simp↓]
theorem coarseMap_ι (n : ℕ) (F : ComposableArrows C n) (t : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    coarseMap hs (SimplicialObject.geometricRealization.ι (topologicalNerve C) n (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (SimplicialObject.geometricRealization.augment_ι (coarseAugmentation hs) n F t).trans
    (coarseAugmentation_app_apply hs (op ⦋n⦌) F)

/-- The coarse projection of `fatClassifyingSpace C` descends along `fatToThinClassifyingSpace`. -/
@[reassoc (attr := simp)]
theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs :=
  fatClassifyingSpace.hom_ext fun m F t ↦
    (congrArg (coarseMap hs) (fatToThinClassifyingSpace_ι m F t)).trans
      ((coarseMap_ι hs _ F t).trans (fatClassifyingSpace.coarseMap_ι hs m F t).symm)

/-- The coarse projection from `thinClassifyingSpace C` is surjective. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) :=
  Function.Surjective.of_comp (g := fatToThinClassifyingSpace C) <| by
    rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
    exact fatClassifyingSpace.coarseMap_surjective hs

/-- With continuous units, `coarseMap` on `thinClassifyingSpace C` is a topological quotient map. -/
theorem isQuotientMap_coarseMap (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)) :
    IsQuotientMap (coarseMap hs) :=
  IsQuotientMap.of_comp (fatToThinClassifyingSpace C).hom.continuous (coarseMap hs).hom.continuous
    (by rw [← TopCat.coe_comp, fatToThinClassifyingSpace_comp_coarseMap]
        exact fatClassifyingSpace.isQuotientMap_coarseMap hs hu)

end CoarseSpace

section TopologicalNerveInstances

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)] (Δ : SimplexCategoryᵒᵖ)

instance [T0Space (Quiver.Total C)] : T0Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T0Space (ComposableArrows C Δ.unop.len))

instance [T1Space (Quiver.Total C)] : T1Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T1Space (ComposableArrows C Δ.unop.len))

instance [T2Space (Quiver.Total C)] : T2Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T2Space (ComposableArrows C Δ.unop.len))

instance [RegularSpace (Quiver.Total C)] : RegularSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (RegularSpace (ComposableArrows C Δ.unop.len))

instance [T3Space (Quiver.Total C)] : T3Space ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (T3Space (ComposableArrows C Δ.unop.len))

instance [CompactSpace (ComposableArrows C Δ.unop.len)] :
    CompactSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (CompactSpace (ComposableArrows C Δ.unop.len))

instance [FirstCountableTopology (Quiver.Total C)] :
    FirstCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (FirstCountableTopology (ComposableArrows C Δ.unop.len))

instance [SecondCountableTopology (Quiver.Total C)] :
    SecondCountableTopology ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (SecondCountableTopology (ComposableArrows C Δ.unop.len))

instance [TopologicalSpace.MetrizableSpace (Quiver.Total C)] :
    TopologicalSpace.MetrizableSpace ((topologicalNerve C).obj Δ) :=
  inferInstanceAs (TopologicalSpace.MetrizableSpace (ComposableArrows C Δ.unop.len))

instance [SecondCountableTopology (Quiver.Total C)] : LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (SimplicialObject.geometricRealization (topologicalNerve C)))

instance [FirstCountableTopology (Quiver.Total C)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  inferInstanceAs
    (UCompactlyGeneratedSpace.{w} (SimplicialObject.geometricRealization (topologicalNerve C)))

end TopologicalNerveInstances

section PointSetTopology

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- When `Quiver.Total C` is `T1`, `thinClassifyingSpace C` is `T1` in its colimit topology. -/
instance instT1Space [T1Space (Quiver.Total C)] : T1Space (thinClassifyingSpace C) :=
  inferInstanceAs (T1Space (SimplicialObject.geometricRealization (topologicalNerve C)))

/-- When `Quiver.Total C` is `T1`, every compact subset of `thinClassifyingSpace C` lies in a single
skeleton stage. -/
theorem exists_subset_range_skeleton_toRealization_of_isCompact [T1Space (Quiver.Total C)]
    {K : Set (thinClassifyingSpace C)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Set.range
      (SimplicialObject.geometricRealization.skeleton.toRealization (topologicalNerve C) n) :=
  SimplicialObject.geometricRealization.exists_subset_range_skeleton_toRealization_of_isCompact
    (topologicalNerve C) hK

/-- When the identity arrows are closed in `Quiver.Total C`, every skeletal stage inclusion into
`thinClassifyingSpace C` is a closed embedding. -/
theorem isClosedEmbedding_skeleton_toRealization
    (hunit : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) (n : ℕ) :
    IsClosedEmbedding
      (SimplicialObject.geometricRealization.skeleton.toRealization (topologicalNerve C) n) :=
  SimplicialObject.geometricRealization.isClosedEmbedding_skeleton_toRealization
    (topologicalNerve C) (fun j ↦ isClosedEmbedding_topologicalNerve_σ hunit j) n

/-- When `Quiver.Total C` is Hausdorff, every skeletal stage inclusion into `thinClassifyingSpace C`
is a closed embedding, with no assumption on identity arrows. -/
theorem isClosedEmbedding_skeleton_toRealization_of_t2Space [T2Space (Quiver.Total C)] (n : ℕ) :
    IsClosedEmbedding
      (SimplicialObject.geometricRealization.skeleton.toRealization (topologicalNerve C) n) :=
  SimplicialObject.geometricRealization.isClosedEmbedding_skeleton_toRealization
    (topologicalNerve C) (fun j ↦ SimplicialObject.isClosedEmbedding_σ (topologicalNerve C) j) n

/-- When `Quiver.Total C` is `T1` and identity arrows are closed, continuous maps from compact
spaces into `thinClassifyingSpace C` factor continuously through a finite skeleton. -/
theorem exists_lift_skeleton_of_compactSpace [T1Space (Quiver.Total C)]
    (hunit : IsClosed (Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C)))
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinClassifyingSpace C)) :
    ∃ (n : ℕ)
      (g' : C(K, (SimplicialObject.geometricRealization.skeleton (topologicalNerve C)).obj n)),
      (SimplicialObject.geometricRealization.skeleton.toRealization (topologicalNerve C) n).hom.comp
        g' = g :=
  SimplicialObject.geometricRealization.exists_lift_skeleton_of_compactSpace
    (topologicalNerve C) (fun j ↦ isClosedEmbedding_topologicalNerve_σ hunit j) g

/-- **Separation of `thinClassifyingSpace C` for second-countable regular arrow spaces.** For any
category whose total arrow space is `T1`, regular, and second-countable (including orbifold, Lie,
and second-countable Hausdorff topological groupoids), `thinClassifyingSpace C` is `T4` — hence
Hausdorff and paracompact — in its colimit topology. -/
instance instT4Space [T1Space (Quiver.Total C)] [RegularSpace (Quiver.Total C)]
    [SecondCountableTopology (Quiver.Total C)] : T4Space (thinClassifyingSpace C) :=
  inferInstanceAs (T4Space (SimplicialObject.geometricRealization (topologicalNerve C)))

/-- **Separation of `thinClassifyingSpace C` for compact Hausdorff categories.** If `Quiver.Total C`
is compact Hausdorff and source, target, units, and composition are continuous, then
`thinClassifyingSpace C` is `T4` in its colimit topology. -/
theorem t4Space_of_compactSpace [TopologicalSpace C] [T2Space (Quiver.Total C)]
    [CompactSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) : T4Space (thinClassifyingSpace C) := by
  have : T2Space C := .of_injective_continuous (fun _ _ h ↦ congrArg Quiver.Total.left h) hu
  have : ∀ n : ℕ, CompactSpace (ComposableArrows C n) :=
    ComposableArrows.compactSpace_of_compactSpace hs hu
      (by simpa only [Quiver.Total.comp_def] using hc) ht
  exact inferInstanceAs (T4Space (SimplicialObject.geometricRealization (topologicalNerve C)))

/-- If `C` is Hausdorff, `Quiver.Total C` is compact, and source, target, units, and composition
are continuous, then `thinClassifyingSpace C` is Lindelöf in its colimit topology. -/
theorem lindelofSpace_of_compactSpace [TopologicalSpace C] [T2Space C]
    [CompactSpace (Quiver.Total C)] (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      p.1.1.comp p.1.2 p.2) : LindelofSpace (thinClassifyingSpace C) := by
  have : ∀ n : ℕ, CompactSpace (ComposableArrows C n) :=
    ComposableArrows.compactSpace_of_compactSpace hs hu
      (by simpa only [Quiver.Total.comp_def] using hc) ht
  exact inferInstanceAs (LindelofSpace (SimplicialObject.geometricRealization (topologicalNerve C)))

end PointSetTopology

section TopologicalGroupoidInstances

variable (C : Type u) [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]

instance instCompactSpaceComposableArrows [T2Space (Quiver.Total C)] [CompactSpace (Quiver.Total C)]
    (n : ℕ) : CompactSpace (ComposableArrows C n) :=
  have : T2Space C := (IsTopologicalGroupoid.isEmbedding_unit C).t2Space
  ComposableArrows.compactSpace_of_compactSpace
    IsTopologicalGroupoid.continuous_source IsTopologicalGroupoid.continuous_unit
    (by simpa only [Quiver.Total.comp_def] using IsTopologicalGroupoid.continuous_comp)
    IsTopologicalGroupoid.continuous_target n

/-- The thin classifying space of any compact Hausdorff topological groupoid is `T4` in its colimit
topology, without second-countability or étaleness. -/
instance instT4SpaceOfCompactSpace [T2Space (Quiver.Total C)] [CompactSpace (Quiver.Total C)] :
    T4Space (thinClassifyingSpace C) :=
  t4Space_of_compactSpace
    IsTopologicalGroupoid.continuous_source IsTopologicalGroupoid.continuous_target
    IsTopologicalGroupoid.continuous_unit IsTopologicalGroupoid.continuous_comp

instance instLindelofSpaceOfCompactSpace [T2Space (Quiver.Total C)]
    [CompactSpace (Quiver.Total C)] : LindelofSpace (thinClassifyingSpace C) :=
  inferInstanceAs (LindelofSpace (SimplicialObject.geometricRealization (topologicalNerve C)))

instance instCompactlyGeneratedSpaceOfCompactSpace [T2Space (Quiver.Total C)]
    [CompactSpace (Quiver.Total C)] : CompactlyGeneratedSpace (thinClassifyingSpace C) :=
  inferInstanceAs
    (CompactlyGeneratedSpace (SimplicialObject.geometricRealization (topologicalNerve C)))

end TopologicalGroupoidInstances

end thinClassifyingSpace

namespace OneObjectGroupoid

variable (G : Type u) [TopologicalSpace G]

instance [T2Space G] : T2Space (Quiver.Total (SingleObj G)) := (arrowHomeomorph G).symm.t2Space

instance [RegularSpace G] : RegularSpace (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).isEmbedding.regularSpace

instance [CompactSpace G] : CompactSpace (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).symm.compactSpace

instance [FirstCountableTopology G] : FirstCountableTopology (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).isEmbedding.firstCountableTopology

instance [SecondCountableTopology G] : SecondCountableTopology (Quiver.Total (SingleObj G)) :=
  (arrowHomeomorph G).isEmbedding.secondCountableTopology

end OneObjectGroupoid

end TauCeti

namespace CategoryTheory.ObjectProperty

section GeneralCategory

variable {C : Type u} [Category.{v} C] [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C)

/-- Inclusion of any full subcategory induces an injection on thin classifying spaces. -/
theorem thinClassifyingSpaceMap_ι_injective :
    Function.Injective (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  SimplicialObject.geometricRealization.map_injective fun _ ↦ by
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact (ComposableArrows.isEmbedding_mapComposableArrows_obj
      TauCeti.isEmbedding_total_fullSubcategory).injective

/-- Inclusion of a closed full subcategory induces a closed embedding on thin classifying spaces. -/
theorem isClosedEmbedding_thinClassifyingSpaceMap_ι [TopologicalSpace C]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C)) (hP : IsClosed {x | P x}) :
    IsClosedEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  SimplicialObject.geometricRealization.isClosedEmbedding_map fun n ↦ by
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact P.isClosedEmbedding_mapComposableArrows_ι hs hP n

end GeneralCategory

section SaturatedGroupoid

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)] (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- On `SimplexCategoryᵒᵖ`, the restricted nerve of a saturated full subgroupoid is the preimage of
the coarse image of `P` in every degree. -/
theorem range_topologicalNerveMap_ι_full (Δ : SimplexCategoryᵒᵖ) :
    range ((TauCeti.topologicalNerveMap P.ι P.continuous_mapTotal_ι).app Δ) =
      (TauCeti.thinClassifyingSpace.coarseAugmentation hs).app Δ ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) := by
  rw [TauCeti.coe_topologicalNerveMap_app]
  refine (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms _).trans ?_
  ext F; refine ⟨fun hF ↦ ⟨F.obj 0, hF, rfl⟩, ?_⟩
  rintro ⟨x, hx, h⟩
  obtain ⟨e⟩ := _root_.Quotient.exact
    (h.trans (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs Δ F))
  exact P.prop_of_iso e hx

include hs in
/-- The inclusion of a saturated open full subgroupoid induces an open embedding on thin classifying
spaces. -/
theorem isOpenEmbedding_thinClassifyingSpaceMap_ι (hP : IsOpen {x | P x}) :
    IsOpenEmbedding (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  SimplicialObject.geometricRealization.isOpenEmbedding_map_of_range_eq_preimage
    (ε := TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (V := _root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
    (fun n ↦ by
      rw [TauCeti.coe_topologicalNerveMap_app]
      exact P.isOpenEmbedding_mapComposableArrows_ι hs hP n)
    (fun n ↦ P.range_topologicalNerveMap_ι_full hs (op ⦋n⦌))

/-- The preimage of a saturated coarse subset in `thinClassifyingSpace C` is the image of the thin
classifying space of the corresponding full restriction. -/
theorem preimage_thinCoarseMap_eq_range_thinClassifyingSpaceMap_ι :
    TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) :=
  SimplicialObject.geometricRealization.preimage_augment_eq_range_map
    (ε := TauCeti.thinClassifyingSpace.coarseAugmentation hs)
    (fun n ↦ P.range_topologicalNerveMap_ι_full hs (op ⦋n⦌))

/-- The thin classifying space of a saturated open full subgroupoid is homeomorphic to the
corresponding coarse-map preimage in `thinClassifyingSpace C`. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_thinCoarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

@[simp↓]
theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (_root_.Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).apply_symm_apply z)

end SaturatedGroupoid

end CategoryTheory.ObjectProperty

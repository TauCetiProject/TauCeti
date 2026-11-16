/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialObject.Realization.Skeleton
public import TauCeti.Topology.CategoryTheory.CoarseSpace.Restrict
public import TauCeti.Topology.CategoryTheory.ComposableArrows

/-!
# The thin classifying space of a topological category

For a category `C` whose total arrow space `Quiver.Total C` carries a topology, its *thin
classifying space* `TauCeti.thinClassifyingSpace C` is the thin geometric realization
`TauCeti.thinRealization (TauCeti.topologicalNerve C)`.

## Main definitions and results

* `TauCeti.thinClassifyingSpace`, `TauCeti.thinClassifyingSpaceMap`,
  `TauCeti.thinClassifyingSpaceHomotopy`: the thin classifying space and its functoriality and
  homotopies induced by continuous families of functors.
* `TauCeti.fatToThinClassifyingSpace`: the natural quotient map
  `‖C‖ = fatClassifyingSpace C ⟶ thinClassifyingSpace C = |C|`, commuting with the coarse
  projections.
* `TauCeti.thinClassifyingSpace.coarseMap`: for a groupoid with continuous source, the coarse
  projection `B_top(C) → |C|` to the orbit space of isomorphism classes, which is a quotient map
  when units are continuous (`TauCeti.thinClassifyingSpace.isQuotientMap_coarseMap`).
* `CategoryTheory.ObjectProperty.isOpenEmbedding_thinClassifyingSpaceMap_ι`,
  `CategoryTheory.ObjectProperty.isClosedEmbedding_thinClassifyingSpaceMap_ι`,
  `CategoryTheory.ObjectProperty.thinClassifyingSpaceRestrictionHomeomorph`: saturated open and
  closed restrictions of `B_top(C)` identify with preimages under the coarse map.
* `TauCeti.thinClassifyingSpace.t4Space_of_secondCountable`,
  `TauCeti.thinClassifyingSpace.paracompactSpace_of_secondCountable`,
  `TauCeti.thinClassifyingSpace.uCompactlyGeneratedSpace_of_secondCountable`: for a second-countable
  regular `T1` total arrow space, `B_top(C)` is `T4` (Hausdorff), paracompact, and compactly
  generated.
* `TauCeti.thinClassifyingSpace.t4Space_of_compact`,
  `TauCeti.thinClassifyingSpace.paracompactSpace_of_compact`,
  `TauCeti.thinClassifyingSpace.compactlyGeneratedSpace_of_compact`: for a compact Hausdorff total
  arrow space with continuous structure maps, `B_top(C)` is `T4` (Hausdorff), paracompact, and
  compactly generated.
* `TauCeti.thinClassifyingSpace.exists_subset_range_skeleton_of_isCompact`,
  `TauCeti.thinClassifyingSpace.exists_lift_skeleton_of_compactSpace`: when `Quiver.Total C` is
  Hausdorff, every compact subset (and every map from a compact space) factors through a single
  finite skeleton of `B_top(C)`.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112.
* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 4.
-/

public noncomputable section

open CategoryTheory Opposite Set Topology

open scoped Simplicial

universe v u w

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
      (t : SimplexCategory.toTop.{max u v}.obj n),
        g (thinRealization.ι _ n (F, t)) = h (thinRealization.ι _ n (F, t))) : g = h :=
  thinRealization.hom_ext _ H

variable {D : Type u} [Category.{v} D] [TopologicalSpace (Quiver.Total D)]

/-- The map of thin classifying spaces induced by a functor that is continuous on total arrows. -/
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
    (t : SimplexCategory.toTop.{max u v}.obj n) :
    thinClassifyingSpaceMap Φ hΦ (thinRealization.ι _ n (F, t)) =
      thinRealization.ι _ n ((Φ.mapComposableArrows _).obj F, t) :=
  (thinRealization.map_ι (topologicalNerveMap Φ hΦ) n F t).trans <|
    congrArg (fun F ↦ thinRealization.ι _ n (F, t))
      (topologicalNerveMap_app_apply Φ hΦ (op n) F)

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
  (congrArg thinRealization.map (topologicalNerveMap_id C)).trans thinRealization.map_id

theorem thinClassifyingSpaceMap_comp {E : Type u} [Category.{v} E]
    [TopologicalSpace (Quiver.Total E)] (Φ : C ⥤ D) (Ψ : D ⥤ E)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) (hΨ : Continuous Ψ.toPrefunctor.mapTotal) :
    thinClassifyingSpaceMap (Φ ⋙ Ψ) (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸
        hΨ.comp hΦ) =
      thinClassifyingSpaceMap Φ hΦ ≫ thinClassifyingSpaceMap Ψ hΨ :=
  (congrArg thinRealization.map (topologicalNerveMap_comp Φ Ψ hΦ hΨ)).trans
    (thinRealization.map_comp (topologicalNerveMap Φ hΦ) (topologicalNerveMap Ψ hΨ))

/-- A continuous family of functors `Φ s`, `s ∈ [0, 1]`, induces a homotopy between the maps on
thin classifying spaces induced by `Φ 0` and `Φ 1`. -/
def thinClassifyingSpaceHomotopy (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2) :
    ContinuousMap.Homotopy (thinClassifyingSpaceMap (Φ 0) (hΦ.comp (.prodMk_right 0))).hom
      (thinClassifyingSpaceMap (Φ 1) (hΦ.comp (.prodMk_right 1))).hom :=
  thinRealization.homotopy
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s)))
    fun n ↦ (ComposableArrows.continuous_uncurry_mapComposableArrows_obj (n := n.len) hΦ).congr
      fun ⟨s, F⟩ ↦ (topologicalNerveMap_app_apply (Φ s) _ (op n) F).symm

theorem thinClassifyingSpaceHomotopy_apply_ι (Φ : unitInterval → C ⥤ D)
    (hΦ : Continuous fun p : unitInterval × Quiver.Total C ↦ (Φ p.1).toPrefunctor.mapTotal p.2)
    (s : unitInterval) (n : SimplexCategory) (F : ComposableArrows C n.len)
    (t : SimplexCategory.toTop.{max u v}.obj n) :
    thinClassifyingSpaceHomotopy Φ hΦ (s, thinRealization.ι _ n (F, t)) =
      thinRealization.ι _ n (((Φ s).mapComposableArrows _).obj F, t) :=
  (thinRealization.homotopy_apply_ι
    (fun s ↦ topologicalNerveMap (Φ s) (hΦ.comp (.prodMk_right s))) _ s n F t).trans <|
    congrArg (fun F ↦ thinRealization.ι _ n (F, t))
      (topologicalNerveMap_app_apply (Φ s) _ (op n) F)

variable (C) in
/-- The canonical quotient map from the fat classifying space to the thin classifying space. -/
def fatToThinClassifyingSpace : fatClassifyingSpace C ⟶ thinClassifyingSpace C :=
  thinRealization.fatToThin (topologicalNerve C)

theorem fatToThinClassifyingSpace_ι (n : SemiSimplexCategory)
    (F : ComposableArrows C (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatToThinClassifyingSpace C (fatRealization.ι _ n (F, t)) =
      thinRealization.ι _ (SemiSimplexCategory.toSimplexCategory.obj n) (F, t) :=
  thinRealization.fatToThin_ι (topologicalNerve C) n F t

variable (C) in
/-- The canonical map from the fat classifying space to the thin classifying space is a quotient
map. -/
theorem isQuotientMap_fatToThinClassifyingSpace :
    IsQuotientMap (fatToThinClassifyingSpace C) :=
  thinRealization.isQuotientMap_fatToThin (topologicalNerve C)

/-- The fat-to-thin comparison map is natural in functors continuous on total arrows. -/
@[reassoc (attr := simp)]
theorem fatToThinClassifyingSpace_naturality (Φ : C ⥤ D)
    (hΦ : Continuous Φ.toPrefunctor.mapTotal) :
    fatClassifyingSpaceMap Φ hΦ ≫ fatToThinClassifyingSpace D =
      fatToThinClassifyingSpace C ≫ thinClassifyingSpaceMap Φ hΦ := by
  rw [fatClassifyingSpaceMap_eq, thinClassifyingSpaceMap_eq]
  exact thinRealization.fatToThin_naturality (topologicalNerveMap Φ hΦ)

end Basic

/-! ### Coarse projection -/

namespace thinClassifyingSpace

section Coarse

variable {C : Type u} [Category.{u} C] [IsGroupoid C] [TopologicalSpace C]
  [TopologicalSpace (Quiver.Total C)]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The augmentation of the topological nerve of a groupoid by the isomorphism class of a vertex. -/
def coarseAugmentation :
    topologicalNerve C ⟶
      (Functor.const _).obj (TopCat.of (Quotient (isIsomorphicSetoid C))) where
  app _ := TopCat.ofHom ⟨fun F ↦ Quotient.mk _ (F.obj 0), by
    apply continuous_quot_mk.comp
    simpa only [Function.comp_def, ComposableArrows.totalArrow_left] using
      hs.comp (ComposableArrows.continuous_totalArrow 0 0 le_rfl)⟩
  naturality _ _ f := by
    ext F
    exact F.quotient_mk_obj ((SimplexCategory.toCat.map f.unop).toFunctor.obj (0 : Fin (_ + 1)))

/-- The coarse augmentation reads the isomorphism class of the first vertex. -/
@[simp↓]
theorem coarseAugmentation_app_apply (m : SimplexCategoryᵒᵖ)
    (F : (topologicalNerve C).obj m) :
    (coarseAugmentation hs).app m F = Quotient.mk (isIsomorphicSetoid C) (F.obj 0) := (rfl)

/-- The coarse projection from the thin classifying space to the orbit space of objects. -/
def coarseMap : thinClassifyingSpace C ⟶ TopCat.of (Quotient (isIsomorphicSetoid C)) :=
  thinRealization.augment (coarseAugmentation hs)

/-- The coarse projection is induced by the coarse augmentation of the topological nerve. -/
theorem coarseMap_eq_augment :
    coarseMap hs = thinRealization.augment (coarseAugmentation hs) := (rfl)

/-- A point of a simplex projects to the isomorphism class of its first vertex. -/
@[simp↓]
theorem coarseMap_ι (m : SimplexCategory) (F : ComposableArrows C m.len)
    (t : SimplexCategory.toTop.{u}.obj m) :
    coarseMap hs (thinRealization.ι _ m (F, t)) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) :=
  (thinRealization.augment_ι (coarseAugmentation hs) m F t).trans
    (coarseAugmentation_app_apply hs (op m) F)

/-- Every orbit occurs as the coarse projection of a vertex in `B_top(C)`. -/
theorem coarseMap_surjective : Function.Surjective (coarseMap hs) := by
  refine Quotient.ind fun x ↦ ?_
  obtain ⟨t⟩ : Nonempty (SimplexCategory.toTop.{u}.obj ⦋0⦌) := inferInstance
  exact ⟨thinRealization.ι _ ⦋0⦌ (ComposableArrows.mk₀ x, t), coarseMap_ι hs _ _ _⟩

/-- With continuous units, the coarse projection `B_top(C) → |C|` is a quotient map. -/
theorem isQuotientMap_coarseMap
    (hu : Continuous (fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))) :
    IsQuotientMap (coarseMap hs) := by
  have h₀ : Continuous (ComposableArrows.mk₀ : C → ComposableArrows C 0) := by
    apply ComposableArrows.continuous_iff.mpr
    intro i j hij
    simpa [ComposableArrows.totalArrow_def, ComposableArrows.mk₀] using hu
  apply thinRealization.isQuotientMap_augment (coarseAugmentation hs) ⦋0⦌
  have heq : ((coarseAugmentation hs).app (op ⦋0⦌)) ∘
      ComposableArrows.mk₀ = Quotient.mk (isIsomorphicSetoid C) :=
    funext fun x ↦ coarseAugmentation_app_apply hs _ _
  exact IsQuotientMap.of_comp h₀ ((coarseAugmentation hs).app _).hom.continuous
    (heq.symm ▸ isQuotientMap_quot_mk)

/-- The fat-to-thin comparison commutes with the coarse projections. -/
@[reassoc (attr := simp)]
theorem fatToThinClassifyingSpace_comp_coarseMap :
    fatToThinClassifyingSpace C ≫ coarseMap hs = fatClassifyingSpace.coarseMap hs :=
  fatClassifyingSpace.hom_ext fun n F t ↦
    (congrArg (coarseMap hs) (fatToThinClassifyingSpace_ι n F t)).trans <|
      (coarseMap_ι hs (SemiSimplexCategory.toSimplexCategory.obj n) F t).trans
        (fatClassifyingSpace.coarseMap_ι hs n F t).symm

end Coarse

/-! ### Point-set topology of the thin classifying space -/

section Topology

variable (C : Type u) [Category.{v} C] [TopologicalSpace (Quiver.Total C)]

/-- When `Quiver.Total C` is second-countable, regular, and `T1` (in particular for a Hausdorff
second-countable manifold of arrows), `B_top(C)` is `T4` (normal and `T1`, hence Hausdorff). -/
theorem t4Space_of_secondCountable [RegularSpace (Quiver.Total C)] [T1Space (Quiver.Total C)]
    [SecondCountableTopology (Quiver.Total C)] : T4Space (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, RegularSpace ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (RegularSpace (ComposableArrows C n))
  have : ∀ n : ℕ, T1Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T1Space (ComposableArrows C n))
  have : ∀ n : ℕ, SecondCountableTopology ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (SecondCountableTopology (ComposableArrows C n))
  have : ∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  thinRealization.t4Space_of_regularSpace_lindelofSpace (topologicalNerve C)

/-- When `Quiver.Total C` is second-countable, regular, and `T1`, `B_top(C)` is paracompact. -/
theorem paracompactSpace_of_secondCountable [RegularSpace (Quiver.Total C)]
    [T1Space (Quiver.Total C)] [SecondCountableTopology (Quiver.Total C)] :
    ParacompactSpace (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, RegularSpace ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (RegularSpace (ComposableArrows C n))
  have : ∀ n : ℕ, T1Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T1Space (ComposableArrows C n))
  have : ∀ n : ℕ, SecondCountableTopology ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (SecondCountableTopology (ComposableArrows C n))
  have : ∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  thinRealization.paracompactSpace_of_regularSpace_lindelofSpace (topologicalNerve C)

/-- When `Quiver.Total C` is first-countable (in particular second-countable), `B_top(C)` is
compactly generated in every universe `w`. -/
theorem uCompactlyGeneratedSpace_of_firstCountable [FirstCountableTopology (Quiver.Total C)] :
    UCompactlyGeneratedSpace.{w} (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, FirstCountableTopology ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (FirstCountableTopology (ComposableArrows C n))
  thinRealization.uCompactlyGeneratedSpace_of_firstCountable (topologicalNerve C)

/-- When `Quiver.Total C` is compact Hausdorff and source, target, units and composition are
continuous, `B_top(C)` is `T4` (hence Hausdorff). -/
theorem t4Space_of_compact [TopologicalSpace C] [CompactSpace (Quiver.Total C)]
    [T2Space (Quiver.Total C)]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C)) :
    T4Space (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, CompactSpace ((topologicalNerve C) _⦋n⦌) :=
    ComposableArrows.compactSpace hs ht hu hc
  have : ∀ n : ℕ, T2Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T2Space (ComposableArrows C n))
  have : ∀ n : ℕ, T1Space ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  have : ∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  have : ∀ n : ℕ, RegularSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  thinRealization.t4Space_of_regularSpace_lindelofSpace (topologicalNerve C)

/-- When `Quiver.Total C` is compact Hausdorff and source, target, units and composition are
continuous, `B_top(C)` is paracompact. -/
theorem paracompactSpace_of_compact [TopologicalSpace C] [CompactSpace (Quiver.Total C)]
    [T2Space (Quiver.Total C)]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C)) :
    ParacompactSpace (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, CompactSpace ((topologicalNerve C) _⦋n⦌) :=
    ComposableArrows.compactSpace hs ht hu hc
  have : ∀ n : ℕ, T2Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T2Space (ComposableArrows C n))
  have : ∀ n : ℕ, T1Space ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  have : ∀ n : ℕ, LindelofSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  have : ∀ n : ℕ, RegularSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  thinRealization.paracompactSpace_of_regularSpace_lindelofSpace (topologicalNerve C)

/-- When `Quiver.Total C` is compact Hausdorff and source, target, units and composition are
continuous, `B_top(C)` is compactly generated. -/
theorem compactlyGeneratedSpace_of_compact [TopologicalSpace C] [CompactSpace (Quiver.Total C)]
    [T2Space (Quiver.Total C)]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : Continuous (Quiver.Total.right : Quiver.Total C → C))
    (hu : Continuous fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C))
    (hc : Continuous fun p : {p : Quiver.Total C × Quiver.Total C // p.1.right = p.2.left} ↦
      (⟨p.1.1.left, p.1.2.right, p.1.1.hom ≫ eqToHom p.2 ≫ p.1.2.hom⟩ : Quiver.Total C)) :
    CompactlyGeneratedSpace (thinClassifyingSpace C) :=
  have : ∀ n : ℕ, CompactSpace ((topologicalNerve C) _⦋n⦌) :=
    ComposableArrows.compactSpace hs ht hu hc
  have : ∀ n : ℕ, T2Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T2Space (ComposableArrows C n))
  have : ∀ n : ℕ, WeaklyLocallyCompactSpace ((topologicalNerve C) _⦋n⦌) := fun _ ↦ inferInstance
  thinRealization.compactlyGeneratedSpace_of_weaklyLocallyCompact (topologicalNerve C)

/-- When `Quiver.Total C` is Hausdorff, every compact subset of `B_top(C)` lies in a single finite
skeleton. -/
theorem exists_subset_range_skeleton_of_isCompact [T2Space (Quiver.Total C)]
    {K : Set (thinClassifyingSpace C)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ range ((thinRealization.skeletonCocone (topologicalNerve C)).ι.app n) :=
  have : ∀ n : ℕ, T2Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T2Space (ComposableArrows C n))
  thinRealization.exists_subset_range_skeleton_of_isCompact_of_t2Space (topologicalNerve C) hK

/-- When `Quiver.Total C` is Hausdorff, every continuous map from a compact space into `B_top(C)`
factors continuously through a single finite skeleton. -/
theorem exists_lift_skeleton_of_compactSpace [T2Space (Quiver.Total C)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinClassifyingSpace C)) :
    ∃ (n : ℕ) (g' : C(K, thinRealization.skeleton (topologicalNerve C) n)),
      ((thinRealization.skeletonCocone (topologicalNerve C)).ι.app n).hom.comp g' = g :=
  have : ∀ n : ℕ, T2Space ((topologicalNerve C) _⦋n⦌) :=
    fun n ↦ inferInstanceAs (T2Space (ComposableArrows C n))
  thinRealization.exists_lift_skeleton_of_compactSpace_of_t2Space (topologicalNerve C) g

end Topology

end thinClassifyingSpace

end TauCeti

/-! ### Saturated open and closed restrictions -/

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{u} C] [IsGroupoid C]
  [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]
  (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
  (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))

/-- The restricted nerve is exactly the part over the image of a saturated object set in the coarse
space, in every simplicial degree. -/
theorem range_topologicalNerveMap_ι_eq_preimage (m : SimplexCategoryᵒᵖ) :
    range ((TauCeti.topologicalNerveMap P.ι P.continuous_mapTotal_ι).app m) =
      (TauCeti.thinClassifyingSpace.coarseAugmentation hs).app m ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) := by
  rw [TauCeti.coe_topologicalNerveMap_app]
  refine (P.range_mapComposableArrows_ι_of_isClosedUnderIsomorphisms _).trans ?_
  ext F
  constructor
  · intro hF
    exact ⟨F.obj 0, hF,
      (TauCeti.thinClassifyingSpace.coarseAugmentation_app_apply hs m F).symm⟩
  · rintro ⟨x, hx, h⟩
    obtain ⟨e⟩ := Quotient.exact
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
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
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
    (V := Quotient.mk (isIsomorphicSetoid C) '' {x | P x})
  · intro m
    rw [TauCeti.coe_topologicalNerveMap_app]
    exact P.isClosedEmbedding_mapComposableArrows_ι hs hP _
  · exact P.range_topologicalNerveMap_ι_eq_preimage hs

/-- The preimage of a saturated coarse subset under the thin coarse projection is the image of
the thin classifying space of its full restriction. -/
theorem preimage_thinCoarseMap_eq_range_thinClassifyingSpaceMap_ι :
    TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x}) =
      range (TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι) := by
  rw [TauCeti.thinClassifyingSpace.coarseMap_eq_augment, TauCeti.thinClassifyingSpaceMap_eq]
  exact TauCeti.thinRealization.preimage_augment_eq_range_map _
    (P.range_topologicalNerveMap_ι_eq_preimage hs)

/-- The thin classifying space of a saturated open restriction is homeomorphic to the coarse-map
preimage, with its subspace topology. -/
def thinClassifyingSpaceRestrictionHomeomorph (hP : IsOpen {x | P x}) :
    TauCeti.thinClassifyingSpace P.FullSubcategory ≃ₜ
      (TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
        (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :=
  (P.isOpenEmbedding_thinClassifyingSpaceMap_ι hs hP).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (P.preimage_thinCoarseMap_eq_range_thinClassifyingSpaceMap_ι hs).symm)

/-- The restriction homeomorphism is induced by the inclusion functor. -/
@[simp↓]
theorem thinClassifyingSpaceRestrictionHomeomorph_apply_val (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace P.FullSubcategory) :
    (P.thinClassifyingSpaceRestrictionHomeomorph hs hP z).val =
      TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι z := (rfl)

/-- Mapping the inverse restriction homeomorphism back by inclusion recovers the point of the
coarse-map preimage. -/
@[simp↓]
theorem thinClassifyingSpaceMap_ι_thinClassifyingSpaceRestrictionHomeomorph_symm_apply
    (hP : IsOpen {x | P x})
    (z : TauCeti.thinClassifyingSpace.coarseMap hs ⁻¹'
      (Quotient.mk (isIsomorphicSetoid C) '' {x | P x})) :
    TauCeti.thinClassifyingSpaceMap P.ι P.continuous_mapTotal_ι
      ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).symm z) = z.val :=
  congrArg Subtype.val ((P.thinClassifyingSpaceRestrictionHomeomorph hs hP).apply_symm_apply z)

end CategoryTheory.ObjectProperty

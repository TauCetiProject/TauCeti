/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core.Basic
public import TauCeti.Topology.VectorBundle.Descent
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Basic

/-!
# The category of finite-rank point-indexed vector-bundle cores

`FiniteRankBundleCore 𝕜 B` stores a natural-number rank and a Mathlib `VectorBundleCore`
with model `Fin rank → 𝕜`, indexed by the base points, with the chart at `x` labelled by `x`.
Its morphisms are `VectorBundleCore.CoordinateHom`: continuous chart operators satisfying
transition compatibility, hence actual continuous fibrewise linear maps of the reconstructed
bundles. Addition of chart operators makes this category preadditive. Every rank-zero core,
in particular the trivial one, is a zero object. No nonemptiness or separation assumption on
the base is required.

Objects here have constant rank. They provide the constituent categories on the clopen rank
strata of a variable-rank bundle; no boundedness assertion about variable ranks is made.
For real or complex scalars and `B : Type u`, both the objects and the morphisms live in
`Type u`, independently of the universe of any original bundle's fibres.
`ofBundle` obtains such an object from an actual bundle with the prescribed model by using
`TauCeti.pointIndexedCore`; its reconstruction comparison is
`TauCeti.pointIndexedCoreHomeomorph`.

`fiberFunctor x` evaluates at a base point as a Mathlib module. The family of these functors
jointly detects equality of morphisms. Over a complete scalar field, `isIso_iff_bijective`
characterizes categorical isomorphisms exactly by fibrewise bijectivity: continuous inversion
in finite-dimensional charts supplies the inverse bundle morphism. Consequently a continuous
family of fibrewise linear equivalences between two cores yields an isomorphism
(`isoOfContinuousEquiv`), and `ofBundleIso` together with
`exists_continuousLinearEquiv_of_ofBundle_iso` (which needs no completeness assumption) relates
isomorphisms between `ofBundle 𝕜 n E₀` and `ofBundle 𝕜 n E₁` to continuous families of fibrewise
continuous linear equivalences.

Between two cores with the same chart domains, a fixed coordinate operator intertwining their
transition maps is a bundle map with that operator on every fibre (`constHom`), and a fixed
intertwining coordinate equivalence is an isomorphism (`constIso`).

Over any nontrivially normed field `𝕜` (without completeness), a family of fibrewise linear maps
between finite-rank cores is a continuous section of the Hom bundle if and only if it induces a
continuous map on total spaces (`continuous_hom_bundle_core_iff`), giving total-space constructors
for bundle morphisms (`ofTotalSpaceContinuous`) and isomorphisms (`isoOfTotalSpaceContinuous`).

A map into the total space of `trivial 𝕜 B n` is continuous exactly when its base point and its
coordinate vector in `Fin n → 𝕜` are (`continuous_trivial_iff`). Hence bundle maps into a trivial
core are exactly the fibrewise linear maps to `Fin n → 𝕜` that are continuous on the source total
space: `continuous_fiberMap_trivial` gives one direction, and over a complete scalar field
`toTrivial` gives the other.

The construction uses Mathlib's vector-bundle cores and preadditive-category interfaces,
and the coordinate descent and Hom-bundle inversion API in the imported modules.
-/

public section

open Bundle CategoryTheory CategoryTheory.Limits VectorBundleCore

namespace TauCeti

universe u v

variable (𝕜 : Type v) [NontriviallyNormedField 𝕜] (B : Type u) [TopologicalSpace B]

/-- A constant finite-rank vector bundle presented by point-indexed coordinate data.
The selected chart at each base point is the chart with that label. -/
structure FiniteRankBundleCore where
  /-- The dimension of each fibre. -/
  rank : ℕ
  /-- The actual Mathlib coordinate core. -/
  core : VectorBundleCore 𝕜 B (Fin rank → 𝕜) B
  /-- The chosen chart at a point is labelled by that point. -/
  indexAt_eq : ∀ x, core.indexAt x = x

namespace FiniteRankBundleCore

variable {𝕜 B}

/-- To prove a property of point-indexed cores, one may assume the chosen index function
is definitionally the identity. This avoids unpacking the fields of `VectorBundleCore`. -/
@[elab_as_elim] theorem induction_on {motive : FiniteRankBundleCore 𝕜 B → Prop}
    (A : FiniteRankBundleCore 𝕜 B)
    (h : ∀ (n : ℕ) (c : VectorBundleCore 𝕜 B (Fin n → 𝕜) B)
      (hc : ∀ x, c.indexAt x = x),
      motive ⟨n,
        { c with
          indexAt := id
          mem_baseSet_at := fun x => by simpa only [id_eq, hc] using c.mem_baseSet_at x },
        fun _ => rfl⟩) : motive A := by
  rcases A with ⟨n, c, hc⟩
  have hi : c.indexAt = id := funext hc
  have hm := h n c hc
  cases c
  cases hi
  exact hm

/-- The transition from a point's own chart to itself is the identity. -/
@[simp] theorem coordChange_self (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    A.core.coordChange x x x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [A.indexAt_eq, ContinuousLinearMap.id_apply] using
    A.core.coordChange_self (A.core.indexAt x) x (A.core.mem_baseSet_at x) v

/-- The preferred trivialization of `A.core` at `x` is the chart `A.core.localTriv x`. -/
theorem trivializationAt_core (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    trivializationAt (Fin A.rank → 𝕜) A.core.Fiber x = A.core.localTriv x := by
  rw [A.core.trivializationAt, ← A.core.localTrivAt_def, A.indexAt_eq]

/-- Expressing a fibre map between point-indexed cores in charts `i` and `j` conjugates by the
transitions through `x` without mentioning `indexAt`. -/
theorem inChartCoordinates_core (A D : FiniteRankBundleCore 𝕜 B) (i j x : B)
    (ϕ : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :
    A.core.inChartCoordinates D.core i j x ϕ =
      (D.core.coordChange x j x).comp (ϕ.comp (A.core.coordChange i x x)) := by
  apply ContinuousLinearMap.ext
  intro u
  rw [inChartCoordinates_apply, A.indexAt_eq, D.indexAt_eq,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]

/-- Pointwise form of `inChartCoordinates_core`. -/
theorem inChartCoordinates_core_apply (A D : FiniteRankBundleCore 𝕜 B) (i j x : B)
    (ϕ : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) (u : Fin A.rank → 𝕜) :
    A.core.inChartCoordinates D.core i j x ϕ u =
      D.core.coordChange x j x (ϕ (A.core.coordChange i x x u)) := by
  rw [inChartCoordinates_apply, A.indexAt_eq, D.indexAt_eq]

/-- The category of point-indexed finite-rank cores, with genuine coordinate bundle morphisms. -/
instance : Category (FiniteRankBundleCore 𝕜 B) where
  Hom A D := CoordinateHom A.core D.core
  id A := CoordinateHom.id A.core
  comp f g := g.comp f
  id_comp := CoordinateHom.comp_id
  comp_id := CoordinateHom.id_comp
  assoc f g h := (CoordinateHom.comp_assoc h g f).symm

variable {A D C : FiniteRankBundleCore 𝕜 B}

/-- Morphisms are determined by their linear maps on all fibres. -/
@[ext] theorem hom_ext {f g : A ⟶ D} (h : ∀ x, f.fiberMap x = g.fiberMap x) : f = g :=
  CoordinateHom.fiberMap_injective (funext h)

@[simp] theorem fiberMap_id (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (𝟙 A : A ⟶ A).fiberMap x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜) :=
  CoordinateHom.fiberMap_id A.core x

@[simp] theorem fiberMap_comp (f : A ⟶ D) (g : D ⟶ C) (x : B) :
    (f ≫ g).fiberMap x = (g.fiberMap x).comp (f.fiberMap x) :=
  CoordinateHom.fiberMap_comp g f x

/-- Evaluating the fibre map of `eqToHom h` casts the coordinate index along the rank equality. -/
@[simp] theorem fiberMap_eqToHom_apply (h : A = D) (x : B)
    (v : Fin A.rank → 𝕜) (i : Fin D.rank) :
    (eqToHom h).fiberMap x v i = v (Fin.cast (congrArg rank h).symm i) := by
  subst h
  simp only [eqToHom_refl, fiberMap_id, ContinuousLinearMap.id_apply, Fin.cast_refl, id_eq]

/-- Each point lies in the chart labelled by itself. -/
theorem mem_baseSet_self (A : FiniteRankBundleCore 𝕜 B) (x : B) : x ∈ A.core.baseSet x := by
  simpa only [A.indexAt_eq] using A.core.mem_baseSet_at x

/-- At the charts labelled by a point, the chart operator of a morphism is its fibre map. -/
theorem operator_self (f : A ⟶ D) (x : B) :
    f.operator x x ⟨x, A.mem_baseSet_self x, D.mem_baseSet_self x⟩ = f.fiberMap x := by
  rw [CoordinateHom.operator_eq]
  ext v
  simp only [inChartCoordinates_apply, A.indexAt_eq, D.indexAt_eq, coordChange_self,
    ContinuousLinearMap.id_apply]

/-- Pointwise addition of coordinate bundle maps makes the category preadditive. -/
instance : Preadditive (FiniteRankBundleCore 𝕜 B) where
  homGroup A D := inferInstanceAs (AddCommGroup (CoordinateHom A.core D.core))
  add_comp _ _ _ f g h := CoordinateHom.comp_add h f g
  comp_add _ _ _ f g h := CoordinateHom.add_comp g h f

@[simp] theorem fiberMap_add (f g : A ⟶ D) (x : B) :
    (f + g).fiberMap x = f.fiberMap x + g.fiberMap x :=
  CoordinateHom.fiberMap_add f g x

@[simp] theorem fiberMap_neg (f : A ⟶ D) (x : B) :
    (-f).fiberMap x = -f.fiberMap x :=
  CoordinateHom.fiberMap_neg f x

/-- Fibre evaluation commutes with finite sums of bundle morphisms. -/
@[simp] theorem fiberMap_sum {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ D)) (x : B) :
    (∑ i ∈ s, f i).fiberMap x = ∑ i ∈ s, (f i).fiberMap x :=
  map_sum
    ({ toFun := fun g : A ⟶ D ↦ g.fiberMap x
       map_zero' := CoordinateHom.fiberMap_zero x
       map_add' := fun g h ↦ fiberMap_add g h x } : (A ⟶ D) →+ _)
    f s

/-- Evaluate a coordinate bundle and its morphisms on the fibre at `x`. -/
@[expose, simps obj]
def fiberFunctor (x : B) : FiniteRankBundleCore 𝕜 B ⥤ ModuleCat 𝕜 where
  obj A := ModuleCat.of 𝕜 (Fin A.rank → 𝕜)
  map f := ModuleCat.ofHom (f.fiberMap x).toLinearMap
  map_id A := by ext v; simp
  map_comp f g := by ext v; simp

@[simp] theorem fiberFunctor_map_apply (x : B) (f : A ⟶ D) (v : Fin A.rank → 𝕜) :
    (fiberFunctor (𝕜 := 𝕜) x).map f v = f.fiberMap x v := (rfl)

/-- Fibre evaluation preserves addition of bundle maps. -/
instance (x : B) : (fiberFunctor (𝕜 := 𝕜) x).Additive where
  map_add {_ _ f g} := by
    apply ModuleCat.hom_ext
    exact congrArg ContinuousLinearMap.toLinearMap (CoordinateHom.fiberMap_add f g x)

/-- Evaluation on all fibres is jointly faithful, including on an empty base. -/
theorem hom_ext_of_fiberFunctor {f g : A ⟶ D}
    (h : ∀ x, (fiberFunctor (𝕜 := 𝕜) x).map f = (fiberFunctor x).map g) : f = g := by
  apply hom_ext
  intro x
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun k => k v) (h x)

/-- Isomorphic finite-rank cores over a nonempty base have the same rank. -/
theorem rank_eq_of_iso [Nonempty B] (e : A ≅ D) : A.rank = D.rank :=
  let ⟨x⟩ := ‹Nonempty B›
  (Module.finrank_fin_fun 𝕜).symm.trans <|
    ((fiberFunctor (𝕜 := 𝕜) x).mapIso e).toLinearEquiv.finrank_eq.trans (Module.finrank_fin_fun 𝕜)

variable (𝕜 B) in
/-- The trivial point-indexed core of rank `n`. This construction also works on the empty base. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin n → 𝕜`.
@[expose]
def trivial (n : ℕ) : FiniteRankBundleCore 𝕜 B where
  rank := n
  core :=
    { baseSet := fun _ => Set.univ
      isOpen_baseSet := fun _ => isOpen_univ
      indexAt := id
      mem_baseSet_at := fun _ => Set.mem_univ _
      coordChange := fun _ _ _ => ContinuousLinearMap.id 𝕜 _
      coordChange_self := fun _ _ _ _ => rfl
      continuousOn_coordChange := fun _ _ => continuousOn_const
      coordChange_comp := fun _ _ _ _ _ _ => rfl }
  indexAt_eq := fun _ => rfl

@[simp] theorem rank_trivial (n : ℕ) : (trivial 𝕜 B n).rank = n := (rfl)

@[simp] theorem localTriv_baseSet_trivial (n : ℕ) (x : B) :
    ((trivial 𝕜 B n).core.localTriv x).baseSet = Set.univ := (rfl)

@[simp] theorem coordChange_trivial (n : ℕ) (i j x : B) :
    (trivial 𝕜 B n).core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) := (rfl)

section ToTrivial

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- A map into the total space of a trivial core is continuous exactly when its base point and
its coordinate vector depend continuously on the argument. -/
theorem continuous_trivial_iff {f : X → (trivial 𝕜 B n).core.TotalSpace} :
    Continuous f ↔
      Continuous (fun y ↦ (f y).proj) ∧ Continuous (fun y ↦ ((f y).snd : Fin n → 𝕜)) := by
  refine ⟨fun h ↦ ⟨(FiberBundle.continuous_proj _ _).comp h,
    continuous_iff_continuousAt.2 fun y ↦
      ((FiberBundle.continuousAt_totalSpace _ f).1 h.continuousAt).2⟩, fun h ↦ ?_⟩
  exact continuous_iff_continuousAt.2 fun y ↦
    (FiberBundle.continuousAt_totalSpace _ f).2 ⟨h.1.continuousAt, h.2.continuousAt⟩

/-- The coordinate vector of a point of a trivial core depends continuously on the point. -/
theorem continuous_trivial_snd :
    Continuous fun p : (trivial 𝕜 B n).core.TotalSpace ↦ (p.snd : Fin n → 𝕜) :=
  (continuous_trivial_iff.1 continuous_id).2

/-- The fibre maps of a bundle map into a trivial core form a continuous map from the source total
space to the coordinate space. -/
theorem continuous_fiberMap_trivial (f : A ⟶ trivial 𝕜 B n) :
    Continuous fun p : A.core.TotalSpace ↦ (f.fiberMap p.proj p.snd : Fin n → 𝕜) := by
  have h := f.continuous_totalSpaceMap
  rw [CoordinateHom.totalSpaceMap_def] at h
  exact continuous_trivial_snd.comp h

variable [CompleteSpace 𝕜]

/-- A family of linear maps from the fibres of a core to `Fin n → 𝕜` which is continuous on the
total space is a bundle map into the trivial core of rank `n`. -/
def toTrivial (f : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (hf : Continuous fun p : A.core.TotalSpace ↦ f p.proj p.snd) : A ⟶ trivial 𝕜 B n :=
  CoordinateHom.ofContinuous f <|
    (continuous_hom_bundle_iff (E₁ := A.core.Fiber) (E₂ := (trivial 𝕜 B n).core.Fiber) f).2 <|
      continuous_trivial_iff.2 ⟨A.core.continuous_proj, hf⟩

@[simp] theorem fiberMap_toTrivial (f : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin n → 𝕜))
    (hf : Continuous fun p : A.core.TotalSpace ↦ f p.proj p.snd) (x : B) :
    (toTrivial f hf).fiberMap x = f x :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

end ToTrivial

/-- A core of rank zero is a zero object: its fibres are zero spaces. -/
theorem isZero_of_rank_eq_zero (A : FiniteRankBundleCore 𝕜 B) (h : A.rank = 0) : IsZero A where
  unique_to D := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    let : Subsingleton (Fin A.rank → 𝕜) := by
      rw [h]
      infer_instance
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]⟩⟩
  unique_from D := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    ext v i
    exact (Fin.cast h i).elim0⟩⟩

/-- The trivial rank-zero core is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 B 0) :=
  isZero_of_rank_eq_zero _ (rank_trivial 0)

/-- A point-indexed rank-zero core supplies the category's zero object. -/
instance : HasZeroObject (FiniteRankBundleCore 𝕜 B) :=
  ⟨⟨trivial 𝕜 B 0, isZero_trivial_zero⟩⟩

variable (𝕜) in
/-- Present an actual vector bundle of rank `n` by its point-indexed core.
The original fibre universe does not occur in the type of the result. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin n → 𝕜`.
@[expose, implicit_reducible]
noncomputable def ofBundle (n : ℕ) (E : B → Type*)
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)]
    [FiberBundle (Fin n → 𝕜) E] [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    FiniteRankBundleCore 𝕜 B where
  rank := n
  core := pointIndexedCore 𝕜 (Fin n → 𝕜) E
  indexAt_eq := pointIndexedCore_indexAt 𝕜 (Fin n → 𝕜) E

@[simp] theorem rank_ofBundle (n : ℕ) (E : B → Type*)
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)]
    [FiberBundle (Fin n → 𝕜) E] [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofBundle 𝕜 n E).rank = n := (rfl)

@[simp] theorem core_ofBundle (n : ℕ) (E : B → Type*)
    [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E)]
    [FiberBundle (Fin n → 𝕜) E] [VectorBundle 𝕜 (Fin n → 𝕜) E] :
    (ofBundle 𝕜 n E).core = pointIndexedCore 𝕜 (Fin n → 𝕜) E := (rfl)

/-- The bundle map whose coordinate matrix is the same operator `T` at every point, from a core
whose chart domains lie in those of the target, when `T` intertwines the transition maps. In the
charts `i` and `j` it is represented by the target transition from `i` to `j` after `T`. -/
def constHom (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T) :
    A ⟶ D where
  operator i j :=
    ⟨fun x => (D.core.coordChange i j x).comp T,
      (continuousOn_iff_continuous_domRestrict.1 ((D.core.continuousOn_coordChange i j).mono
        fun _ (hx : _ ∈ A.core.baseSet i ∩ D.core.baseSet j) =>
          ⟨hbase i hx.1, hx.2⟩)).clm_comp_const T⟩
  compatible i i' j j' x hi hi' hj hj' v := by
    have hDi : x ∈ D.core.baseSet i := hbase i hi
    have hDi' : x ∈ D.core.baseSet i' := hbase i' hi'
    -- Both sides are transitions of `D` applied after `T`; the calculation is stated on the
    -- underlying operators, to which the chart operators reduce.
    calc D.core.coordChange j j' x (D.core.coordChange i j x (T v))
        = D.core.coordChange i j' x (T v) := D.core.coordChange_comp i j j' x ⟨⟨hDi, hj⟩, hj'⟩ _
      _ = D.core.coordChange i' j' x (D.core.coordChange i i' x (T v)) :=
        (D.core.coordChange_comp i i' j' x ⟨⟨hDi, hDi'⟩, hj'⟩ _).symm
      _ = D.core.coordChange i' j' x (T (A.core.coordChange i i' x v)) := by
        rw [← ContinuousLinearMap.comp_apply T, hT i i' x hi hi', ContinuousLinearMap.comp_apply]

/-- In charts `i` and `j`, a constant intertwining map is the target transition after `T`. -/
@[simp] theorem operator_constHom (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T)
    (i j : B) :
    (constHom hbase T hT).operator i j =
      ⟨fun x ↦ (D.core.coordChange i j x).comp T,
        (continuousOn_iff_continuous_domRestrict.1 ((D.core.continuousOn_coordChange i j).mono
          fun _ (hx : _ ∈ A.core.baseSet i ∩ D.core.baseSet j) ↦
            ⟨hbase i hx.1, hx.2⟩)).clm_comp_const T⟩ := (rfl)

/-- A bundle map with constant coordinate matrix `T` is `T` on every fibre. -/
@[simp] theorem fiberMap_constHom (hbase : ∀ i, A.core.baseSet i ⊆ D.core.baseSet i)
    (T : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hT : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      T.comp (A.core.coordChange i j x) = (D.core.coordChange i j x).comp T) (x : B) :
    (constHom hbase T hT).fiberMap x = T := by
  ext v : 1
  rw [CoordinateHom.fiberMap_def]
  simp only [constHom, ContinuousMap.coe_mk, ContinuousLinearMap.comp_apply, A.indexAt_eq,
    D.indexAt_eq, coordChange_self, ContinuousLinearMap.id_apply]

/-- An equivalence intertwining two cores' transitions also intertwines them in reverse. -/
theorem coordChange_intertwines_symm (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      e.toContinuousLinearMap.comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp e.toContinuousLinearMap)
    (i j : B) (x : B) (hi : x ∈ D.core.baseSet i) (hj : x ∈ D.core.baseSet j) :
    e.symm.toContinuousLinearMap.comp (D.core.coordChange i j x) =
      (A.core.coordChange i j x).comp e.symm.toContinuousLinearMap := by
  ext w : 1
  apply e.injective
  have h := congrArg (fun S => S (e.symm w))
    (he i j x ((hbase i).symm ▸ hi) ((hbase j).symm ▸ hj))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] at h ⊢
  exact h.symm

/-- Two cores with the same chart domains whose transition maps are intertwined by a fixed
coordinate equivalence `e` are isomorphic, by `e` on every fibre. -/
def constIso (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) :
    A ≅ D where
  hom := constHom (fun i => (hbase i).le) e he
  inv := constHom (fun i => (hbase i).ge) e.symm.toContinuousLinearMap
    (coordChange_intertwines_symm hbase e he)
  hom_inv_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_constHom, fiberMap_constHom, fiberMap_id]
    exact e.coe_symm_comp_coe
  inv_hom_id := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_constHom, fiberMap_constHom, fiberMap_id]
    exact e.coe_comp_coe_symm

@[simp] theorem fiberMap_constIso_hom (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) (x : B) :
    (constIso hbase e he).hom.fiberMap x = e :=
  fiberMap_constHom (fun i => (hbase i).le) _ he x

@[simp] theorem fiberMap_constIso_inv (hbase : ∀ i, A.core.baseSet i = D.core.baseSet i)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (he : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)).comp (A.core.coordChange i j x) =
        (D.core.coordChange i j x).comp (e : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))) (x : B) :
    (constIso hbase e he).inv.fiberMap x = e.symm := by
  simp only [constIso, fiberMap_constHom]

section TotalSpace

/-- A family of fibrewise continuous linear maps between two finite-rank cores is continuous as a
section of the Hom bundle if and only if the induced map on total spaces is continuous. Because the
source model `Fin A.rank → 𝕜` carries its standard coordinate basis, no completeness assumption on
`𝕜` is required. -/
theorem continuous_hom_bundle_core_iff
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :
    Continuous (fun x ↦ TotalSpace.mk' ((Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
      (E := fun y ↦ A.core.Fiber y →L[𝕜] D.core.Fiber y) x (ϕ x)) ↔
      Continuous (fun p : A.core.TotalSpace ↦
        (⟨p.proj, ϕ p.proj p.snd⟩ : D.core.TotalSpace)) := by
  constructor
  · intro hϕ
    have h := (CoordinateHom.ofContinuous ϕ hϕ).continuous_totalSpaceMap
    rwa [CoordinateHom.totalSpaceMap_def, CoordinateHom.fiberMap_ofContinuous] at h
  · intro hϕ
    refine continuous_hom_bundle_iff_forall_continuousOn.2 fun i j ↦ ?_
    have hU : IsOpen (A.core.baseSet i ∩ D.core.baseSet j) :=
      (A.core.isOpen_baseSet i).inter (D.core.isOpen_baseSet j)
    refine hU.continuousOn_iff.2 fun x hx ↦ continuousAt_clm_pi_iff.2 fun v ↦ ?_
    let e₁ := A.core.localTriv i
    let e₂ := D.core.localTriv j
    have hx₁ : x ∈ e₁.baseSet := hx.1
    have hx₂ : (⟨x, ϕ x (e₁.symm x v)⟩ : D.core.TotalSpace) ∈ e₂.source :=
      (D.core.mem_localTriv_source j _).2 hx.2
    have hs : ContinuousAt (fun y ↦ (⟨y, e₁.symm y v⟩ : A.core.TotalSpace)) x :=
      (e₁.continuousOn_symm.continuousAt
        ((e₁.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx₁, Set.mem_univ v⟩)).comp
          (continuousAt_id.prodMk continuousAt_const)
    have hg : ContinuousAt (fun y ↦ (⟨y, ϕ y (e₁.symm y v)⟩ : D.core.TotalSpace)) x :=
      hϕ.continuousAt.comp_of_eq hs rfl
    have ht : ContinuousAt (fun y ↦ e₂ ⟨y, ϕ y (e₁.symm y v)⟩) x :=
      (e₂.continuousOn.continuousAt (e₂.open_source.mem_nhds hx₂)).comp_of_eq hg rfl
    refine ht.snd.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy₁ : y ∈ (A.core.localTriv i).baseSet := hy.1
    simp only [e₂, D.core.localTriv_apply, e₁, A.core.localTriv_symm_apply i hy₁,
      inChartCoordinates_apply]

/-- Construct a morphism of finite-rank cores from fibrewise continuous linear maps that induce a
continuous map on total spaces. -/
def ofTotalSpaceContinuous
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.snd⟩ : D.core.TotalSpace)) : A ⟶ D :=
  CoordinateHom.ofContinuous ϕ ((continuous_hom_bundle_core_iff ϕ).2 hϕ)

@[simp]
theorem fiberMap_ofTotalSpaceContinuous
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.snd⟩ : D.core.TotalSpace)) (x : B) :
    (ofTotalSpaceContinuous ϕ hϕ).fiberMap x = ϕ x :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x

@[simp]
theorem totalSpaceMap_ofTotalSpaceContinuous
    (ϕ : B → (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜))
    (hϕ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, ϕ p.proj p.snd⟩ : D.core.TotalSpace)) (p : A.core.TotalSpace) :
    (ofTotalSpaceContinuous ϕ hϕ).totalSpaceMap p = ⟨p.proj, ϕ p.proj p.snd⟩ := by
  rcases p with ⟨x, v⟩
  simp [CoordinateHom.totalSpaceMap_mk]

/-- Construct an isomorphism of finite-rank cores from fibrewise continuous linear equivalences
whose forward and inverse maps are continuous on total spaces. -/
def isoOfTotalSpaceContinuous
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.snd⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.snd⟩ : A.core.TotalSpace)) : A ≅ D where
  hom := ofTotalSpaceContinuous (fun x ↦ (Φ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)))
    (hΦ₁.congr fun _ ↦ rfl)
  inv := ofTotalSpaceContinuous
    (fun x ↦ ((Φ x).symm : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)))
    (hΦ₂.congr fun _ ↦ rfl)
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_ofTotalSpaceContinuous, fiberMap_ofTotalSpaceContinuous,
      fiberMap_id]
    exact (Φ x).coe_symm_comp_coe
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, fiberMap_ofTotalSpaceContinuous, fiberMap_ofTotalSpaceContinuous,
      fiberMap_id]
    exact (Φ x).coe_comp_coe_symm

@[simp]
theorem fiberMap_isoOfTotalSpaceContinuous_hom
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.snd⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.snd⟩ : A.core.TotalSpace)) (x : B) :
    (isoOfTotalSpaceContinuous Φ hΦ₁ hΦ₂).hom.fiberMap x =
      (Φ x : (Fin A.rank → 𝕜) →L[𝕜] (Fin D.rank → 𝕜)) :=
  fiberMap_ofTotalSpaceContinuous _ (hΦ₁.congr fun _ ↦ rfl) x

@[simp]
theorem fiberMap_isoOfTotalSpaceContinuous_inv
    (Φ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
    (hΦ₁ : Continuous fun p : A.core.TotalSpace ↦
      (⟨p.proj, Φ p.proj p.snd⟩ : D.core.TotalSpace))
    (hΦ₂ : Continuous fun p : D.core.TotalSpace ↦
      (⟨p.proj, (Φ p.proj).symm p.snd⟩ : A.core.TotalSpace)) (x : B) :
    (isoOfTotalSpaceContinuous Φ hΦ₁ hΦ₂).inv.fiberMap x =
      ((Φ x).symm : (Fin D.rank → 𝕜) →L[𝕜] (Fin A.rank → 𝕜)) :=
  fiberMap_ofTotalSpaceContinuous _ (hΦ₂.congr fun _ ↦ rfl) x

/-- The continuous linear equivalence on the fibre at `x` induced by a categorical isomorphism of
finite-rank cores. -/
def isoFiberEquiv (e : A ≅ D) (x : B) : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) :=
  ContinuousLinearEquiv.ofContinuousLinearMap (e.hom.fiberMap x) (e.inv.fiberMap x)
    (ContinuousLinearMap.ext fun v ↦ by
      have h := congrArg (fun k : D ⟶ D ↦ k.fiberMap x v) e.inv_hom_id
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h)
    (ContinuousLinearMap.ext fun v ↦ by
      have h := congrArg (fun k : A ⟶ A ↦ k.fiberMap x v) e.hom_inv_id
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h)

@[simp]
theorem isoFiberEquiv_apply (e : A ≅ D) (x : B) (v : Fin A.rank → 𝕜) :
    isoFiberEquiv e x v = e.hom.fiberMap x v :=
  (rfl)

@[simp]
theorem isoFiberEquiv_symm_apply (e : A ≅ D) (x : B) (v : Fin D.rank → 𝕜) :
    (isoFiberEquiv e x).symm v = e.inv.fiberMap x v :=
  (rfl)

/-- Re-express a continuous linear equivalence between core fibres directly on coordinate models so
its type reduces under `implicit` transparency. -/
def ofCoreEquiv {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) :
    (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) where
  toFun v := e v
  invFun v := e.symm v
  left_inv v := e.symm_apply_apply v
  right_inv v := e.apply_symm_apply v
  map_add' u v := e.map_add u v
  map_smul' c v := e.map_smul c v
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

@[simp]
theorem ofCoreEquiv_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) (v : Fin A.rank → 𝕜) :
    ofCoreEquiv A D y z e v = e v :=
  (rfl)

@[simp]
theorem ofCoreEquiv_symm_apply {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (A : FiniteRankBundleCore 𝕜 Y) (D : FiniteRankBundleCore 𝕜 Z) (y : Y) (z : Z)
    (e : A.core.Fiber y ≃L[𝕜] D.core.Fiber z) (v : Fin D.rank → 𝕜) :
    (ofCoreEquiv A D y z e).symm v = e.symm v :=
  (rfl)

end TotalSpace

section IsoTrivial

variable (A : FiniteRankBundleCore 𝕜 B) {r : ℕ}
  (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin r → 𝕜))
  (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
    A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))

/-- A core whose transition maps on chart overlaps are all the identity, equipped with a continuous
linear equivalence of its model fibre with `Fin r → 𝕜`, is canonically isomorphic to `trivial 𝕜 B r`
even when its chart domains are proper subsets of `B`. -/
def isoTrivialOfCoordChangeEqId : A ≅ trivial 𝕜 B r where
  hom :=
    { operator := fun _ _ ↦ ⟨fun _ ↦ e.toContinuousLinearMap, continuous_const⟩
      compatible := fun i i' _ _ x hi hi' _ _ _ ↦ by
        rw [coordChange_trivial, h i i' x hi hi']; rfl }
  inv :=
    { operator := fun _ _ ↦ ⟨fun _ ↦ e.symm.toContinuousLinearMap, continuous_const⟩
      compatible := fun _ _ j j' x _ _ hj hj' _ ↦ by
        rw [coordChange_trivial, h j j' x hj hj']; rfl }
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def, fiberMap_id]
    ext v : 1; exact e.symm_apply_apply v
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def, fiberMap_id]
    ext v : 1; exact e.apply_symm_apply v

theorem operator_isoTrivialOfCoordChangeEqId_hom (i j : B)
    (x : ↥(A.core.baseSet i ∩ (trivial 𝕜 B r).core.baseSet j)) :
    (isoTrivialOfCoordChangeEqId A e h).hom.operator i j x = e.toContinuousLinearMap := (rfl)

theorem operator_isoTrivialOfCoordChangeEqId_inv (i j : B)
    (x : ↥((trivial 𝕜 B r).core.baseSet i ∩ A.core.baseSet j)) :
    (isoTrivialOfCoordChangeEqId A e h).inv.operator i j x = e.symm.toContinuousLinearMap := (rfl)

@[simp] theorem fiberMap_isoTrivialOfCoordChangeEqId_hom (x : B) :
    (isoTrivialOfCoordChangeEqId A e h).hom.fiberMap x = e.toContinuousLinearMap := by
  rw [CoordinateHom.fiberMap_def]; rfl

@[simp] theorem fiberMap_isoTrivialOfCoordChangeEqId_inv (x : B) :
    (isoTrivialOfCoordChangeEqId A e h).inv.fiberMap x = e.symm.toContinuousLinearMap := by
  rw [CoordinateHom.fiberMap_def]; rfl

end IsoTrivial

section Isomorphisms

variable [CompleteSpace 𝕜]

/-- A morphism of finite-rank cores is invertible exactly when it is bijective on every fibre.
The inverse is continuous, rather than merely a family of algebraic inverses. -/
theorem isIso_iff_bijective (f : A ⟶ D) :
    IsIso f ↔ ∀ x, Function.Bijective (f.fiberMap x) := by
  constructor
  · intro hf x
    let := hf
    refine ⟨Function.HasLeftInverse.injective ⟨(inv f).fiberMap x, ?_⟩,
      Function.HasRightInverse.surjective ⟨(inv f).fiberMap x, ?_⟩⟩
    · intro v
      have h := congrArg (fun k : A ⟶ A => k.fiberMap x v) (IsIso.hom_inv_id f)
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
    · intro v
      have h := congrArg (fun k : D ⟶ D => k.fiberMap x v) (IsIso.inv_hom_id f)
      simpa only [fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] using h
  · intro hf
    let e (x : B) : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜) :=
      (LinearEquiv.ofBijective (f.fiberMap x).toLinearMap (hf x)).toContinuousLinearEquiv
    have he (x : B) : (f.fiberMap x).IsInvertible := ⟨e x, rfl⟩
    let g : D ⟶ A := CoordinateHom.ofContinuous (fun x => (f.fiberMap x).inverse)
      (f.continuous_fiberMap.clm_bundle_inverse (E₁ := A.core.Fiber) (E₂ := D.core.Fiber)
        (b := fun x => x) he)
    have hg (x : B) : g.fiberMap x = (f.fiberMap x).inverse :=
      congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x
    exact ⟨g, by
      apply hom_ext
      intro x
      simp only [fiberMap_comp, hg, fiberMap_id, (he x).inverse_comp_self], by
      apply hom_ext
      intro x
      simp only [fiberMap_comp, hg, fiberMap_id, (he x).self_comp_inverse]⟩

section IsoEquiv
variable {A D : FiniteRankBundleCore 𝕜 B}
  (ψ : B → (Fin A.rank → 𝕜) ≃L[𝕜] (Fin D.rank → 𝕜))
  (hψ : Continuous fun p : A.core.TotalSpace ↦
    TotalSpace.mk' (Fin D.rank → 𝕜) (E := D.core.Fiber) p.proj (ψ p.proj p.snd))
/-- Fibrewise continuous linear equivalences continuous on total spaces induce a core iso. -/
def isoOfContinuousEquiv : A ≅ D where
  hom := CoordinateHom.ofContinuous (fun x ↦ (ψ x).toContinuousLinearMap)
    ((continuous_hom_bundle_iff (E₁ := A.core.Fiber) (E₂ := D.core.Fiber) _).2 hψ)
  inv := CoordinateHom.ofContinuous (fun x ↦ (ψ x).symm.toContinuousLinearMap)
    ((continuous_hom_bundle_iff (E₁ := D.core.Fiber) (E₂ := A.core.Fiber) _).2
      (continuous_bundle_symm (E₁ := A.core.Fiber) (E₂ := D.core.Fiber) ψ hψ))
  hom_inv_id := hom_ext fun x ↦ by
    simpa only [fiberMap_comp, fiberMap_id, congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x]
      using (ψ x).coe_symm_comp_coe
  inv_hom_id := hom_ext fun x ↦ by
    simpa only [fiberMap_comp, fiberMap_id, congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x]
      using (ψ x).coe_comp_coe_symm
@[simp] theorem fiberMap_isoOfContinuousEquiv_hom (x : B) :
    (isoOfContinuousEquiv ψ hψ).hom.fiberMap x = ψ x :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x
@[simp] theorem fiberMap_isoOfContinuousEquiv_inv (x : B) :
    (isoOfContinuousEquiv ψ hψ).inv.fiberMap x = (ψ x).symm :=
  congrFun (CoordinateHom.fiberMap_ofContinuous _ _) x
end IsoEquiv

section OfBundle
variable {n : ℕ} {E₀ E₁ : B → Type*} [∀ x, AddCommMonoid (E₀ x)] [∀ x, Module 𝕜 (E₀ x)]
  [∀ x, TopologicalSpace (E₀ x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E₀)]
  [FiberBundle (Fin n → 𝕜) E₀] [VectorBundle 𝕜 (Fin n → 𝕜) E₀]
  [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace (Fin n → 𝕜) E₁)] [FiberBundle (Fin n → 𝕜) E₁]
  [VectorBundle 𝕜 (Fin n → 𝕜) E₁] (Φ : ∀ x, E₀ x ≃L[𝕜] E₁ x)
  (hΦ : Continuous fun p : TotalSpace (Fin n → 𝕜) E₀ ↦
    TotalSpace.mk' (Fin n → 𝕜) (E := E₁) p.proj (Φ p.proj p.snd))
/-- Continuous fibrewise continuous linear equivalences induce an iso of `ofBundle` cores. -/
noncomputable def ofBundleIso : ofBundle 𝕜 n E₀ ≅ ofBundle 𝕜 n E₁ :=
  let h₀ := pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) E₀
  let h₁ := pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) E₁
  isoOfContinuousEquiv (fun x ↦ (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₀ x).trans
      ((Φ x).trans (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₁ x).symm)) <|
    (h₁.symm.continuous.comp (hΦ.comp h₀.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, pointIndexedCoreHomeomorph_apply,
        pointIndexedCoreHomeomorph_symm_apply, TotalSpace.mk']
      exact congrArg (TotalSpace.mk p.proj)
        ((ContinuousLinearEquiv.trans_apply _ _ _).trans
          (ContinuousLinearEquiv.trans_apply _ _ _)).symm
@[simp] theorem fiberMap_ofBundleIso_hom (x : B) :
    (ofBundleIso Φ hΦ).hom.fiberMap x = ContinuousLinearEquiv.toContinuousLinearMap
      ((pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₀ x).trans
        ((Φ x).trans (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₁ x).symm)) := by
  rw [ofBundleIso]; exact fiberMap_isoOfContinuousEquiv_hom _ _ x
@[simp] theorem fiberMap_ofBundleIso_inv (x : B) :
    (ofBundleIso Φ hΦ).inv.fiberMap x = ContinuousLinearEquiv.toContinuousLinearMap
      ((pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₀ x).trans
        ((Φ x).trans (pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₁ x).symm)).symm := by
  rw [ofBundleIso]; exact fiberMap_isoOfContinuousEquiv_inv _ _ x
end OfBundle
end Isomorphisms

/-- An iso between `ofBundle` cores yields a continuous family of fibrewise equivalences. -/
theorem exists_continuousLinearEquiv_of_ofBundle_iso {n : ℕ} {E₀ E₁ : B → Type*}
    [∀ x, AddCommMonoid (E₀ x)] [∀ x, Module 𝕜 (E₀ x)] [∀ x, TopologicalSpace (E₀ x)]
    [TopologicalSpace (TotalSpace (Fin n → 𝕜) E₀)] [FiberBundle (Fin n → 𝕜) E₀]
    [VectorBundle 𝕜 (Fin n → 𝕜) E₀] [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace (Fin n → 𝕜) E₁)]
    [FiberBundle (Fin n → 𝕜) E₁] [VectorBundle 𝕜 (Fin n → 𝕜) E₁]
    (β : ofBundle 𝕜 n E₀ ≅ ofBundle 𝕜 n E₁) :
    ∃ Φ : ∀ x, E₀ x ≃L[𝕜] E₁ x, Continuous fun p : TotalSpace (Fin n → 𝕜) E₀ ↦
      TotalSpace.mk' (Fin n → 𝕜) (E := E₁) p.proj (Φ p.proj p.snd) := by
  let e₀ (x : B) : (Fin n → 𝕜) ≃L[𝕜] E₀ x := pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₀ x
  let e₁ (x : B) : (Fin n → 𝕜) ≃L[𝕜] E₁ x := pointIndexedCoreFiberEquiv 𝕜 (Fin n → 𝕜) E₁ x
  let f x := (e₁ x).toContinuousLinearMap.comp
    ((β.hom.fiberMap x).comp (e₀ x).symm.toContinuousLinearMap)
  let g x := (e₀ x).toContinuousLinearMap.comp
    ((β.inv.fiberMap x).comp (e₁ x).symm.toContinuousLinearMap)
  refine ⟨fun x ↦ ContinuousLinearEquiv.ofContinuousLinearMap (f x) (g x)
      (ContinuousLinearMap.ext fun w ↦ by
        have h := congrArg (fun k : ofBundle 𝕜 n E₁ ⟶ _ ↦ k.fiberMap x ((e₁ x).symm w)) β.inv_hom_id
        simpa only [f, g, fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
          using congrArg (e₁ x) h)
      (ContinuousLinearMap.ext fun v ↦ by
        have h := congrArg (fun k : ofBundle 𝕜 n E₀ ⟶ _ ↦ k.fiberMap x ((e₀ x).symm v)) β.hom_inv_id
        simpa only [f, g, fiberMap_comp, fiberMap_id, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
          ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.apply_symm_apply]
          using congrArg (e₀ x) h),
    ((pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) E₁).continuous.comp
      (β.hom.continuous_totalSpaceMap.comp
        (pointIndexedCoreHomeomorph 𝕜 (Fin n → 𝕜) E₀).symm.continuous)).congr fun p ↦ by
      rw [Function.comp_apply, Function.comp_apply, pointIndexedCoreHomeomorph_symm_apply,
        CoordinateHom.totalSpaceMap_mk, pointIndexedCoreHomeomorph_apply, TotalSpace.mk']
      exact congrArg (TotalSpace.mk p.proj)
        (congrFun (ContinuousLinearEquiv.coe_ofContinuousLinearMap (f p.proj) (g p.proj) _ _)
          p.snd).symm⟩

end FiniteRankBundleCore
end TauCeti

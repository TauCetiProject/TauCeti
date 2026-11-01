/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Core
public import TauCeti.Topology.VectorBundle.Descent
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The category of finite-rank point-indexed vector-bundle cores

`FiniteRankBundleCore 𝕜 B` stores a natural-number rank and a Mathlib `VectorBundleCore`
with model `Fin rank → 𝕜`, indexed by the base points, with the chart at `x` labelled by `x`.
Its morphisms are `VectorBundleCore.CoordinateHom`: continuous chart operators satisfying
transition compatibility, hence actual continuous fibrewise linear maps of the reconstructed
bundles. Addition of chart operators makes this category preadditive. The trivial rank-zero
core is a zero object. No nonemptiness or separation assumption on the base is required.

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
in finite-dimensional charts supplies the inverse bundle morphism.

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

/-- The trivial rank-zero core is a zero object. -/
theorem isZero_trivial_zero : IsZero (trivial 𝕜 B 0) where
  unique_to D := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    apply ContinuousLinearMap.ext
    intro v
    let : Subsingleton (Fin (trivial 𝕜 B 0).rank → 𝕜) := by
      rw [rank_trivial]
      infer_instance
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]⟩⟩
  unique_from A := ⟨⟨⟨0⟩, fun f => by
    apply hom_ext
    intro x
    ext v i
    exact Fin.elim0 i⟩⟩

/-- A point-indexed rank-zero core supplies the category's zero object. -/
instance : HasZeroObject (FiniteRankBundleCore 𝕜 B) :=
  ⟨⟨trivial 𝕜 B 0, isZero_trivial_zero⟩⟩

variable (𝕜) in
/-- Present an actual vector bundle of rank `n` by its point-indexed core.
The original fibre universe does not occur in the type of the result. -/
-- Expose the rank projection so the dependent fibre model reduces to `Fin n → 𝕜`.
@[expose]
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

end Isomorphisms
end FiniteRankBundleCore
end TauCeti

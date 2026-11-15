/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The symmetric monoidal category of finite-rank bundle cores

The tensor product `FiniteRankBundleCore.tensor` of point-indexed cores, with the trivial line
bundle `trivial 𝕜 B 1` as unit, makes `FiniteRankBundleCore 𝕜 B` a symmetric monoidal
category in which the tensor product is additive in each variable
(`MonoidalPreadditive`). The structure isomorphisms are actual bundle isomorphisms with a fixed
coordinate matrix on every fibre:

* the associator `(A ⊗ D) ⊗ C ≅ A ⊗ (D ⊗ C)` is `ContinuousLinearEquiv.kroneckerAssoc`;
* the unitors `𝟙 ⊗ A ≅ A` and `A ⊗ 𝟙 ≅ A` are `ContinuousLinearEquiv.kroneckerLid` and
  `ContinuousLinearEquiv.kroneckerRid`;
* the braiding `A ⊗ D ≅ D ⊗ A` is the coordinate swap `ContinuousLinearEquiv.kroneckerComm`.

Each of these coordinate isomorphisms intertwines the Kronecker products of the transition
maps, so it defines an isomorphism of cores by `FiniteRankBundleCore.constIso`. The same
intertwining relations, applied to the fibre maps of bundle morphisms, give naturality, and the
coherence laws hold fibrewise as identities between coordinate permutations.

Together with the Whitney biproducts of `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`,
this is the structure of a symmetric monoidal preadditive category with binary biproducts, which
is what the commutative ring structure on split Grothendieck groups
(`TauCeti.SplitK0.instCommRing`) consumes: the tensor product of cores descends to the product
of classes, `[A] * [D] = [A ⊗ D]`, with the class of the trivial line bundle as unit. Pullback
along a continuous map `f` commutes strictly with tensor products, the monoidal unit, the
associator, the unitors, and the braiding, making `pullbackFunctor f` a braided strong monoidal
functor with identity unit and tensorator isomorphisms (`pullbackCoreMonoidal`,
`instMonoidalPullbackFunctor`, `instBraidedPullbackFunctor`). The base is arbitrary, and the
scalar field need not be complete.

For the tensor product of vector bundles and its transition functions see Milnor–Stasheff,
*Characteristic Classes*, §3, and Atiyah, *K-Theory*, §1.2.
-/

public section

open CategoryTheory VectorBundleCore
open scoped MonoidalCategory

namespace TauCeti.FiniteRankBundleCore

open ContinuousLinearEquiv ContinuousLinearMap

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]

/-- The tensor product of cores, with the trivial line bundle as unit. The associator and
unitors are the bundle isomorphisms with the Kronecker coherence isomorphisms as their
constant coordinate matrices. -/
instance : MonoidalCategoryStruct (FiniteRankBundleCore 𝕜 B) where
  tensorObj := tensor
  whiskerLeft A _ _ g := tensorHom (𝟙 A) g
  whiskerRight f D := tensorHom f (𝟙 D)
  tensorHom := tensorHom
  tensorUnit := trivial 𝕜 B 1
  associator A D C :=
    constIso (fun _ => Set.inter_assoc _ _ _) (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
      fun _ _ _ _ _ => kroneckerAssoc_comp_kronecker _ _ _
  leftUnitor A :=
    constIso (fun _ => Set.univ_inter _) (kroneckerLid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerLid_comp_kronecker _
  rightUnitor A :=
    constIso (fun _ => Set.inter_univ _) (kroneckerRid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerRid_comp_kronecker _

variable {A A' D D' C : FiniteRankBundleCore 𝕜 B}

@[simp] theorem rank_tensorObj (A D : FiniteRankBundleCore 𝕜 B) :
    (A ⊗ D).rank = A.rank * D.rank := (rfl)

@[simp] theorem rank_tensorUnit : (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank = 1 := (rfl)

/-- The monoidal tensor product of bundle maps is the Kronecker product on every fibre. -/
@[simp] theorem fiberMap_tensorHom_monoidal (f : A ⟶ A') (g : D ⟶ D') (x : B) :
    (f ⊗ₘ g).fiberMap x = (f.fiberMap x).kronecker (g.fiberMap x) :=
  fiberMap_tensorHom f g x

@[simp] theorem fiberMap_whiskerLeft (A : FiniteRankBundleCore 𝕜 B) (g : D ⟶ D') (x : B) :
    (A ◁ g).fiberMap x = (ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)).kronecker (g.fiberMap x) := by
  rw [← fiberMap_id]
  exact fiberMap_tensorHom (𝟙 A) g x

@[simp] theorem fiberMap_whiskerRight (f : A ⟶ A') (D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (f ▷ D).fiberMap x = (f.fiberMap x).kronecker (ContinuousLinearMap.id 𝕜 (Fin D.rank → 𝕜)) := by
  rw [← fiberMap_id]
  exact fiberMap_tensorHom f (𝟙 D) x

@[simp] theorem fiberMap_associator_hom (A D C : FiniteRankBundleCore 𝕜 B) (x : B) :
    (α_ A D C).hom.fiberMap x = (kroneckerAssoc 𝕜 A.rank D.rank C.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_associator_inv (A D C : FiniteRankBundleCore 𝕜 B) (x : B) :
    (α_ A D C).inv.fiberMap x =
      (kroneckerAssoc 𝕜 A.rank D.rank C.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

@[simp] theorem fiberMap_leftUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (λ_ A).hom.fiberMap x = (kroneckerLid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_leftUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (λ_ A).inv.fiberMap x = (kroneckerLid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

@[simp] theorem fiberMap_rightUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (ρ_ A).hom.fiberMap x = (kroneckerRid 𝕜 A.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_rightUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (x : B) :
    (ρ_ A).inv.fiberMap x = (kroneckerRid 𝕜 A.rank).symm.toContinuousLinearMap :=
  fiberMap_constIso_inv _ _ _ x

/-- Finite-rank cores form a monoidal category under the tensor product. The coherence laws
hold fibrewise as the coherence laws of the Kronecker coordinate isomorphisms. -/
instance : MonoidalCategory (FiniteRankBundleCore 𝕜 B) where
  tensorHom_def f g := by
    have h := tensorHom_comp_tensorHom f (𝟙 _) (𝟙 _) g
    rw [Category.comp_id, Category.id_comp] at h
    exact h.symm
  id_tensorHom_id := id_tensorHom_id
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := tensorHom_comp_tensorHom f₁ g₁ f₂ g₂
  whiskerLeft_id := id_tensorHom_id
  id_whiskerRight := id_tensorHom_id
  associator_naturality f g h := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_tensorHom_monoidal, fiberMap_associator_hom]
    exact kroneckerAssoc_comp_kronecker _ _ _
  leftUnitor_naturality f := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_leftUnitor_hom]
    exact kroneckerLid_comp_kronecker _
  rightUnitor_naturality f := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerRight, fiberMap_rightUnitor_hom]
    exact kroneckerRid_comp_kronecker _
  pentagon A D C E := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom]
    exact kroneckerAssoc_pentagon _ _ _ _
  triangle A D := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom, fiberMap_leftUnitor_hom, fiberMap_rightUnitor_hom]
    exact kroneckerAssoc_triangle _ _

/-- The tensor product of bundle maps is additive in each variable. -/
instance : MonoidalPreadditive (FiniteRankBundleCore 𝕜 B) where
  whiskerLeft_zero := tensorHom_zero _
  zero_whiskerRight := zero_tensorHom _
  whiskerLeft_add _ _ := tensorHom_add _ _ _
  add_whiskerRight _ _ := add_tensorHom _ _ _

/-- The braiding `A ⊗ D ≅ D ⊗ A` of cores, with the coordinate swap `kroneckerComm` as its
constant coordinate matrix. -/
def tensorComm (A D : FiniteRankBundleCore 𝕜 B) : A ⊗ D ≅ D ⊗ A :=
  constIso (fun _ => Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
    fun _ _ _ _ _ => kroneckerComm_comp_kronecker _ _

@[simp] theorem fiberMap_tensorComm_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (tensorComm A D).hom.fiberMap x = (kroneckerComm 𝕜 A.rank D.rank).toContinuousLinearMap :=
  fiberMap_constIso_hom _ _ _ x

@[simp] theorem fiberMap_tensorComm_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (tensorComm A D).inv.fiberMap x = (kroneckerComm 𝕜 D.rank A.rank).toContinuousLinearMap := by
  rw [← kroneckerComm_symm]
  exact fiberMap_constIso_inv _ _ _ x

/-- The braiding `tensorComm` makes the monoidal category of finite-rank cores symmetric. -/
instance : SymmetricCategory (FiniteRankBundleCore 𝕜 B) where
  braiding := tensorComm
  braiding_naturality_right A _ _ g := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_tensorComm_hom]
    exact kroneckerComm_comp_kronecker _ _
  braiding_naturality_left f D := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_tensorComm_hom]
    exact kroneckerComm_comp_kronecker _ _
  hexagon_forward A D C := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_hom, fiberMap_tensorComm_hom]
    exact kroneckerComm_hexagon_forward _ _ _
  hexagon_reverse A D C := hom_ext fun x => by
    simp only [fiberMap_comp, fiberMap_whiskerLeft, fiberMap_whiskerRight,
      fiberMap_associator_inv, fiberMap_tensorComm_hom]
    exact kroneckerComm_hexagon_reverse _ _ _
  symmetry A D := hom_ext fun x => by
    rw [fiberMap_comp, fiberMap_tensorComm_hom, fiberMap_tensorComm_hom, fiberMap_id,
      ← kroneckerComm_symm]
    exact (kroneckerComm 𝕜 A.rank D.rank).coe_symm_comp_coe

/-- The monoidal braiding is the constant isomorphism induced by the Kronecker swap. -/
theorem braiding_def (A D : FiniteRankBundleCore 𝕜 B) :
    (β_ A D) =
      constIso (fun _ => Set.inter_comm _ _) (kroneckerComm 𝕜 A.rank D.rank)
        (fun _ _ _ _ _ => kroneckerComm_comp_kronecker _ _) := (rfl)

@[simp] theorem fiberMap_braiding_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).hom.fiberMap x = (kroneckerComm 𝕜 A.rank D.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_hom A D x

@[simp] theorem fiberMap_braiding_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).inv.fiberMap x = (kroneckerComm 𝕜 D.rank A.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_inv A D x

section Pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pulling back the monoidal unit gives the monoidal unit over the new base. -/
@[simp] theorem pullback_tensorUnit (f : C(X, Y)) :
    (𝟙_ (FiniteRankBundleCore 𝕜 Y)).pullback f = 𝟙_ (FiniteRankBundleCore 𝕜 X) := (rfl)

@[simp] theorem pullbackMap_whiskerLeft (A : FiniteRankBundleCore 𝕜 Y)
    {D₁ D₂ : FiniteRankBundleCore 𝕜 Y} (b : D₁ ⟶ D₂) (f : C(X, Y)) :
    pullbackMap (A ◁ b) f = A.pullback f ◁ pullbackMap b f := by
  change pullbackMap (tensorHom (𝟙 A) b) f = tensorHom (𝟙 (A.pullback f)) (pullbackMap b f)
  rw [pullbackMap_tensorHom, pullbackMap_id]

@[simp] theorem pullbackMap_whiskerRight {A₁ A₂ : FiniteRankBundleCore 𝕜 Y}
    (a : A₁ ⟶ A₂) (D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (a ▷ D) f = pullbackMap a f ▷ D.pullback f := by
  change pullbackMap (tensorHom a (𝟙 D)) f = tensorHom (pullbackMap a f) (𝟙 (D.pullback f))
  rw [pullbackMap_tensorHom, pullbackMap_id]

@[simp] theorem pullbackMap_associator_hom (A D C : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (α_ A D C).hom f = (α_ (A.pullback f) (D.pullback f) (C.pullback f)).hom :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_associator_hom A D C (f x)).trans
      (fiberMap_associator_hom (A.pullback f) (D.pullback f) (C.pullback f) x).symm)

@[simp] theorem pullbackMap_associator_inv (A D C : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (α_ A D C).inv f = (α_ (A.pullback f) (D.pullback f) (C.pullback f)).inv :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_associator_inv A D C (f x)).trans
      (fiberMap_associator_inv (A.pullback f) (D.pullback f) (C.pullback f) x).symm)

@[simp] theorem pullbackMap_leftUnitor_hom (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (λ_ A).hom f = (λ_ (A.pullback f)).hom :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_leftUnitor_hom A (f x)).trans
      (fiberMap_leftUnitor_hom (A.pullback f) x).symm)

@[simp] theorem pullbackMap_leftUnitor_inv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (λ_ A).inv f = (λ_ (A.pullback f)).inv :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_leftUnitor_inv A (f x)).trans
      (fiberMap_leftUnitor_inv (A.pullback f) x).symm)

@[simp] theorem pullbackMap_rightUnitor_hom (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (ρ_ A).hom f = (ρ_ (A.pullback f)).hom :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_rightUnitor_hom A (f x)).trans
      (fiberMap_rightUnitor_hom (A.pullback f) x).symm)

@[simp] theorem pullbackMap_rightUnitor_inv (A : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (ρ_ A).inv f = (ρ_ (A.pullback f)).inv :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_rightUnitor_inv A (f x)).trans
      (fiberMap_rightUnitor_inv (A.pullback f) x).symm)

@[simp] theorem pullbackMap_braiding_hom (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (β_ A D).hom f = (β_ (A.pullback f) (D.pullback f)).hom :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_braiding_hom A D (f x)).trans
      (fiberMap_braiding_hom (A.pullback f) (D.pullback f) x).symm)

@[simp] theorem pullbackMap_braiding_inv (A D : FiniteRankBundleCore 𝕜 Y) (f : C(X, Y)) :
    pullbackMap (β_ A D).inv f = (β_ (A.pullback f) (D.pullback f)).inv :=
  hom_ext fun x => (fiberMap_pullbackMap _ f x).trans
    ((fiberMap_braiding_inv A D (f x)).trans
      (fiberMap_braiding_inv (A.pullback f) (D.pullback f) x).symm)

/-- Strict monoidal data for `pullbackFunctor f`, with identity unit and tensorator isomorphisms. -/
@[expose] def pullbackCoreMonoidal (f : C(X, Y)) : (pullbackFunctor (𝕜 := 𝕜) f).CoreMonoidal where
  εIso :=
    { hom := 𝟙 _
      inv := 𝟙 _
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }
  μIso _ _ :=
    { hom := 𝟙 _
      inv := 𝟙 _
      hom_inv_id := Category.id_comp _
      inv_hom_id := Category.id_comp _ }
  μIso_hom_natural_left a A' :=
    (Category.comp_id _).trans
      ((pullbackMap_whiskerRight a A' f).symm.trans (Category.id_comp _).symm)
  μIso_hom_natural_right A' a :=
    (Category.comp_id _).trans
      ((pullbackMap_whiskerLeft A' a f).symm.trans (Category.id_comp _).symm)
  associativity A D C :=
    ((congrArg (· ≫ (𝟙 _ ≫ pullbackMap (α_ A D C).hom f))
        (MonoidalCategory.id_whiskerRight (A.pullback f ⊗ D.pullback f) (C.pullback f))).trans
      ((Category.id_comp _).trans
        ((Category.id_comp _).trans (pullbackMap_associator_hom A D C f)))).trans
      ((congrArg ((α_ (A.pullback f) (D.pullback f) (C.pullback f)).hom ≫ ·)
        ((congrArg (· ≫ 𝟙 _)
          (MonoidalCategory.whiskerLeft_id (A.pullback f) (D.pullback f ⊗ C.pullback f))).trans
          (Category.id_comp _))).trans (Category.comp_id _)).symm
  left_unitality A :=
    ((pullbackMap_leftUnitor_hom A f).symm.trans (Category.id_comp _).symm).trans
      ((Category.id_comp _).symm.trans
        (congrArg (· ≫ _)
          (MonoidalCategory.id_whiskerRight (𝟙_ (FiniteRankBundleCore 𝕜 X)) (A.pullback f)).symm))
  right_unitality A :=
    ((pullbackMap_rightUnitor_hom A f).symm.trans (Category.id_comp _).symm).trans
      ((Category.id_comp _).symm.trans
        (congrArg (· ≫ _)
          (MonoidalCategory.whiskerLeft_id (A.pullback f) (𝟙_ (FiniteRankBundleCore 𝕜 X))).symm))

/-- `pullbackFunctor f` is a strong monoidal functor with strict unit and tensorator equalities. -/
instance instMonoidalPullbackFunctor (f : C(X, Y)) :
    (pullbackFunctor (𝕜 := 𝕜) f).Monoidal :=
  (pullbackCoreMonoidal f).toMonoidal

@[simp] theorem pullbackFunctor_ε (f : C(X, Y)) :
    Functor.LaxMonoidal.ε (pullbackFunctor (𝕜 := 𝕜) f) = 𝟙 _ :=
  (pullbackCoreMonoidal f).toLaxMonoidal_ε

@[simp] theorem pullbackFunctor_μ (f : C(X, Y)) (A D : FiniteRankBundleCore 𝕜 Y) :
    Functor.LaxMonoidal.μ (pullbackFunctor (𝕜 := 𝕜) f) A D = 𝟙 _ :=
  (pullbackCoreMonoidal f).toLaxMonoidal_μ A D

@[simp] theorem pullbackFunctor_η (f : C(X, Y)) :
    Functor.OplaxMonoidal.η (pullbackFunctor (𝕜 := 𝕜) f) = 𝟙 _ :=
  (pullbackCoreMonoidal f).toOplaxMonoidal_η

@[simp] theorem pullbackFunctor_δ (f : C(X, Y)) (A D : FiniteRankBundleCore 𝕜 Y) :
    Functor.OplaxMonoidal.δ (pullbackFunctor (𝕜 := 𝕜) f) A D = 𝟙 _ :=
  (pullbackCoreMonoidal f).toOplaxMonoidal_δ A D

/-- `pullbackFunctor f` is a braided (hence symmetric) strong monoidal functor. -/
instance instBraidedPullbackFunctor (f : C(X, Y)) :
    (pullbackFunctor (𝕜 := 𝕜) f).Braided where
  braided A D :=
    ((congrArg (· ≫ _) (pullbackFunctor_μ f A D)).trans (Category.id_comp _)).trans
      ((pullbackMap_braiding_hom A D f).trans
        ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (pullbackFunctor_μ f D A).symm)))

end Pullback

end TauCeti.FiniteRankBundleCore

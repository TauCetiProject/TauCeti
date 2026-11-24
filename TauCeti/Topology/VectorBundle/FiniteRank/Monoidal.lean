/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic
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
coherence laws hold fibrewise as identities between coordinate permutations. Tensor powers are
provided by the generic monoidal construction `TauCeti.tensorPow`, with rank computed by
`FiniteRankBundleCore.rank_tensorPow`; when a transition map of a core is multiplication by a
scalar, the corresponding transition map of its `m`th tensor power is multiplication by the `m`th
power of that scalar (`FiniteRankBundleCore.coordChange_tensorPow_of_eq_smul_id`).

Together with the Whitney biproducts of `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`,
this is the structure of a symmetric monoidal preadditive category with binary biproducts, which
is what the commutative ring structure on split Grothendieck groups
(`TauCeti.SplitK0.instCommRing`) consumes: the tensor product of cores descends to the product
of classes, `[A] * [D] = [A ⊗ D]`, with the class of the trivial line bundle as unit. Pullback
along a continuous map preserves tensor products, the tensor unit, and all coherence
isomorphisms strictly, making `pullbackFunctor f` a braided monoidal functor. The base is
arbitrary, and the scalar field need not be complete.

For the tensor product of vector bundles and its transition functions see Milnor–Stasheff,
*Characteristic Classes*, §3, and Atiyah, *K-Theory*, §1.2.
-/

public section

open CategoryTheory MonoidalCategory VectorBundleCore
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
    constIso (fun _ => (Set.inter_assoc _ _ _).le) (kroneckerAssoc 𝕜 A.rank D.rank C.rank)
      fun _ _ _ _ _ => kroneckerAssoc_comp_kronecker _ _ _
  leftUnitor A :=
    constIso (fun _ => (Set.univ_inter _).le) (kroneckerLid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerLid_comp_kronecker _
  rightUnitor A :=
    constIso (fun _ => (Set.inter_univ _).le) (kroneckerRid 𝕜 A.rank)
      fun _ _ _ _ _ => kroneckerRid_comp_kronecker _

variable {A A' D D' C : FiniteRankBundleCore 𝕜 B}

@[simp] theorem rank_tensorObj (A D : FiniteRankBundleCore 𝕜 B) :
    (A ⊗ D).rank = A.rank * D.rank := (rfl)

@[simp] theorem rank_tensorUnit : (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank = 1 := (rfl)

@[simp] theorem localTriv_baseSet_tensorObj (A D : FiniteRankBundleCore 𝕜 B) (i : B) :
    ((A ⊗ D).core.localTriv i).baseSet = A.core.baseSet i ∩ D.core.baseSet i :=
  localTriv_baseSet_tensor A D i

@[simp] theorem coordChange_tensorObj (A D : FiniteRankBundleCore 𝕜 B) (i j x : B) :
    (A ⊗ D).core.coordChange i j x =
      (A.core.coordChange i j x).kronecker (D.core.coordChange i j x) :=
  coordChange_tensor A D i j x

@[simp] theorem localTriv_baseSet_tensorUnit (i : B) :
    ((𝟙_ (FiniteRankBundleCore 𝕜 B)).core.localTriv i).baseSet = Set.univ := (rfl)

@[simp] theorem coordChange_tensorUnit (i j x : B) :
    (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.coordChange i j x =
      ContinuousLinearMap.id 𝕜 (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜) := (rfl)

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
  constIso (fun _ => (Set.inter_comm _ _).le) (kroneckerComm 𝕜 A.rank D.rank)
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
      constIso (fun _ => (Set.inter_comm _ _).le) (kroneckerComm 𝕜 A.rank D.rank)
        (fun _ _ _ _ _ => kroneckerComm_comp_kronecker _ _) := (rfl)

@[simp] theorem fiberMap_braiding_hom (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).hom.fiberMap x = (kroneckerComm 𝕜 A.rank D.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_hom A D x

@[simp] theorem fiberMap_braiding_inv (A D : FiniteRankBundleCore 𝕜 B) (x : B) :
    (β_ A D).inv.fiberMap x = (kroneckerComm 𝕜 D.rank A.rank).toContinuousLinearMap :=
  fiberMap_tensorComm_inv A D x

/-- The `m`-th tensor power of a core of rank `r` has rank `r ^ m`. -/
@[simp] theorem rank_tensorPow (A : FiniteRankBundleCore 𝕜 B) :
    ∀ m : ℕ, (tensorPow A m).rank = A.rank ^ m
  | 0 => rfl
  | m + 1 => by rw [tensorPow_succ, rank_tensorObj, rank_tensorPow A m, pow_succ']

/-- Every tensor power of a core of rank one has rank one. -/
theorem rank_tensorPow_of_rank_eq_one {A : FiniteRankBundleCore 𝕜 B} (hA : A.rank = 1) (m : ℕ) :
    (tensorPow A m).rank = 1 := by
  rw [rank_tensorPow, hA, one_pow]

/-- The chart domains of a core lie in those of each of its tensor powers. -/
theorem baseSet_subset_baseSet_tensorPow (A : FiniteRankBundleCore 𝕜 B) (i : B) :
    ∀ m : ℕ, A.core.baseSet i ⊆ (tensorPow A m).core.baseSet i
  | 0 => Set.subset_univ _
  | m + 1 => Set.subset_inter subset_rfl (baseSet_subset_baseSet_tensorPow A i m)

/-- If a transition map of `A` is multiplication by `c`, the corresponding transition map of the
`m`th tensor power of `A` is multiplication by `c ^ m`. -/
theorem coordChange_tensorPow_of_eq_smul_id (A : FiniteRankBundleCore 𝕜 B) {i j x : B} {c : 𝕜}
    (hc : A.core.coordChange i j x = c • ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    ∀ m : ℕ, (tensorPow A m).core.coordChange i j x =
      c ^ m • ContinuousLinearMap.id 𝕜 (Fin (tensorPow A m).rank → 𝕜)
  | 0 => by
    rw [pow_zero, one_smul]
    -- `tensorPow A 0` is the tensor unit by definition (`tensorPow_zero`).
    exact coordChange_tensorUnit i j x
  | m + 1 => by
    rw [tensorPow_succ, coordChange_tensorObj, coordChange_tensorPow_of_eq_smul_id A hc m, hc,
      smul_kronecker, kronecker_smul, id_kronecker_id, smul_smul, ← pow_succ']
    -- The two identities are stated on `Fin (A.rank * (tensorPow A m).rank) → 𝕜`, the model of
    -- `A ⊗ tensorPow A m` by definition (`rank_tensorObj`).
    rfl

/-- Over a nonempty base, any left factor in a tensor-product isomorphism with the monoidal unit
has rank one. -/
theorem rank_eq_one_of_tensor_iso_tensorUnit [Nonempty B] {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ⊗ D ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B)) : A.rank = 1 :=
  Nat.eq_one_of_mul_eq_one_right (rank_eq_of_iso e)

section Pullback

variable {X : Type*} [TopologicalSpace X]

@[simp] theorem pullback_tensorObj (A D : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    (A ⊗ D).pullback f = A.pullback f ⊗ D.pullback f := (rfl)

@[simp] theorem pullback_tensorUnit (f : C(X, B)) :
    (𝟙_ (FiniteRankBundleCore 𝕜 B)).pullback f = 𝟙_ (FiniteRankBundleCore 𝕜 X) := (rfl)

/-- Pulling back commutes with the monoidal tensor product `⊗ₘ` of bundle morphisms; stated on
`MonoidalCategoryStruct.tensorHom` because `simp` does not unfold `⊗ₘ` to match
`pullbackMap_tensorHom`. -/
@[simp] theorem pullbackMap_tensorHom_monoidal (a : A ⟶ A') (b : D ⟶ D') (f : C(X, B)) :
    pullbackMap (a ⊗ₘ b) f = pullbackMap a f ⊗ₘ pullbackMap b f :=
  pullbackMap_tensorHom a b f

@[simp] theorem pullbackMap_whiskerLeft (A : FiniteRankBundleCore 𝕜 B) (b : D ⟶ D')
    (f : C(X, B)) :
    pullbackMap (A ◁ b) f = A.pullback f ◁ pullbackMap b f := by
  rw [← MonoidalCategory.id_tensorHom, pullbackMap_tensorHom_monoidal, pullbackMap_id,
    MonoidalCategory.id_tensorHom]

@[simp] theorem pullbackMap_whiskerRight (a : A ⟶ A') (D : FiniteRankBundleCore 𝕜 B)
    (f : C(X, B)) :
    pullbackMap (a ▷ D) f = pullbackMap a f ▷ D.pullback f := by
  rw [← MonoidalCategory.tensorHom_id, pullbackMap_tensorHom_monoidal, pullbackMap_id,
    MonoidalCategory.tensorHom_id]

@[simp] theorem pullbackMap_associator_hom (A D C : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (α_ A D C).hom f = (α_ (A.pullback f) (D.pullback f) (C.pullback f)).hom :=
  pullbackMap_constIso_hom _ _ _ f

@[simp] theorem pullbackMap_associator_inv (A D C : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (α_ A D C).inv f = (α_ (A.pullback f) (D.pullback f) (C.pullback f)).inv :=
  pullbackMap_constIso_inv _ _ _ f

@[simp] theorem pullbackMap_leftUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (λ_ A).hom f = (λ_ (A.pullback f)).hom :=
  pullbackMap_constIso_hom _ _ _ f

@[simp] theorem pullbackMap_leftUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (λ_ A).inv f = (λ_ (A.pullback f)).inv :=
  pullbackMap_constIso_inv _ _ _ f

@[simp] theorem pullbackMap_rightUnitor_hom (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (ρ_ A).hom f = (ρ_ (A.pullback f)).hom :=
  pullbackMap_constIso_hom _ _ _ f

@[simp] theorem pullbackMap_rightUnitor_inv (A : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (ρ_ A).inv f = (ρ_ (A.pullback f)).inv :=
  pullbackMap_constIso_inv _ _ _ f

@[simp] theorem pullbackMap_braiding_hom (A D : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (β_ A D).hom f = (β_ (A.pullback f) (D.pullback f)).hom :=
  pullbackMap_constIso_hom _ _ _ f

@[simp] theorem pullbackMap_braiding_inv (A D : FiniteRankBundleCore 𝕜 B) (f : C(X, B)) :
    pullbackMap (β_ A D).inv f = (β_ (A.pullback f) (D.pullback f)).inv :=
  pullbackMap_constIso_inv _ _ _ f

/-- Pullback of finite-rank cores is strictly monoidal: its unit and tensorator comparisons are
identity morphisms. -/
instance instMonoidalPullbackFunctor (f : C(X, B)) :
    (pullbackFunctor (𝕜 := 𝕜) f).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := eqToIso (pullback_tensorUnit f).symm
      μIso A D := eqToIso (pullback_tensorObj A D f).symm
      μIso_hom_natural_left a D := eq_of_heq <| by
        simp only [eqToIso.hom, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
        simp only [pullbackMap_whiskerRight]; exact HEq.rfl
      μIso_hom_natural_right A b := eq_of_heq <| by
        simp only [eqToIso.hom, comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
        simp only [pullbackMap_whiskerLeft]; exact HEq.rfl
      associativity A D C := eq_of_heq <| by
        simp only [eqToIso.hom, MonoidalCategory.eqToHom_whiskerRight,
          MonoidalCategory.whiskerLeft_eqToHom, eqToHom_trans, eqToHom_comp_heq_iff,
          heq_comp_eqToHom_iff]
        simp only [pullbackMap_associator_hom]; exact HEq.rfl
      left_unitality A := eq_of_heq <| by
        simp only [eqToIso.hom, MonoidalCategory.eqToHom_whiskerRight, heq_eqToHom_comp_iff]
        simp only [pullbackMap_leftUnitor_hom]; exact HEq.rfl
      right_unitality A := eq_of_heq <| by
        simp only [eqToIso.hom, MonoidalCategory.whiskerLeft_eqToHom, heq_eqToHom_comp_iff]
        simp only [pullbackMap_rightUnitor_hom]; exact HEq.rfl }

/-- Pullback of finite-rank cores is lax braided. -/
instance instLaxBraidedPullbackFunctor (f : C(X, B)) :
    (pullbackFunctor (𝕜 := 𝕜) f).LaxBraided where
  braided A D := eq_of_heq <| by
    simp only [Functor.CoreMonoidal.toLaxMonoidal_μ, eqToIso.hom, eqToHom_comp_heq_iff,
      heq_comp_eqToHom_iff]
    simp only [pullbackMap_braiding_hom]; exact HEq.rfl

/-- Pullback of finite-rank cores is a braided monoidal functor. -/
instance instBraidedPullbackFunctor (f : C(X, B)) :
    (pullbackFunctor (𝕜 := 𝕜) f).Braided where

@[simp] theorem pullbackFunctor_ε (f : C(X, B)) :
    Functor.LaxMonoidal.ε (pullbackFunctor (𝕜 := 𝕜) f) = 𝟙 _ := (rfl)

@[simp] theorem pullbackFunctor_μ (f : C(X, B)) (A D : FiniteRankBundleCore 𝕜 B) :
    Functor.LaxMonoidal.μ (pullbackFunctor (𝕜 := 𝕜) f) A D = 𝟙 _ := (rfl)

@[simp] theorem pullbackFunctor_η (f : C(X, B)) :
    Functor.OplaxMonoidal.η (pullbackFunctor (𝕜 := 𝕜) f) = 𝟙 _ := (rfl)

@[simp] theorem pullbackFunctor_δ (f : C(X, B)) (A D : FiniteRankBundleCore 𝕜 B) :
    Functor.OplaxMonoidal.δ (pullbackFunctor (𝕜 := 𝕜) f) A D = 𝟙 _ := (rfl)

end Pullback

end TauCeti.FiniteRankBundleCore

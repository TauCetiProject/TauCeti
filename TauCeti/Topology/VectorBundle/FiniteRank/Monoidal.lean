/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Tensor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Skeleton

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

Iterating the monoidal product on the right defines the `m`-th tensor power
`FiniteRankBundleCore.tensorPower A m` of rank `A.rank ^ m`, functorial in bundle maps and
equipped with canonical coherence isomorphisms for the unit core, first powers, addition of
exponents, and tensor products of factors, matching powers in `CategoryTheory.Skeleton`.

Together with the Whitney biproducts of `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`,
this is the structure of a symmetric monoidal preadditive category with binary biproducts, which
is what the commutative ring structure on split Grothendieck groups
(`TauCeti.SplitK0.instCommRing`) consumes: the tensor product of cores descends to the product
of classes, `[A] * [D] = [A ⊗ D]`, with the class of the trivial line bundle as unit. The base is
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

/-! ### Tensor powers of finite-rank cores -/

section TensorPower

/-- The `m`-th tensor power of a finite-rank core, defined right-recursively with the monoidal
unit `𝟙_ (FiniteRankBundleCore 𝕜 B)` at `0` and `A.tensorPower m ⊗ A` at `m + 1`. -/
-- Expose the recursive equation so the dependent fibre model reduces on concrete exponents.
@[expose]
def tensorPower (A : FiniteRankBundleCore 𝕜 B) : ℕ → FiniteRankBundleCore 𝕜 B
  | 0 => 𝟙_ (FiniteRankBundleCore 𝕜 B)
  | m + 1 => A.tensorPower m ⊗ A

@[simp] theorem tensorPower_zero (A : FiniteRankBundleCore 𝕜 B) :
    A.tensorPower 0 = 𝟙_ (FiniteRankBundleCore 𝕜 B) := (rfl)

theorem tensorPower_succ (A : FiniteRankBundleCore 𝕜 B) (m : ℕ) :
    A.tensorPower (m + 1) = A.tensorPower m ⊗ A := (rfl)

/-- The `m`-th tensor power of a core of rank `r` has rank `r ^ m`. -/
@[simp] theorem rank_tensorPower (A : FiniteRankBundleCore 𝕜 B) :
    ∀ m : ℕ, (A.tensorPower m).rank = A.rank ^ m
  | 0 => rfl
  | m + 1 => by rw [tensorPower_succ, rank_tensorObj, rank_tensorPower A m, pow_succ]

/-- The `m`-th tensor power of a bundle morphism `f : A ⟶ D`. -/
def tensorPowerHom (f : A ⟶ D) : ∀ m : ℕ, A.tensorPower m ⟶ D.tensorPower m
  | 0 => 𝟙 (𝟙_ (FiniteRankBundleCore 𝕜 B))
  | m + 1 => tensorPowerHom f m ⊗ₘ f

@[simp] theorem tensorPowerHom_zero (f : A ⟶ D) :
    tensorPowerHom f 0 = 𝟙 (𝟙_ (FiniteRankBundleCore 𝕜 B)) := (rfl)

theorem tensorPowerHom_succ (f : A ⟶ D) (m : ℕ) :
    tensorPowerHom f (m + 1) = tensorPowerHom f m ⊗ₘ f := (rfl)

/-- Taking the `m`-th tensor power preserves identity morphisms. -/
@[simp] theorem tensorPowerHom_id (A : FiniteRankBundleCore 𝕜 B) :
    ∀ m : ℕ, tensorPowerHom (𝟙 A) m = 𝟙 (A.tensorPower m)
  | 0 => rfl
  | m + 1 => by
    change tensorPowerHom (𝟙 A) m ⊗ₘ 𝟙 A = 𝟙 (A.tensorPower m ⊗ A)
    rw [tensorPowerHom_id A m, MonoidalCategory.id_tensorHom_id]

/-- Taking the `m`-th tensor power preserves composition of bundle morphisms. -/
@[reassoc (attr := simp)] theorem tensorPowerHom_comp (f : A ⟶ D) (g : D ⟶ C) :
    ∀ m : ℕ, tensorPowerHom f m ≫ tensorPowerHom g m = tensorPowerHom (f ≫ g) m
  | 0 => Category.id_comp _
  | m + 1 => by
    change (tensorPowerHom f m ⊗ₘ f) ≫ (tensorPowerHom g m ⊗ₘ g) =
      tensorPowerHom (f ≫ g) m ⊗ₘ (f ≫ g)
    rw [MonoidalCategory.tensorHom_comp_tensorHom, tensorPowerHom_comp f g m]

/-- An isomorphism of cores induces an isomorphism between their `m`-th tensor powers. -/
def tensorPowerCongr (e : A ≅ D) (m : ℕ) : A.tensorPower m ≅ D.tensorPower m where
  hom := tensorPowerHom e.hom m
  inv := tensorPowerHom e.inv m
  hom_inv_id := by rw [tensorPowerHom_comp, e.hom_inv_id, tensorPowerHom_id]
  inv_hom_id := by rw [tensorPowerHom_comp, e.inv_hom_id, tensorPowerHom_id]

@[simp] theorem tensorPowerCongr_hom (e : A ≅ D) (m : ℕ) :
    (tensorPowerCongr e m).hom = tensorPowerHom e.hom m := (rfl)

@[simp] theorem tensorPowerCongr_inv (e : A ≅ D) (m : ℕ) :
    (tensorPowerCongr e m).inv = tensorPowerHom e.inv m := (rfl)

@[simp] theorem tensorPowerCongr_refl (A : FiniteRankBundleCore 𝕜 B) (m : ℕ) :
    tensorPowerCongr (Iso.refl A) m = Iso.refl (A.tensorPower m) :=
  Iso.ext (tensorPowerHom_id A m)

@[simp] theorem tensorPowerCongr_symm (e : A ≅ D) (m : ℕ) :
    (tensorPowerCongr e m).symm = tensorPowerCongr e.symm m := (rfl)

@[simp] theorem tensorPowerCongr_trans (e₁ : A ≅ D) (e₂ : D ≅ C) (m : ℕ) :
    tensorPowerCongr (e₁ ≪≫ e₂) m = tensorPowerCongr e₁ m ≪≫ tensorPowerCongr e₂ m :=
  Iso.ext (tensorPowerHom_comp e₁.hom e₂.hom m).symm

/-- The first tensor power of a core is canonically isomorphic to the core itself via the left
unitor. -/
def tensorPowerOne (A : FiniteRankBundleCore 𝕜 B) : A.tensorPower 1 ≅ A :=
  λ_ A

@[simp] theorem tensorPowerOne_hom (A : FiniteRankBundleCore 𝕜 B) :
    (tensorPowerOne A).hom = (λ_ A).hom := (rfl)

@[simp] theorem tensorPowerOne_inv (A : FiniteRankBundleCore 𝕜 B) :
    (tensorPowerOne A).inv = (λ_ A).inv := (rfl)

/-- Every tensor power of the monoidal unit is canonically isomorphic to the monoidal unit. -/
def tensorUnitTensorPowerIso :
    ∀ m : ℕ, (𝟙_ (FiniteRankBundleCore 𝕜 B)).tensorPower m ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B)
  | 0 => Iso.refl _
  | m + 1 => (tensorUnitTensorPowerIso m ⊗ᵢ Iso.refl _) ≪≫ λ_ _

@[simp] theorem tensorUnitTensorPowerIso_zero :
    tensorUnitTensorPowerIso (𝕜 := 𝕜) (B := B) 0 = Iso.refl _ := (rfl)

theorem tensorUnitTensorPowerIso_succ (m : ℕ) :
    tensorUnitTensorPowerIso (𝕜 := 𝕜) (B := B) (m + 1) =
      (tensorUnitTensorPowerIso m ⊗ᵢ Iso.refl _) ≪≫ λ_ _ := (rfl)

/-- Tensor powers convert sums of exponents into tensor products. -/
def tensorPowerAdd (A : FiniteRankBundleCore 𝕜 B) (m : ℕ) :
    ∀ k : ℕ, A.tensorPower (m + k) ≅ A.tensorPower m ⊗ A.tensorPower k
  | 0 => (ρ_ (A.tensorPower m)).symm
  | k + 1 => (tensorPowerAdd A m k ⊗ᵢ Iso.refl A) ≪≫ α_ (A.tensorPower m) (A.tensorPower k) A

@[simp] theorem tensorPowerAdd_zero (A : FiniteRankBundleCore 𝕜 B) (m : ℕ) :
    tensorPowerAdd A m 0 = (ρ_ (A.tensorPower m)).symm := (rfl)

theorem tensorPowerAdd_succ (A : FiniteRankBundleCore 𝕜 B) (m k : ℕ) :
    tensorPowerAdd A m (k + 1) =
      (tensorPowerAdd A m k ⊗ᵢ Iso.refl A) ≪≫ α_ (A.tensorPower m) (A.tensorPower k) A := (rfl)

/-- Tensor powers distribute over tensor products of cores via the symmetric braiding. -/
def tensorTensorPowerIso (A D : FiniteRankBundleCore 𝕜 B) :
    ∀ m : ℕ, (A ⊗ D).tensorPower m ≅ A.tensorPower m ⊗ D.tensorPower m
  | 0 => (λ_ (𝟙_ (FiniteRankBundleCore 𝕜 B))).symm
  | m + 1 =>
    (tensorTensorPowerIso A D m ⊗ᵢ Iso.refl (A ⊗ D)) ≪≫
      { hom := tensorμ (A.tensorPower m) (D.tensorPower m) A D
        inv := tensorδ (A.tensorPower m) (D.tensorPower m) A D
        hom_inv_id := tensorμ_tensorδ _ _ _ _
        inv_hom_id := tensorδ_tensorμ _ _ _ _ }

@[simp] theorem tensorTensorPowerIso_zero (A D : FiniteRankBundleCore 𝕜 B) :
    tensorTensorPowerIso A D 0 = (λ_ (𝟙_ (FiniteRankBundleCore 𝕜 B))).symm := (rfl)

theorem tensorTensorPowerIso_succ (A D : FiniteRankBundleCore 𝕜 B) (m : ℕ) :
    tensorTensorPowerIso A D (m + 1) =
      (tensorTensorPowerIso A D m ⊗ᵢ Iso.refl (A ⊗ D)) ≪≫
        { hom := tensorμ (A.tensorPower m) (D.tensorPower m) A D
          inv := tensorδ (A.tensorPower m) (D.tensorPower m) A D
          hom_inv_id := tensorμ_tensorδ _ _ _ _
          inv_hom_id := tensorδ_tensorμ _ _ _ _ } := (rfl)

/-- In the monoidal skeleton of `FiniteRankBundleCore 𝕜 B`, the class of `A.tensorPower m` is the
`m`-th monoid power of the class of `A`. -/
@[simp] theorem toSkeleton_tensorPower (A : FiniteRankBundleCore 𝕜 B) :
    ∀ m : ℕ, toSkeleton (A.tensorPower m) = toSkeleton A ^ m
  | 0 => by
    rw [tensorPower_zero, pow_zero]
    rfl
  | m + 1 => by
    rw [tensorPower_succ, Skeleton.toSkeleton_tensorObj, toSkeleton_tensorPower A m, pow_succ]

end TensorPower

section TensorUnitCriteria

@[simp] theorem coordChange_tensorUnit (i j x : B) :
    (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.coordChange i j x =
      ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜) :=
  (rfl)

/-- Isomorphic finite-rank cores over a nonempty base have the same rank. -/
theorem rank_eq_of_iso [Nonempty B] {A D : FiniteRankBundleCore 𝕜 B} (e : A ≅ D) :
    A.rank = D.rank := by
  obtain ⟨x⟩ := ‹Nonempty B›
  calc
    A.rank = Module.finrank 𝕜 ((fiberFunctor (𝕜 := 𝕜) x).obj A) :=
      (Module.finrank_fin_fun 𝕜).symm
    _ = Module.finrank 𝕜 ((fiberFunctor (𝕜 := 𝕜) x).obj D) :=
      ((fiberFunctor (𝕜 := 𝕜) x).mapIso e).toLinearEquiv.finrank_eq
    _ = D.rank := Module.finrank_fin_fun 𝕜

/-- Over a nonempty base, any left factor in a tensor-product isomorphism with the monoidal unit
has rank one. -/
theorem rank_eq_one_of_tensor_iso_tensorUnit [Nonempty B] {A D : FiniteRankBundleCore 𝕜 B}
    (e : A ⊗ D ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B)) : A.rank = 1 :=
  Nat.eq_one_of_mul_eq_one_right (rank_eq_of_iso e)

/-- A core whose transition maps on chart overlaps are all the identity, equipped with a continuous
linear equivalence of its model fibre with `Fin 1 → 𝕜`, is canonically isomorphic to the monoidal
unit `𝟙_ (FiniteRankBundleCore 𝕜 B)` even when its chart domains are proper subsets of `B`. -/
def isoTensorUnitOfCoordChangeEqId (A : FiniteRankBundleCore 𝕜 B)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) :
    A ≅ 𝟙_ (FiniteRankBundleCore 𝕜 B) where
  hom :=
    { operator := fun _ _ ↦ ⟨fun _ ↦ e.toContinuousLinearMap, continuous_const⟩
      compatible := fun i i' _ _ x hi hi' _ _ v ↦ by
        rw [coordChange_tensorUnit, h i i' x hi hi']
        rfl }
  inv :=
    { operator := fun _ _ ↦ ⟨fun _ ↦ e.symm.toContinuousLinearMap, continuous_const⟩
      compatible := fun _ _ j j' x _ _ hj hj' v ↦ by
        rw [coordChange_tensorUnit, h j j' x hj hj']
        rfl }
  hom_inv_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def, fiberMap_id]
    ext v : 1
    exact e.symm_apply_apply v
  inv_hom_id := hom_ext fun x ↦ by
    rw [fiberMap_comp, CoordinateHom.fiberMap_def, CoordinateHom.fiberMap_def, fiberMap_id]
    ext v : 1
    exact e.apply_symm_apply v

theorem operator_isoTensorUnitOfCoordChangeEqId_hom (A : FiniteRankBundleCore 𝕜 B)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
    (i j : B) (x : ↥(A.core.baseSet i ∩ (𝟙_ (FiniteRankBundleCore 𝕜 B)).core.baseSet j)) :
    (isoTensorUnitOfCoordChangeEqId A e h).hom.operator i j x = e.toContinuousLinearMap :=
  (rfl)

theorem operator_isoTensorUnitOfCoordChangeEqId_inv (A : FiniteRankBundleCore 𝕜 B)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜))
    (i j : B) (x : ↥((𝟙_ (FiniteRankBundleCore 𝕜 B)).core.baseSet i ∩ A.core.baseSet j)) :
    (isoTensorUnitOfCoordChangeEqId A e h).inv.operator i j x = e.symm.toContinuousLinearMap :=
  (rfl)

@[simp] theorem fiberMap_isoTensorUnitOfCoordChangeEqId_hom (A : FiniteRankBundleCore 𝕜 B)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (x : B) :
    (isoTensorUnitOfCoordChangeEqId A e h).hom.fiberMap x = e.toContinuousLinearMap := by
  rw [CoordinateHom.fiberMap_def]
  rfl

@[simp] theorem fiberMap_isoTensorUnitOfCoordChangeEqId_inv (A : FiniteRankBundleCore 𝕜 B)
    (e : (Fin A.rank → 𝕜) ≃L[𝕜] (Fin (𝟙_ (FiniteRankBundleCore 𝕜 B)).rank → 𝕜))
    (h : ∀ i j x, x ∈ A.core.baseSet i → x ∈ A.core.baseSet j →
      A.core.coordChange i j x = ContinuousLinearMap.id 𝕜 (Fin A.rank → 𝕜)) (x : B) :
    (isoTensorUnitOfCoordChangeEqId A e h).inv.fiberMap x = e.symm.toContinuousLinearMap := by
  rw [CoordinateHom.fiberMap_def]
  rfl

end TensorUnitCriteria

end TauCeti.FiniteRankBundleCore

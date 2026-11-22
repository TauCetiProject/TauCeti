/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety
public import TauCeti.AlgebraicGeometry.AbelianScheme.Product
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Rigidity
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# Abelian schemes over a field: commutativity, rigidity, morphism groups, and products

`TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety` establishes the adapters
`AbelianScheme.ofAbelianVariety` and `AbelianScheme.toAbelianVariety` and the equivalence of
categories `AbelianScheme.fieldEquivalence : AbelianScheme (Spec (.of K)) ≌ AbelianVariety K`.

This file supplies the additional structure and compatibility results over a field:

* `AbelianScheme.isCommMonObj_field`: the group law of an abelian scheme over a field is
  commutative;
* `AbelianScheme.homEquivPointed`: over a field, homomorphisms of abelian schemes are equivalent
  to zero-preserving morphisms over `Spec K`;
* `AbelianScheme.Field.instCommGroup` and `AbelianScheme.Field.toAbelianVarietyMulEquiv`: the
  pointwise commutative group structure on homomorphisms over a field;
* `AbelianScheme.toAbelianVarietyIdentityIso`, `AbelianScheme.ofAbelianVarietyTrivialIso`,
  `AbelianScheme.toAbelianVarietyProdIso`, `AbelianScheme.ofAbelianVarietyProdIso`, and
  `AbelianScheme.toAbelianVarietyBaseChangeNatIso`: compatibility of the adapters with the zero
  object, binary products, and base change along field extensions.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {K : Type u} [Field K]

noncomputable section

/-! ### Underlying schemes and zero sections under the field adapters -/

@[simp]
lemma ofAbelianVariety_toScheme (A : AbelianVariety K) :
    (ofAbelianVariety A).toScheme = A.toScheme :=
  (rfl)

@[simp]
lemma toAbelianVariety_toScheme (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.toScheme = A.toScheme :=
  (rfl)

@[simp]
lemma ofAbelianVariety_zeroSection (A : AbelianVariety K) :
    (ofAbelianVariety A).zeroSection = A.zeroSection :=
  (rfl)

@[simp]
lemma toAbelianVariety_zeroSection (A : AbelianScheme (Spec (.of K))) :
    A.toAbelianVariety.zeroSection = A.zeroSection :=
  (rfl)

/-! ### Commutativity and pointed morphisms over a field -/

/-- The group law of an abelian scheme over a field is commutative. -/
instance isCommMonObj_field (A : AbelianScheme (Spec (.of K))) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

/-- Over a field, homomorphisms of abelian schemes are equivalent to morphisms over `Spec K`
preserving the identity section. -/
def homEquivPointed (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]} where
  toFun f := ⟨toOverHom f, one_hom f⟩
  invFun f := homMk f.val f.property (isMonHom_of_one_hom f.val f.property).mul_hom
  left_inv _ := toOverHom_injective (toOverHom_homMk _ _ _)
  right_inv _ := Subtype.ext (toOverHom_homMk _ _ _)

@[simp]
lemma coe_homEquivPointed_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (homEquivPointed A B f : A.toOver ⟶ B.toOver) = toOverHom f :=
  (rfl)

@[simp]
lemma toOverHom_homEquivPointed_symm_apply {A B : AbelianScheme (Spec (.of K))}
    (f : {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]}) :
    toOverHom ((homEquivPointed A B).symm f) = f.val :=
  toOverHom_homMk _ _ _

/-! ### Pointwise group structure on homomorphisms over a field -/

private lemma isEquivalence_toAbelianVarietyFunctor :
    (toAbelianVarietyFunctor (K := K)).IsEquivalence :=
  fieldEquivalence_functor (K := K) ▸
    (inferInstance : (fieldEquivalence (K := K)).functor.IsEquivalence)

private lemma isEquivalence_ofAbelianVarietyFunctor :
    (ofAbelianVarietyFunctor (K := K)).IsEquivalence :=
  fieldEquivalence_inverse (K := K) ▸
    (inferInstance : (fieldEquivalence (K := K)).inverse.IsEquivalence)

namespace Field

open scoped AbelianVariety.Hom

attribute [local instance] isEquivalence_toAbelianVarietyFunctor

/-- The bijection on homomorphisms induced by `fieldEquivalence`. -/
def homEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ (toAbelianVariety A ⟶ toAbelianVariety B) :=
  (Functor.FullyFaithful.ofFullyFaithful (toAbelianVarietyFunctor (K := K))).homEquiv

/-- Over a field, homomorphisms of abelian schemes form a commutative group under the pointwise
group law of the target. -/
scoped instance instCommGroup (A B : AbelianScheme (Spec (.of K))) : CommGroup (A ⟶ B) :=
  (homEquiv A B).commGroup

/-- Over a field, `toAbelianVarietyFunctor.map` is a group isomorphism for the pointwise group
laws. -/
def toAbelianVarietyMulEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃* (toAbelianVariety A ⟶ toAbelianVariety B) where
  __ := homEquiv A B
  map_mul' _ _ := (homEquiv A B).apply_symm_apply _

@[simp]
lemma toAbelianVarietyMulEquiv_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    toAbelianVarietyMulEquiv A B f = toAbelianVarietyFunctor.map f :=
  (rfl)

@[simp]
lemma toOverHom_one (A B : AbelianScheme (Spec (.of K))) :
    toOverHom (1 : A ⟶ B) = 1 :=
  (toOverHom_toAbelianVarietyFunctor_map (1 : A ⟶ B)).symm.trans <|
    (congrArg AbelianVariety.Hom.toOverHom (map_one (toAbelianVarietyMulEquiv A B))).trans
      AbelianVariety.Hom.toOverHom_one

@[simp]
lemma toOverHom_mul {A B : AbelianScheme (Spec (.of K))} (f g : A ⟶ B) :
    toOverHom (f * g) = toOverHom f * toOverHom g :=
  (toOverHom_toAbelianVarietyFunctor_map (f * g)).symm.trans <|
    (congrArg AbelianVariety.Hom.toOverHom (map_mul (toAbelianVarietyMulEquiv A B) f g)).trans <|
      (AbelianVariety.Hom.toOverHom_mul (toAbelianVarietyMulEquiv A B f)
        (toAbelianVarietyMulEquiv A B g)).trans <|
        congrArg₂ (· * ·) (toOverHom_toAbelianVarietyFunctor_map f)
          (toOverHom_toAbelianVarietyFunctor_map g)

@[simp]
lemma toOverHom_inv {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    toOverHom f⁻¹ = (toOverHom f)⁻¹ :=
  (toOverHom_toAbelianVarietyFunctor_map f⁻¹).symm.trans <|
    (congrArg AbelianVariety.Hom.toOverHom (map_inv (toAbelianVarietyMulEquiv A B) f)).trans <|
      (AbelianVariety.Hom.toOverHom_inv (toAbelianVarietyMulEquiv A B f)).trans <|
        congrArg Inv.inv (toOverHom_toAbelianVarietyFunctor_map f)

end Field

/-! ### Compatibility with zero, products, and base change along field extensions -/

section Compatibility

attribute [local instance] isEquivalence_toAbelianVarietyFunctor
  isEquivalence_ofAbelianVarietyFunctor

/-- `toAbelianVariety` sends `identity (Spec K)` to `AbelianVariety.trivial K`. -/
def toAbelianVarietyIdentityIso (K : Type u) [Field K] :
    toAbelianVariety (identity (Spec (.of K))) ≅ AbelianVariety.trivial K :=
  ((isTerminalIdentity (Spec (.of K))).isTerminalObj
    (toAbelianVarietyFunctor (K := K))).uniqueUpToIso (AbelianVariety.isTerminalTrivial K)

/-- `ofAbelianVariety` sends `AbelianVariety.trivial K` to `identity (Spec K)`. -/
def ofAbelianVarietyTrivialIso (K : Type u) [Field K] :
    ofAbelianVariety (AbelianVariety.trivial K) ≅ identity (Spec (.of K)) :=
  ((AbelianVariety.isTerminalTrivial K).isTerminalObj
    (ofAbelianVarietyFunctor (K := K))).uniqueUpToIso (isTerminalIdentity (Spec (.of K)))

private def avBinaryFan (A B : AbelianVariety K) : BinaryFan A B :=
  BinaryFan.mk (AbelianVariety.prod.fst A B) (AbelianVariety.prod.snd A B)

private def avBinaryFanIsLimit (A B : AbelianVariety K) : IsLimit (avBinaryFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦ AbelianVariety.prod.lift f g)
    (fun f g ↦ AbelianVariety.prod.lift_fst f g)
    (fun f g ↦ AbelianVariety.prod.lift_snd f g)
    (fun f g _ hfst hsnd ↦ AbelianVariety.prod.hom_ext
      (hfst.trans (AbelianVariety.prod.lift_fst f g).symm)
      (hsnd.trans (AbelianVariety.prod.lift_snd f g).symm))

/-- `toAbelianVariety` preserves binary products, compatibly with projections. -/
def toAbelianVarietyProdIso (A B : AbelianScheme (Spec (.of K))) :
    toAbelianVariety (A.prod B) ≅ (toAbelianVariety A).prod (toAbelianVariety B) :=
  (mapIsLimitOfPreservesOfIsLimit toAbelianVarietyFunctor _ _
    (prod.binaryFanIsLimit A B)).conePointUniqueUpToIso
    (avBinaryFanIsLimit (toAbelianVariety A) (toAbelianVariety B))

@[simp]
lemma toAbelianVarietyProdIso_hom_fst (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.fst (toAbelianVariety A) (toAbelianVariety B) =
      toAbelianVarietyFunctor.map (prod.fst A B) :=
  (mapIsLimitOfPreservesOfIsLimit toAbelianVarietyFunctor _ _
    (prod.binaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (avBinaryFanIsLimit (toAbelianVariety A) (toAbelianVariety B)) ⟨WalkingPair.left⟩

@[simp]
lemma toAbelianVarietyProdIso_hom_snd (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.snd (toAbelianVariety A) (toAbelianVariety B) =
      toAbelianVarietyFunctor.map (prod.snd A B) :=
  (mapIsLimitOfPreservesOfIsLimit toAbelianVarietyFunctor _ _
    (prod.binaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (avBinaryFanIsLimit (toAbelianVariety A) (toAbelianVariety B)) ⟨WalkingPair.right⟩

/-- `ofAbelianVariety` preserves binary products, compatibly with projections. -/
def ofAbelianVarietyProdIso (A B : AbelianVariety K) :
    ofAbelianVariety (A.prod B) ≅ (ofAbelianVariety A).prod (ofAbelianVariety B) :=
  (mapIsLimitOfPreservesOfIsLimit ofAbelianVarietyFunctor _ _
    (avBinaryFanIsLimit A B)).conePointUniqueUpToIso
    (prod.binaryFanIsLimit (ofAbelianVariety A) (ofAbelianVariety B))

@[simp]
lemma ofAbelianVarietyProdIso_hom_fst (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.fst (ofAbelianVariety A) (ofAbelianVariety B) =
      ofAbelianVarietyFunctor.map (AbelianVariety.prod.fst A B) :=
  (mapIsLimitOfPreservesOfIsLimit ofAbelianVarietyFunctor _ _
    (avBinaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (prod.binaryFanIsLimit (ofAbelianVariety A) (ofAbelianVariety B)) ⟨WalkingPair.left⟩

@[simp]
lemma ofAbelianVarietyProdIso_hom_snd (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.snd (ofAbelianVariety A) (ofAbelianVariety B) =
      ofAbelianVarietyFunctor.map (AbelianVariety.prod.snd A B) :=
  (mapIsLimitOfPreservesOfIsLimit ofAbelianVarietyFunctor _ _
    (avBinaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (prod.binaryFanIsLimit (ofAbelianVariety A) (ofAbelianVariety B)) ⟨WalkingPair.right⟩

end Compatibility

/-- Naturality of `toAbelianVariety_baseChange`: the adapter functor commutes with base change
along a field extension `K → L`. -/
def toAbelianVarietyBaseChangeNatIso (L : Type u) [Field L] [Algebra K L] :
    baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
        toAbelianVarietyFunctor (K := L) ≅
      toAbelianVarietyFunctor (K := K) ⋙ AbelianVariety.baseChangeFunctor L :=
  NatIso.ofComponents
    (fun A ↦ eqToIso (by simp [toAbelianVariety_baseChange]))
    fun {A B} φ ↦ by
      apply AbelianVariety.Hom.toOverHom_injective
      have htoOver_eqToHom : ∀ {X Y : AbelianVariety L} (h : X = Y),
          AbelianVariety.Hom.toOverHom (eqToHom h) = eqToHom (congrArg AbelianVariety.toOver h) :=
        fun h ↦ eqToHom_map AbelianVariety.Hom.toOverFunctor h
      have hlhs :
          AbelianVariety.Hom.toOverHom
              ((baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
                  toAbelianVarietyFunctor (K := L)).map φ ≫
                (eqToIso (by simp [toAbelianVariety_baseChange] :
                  (baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
                    toAbelianVarietyFunctor (K := L)).obj B =
                  (toAbelianVarietyFunctor (K := K) ⋙
                    AbelianVariety.baseChangeFunctor L).obj B)).hom) =
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (toOverHom φ) ≫
              eqToHom (by simp [AbelianVariety.baseChange_toOver] :
                (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj B.toOver =
                ((toAbelianVarietyFunctor (K := K) ⋙
                  AbelianVariety.baseChangeFunctor L).obj B).toOver) := by
        rw [AbelianVariety.Hom.toOverHom_comp, eqToIso.hom, htoOver_eqToHom]
        exact congrArg (· ≫ _)
          ((toOverHom_toAbelianVarietyFunctor_map _).trans (toOverHom_baseChangeFunctor_map _ φ))
      have hrhs :
          AbelianVariety.Hom.toOverHom
              ((eqToIso (by simp [toAbelianVariety_baseChange] :
                  (baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
                    toAbelianVarietyFunctor (K := L)).obj A =
                  (toAbelianVarietyFunctor (K := K) ⋙
                    AbelianVariety.baseChangeFunctor L).obj A)).hom ≫
                (toAbelianVarietyFunctor (K := K) ⋙
                  AbelianVariety.baseChangeFunctor L).map φ) =
            (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (toOverHom φ) ≫
              eqToHom (by simp [AbelianVariety.baseChange_toOver] :
                (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj B.toOver =
                ((toAbelianVarietyFunctor (K := K) ⋙
                  AbelianVariety.baseChangeFunctor L).obj B).toOver) := by
        rw [AbelianVariety.Hom.toOverHom_comp, eqToIso.hom, htoOver_eqToHom]
        dsimp only [Functor.comp_map]
        rw [AbelianVariety.baseChangeFunctor_map, AbelianVariety.Hom.toOverHom_comp,
          AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_baseChange,
          htoOver_eqToHom, htoOver_eqToHom]
        have hconj : ∀ {X Y Z : Over (Spec (.of L))} {f g : X ⟶ Y}
            (_ : f = g) (hX : X = X) (hZ : Y = Z),
            eqToHom hX ≫ f ≫ eqToHom hZ = g ≫ eqToHom hZ := by
          intro X Y Z f g hfg hX hZ
          rw [eqToHom_refl, Category.id_comp, hfg]
        simp only [Category.assoc]
        rw [eqToHom_trans_assoc, eqToHom_trans_assoc, eqToHom_trans]
        exact hconj (congrArg (Over.pullback _).map (toOverHom_toAbelianVarietyFunctor_map φ)) _ _
      exact hlhs.trans hrhs.symm

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

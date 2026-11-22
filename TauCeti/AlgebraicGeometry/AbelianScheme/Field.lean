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
* `AbelianScheme.Field.homEquiv` and `AbelianScheme.Field.toAbelianVarietyMulEquiv`: the
  pointwise commutative group equivalence on homomorphisms over a field, specializing
  `AbelianScheme.instCommGroup`;
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

/-! ### Commutativity and pointwise group structure on homomorphisms over a field -/

/-- The group law of an abelian scheme over a field is commutative. -/
instance isCommMonObj_field (A : AbelianScheme (Spec (.of K))) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

namespace Field

open scoped TauCeti.AlgebraicGeometry.AbelianScheme AbelianVariety.Hom

/-- The bijection on homomorphisms induced by `fieldEquivalence`. -/
def homEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ (toAbelianVariety A ⟶ toAbelianVariety B) :=
  (Functor.FullyFaithful.ofFullyFaithful (toAbelianVarietyFunctor (K := K))).homEquiv

/-- Over a field, `toAbelianVarietyFunctor.map` is a group isomorphism for the pointwise group
laws. -/
def toAbelianVarietyMulEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃* (toAbelianVariety A ⟶ toAbelianVariety B) where
  __ := homEquiv A B
  map_mul' f g := AbelianVariety.Hom.toOverHom_injective <| by
    change AbelianVariety.Hom.toOverHom (toAbelianVarietyFunctor.map (f * g)) =
      AbelianVariety.Hom.toOverHom
        (toAbelianVarietyFunctor.map f * toAbelianVarietyFunctor.map g)
    rw [toOverHom_toAbelianVarietyFunctor_map, toOverHom_mul, AbelianVariety.Hom.toOverHom_mul,
      toOverHom_toAbelianVarietyFunctor_map, toOverHom_toAbelianVarietyFunctor_map]
    simp only [CategoryTheory.Hom.mul_def]
    rfl

@[simp]
lemma toAbelianVarietyMulEquiv_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    toAbelianVarietyMulEquiv A B f = toAbelianVarietyFunctor.map f :=
  (rfl)

end Field

/-- Over a field, homomorphisms of abelian schemes are equivalent to morphisms over `Spec K`
preserving the identity section. -/
def homEquivPointed (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]} :=
  (Field.homEquiv A B).trans
    (AbelianVariety.Hom.equivPointed A.toAbelianVariety B.toAbelianVariety)

@[simp]
lemma coe_homEquivPointed_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (homEquivPointed A B f : A.toOver ⟶ B.toOver) = toOverHom f :=
  (AbelianVariety.coe_equivPointed_apply (Field.homEquiv A B f)).trans
    (toOverHom_toAbelianVarietyFunctor_map f)

@[simp]
lemma toOverHom_homEquivPointed_symm_apply {A B : AbelianScheme (Spec (.of K))}
    (f : {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]}) :
    toOverHom ((homEquivPointed A B).symm f) = f.val :=
  (toOverHom_toAbelianVarietyFunctor_map _).symm.trans <|
    (congrArg AbelianVariety.Hom.toOverHom ((Field.homEquiv A B).apply_symm_apply _)).trans
      (AbelianVariety.Hom.toOverHom_equivPointed_symm_apply
        (A := A.toAbelianVariety) (B := B.toAbelianVariety) f)

/-! ### Compatibility with zero, products, and base change along field extensions -/

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

private def abelianSchemeProdIsLimit (A B : AbelianScheme (Spec (.of K))) :
    IsLimit (BinaryFan.mk (prod.fst A B) (prod.snd A B)) := by
  rw [← prod.binaryFan_def]
  exact prod.binaryFanIsLimit A B

private def abelianVarietyProdIsLimit (A B : AbelianVariety K) :
    IsLimit (BinaryFan.mk (AbelianVariety.prod.fst A B) (AbelianVariety.prod.snd A B)) := by
  rw [← AbelianVariety.prod.binaryFan_def]
  exact AbelianVariety.prod.binaryFanIsLimit A B

private def toAbelianVarietyProdIsLimit (A B : AbelianScheme (Spec (.of K))) :
    IsLimit (BinaryFan.mk (toAbelianVarietyFunctor.map (prod.fst A B))
      (toAbelianVarietyFunctor.map (prod.snd A B))) :=
  mapIsLimitOfPreservesOfIsLimit toAbelianVarietyFunctor (prod.fst A B) (prod.snd A B)
    (abelianSchemeProdIsLimit A B)

private def ofAbelianVarietyProdIsLimit (A B : AbelianVariety K) :
    IsLimit (BinaryFan.mk (ofAbelianVarietyFunctor.map (AbelianVariety.prod.fst A B))
      (ofAbelianVarietyFunctor.map (AbelianVariety.prod.snd A B))) :=
  mapIsLimitOfPreservesOfIsLimit ofAbelianVarietyFunctor
    (AbelianVariety.prod.fst A B) (AbelianVariety.prod.snd A B) (abelianVarietyProdIsLimit A B)

/-- `toAbelianVariety` preserves binary products, compatibly with projections. -/
def toAbelianVarietyProdIso (A B : AbelianScheme (Spec (.of K))) :
    toAbelianVariety (A.prod B) ≅ (toAbelianVariety A).prod (toAbelianVariety B) :=
  (toAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso
    (abelianVarietyProdIsLimit (toAbelianVariety A) (toAbelianVariety B))

@[simp]
lemma toAbelianVarietyProdIso_hom_fst (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.fst (toAbelianVariety A) (toAbelianVariety B) =
      toAbelianVarietyFunctor.map (prod.fst A B) :=
  (toAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso_hom_comp
    (abelianVarietyProdIsLimit (toAbelianVariety A) (toAbelianVariety B)) ⟨WalkingPair.left⟩

@[simp]
lemma toAbelianVarietyProdIso_hom_snd (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.snd (toAbelianVariety A) (toAbelianVariety B) =
      toAbelianVarietyFunctor.map (prod.snd A B) :=
  (toAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso_hom_comp
    (abelianVarietyProdIsLimit (toAbelianVariety A) (toAbelianVariety B)) ⟨WalkingPair.right⟩

/-- `ofAbelianVariety` preserves binary products, compatibly with projections. -/
def ofAbelianVarietyProdIso (A B : AbelianVariety K) :
    ofAbelianVariety (A.prod B) ≅ (ofAbelianVariety A).prod (ofAbelianVariety B) :=
  (ofAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso
    (abelianSchemeProdIsLimit (ofAbelianVariety A) (ofAbelianVariety B))

@[simp]
lemma ofAbelianVarietyProdIso_hom_fst (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.fst (ofAbelianVariety A) (ofAbelianVariety B) =
      ofAbelianVarietyFunctor.map (AbelianVariety.prod.fst A B) :=
  (ofAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso_hom_comp
    (abelianSchemeProdIsLimit (ofAbelianVariety A) (ofAbelianVariety B)) ⟨WalkingPair.left⟩

@[simp]
lemma ofAbelianVarietyProdIso_hom_snd (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.snd (ofAbelianVariety A) (ofAbelianVariety B) =
      ofAbelianVarietyFunctor.map (AbelianVariety.prod.snd A B) :=
  (ofAbelianVarietyProdIsLimit A B).conePointUniqueUpToIso_hom_comp
    (abelianSchemeProdIsLimit (ofAbelianVariety A) (ofAbelianVariety B)) ⟨WalkingPair.right⟩

private lemma toOverHom_eqToHom {L : Type u} [Field L] {A B : AbelianVariety L} (h : A = B) :
    AbelianVariety.Hom.toOverHom (eqToHom h) = eqToHom (congrArg AbelianVariety.toOver h) := by
  subst h
  exact AbelianVariety.Hom.toOverHom_id A

private lemma toOverHom_abelianVarietyBaseChangeFunctor_map {A B : AbelianVariety K} (f : A ⟶ B)
    (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety.Hom.toOverHom ((AbelianVariety.baseChangeFunctor L).map f) =
      eqToHom (by rw [AbelianVariety.baseChangeFunctor_obj, AbelianVariety.baseChange_toOver]) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
          (AbelianVariety.Hom.toOverHom f) ≫
        eqToHom (by
          rw [AbelianVariety.baseChangeFunctor_obj, AbelianVariety.baseChange_toOver]) := by
  rw [AbelianVariety.baseChangeFunctor_map, AbelianVariety.Hom.toOverHom_comp,
    AbelianVariety.Hom.toOverHom_comp, toOverHom_eqToHom, toOverHom_eqToHom,
    AbelianVariety.Hom.toOverHom_baseChange]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

private lemma toOverHom_toAbelianVarietyBaseChange_map {A B : AbelianScheme (Spec (.of K))}
    (φ : A ⟶ B) (L : Type u) [Field L] [Algebra K L] :
    AbelianVariety.Hom.toOverHom
        ((baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
          toAbelianVarietyFunctor (K := L)).map φ) =
      eqToHom (rfl : ((baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
          toAbelianVarietyFunctor (K := L)).obj A).toOver =
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj A.toOver) ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map (toOverHom φ) ≫
        eqToHom (rfl : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj
            B.toOver =
          ((baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
            toAbelianVarietyFunctor (K := L)).obj B).toOver) := by
  rw [Functor.comp_map, toOverHom_toAbelianVarietyFunctor_map, toOverHom_baseChangeFunctor_map]
  exact (Category.id_comp _).symm.trans (Category.comp_id _).symm

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
      rw [eqToIso.hom, eqToIso.hom, AbelianVariety.Hom.toOverHom_comp,
        AbelianVariety.Hom.toOverHom_comp, toOverHom_eqToHom, toOverHom_eqToHom,
        toOverHom_toAbelianVarietyBaseChange_map, Functor.comp_map,
        toOverHom_abelianVarietyBaseChangeFunctor_map]
      simp only [eqToHom_trans_assoc]
      rw [toOverHom_toAbelianVarietyFunctor_map]
      simp only [eqToHom_refl, Category.id_comp]
      rfl

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

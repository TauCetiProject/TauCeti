/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.Product
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.BaseChange
public import TauCeti.AlgebraicGeometry.AbelianVariety.Hom.Rigidity
public import TauCeti.AlgebraicGeometry.AbelianVariety.Product
public import TauCeti.AlgebraicGeometry.AbelianVariety.Trivial

/-!
# Abelian schemes over a field

Over the spectrum `Spec K` of a field `K`, an abelian scheme is equivalent to an abelian variety
over `K` (`TauCeti.AlgebraicGeometry.AbelianVariety K`):

* `AbelianScheme.ofAbelianVariety` sends an abelian variety `A : AbelianVariety K` to an abelian
  scheme over `Spec K` using its derived smoothness and geometric connectedness;
* `AbelianScheme.toAbelianVariety` sends an abelian scheme `A : AbelianScheme (Spec (.of K))` to an
  abelian variety over `K` using `AbelianScheme.geometricallyIntegral`;
* `AbelianScheme.fieldEquivalence` packages these inverse adapters as an equivalence of categories
  `AbelianScheme (Spec (.of K)) ≌ AbelianVariety K`.

Over a field, the group law of an abelian scheme is commutative (`AbelianScheme.isCommMonObj_field`)
and every zero-preserving morphism over `Spec K` is automatically a homomorphism
(`AbelianScheme.Hom.equivPointed`). The adapters preserve the pointwise commutative group law on
homomorphisms (`AbelianScheme.Field.toAbelianVarietyMulEquiv`), the zero object
(`AbelianScheme.toAbelianVarietyIdentityIso`, `AbelianScheme.ofAbelianVarietyTrivialIso`),
binary products (`AbelianScheme.toAbelianVarietyProdIso`,
`AbelianScheme.ofAbelianVarietyProdIso`), and base change along field extensions
(`AbelianScheme.toAbelianVarietyBaseChangeIso`, `AbelianScheme.ofAbelianVarietyBaseChangeIso`).
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

/-! ### Adapters between `AbelianScheme (Spec (.of K))` and `AbelianVariety K` -/

/-- Regard an abelian variety over `K` as an abelian scheme over `Spec K`. -/
def ofAbelianVariety (A : AbelianVariety K) : AbelianScheme (Spec (.of K)) where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  smooth := A.smooth
  geometricallyConnected := A.geometricallyConnected

/-- Regard an abelian scheme over `Spec K` as an abelian variety over `K`. -/
def toAbelianVariety (A : AbelianScheme (Spec (.of K))) : AbelianVariety K where
  toOver := A.toOver
  grpObj := A.grpObj
  isProper := A.isProper
  geometricallyIntegral := A.geometricallyIntegral

@[simp]
lemma ofAbelianVariety_toOver (A : AbelianVariety K) :
    (ofAbelianVariety A).toOver = A.toOver :=
  (rfl)

@[simp]
lemma ofAbelianVariety_toScheme (A : AbelianVariety K) :
    (ofAbelianVariety A).toScheme = A.toScheme :=
  (rfl)

@[simp]
lemma toAbelianVariety_toOver (A : AbelianScheme (Spec (.of K))) :
    (toAbelianVariety A).toOver = A.toOver :=
  (rfl)

@[simp]
lemma toAbelianVariety_toScheme (A : AbelianScheme (Spec (.of K))) :
    (toAbelianVariety A).toScheme = A.toScheme :=
  (rfl)

/-- Converting an abelian variety to an abelian scheme over `Spec K` and back recovers it. -/
@[simp]
lemma toAbelianVariety_ofAbelianVariety (A : AbelianVariety K) :
    toAbelianVariety (ofAbelianVariety A) = A := by
  cases A
  rfl

/-- Converting an abelian scheme over `Spec K` to an abelian variety and back recovers it. -/
@[simp]
lemma ofAbelianVariety_toAbelianVariety (A : AbelianScheme (Spec (.of K))) :
    ofAbelianVariety (toAbelianVariety A) = A := by
  cases A
  rfl

lemma ofAbelianVariety_one (A : AbelianVariety K) :
    η[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) = η[A.toOver] :=
  Category.comp_id _

@[simp]
lemma ofAbelianVariety_zeroSection (A : AbelianVariety K) :
    (ofAbelianVariety A).zeroSection ≫ eqToHom (ofAbelianVariety_toScheme A) = A.zeroSection := by
  rw [← Over.eqToHom_left (ofAbelianVariety_toOver A)]
  exact congrArg Over.Hom.left (ofAbelianVariety_one A)

lemma ofAbelianVariety_mul (A : AbelianVariety K) :
    μ[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) =
      (eqToHom (ofAbelianVariety_toOver A) ⊗ₘ eqToHom (ofAbelianVariety_toOver A)) ≫
        μ[A.toOver] :=
  (Category.comp_id μ[(ofAbelianVariety A).toOver]).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _).symm))

lemma ofAbelianVariety_inv (A : AbelianVariety K) :
    ι[(ofAbelianVariety A).toOver] ≫ eqToHom (ofAbelianVariety_toOver A) =
      eqToHom (ofAbelianVariety_toOver A) ≫ ι[A.toOver] :=
  (Category.comp_id _).trans (Category.id_comp _).symm

lemma toAbelianVariety_one (A : AbelianScheme (Spec (.of K))) :
    η[(toAbelianVariety A).toOver] ≫ eqToHom (toAbelianVariety_toOver A) = η[A.toOver] :=
  Category.comp_id _

@[simp]
lemma toAbelianVariety_zeroSection (A : AbelianScheme (Spec (.of K))) :
    (toAbelianVariety A).zeroSection ≫ eqToHom (toAbelianVariety_toScheme A) = A.zeroSection := by
  rw [← Over.eqToHom_left (toAbelianVariety_toOver A)]
  exact congrArg Over.Hom.left (toAbelianVariety_one A)

lemma toAbelianVariety_mul (A : AbelianScheme (Spec (.of K))) :
    μ[(toAbelianVariety A).toOver] ≫ eqToHom (toAbelianVariety_toOver A) =
      (eqToHom (toAbelianVariety_toOver A) ⊗ₘ eqToHom (toAbelianVariety_toOver A)) ≫
        μ[A.toOver] :=
  (Category.comp_id μ[(toAbelianVariety A).toOver]).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _).symm))

lemma toAbelianVariety_inv (A : AbelianScheme (Spec (.of K))) :
    ι[(toAbelianVariety A).toOver] ≫ eqToHom (toAbelianVariety_toOver A) =
      eqToHom (toAbelianVariety_toOver A) ≫ ι[A.toOver] :=
  (Category.comp_id _).trans (Category.id_comp _).symm

instance isMonHom_eqToHom_ofAbelianVariety_toOver (A : AbelianVariety K) :
    IsMonHom (eqToHom (ofAbelianVariety_toOver A)) where
  one_hom := ofAbelianVariety_one A
  mul_hom := ofAbelianVariety_mul A

instance isMonHom_eqToHom_ofAbelianVariety_toOver_symm (A : AbelianVariety K) :
    IsMonHom (eqToHom (ofAbelianVariety_toOver A).symm) :=
  haveI : IsMonHom (eqToIso (ofAbelianVariety_toOver A)).hom :=
    isMonHom_eqToHom_ofAbelianVariety_toOver A
  inferInstanceAs (IsMonHom (eqToIso (ofAbelianVariety_toOver A)).inv)

instance isMonHom_eqToHom_toAbelianVariety_toOver (A : AbelianScheme (Spec (.of K))) :
    IsMonHom (eqToHom (toAbelianVariety_toOver A)) where
  one_hom := toAbelianVariety_one A
  mul_hom := toAbelianVariety_mul A

instance isMonHom_eqToHom_toAbelianVariety_toOver_symm (A : AbelianScheme (Spec (.of K))) :
    IsMonHom (eqToHom (toAbelianVariety_toOver A).symm) :=
  haveI : IsMonHom (eqToIso (toAbelianVariety_toOver A)).hom :=
    isMonHom_eqToHom_toAbelianVariety_toOver A
  inferInstanceAs (IsMonHom (eqToIso (toAbelianVariety_toOver A)).inv)

private instance isMonHom_eqToHom_avProd_toOver (A B : AbelianVariety K) :
    IsMonHom (eqToHom (AbelianVariety.prod_toOver A B)) where
  one_hom := AbelianVariety.prod_one A B
  mul_hom := AbelianVariety.prod_mul A B

private instance isMonHom_eqToHom_avProd_toOver_symm (A B : AbelianVariety K) :
    IsMonHom (eqToHom (AbelianVariety.prod_toOver A B).symm) :=
  haveI : IsMonHom (eqToIso (AbelianVariety.prod_toOver A B)).hom :=
    isMonHom_eqToHom_avProd_toOver A B
  inferInstanceAs (IsMonHom (eqToIso (AbelianVariety.prod_toOver A B)).inv)

/-! ### Commutativity and pointed morphisms over a field -/

/-- The group law of an abelian scheme over a field is commutative. -/
instance isCommMonObj_field (A : AbelianScheme (Spec (.of K))) : IsCommMonObj A.toOver :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.toOver

/-- Over a field, homomorphisms of abelian schemes are equivalent to morphisms over `Spec K`
preserving the identity section. -/
def Hom.equivPointed (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]} where
  toFun f := ⟨Hom.toOverHom f, Hom.one_hom f⟩
  invFun f := Hom.mk' f.1 f.2 (isMonHom_of_one_hom f.1 f.2).mul_hom
  left_inv _ := Hom.toOverHom_injective (Hom.toOverHom_mk' _ _ _)
  right_inv _ := Subtype.ext (Hom.toOverHom_mk' _ _ _)

@[simp]
lemma Hom.coe_equivPointed_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (Hom.equivPointed A B f : A.toOver ⟶ B.toOver) = Hom.toOverHom f :=
  (rfl)

@[simp]
lemma Hom.toOverHom_equivPointed_symm_apply {A B : AbelianScheme (Spec (.of K))}
    (f : {f : A.toOver ⟶ B.toOver // η[A.toOver] ≫ f = η[B.toOver]}) :
    Hom.toOverHom ((Hom.equivPointed A B).symm f) = f.1 :=
  Hom.toOverHom_mk' _ _ _

/-! ### Equivalence of categories over `Spec K` -/

/-- Transport a homomorphism of abelian schemes over `Spec K` to a homomorphism of abelian
varieties. -/
def Hom.toAbelianVariety {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    AbelianScheme.toAbelianVariety A ⟶ AbelianScheme.toAbelianVariety B :=
  AbelianVariety.Hom.mk'
    (eqToHom (toAbelianVariety_toOver A) ≫ Hom.toOverHom f ≫
      eqToHom (toAbelianVariety_toOver B).symm)
    (IsMonHom.one_hom _) (IsMonHom.mul_hom _)

/-- Transport a homomorphism of abelian varieties over `K` to a homomorphism of abelian schemes over
`Spec K`. -/
def Hom.ofAbelianVariety {A B : AbelianVariety K} (f : A ⟶ B) :
    AbelianScheme.ofAbelianVariety A ⟶ AbelianScheme.ofAbelianVariety B :=
  Hom.mk
    (eqToHom (ofAbelianVariety_toOver A) ≫ AbelianVariety.Hom.toOverHom f ≫
      eqToHom (ofAbelianVariety_toOver B).symm)

@[simp]
lemma Hom.toOverHom_toAbelianVariety {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    AbelianVariety.Hom.toOverHom (Hom.toAbelianVariety f) =
      eqToHom (toAbelianVariety_toOver A) ≫ Hom.toOverHom f ≫
        eqToHom (toAbelianVariety_toOver B).symm :=
  AbelianVariety.Hom.toOverHom_mk' _ _ _

@[simp]
lemma Hom.toOverHom_ofAbelianVariety {A B : AbelianVariety K} (f : A ⟶ B) :
    Hom.toOverHom (Hom.ofAbelianVariety f) =
      eqToHom (ofAbelianVariety_toOver A) ≫ AbelianVariety.Hom.toOverHom f ≫
        eqToHom (ofAbelianVariety_toOver B).symm :=
  Hom.toOverHom_mk _

@[simp]
lemma Hom.toAbelianVariety_id (A : AbelianScheme (Spec (.of K))) :
    Hom.toAbelianVariety (𝟙 A) = 𝟙 (AbelianScheme.toAbelianVariety A) :=
  AbelianVariety.Hom.toOverHom_injective (by
    rw [Hom.toOverHom_toAbelianVariety, Hom.toOverHom_id, AbelianVariety.Hom.toOverHom_id]; simp)

@[simp]
lemma Hom.toAbelianVariety_comp {A B C : AbelianScheme (Spec (.of K))} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toAbelianVariety (f ≫ g) = Hom.toAbelianVariety f ≫ Hom.toAbelianVariety g :=
  AbelianVariety.Hom.toOverHom_injective (by
    rw [Hom.toOverHom_toAbelianVariety, Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_comp,
      Hom.toOverHom_toAbelianVariety, Hom.toOverHom_toAbelianVariety]; simp)

@[simp]
lemma Hom.ofAbelianVariety_id (A : AbelianVariety K) :
    Hom.ofAbelianVariety (𝟙 A) = 𝟙 (AbelianScheme.ofAbelianVariety A) :=
  Hom.toOverHom_injective (by
    rw [Hom.toOverHom_ofAbelianVariety, AbelianVariety.Hom.toOverHom_id, Hom.toOverHom_id]; simp)

@[simp]
lemma Hom.ofAbelianVariety_comp {A B C : AbelianVariety K} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.ofAbelianVariety (f ≫ g) = Hom.ofAbelianVariety f ≫ Hom.ofAbelianVariety g :=
  Hom.toOverHom_injective (by
    rw [Hom.toOverHom_ofAbelianVariety, AbelianVariety.Hom.toOverHom_comp, Hom.toOverHom_comp,
      Hom.toOverHom_ofAbelianVariety, Hom.toOverHom_ofAbelianVariety]; simp)

/-- The functor sending abelian schemes over `Spec K` to abelian varieties over `K`. -/
def toAbelianVarietyFunctor (K : Type u) [Field K] :
    AbelianScheme (Spec (.of K)) ⥤ AbelianVariety K where
  obj := toAbelianVariety
  map := Hom.toAbelianVariety
  map_id := Hom.toAbelianVariety_id
  map_comp := Hom.toAbelianVariety_comp

/-- The functor sending abelian varieties over `K` to abelian schemes over `Spec K`. -/
def ofAbelianVarietyFunctor (K : Type u) [Field K] :
    AbelianVariety K ⥤ AbelianScheme (Spec (.of K)) where
  obj := ofAbelianVariety
  map := Hom.ofAbelianVariety
  map_id := Hom.ofAbelianVariety_id
  map_comp := Hom.ofAbelianVariety_comp

@[simp]
lemma toAbelianVarietyFunctor_obj (A : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyFunctor K).obj A = toAbelianVariety A :=
  (rfl)

@[simp]
lemma toAbelianVarietyFunctor_map {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    (toAbelianVarietyFunctor K).map f =
      eqToHom (toAbelianVarietyFunctor_obj A) ≫ Hom.toAbelianVariety f ≫
        eqToHom (toAbelianVarietyFunctor_obj B).symm :=
  (rfl)

@[simp]
lemma ofAbelianVarietyFunctor_obj (A : AbelianVariety K) :
    (ofAbelianVarietyFunctor K).obj A = ofAbelianVariety A :=
  (rfl)

@[simp]
lemma ofAbelianVarietyFunctor_map {A B : AbelianVariety K} (f : A ⟶ B) :
    (ofAbelianVarietyFunctor K).map f =
      eqToHom (ofAbelianVarietyFunctor_obj A) ≫ Hom.ofAbelianVariety f ≫
        eqToHom (ofAbelianVarietyFunctor_obj B).symm :=
  (rfl)

private lemma toOverHom_eqToHom {A B : AbelianScheme (Spec (.of K))} (h : A = B) :
    Hom.toOverHom (eqToHom h) = eqToHom (congrArg AbelianScheme.toOver h) :=
  eqToHom_map Hom.toOverFunctor h

private lemma avToOverHom_eqToHom {A B : AbelianVariety K} (h : A = B) :
    AbelianVariety.Hom.toOverHom (eqToHom h) = eqToHom (congrArg AbelianVariety.toOver h) :=
  eqToHom_map AbelianVariety.Hom.toOverFunctor h

/-- Over a field `K`, the category of abelian schemes over `Spec K` is equivalent to the category
of abelian varieties over `K`. -/
def fieldEquivalence (K : Type u) [Field K] :
    AbelianScheme (Spec (.of K)) ≌ AbelianVariety K where
  functor := toAbelianVarietyFunctor K
  inverse := ofAbelianVarietyFunctor K
  unitIso := NatIso.ofComponents
    (fun A ↦ eqToIso (by simp)) fun {A B} f ↦ by
      apply Hom.toOverHom_injective
      rw [Functor.id_map, Functor.comp_map, toAbelianVarietyFunctor_map,
        ofAbelianVarietyFunctor_map]
      simp only [eqToIso.hom, Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_comp,
        Hom.toOverHom_ofAbelianVariety, Hom.toOverHom_toAbelianVariety, toOverHom_eqToHom,
        avToOverHom_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp]
  counitIso := NatIso.ofComponents
    (fun A ↦ eqToIso (by simp)) fun {A B} f ↦ by
      apply AbelianVariety.Hom.toOverHom_injective
      rw [Functor.comp_map, Functor.id_map, ofAbelianVarietyFunctor_map,
        toAbelianVarietyFunctor_map]
      simp only [eqToIso.hom, AbelianVariety.Hom.toOverHom_comp, Hom.toOverHom_comp,
        Hom.toOverHom_toAbelianVariety, Hom.toOverHom_ofAbelianVariety, avToOverHom_eqToHom,
        toOverHom_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]
  functor_unitIso_comp A := by
    apply AbelianVariety.Hom.toOverHom_injective
    simp only [NatIso.ofComponents_hom_app, eqToIso.hom, toAbelianVarietyFunctor_map,
      AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id,
      Hom.toOverHom_toAbelianVariety, avToOverHom_eqToHom, toOverHom_eqToHom, Category.assoc,
      eqToHom_trans, eqToHom_refl]

/-! ### Pointwise group structure on homomorphisms over a field -/

namespace Field

open scoped AbelianVariety.Hom

/-- The bijection on homomorphisms induced by `fieldEquivalence`. -/
def homEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃ (toAbelianVariety A ⟶ toAbelianVariety B) :=
  (fieldEquivalence K).fullyFaithfulFunctor.homEquiv

/-- Over a field, homomorphisms of abelian schemes form a commutative group under the pointwise
group law of the target. -/
scoped instance instCommGroup (A B : AbelianScheme (Spec (.of K))) : CommGroup (A ⟶ B) :=
  (homEquiv A B).commGroup

/-- Over a field, `Hom.toAbelianVariety` is a group isomorphism for the pointwise group laws. -/
def toAbelianVarietyMulEquiv (A B : AbelianScheme (Spec (.of K))) :
    (A ⟶ B) ≃* (toAbelianVariety A ⟶ toAbelianVariety B) where
  __ := homEquiv A B
  map_mul' _ _ := (homEquiv A B).apply_symm_apply _

@[simp]
lemma toAbelianVarietyMulEquiv_apply {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    toAbelianVarietyMulEquiv A B f = Hom.toAbelianVariety f :=
  (rfl)

private lemma toOverHom_eq_conj {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    Hom.toOverHom f = eqToHom (toAbelianVariety_toOver A).symm ≫
      AbelianVariety.Hom.toOverHom (toAbelianVarietyMulEquiv A B f) ≫
      eqToHom (toAbelianVariety_toOver B) := by
  simp [toAbelianVarietyMulEquiv_apply]

@[simp]
lemma toOverHom_one (A B : AbelianScheme (Spec (.of K))) :
    Hom.toOverHom (1 : A ⟶ B) = 1 := by
  rw [toOverHom_eq_conj, map_one, AbelianVariety.Hom.toOverHom_one, MonObj.one_comp,
    MonObj.comp_one]

@[simp]
lemma toOverHom_mul {A B : AbelianScheme (Spec (.of K))} (f g : A ⟶ B) :
    Hom.toOverHom (f * g) = Hom.toOverHom f * Hom.toOverHom g := by
  rw [toOverHom_eq_conj, map_mul, AbelianVariety.Hom.toOverHom_mul, MonObj.mul_comp,
    MonObj.comp_mul]
  simp [toAbelianVarietyMulEquiv_apply]

@[simp]
lemma toOverHom_inv {A B : AbelianScheme (Spec (.of K))} (f : A ⟶ B) :
    Hom.toOverHom f⁻¹ = (Hom.toOverHom f)⁻¹ := by
  rw [toOverHom_eq_conj, map_inv, AbelianVariety.Hom.toOverHom_inv, GrpObj.inv_comp,
    GrpObj.comp_inv]
  simp [toAbelianVarietyMulEquiv_apply]

end Field

/-! ### Compatibility with zero, products, and base change along field extensions -/

/-- `toAbelianVariety` sends `identity (Spec K)` to `AbelianVariety.trivial K`. -/
def toAbelianVarietyIdentityIso (K : Type u) [Field K] :
    toAbelianVariety (identity (Spec (.of K))) ≅ AbelianVariety.trivial K :=
  ((isTerminalIdentity (Spec (.of K))).isTerminalObj (fieldEquivalence K).functor).uniqueUpToIso
    (AbelianVariety.isTerminalTrivial K)

/-- `ofAbelianVariety` sends `AbelianVariety.trivial K` to `identity (Spec K)`. -/
def ofAbelianVarietyTrivialIso (K : Type u) [Field K] :
    ofAbelianVariety (AbelianVariety.trivial K) ≅ identity (Spec (.of K)) :=
  ((AbelianVariety.isTerminalTrivial K).isTerminalObj (fieldEquivalence K).inverse).uniqueUpToIso
    (isTerminalIdentity (Spec (.of K)))

/-- `toAbelianVariety` preserves binary products, compatibly with projections. -/
def toAbelianVarietyProdIso (A B : AbelianScheme (Spec (.of K))) :
    toAbelianVariety (A.prod B) ≅ (toAbelianVariety A).prod (toAbelianVariety B) where
  hom := AbelianVariety.prod.lift
    (Hom.toAbelianVariety (prod.fst A B)) (Hom.toAbelianVariety (prod.snd A B))
  inv := AbelianVariety.Hom.mk'
    (eqToHom (AbelianVariety.prod_toOver (toAbelianVariety A) (toAbelianVariety B)) ≫
      (eqToHom (toAbelianVariety_toOver A) ⊗ₘ eqToHom (toAbelianVariety_toOver B)) ≫
      eqToHom (prod_toOver A B).symm ≫ eqToHom (toAbelianVariety_toOver (A.prod B)).symm)
    (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  hom_inv_id := by
    apply AbelianVariety.Hom.toOverHom_injective
    rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id,
      AbelianVariety.prod.toOverHom_lift, AbelianVariety.Hom.toOverHom_mk' _ _ _,
      ← cancel_mono (eqToHom (toAbelianVariety_toOver (A.prod B))),
      ← cancel_mono (eqToHom (prod_toOver A B))]
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply AbelianVariety.prod.hom_ext <;>
    · simp only [Category.assoc, AbelianVariety.prod.lift_fst, AbelianVariety.prod.lift_snd,
        Category.id_comp]
      apply AbelianVariety.Hom.toOverHom_injective
      rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_mk' _ _ _,
        Hom.toOverHom_toAbelianVariety]
      simp only [prod.toOverHom_fst, prod.toOverHom_snd, AbelianVariety.prod.toOverHom_fst,
        AbelianVariety.prod.toOverHom_snd, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, tensorHom_fst_assoc, tensorHom_snd_assoc, eqToHom_trans,
        Category.comp_id]

@[simp]
lemma toAbelianVarietyProdIso_hom_fst (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.fst (toAbelianVariety A) (toAbelianVariety B) =
      Hom.toAbelianVariety (prod.fst A B) :=
  AbelianVariety.prod.lift_fst _ _

@[simp]
lemma toAbelianVarietyProdIso_hom_snd (A B : AbelianScheme (Spec (.of K))) :
    (toAbelianVarietyProdIso A B).hom ≫
        AbelianVariety.prod.snd (toAbelianVariety A) (toAbelianVariety B) =
      Hom.toAbelianVariety (prod.snd A B) :=
  AbelianVariety.prod.lift_snd _ _

/-- `ofAbelianVariety` preserves binary products, compatibly with projections. -/
def ofAbelianVarietyProdIso (A B : AbelianVariety K) :
    ofAbelianVariety (A.prod B) ≅ (ofAbelianVariety A).prod (ofAbelianVariety B) where
  hom := prod.lift
    (Hom.ofAbelianVariety (AbelianVariety.prod.fst A B))
    (Hom.ofAbelianVariety (AbelianVariety.prod.snd A B))
  inv := Hom.mk
    (eqToHom (prod_toOver (ofAbelianVariety A) (ofAbelianVariety B)) ≫
      (eqToHom (ofAbelianVariety_toOver A) ⊗ₘ eqToHom (ofAbelianVariety_toOver B)) ≫
      eqToHom (AbelianVariety.prod_toOver A B).symm ≫
      eqToHom (ofAbelianVariety_toOver (A.prod B)).symm)
  hom_inv_id := by
    apply Hom.toOverHom_injective
    rw [Hom.toOverHom_comp, Hom.toOverHom_id, prod.toOverHom_lift, Hom.toOverHom_mk,
      ← cancel_mono (eqToHom (ofAbelianVariety_toOver (A.prod B))),
      ← cancel_mono (eqToHom (AbelianVariety.prod_toOver A B))]
    apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]
  inv_hom_id := by
    apply prod.hom_ext <;>
    · simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.id_comp]
      apply Hom.toOverHom_injective
      rw [Hom.toOverHom_comp, Hom.toOverHom_mk, Hom.toOverHom_ofAbelianVariety]
      simp only [AbelianVariety.prod.toOverHom_fst, AbelianVariety.prod.toOverHom_snd,
        prod.toOverHom_fst, prod.toOverHom_snd, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, tensorHom_fst_assoc, tensorHom_snd_assoc,
        eqToHom_trans, Category.comp_id]

@[simp]
lemma ofAbelianVarietyProdIso_hom_fst (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.fst (ofAbelianVariety A) (ofAbelianVariety B) =
      Hom.ofAbelianVariety (AbelianVariety.prod.fst A B) :=
  prod.lift_fst _ _

@[simp]
lemma ofAbelianVarietyProdIso_hom_snd (A B : AbelianVariety K) :
    (ofAbelianVarietyProdIso A B).hom ≫ prod.snd (ofAbelianVariety A) (ofAbelianVariety B) =
      Hom.ofAbelianVariety (AbelianVariety.prod.snd A B) :=
  prod.lift_snd _ _

/-- `toAbelianVariety` commutes with base change along a field extension `K → L`. -/
def toAbelianVarietyBaseChangeIso (A : AbelianScheme (Spec (.of K)))
    (L : Type u) [Field L] [Algebra K L] :
    toAbelianVariety (A.baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))) ≅
      (toAbelianVariety A).baseChange L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  { hom := AbelianVariety.Hom.mk'
      (eqToHom (toAbelianVariety_toOver (A.baseChange f)) ≫ eqToHom (baseChange_toOver A f) ≫
        (Over.pullback f).map (eqToHom (toAbelianVariety_toOver A).symm) ≫
        eqToHom (AbelianVariety.baseChange_toOver (toAbelianVariety A) L).symm)
      (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
    inv := AbelianVariety.Hom.mk'
      (eqToHom (AbelianVariety.baseChange_toOver (toAbelianVariety A) L) ≫
        (Over.pullback f).map (eqToHom (toAbelianVariety_toOver A)) ≫
        eqToHom (baseChange_toOver A f).symm ≫
        eqToHom (toAbelianVariety_toOver (A.baseChange f)).symm)
      (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
    hom_inv_id := AbelianVariety.Hom.toOverHom_injective (by
      rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id]
      simp [AbelianVariety.Hom.toOverHom_mk' _ _ _, Category.assoc])
    inv_hom_id := AbelianVariety.Hom.toOverHom_injective (by
      rw [AbelianVariety.Hom.toOverHom_comp, AbelianVariety.Hom.toOverHom_id]
      simp [AbelianVariety.Hom.toOverHom_mk' _ _ _, Category.assoc]) }

/-- `ofAbelianVariety` commutes with base change along a field extension `K → L`. -/
def ofAbelianVarietyBaseChangeIso (A : AbelianVariety K)
    (L : Type u) [Field L] [Algebra K L] :
    ofAbelianVariety (A.baseChange L) ≅
      (ofAbelianVariety A).baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let e := (eqToIso (ofAbelianVariety_toOver (A.baseChange L))).trans
    ((eqToIso (AbelianVariety.baseChange_toOver A L)).trans
      (((Over.pullback f).mapIso (eqToIso (ofAbelianVariety_toOver A)).symm).trans
        (eqToIso (baseChange_toOver (ofAbelianVariety A) f)).symm))
  have : IsMonHom e.hom := by
    dsimp only [e, Iso.trans_hom, eqToIso.hom, eqToIso.inv, Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  isoMk e

/-- Naturality of `toAbelianVarietyBaseChangeIso`: the adapter functor commutes with base change
along a field extension `K → L`. -/
def toAbelianVarietyBaseChangeNatIso (L : Type u) [Field L] [Algebra K L] :
    baseChangeFunctor (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⋙
        toAbelianVarietyFunctor L ≅
      toAbelianVarietyFunctor K ⋙ AbelianVariety.baseChangeFunctor L :=
  NatIso.ofComponents
    (fun A ↦ (eqToIso (by simp)).trans
      ((toAbelianVarietyBaseChangeIso A L).trans (eqToIso (by simp))))
    fun {A B} φ ↦ by
      apply AbelianVariety.Hom.toOverHom_injective
      dsimp only [Functor.comp_obj, Functor.comp_map]
      simp only [baseChangeFunctor_map, toAbelianVarietyFunctor_map,
        AbelianVariety.baseChangeFunctor_map, Iso.trans_hom, eqToIso.hom,
        AbelianVariety.Hom.toOverHom_comp, Hom.toOverHom_toAbelianVariety, Hom.toOverHom_comp,
        Hom.toOverHom_baseChange, AbelianVariety.Hom.toOverHom_baseChange,
        toAbelianVarietyBaseChangeIso, AbelianVariety.Hom.toOverHom_mk' _ _ _,
        avToOverHom_eqToHom, toOverHom_eqToHom,
        CategoryTheory.Functor.map_comp (Over.pullback _), eqToHom_map (Over.pullback _),
        Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

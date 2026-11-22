/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.BaseChange

/-!
# Products of abelian schemes

This file constructs the binary product `A.prod B` of two abelian schemes over a base scheme `S`,
carried by the fibre product `A.toOver ⊗ B.toOver` in `Over S` with the componentwise group law.
Properness, smoothness, and geometric connectedness are stable under fibre products, so `A.prod B`
is an abelian scheme over `S`.

The projections `AbelianScheme.prod.fst`, `AbelianScheme.prod.snd` and pairing
`AbelianScheme.prod.lift` exhibit `A.prod B` as the categorical binary product in
`AbelianScheme S` (`AbelianScheme.prod.binaryFan` and `AbelianScheme.prod.binaryFanIsLimit`),
giving `HasBinaryProducts (AbelianScheme S)` and `HasFiniteProducts (AbelianScheme S)`. The file
also records:

* `AbelianScheme.prodIdentityIso` and `AbelianScheme.identityProdIso`: the product of `A` with
  `AbelianScheme.identity S` is canonically isomorphic to `A`;
* `AbelianScheme.baseChangeProdIso`: base change along any morphism `f : T ⟶ S` preserves
  products of abelian schemes compatibly with the projections.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianScheme

variable {S T : Scheme.{u}}

noncomputable section

/-- The product of two abelian schemes over `S`, carried by their fibre product over `S` with the
componentwise group law. -/
@[expose] def prod (A B : AbelianScheme S) : AbelianScheme S where
  toOver := A.toOver ⊗ B.toOver
  grpObj := inferInstance
  isProper := by
    rw [Over.tensorObj_hom]
    exact MorphismProperty.comp_mem @IsProper _ _
      (inferInstanceAs (IsProper (pullback.fst A.toOver.hom B.toOver.hom))) A.isProper
  smooth := by
    rw [Over.tensorObj_hom]
    exact MorphismProperty.comp_mem @Smooth _ _
      (inferInstanceAs (Smooth (pullback.fst A.toOver.hom B.toOver.hom))) A.smooth
  geometricallyConnected := by
    rw [Over.tensorObj_hom]
    have : UniversallyOpen (pullback.fst A.toOver.hom B.toOver.hom) := inferInstance
    exact GeometricallyConnected.comp (pullback.fst A.toOver.hom B.toOver.hom) A.toOver.hom

/-- The group scheme underlying a product is the fibre product group scheme. -/
@[simp]
lemma prod_toOver (A B : AbelianScheme S) : (prod A B).toOver = A.toOver ⊗ B.toOver :=
  (rfl)

/-- The scheme underlying a product is the fibre product over `S`. -/
@[simp]
lemma prod_toScheme (A B : AbelianScheme S) :
    (prod A B).toScheme = pullback A.toOver.hom B.toOver.hom :=
  (rfl)

/-- The unit section of a product is the componentwise unit section. -/
lemma prod_one (A B : AbelianScheme S) :
    η[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) = η[A.toOver ⊗ B.toOver] :=
  Category.comp_id _

/-- The multiplication on a product is componentwise multiplication. -/
lemma prod_mul (A B : AbelianScheme S) :
    μ[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      (eqToHom (prod_toOver A B) ⊗ₘ eqToHom (prod_toOver A B)) ≫ μ[A.toOver ⊗ B.toOver] :=
  (Category.comp_id μ[(prod A B).toOver]).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (MonoidalCategory.id_tensorHom_id _ _).symm))

/-- Inversion on a product is componentwise inversion. -/
lemma prod_inv (A B : AbelianScheme S) :
    ι[(prod A B).toOver] ≫ eqToHom (prod_toOver A B) =
      eqToHom (prod_toOver A B) ≫ ι[A.toOver ⊗ B.toOver] :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The transport isomorphism for `prod_toOver` is a homomorphism of monoid objects. -/
instance isMonHom_eqToHom_prod_toOver (A B : AbelianScheme S) :
    IsMonHom (eqToHom (prod_toOver A B)) where
  one_hom := prod_one A B
  mul_hom := prod_mul A B

/-- The inverse transport isomorphism for `prod_toOver` is a homomorphism of monoid objects. -/
instance isMonHom_eqToHom_prod_toOver_symm (A B : AbelianScheme S) :
    IsMonHom (eqToHom (prod_toOver A B).symm) :=
  haveI : IsMonHom (eqToIso (prod_toOver A B)).hom := isMonHom_eqToHom_prod_toOver A B
  inferInstanceAs (IsMonHom (eqToIso (prod_toOver A B)).inv)

namespace prod

/-- The first projection from a product of abelian schemes. -/
def fst (A B : AbelianScheme S) : prod A B ⟶ A :=
  let f := eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver
  homMk f (IsMonHom.one_hom f) (IsMonHom.mul_hom f)

/-- The second projection from a product of abelian schemes. -/
def snd (A B : AbelianScheme S) : prod A B ⟶ B :=
  let f := eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver
  homMk f (IsMonHom.one_hom f) (IsMonHom.mul_hom f)

/-- Pair two homomorphisms with a common source into a homomorphism into a product. -/
def lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ prod A B :=
  let h := CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g) ≫
    eqToHom (prod_toOver A B).symm
  homMk h (IsMonHom.one_hom h) (IsMonHom.mul_hom h)

@[simp]
lemma toOverHom_fst (A B : AbelianScheme S) :
    toOverHom (fst A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.fst A.toOver B.toOver :=
  toOverHom_homMk _ _ _

@[simp]
lemma toOverHom_snd (A B : AbelianScheme S) :
    toOverHom (snd A B) =
      eqToHom (prod_toOver A B) ≫ CartesianMonoidalCategory.snd A.toOver B.toOver :=
  toOverHom_homMk _ _ _

@[simp]
lemma toOverHom_lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    toOverHom (lift f g) =
      CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g) ≫
        eqToHom (prod_toOver A B).symm :=
  toOverHom_homMk _ _ _

@[simp]
lemma lift_fst {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ fst A B = f :=
  toOverHom_injective (by rw [toOverHom_comp]; simp)

@[simp]
lemma lift_snd {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    lift f g ≫ snd A B = g :=
  toOverHom_injective (by rw [toOverHom_comp]; simp)

/-- Homomorphisms into a product of abelian schemes are determined by their two projections. -/
@[ext]
lemma hom_ext {A B C : AbelianScheme S} {f g : C ⟶ prod A B} (hfst : f ≫ fst A B = g ≫ fst A B)
    (hsnd : f ≫ snd A B = g ≫ snd A B) : f = g := by
  apply toOverHom_injective
  rw [← cancel_mono (eqToHom (prod_toOver A B))]
  apply CartesianMonoidalCategory.hom_ext
  · simpa only [toOverHom_comp, toOverHom_fst, ← Category.assoc] using
      congrArg toOverHom hfst
  · simpa only [toOverHom_comp, toOverHom_snd, ← Category.assoc] using
      congrArg toOverHom hsnd

@[reassoc, simp]
lemma comp_lift {A B C D : AbelianScheme S} (h : D ⟶ C) (f : C ⟶ A) (g : C ⟶ B) :
    h ≫ lift f g = lift (h ≫ f) (h ≫ g) :=
  hom_ext (by simp) (by simp)

@[simp]
lemma lift_comp_fst_snd {A B C : AbelianScheme S} (f : C ⟶ prod A B) :
    lift (f ≫ fst A B) (f ≫ snd A B) = f :=
  hom_ext (by simp) (by simp)

/-- The binary fan exhibiting `A.prod B` as the categorical product of `A` and `B`. -/
@[expose] def binaryFan (A B : AbelianScheme S) : BinaryFan A B :=
  BinaryFan.mk (fst A B) (snd A B)

/-- `prod.binaryFan A B` is a limit cone in `AbelianScheme S`. -/
def binaryFanIsLimit (A B : AbelianScheme S) : IsLimit (binaryFan A B) :=
  BinaryFan.IsLimit.mk _ (fun f g ↦ lift f g) (fun f g ↦ lift_fst f g) (fun f g ↦ lift_snd f g)
    fun f g _ hfst hsnd ↦ hom_ext (hfst.trans (lift_fst f g).symm) (hsnd.trans (lift_snd f g).symm)

end prod

/-- The concrete product supplies the categorical binary product of abelian schemes. -/
instance hasBinaryProduct (A B : AbelianScheme S) : HasBinaryProduct A B :=
  HasLimit.mk ⟨prod.binaryFan A B, prod.binaryFanIsLimit A B⟩

/-- Abelian schemes over `S` have categorical binary products. -/
instance hasBinaryProducts : HasBinaryProducts (AbelianScheme S) :=
  hasBinaryProducts_of_hasLimit_pair (AbelianScheme S)

/-- Abelian schemes over `S` have all finite products. -/
instance hasFiniteProducts : HasFiniteProducts (AbelianScheme S) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-- The product of `A` with the identity abelian scheme `S` is canonically isomorphic to `A`. -/
def prodIdentityIso (A : AbelianScheme S) : A.prod (identity S) ≅ A where
  hom := prod.fst A (identity S)
  inv := prod.lift (𝟙 A) (toIdentity A)
  hom_inv_id := prod.hom_ext (by simp) (Subsingleton.elim _ _)
  inv_hom_id := by simp

/-- The product of the identity abelian scheme `S` with `A` is canonically isomorphic to `A`. -/
def identityProdIso (A : AbelianScheme S) : (identity S).prod A ≅ A where
  hom := prod.snd (identity S) A
  inv := prod.lift (toIdentity A) (𝟙 A)
  hom_inv_id := prod.hom_ext (Subsingleton.elim _ _) (by simp)
  inv_hom_id := by simp

private abbrev grpBinaryFan (A B : AbelianScheme S) :
    BinaryFan (Grp.mk A.toOver) (Grp.mk B.toOver) :=
  BinaryFan.mk (prod.fst A B).hom (prod.snd A B).hom

private def grpBinaryFanIsLimit (A B : AbelianScheme S) :
    IsLimit (grpBinaryFan A B) :=
  BinaryFan.IsLimit.mk _
    (fun f g ↦
      haveI : IsMonHom f.hom.hom := f.hom.isMonHom_hom
      haveI : IsMonHom g.hom.hom := g.hom.isMonHom_hom
      Grp.homMk' (A := _) (B := Grp.mk (A.prod B).toOver)
        { hom := CartesianMonoidalCategory.lift f.hom.hom g.hom.hom ≫
            eqToHom (prod_toOver A B).symm
          isMonHom_hom :=
            { one_hom := by
                rw [← cancel_mono (eqToHom (prod_toOver A B)), Category.assoc, prod_one]
                simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
                exact IsMonHom.one_hom (CartesianMonoidalCategory.lift f.hom.hom g.hom.hom)
              mul_hom := by
                rw [← cancel_mono (eqToHom (prod_toOver A B))]
                simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
                rw [prod_mul]
                simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, eqToHom_trans,
                  eqToHom_refl, Category.comp_id]
                exact IsMonHom.mul_hom (CartesianMonoidalCategory.lift f.hom.hom g.hom.hom) } })
    (fun f g ↦ Grp.hom_ext _ _ (by
      have hfst : (grpBinaryFan A B).fst.hom.hom = toOverHom (prod.fst A B) := rfl
      rw [Grp.comp', Mon.comp_hom', hfst, prod.toOverHom_fst]
      simp [Category.assoc]))
    (fun f g ↦ Grp.hom_ext _ _ (by
      have hsnd : (grpBinaryFan A B).snd.hom.hom = toOverHom (prod.snd A B) := rfl
      rw [Grp.comp', Mon.comp_hom', hsnd, prod.toOverHom_snd]
      simp [Category.assoc]))
    (fun f g m hfst hsnd ↦ Grp.hom_ext _ _ (by
      rw [← cancel_mono (eqToHom (prod_toOver A B))]
      apply CartesianMonoidalCategory.hom_ext
      · have h := congrArg (fun k : _ ⟶ Grp.mk A.toOver ↦ k.hom.hom) hfst
        have h1 : (grpBinaryFan A B).fst.hom.hom = toOverHom (prod.fst A B) := rfl
        rw [Grp.comp', Mon.comp_hom', h1, prod.toOverHom_fst] at h
        simpa [Category.assoc] using h
      · have h := congrArg (fun k : _ ⟶ Grp.mk B.toOver ↦ k.hom.hom) hsnd
        have h2 : (grpBinaryFan A B).snd.hom.hom = toOverHom (prod.snd A B) := rfl
        rw [Grp.comp', Mon.comp_hom', h2, prod.toOverHom_snd] at h
        simpa [Category.assoc] using h))

/-- Base change preserves products of abelian schemes, respecting the group laws and projections. -/
def baseChangeProdIso (A B : AbelianScheme S) (f : T ⟶ S) :
    (A.prod B).baseChange f ≅ (A.baseChange f).prod (B.baseChange f) :=
  (fullyFaithfulInducedFunctor fun X : AbelianScheme T ↦ Grp.mk X.toOver).preimageIso
    ((mapIsLimitOfPreservesOfIsLimit (Over.pullback f).mapGrp _ _
        (grpBinaryFanIsLimit A B)).conePointUniqueUpToIso
      (grpBinaryFanIsLimit (A.baseChange f) (B.baseChange f)))

@[simp]
lemma baseChangeProdIso_hom_fst (A B : AbelianScheme S) (f : T ⟶ S) :
    (baseChangeProdIso A B f).hom ≫ prod.fst (A.baseChange f) (B.baseChange f) =
      (baseChangeFunctor f).map (prod.fst A B) := by
  apply InducedCategory.hom_ext
  exact (mapIsLimitOfPreservesOfIsLimit (Over.pullback f).mapGrp _ _
    (grpBinaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (grpBinaryFanIsLimit (A.baseChange f) (B.baseChange f)) ⟨WalkingPair.left⟩

@[simp]
lemma baseChangeProdIso_hom_snd (A B : AbelianScheme S) (f : T ⟶ S) :
    (baseChangeProdIso A B f).hom ≫ prod.snd (A.baseChange f) (B.baseChange f) =
      (baseChangeFunctor f).map (prod.snd A B) := by
  apply InducedCategory.hom_ext
  exact (mapIsLimitOfPreservesOfIsLimit (Over.pullback f).mapGrp _ _
    (grpBinaryFanIsLimit A B)).conePointUniqueUpToIso_hom_comp
    (grpBinaryFanIsLimit (A.baseChange f) (B.baseChange f)) ⟨WalkingPair.right⟩

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

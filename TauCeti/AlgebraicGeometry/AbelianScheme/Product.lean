/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AbelianScheme.RelativeDimension
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Products of abelian schemes

For abelian schemes `A` and `B` over a scheme `S`, the fibre product `A ×_S B` with the
componentwise group law is again an abelian scheme `A.prod B`: properness and smoothness are
stable under base change and composition, and geometric connectedness is stable under composition
of universally open morphisms. With its two projections it is the categorical product in the
category of abelian schemes over `S`, whose terminal object is the identity abelian scheme `S`.

Products commute with base change: for `f : T ⟶ S`, the canonical comparison
`(A ×_S B)_T ⟶ A_T ×_T B_T` built from the pulled-back projections preserves the group laws and
is an isomorphism of abelian schemes (`AbelianScheme.baseChangeProdIso`). Relative dimensions add,
`g_{A ×_S B} = g_A + g_B` (`AbelianScheme.relativeDimension_prod`): over the residue field of a
point the two factors are smooth of constant relative dimension, and a fibre product of smooth
morphisms of relative dimensions `m` and `n` is smooth of relative dimension `m + n`. The product
with the identity abelian scheme is canonically the other factor.

## Main declarations

* `TauCeti.AlgebraicGeometry.AbelianScheme.prod`: the product `A ×_S B`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.prod.isLimit`: the product with its projections is a
  limit cone, so abelian schemes over `S` have finite products.
* `TauCeti.AlgebraicGeometry.AbelianScheme.identityIsTerminal`: the identity abelian scheme is
  terminal.
* `TauCeti.AlgebraicGeometry.AbelianScheme.baseChangeProdIso`: `(A ×_S B)_T ≅ A_T ×_T B_T`.
* `TauCeti.AlgebraicGeometry.AbelianScheme.relativeDimension_prod`: relative dimensions add.
* `TauCeti.AlgebraicGeometry.AbelianScheme.prodIdentityIso` and
  `TauCeti.AlgebraicGeometry.AbelianScheme.identityProdIso`: `A ×_S S ≅ A ≅ S ×_S A`, given by
  the projections to `A`.

## References

* G. Faltings and C.-L. Chai, *Degeneration of abelian varieties*, Chapter I, §1.
* J. S. Milne, *Abelian varieties* (2022 revision), §20.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

open scoped CategoryTheory.Obj

namespace TauCeti

namespace AlgebraicGeometry

namespace AbelianScheme

universe u

variable {S T : Scheme.{u}}

noncomputable section

/-- The **product** `A ×_S B` of two abelian schemes over `S`: the fibre product of the
underlying schemes over `S`, with the componentwise group law.

Its structure morphism is the base change `A ×_S B ⟶ A` of `B ⟶ S` followed by `A ⟶ S`, a
composite of proper smooth morphisms with geometrically connected fibres.

It is reducible so that instance search sees the componentwise group law of
`A.toOver ⊗ B.toOver` on `(A.prod B).toOver`, which the projections and the pairing need. -/
@[expose, reducible] def prod (A B : AbelianScheme S) : AbelianScheme S where
  toOver := A.toOver ⊗ B.toOver
  grpObj := inferInstance
  isProper := MorphismProperty.comp_mem @IsProper _ _
    (inferInstanceAs (IsProper (pullback.fst A.toOver.hom B.toOver.hom))) A.isProper
  smooth := MorphismProperty.comp_mem @Smooth _ _
    (inferInstanceAs (Smooth (pullback.fst A.toOver.hom B.toOver.hom))) A.smooth
  geometricallyConnected :=
    have : GeometricallyConnected (pullback.fst A.toOver.hom B.toOver.hom) := inferInstance
    GeometricallyConnected.comp (pullback.fst A.toOver.hom B.toOver.hom) A.toOver.hom

@[simp]
lemma prod_toOver (A B : AbelianScheme S) : (A.prod B).toOver = A.toOver ⊗ B.toOver :=
  (rfl)

/-- The underlying scheme of a product is the fibre product of the underlying schemes over
`S`. -/
lemma prod_toScheme (A B : AbelianScheme S) :
    (A.prod B).toScheme = pullback A.toOver.hom B.toOver.hom :=
  (rfl)

/-- If `A` and `B` are smooth of relative dimensions `m` and `n` over `S`, their product is smooth
of relative dimension `m + n`. -/
instance smoothOfRelativeDimension_prod (A B : AbelianScheme S) (m n : ℕ)
    [SmoothOfRelativeDimension m A.toOver.hom] [SmoothOfRelativeDimension n B.toOver.hom] :
    SmoothOfRelativeDimension (m + n) (A.prod B).toOver.hom := by
  rw [add_comm]
  exact inferInstanceAs
    (SmoothOfRelativeDimension (n + m) (pullback.fst A.toOver.hom B.toOver.hom ≫ A.toOver.hom))

namespace prod

/-- The first projection `A ×_S B ⟶ A`, a homomorphism of abelian schemes. -/
def fst (A B : AbelianScheme S) : A.prod B ⟶ A :=
  homMk (CartesianMonoidalCategory.fst A.toOver B.toOver)
    (IsMonHom.one_hom (CartesianMonoidalCategory.fst A.toOver B.toOver))
    (IsMonHom.mul_hom (CartesianMonoidalCategory.fst A.toOver B.toOver))

/-- The second projection `A ×_S B ⟶ B`, a homomorphism of abelian schemes. -/
def snd (A B : AbelianScheme S) : A.prod B ⟶ B :=
  homMk (CartesianMonoidalCategory.snd A.toOver B.toOver)
    (IsMonHom.one_hom (CartesianMonoidalCategory.snd A.toOver B.toOver))
    (IsMonHom.mul_hom (CartesianMonoidalCategory.snd A.toOver B.toOver))

/-- The homomorphism `C ⟶ A ×_S B` with components `f` and `g`. -/
def lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) : C ⟶ A.prod B :=
  homMk (CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g))
    (IsMonHom.one_hom (CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g)))
    (IsMonHom.mul_hom (CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g)))

@[simp]
lemma toOverHom_fst (A B : AbelianScheme S) :
    toOverHom (fst A B) = CartesianMonoidalCategory.fst A.toOver B.toOver :=
  toOverHom_homMk _ _ _

@[simp]
lemma toOverHom_snd (A B : AbelianScheme S) :
    toOverHom (snd A B) = CartesianMonoidalCategory.snd A.toOver B.toOver :=
  toOverHom_homMk _ _ _

@[simp]
lemma toOverHom_lift {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) :
    toOverHom (lift f g) = CartesianMonoidalCategory.lift (toOverHom f) (toOverHom g) :=
  toOverHom_homMk _ _ _

@[reassoc (attr := simp)]
lemma lift_fst {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) : lift f g ≫ fst A B = f :=
  toOverHom_injective (by
    rw [toOverHom_comp, toOverHom_lift, toOverHom_fst, CartesianMonoidalCategory.lift_fst])

@[reassoc (attr := simp)]
lemma lift_snd {A B C : AbelianScheme S} (f : C ⟶ A) (g : C ⟶ B) : lift f g ≫ snd A B = g :=
  toOverHom_injective (by
    rw [toOverHom_comp, toOverHom_lift, toOverHom_snd, CartesianMonoidalCategory.lift_snd])

/-- Homomorphisms into a product are determined by their two components. -/
@[ext]
lemma hom_ext {A B C : AbelianScheme S} {f g : C ⟶ A.prod B}
    (hfst : f ≫ fst A B = g ≫ fst A B) (hsnd : f ≫ snd A B = g ≫ snd A B) : f = g := by
  apply toOverHom_injective
  apply CartesianMonoidalCategory.hom_ext
  · rw [← toOverHom_fst, ← toOverHom_comp, ← toOverHom_comp, hfst]
  · rw [← toOverHom_snd, ← toOverHom_comp, ← toOverHom_comp, hsnd]

/-- The product `A ×_S B` with its two projections is a product in the category of abelian
schemes over `S`. -/
def isLimit (A B : AbelianScheme S) : IsLimit (BinaryFan.mk (fst A B) (snd A B)) :=
  BinaryFan.IsLimit.mk _ lift lift_fst lift_snd
    fun f g _ hfst hsnd ↦ hom_ext (by simpa using hfst) (by simpa using hsnd)

end prod

instance hasBinaryProduct (A B : AbelianScheme S) : HasBinaryProduct A B :=
  HasLimit.mk ⟨_, prod.isLimit A B⟩

instance hasBinaryProducts : HasBinaryProducts (AbelianScheme S) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- The identity abelian scheme `S` is a terminal object: the unique homomorphism from `A` is its
structure morphism. -/
def identityIsTerminal : IsTerminal (identity S) :=
  IsTerminal.ofUniqueHom (fun A ↦ homMk (toUnit A.toOver) (IsMonHom.one_hom (toUnit A.toOver))
    (IsMonHom.mul_hom (toUnit A.toOver))) fun _ _ ↦ toOverHom_injective (toUnit_unique _ _)

instance hasTerminal : HasTerminal (AbelianScheme S) :=
  identityIsTerminal.hasTerminal

instance hasFiniteProducts : HasFiniteProducts (AbelianScheme S) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ### Base change of products -/

/-- The comparison `(A ×_S B)_T ⟶ A_T ×_T B_T` is the pairing of the images of the two
projections under the monoidal pullback functor, each of which preserves the group laws. -/
private lemma isMonHom_prodComparison (f : T ⟶ S) (A B : AbelianScheme S) :
    IsMonHom (M := ((A.prod B).baseChange f).toOver)
      (N := ((A.baseChange f).prod (B.baseChange f)).toOver)
      (prodComparisonIso (Over.pullback f) A.toOver B.toOver).hom := by
  rw [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison]
  -- The group laws of `(A.prod B).baseChange f` and of `(A.baseChange f).prod (B.baseChange f)`
  -- are by definition Mathlib's group laws on `(Over.pullback f).obj (A.toOver ⊗ B.toOver)` and
  -- on `(Over.pullback f).obj A.toOver ⊗ (Over.pullback f).obj B.toOver`.
  exact inferInstanceAs (IsMonHom (CartesianMonoidalCategory.lift
    ((Over.pullback f).map (CartesianMonoidalCategory.fst A.toOver B.toOver))
    ((Over.pullback f).map (CartesianMonoidalCategory.snd A.toOver B.toOver))))

/-- The comparison `(A ×_S B)_T ⟶ A_T ×_T B_T` built from the pulled-back projections is an
isomorphism of abelian schemes over `T`. -/
def baseChangeProdIso (f : T ⟶ S) (A B : AbelianScheme S) :
    (A.prod B).baseChange f ≅ (A.baseChange f).prod (B.baseChange f) :=
  @isoMk _ _ _ (prodComparisonIso (Over.pullback f) A.toOver B.toOver)
    (isMonHom_prodComparison f A B)

@[simp]
lemma toOverHom_baseChangeProdIso_hom (f : T ⟶ S) (A B : AbelianScheme S) :
    toOverHom (baseChangeProdIso f A B).hom =
      CartesianMonoidalCategory.prodComparison (Over.pullback f) A.toOver B.toOver :=
  (@toOverHom_isoMk_hom _ _ _ _ (isMonHom_prodComparison f A B)).trans
    (prodComparisonIso_hom _ _ _)

/-- The first component of the base-change comparison is the base change of the first
projection. -/
@[reassoc (attr := simp)]
lemma baseChangeProdIso_hom_fst (f : T ⟶ S) (A B : AbelianScheme S) :
    (baseChangeProdIso f A B).hom ≫ prod.fst _ _ = (baseChangeFunctor f).map (prod.fst A B) :=
  toOverHom_injective (by
    rw [toOverHom_comp, toOverHom_baseChangeProdIso_hom, prod.toOverHom_fst]
    exact (CartesianMonoidalCategory.prodComparison_fst _ _ _).trans
      ((congrArg _ (prod.toOverHom_fst A B).symm).trans (toOverHom_baseChangeFunctor_map f _).symm))

/-- The second component of the base-change comparison is the base change of the second
projection. -/
@[reassoc (attr := simp)]
lemma baseChangeProdIso_hom_snd (f : T ⟶ S) (A B : AbelianScheme S) :
    (baseChangeProdIso f A B).hom ≫ prod.snd _ _ = (baseChangeFunctor f).map (prod.snd A B) :=
  toOverHom_injective (by
    rw [toOverHom_comp, toOverHom_baseChangeProdIso_hom, prod.toOverHom_snd]
    exact (CartesianMonoidalCategory.prodComparison_snd _ _ _).trans
      ((congrArg _ (prod.toOverHom_snd A B).symm).trans (toOverHom_baseChangeFunctor_map f _).symm))

/-! ### Relative dimension -/

/-- **Relative dimensions add**: the relative dimension of `A ×_S B` at `s` is the sum of the
relative dimensions of `A` and `B` at `s`. -/
@[simp]
theorem relativeDimension_prod (A B : AbelianScheme S) (s : S) :
    (A.prod B).relativeDimension s = A.relativeDimension s + B.relativeDimension s := by
  -- Pass to the fibre over `s`, a base with one point, where the relative dimensions of the two
  -- factors are constant.
  let f := S.fromSpecResidueField s
  let p : Spec (S.residueField s) := IsLocalRing.closedPoint _
  have hp : f p = s := S.fromSpecResidueField_apply s p
  have := A.smoothOfRelativeDimension_baseChange_fromSpecResidueField s
  have := B.smoothOfRelativeDimension_baseChange_fromSpecResidueField s
  have key := ((smoothOfRelativeDimension_iff _ _).mp
    (smoothOfRelativeDimension_prod (A.baseChange f) (B.baseChange f) (A.relativeDimension s)
      (B.relativeDimension s))) p
  rwa [← relativeDimension_eq_of_iso (toOverFunctor.mapIso (baseChangeProdIso f A B)),
    relativeDimension_baseChange, hp] at key

/-! ### Products with the identity abelian scheme -/

/-- The product of `A` with the identity abelian scheme is canonically `A`, through the first
projection. -/
def prodIdentityIso (A : AbelianScheme S) : A.prod (identity S) ≅ A :=
  @isoMk _ _ _ (ρ_ A.toOver) (inferInstance : IsMonHom (ρ_ A.toOver).hom)

lemma toOverHom_prodIdentityIso_hom (A : AbelianScheme S) :
    toOverHom (prodIdentityIso A).hom = (ρ_ A.toOver).hom :=
  @toOverHom_isoMk_hom _ _ _ _ (inferInstance : IsMonHom (ρ_ A.toOver).hom)

/-- The isomorphism `A ×_S S ≅ A` is the first projection. -/
@[simp]
lemma prodIdentityIso_hom (A : AbelianScheme S) :
    (prodIdentityIso A).hom = prod.fst A (identity S) :=
  -- The unit of `Over S` is `(identity S).toOver` (`identity_toOver`).
  toOverHom_injective (by
    rw [toOverHom_prodIdentityIso_hom, prod.toOverHom_fst]
    exact rightUnitor_hom A.toOver)

/-- The inverse of `A ×_S S ≅ A` is the section of the first projection. -/
@[reassoc]
lemma prodIdentityIso_inv_fst (A : AbelianScheme S) :
    (prodIdentityIso A).inv ≫ prod.fst A (identity S) = 𝟙 A := by
  rw [← prodIdentityIso_hom, Iso.inv_hom_id]

/-- The product of the identity abelian scheme with `A` is canonically `A`, through the second
projection. -/
def identityProdIso (A : AbelianScheme S) : (identity S).prod A ≅ A :=
  @isoMk _ _ _ (λ_ A.toOver) (inferInstance : IsMonHom (λ_ A.toOver).hom)

lemma toOverHom_identityProdIso_hom (A : AbelianScheme S) :
    toOverHom (identityProdIso A).hom = (λ_ A.toOver).hom :=
  @toOverHom_isoMk_hom _ _ _ _ (inferInstance : IsMonHom (λ_ A.toOver).hom)

/-- The isomorphism `S ×_S A ≅ A` is the second projection. -/
@[simp]
lemma identityProdIso_hom (A : AbelianScheme S) :
    (identityProdIso A).hom = prod.snd (identity S) A :=
  -- The unit of `Over S` is `(identity S).toOver` (`identity_toOver`).
  toOverHom_injective (by
    rw [toOverHom_identityProdIso_hom, prod.toOverHom_snd]
    exact leftUnitor_hom A.toOver)

/-- The inverse of `S ×_S A ≅ A` is the section of the second projection. -/
@[reassoc]
lemma identityProdIso_inv_snd (A : AbelianScheme S) :
    (identityProdIso A).inv ≫ prod.snd (identity S) A = 𝟙 A := by
  rw [← identityProdIso_hom, Iso.inv_hom_id]

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti

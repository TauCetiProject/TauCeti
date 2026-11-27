/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Idempotents
public import TauCeti.LinearAlgebra.TensorProduct.Prod

/-!
# The Picard group of a product of rings

Let `A` and `B` be `R`-algebras whose structure maps make `R → A × B` bijective, so that `R` is
the product ring `A × B` and `Spec R` is the disjoint union of the clopen pieces `Spec A` and
`Spec B`. Then an invertible `R`-module is determined by its two base changes, and every pair of
invertible modules over `A` and over `B` glues to an invertible `R`-module, namely their product.
So extension of scalars to the two factors is an isomorphism of Picard groups
`Pic R ≃* Pic A × Pic B`, whose inverse sends the classes of `P` and `Q` to the class of `P × Q`.

Two instances are recorded: the product ring `A × B` with its projections, and a ring `R` with
an idempotent `e`, split as `R / (1 - e) × R / (e)`. The latter is the restriction of a Picard
class to a clopen subset of `Spec R` and to its complement; it is what makes a Picard class
locally determined over a finite clopen partition of `Spec R`.

## Main declarations

* `Module.Invertible.prod_of_bijective`: the product of an invertible `A`-module and an
  invertible `B`-module is an invertible `R`-module.
* `CommRing.Pic.prodEquivOfBijective`: the isomorphism `Pic R ≃* Pic A × Pic B` given by
  extension of scalars, with `CommRing.Pic.prodEquivOfBijective_symm_mk` computing its inverse.
* `CommRing.Pic.prodEquiv`: the isomorphism `Pic (A × B) ≃* Pic A × Pic B`, with inverse
  computed by `CommRing.Pic.prodEquiv_symm_mk`.
* `CommRing.Pic.prodEquivOfIsIdempotentElem`: for an idempotent `e` of `R`, the isomorphism
  `Pic R ≃* Pic (R ⧸ span {1 - e}) × Pic (R ⧸ span {e})`, with inverse computed by
  `CommRing.Pic.prodEquivOfIsIdempotentElem_symm_mk`; `CommRing.Pic.ext_of_isIdempotentElem` says
  that a Picard class is determined by its base changes to the two factors.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145, AMS, 2013, Chapter I, Section 3 (the Picard group of a commutative ring).
-/

public section

open TensorProduct Module

section Bijective

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A]
  [Algebra R B] (h : Function.Bijective ((algebraMap R A).prod (algebraMap R B)))
  (P Q : Type*) [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]
  [AddCommMonoid Q] [Module R Q] [Module B Q] [IsScalarTower R B Q]

include h

/-- Given inverses `P'` of `P` over `A` and `Q'` of `Q` over `B`, the product `P' × Q'` is an
inverse of `P × Q` over `R`. -/
private noncomputable def tensorProdEquiv {P' Q' : Type*} [AddCommMonoid P'] [Module R P']
    [Module A P'] [IsScalarTower R A P'] [AddCommMonoid Q'] [Module R Q'] [Module B Q']
    [IsScalarTower R B Q'] (eP : P' ⊗[A] P ≃ₗ[A] A) (eQ : Q' ⊗[B] Q ≃ₗ[B] B) :
    (P' × Q') ⊗[R] (P × Q) ≃ₗ[R] R :=
  haveI := subsingleton_of_surjective_prod h.surjective (P := P') (Q := Q)
  haveI := subsingleton_of_surjective_prod h.surjective (P := P) (Q := Q')
  haveI : Subsingleton (Q' ⊗[R] P) := (TensorProduct.comm R Q' P).toEquiv.subsingleton
  letI : Unique (P' ⊗[R] Q) := uniqueOfSubsingleton 0
  letI : Unique (Q' ⊗[R] P) := uniqueOfSubsingleton 0
  haveI : CompatibleSMul R A P' P := .of_algebraMap_surjective _ _
    (Algebra.algebraMap_surjective_fst_of_surjective_prod h.surjective)
  haveI : CompatibleSMul R B Q' Q := .of_algebraMap_surjective _ _
    (Algebra.algebraMap_surjective_snd_of_surjective_prod h.surjective)
  prodLeft R R P' Q' (P × Q) ≪≫ₗ
    (prodRight R R P' P Q ≪≫ₗ LinearEquiv.prodUnique).prodCongr
      (prodRight R R Q' P Q ≪≫ₗ LinearEquiv.uniqueProd) ≪≫ₗ
    ((equivOfCompatibleSMul R A R P' P).symm ≪≫ₗ eP.restrictScalars R).prodCongr
      ((equivOfCompatibleSMul R B R Q' Q).symm ≪≫ₗ eQ.restrictScalars R) ≪≫ₗ
    (Algebra.linearEquivProdOfBijective h).symm

/-- If `R → A × B` is bijective, the product of an invertible `A`-module and an invertible
`B`-module is an invertible `R`-module. -/
theorem Module.Invertible.prod_of_bijective [Module.Invertible A P] [Module.Invertible B Q] :
    Module.Invertible R (P × Q) :=
  .right (tensorProdEquiv h P Q (Module.Invertible.linearEquiv A P)
    (Module.Invertible.linearEquiv B Q))

end Bijective

namespace CommRing.Pic

section Bijective

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A]
  [Algebra R B] (h : Function.Bijective ((algebraMap R A).prod (algebraMap R B)))

section Modules

variable (hs : Function.Surjective ((algebraMap R A).prod (algebraMap R B)))
  {P Q : Type*} [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]
  [AddCommMonoid Q] [Module R Q] [Module B Q] [IsScalarTower R B Q]

include hs

/-- If `R → A × B` is surjective, the class of the product of an `A`-module `P` and a `B`-module
`Q` restricts to the class of `P` over `A`. -/
theorem mapAlgebra_mk_prod_fst_of_surjective [Module.Invertible A P]
    [Module.Invertible R (P × Q)] : mapAlgebra R A (Pic.mk R (P × Q)) = Pic.mk A P := by
  rw [mapAlgebra_apply, mk_eq_mk_iff]
  exact ⟨AlgebraTensorModule.congr (.refl A A) (mk.linearEquiv ..) ≪≫ₗ
    prodRightEquivFstOfSurjective hs P Q⟩

/-- If `R → A × B` is surjective, the class of the product of an `A`-module `P` and a `B`-module
`Q` restricts to the class of `Q` over `B`. -/
theorem mapAlgebra_mk_prod_snd_of_surjective [Module.Invertible B Q]
    [Module.Invertible R (P × Q)] : mapAlgebra R B (Pic.mk R (P × Q)) = Pic.mk B Q := by
  rw [mapAlgebra_apply, mk_eq_mk_iff]
  exact ⟨AlgebraTensorModule.congr (.refl B B) (mk.linearEquiv ..) ≪≫ₗ
    prodRightEquivSndOfSurjective hs P Q⟩

end Modules

include h

/-- If `R → A × B` is bijective, a Picard class of `R` is determined by its base changes to `A`
and to `B`. -/
theorem prod_mapAlgebra_injective_of_bijective :
    Function.Injective ((mapAlgebra R A).prod (mapAlgebra R B)) := by
  refine (injective_iff_map_eq_one _).mpr fun M hM ↦ ?_
  obtain ⟨hA, hB⟩ := Prod.ext_iff.mp hM
  simp only [MonoidHom.prod_apply, Prod.fst_one, Prod.snd_one, mapAlgebra_apply,
    mk_eq_one_iff] at hA hB
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  rw [← mk_eq_self (M := M), mk_eq_one_iff]
  exact ⟨equivProdOfBijective h M ≪≫ₗ
    (eA.restrictScalars R).prodCongr (eB.restrictScalars R) ≪≫ₗ
    (Algebra.linearEquivProdOfBijective h).symm⟩

/-- If `R → A × B` is bijective, every pair of Picard classes of `A` and of `B` comes from a
Picard class of `R`. -/
theorem prod_mapAlgebra_surjective_of_bijective :
    Function.Surjective ((mapAlgebra R A).prod (mapAlgebra R B)) := by
  rintro ⟨P, Q⟩
  let : Module R P := Module.compHom P (algebraMap R A)
  have : IsScalarTower R A P := IsScalarTower.of_compHom R A P
  let : Module R Q := Module.compHom Q (algebraMap R B)
  have : IsScalarTower R B Q := IsScalarTower.of_compHom R B Q
  have := Module.Invertible.prod_of_bijective h P Q
  refine ⟨Pic.mk R (P × Q), Prod.ext ?_ ?_⟩
  · rw [MonoidHom.prod_apply, mapAlgebra_mk_prod_fst_of_surjective h.surjective, mk_eq_self]
  · rw [MonoidHom.prod_apply, mapAlgebra_mk_prod_snd_of_surjective h.surjective, mk_eq_self]

/-- If `R → A × B` is bijective, extension of scalars to `A` and to `B` is a bijection
`Pic R → Pic A × Pic B`. -/
theorem prod_mapAlgebra_bijective_of_bijective :
    Function.Bijective ((mapAlgebra R A).prod (mapAlgebra R B)) :=
  ⟨prod_mapAlgebra_injective_of_bijective h, prod_mapAlgebra_surjective_of_bijective h⟩

/-- If `R → A × B` is bijective, then the Picard group of `R` is the product of the Picard
groups of `A` and `B`, by extension of scalars to each factor. -/
noncomputable def prodEquivOfBijective : Pic R ≃* Pic A × Pic B :=
  .ofBijective ((mapAlgebra R A).prod (mapAlgebra R B)) (prod_mapAlgebra_bijective_of_bijective h)

@[simp]
theorem prodEquivOfBijective_apply (M : Pic R) :
    prodEquivOfBijective h M = (mapAlgebra R A M, mapAlgebra R B M) := by
  rw [prodEquivOfBijective, MulEquiv.ofBijective_apply, MonoidHom.prod_apply]

/-- If `R → A × B` is bijective, the inverse of `prodEquivOfBijective` sends the classes of an
invertible `A`-module `P` and an invertible `B`-module `Q` to the class of `P × Q`. -/
theorem prodEquivOfBijective_symm_mk {P Q : Type*} [AddCommMonoid P] [Module R P] [Module A P]
    [IsScalarTower R A P] [AddCommMonoid Q] [Module R Q] [Module B Q] [IsScalarTower R B Q]
    [Module.Invertible A P] [Module.Invertible B Q] :
    haveI := Module.Invertible.prod_of_bijective h P Q
    (prodEquivOfBijective h).symm (Pic.mk A P, Pic.mk B Q) = Pic.mk R (P × Q) := by
  have := Module.Invertible.prod_of_bijective h P Q
  rw [MulEquiv.symm_apply_eq, prodEquivOfBijective_apply,
    mapAlgebra_mk_prod_fst_of_surjective h.surjective,
    mapAlgebra_mk_prod_snd_of_surjective h.surjective]

end Bijective

section Prod

variable (A B : Type*) [CommSemiring A] [CommSemiring B]

/-- The Picard group of a product of two commutative semirings is the product of their Picard
groups, by extension of scalars along the two projections. -/
noncomputable def prodEquiv : Pic (A × B) ≃* Pic A × Pic B :=
  letI := (RingHom.fst A B).toAlgebra
  letI := (RingHom.snd A B).toAlgebra
  -- For these algebra structures `R → A × B` is the identity of `A × B`.
  prodEquivOfBijective (R := A × B) Function.bijective_id

@[simp]
theorem prodEquiv_apply (M : Pic (A × B)) :
    prodEquiv A B M = (mapRingHom (RingHom.fst A B) M, mapRingHom (RingHom.snd A B) M) := by
  let := (RingHom.fst A B).toAlgebra
  let := (RingHom.snd A B).toAlgebra
  -- `mapRingHom f` is by definition `mapAlgebra` for the algebra structure `f.toAlgebra`.
  exact prodEquivOfBijective_apply (R := A × B) Function.bijective_id M

/-- The inverse of `prodEquiv` sends the classes of an invertible `A`-module `P` and an invertible
`B`-module `Q` to the class of `P × Q`, on which `A × B` acts through the two projections. -/
theorem prodEquiv_symm_mk {P Q : Type*} [AddCommMonoid P] [Module A P] [AddCommMonoid Q]
    [Module B Q] [Module.Invertible A P] [Module.Invertible B Q] :
    letI := (RingHom.fst A B).toAlgebra
    letI := (RingHom.snd A B).toAlgebra
    letI := Module.compHom P (RingHom.fst A B)
    letI := Module.compHom Q (RingHom.snd A B)
    haveI := IsScalarTower.of_compHom (A × B) A P
    haveI := IsScalarTower.of_compHom (A × B) B Q
    haveI := Module.Invertible.prod_of_bijective (R := A × B) Function.bijective_id P Q
    (prodEquiv A B).symm (Pic.mk A P, Pic.mk B Q) = Pic.mk (A × B) (P × Q) := by
  let := (RingHom.fst A B).toAlgebra
  let := (RingHom.snd A B).toAlgebra
  let := Module.compHom P (RingHom.fst A B)
  let := Module.compHom Q (RingHom.snd A B)
  have := IsScalarTower.of_compHom (A × B) A P
  have := IsScalarTower.of_compHom (A × B) B Q
  exact prodEquivOfBijective_symm_mk (R := A × B) Function.bijective_id

end Prod

section Idempotent

variable {R : Type*} [CommRing R] {e : R}

/-- For an idempotent `e`, the Picard group of `R` is the product of the Picard groups of
`R ⧸ span {1 - e}` and `R ⧸ span {e}`: a Picard class is determined by, and can be prescribed
arbitrarily on, a clopen subset of `Spec R` and its complement. -/
noncomputable def prodEquivOfIsIdempotentElem (he : IsIdempotentElem e) :
    Pic R ≃* Pic (R ⧸ Ideal.span {1 - e}) × Pic (R ⧸ Ideal.span {e}) :=
  prodEquivOfBijective <| RingHom.prod_bijective_of_isIdempotentElem he.one_sub he
    (sub_add_cancel 1 e) he.one_sub_mul_self

@[simp]
theorem prodEquivOfIsIdempotentElem_apply (he : IsIdempotentElem e) (M : Pic R) :
    prodEquivOfIsIdempotentElem he M =
      (mapAlgebra R (R ⧸ Ideal.span {1 - e}) M, mapAlgebra R (R ⧸ Ideal.span {e}) M) :=
  prodEquivOfBijective_apply _ M

/-- For an idempotent `e`, the inverse of `prodEquivOfIsIdempotentElem` glues the classes of an
invertible module `P` over `R ⧸ span {1 - e}` and an invertible module `Q` over `R ⧸ span {e}` to
the class of `P × Q`. -/
theorem prodEquivOfIsIdempotentElem_symm_mk (he : IsIdempotentElem e) {P Q : Type*}
    [AddCommMonoid P] [Module R P] [Module (R ⧸ Ideal.span {1 - e}) P]
    [IsScalarTower R (R ⧸ Ideal.span {1 - e}) P] [AddCommMonoid Q] [Module R Q]
    [Module (R ⧸ Ideal.span {e}) Q] [IsScalarTower R (R ⧸ Ideal.span {e}) Q]
    [Module.Invertible (R ⧸ Ideal.span {1 - e}) P] [Module.Invertible (R ⧸ Ideal.span {e}) Q] :
    haveI := Module.Invertible.prod_of_bijective (RingHom.prod_bijective_of_isIdempotentElem
      he.one_sub he (sub_add_cancel 1 e) he.one_sub_mul_self) P Q
    (prodEquivOfIsIdempotentElem he).symm
      (Pic.mk (R ⧸ Ideal.span {1 - e}) P, Pic.mk (R ⧸ Ideal.span {e}) Q) = Pic.mk R (P × Q) :=
  prodEquivOfBijective_symm_mk _

/-- For an idempotent `e`, a Picard class over `R` is determined by its base changes to
`R ⧸ span {1 - e}` and `R ⧸ span {e}`, that is, to the clopen set `D(e)` of `Spec R` and to its
complement. -/
theorem ext_of_isIdempotentElem (he : IsIdempotentElem e) {L M : Pic R}
    (h₁ : mapRingHom (Ideal.Quotient.mk (Ideal.span {1 - e})) L =
      mapRingHom (Ideal.Quotient.mk (Ideal.span {1 - e})) M)
    (h₂ : mapRingHom (Ideal.Quotient.mk (Ideal.span {e})) L =
      mapRingHom (Ideal.Quotient.mk (Ideal.span {e})) M) : L = M := by
  refine (prodEquivOfIsIdempotentElem he).injective (Prod.ext ?_ ?_) <;>
    simpa [← mapRingHom_algebraMap, Ideal.Quotient.algebraMap_eq]

end Idempotent

end CommRing.Pic

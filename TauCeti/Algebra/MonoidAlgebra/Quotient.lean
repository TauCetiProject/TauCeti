/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.MonoidAlgebra.Basic
import TauCeti.RingTheory.Ideal.Extended

/-!
# Quotients of monoid algebras by coefficient ideals

For a commutative semiring `R`, an ideal `I` of a commutative `R`-algebra `A`, and a monoid `M`
(not necessarily commutative), pushing `I` forward along
`MonoidAlgebra.singleOneRingHom : A →+* A[M]` cuts out the two-sided ideal of elements whose
coefficients all lie in `I` (`MonoidAlgebra.mem_map_singleOneRingHom_iff`). When `A` is a
commutative ring, reducing coefficients modulo `I` has this exact kernel and yields
`MonoidAlgebra.quotientAlgEquiv : A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`.

## Main declarations

* `MonoidAlgebra.mem_map_singleOneRingHom_iff`: membership in `I.map singleOneRingHom` is
  equivalent to every coefficient lying in `I`.
* `MonoidAlgebra.instIsTwoSidedMapSingleOneRingHom`: `I.map singleOneRingHom` is a two-sided ideal
  of `A[M]` even when `M` is non-commutative.
* `MonoidAlgebra.ker_mapRingHom_quotientMk`, `MonoidAlgebra.ker_mapAlgHom_quotientMk`: reducing
  coefficients modulo `I` has kernel `I.map singleOneRingHom`.
* `MonoidAlgebra.quotientAlgEquiv`: canonical `R`-algebra isomorphism
  `A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`.
-/

public section

namespace MonoidAlgebra

section Semiring
variable {A : Type*} [CommSemiring A] {M : Type*} [Monoid M]

private theorem singleOneRingHom_eq_algebraMap :
    (singleOneRingHom : A →+* MonoidAlgebra A M) = algebraMap A (MonoidAlgebra A M) :=
  RingHom.ext fun _ ↦ by simp

/-- An element of `A[M]` lies in `I.map singleOneRingHom` iff every coefficient lies in `I`. -/
@[simp] theorem mem_map_singleOneRingHom_iff {I : Ideal A} {x : MonoidAlgebra A M} :
    x ∈ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I ↔ ∀ m, x.coeff m ∈ I := by
  rw [singleOneRingHom_eq_algebraMap, Ideal.mem_map_algebraMap_iff,
    TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff]

/-- Pushing an ideal `I` of a commutative semiring `A` forward along `singleOneRingHom` produces a
two-sided ideal of `A[M]` even when `M` is non-commutative, because the elements of `A` are central
in `A[M]`. -/
instance instIsTwoSidedMapSingleOneRingHom (I : Ideal A) :
    (Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I).IsTwoSided :=
  singleOneRingHom_eq_algebraMap (A := A) (M := M) ▸ Ideal.instIsTwoSidedMapAlgebraMap I
end Semiring

section CommRing
variable (R : Type*) [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]
  (M : Type*) [Monoid M] (I : Ideal A)

/-- The kernel of coefficientwise reduction `A[M] →+* (A ⧸ I)[M]` is the pushforward ideal
`I.map singleOneRingHom`. -/
theorem ker_mapRingHom_quotientMk :
    RingHom.ker (mapRingHom M (Ideal.Quotient.mk I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I := by
  ext x; simp only [RingHom.mem_ker, mem_map_singleOneRingHom_iff,
    TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff, Ideal.mk_ker,
    TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff]

/-- The kernel of the `R`-algebra coefficientwise reduction `A[M] →ₐ[R] (A ⧸ I)[M]` is
`I.map singleOneRingHom`. -/
theorem ker_mapAlgHom_quotientMk :
    RingHom.ker (mapAlgHom M (Ideal.Quotient.mkₐ R I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I := by
  rw [← RingHom.ker_coe_toRingHom, toRingHom_mapAlgHom, Ideal.Quotient.mkₐ_toRingHom,
    ker_mapRingHom_quotientMk]

/-- Reducing coefficients modulo `I` gives `A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`. -/
noncomputable def quotientAlgEquiv :
    (MonoidAlgebra A M ⧸ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I) ≃ₐ[R]
      MonoidAlgebra (A ⧸ I) M :=
  (Ideal.quotientEquivAlgOfEq R (ker_mapAlgHom_quotientMk R M I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := mapAlgHom M (Ideal.Quotient.mkₐ R I))
      (map_surjective (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective))

@[simp] theorem quotientAlgEquiv_mk (x : MonoidAlgebra A M) :
    quotientAlgEquiv R M I (Ideal.Quotient.mk _ x) = mapAlgHom M (Ideal.Quotient.mkₐ R I) x := (rfl)
@[simp] theorem quotientAlgEquiv_symm_single_mk (m : M) (a : A) :
    (quotientAlgEquiv R M I).symm (single m (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (single m a) :=
  (quotientAlgEquiv R M I).injective (by simp)
end CommRing

end MonoidAlgebra

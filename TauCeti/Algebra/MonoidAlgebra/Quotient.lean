/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.MonoidAlgebra.Basic

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

/-- An element of `A[M]` lies in `I.map singleOneRingHom` iff every coefficient lies in `I`. -/
@[simp] theorem mem_map_singleOneRingHom_iff {I : Ideal A} {x : MonoidAlgebra A M} :
    x ∈ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I ↔ ∀ m, x.coeff m ∈ I := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · intro hx
    refine Submodule.span_induction ?_ (by simp)
      (fun _ _ _ _ hx hy m ↦ by simpa using I.add_mem (hx m) (hy m)) (fun y x _ hx m ↦ ?_) hx
    · rintro _ ⟨a, ha, rfl⟩ m
      classical rcases eq_or_ne (1 : M) m with hm | hm; · simpa [hm] using ha
      · simp [hm]
    · classical
      rw [smul_eq_mul, coeff_mul]; simp only [Finsupp.sum]
      refine Submodule.sum_mem I fun m₁ _ ↦ Submodule.sum_mem I fun m₂ _ ↦ ?_
      split_ifs
      · exact I.mul_mem_left _ (hx m₂)
      · exact I.zero_mem
  · rw [← sum_coeff_single x, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    have h : single m (x.coeff m) = single m 1 * singleOneRingHom (x.coeff m) := by
      simp [single_mul_single]
    exact h ▸ Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem singleOneRingHom (hx m))

/-- Pushing an ideal `I` of a commutative semiring `A` forward along `singleOneRingHom` produces a
two-sided ideal of `A[M]` even when `M` is non-commutative, because the elements of `A` are central
in `A[M]`. -/
instance instIsTwoSidedMapSingleOneRingHom (I : Ideal A) :
    (Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I).IsTwoSided where
  mul_mem_of_left {x} y hx := mem_map_singleOneRingHom_iff.2 fun m ↦ by
    classical
    rw [coeff_mul]; simp only [Finsupp.sum]
    refine Submodule.sum_mem I fun m₁ _ ↦ Submodule.sum_mem I fun m₂ _ ↦ ?_
    split_ifs
    · exact I.mul_mem_right _ (mem_map_singleOneRingHom_iff.1 hx m₁)
    · exact I.zero_mem

end Semiring

section CommRing

variable (R : Type*) [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]
  (M : Type*) [Monoid M] (I : Ideal A)

/-- The kernel of coefficientwise reduction `A[M] →+* (A ⧸ I)[M]` is the pushforward ideal
`I.map singleOneRingHom`. -/
theorem ker_mapRingHom_quotientMk :
    RingHom.ker (mapRingHom M (Ideal.Quotient.mk I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I := by
  ext x; simp [RingHom.mem_ker, TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff,
    TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff]

/-- The kernel of the `R`-algebra coefficientwise reduction `A[M] →ₐ[R] (A ⧸ I)[M]` is
`I.map singleOneRingHom`. -/
theorem ker_mapAlgHom_quotientMk :
    RingHom.ker (mapAlgHom M (Ideal.Quotient.mkₐ R I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I :=
  ker_mapRingHom_quotientMk M I

/-- Reducing coefficients modulo `I` gives `A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`. -/
noncomputable def quotientAlgEquiv :
    (MonoidAlgebra A M ⧸ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I) ≃ₐ[R]
      MonoidAlgebra (A ⧸ I) M :=
  (Ideal.quotientEquivAlgOfEq R (ker_mapAlgHom_quotientMk R M I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := mapAlgHom M (Ideal.Quotient.mkₐ R I))
      (map_surjective (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective))

@[simp] theorem quotientAlgEquiv_mk (x : MonoidAlgebra A M) :
    quotientAlgEquiv R M I (Ideal.Quotient.mk _ x) = mapAlgHom M (Ideal.Quotient.mkₐ R I) x :=
  (rfl)

@[simp] theorem quotientAlgEquiv_symm_single_mk (m : M) (a : A) :
    (quotientAlgEquiv R M I).symm (single m (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (single m a) :=
  (quotientAlgEquiv R M I).injective (by simp)

end CommRing

end MonoidAlgebra

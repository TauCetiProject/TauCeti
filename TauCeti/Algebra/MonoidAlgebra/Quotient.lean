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

For an ideal `I` of a commutative ring `A` and a monoid `M`, pushing `I` forward along
`MonoidAlgebra.singleOneRingHom : A →+* A[M]` yields the two-sided ideal of elements of `A[M]` all
of whose coefficients lie in `I` (`MonoidAlgebra.mem_map_singleOneRingHom_iff`). This ideal is the
kernel of the coefficientwise reduction `A[M] →ₐ[R] (A ⧸ I)[M]`, giving the canonical isomorphism
`MonoidAlgebra.quotientAlgEquiv : A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`.

## Main declarations

* `MonoidAlgebra.mem_map_singleOneRingHom_iff`: an element of `A[M]` lies in
  `I.map singleOneRingHom` if and only if all of its coefficients lie in `I`.
* `MonoidAlgebra.ker_mapAlgHom_quotientMk`: the kernel of the coefficientwise quotient map
  `A[M] →ₐ[R] (A ⧸ I)[M]` is `I.map singleOneRingHom`.
* `MonoidAlgebra.quotientAlgEquiv`: the `R`-algebra isomorphism
  `A[M] ⧸ I.map singleOneRingHom ≃ₐ[R] (A ⧸ I)[M]`.
-/

public section

namespace MonoidAlgebra

section Semiring

variable {A : Type*} [CommSemiring A] {M : Type*} [Monoid M]

/-- An element of `A[M]` lies in `I.map singleOneRingHom` if and only if every coefficient lies in
`I`. -/
@[simp]
theorem mem_map_singleOneRingHom_iff {I : Ideal A} {x : MonoidAlgebra A M} :
    x ∈ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I ↔ ∀ m, x.coeff m ∈ I := by
  constructor
  · intro hx
    refine Submodule.span_induction ?_ (by simp)
      (fun x y _ _ hx hy m ↦ by simpa using I.add_mem (hx m) (hy m))
      (fun y x _ hx m ↦ ?_) hx
    · rintro _ ⟨a, ha, rfl⟩ m
      classical
      change (single (1 : M) a).coeff m ∈ I
      rw [coeff_single, Finsupp.single_apply]
      split_ifs
      · exact ha
      · exact I.zero_mem
    · classical
      rw [smul_eq_mul, coeff_mul, Finsupp.sum]
      refine Submodule.sum_mem I fun m₁ _ ↦ ?_
      rw [Finsupp.sum]
      refine Submodule.sum_mem I fun m₂ _ ↦ ?_
      split_ifs
      · exact I.mul_mem_left _ (hx m₂)
      · exact I.zero_mem
  · intro hx
    rw [← sum_coeff_single x, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    have h : single m (x.coeff m) = single m 1 * singleOneRingHom (x.coeff m) := by
      simp [single_mul_single]
    rw [h]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem singleOneRingHom (hx m))

/-- The ideal `I.map singleOneRingHom` in `A[M]` is two-sided, even when `M` is not commutative. -/
instance instIsTwoSidedMapSingleOneRingHom (I : Ideal A) :
    (Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I).IsTwoSided where
  mul_mem_of_left {x} y hx := by
    classical
    rw [mem_map_singleOneRingHom_iff] at hx ⊢
    intro m
    rw [coeff_mul, Finsupp.sum]
    refine Submodule.sum_mem I fun m₁ _ ↦ ?_
    rw [Finsupp.sum]
    refine Submodule.sum_mem I fun m₂ _ ↦ ?_
    split_ifs
    · exact I.mul_mem_right _ (hx m₁)
    · exact I.zero_mem

end Semiring

section CommRing

variable (R : Type*) [CommSemiring R] {A : Type*} [CommRing A] [Algebra R A]
  (M : Type*) [Monoid M] (I : Ideal A)

/-- The kernel of the coefficientwise quotient map `A[M] →+* (A ⧸ I)[M]` is
`I.map singleOneRingHom`. -/
theorem ker_mapRingHom_quotientMk :
    RingHom.ker (mapRingHom M (Ideal.Quotient.mk I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I := by
  ext x
  simp [RingHom.mem_ker, TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff,
    TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff]

/-- The kernel of the coefficientwise quotient map `A[M] →ₐ[R] (A ⧸ I)[M]` is
`I.map singleOneRingHom`. -/
theorem ker_mapAlgHom_quotientMk :
    RingHom.ker (mapAlgHom M (Ideal.Quotient.mkₐ R I)) =
      Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I :=
  ker_mapRingHom_quotientMk M I

/-- **Quotient of a monoid algebra by a coefficient ideal.** Reducing the coefficients of `A[M]`
modulo an ideal `I` of `A` identifies `A[M] ⧸ I.map singleOneRingHom` with `(A ⧸ I)[M]`. -/
noncomputable def quotientAlgEquiv :
    (MonoidAlgebra A M ⧸ Ideal.map (singleOneRingHom : A →+* MonoidAlgebra A M) I) ≃ₐ[R]
      MonoidAlgebra (A ⧸ I) M :=
  (Ideal.quotientEquivAlgOfEq R (ker_mapAlgHom_quotientMk R M I).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := mapAlgHom M (Ideal.Quotient.mkₐ R I))
      (map_surjective (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective))

@[simp]
theorem quotientAlgEquiv_mk (x : MonoidAlgebra A M) :
    quotientAlgEquiv R M I (Ideal.Quotient.mk _ x) =
      mapAlgHom M (Ideal.Quotient.mkₐ R I) x :=
  (rfl)

@[simp]
theorem quotientAlgEquiv_symm_single_mk (m : M) (a : A) :
    (quotientAlgEquiv R M I).symm (single m (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (single m a) := by
  apply (quotientAlgEquiv R M I).injective
  simp

end CommRing

end MonoidAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Componentwise quotient maps of products

For families of two-sided ideals `I j ≤ J j` of an `R₁`-algebra `A`, the quotient maps
`A ⧸ I j → A ⧸ J j` assemble into an `R₁`-algebra map `∏ j, A ⧸ I j → ∏ j, A ⧸ J j`, which is
surjective. This is the product version of Mathlib's `Ideal.Quotient.factorₐ`.

For ideals `I i` of a commutative ring and exponents `n i`, the factors of `∏ i, A ⧸ I i ^ n i`
with `n i = 0` are zero, so restricting to the factors with `n i ≠ 0` is a linear bijection.

Conversely, for an arbitrary family of rings `R i` and two-sided ideals `I i`, the quotient of
`∏ i, R i` by the product ideal `Ideal.pi I` is canonically ring-isomorphic to `∏ i, R i ⧸ I i`
(`Ideal.piQuotRingEquiv`), and for a principal ideal `(d)` in a product of commutative rings this
gives `(∏ i, R i) ⧸ (d) ≃+* ∏ i, R i ⧸ (d i)` (`Ideal.quotientSpanSingletonPiEquiv`).

## Main declarations

* `TauCeti.Ideal.Quotient.piFactorₐ`: the componentwise quotient map.
* `TauCeti.Ideal.Quotient.piFactorₐ_surjective`: it is surjective.
* `TauCeti.Ideal.Quotient.bijective_pi_restrict_pow`: dropping the factors `A ⧸ I ^ 0 = 0` from
  `∏ i, A ⧸ I i ^ n i` is a linear bijection.
* `Ideal.piQuotRingEquiv`: `(∏ i, R i) ⧸ Ideal.pi I ≃+* ∏ i, (R i ⧸ I i)`.
* `Ideal.quotientSpanSingletonPiEquiv`:
  `(∏ i, R i) ⧸ Ideal.span {d} ≃+* ∏ i, R i ⧸ Ideal.span {d i}`.
-/

public section

namespace TauCeti

namespace Ideal.Quotient

variable (R₁ : Type*) {A : Type*} [CommSemiring R₁] [Ring A] [Algebra R₁ A] {ι : Type*}
  {I J : ι → Ideal A} [∀ j, (I j).IsTwoSided] [∀ j, (J j).IsTwoSided]

/-- The componentwise quotient map `∏ j, A ⧸ I j → ∏ j, A ⧸ J j` for ideals `I j ≤ J j`. -/
def piFactorₐ (hle : ∀ j, I j ≤ J j) : ((j : ι) → A ⧸ I j) →ₐ[R₁] ((j : ι) → A ⧸ J j) :=
  AlgHom.pi fun j ↦ (Ideal.Quotient.factorₐ R₁ (hle j)).comp (Pi.evalAlgHom R₁ _ j)

/-- Each component of `piFactorₐ` is the quotient map `A ⧸ I j → A ⧸ J j`. -/
@[simp]
theorem piFactorₐ_apply (hle : ∀ j, I j ≤ J j) (x : (j : ι) → A ⧸ I j) (j : ι) :
    piFactorₐ R₁ hle x j = Ideal.Quotient.factor (hle j) (x j) :=
  (rfl)

/-- The componentwise quotient map is surjective. -/
theorem piFactorₐ_surjective (hle : ∀ j, I j ≤ J j) :
    Function.Surjective (piFactorₐ R₁ hle) :=
  -- `piFactorₐ R₁ hle` is definitionally `Pi.map` of the factor maps, as in `piFactorₐ_apply`.
  Function.Surjective.piMap fun j ↦ Ideal.Quotient.factor_surjective (hle j)

end Ideal.Quotient

namespace Ideal.Quotient

variable {A : Type*} [CommRing A]

/-- Dropping the factors with exponent zero from `∏ᵢ A ⧸ Iᵢ ^ nᵢ` is bijective, as those factors
are `A ⧸ A = 0`. -/
theorem bijective_pi_restrict_pow {ι : Type*} (I : ι → Ideal A) (n : ι → ℕ) :
    Function.Bijective (LinearMap.pi fun y : {i // n i ≠ 0} ↦ LinearMap.proj y.1 :
      (∀ i, A ⧸ I i ^ n i) →ₗ[A] ∀ y : {i // n i ≠ 0}, A ⧸ I y ^ n y) := by
  classical
  refine ⟨fun x x' hxx' ↦ funext fun i ↦ ?_, fun y ↦ ?_⟩
  · by_cases hi : n i = 0
    · have : Subsingleton (A ⧸ I i ^ n i) := by
        rw [Ideal.Quotient.subsingleton_iff]
        simp [hi]
      exact Subsingleton.elim _ _
    · exact congr_fun hxx' ⟨i, hi⟩
  · refine ⟨fun i ↦ if hi : n i = 0 then 0 else y ⟨i, hi⟩, funext fun i ↦ ?_⟩
    simp only [LinearMap.pi_apply, LinearMap.proj_apply, i.2, ↓reduceDIte]

end Ideal.Quotient

end TauCeti

namespace Ideal

section Ring

variable {ι : Type*} {R : ι → Type*} [∀ i, Ring (R i)] (I : ∀ i, Ideal (R i))
  [∀ i, (I i).IsTwoSided]

/-- The quotient of a product of rings by a product ideal `Ideal.pi I` is canonically isomorphic
to the product of the factorwise quotients. The index type need not be finite. -/
noncomputable def piQuotRingEquiv : ((∀ i, R i) ⧸ Ideal.pi I) ≃+* ∀ i, R i ⧸ I i :=
  RingEquiv.ofBijective
    (Ideal.Quotient.lift (Ideal.pi I)
      (RingHom.pi fun i ↦ (Ideal.Quotient.mk (I i)).comp (Pi.evalRingHom R i))
      fun _ hx ↦ funext fun i ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hx i))
    ⟨by
      rw [injective_lift_iff]
      ext x
      simp [RingHom.mem_ker, funext_iff, Ideal.Quotient.eq_zero_iff_mem, mem_pi],
     fun y ↦ ⟨Ideal.Quotient.mk (Ideal.pi I) fun i ↦ Quotient.out (y i),
      funext fun i ↦ Quotient.out_eq' (y i)⟩⟩

/-- `piQuotRingEquiv` sends the class of `x` to the family of factorwise classes `mk (I i) (x i)`.
-/
@[simp]
theorem piQuotRingEquiv_mk (x : ∀ i, R i) :
    piQuotRingEquiv I (Ideal.Quotient.mk (Ideal.pi I) x) =
      fun i ↦ Ideal.Quotient.mk (I i) (x i) :=
  (rfl)

/-- `(piQuotRingEquiv I).symm` sends a family of classes `mk (I i) (x i)` to the class of `x`. -/
@[simp]
theorem piQuotRingEquiv_symm_mk (x : ∀ i, R i) :
    (piQuotRingEquiv I).symm (fun i ↦ Ideal.Quotient.mk (I i) (x i)) =
      Ideal.Quotient.mk (Ideal.pi I) x :=
  (piQuotRingEquiv I).symm_apply_eq.mpr (rfl)

end Ring

section CommRing

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

/-- The quotient of a product of commutative rings by a principal ideal `(d)` splits as the product
of the factorwise principal quotients `R i ⧸ (d i)`. -/
noncomputable def quotientSpanSingletonPiEquiv (d : ∀ i, R i) :
    ((∀ i, R i) ⧸ Ideal.span {d}) ≃+* ∀ i, R i ⧸ Ideal.span {d i} :=
  (Ideal.quotEquivOfEq Ideal.pi_span.symm).trans (piQuotRingEquiv fun i ↦ Ideal.span {d i})

/-- `quotientSpanSingletonPiEquiv d` sends the class of `x` to `fun i ↦ mk (span {d i}) (x i)`. -/
@[simp]
theorem quotientSpanSingletonPiEquiv_mk (d x : ∀ i, R i) :
    quotientSpanSingletonPiEquiv d (Ideal.Quotient.mk (Ideal.span {d}) x) =
      fun i ↦ Ideal.Quotient.mk (Ideal.span {d i}) (x i) :=
  (rfl)

/-- `(quotientSpanSingletonPiEquiv d).symm` sends `fun i ↦ mk (span {d i}) (x i)` to `mk (d) x`. -/
@[simp]
theorem quotientSpanSingletonPiEquiv_symm_mk (d x : ∀ i, R i) :
    (quotientSpanSingletonPiEquiv d).symm
        (fun i ↦ Ideal.Quotient.mk (Ideal.span {d i}) (x i)) =
      Ideal.Quotient.mk (Ideal.span {d}) x :=
  (quotientSpanSingletonPiEquiv d).symm_apply_eq.mpr (rfl)

end CommRing

end Ideal

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Ideal.Operations.Pi

/-!
# Componentwise quotient maps of products

For a family of `R₁`-algebras `A j` and two-sided ideals `I j ≤ J j` of `A j`, the quotient maps
`A j ⧸ I j → A j ⧸ J j` assemble into an `R₁`-algebra map `∏ j, A j ⧸ I j → ∏ j, A j ⧸ J j`,
which is surjective. This is the product version of Mathlib's `Ideal.Quotient.factorₐ`.

For ideals `I i` of a ring `A` and exponents `n i`, the factors of `∏ i, A ⧸ I i ^ n i` with
`n i = 0` are zero, so restricting to the factors with `n i ≠ 0` is a linear bijection.

For a two-sided ideal `J` of a ring `R` and an index type `ι`, the coordinatewise reduction map
`Ideal.quotPiSMulTopToPiQuot J ι : ((ι → R) ⧸ (J • ⊤)) →ₗ[R] (ι → R ⧸ J)` is always surjective.
When `R` is commutative and `J` is finitely generated (`J.FG`), `J` commutes with arbitrary
products of modules (`Ideal.FG.smul_top_pi_eq_pi`), so `Ideal.quotPiSMulTopToPiQuot J ι` is
injective and upgrades to a linear equivalence `Ideal.FG.quotPiSMulTopEquiv`.

## Main declarations

* `TauCeti.Ideal.Quotient.piFactorₐ`: the componentwise quotient map.
* `TauCeti.Ideal.Quotient.piFactorₐ_surjective`: it is surjective.
* `TauCeti.Ideal.Quotient.bijective_pi_restrict_pow`: dropping the factors `A ⧸ I ^ 0 = 0` from
  `∏ i, A ⧸ I i ^ n i` is a linear bijection.
* `Ideal.quotPiSMulTopToPiQuot`: the canonical surjective `R`-linear map
  `((ι → R) ⧸ (J • ⊤)) →ₗ[R] (ι → R ⧸ J)`.
* `Ideal.FG.quotPiSMulTopToPiQuot_injective`, `Ideal.FG.quotPiSMulTopToPiQuot_bijective`,
  `Ideal.FG.quotPiSMulTopEquiv`: for a finitely generated ideal `J` of a commutative ring `R`,
  `J.quotPiSMulTopToPiQuot ι` is a linear equivalence.
-/

public section

namespace TauCeti

namespace Ideal.Quotient

section piFactorₐ

variable (R₁ : Type*) {ι : Type*} {A : ι → Type*} [CommSemiring R₁] [∀ j, Ring (A j)]
  [∀ j, Algebra R₁ (A j)] {I J : (j : ι) → Ideal (A j)} [∀ j, (I j).IsTwoSided]
  [∀ j, (J j).IsTwoSided]

/-- The componentwise quotient map `∏ j, A j ⧸ I j → ∏ j, A j ⧸ J j` for ideals `I j ≤ J j`. -/
def piFactorₐ (hle : ∀ j, I j ≤ J j) : ((j : ι) → A j ⧸ I j) →ₐ[R₁] ((j : ι) → A j ⧸ J j) :=
  AlgHom.pi fun j ↦ (Ideal.Quotient.factorₐ R₁ (hle j)).comp (Pi.evalAlgHom R₁ _ j)

/-- Each component of `piFactorₐ` is the quotient map `A j ⧸ I j → A j ⧸ J j`. -/
@[simp]
theorem piFactorₐ_apply (hle : ∀ j, I j ≤ J j) (x : (j : ι) → A j ⧸ I j) (j : ι) :
    piFactorₐ R₁ hle x j = Ideal.Quotient.factor (hle j) (x j) :=
  (rfl)

/-- The componentwise quotient map is surjective. -/
theorem piFactorₐ_surjective (hle : ∀ j, I j ≤ J j) :
    Function.Surjective (piFactorₐ R₁ hle) :=
  -- `piFactorₐ R₁ hle` is definitionally `Pi.map` of the factor maps, as in `piFactorₐ_apply`.
  Function.Surjective.piMap fun j ↦ Ideal.Quotient.factor_surjective (hle j)

end piFactorₐ

/-- Dropping the factors with exponent zero from `∏ᵢ A ⧸ Iᵢ ^ nᵢ` is bijective, as those factors
are `A ⧸ A = 0`. -/
theorem bijective_pi_restrict_pow {A ι : Type*} [Ring A] (I : ι → Ideal A) (n : ι → ℕ) :
    Function.Bijective (LinearMap.pi fun y : {i // n i ≠ 0} ↦ LinearMap.proj y.val :
      (∀ i, A ⧸ I i ^ n i) →ₗ[A] ∀ y : {i // n i ≠ 0}, A ⧸ I y ^ n y) := by
  classical
  refine ⟨fun x x' hxx' ↦ funext fun i ↦ ?_, fun y ↦ ?_⟩
  · by_cases hi : n i = 0
    · have : Subsingleton (A ⧸ I i ^ n i) := Ideal.Quotient.subsingleton_iff.mpr (by simp [hi])
      exact Subsingleton.elim _ _
    · exact congr_fun hxx' ⟨i, hi⟩
  · refine ⟨fun i ↦ if hi : n i = 0 then 0 else y ⟨i, hi⟩, funext fun i ↦ ?_⟩
    simp only [LinearMap.pi_apply, LinearMap.proj_apply, i.property, ↓reduceDIte]

end Ideal.Quotient

end TauCeti

namespace Ideal

section QuotPiSMulTop

section Ring

variable {R : Type*} [Ring R] (J : Ideal R) [J.IsTwoSided]

/-- Coordinatewise reduction modulo a two-sided ideal `J` on a product `ι → R`, factored through
`(ι → R) ⧸ (J • ⊤)`. -/
def quotPiSMulTopToPiQuot (ι : Type*) :
    ((ι → R) ⧸ (J • (⊤ : Submodule R (ι → R)))) →ₗ[R] (ι → R ⧸ J) :=
  (J • (⊤ : Submodule R (ι → R))).liftQ
    (LinearMap.pi fun i ↦ J.mkQ.comp (LinearMap.proj i)) <| by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker]
      ext i
      rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.smul_apply,
        smul_eq_mul, Submodule.mkQ_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Ideal.IsTwoSided.mul_mem_of_left (x i) hr

/-- Evaluating `Ideal.quotPiSMulTopToPiQuot` on `Submodule.Quotient.mk x` reduces each coordinate
modulo `J`. -/
@[simp, grind =]
theorem quotPiSMulTopToPiQuot_mk {ι : Type*} (x : ι → R) (i : ι) :
    J.quotPiSMulTopToPiQuot ι (Submodule.Quotient.mk x) i = Ideal.Quotient.mk J (x i) := by
  rw [quotPiSMulTopToPiQuot, Submodule.liftQ_apply, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk]

/-- `Ideal.quotPiSMulTopToPiQuot J ι` is always surjective. -/
theorem quotPiSMulTopToPiQuot_surjective (ι : Type*) :
    Function.Surjective (J.quotPiSMulTopToPiQuot ι) := fun y ↦ by
  choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
  exact ⟨Submodule.Quotient.mk x, funext fun i ↦ by simp [hx i]⟩

end Ring

section FG

variable {R : Type*} [CommRing R] {J : Ideal R} (hJ : J.FG)
include hJ

/-- For a finitely generated ideal `J` of a commutative ring `R`, `Ideal.quotPiSMulTopToPiQuot J ι`
is injective. -/
theorem FG.quotPiSMulTopToPiQuot_injective (ι : Type*) :
    Function.Injective (J.quotPiSMulTopToPiQuot ι) := by
  refine LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ fun x hx ↦ ?_)
  rw [hJ.smul_top_pi_self_eq_pi]
  intro i _
  exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using congr_fun (LinearMap.mem_ker.mp hx) i)

/-- For a finitely generated ideal `J` of a commutative ring `R`, `Ideal.quotPiSMulTopToPiQuot J ι`
is bijective. -/
theorem FG.quotPiSMulTopToPiQuot_bijective (ι : Type*) :
    Function.Bijective (J.quotPiSMulTopToPiQuot ι) :=
  ⟨hJ.quotPiSMulTopToPiQuot_injective ι, J.quotPiSMulTopToPiQuot_surjective ι⟩

/-- For a finitely generated ideal `J` of a commutative ring `R`, the canonical `R`-linear
equivalence `((ι → R) ⧸ (J • ⊤)) ≃ₗ[R] (ι → R ⧸ J)`. -/
noncomputable def FG.quotPiSMulTopEquiv (ι : Type*) :
    ((ι → R) ⧸ (J • (⊤ : Submodule R (ι → R)))) ≃ₗ[R] (ι → R ⧸ J) :=
  LinearEquiv.ofBijective (J.quotPiSMulTopToPiQuot ι) (hJ.quotPiSMulTopToPiQuot_bijective ι)

/-- Underlying function of `Ideal.FG.quotPiSMulTopEquiv`. -/
@[simp, grind =]
theorem FG.quotPiSMulTopEquiv_apply {ι : Type*}
    (q : (ι → R) ⧸ (J • (⊤ : Submodule R (ι → R)))) :
    hJ.quotPiSMulTopEquiv ι q = J.quotPiSMulTopToPiQuot ι q :=
  LinearEquiv.ofBijective_apply _ q

/-- Right-inverse identity for `Ideal.FG.quotPiSMulTopEquiv`. -/
@[simp, grind =]
theorem FG.quotPiSMulTopToPiQuot_quotPiSMulTopEquiv_symm {ι : Type*} (y : ι → R ⧸ J) :
    J.quotPiSMulTopToPiQuot ι ((hJ.quotPiSMulTopEquiv ι).symm y) = y := by
  rw [← hJ.quotPiSMulTopEquiv_apply, LinearEquiv.apply_symm_apply]

end FG

end QuotPiSMulTop

end Ideal

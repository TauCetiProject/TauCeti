/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# Formal exponential sums

A formal exponential sum with coefficients and exponents in a commutative ring `K` is an element
`x = ∑ δ_γ [γ]` of the additive monoid algebra `K[K]`, where `[γ] * [γ'] = [γ + γ']`. This file
develops the two operations on such sums used in the Hermite–Lindemann proof of the
Lindemann–Weierstrass theorem.

* `expEval K : K[K] →ₐ[K] ℂ` evaluates a formal sum at the exponential function,
  `∑ δ_γ [γ] ↦ ∑ δ_γ exp γ`, for any `K`-algebra structure on `ℂ`. It is the algebra lift of the
  exponential character, so it is multiplicative by construction. For an intermediate field
  `L` of `ℂ / ℚ` the Lindemann–Weierstrass theorem states that `expEval L` is injective when `L`
  consists of algebraic numbers; it is not injective for `L = ⊤`, since `exp (2πi) = exp 0`.
* `galConj τ : K[K] ≃ₐ[F] K[K]` is the conjugation `∑ δ_γ [γ] ↦ ∑ τ(δ_γ) [τ γ]` by an
  automorphism `τ` of the `F`-algebra `K`, acting simultaneously on coefficients and exponents.
  It is a group homomorphism in `τ`, and a sum is fixed by every `galConj τ` exactly when each
  `τ` sends its coefficient at `γ` to its coefficient at `τ γ` (`forall_galConj_eq_iff`).
  Taking the product of all conjugates produces fixed sums (`galConj_prod_galConj`), which is how
  the proof reduces the general theorem to Galois-invariant exponential relations.

The evaluation is not Galois-equivariant: `expEval` of `galConj τ x` is in general a different
complex number from `expEval x`.

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.2, Theorem 4.11.
* Y. Zhao, formalization of the Lindemann–Weierstrass theorem in Lean, `Basic.lean`, the proof of
  `algebraicIndependent_exp`, which works with exponential sums in `AddMonoidAlgebra`.
-/

public section

open AddMonoidAlgebra Complex

namespace TauCeti.LindemannWeierstrass

section galConj

variable {F K : Type*} [CommSemiring F] [Semiring K] [Algebra F K]

/-- Conjugation of formal exponential sums `∑ δ_γ [γ] ↦ ∑ τ(δ_γ) [τ γ]` by an automorphism `τ`
of the `F`-algebra `K`, acting on coefficients and exponents simultaneously. -/
noncomputable def galConj (τ : K ≃ₐ[F] K) : K[K] ≃ₐ[F] K[K] :=
  (domCongr F K τ.toAddEquiv).trans (mapAlgEquiv F K τ)

/-- The coefficient of `galConj τ x` at `γ` is the conjugate of the coefficient of `x` at
`τ⁻¹ γ`. -/
@[simp]
theorem coeff_galConj (τ : K ≃ₐ[F] K) (x : K[K]) (γ : K) :
    (galConj τ x).coeff γ = τ (x.coeff (τ.symm γ)) := by
  simp [galConj]

/-- The coefficient of `galConj τ x` at `τ γ` is the conjugate of the coefficient of `x`
at `γ`. -/
theorem coeff_galConj_apply (τ : K ≃ₐ[F] K) (x : K[K]) (γ : K) :
    (galConj τ x).coeff (τ γ) = τ (x.coeff γ) := by
  simp

/-- Conjugation sends the monomial `δ [γ]` to `τ(δ) [τ γ]`. -/
@[simp]
theorem galConj_single (τ : K ≃ₐ[F] K) (γ δ : K) :
    galConj τ (single γ δ) = single (τ γ) (τ δ) := by
  simp [galConj]

/-- Conjugation by the identity is the identity. -/
@[simp]
theorem galConj_refl : galConj (AlgEquiv.refl : K ≃ₐ[F] K) = AlgEquiv.refl := by
  ext
  simp

/-- Conjugation is compatible with composition of automorphisms. -/
@[simp]
theorem galConj_trans (τ σ : K ≃ₐ[F] K) :
    galConj (τ.trans σ) = (galConj τ).trans (galConj σ) := by
  ext
  simp

/-- The inverse of conjugation by `τ` is conjugation by `τ⁻¹`. -/
@[simp]
theorem galConj_symm (τ : K ≃ₐ[F] K) : (galConj τ).symm = galConj τ.symm := by
  ext x : 1
  rw [AlgEquiv.symm_apply_eq]
  ext
  simp

/-- Conjugation moves the support of a formal sum by `τ`. -/
@[simp]
theorem support_galConj (τ : K ≃ₐ[F] K) (x : K[K]) :
    (galConj τ x).coeff.support = x.coeff.support.map (τ : K ≃ K).toEmbedding := by
  ext γ
  simp [Finset.mem_map_equiv]

/-- A formal sum is fixed by every conjugation exactly when each automorphism maps its
coefficient at `γ` to its coefficient at `τ γ`. -/
theorem forall_galConj_eq_iff {x : K[K]} :
    (∀ τ : K ≃ₐ[F] K, galConj τ x = x) ↔
      ∀ (τ : K ≃ₐ[F] K) (γ : K), x.coeff (τ γ) = τ (x.coeff γ) := by
  refine ⟨fun h τ γ ↦ ?_, fun h τ ↦ ?_⟩
  · rw [← coeff_galConj_apply, h]
  · ext γ
    rw [coeff_galConj, ← h, AlgEquiv.apply_symm_apply]

end galConj

section prod

variable {F K : Type*} [CommSemiring F] [CommSemiring K] [Algebra F K] [Fintype (K ≃ₐ[F] K)]

/-- The product of all conjugates of a formal sum is fixed by every conjugation. -/
theorem galConj_prod_galConj (σ : K ≃ₐ[F] K) (x : K[K]) :
    galConj σ (∏ τ : K ≃ₐ[F] K, galConj τ x) = ∏ τ : K ≃ₐ[F] K, galConj τ x := by
  simp_rw [map_prod, ← AlgEquiv.trans_apply, ← galConj_trans, ← AlgEquiv.aut_mul]
  exact Equiv.prod_comp (Equiv.mulLeft σ) fun τ ↦ galConj τ x

end prod

section expEval

variable (K : Type*) [CommSemiring K] [Algebra K ℂ]

/-- Evaluation of formal exponential sums at the exponential function,
`∑ δ_γ [γ] ↦ ∑ δ_γ exp γ`. -/
noncomputable def expEval : K[K] →ₐ[K] ℂ :=
  lift K ℂ K
    (expMonoidHom.comp (AddMonoidHom.toMultiplicative (algebraMap K ℂ).toAddMonoidHom))

variable {K}

/-- The exponential evaluation of the monomial `c [γ]` is `c * exp γ`. -/
@[simp]
theorem expEval_single (γ c : K) :
    expEval K (single γ c) = algebraMap K ℂ c * exp (algebraMap K ℂ γ) := by
  simp [expEval, Algebra.smul_def, expMonoidHom]

/-- The exponential evaluation of `∑ δ_γ [γ]` is the finite sum `∑ δ_γ exp γ`. -/
theorem expEval_apply (x : K[K]) :
    expEval K x =
      ∑ γ ∈ x.coeff.support, algebraMap K ℂ (x.coeff γ) * exp (algebraMap K ℂ γ) := by
  simp [expEval, lift_apply', Finsupp.sum, expMonoidHom]

end expEval

end TauCeti.LindemannWeierstrass

end

/-! ### Examples -/

open AddMonoidAlgebra Complex

namespace TauCeti.LindemannWeierstrass

variable {L : IntermediateField ℚ ℂ}

/- The exponential evaluation of a constant is the constant. -/
example (c : L) : expEval L (single 0 c) = (c : ℂ) := by
  simp

/- Evaluation is multiplicative: `[γ] [γ'] = [γ + γ']` evaluates to `exp γ exp γ'`. -/
example (γ γ' : L) :
    expEval L (single γ 1 * single γ' 1) = exp (γ : ℂ) * exp (γ' : ℂ) ∧
      expEval L (single γ 1 * single γ' 1) = exp ((γ : ℂ) + γ') := by
  simp [single_mul_single, exp_add]

/- `expEval` is not injective on all of `ℂ`: the formal sum `[0] - [2πi]` is nonzero, but its
exponential evaluation vanishes. -/
example :
    (single (0 : (⊤ : IntermediateField ℚ ℂ)) (1 : (⊤ : IntermediateField ℚ ℂ)) -
        single ⟨2 * (Real.pi : ℂ) * I, trivial⟩ 1) ≠ 0 ∧
      expEval (⊤ : IntermediateField ℚ ℂ) (single (0 : (⊤ : IntermediateField ℚ ℂ))
        (1 : (⊤ : IntermediateField ℚ ℂ)) - single ⟨2 * (Real.pi : ℂ) * I, trivial⟩ 1) = 0 := by
  have h : (⟨2 * (Real.pi : ℂ) * I, trivial⟩ : (⊤ : IntermediateField ℚ ℂ)) ≠ 0 := by
    rw [ne_eq, Subtype.ext_iff]
    simp [Real.pi_ne_zero, I_ne_zero]
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · have := congrArg (fun y ↦ y.coeff 0) h0
    simp [h.symm] at this
  · simp [exp_two_pi_mul_I]

/- Conjugation fixes rational constants. -/
example (τ : L ≃ₐ[ℚ] L) (q : ℚ) : galConj τ (single (0 : L) (q : L)) = single 0 (q : L) := by
  simp

/- Complex conjugation, when it restricts to `L`, sends `i [i]` to `-i [-i]`. -/
example (hI : I ∈ L) (τ : L ≃ₐ[ℚ] L) (hτ : τ ⟨I, hI⟩ = -⟨I, hI⟩) :
    galConj τ (single ⟨I, hI⟩ ⟨I, hI⟩) = single (-⟨I, hI⟩) (-⟨I, hI⟩) := by
  simp [hτ]

/- An automorphism negating `s` fixes the symmetric sum `[s] + [-s]`. -/
example (s : L) (τ : L ≃ₐ[ℚ] L) (hτ : τ s = -s) :
    galConj τ (single s 1 + single (-s) 1) = single s 1 + single (-s) 1 := by
  simp [hτ, add_comm]

/- Exponential evaluation is not Galois-equivariant: conjugating `[√2]` to `[-√2]` changes its
value from `exp √2` to `exp (-√2)`. -/
example (s : L) (hs : (s : ℂ) = Real.sqrt 2) (τ : L ≃ₐ[ℚ] L) (hτ : τ s = -s) :
    expEval L (galConj τ (single s 1)) = exp (-(Real.sqrt 2 : ℂ)) ∧
      exp (-(Real.sqrt 2 : ℂ)) ≠ exp (Real.sqrt 2 : ℂ) ∧
      exp (Real.sqrt 2 : ℂ) = expEval L (single s 1) := by
  refine ⟨by simp [hτ, hs], ?_, by simp [hs]⟩
  rw [← ofReal_neg, ← ofReal_exp, ← ofReal_exp, ne_eq, ofReal_inj, Real.exp_eq_exp]
  have : 0 < Real.sqrt 2 := by positivity
  linarith

end TauCeti.LindemannWeierstrass

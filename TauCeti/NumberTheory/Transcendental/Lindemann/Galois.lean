/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.NumberTheory.Transcendental.Lindemann.ExpSum

import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.NumberTheory.NumberField.House
import TauCeti.NumberTheory.Transcendental.Lindemann.AuxValue

/-!
# The Lindemann–Weierstrass theorem over a Galois number field

Let `K` be a number field, Galois over `ℚ`, together with an embedding of `K` into `ℂ` (an
`Algebra K ℂ` structure). A formal exponential sum `x = ∑ δ_γ [γ] ∈ K[K]` evaluates to the complex
number `expEval K x = ∑ δ_γ exp γ`. This file proves that this evaluation is injective: distinct
elements of `K` have `K`-linearly independent exponentials.

* `expEval_ne_zero_of_forall_galConj_eq`: the weak Lindemann–Weierstrass theorem. A nonzero
  formal sum fixed by the conjugations `galConj τ`, `τ ∈ Gal(K/ℚ)`, does not evaluate to `0`.
* `expEval_injective`: the evaluation `expEval K : K[K] →ₐ[K] ℂ` is injective. The product of the
  conjugates of a formal sum `x` is Galois-invariant, it is nonzero when `x` is since `K[K]` is a
  domain, and its evaluation vanishes when that of `x` does.

The weak theorem follows Hermite's argument. After clearing denominators, the coefficients `δ_γ`
are algebraic integers and `l γ` is an algebraic integer for a positive integer `l` and every
`γ` in the support `S` of `x`. Fix `γ₀ ∈ S`. For large primes `p` the auxiliary value
`a = auxValue x l p γ₀` is a nonzero algebraic integer (`auxValue_ne_zero`,
`isIntegral_auxValue`), so some complex conjugate of `a` has absolute value at least `1`
(`NumberField.exists_conjugate_one_le_norm`). Since `K / ℚ` is normal and `x` is
Galois-invariant, the conjugates of `a` are the auxiliary values at the conjugates of `γ₀`
(`auxValue_galConj`), and if `expEval K x = 0` these all have absolute value less than `1` for
large `p` (`eventually_norm_auxValue_lt_one`).

## References

* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 4, §4.2, Theorem 4.11 and its proof,
  and the deduction of Theorem 4.8 from it.
* Y. Zhao, formalization of the Lindemann–Weierstrass theorem in Lean, `Basic.lean`, which
  reduces to Galois-invariant exponential sums by taking the product of all conjugates.
-/

public section

open AddMonoidAlgebra Filter Finset NumberField

namespace TauCeti.LindemannWeierstrass

variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Algebra K ℂ]

/-- The weak Lindemann–Weierstrass theorem for formal sums with integral coefficients. -/
private theorem expEval_ne_zero_of_forall_galConj_eq_of_isIntegral {x : K[K]} (hx : x ≠ 0)
    (hfix : ∀ τ : K ≃ₐ[ℚ] K, galConj τ x = x) (hint : ∀ γ, IsIntegral ℤ (x.coeff γ)) :
    expEval K x ≠ 0 := by
  classical
  intro h0
  set S := x.coeff.support
  obtain ⟨γ₀, hγ₀⟩ : S.Nonempty := Finsupp.support_nonempty_iff.2 (coeff_eq_zero.not.2 hx)
  -- A positive integer `l` such that `l γ` is an algebraic integer for every `γ ∈ S`.
  obtain ⟨m, hm, hmS⟩ := exists_integral_multiples ℤ ℚ S
  have hl : ∀ γ ∈ S, IsIntegral ℤ ((m.natAbs : K) * γ) := fun γ hγ ↦ by
    rw [← Int.cast_natCast, Int.natCast_natAbs, ← zsmul_eq_mul]
    rcases abs_choice m with h | h <;> rw [h]
    · exact hmS γ hγ
    · simpa only [neg_smul] using (hmS γ hγ).neg
  -- The conjugates of `γ₀` lie in `S`, since `x` is Galois-invariant.
  have hτS (τ : K ≃ₐ[ℚ] K) : τ γ₀ ∈ S := by
    have h : τ γ₀ ∈ (galConj τ x).coeff.support := by
      rw [support_galConj]
      exact mem_map_of_mem _ hγ₀
    rwa [hfix] at h
  -- Choose a large prime `p`, beyond the bound of `auxValue_ne_zero` and the threshold after
  -- which all the auxiliary values have absolute value less than `1`.
  set N := |Algebra.norm ℚ (x.coeff γ₀ *
    ((m.natAbs : K) ^ #S * ∏ γ' ∈ S.erase γ₀, (γ₀ - γ')))|
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.1 (eventually_norm_auxValue_lt_one h0 m.natAbs)
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max p₀ (⌈N⌉₊ + 1))
  have hpN : N < p := by
    have := Nat.le_ceil N
    have : ((⌈N⌉₊ + 1 : ℕ) : ℚ) ≤ p := by exact_mod_cast le_of_max_le_right hp_ge
    push_cast at this
    linarith
  set a := auxValue x m.natAbs p γ₀
  have ha0 : a ≠ 0 := auxValue_ne_zero hγ₀ hint (Int.natAbs_ne_zero.2 hm) hl hp hpN
  -- Some complex embedding `σ` of the nonzero algebraic integer `a` has absolute value at least
  -- `1`. Since `K / ℚ` is normal, `σ` is the fixed embedding precomposed with an automorphism `τ`,
  -- and `τ a` is the auxiliary value at `τ γ₀`, of absolute value less than `1`.
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm (K := K)
    (α := ⟨a, isIntegral_auxValue hγ₀ hint hl⟩) fun h ↦ ha0 congr($h.1)
  set τ := σ.toRatAlgHom.restrictNormal' K
  have hτ : σ a = algebraMap K ℂ (auxValue x m.natAbs p (τ γ₀)) := by
    rw [← hfix τ, auxValue_galConj]
    simpa only [τ, AlgHom.restrictNormal', AlgEquiv.ofBijective_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingHom.toRatAlgHom_apply] using
      (σ.toRatAlgHom.restrictNormal_commutes K a).symm
  exact (hp₀ p (le_of_max_le_left hp_ge) _ (hτS τ)).not_ge (hτ ▸ hσ)

/-- **The weak Lindemann–Weierstrass theorem.** Let `K` be a number field, Galois over `ℚ` and
embedded in `ℂ`. If a nonzero formal exponential sum `x = ∑ δ_γ [γ] ∈ K[K]` is fixed by the
conjugation `galConj τ` for every `τ ∈ Gal(K/ℚ)`, then `∑ δ_γ exp γ ≠ 0`. -/
theorem expEval_ne_zero_of_forall_galConj_eq {x : K[K]} (hx : x ≠ 0)
    (hfix : ∀ τ : K ≃ₐ[ℚ] K, galConj τ x = x) : expEval K x ≠ 0 := by
  classical
  -- Multiply `x` by a nonzero integer `m` clearing the denominators of its coefficients.
  obtain ⟨m, hm, hm'⟩ := exists_integral_multiples ℤ ℚ (x.coeff.support.image x.coeff)
  have hint (γ : K) : IsIntegral ℤ (m • x.coeff γ) := by
    by_cases hγ : γ ∈ x.coeff.support
    · exact hm' _ (mem_image_of_mem _ hγ)
    · rw [Finsupp.notMem_support_iff.1 hγ, smul_zero]
      exact isIntegral_zero
  have hmx : m • x ≠ 0 := smul_ne_zero hm hx
  have h := expEval_ne_zero_of_forall_galConj_eq_of_isIntegral hmx
    (fun τ ↦ by rw [map_zsmul, hfix]) (fun γ ↦ by simpa only [coeff_smul_apply] using hint γ)
  rw [map_zsmul] at h
  exact right_ne_zero_of_smul h

/-- **The Lindemann–Weierstrass theorem over a Galois number field.** Let `K` be a number field,
Galois over `ℚ` and embedded in `ℂ`. Then the exponential evaluation
`∑ δ_γ [γ] ↦ ∑ δ_γ exp γ` of formal sums in `K[K]` is injective: the exponentials of distinct
elements of `K` are linearly independent over `K`. -/
theorem expEval_injective : Function.Injective (expEval K) := by
  refine (injective_iff_map_eq_zero _).2 fun x h0 ↦ by_contra fun hx ↦ ?_
  -- The product of the conjugates of `x` is a nonzero Galois-invariant sum with value `0`.
  refine expEval_ne_zero_of_forall_galConj_eq (x := ∏ τ : K ≃ₐ[ℚ] K, galConj τ x)
    (prod_ne_zero_iff.2 fun τ _ ↦ (map_ne_zero_iff _ (galConj τ).injective).2 hx)
    (fun σ ↦ galConj_prod_galConj σ x) ?_
  rw [map_prod]
  have h1 : galConj (1 : K ≃ₐ[ℚ] K) x = x := by
    rw [AlgEquiv.aut_one, galConj_refl, AlgEquiv.coe_refl, id_eq]
  exact prod_eq_zero (mem_univ 1) (by rwa [h1])

end TauCeti.LindemannWeierstrass

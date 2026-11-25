/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Henselian.Basic

/-!
# Henselian pairs by roots near `1`

A pair `(R, I)` is Henselian if and only if `I` lies in the Jacobson radical of `R` and, for
every `n ≥ 1`, every polynomial

  `Xⁿ (X - 1) + aₙ Xⁿ + ⋯ + a₁ X + a₀`  with all `aᵢ ∈ I`

has a root in `1 + I`. This is condition (5) of the Stacks Project's characterisation of Henselian
pairs, which it attributes to Gabber. It tests only one family of polynomials, all with the same
reduction `Xⁿ (X - 1)` modulo `I` and the same simple root `1`, whereas Mathlib's `HenselianRing`
asks for lifts of every simple root of every monic polynomial.

## Main results

* `TauCeti.HenselianRing.exists_isRoot_X_pow_mul_X_sub_one_add`: over a Henselian pair `(R, I)`,
  `Xⁿ (X - 1) + p` has a root in `1 + I` whenever every coefficient of `p` lies in `I`.
* `TauCeti.henselianRing_of_forall_exists_isRoot_X_pow_mul_X_sub_one_add`: if `I` lies in the
  Jacobson radical and these polynomials have roots in `1 + I`, then `(R, I)` is Henselian.
* `TauCeti.henselianRing_iff_forall_exists_isRoot_X_pow_mul_X_sub_one_add`: the equivalence.

## Implementation notes

For the converse, let `a₀` be a simple root of `f` modulo `I`, and let `g = f(X + a₀)` have
coefficients `c₀, c₁, …, c_{m+2}`, so that `c₀ ∈ I` and `c₁` is a unit. Substituting
`X = -c₀ c₁⁻¹ Z` gives `c₀ (1 - Z + ∑ₖ₌₂ cₖ (-c₁⁻¹)ᵏ c₀ᵏ⁻¹ Zᵏ)`; reversing the bracket in degree
`m + 2` gives `X^(m+1) (X - 1) + p` with every coefficient of `p` in `I`. A root `w ∈ 1 + I` of
the reversed polynomial is a unit, and `-c₀ c₁⁻¹ w⁻¹ ∈ I` is a root of `g`. Neither `f` nor `g`
needs to be monic.

## References

* [Stacks Project, Lemma 15.11.6](https://stacks.math.columbia.edu/tag/09XI), condition (5).
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- A polynomial vanishes modulo `I` exactly when all its coefficients lie in `I`. -/
theorem map_mk_eq_zero_iff {p : R[X]} :
    p.map (Ideal.Quotient.mk I) = 0 ↔ ∀ i, p.coeff i ∈ I := by
  refine ⟨fun h i ↦ ?_, fun hp ↦ ?_⟩
  · simpa [Ideal.Quotient.eq_zero_iff_mem] using congrArg (·.coeff i) h
  · ext i
    simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (hp i)

end Polynomial

namespace TauCeti

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- **Roots near `1` over a Henselian pair.** If `(R, I)` is Henselian and every coefficient of `p`
lies in `I`, then `Xⁿ (X - 1) + p` has a root in `1 + I`. No bound on the degree of `p` is
needed. -/
@[stacks 09XI "(1) ⇒ (5)"]
theorem HenselianRing.exists_isRoot_X_pow_mul_X_sub_one_add [HenselianRing R I] (n : ℕ)
    {p : R[X]} (hp : ∀ i, p.coeff i ∈ I) :
    ∃ a : R, (X ^ n * (X - 1) + p).IsRoot a ∧ a - 1 ∈ I := by
  have hp₀ : p.map (Ideal.Quotient.mk I) = 0 := map_mk_eq_zero_iff.mpr hp
  -- Modulo `I` the polynomial is `Xⁿ (X - 1)`, with the simple root `1`.
  refine exists_isRoot_sub_mem _ ?_ ?_
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_map_apply]
    simp [Polynomial.map_add, hp₀]
  · rw [← eval_map_apply, ← derivative_map]
    simp [Polynomial.map_add, hp₀]

/-- **Henselian pairs from roots near `1`.** Let `I` lie in the Jacobson radical of `R`. If for
every `n ≥ 1` and every `p` of degree at most `n` with all coefficients in `I`, the polynomial
`Xⁿ (X - 1) + p` has a root in `1 + I`, then `(R, I)` is Henselian. -/
@[stacks 09XI "(5) ⇒ (1)"]
theorem henselianRing_of_forall_exists_isRoot_X_pow_mul_X_sub_one_add
    (hjac : I ≤ Ring.jacobson R)
    (H : ∀ n : ℕ, 1 ≤ n → ∀ p : R[X], p.natDegree ≤ n → (∀ i, p.coeff i ∈ I) →
      ∃ a : R, (X ^ n * (X - 1) + p).IsRoot a ∧ a - 1 ∈ I) :
    HenselianRing R I where
  jac := hjac
  is_henselian f _ a₀ hfa₀ hunit := by
    have := isLocalHom_of_le_jacobson hjac
    -- Translate the approximate root to `0`: `g = f(X + a₀) = c₀ + c₁ X + ⋯`.
    set g := taylor a₀ f
    set m := g.natDegree
    have hc₀ : g.coeff 0 ∈ I := by rwa [taylor_coeff_zero]
    obtain ⟨v, hvu⟩ : ∃ v, g.coeff 1 * v = 1 := by
      rw [taylor_coeff_one]
      exact (isUnit_of_map_unit (Ideal.Quotient.mk I) _ hunit).exists_right_inv
    -- The reversal of `g(-c₀ v Z) / c₀` in degree `m + 2`.
    set p : R[X] := ∑ i ∈ Finset.range (m + 1),
      C (g.coeff (i + 2) * (-v) ^ (i + 2) * g.coeff 0 ^ (i + 1)) * X ^ (m - i) with hp
    have hpdeg : p.natDegree ≤ m + 1 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ ↦
        (natDegree_C_mul_X_pow_le _ _).trans (by omega)
    have hpI : ∀ j, p.coeff j ∈ I := fun j ↦ by
      rw [hp, finsetSum_coeff]
      refine sum_mem fun i _ ↦ ?_
      rw [coeff_C_mul_X_pow]
      split_ifs
      · exact I.mul_mem_left _ (Ideal.pow_mem_of_mem _ hc₀ _ i.succ_pos)
      · exact I.zero_mem
    obtain ⟨w, hw, hw1⟩ := H (m + 1) (by omega) p hpdeg hpI
    have hwu : IsUnit w := Ideal.isUnit_of_sub_one_mem_jacobson w (hjac hw1)
    obtain ⟨w', hww'⟩ := hwu.exists_right_inv
    -- `b = -c₀ v w⁻¹` is a root of `g`, as `g(b) w^(m+2) = c₀ (w^(m+1) (w - 1) + p(w)) = 0`.
    have hterm : ∀ i ∈ Finset.range (m + 1),
        g.coeff (i + 1 + 1) * (-g.coeff 0 * v * w') ^ (i + 1 + 1) * w ^ (m + 2) =
          g.coeff 0 * (g.coeff (i + 2) * (-v) ^ (i + 2) * g.coeff 0 ^ (i + 1) * w ^ (m - i)) :=
        fun i hi ↦ by
      have hpow : w ^ (m + 2) = w ^ (m - i) * w ^ (i + 2) := by
        rw [← pow_add]; congr 1; have := Finset.mem_range.mp hi; omega
      calc g.coeff (i + 1 + 1) * (-g.coeff 0 * v * w') ^ (i + 1 + 1) * w ^ (m + 2)
          = g.coeff (i + 2) * (-g.coeff 0 * v) ^ (i + 2) * w ^ (m - i) * (w * w') ^ (i + 2) := by
            rw [hpow]; ring
        _ = _ := by rw [hww', one_pow]; ring
    have hgb : g.eval (-g.coeff 0 * v * w') * w ^ (m + 2) =
        g.coeff 0 * (X ^ (m + 1) * (X - 1) + p).eval w := by
      rw [eval_eq_sum_range' (n := m + 3) (by omega), Finset.sum_mul, Finset.sum_range_succ',
        Finset.sum_range_succ', Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      simp only [hp, eval_add, eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_finsetSum,
        eval_C]
      linear_combination (-g.coeff 0 * w' * w ^ (m + 2)) * hvu - (g.coeff 0 * w ^ (m + 1)) * hww'
    refine ⟨-g.coeff 0 * v * w' + a₀, ?_, ?_⟩
    · rw [IsRoot, ← taylor_eval, ← (hwu.pow (m + 2)).mul_left_eq_zero, hgb, hw.eq_zero, mul_zero]
    · rw [add_sub_cancel_right]
      exact I.mul_mem_right _ (I.mul_mem_right _ (I.neg_mem_iff.mpr hc₀))

/-- **Henselian pairs by roots near `1`.** A pair `(R, I)` is Henselian if and only if `I` lies in
the Jacobson radical of `R` and, for every `n ≥ 1`, every polynomial
`Xⁿ (X - 1) + aₙ Xⁿ + ⋯ + a₀` with all `aᵢ ∈ I` has a root in `1 + I`. -/
@[stacks 09XI "(1) ⇔ (5)"]
theorem henselianRing_iff_forall_exists_isRoot_X_pow_mul_X_sub_one_add :
    HenselianRing R I ↔ I ≤ Ring.jacobson R ∧
      ∀ n : ℕ, 1 ≤ n → ∀ p : R[X], p.natDegree ≤ n → (∀ i, p.coeff i ∈ I) →
        ∃ a : R, (X ^ n * (X - 1) + p).IsRoot a ∧ a - 1 ∈ I :=
  ⟨fun _ ↦ ⟨HenselianRing.jac, fun n _ _ _ hp ↦
      HenselianRing.exists_isRoot_X_pow_mul_X_sub_one_add n hp⟩,
    fun ⟨hjac, H⟩ ↦ henselianRing_of_forall_exists_isRoot_X_pow_mul_X_sub_one_add hjac H⟩

end TauCeti

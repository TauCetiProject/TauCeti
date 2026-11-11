/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import TauCeti.Algebra.Polynomial.PowChar

/-!
# `p`-independent pairs

Let `k` be a field of characteristic `p > 0`. Two elements `a, b ∈ k` are `p`-independent when
the monomials `a ^ i * b ^ j` with `i, j < p` are linearly independent over the subfield `k ^ p`
of `p`-th powers; for instance, independent indeterminates `a` and `b` over `𝔽_p`. Equivalently,
`[k ^ p (a, b) : k ^ p] = p ^ 2`.

## Main results

* `TauCeti.IsPIndependentPair`: `a` and `b` are `p`-independent.
* `TauCeti.isPIndependentPair_iff_linearIndependent`: `p`-independence is linear independence of
  the monomials `a ^ i * b ^ j` over the field range of Frobenius.
* `TauCeti.IsPIndependentPair.eq_zero_of_sum_pow_mul_C_eq_zero`: a `p`-independent pair stays
  `p`-independent over the `p`-th powers of `k[X]`.
* `TauCeti.notMem_span_pair_of_pow_eq`: `α ∉ k + k β` for `p`-th roots `α` of `a` and `β` of `b`
  in an extension of `k`.

## References

* S. Lang, *Algebra*, 3rd ed., GTM 211, Springer, 2002, Chapter VIII, Section 4, on separable
  and regular extensions.
-/

public section

open Finset

namespace TauCeti

variable {k : Type*} [Field k] {p : ℕ} {a b : k}

variable (p) in
/-- `a` and `b` are `p`-independent: the monomials `a ^ i * b ^ j` with `i, j < p` are linearly
independent over the subfield of `p`-th powers of `k`. -/
def IsPIndependentPair (a b : k) : Prop :=
  ∀ c : ℕ → ℕ → k,
    ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0 → ∀ i < p, ∀ j < p, c i j = 0

/-- Unfolding `IsPIndependentPair`: every vanishing combination `∑ cᵢⱼ ^ p a ^ i b ^ j` with
`i, j < p` has zero coefficients. -/
theorem isPIndependentPair_iff : IsPIndependentPair p a b ↔ ∀ c : ℕ → ℕ → k,
    ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0 → ∀ i < p, ∀ j < p, c i j = 0 :=
  Iff.rfl

/-- `a` and `b` are `p`-independent exactly when the monomials `a ^ i * b ^ j` with `i, j < p`
are linearly independent over the field range `k ^ p` of Frobenius. -/
theorem isPIndependentPair_iff_linearIndependent [ExpChar k p] :
    IsPIndependentPair p a b ↔ LinearIndependent (frobenius k p).fieldRange
      (fun ij : Fin p × Fin p ↦ a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ)) := by
  have hp : p ≠ 0 := (expChar_pos k p).ne'
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg ij
    choose c hc using fun ij ↦ RingHom.mem_fieldRange.mp (g ij).2
    have := h (fun i j ↦ if h : i < p ∧ j < p then c (⟨i, h.1⟩, ⟨j, h.2⟩) else 0) ?_
      ij.1 ij.1.2 ij.2 ij.2.2
    · rw [Subtype.ext_iff, ← hc]
      simpa using this
    · rw [Fintype.sum_prod_type] at hg
      simpa [sum_range, Subfield.smul_def, ← hc, frobenius_def, mul_assoc] using hg
  · intro h c hc i hi j hj
    have := h (fun ij ↦ ⟨c ij.1 ij.2 ^ p, c ij.1 ij.2, frobenius_def ..⟩) ?_ (⟨i, hi⟩, ⟨j, hj⟩)
    · simpa [Subtype.ext_iff, hp] using this
    · rw [Fintype.sum_prod_type]
      simpa [sum_range, Subfield.smul_def, mul_assoc] using hc

/-- A vanishing combination `∑ cᵢⱼ ^ p a ^ i b ^ j` of a `p`-independent pair has all its
coefficients `cᵢⱼ` with `i, j < p` equal to zero. -/
theorem IsPIndependentPair.eq_zero (hab : IsPIndependentPair p a b) {c : ℕ → ℕ → k}
    (h : ∑ i ∈ range p, ∑ j ∈ range p, c i j ^ p * a ^ i * b ^ j = 0) {i j : ℕ} (hi : i < p)
    (hj : j < p) : c i j = 0 :=
  hab c h i hi j hj

open Polynomial in
/-- `p`-independence of `a` and `b` over `k ^ p` gives `p`-independence over `k[X] ^ p`: a
vanishing combination `∑ Pᵢⱼ ^ p a ^ i b ^ j` with polynomial `Pᵢⱼ` has `Pᵢⱼ = 0` for `i, j < p`. -/
theorem IsPIndependentPair.eq_zero_of_sum_pow_mul_C_eq_zero [ExpChar k p]
    (hab : IsPIndependentPair p a b) {P : ℕ → ℕ → k[X]}
    (h : ∑ i ∈ range p, ∑ j ∈ range p, P i j ^ p * C (a ^ i * b ^ j) = 0) {i j : ℕ} (hi : i < p)
    (hj : j < p) : P i j = 0 := by
  ext n
  have hn := congrArg (coeff · (p * n)) h
  simp only [finsetSum_coeff, coeff_mul_C, coeff_pow_char_mul, coeff_zero] at hn
  exact hab.eq_zero (c := fun i j ↦ (P i j).coeff n) (by simpa only [mul_assoc] using hn) hi hj

/-- `α ∉ k + k β` when `α` and `β` are `p`-th roots of a `p`-independent pair `a, b`. -/
theorem notMem_span_pair_of_pow_eq [hp : Fact p.Prime] [CharP k p]
    (hab : IsPIndependentPair p a b) {K : Type*} [Field K] [Algebra k K] {α β : K}
    (hα : α ^ p = algebraMap k K a) (hβ : β ^ p = algebraMap k K b) :
    α ∉ Submodule.span k {1, β} := by
  have := charP_of_injective_algebraMap (algebraMap k K).injective p
  rw [Submodule.mem_span_pair]
  rintro ⟨c₀, c₂, h⟩
  have hpow := congrArg (· ^ p) h
  simp only [add_pow_char, Algebra.smul_def, mul_pow, mul_one, hα, hβ, ← map_pow,
    ← map_mul, ← map_add] at hpow
  have := hab.eq_zero (c := fun i j ↦ if i = 0 ∧ j = 0 then c₀ else if i = 1 ∧ j = 0 then -1 else
      if i = 0 ∧ j = 1 then c₂ else 0) ?_ hp.out.one_lt hp.out.pos
  · simp at this
  · have hpa := (algebraMap k K).injective hpow
    have hp0 : p ≠ 0 := hp.out.ne_zero
    have h0 : 0 ∈ range p := mem_range.mpr hp.out.pos
    have h1 : 1 ∈ range p := mem_range.mpr hp.out.one_lt
    rw [sum_eq_add 0 1 zero_ne_one (fun i _ hi ↦ sum_eq_zero fun j _ ↦ by
        simp [hi.1, hi.2, zero_pow hp0]) (absurd h0) (absurd h1),
      sum_eq_add 0 1 zero_ne_one (fun j _ hj ↦ by simp [hj.1, hj.2, zero_pow hp0])
        (absurd h0) (absurd h1),
      sum_eq_single 0 (fun j _ hj ↦ by simp [hj, zero_pow hp0]) (absurd h0)]
    simp only [and_true, one_ne_zero, zero_ne_one, and_false, ite_true, ite_false, pow_zero,
      pow_one, mul_one, neg_one_pow_char]
    linear_combination hpa

end TauCeti

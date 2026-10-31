/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.CharP.Quotient

/-!
# Gauss sums over finite fields

This file adds four classical facts about Gauss sums `g(χ, ψ)` of characters of a finite field `F`
to Mathlib's theory in `Mathlib.NumberTheory.GaussSum`.

Let `χ` be a nontrivial multiplicative character and `ψ` a primitive additive character, both
with complex values. Mathlib's `gaussSum_mul_gaussSum_eq_card` computes
`g(χ, ψ) g(χ⁻¹, ψ⁻¹) = #F`, and `star_gaussSum_eq` identifies `g(χ⁻¹, ψ⁻¹)` with the complex
conjugate of `g(χ, ψ)`. Together they give the classical absolute value `|g(χ, ψ)| = √#F`.

Let `l` be a prime and `χ` a character with `χ ^ l = 1`, with values in a domain `R`. Raising to
the `l`-th power is additive modulo `l`, so `g(χ, ψ)^l ≡ g(χ^l, ψ^l) = g(1, ψ^l) ≡ -1` modulo
`l R` as soon as `ψ ^ l` is nontrivial. This is the congruence behind `Φ(P) ≡ -1 (mod l)` for the
`l`-th power `Φ(P)` of the Gauss sum of the `l`-th power residue character.

If instead the coefficients have characteristic `p`, then raising to the power `q = p ^ n` is
additive, so `g(χ, ψ) ^ q = g(χ ^ q, ψ ^ q)`; when `χ ^ q = χ` and `q` is invertible in `F`,
reindexing gives `g(χ, ψ) ^ q = χ⁻¹ (q) g(χ, ψ)`. Read modulo a prime of residue
characteristic `p`, this computes the power residue symbol of `Φ(P)` at a second prime.

If `F` has characteristic `p` and `ψ` is invariant under the Frobenius `x ↦ x ^ p`, as every
additive character factoring through the trace to `𝔽_p` is (`TauCeti.apply_pow_char_of_trace`),
then reindexing the Gauss sum by the Frobenius gives `g(χ ^ p, ψ) = g(χ, ψ)`.

## Main results

* `TauCeti.norm_gaussSum`: `‖g(χ, ψ)‖ = √#F`.
* `TauCeti.gaussSum_pow_modEq_neg_one`: `g(χ, ψ)^l ≡ -1 (mod l)` when `χ ^ l = 1` and
  `ψ ^ l ≠ 1`.
* `TauCeti.gaussSum_pow_char_pow`: `g(χ, ψ) ^ q = χ⁻¹ (q) g(χ, ψ)` when the coefficients have
  characteristic `p`, `q = p ^ n` and `χ ^ q = χ`.
* `TauCeti.apply_pow_char_of_trace`: `ψ (x ^ p) = ψ x` when `ψ` factors through the trace to
  `𝔽_p`.
* `MulChar.gaussSum_pow_char_left`: `g(χ ^ p, ψ) = g(χ, ψ)` when `ψ (x ^ p) = ψ x`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 8, §2,
  Proposition 8.2.2, and Chapter 14, §5.
-/

public section

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- **A complex Gauss sum has absolute value `√#F`.** If `χ` is a nontrivial multiplicative
character and `ψ` a primitive additive character of a finite field `F`, both with values in `ℂ`,
then `‖g(χ, ψ)‖ = √#F`. -/
theorem norm_gaussSum {χ : MulChar F ℂ} (hχ : χ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = √(Fintype.card F) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq, ← starRingEnd_apply, Complex.mul_conj'] at h
  rw [← Real.sqrt_sq (norm_nonneg _)]
  exact congrArg Real.sqrt (by exact_mod_cast h)

/-- **The `l`-th power of a Gauss sum modulo `l`.** Let `l` be a prime, `χ` a multiplicative
character with `χ ^ l = 1` and `ψ` an additive character with `ψ ^ l ≠ 1` of a finite field `F`,
both with values in a domain `R`. Then `g(χ, ψ)^l ≡ -1` modulo `l R`. -/
theorem gaussSum_pow_modEq_neg_one {R : Type*} [CommRing R] [IsDomain R] {l : ℕ} [Fact l.Prime]
    {χ : MulChar F R} (hχ : χ ^ l = 1) {ψ : AddChar F R} (hψ : ψ ^ l ≠ 1) :
    gaussSum χ ψ ^ l ≡ -1 [SMOD Ideal.span {(l : R)}] := by
  by_cases hl : IsUnit (l : R)
  · rw [Ideal.span_singleton_eq_top.mpr hl]
    exact SModEq.top
  have := CharP.quotient R l hl
  -- In `R ⧸ l R`, of characteristic `l`, the `l`-th power of `g(χ, ψ)` is `g(χ ^ l, ψ ^ l)`.
  rw [SModEq.sub_mem, ← Ideal.Quotient.eq, ← gaussSum_one_left hψ, ← hχ, map_pow, gaussSum,
    gaussSum, map_sum, map_sum, sum_pow_char]
  simp only [map_mul, mul_pow, ← map_pow, ← MulChar.pow_apply' χ (Fact.out : l.Prime).ne_zero,
    AddChar.pow_apply]

/-- **The Frobenius on a Gauss sum.** Let `R` have prime characteristic `p` and let `q = p ^ n` be
invertible in the finite ring `A`. If the multiplicative character `χ` satisfies `χ ^ q = χ`,
for instance because its order divides `q - 1`, then `g(χ, ψ) ^ q = χ⁻¹ (q) g(χ, ψ)` for every
additive character `ψ`. For a quadratic character this is Mathlib's
`MulChar.IsQuadratic.gaussSum_frob_iter`. -/
theorem gaussSum_pow_char_pow {A : Type*} [CommRing A] [Fintype A] {R : Type*} [CommRing R]
    {p : ℕ} [Fact p.Prime] [CharP R p] {n : ℕ} {χ : MulChar A R} (hχ : χ ^ p ^ n = χ)
    (ψ : AddChar A R) (hq : IsUnit ((p : A) ^ n)) :
    gaussSum χ ψ ^ p ^ n = χ⁻¹ ((p : A) ^ n) * gaussSum χ ψ := by
  have h : gaussSum χ ψ ^ p ^ n = gaussSum χ (ψ ^ p ^ n) := by
    rw [gaussSum, gaussSum, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [mul_pow, ← MulChar.pow_apply' χ (pow_ne_zero n (Fact.out : p.Prime).ne_zero), hχ,
      AddChar.pow_apply]
  rw [h, AddChar.pow_mulShift, Nat.cast_pow, ← hq.unit_spec, gaussSum_mulShift_eq]

omit [Fintype F] in
/-- An additive character factoring through the trace to `𝔽_p` is invariant under the Frobenius:
if `ψ x = g (Tr x)` for all `x`, then `ψ (x ^ p) = ψ x`. -/
theorem apply_pow_char_of_trace {p : ℕ} [Fact p.Prime] [Finite F] [Algebra (ZMod p) F]
    {R : Type*} [Monoid R] {ψ : AddChar F R} {g : ZMod p → R}
    (hψ : ∀ x, ψ x = g (Algebra.trace (ZMod p) F x)) (x : F) :
    ψ (x ^ p) = ψ x := by
  have h : x ^ p = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) F x := by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ZMod.card]
  rw [hψ, hψ, h, Algebra.trace_eq_of_algEquiv]

end TauCeti

namespace MulChar

variable {F : Type*} [Field F] [Fintype F]

/-- **Gauss sums are invariant under the Frobenius.** If `F` has characteristic `p` and the
additive character `ψ` satisfies `ψ (x ^ p) = ψ x`, then `g(χ ^ p, ψ) = g(χ, ψ)` for every
multiplicative character `χ`. -/
theorem gaussSum_pow_char_left {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP F p]
    (χ : MulChar F R) {ψ : AddChar F R} (hψ : ∀ x, ψ (x ^ p) = ψ x) :
    gaussSum (χ ^ p) ψ = gaussSum χ ψ := by
  conv_rhs => rw [gaussSum, ← (frobeniusEquiv F p).toEquiv.sum_comp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp [frobenius_def, hψ, MulChar.pow_apply' χ (Fact.out : p.Prime).ne_zero]

end MulChar

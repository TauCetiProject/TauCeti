/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Multiplicity
import TauCeti.NumberTheory.Bernoulli.Basic
import TauCeti.NumberTheory.Bernoulli.Polynomials

/-!
# Voronoi's congruence for Bernoulli polynomials

Let `k ≥ 1` and `M ≥ 1`, and let `a, x, y, J` be integers with `a y = x + M J`. Then
`Mᵏ⁻¹ / k · (Bₖ(x / M) - aᵏ Bₖ(y / M))` is `xᵏ⁻¹ ((a - 1) / 2 - J)` up to an integer multiple of
`M / (k Pₖ₊₁)`, where `Pₖ₊₁ = primorial (k + 1)` is the product of the primes `≤ k + 1`. This is
Voronoi's congruence for a single residue. Taken at a residue `b` modulo `M` prime to `a`, with
`y` the representative of `b' = a⁻¹ b`, it compares the twisted Bernoulli values at `b` and `b'`
with the rational number `ε_a(b) = (a - 1) / 2 - (a ⟨b'⟩ - ⟨b⟩) / M`. For `k = 1` the congruence
is the equality `B₁(⟨b⟩ / M) - a B₁(⟨b'⟩ / M) = ε_a(b)`.

The proof expands `Mᵏ Bₖ(x / M) = ∑ᵢ (k choose i) Bᵢ xᵏ⁻ⁱ Mⁱ` and the same for
`a y = x + M J`. Every term with `i ≥ 2` is divisible by `M²`, up to the denominator of `Bᵢ`,
which divides `Pₖ₊₁` by the theorem of von Staudt and Clausen (Mathlib's
`Bernoulli.vonStaudt_clausen`). The terms with `i ≤ 1` are compared to first order in `M J`.

The expansion is `TauCeti.pow_mul_bernoulli_eval_div` and the integrality of `Pₖ₊₁ Bᵢ` for
`i ≤ k` is `TauCeti.exists_intCast_eq_primorial_mul_bernoulli`.

## Main results

* `TauCeti.exists_pow_div_mul_bernoulli_eval_sub_eq`: Voronoi's congruence for one residue.
* `TauCeti.exists_pow_div_mul_bernoulli_eval_val_sub_eq`: the same at the residues `b = a b'`
  modulo `M`, with `ε_a(b) = (a - 1) / 2 - ⌊a ⟨b'⟩ / M⌋`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
  Chapter 15 (von Staudt–Clausen and Voronoi's congruence).
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Chapter 5.

## Provenance

The comparison to first order in `M J` (through Mathlib's `sq_dvd_add_pow_sub_sub`) follows
grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cyclotomic/Voronoi.lean`, declaration `New.OddPart.voronoi_congruence`. There the
denominators are cleared with `(k + 1)!`; here they are cleared with the primorial, through von
Staudt–Clausen, and the congruence is stated for one residue.
-/

public section

open Finset Nat

namespace TauCeti

/-- The integer congruence behind Voronoi's congruence. With `c i = primorial (k + 1) Bᵢ`, the
integer `∑ᵢ (k choose i) cᵢ Mⁱ (xᵏ⁻ⁱ - aⁱ (x + M J)ᵏ⁻ⁱ)` is `k M xᵏ⁻¹ (c₁ (1 - a) - c₀ J)`
modulo `M²`. -/
private theorem sq_dvd_sum_sub {k : ℕ} (hk : k ≠ 0) (c : ℕ → ℤ) (M a x J : ℤ) :
    M ^ 2 ∣ ∑ i ∈ range (k + 1), (k.choose i : ℤ) * c i * M ^ i *
        (x ^ (k - i) - a ^ i * (x + M * J) ^ (k - i)) -
      k * M * x ^ (k - 1) * (c 1 * (1 - a) - c 0 * J) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_iff_ne_zero.2 hk)
  rw [sum_range_succ', sum_range_succ']
  -- the terms with `i ≥ 2` carry the factor `M ^ i`
  have h2 : M ^ 2 ∣ ∑ i ∈ range k, ((k + 1).choose (i + 1 + 1) : ℤ) * c (i + 1 + 1) *
      M ^ (i + 1 + 1) * (x ^ (k + 1 - (i + 1 + 1)) - a ^ (i + 1 + 1) *
        (x + M * J) ^ (k + 1 - (i + 1 + 1))) :=
    dvd_sum fun i _ ↦ Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow M (by omega)) _) _
  -- the term with `i = 0`, to first order in `M J`
  have h0 : (M * J) ^ 2 ∣ (x + M * J) ^ (k + 1) - x ^ k * (M * J) * (k + 1 : ℕ) - x ^ (k + 1) :=
    sq_dvd_add_pow_sub_sub (M * J) x (k + 1)
  -- the term with `i = 1`: `x ^ k - (x + M J) ^ k` is divisible by `M J`
  have h1 : M * J ∣ (x + M * J) ^ k - x ^ k := by
    simpa using sub_dvd_pow_sub_pow (x + M * J) x k
  obtain ⟨u, hu⟩ := h0
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, hw⟩ := h2
  refine ⟨w - c 0 * J ^ 2 * u - (k + 1) * c 1 * a * J * v, ?_⟩
  simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, one_mul,
    Nat.sub_zero, Nat.add_sub_cancel, zero_add, Nat.cast_one, Nat.cast_add,
    Nat.add_sub_add_right] at hu hw ⊢
  linear_combination hw - c 0 * hu - (k + 1) * c 1 * a * M * hv

/-- **Voronoi's congruence for one residue.** Let `k ≥ 1`, `M ≠ 0`, and let `a, x, y, J` be integers
with `a y = x + M J`. Then for some integer `z`,
`Mᵏ⁻¹ / k · (Bₖ(x / M) - aᵏ Bₖ(y / M)) = xᵏ⁻¹ ((a - 1) / 2 - J) + M / (k primorial (k + 1)) · z`. -/
theorem exists_pow_div_mul_bernoulli_eval_sub_eq {k : ℕ} (hk : k ≠ 0) {M : ℕ} (hM : M ≠ 0)
    {a x y J : ℤ} (h : a * y = x + M * J) :
    ∃ z : ℤ, (M : ℚ) ^ (k - 1) / k *
        ((Polynomial.bernoulli k).eval ((x : ℚ) / M) -
          a ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M)) =
      x ^ (k - 1) * ((a - 1) / 2 - J) + M / (k * primorial (k + 1)) * z := by
  choose! c' hc' using fun i (hi : i < k + 1) ↦
    exists_intCast_eq_primorial_mul_bernoulli (Nat.lt_succ_iff.1 hi)
  obtain ⟨z, hz⟩ := sq_dvd_sum_sub hk c' M a x J
  refine ⟨z, ?_⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have hkq : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have hP : (primorial (k + 1) : ℚ) ≠ 0 := by exact_mod_cast primorial_ne_zero _
  have hc0 := hc' 0 (by omega)
  have hc1 := hc' 1 (by omega)
  rw [bernoulli_zero, mul_one] at hc0
  rw [bernoulli_one] at hc1
  -- the integer identity, cast to `ℚ`, is the claim multiplied by `k M primorial (k + 1)`
  have hzq := congrArg (fun n : ℤ ↦ (n : ℚ)) hz
  push_cast at hzq
  have hy : (a : ℚ) ^ k * (M ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M)) =
      ∑ i ∈ range (k + 1), (k.choose i : ℚ) * bernoulli i * a ^ i *
        (x + M * J) ^ (k - i) * M ^ i := by
    rw [pow_mul_bernoulli_eval_div hMq, mul_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    have hik : (a : ℚ) ^ k = a ^ (k - i) * a ^ i := by
      rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.1 (mem_range.1 hi))]
    have hxy : ((x : ℚ) + M * J) = a * y := by exact_mod_cast h.symm
    rw [hxy, mul_pow, hik]
    ring
  have hsum : ∑ i ∈ range (k + 1), (k.choose i : ℚ) * c' i * M ^ i *
      (x ^ (k - i) - a ^ i * (x + M * J) ^ (k - i)) =
      primorial (k + 1) * M ^ k *
        ((Polynomial.bernoulli k).eval ((x : ℚ) / M) -
          a ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M)) := by
    have hfactor : (primorial (k + 1) : ℚ) * M ^ k *
        ((Polynomial.bernoulli k).eval ((x : ℚ) / M) -
          a ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M)) = primorial (k + 1) *
          (M ^ k * (Polynomial.bernoulli k).eval ((x : ℚ) / M) -
            a ^ k * (M ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M))) := by ring
    rw [hfactor, hy, pow_mul_bernoulli_eval_div hMq, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun i hi ↦ ?_
    rw [hc' i (mem_range.1 hi)]
    ring
  rw [hsum, hc0, hc1] at hzq
  have hk1 : (M : ℚ) ^ k = M ^ (k - 1) * M := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hk)]
  rw [hk1] at hzq
  have hzq' : (primorial (k + 1) : ℚ) * M ^ (k - 1) *
      ((Polynomial.bernoulli k).eval ((x : ℚ) / M) -
        a ^ k * (Polynomial.bernoulli k).eval ((y : ℚ) / M)) -
      k * x ^ (k - 1) * (primorial (k + 1) * -2⁻¹ * (1 - a) - primorial (k + 1) * J) = M * z :=
    mul_left_cancel₀ hMq (by linear_combination hzq)
  field_simp
  linear_combination 2 * hzq'

/-- **Voronoi's congruence at the residues modulo `M`.** Let `k ≥ 1`, `M ≥ 1`, `a ≥ 0`, and let
`b'` be a residue modulo `M` and `b = a b'`, with representatives `⟨b⟩, ⟨b'⟩ ∈ [0, M)`. Then for
some integer `z`,
`Mᵏ⁻¹ / k · (Bₖ(⟨b⟩ / M) - aᵏ Bₖ(⟨b'⟩ / M)) = ⟨b⟩ᵏ⁻¹ ε_a(b) + M / (k Pₖ₊₁) · z`,
where `Pₖ₊₁ = primorial (k + 1)` and `ε_a(b) = (a - 1) / 2 - ⌊a ⟨b'⟩ / M⌋`. When `a` is prime to
`M`, `b' = a⁻¹ b` and `⌊a ⟨b'⟩ / M⌋ = (a ⟨b'⟩ - ⟨b⟩) / M`. -/
theorem exists_pow_div_mul_bernoulli_eval_val_sub_eq {k : ℕ} (hk : k ≠ 0) {M : ℕ} [NeZero M]
    (a : ℕ) (b' : ZMod M) :
    ∃ z : ℤ, (M : ℚ) ^ (k - 1) / k *
        ((Polynomial.bernoulli k).eval ((((a : ZMod M) * b').val : ℚ) / M) -
          a ^ k * (Polynomial.bernoulli k).eval ((b'.val : ℚ) / M)) =
      (((a : ZMod M) * b').val : ℚ) ^ (k - 1) * ((a - 1) / 2 - (a * b'.val / M : ℕ)) +
      M / (k * primorial (k + 1)) * z := by
  -- `a ⟨b'⟩ = ⟨b⟩ + M ⌊a ⟨b'⟩ / M⌋`
  have h : ((a * b'.val : ℕ) : ℤ) = ((a : ZMod M) * b').val + M * (a * b'.val / M : ℕ) := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    exact_mod_cast (Nat.mod_add_div _ _).symm
  push_cast at h
  obtain ⟨z, hz⟩ := exists_pow_div_mul_bernoulli_eval_sub_eq hk (NeZero.ne M) h
  refine ⟨z, ?_⟩
  simp only [Int.cast_natCast] at hz
  exact hz

end TauCeti

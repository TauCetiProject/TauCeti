/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Ring.Identities
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Capelli's theorem: irreducibility of `Xⁿ - a` over an arbitrary field

Let `K` be a field of any characteristic, `n ≠ 0` and `a ∈ K`. **Capelli's theorem** says that
`Xⁿ - a` is irreducible over `K` if and only if `a` is not a `p`-th power in `K` for any prime
`p ∣ n`, and `a ∉ -4K⁴` when `4 ∣ n`. Mathlib proves the odd case
(`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`); the extra condition for `4 ∣ n` is needed
because of Sophie Germain's identity `X⁴ + 4b⁴ = (X² - 2bX + 2b²)(X² + 2bX + 2b²)`, so for
instance `X⁴ + 4` is reducible over `ℚ` although `-4` is not a square there.

## Main results

* `TauCeti.X_pow_two_pow_sub_C_irreducible`: `X^(2ᵏ) - a` is irreducible when `a` is not a
  square and, for `k ≥ 2`, `a ∉ -4K⁴`.
* `TauCeti.neg_four_mul_pow_four_ne_of_irreducible_X_pow_sub_C`: if `Xⁿ - a` is irreducible
  and `4 ∣ n`, then `a ∉ -4K⁴`.
* `TauCeti.X_pow_sub_C_irreducible_of_forall_prime`: the sufficiency half of Capelli's theorem.
* `TauCeti.X_pow_sub_C_irreducible_iff_forall_prime`: **Capelli's theorem**.

## Implementation notes

The heart of the proof is the two-power case `n = 2ᵏ`. Let `β` be a root of the irreducible
`X² - a` and `L = K(β)`. Writing an element of `L` as `x + yβ`, a fourth root `γ` of `a` in `L`
satisfies `γ² = ±β`, which forces `x² + ay² = 0` and `2xy = ±1`, hence `a = -4x⁴`. So if
`a ∉ -4K⁴`, then `β` is neither a square nor in `-4L⁴`, and induction over `L` applies. In
characteristic `2` the equation `2xy = ±1` has no solution, so no case split is needed. For a
general `n = 2ᵏm` with `m` odd one adjoins a root `α` of `Xᵐ - a` and transports the
hypotheses to `α` with the norm, whose value at `α` is `a` because `m` is odd; this reduction
follows the proof of Mathlib's `X_pow_sub_C_irreducible_of_odd`.

## References

* S. Lang, *Algebra*, Chapter VI, Theorem 9.1.
* F. Szechtman, *On the degree of repeated radical extensions*, Section 1, criterion (C).
* B. Koley and A. S. Reddy, *Irreducibility of xⁿ − a*, Lemma 10 and Theorem 1.
-/

public section

namespace TauCeti

open Polynomial AdjoinRoot

variable {K : Type*} [Field K]

section QuadraticStep

variable {a : K} [Fact (Irreducible (X ^ 2 - C a))]

/-- If `a` is not a square in `K` but is a fourth power in `K(√a)`, then `a ∈ -4K⁴`. -/
private theorem exists_neg_four_mul_pow_four_eq_of_pow_four_eq (ha : ∀ b : K, b ^ 2 ≠ a)
    {γ : AdjoinRoot (X ^ 2 - C a)} (hγ : γ ^ 4 = algebraMap K _ a) :
    ∃ x : K, -4 * x ^ 4 = a := by
  have hβ : root (X ^ 2 - C a) ^ 2 = algebraMap K _ a := root_X_pow_sub_C_pow 2 a
  -- Since `a` is not a square, `1` and `β = √a` are linearly independent over `K`.
  have hind (u v : K)
      (h : algebraMap K _ u + algebraMap K _ v * root (X ^ 2 - C a) = 0) : u = 0 ∧ v = 0 := by
    have hinj := (algebraMap K (AdjoinRoot (X ^ 2 - C a))).injective
    by_cases hv : v = 0
    · subst hv
      exact ⟨hinj (by simpa using h), rfl⟩
    · refine (ha (-u / v) (hinj ?_)).elim
      have hroot : root (X ^ 2 - C a) = algebraMap K _ (-u / v) := by
        rw [map_div₀, map_neg, eq_div_iff ((_root_.map_ne_zero _).mpr hv)]
        linear_combination h
      rw [map_pow, ← hroot, hβ]
  -- Write `γ = x + yβ` in the power basis `1, β`.
  let pb := powerBasis' (monic_X_pow_sub_C a two_ne_zero)
  obtain ⟨f, hf, rfl⟩ := pb.exists_eq_aeval γ
  have hf : f.natDegree ≤ 1 := by
    have : pb.dim = 2 := by simp [pb]
    lia
  have hgen : pb.gen = root (X ^ 2 - C a) := by simp [pb]
  rw [eq_X_add_C_of_natDegree_le_one hf] at hγ
  simp only [map_add, map_mul, aeval_C, aeval_X, hgen] at hγ
  generalize f.coeff 0 = x at hγ
  generalize f.coeff 1 = y at hγ
  -- Since `γ⁴ = β²`, the square `γ²` is `sβ` for a sign `s = ±1`.
  obtain ⟨s, hs, hγs⟩ : ∃ s : K, s ^ 2 = 1 ∧
      (algebraMap K _ y * root (X ^ 2 - C a) + algebraMap K _ x) ^ 2 =
        algebraMap K _ s * root (X ^ 2 - C a) := by
    have : ((algebraMap K _ y * root (X ^ 2 - C a) + algebraMap K _ x) ^ 2 - root (X ^ 2 - C a)) *
        ((algebraMap K _ y * root (X ^ 2 - C a) + algebraMap K _ x) ^ 2 +
          root (X ^ 2 - C a)) = 0 := by
      linear_combination hγ - hβ
    rcases mul_eq_zero.mp this with h | h
    · exact ⟨1, one_pow 2, by rw [map_one, one_mul]; linear_combination h⟩
    · exact ⟨-1, by ring, by rw [map_neg, map_one]; linear_combination h⟩
  -- Comparing coordinates in `1, β` gives `x² + ay² = 0` and `2xy = s`.
  obtain ⟨h₁, h₂⟩ := hind (x ^ 2 + a * y ^ 2) (2 * x * y - s) (by
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
    linear_combination hγs - algebraMap K _ y ^ 2 * hβ)
  exact ⟨x, by linear_combination (-4 * x ^ 2) * h₁ + a * (s + 2 * x * y) * h₂ + a * hs⟩

end QuadraticStep

/-- **The two-power case of Capelli's theorem.** Over any field `K`, if `a` is not a square
in `K` and, when `k ≥ 2`, `a` is not of the form `-4b⁴`, then `X^(2ᵏ) - a` is irreducible.
The second condition cannot be dropped: `X⁴ + 4` is reducible over `ℚ`. -/
theorem X_pow_two_pow_sub_C_irreducible (k : ℕ) {a : K} (ha : ∀ b : K, b ^ 2 ≠ a)
    (ha' : 2 ≤ k → ∀ b : K, -4 * b ^ 4 ≠ a) : Irreducible (X ^ 2 ^ k - C a) := by
  induction k generalizing K a with
  | zero => simpa using irreducible_X_sub_C a
  | succ k ih =>
    have h₂ := X_pow_sub_C_irreducible_of_prime Nat.prime_two ha
    obtain _ | k := k
    · simpa using h₂
    have := Fact.mk h₂
    have ha'' := ha' (by lia)
    rw [pow_succ]
    refine X_pow_mul_sub_C_irreducible h₂ (ih (fun γ hγ ↦ ?_) (fun _ δ hδ ↦ ?_))
    · -- A square root `γ` of `√a` is a fourth root of `a`.
      obtain ⟨x, hx⟩ := exists_neg_four_mul_pow_four_eq_of_pow_four_eq ha (γ := γ) (by
        rw [AdjoinRoot.algebraMap_eq, ← root_X_pow_sub_C_pow 2 a, ← hγ]; ring)
      exact ha'' x hx
    · -- If `√a = -4δ⁴`, then `2δ²` is a fourth root of `a`.
      obtain ⟨x, hx⟩ := exists_neg_four_mul_pow_four_eq_of_pow_four_eq ha (γ := 2 * δ ^ 2) (by
        rw [AdjoinRoot.algebraMap_eq, ← root_X_pow_sub_C_pow 2 a, ← hδ]; ring)
      exact ha'' x hx

/-- If `Xⁿ - a` is irreducible and `4 ∣ n`, then `a` is not of the form `-4b⁴`: otherwise
Sophie Germain's identity factors `Xⁿ - a` into two polynomials of degree `n / 2`. This is the
companion of Mathlib's `pow_ne_of_irreducible_X_pow_sub_C`. -/
theorem neg_four_mul_pow_four_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) (hn : 4 ∣ n) (b : K) : -4 * b ^ 4 ≠ a := by
  obtain ⟨l, rfl⟩ := hn
  have hl : l ≠ 0 := by
    rintro rfl
    exact not_irreducible_C (1 - a) (by simpa using H)
  rintro rfl
  set p₁ : K[X] := X ^ 2 - C (2 * b) * X + C (2 * b ^ 2)
  set p₂ : K[X] := X ^ 2 + C (2 * b) * X + C (2 * b ^ 2)
  have hfac : (X ^ (4 * l) - C (-4 * b ^ 4) : K[X]) = p₁.comp (X ^ l) * p₂.comp (X ^ l) := by
    simp only [p₁, p₂, sub_comp, add_comp, mul_comp, pow_comp, X_comp, C_comp]
    simp only [map_mul, map_neg, map_pow, map_ofNat, pow_mul]
    linear_combination pow_four_add_four_mul_pow_four' (a := (X : K[X]) ^ l) (b := C b)
  have hdeg {q : K[X]} (hq : q.natDegree = 2) (hu : IsUnit (q.comp (X ^ l))) : False := by
    have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_comp, hq, natDegree_X_pow] at this
    lia
  rcases (hfac ▸ H).isUnit_or_isUnit rfl with hu | hu
  · exact hdeg (by simp only [p₁]; compute_degree!) hu
  · exact hdeg (by simp only [p₂]; compute_degree!) hu

/-- **Capelli's theorem**, sufficiency: over any field `K`, if `n ≠ 0`, `a` is not a `p`-th
power for any prime `p ∣ n`, and `a` is not of the form `-4b⁴` when `4 ∣ n`, then `Xⁿ - a` is
irreducible. -/
theorem X_pow_sub_C_irreducible_of_forall_prime {n : ℕ} (hn : n ≠ 0) {a : K}
    (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a)
    (ha' : 4 ∣ n → ∀ b : K, -4 * b ^ 4 ≠ a) : Irreducible (X ^ n - C a) := by
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm₀ : m ≠ 0 := hm.pos.ne'
  have hirr : Irreducible (X ^ m - C a) :=
    X_pow_sub_C_irreducible_of_odd hm fun p hp hpm ↦ ha p hp (Dvd.dvd.mul_left hpm _)
  obtain rfl | hk := Nat.eq_zero_or_pos k
  · simpa using hirr
  have := Fact.mk hirr
  have hnorm : Algebra.norm K (root (X ^ m - C a)) = a := by
    rw [norm_root_X_pow_sub_C hm₀, hm.neg_one_pow, neg_one_mul, neg_neg]
  refine X_pow_mul_sub_C_irreducible hirr (X_pow_two_pow_sub_C_irreducible k (fun γ hγ ↦ ?_)
    fun hk₂ δ hδ ↦ ?_)
  · -- The norm of a square root of `α` is a square root of `a`.
    refine ha 2 Nat.prime_two (Dvd.dvd.mul_right (dvd_pow_self 2 hk.ne') _) (Algebra.norm K γ) ?_
    rw [← map_pow, hγ, hnorm]
  · -- Taking norms in `α = -4δ⁴` gives `a = (-4)ᵐ N(δ)⁴ ∈ -4K⁴`, as `m` is odd.
    have h4 : 4 ∣ 2 ^ k * m := Dvd.dvd.mul_right (dvd_trans (by norm_num) (pow_dvd_pow 2 hk₂)) _
    obtain ⟨j, rfl⟩ := hm
    refine ha' h4 (2 ^ j * Algebra.norm K δ) ?_
    have hfin : Module.finrank K (AdjoinRoot (X ^ (2 * j + 1) - C a)) = 2 * j + 1 := by
      rw [(powerBasis (X_pow_sub_C_ne_zero (by lia) a)).finrank, powerBasis_dim,
        natDegree_X_pow_sub_C]
    have := congrArg (Algebra.norm K) hδ
    have hneg4 : (-4 : AdjoinRoot (X ^ (2 * j + 1) - C a)) = algebraMap K _ (-4) := by
      rw [map_neg, map_ofNat]
    rw [hnorm, map_mul, map_pow, hneg4, Algebra.norm_algebraMap, hfin] at this
    have hpow : (-4 : K) ^ (2 * j + 1) = -4 * (2 ^ j) ^ 4 := by
      rw [pow_succ, pow_mul, ← pow_mul _ j 4, mul_comm j 4, pow_mul]
      norm_num [mul_comm]
    rw [hpow] at this
    linear_combination this

/-- **Capelli's theorem.** Over any field `K` and for `n ≠ 0`, the binomial `Xⁿ - a` is
irreducible if and only if `a` is not a `p`-th power for any prime `p ∣ n` and, when `4 ∣ n`,
`a` is not of the form `-4b⁴`. For odd `n` this is Mathlib's
`X_pow_sub_C_irreducible_iff_forall_prime_of_odd`. -/
theorem X_pow_sub_C_irreducible_iff_forall_prime {n : ℕ} (hn : n ≠ 0) {a : K} :
    Irreducible (X ^ n - C a) ↔
      (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) ∧ (4 ∣ n → ∀ b : K, -4 * b ^ 4 ≠ a) :=
  ⟨fun H ↦ ⟨fun _ hp hpn ↦ pow_ne_of_irreducible_X_pow_sub_C H hpn hp.ne_one,
      fun h4 ↦ neg_four_mul_pow_four_ne_of_irreducible_X_pow_sub_C H h4⟩,
    fun h ↦ X_pow_sub_C_irreducible_of_forall_prime hn h.1 h.2⟩

end TauCeti

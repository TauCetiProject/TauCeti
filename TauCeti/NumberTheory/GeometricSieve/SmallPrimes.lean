/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.Chebyshev.PowerTail
public import TauCeti.NumberTheory.GeometryOfNumbers.ResidueClassCount
import Mathlib.Data.Set.Card.Arithmetic

/-!
# The small-prime half of the geometric sieve

Let `B ⊆ ℝ^ι` be bounded, `n` the cardinality of `ι`, and `k ≥ 2`. Suppose that for every prime
`p` we are given a set `S p ⊆ (ℤ/pℤ)^ι` of residues, with `#S p ≤ C₀ · p ^ (n - k)` for all primes
`p` beyond some `M₀`. Then there is a constant `C` such that for all `r ≥ 0` and `M > 1`, the pairs
`(a, p)` with `a ∈ r • B ∩ ℤ^ι`, `p` prime, `M < p ≤ r` and `a mod p ∈ S p` number at most
`C · r ^ n / (M ^ (k - 1) · log M)`.

In the geometric sieve, `S p = Y(𝔽_p)` for a closed subscheme `Y ⊆ 𝔸^n_ℤ` of codimension `k`, and
the bound `#Y(𝔽_p) = O(p ^ (n - k))` for large `p` is the input. The finitely many small primes cost
nothing: there `#S p ≤ p ^ n ≤ M₀ ^ k · p ^ (n - k)`, so the bound holds for every prime after
enlarging `C₀`. For `p ≤ r` the residue-class count
`Bornology.IsBounded.exists_ncard_reduction_mem_le` shows that `p` contributes
`O(#S p · (r / p) ^ n) = O(r ^ n / p ^ k)` points, and the prime sum
`∑_{M < p ≤ r} r ^ n / p ^ k = O(r ^ n / (M ^ (k - 1) log M))` of
`TauCeti.sum_primesLE_filter_gt_div_pow_le` keeps Chebyshev's logarithmic saving.

The primes `p > r` are not covered here: there the count of points in a residue class modulo `p`
is no longer of order `(r / p) ^ n`, and a separate argument is needed.

## Main results

* `TauCeti.GeometricSieve.exists_ncard_pairs_reduction_mem_le`: the bound for pairs `(a, p)`.
* `TauCeti.GeometricSieve.exists_ncard_exists_prime_reduction_mem_le`: the same bound for the
  points `a` reducing into `S p` for at least one prime `M < p ≤ r`.

## References

* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Theorem 3.3, display (16).
-/

public section

open Finset
open scoped Pointwise

namespace TauCeti.GeometricSieve

variable {ι : Type*}

/-- A bound `#S p ≤ C₀ · p ^ (n - k)` for the primes `p > M₀` extends to all primes after
enlarging the constant, since `#S p ≤ p ^ n` always. -/
private theorem exists_ncard_le_mul_pow_div_pow [Fintype ι] (S : ∀ p : ℕ, Set (ι → ZMod p)) {k : ℕ}
    {C₀ M₀ : ℝ} (hS : ∀ p : ℕ, p.Prime → M₀ < p →
      ((S p).ncard : ℝ) ≤ C₀ * (p : ℝ) ^ ((Fintype.card ι : ℝ) - k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime →
      ((S p).ncard : ℝ) ≤ C * ((p : ℝ) ^ Fintype.card ι / (p : ℝ) ^ k) := by
  refine ⟨max C₀ (|M₀| ^ k), le_max_of_le_right (by positivity), fun p hp ↦ ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq : (0 : ℝ) ≤ (p : ℝ) ^ Fintype.card ι / (p : ℝ) ^ k := by positivity
  by_cases hpM : M₀ < p
  · have h := hS p hp hpM
    rw [Real.rpow_sub hp0, Real.rpow_natCast, Real.rpow_natCast] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)
  · -- A small prime: `#S p ≤ p ^ n = p ^ k · p ^ (n - k)` with `p ≤ M₀`.
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcard : ((S p).ncard : ℝ) ≤ (p : ℝ) ^ Fintype.card ι := by
      have h := Set.ncard_le_card (S p)
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card] at h
      exact_mod_cast h
    have hpk : (p : ℝ) ^ k ≤ |M₀| ^ k :=
      pow_le_pow_left₀ hp0.le ((not_lt.mp hpM).trans (le_abs_self M₀)) k
    calc ((S p).ncard : ℝ) ≤ (p : ℝ) ^ Fintype.card ι := hcard
      _ = (p : ℝ) ^ k * ((p : ℝ) ^ Fintype.card ι / (p : ℝ) ^ k) := by field_simp
      _ ≤ max C₀ (|M₀| ^ k) * ((p : ℝ) ^ Fintype.card ι / (p : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_right (hpk.trans (le_max_right _ _)) hq

/-- The pairs `(a, p)` with `M < p ≤ r` are counted prime by prime: for each such prime they are
the integer points of `r • B` reducing into `S p`. -/
private theorem ncard_pairs_le_sum [Finite ι] (S : ∀ p : ℕ, Set (ι → ZMod p)) {B : Set (ι → ℝ)}
    (hB : Bornology.IsBounded B) (r M : ℝ) :
    {x : (ι → ℤ) × ℕ | (fun i ↦ (x.1 i : ℝ)) ∈ r • B ∧ x.2.Prime ∧ M < x.2 ∧
        (x.2 : ℝ) ≤ r ∧ (fun i ↦ (x.1 i : ZMod x.2)) ∈ S x.2}.ncard ≤
      ∑ p ∈ (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ)),
        {a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧ (fun i ↦ (a i : ZMod p)) ∈ S p}.ncard := by
  have := Fintype.ofFinite ι
  set A : ℕ → Set (ι → ℤ) := fun p ↦
    {a | (fun i ↦ (a i : ℝ)) ∈ r • B ∧ (fun i ↦ (a i : ZMod p)) ∈ S p}
  set P := (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ))
  have hsub : {x : (ι → ℤ) × ℕ | (fun i ↦ (x.1 i : ℝ)) ∈ r • B ∧ x.2.Prime ∧ M < x.2 ∧
      (x.2 : ℝ) ≤ r ∧ (fun i ↦ (x.1 i : ZMod x.2)) ∈ S x.2} ⊆
      ⋃ p ∈ P, (fun a ↦ (a, p)) '' A p := by
    rintro ⟨a, p⟩ ⟨ha, hp, hMp, hpr, haS⟩
    exact Set.mem_biUnion (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨Nat.le_floor hpr, hp⟩, hMp⟩)
      ⟨a, ⟨ha, haS⟩, rfl⟩
  have hfin : (⋃ p ∈ P, (fun a ↦ (a, p)) '' A p).Finite :=
    P.finite_toSet.biUnion fun p _ ↦
      (((hB.smul₀ r).finite_setOf_intCast_mem).subset fun a (ha : a ∈ A p) ↦ ha.1).image _
  refine (Set.ncard_le_ncard hsub hfin).trans ((P.set_ncard_biUnion_le _).trans_eq ?_)
  exact sum_congr rfl fun p _ ↦ Set.ncard_image_of_injective _ fun _ _ h ↦ congrArg Prod.fst h

/-- **The geometric sieve for small primes.** Let `B ⊆ ℝ^ι` be bounded, `n` the cardinality of
`ι`, `k ≥ 2`, and let `S p ⊆ (ℤ/pℤ)^ι` satisfy `#S p ≤ C₀ · p ^ (n - k)` for every prime
`p > M₀`. There is a constant `C` such that for all `r ≥ 0` and `M > 1` the pairs `(a, p)` with
`a ∈ r • B ∩ ℤ^ι`, `p` prime, `M < p ≤ r` and `a mod p ∈ S p` number at most
`C · r ^ n / (M ^ (k - 1) · log M)`. -/
theorem exists_ncard_pairs_reduction_mem_le [Fintype ι] (S : ∀ p : ℕ, Set (ι → ZMod p)) {k : ℕ}
    (hk : 2 ≤ k) {C₀ M₀ : ℝ} (hS : ∀ p : ℕ, p.Prime → M₀ < p →
      ((S p).ncard : ℝ) ≤ C₀ * (p : ℝ) ^ ((Fintype.card ι : ℝ) - k))
    {B : Set (ι → ℝ)} (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r M : ℝ, 0 ≤ r → 1 < M →
      ({x : (ι → ℤ) × ℕ | (fun i ↦ (x.1 i : ℝ)) ∈ r • B ∧ x.2.Prime ∧ M < x.2 ∧
          (x.2 : ℝ) ≤ r ∧ (fun i ↦ (x.1 i : ZMod x.2)) ∈ S x.2}.ncard : ℝ) ≤
        C * r ^ Fintype.card ι / (M ^ (k - 1) * Real.log M) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hB.exists_ncard_reduction_mem_le
  obtain ⟨C₂, hC₂, h₂⟩ := exists_ncard_le_mul_pow_div_pow S hS
  have hk1 : (0 : ℝ) < k - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨C₁ * C₂ * ((k : ℝ) * Real.log 4 / (k - 1)), by positivity, fun r M hr hM ↦ ?_⟩
  set n := Fintype.card ι
  set P := (Nat.primesLE ⌊r⌋₊).filter (fun p : ℕ ↦ M < (p : ℝ))
  -- Each prime `M < p ≤ r` contributes `O(r ^ n / p ^ k)` pairs.
  have hA : ∀ p ∈ P, ({a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧
      (fun i ↦ (a i : ZMod p)) ∈ S p}.ncard : ℝ) ≤ C₁ * C₂ * (r ^ n / (p : ℝ) ^ k) := by
    intro p hpP
    obtain ⟨hpr, hp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hpP).1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    calc _ ≤ C₁ * (S p).ncard * (r / p) ^ n :=
          h₁ r p (S p) hp.pos ((Nat.le_floor_iff hr).mp hpr)
      _ ≤ C₁ * (C₂ * ((p : ℝ) ^ n / (p : ℝ) ^ k)) * (r / p) ^ n := by
          gcongr
          exact h₂ p hp
      _ = C₁ * C₂ * (r ^ n / (p : ℝ) ^ k) := by
          rw [div_pow]
          field_simp
  calc _ ≤ ∑ p ∈ P, ({a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧
          (fun i ↦ (a i : ZMod p)) ∈ S p}.ncard : ℝ) := by
        exact_mod_cast ncard_pairs_le_sum S hB r M
    _ ≤ ∑ p ∈ P, C₁ * C₂ * (r ^ n / (p : ℝ) ^ k) := sum_le_sum hA
    _ = C₁ * C₂ * ∑ p ∈ P, r ^ n / (p : ℝ) ^ k := by rw [mul_sum]
    _ ≤ C₁ * C₂ * ((k : ℝ) * Real.log 4 / (k - 1) * r ^ n / (M ^ (k - 1) * Real.log M)) := by
        gcongr
        exact sum_primesLE_filter_gt_div_pow_le hM hr hk n
    _ = _ := by ring

/-- **The geometric sieve for small primes, counting points.** Under the hypotheses of
`exists_ncard_pairs_reduction_mem_le`, the points `a ∈ r • B ∩ ℤ^ι` reducing into `S p` for at
least one prime `M < p ≤ r` number at most `C · r ^ n / (M ^ (k - 1) · log M)`. -/
theorem exists_ncard_exists_prime_reduction_mem_le [Fintype ι]
    (S : ∀ p : ℕ, Set (ι → ZMod p)) {k : ℕ}
    (hk : 2 ≤ k) {C₀ M₀ : ℝ} (hS : ∀ p : ℕ, p.Prime → M₀ < p →
      ((S p).ncard : ℝ) ≤ C₀ * (p : ℝ) ^ ((Fintype.card ι : ℝ) - k))
    {B : Set (ι → ℝ)} (hB : Bornology.IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r M : ℝ, 0 ≤ r → 1 < M →
      ({a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧ ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℝ) ≤ r ∧
          (fun i ↦ (a i : ZMod p)) ∈ S p}.ncard : ℝ) ≤
        C * r ^ Fintype.card ι / (M ^ (k - 1) * Real.log M) := by
  obtain ⟨C, hC, h⟩ := exists_ncard_pairs_reduction_mem_le S hk hS hB
  refine ⟨C, hC, fun r M hr hM ↦ (?_ : _ ≤ _).trans (h r M hr hM)⟩
  -- Every such point is the first coordinate of a counted pair, and there are finitely many pairs.
  have hfin : {x : (ι → ℤ) × ℕ | (fun i ↦ (x.1 i : ℝ)) ∈ r • B ∧ x.2.Prime ∧ M < x.2 ∧
      (x.2 : ℝ) ≤ r ∧ (fun i ↦ (x.1 i : ZMod x.2)) ∈ S x.2}.Finite :=
    ((hB.smul₀ r).finite_setOf_intCast_mem.prod (Set.finite_le_nat ⌊r⌋₊)).subset
      fun x hx ↦ ⟨hx.1, Nat.le_floor hx.2.2.2.1⟩
  refine Nat.cast_le.mpr ((Set.ncard_le_ncard ?_ (hfin.image Prod.fst)).trans
    (Set.ncard_image_le hfin))
  rintro a ⟨ha, p, hp, hMp, hpr, haS⟩
  exact ⟨(a, p), ⟨ha, hp, hMp, hpr, haS⟩, rfl⟩

end TauCeti.GeometricSieve

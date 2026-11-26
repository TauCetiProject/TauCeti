/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Primorial
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
import TauCeti.Data.Int.DivMod
import TauCeti.NumberTheory.Bernoulli.Voronoi
import TauCeti.NumberTheory.MulChar.Basic

/-!
# Voronoi's congruence for generalized Bernoulli numbers

Let `χ` be a Dirichlet character modulo `T` with values in a commutative ring `O`, let `e ≥ 1`
and let `b` be prime to `T`. For a unit `t` modulo `T` with representative `⟨t⟩ ∈ [0, T)`, put
`θ_{T,b}(t) = ⌊b⟨t⟩ / T⌋ - ⌊b⟨-t⟩ / T⌋`. The coefficient of the Stickelberger element
`s_{T,b}` smoothed by `b` (`TauCeti.smoothedStickelberger`) at `c` is `⌊b⟨c⁻¹⟩ / T⌋`, so
`θ_{T,b}(t)` is the coefficient at `t⁻¹` of its minus part `(1 - [-1]) s_{T,b}`. Voronoi's
congruence compares the twisted Stickelberger sum `Θ = ∑_t θ_{T,b}(t) ⟨t⟩ᵉ χ(t)` with the
generalized Bernoulli number `B_{e+1,χ}` (Tau Ceti's `DirichletCharacter.generalizedBernoulli`,
at the modulus `T`):

`P_{e+2} ((e + 1) bᵉ χ(b) Θ - 2 (χ(b) bᵉ⁺¹ - 1) B_{e+1,χ}) ∈ T O`,

where `P_{e+2} = primorial (e + 2)` is the product of the primes `≤ e + 2`. Here `B_{e+1,χ}` lives
in a `ℚ`-algebra `R` under `O`, and `T O` means the `O`-multiples of `T` in `R`.

The proof sums Voronoi's congruence for one residue
(`TauCeti.exists_pow_div_mul_bernoulli_eval_val_sub_eq`), twisted by `χ`, over the residues
modulo `T`, and uses `θ_{T,b}(t) = 2 ⌊b⟨t⟩ / T⌋ - (b - 1)` for units `t`.

## Main results

* `DirichletCharacter.primorial_mul_sub_generalizedBernoulli_mem_span`: Voronoi's congruence
  for `B_{e+1,χ}`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
  Chapter 15.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Chapter 5.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Cyclotomic/Voronoi.lean`, declarations `New.OddPart.voronoi_congruence` and
`New.OddPart.voronoi_congruence_bernoulli`, which state the congruence for a character modulo
`N`, a multiplier `c ≡ 1` modulo `N` and the level `N m`, modulo `m`. Here it is stated at the
level of the character, for every multiplier prime to it, and for the generalized Bernoulli
number itself; the denominators are cleared with the primorial rather than with `(e + 2)!`.
-/

public section

open Finset

namespace DirichletCharacter

variable {T : ℕ} [NeZero T]

/-- Voronoi's congruence for one residue, with the denominators cleared:
`2 P Tᵉ (B_{e+1}(⟨b s⟩ / T) - bᵉ⁺¹ B_{e+1}(⟨s⟩ / T)) - (e + 1) P bᵉ ⟨s⟩ᵉ (b - 1 - 2 ⌊b⟨s⟩ / T⌋)`
is an integer multiple of `T`. -/
private theorem exists_two_mul_primorial_mul_sub_eq {e : ℕ} (he : e ≠ 0) (b : ℕ) (s : ZMod T) :
    ∃ n : ℤ, 2 * primorial (e + 2) * (T : ℚ) ^ e *
        ((Polynomial.bernoulli (e + 1)).eval ((((b : ZMod T) * s).val : ℚ) / T) -
          b ^ (e + 1) * (Polynomial.bernoulli (e + 1)).eval ((s.val : ℚ) / T)) -
      (e + 1) * primorial (e + 2) * b ^ e * (s.val : ℚ) ^ e *
        (b - 1 - 2 * (b * s.val / T : ℕ)) = T * n := by
  obtain ⟨z, hz⟩ := TauCeti.exists_pow_div_mul_bernoulli_eval_val_sub_eq (k := e + 1)
    (Nat.succ_ne_zero e) b s
  have he2 : e + 1 + 1 = e + 2 := by omega
  simp only [Nat.add_sub_cancel, he2] at hz
  set q := b * s.val / T
  -- `⟨b s⟩ ≡ b ⟨s⟩` modulo `T`, hence also their `e`-th powers
  set u := ((b : ZMod T) * s).val
  have hu : (T : ℤ) ∣ u - b * s.val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [u]
  obtain ⟨w, hw⟩ := (hu.trans (sub_dvd_pow_sub_pow _ _ e))
  have hwq : (u : ℚ) ^ e - (b * s.val) ^ e = T * w := by exact_mod_cast hw
  refine ⟨2 * z + (e + 1) * primorial (e + 2) * w * (b - 1 - 2 * q), ?_⟩
  have hk : (e : ℚ) + 1 ≠ 0 := by positivity
  have hP : (primorial (e + 2) : ℚ) ≠ 0 := by exact_mod_cast primorial_ne_zero _
  push_cast at hz ⊢
  field_simp at hz
  linear_combination hz + (e + 1) * primorial (e + 2) * (b - 1 - 2 * (q : ℚ)) * hwq

/-- The twisted Stickelberger sum over the units is the sum over all residues of
`χ(s) ⟨s⟩ᵉ (2 ⌊b⟨s⟩ / T⌋ - (b - 1))`. -/
private theorem sum_units_eq_sum {O : Type*} [CommRing O] (χ : DirichletCharacter O T) {e : ℕ}
    (he : e ≠ 0) {b : ℕ} (hb : b.Coprime T) :
    ∑ t : (ZMod T)ˣ, (((b * (t : ZMod T).val / T : ℕ) : ℤ) -
        ((b * (-(t : ZMod T)).val / T : ℕ) : ℤ) : O) * (t : ZMod T).val ^ e * χ t =
      ∑ s : ZMod T, χ s * (s.val ^ e * ((2 * (b * s.val / T : ℕ) - (b - 1) : ℤ) : O)) := by
  rw [χ.sum_mul_eq_sum_units]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rcases eq_or_ne (t : ZMod T).val 0 with h0 | h0
  · simp [h0, he]
  -- for a unit `t ≠ 0`, `⟨-t⟩ = T - ⟨t⟩` and `T ∤ b ⟨t⟩`
  have hneg : (-(t : ZMod T)).val = T - (t : ZMod T).val := by
    rw [ZMod.neg_val', Nat.mod_eq_of_lt (by have := ZMod.val_lt (t : ZMod T); omega)]
  have hdvd : ¬ T ∣ b * (t : ZMod T).val := fun h ↦ by
    have h1 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.mul_right hb.symm (ZMod.val_coe_unit_coprime t).symm) h
    subst h1
    exact h0 (by rw [ZMod.val_eq_zero]; exact Subsingleton.elim _ _)
  rw [hneg, TauCeti.natCast_mul_sub_div (ZMod.val_lt _).le hdvd]
  push_cast
  ring

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra ℚ R] [Algebra O R]

/-- **Voronoi's congruence for generalized Bernoulli numbers.** Let `χ` be a Dirichlet character
modulo `T` with values in a commutative ring `O`, let `R` be a `ℚ`-algebra over `O`, let `e ≥ 1`
and let `b` be prime to `T`. With `θ_{T,b}(t) = ⌊b⟨t⟩ / T⌋ - ⌊b⟨-t⟩ / T⌋` for a unit `t` with
representative `⟨t⟩ ∈ [0, T)`, and `P_{e+2} = primorial (e + 2)`,

`P_{e+2} ((e + 1) bᵉ χ(b) ∑_t θ_{T,b}(t) ⟨t⟩ᵉ χ(t) - 2 (χ(b) bᵉ⁺¹ - 1) B_{e+1,χ})`

is an `O`-multiple of `T` in `R`, where `B_{e+1,χ}` is the generalized Bernoulli number of `χ`
with values in `R`, at the modulus `T`. No parity condition on `χ` is needed. -/
theorem primorial_mul_sub_generalizedBernoulli_mem_span (χ : DirichletCharacter O T) {e : ℕ}
    (he : e ≠ 0) {b : ℕ} (hb : b.Coprime T) :
    (primorial (e + 2) : R) * ((e + 1) * algebraMap O R (b ^ e * χ b *
        ∑ t : (ZMod T)ˣ, (((b * (t : ZMod T).val / T : ℕ) : ℤ) -
          ((b * (-(t : ZMod T)).val / T : ℕ) : ℤ) : O) * (t : ZMod T).val ^ e * χ t) -
      2 * (algebraMap O R (χ b) * b ^ (e + 1) - 1) *
        generalizedBernoulli (χ.ringHomComp (algebraMap O R)) (e + 1)) ∈
      Submodule.span O {(T : R)} := by
  set φ := algebraMap O R
  set χ' : DirichletCharacter R T := χ.ringHomComp φ
  set P := primorial (e + 2)
  set Bq : ZMod T → R := fun s ↦
    algebraMap ℚ R ((Polynomial.bernoulli (e + 1)).eval ((s.val : ℚ) / T))
  have hB : χ'.generalizedBernoulli (e + 1) = (T : R) ^ e * ∑ a : ZMod T, χ' a * Bq a := by
    rw [generalizedBernoulli_eq_pow_mul_sum_bernoulli_eval _ (by omega), Nat.add_sub_cancel]
  -- reindex the Bernoulli sum by `s ↦ b s`
  have hre : ∑ s : ZMod T, χ' ((b : ZMod T) * s) * Bq ((b : ZMod T) * s) =
      ∑ a : ZMod T, χ' a * Bq a :=
    by simpa using Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime b hb)) (fun a ↦ χ' a * Bq a)
  choose n hn using fun s ↦ exists_two_mul_primorial_mul_sub_eq (T := T) he b s
  -- the claim is the sum of the twisted congruences for one residue
  have hsum : (P : R) * ((e + 1) * φ (b ^ e * χ b *
        ∑ t : (ZMod T)ˣ, (((b * (t : ZMod T).val / T : ℕ) : ℤ) -
          ((b * (-(t : ZMod T)).val / T : ℕ) : ℤ) : O) * (t : ZMod T).val ^ e * χ t) -
      2 * (φ (χ b) * b ^ (e + 1) - 1) * χ'.generalizedBernoulli (e + 1)) =
      ∑ s : ZMod T, φ (χ ((b : ZMod T) * s) * n s) * T := by
    -- only the term `-1` of `χ(b) bᵉ⁺¹ - 1` is reindexed by `s ↦ b s`
    have hsplit : 2 * (φ (χ b) * b ^ (e + 1) - 1) * χ'.generalizedBernoulli (e + 1) =
        2 * φ (χ b) * b ^ (e + 1) * ((T : R) ^ e * ∑ a : ZMod T, χ' a * Bq a) -
          2 * ((T : R) ^ e * ∑ s : ZMod T, χ' ((b : ZMod T) * s) * Bq ((b : ZMod T) * s)) := by
      rw [hre, hB]
      ring
    rw [sum_units_eq_sum χ he hb, hsplit]
    simp only [map_mul, map_pow, map_natCast, map_sum, map_intCast, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun s _ ↦ ?_
    have h := congrArg (algebraMap ℚ R) (hn s)
    simp only [map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_add, map_one,
      map_intCast] at h
    simp only [χ', Bq, MulChar.ringHomComp_apply, Int.cast_sub, Int.cast_mul,
      Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
    linear_combination φ (χ b) * φ (χ s) * h
  rw [hsum]
  refine Submodule.sum_mem _ fun s _ ↦ ?_
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end DirichletCharacter

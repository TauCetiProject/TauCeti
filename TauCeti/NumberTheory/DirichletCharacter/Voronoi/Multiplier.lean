/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.BernoulliBounds
import TauCeti.LinearAlgebra.Matrix.GroupMatrix
import TauCeti.NumberTheory.MulChar.Basic

/-!
# A bounded multiplier for twisted Voronoi congruences

A single positive integer can supply both the factors from a smoothing parameter prime to a
prescribed prime and the scaled Bernoulli sums for all characters of the relevant parity. The
smoothing parameters are `N + 1` and `2N + 1`. The integer is a multiple of the Bernoulli group
determinant, so the Bernoulli divisibility holds in the coefficient ring itself.

The determinant method comes from `New.OddPart.exists_isStickelbergerBound` in
`grh/src/Lib/Cyclotomic/Voronoi.lean` of lsernau/grh-lean at `72fead1`.
-/

open Finset Nat

namespace TauCeti

private theorem smoothingFactors_le {N e L : ℕ} (hL : 2 * N + 1 ≤ L) :
    (((N + 1) ^ e - 1) * ((N + 1) ^ (e + 1) - 1)) *
        (((2 * N + 1) ^ e - 1) * ((2 * N + 1) ^ (e + 1) - 1)) ≤
      L ^ (2 * (e + (e + 1))) := by
  have hL' : N + 1 ≤ L := by omega
  calc
    _ ≤ (L ^ e * L ^ (e + 1)) * (L ^ e * L ^ (e + 1)) := by
      gcongr <;> exact (Nat.sub_le _ _).trans (Nat.pow_le_pow_left (by assumption) _)
    _ = _ := by simp only [← pow_add]; congr 1; omega

private theorem stickelbergerMultiplier_le (N : ℕ) [NeZero N] {e D : ℕ} (he : 0 < e)
    (hD : D ≤ (2 ^ (N + e + 3)) ^ (2 * (e + (e + 1)))) :
    D * (N * (e + 1) * (e + 2)! ^ 2) * (bernoulliGroupDet N (e + 1)).natAbs ≤
      2 ^ (N + e + 3) ^ 6 := by
  -- The positive-degree determinant estimate is the only non-elementary size input.
  let y := N + e + 3
  let L := 2 ^ y
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hy : 5 ≤ y := by dsimp [y]; omega
  have hyL : y ≤ L := y.lt_two_pow_self.le
  have h32 : 32 ≤ L := Nat.pow_le_pow_right (by decide : 0 < 2) hy
  have hNL : N ≤ L := (show N ≤ y by dsimp [y]; omega).trans hyL
  have heL : e + 2 ≤ L := (show e + 2 ≤ y by dsimp [y]; omega).trans hyL
  have hfac (j : ℕ) (hj : j ≤ L) : j ! ≤ L ^ j :=
    j.factorial_le_pow.trans (Nat.pow_le_pow_left hj _)
  have hdet : (bernoulliGroupDet N (e + 1)).natAbs ≤ (32 * N ^ (e + 2) * (e + 1)!) ^ N.totient := by
    have h := abs_bernoulliGroupDet_le (M := N) (k := e + 1) (by omega)
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hdet' : (bernoulliGroupDet N (e + 1)).natAbs ≤ L ^ ((1 + (e + 2) + (e + 1)) * N) := by
    rw [pow_mul, pow_add, pow_add, pow_one]
    refine hdet.trans ((Nat.pow_le_pow_left ?_ _).trans (Nat.pow_le_pow_right (by positivity) ?_))
    · gcongr
      exact hfac _ (by omega)
    · exact Nat.totient_le N
  have hscale : N * (e + 1) * (e + 2)! ^ 2 ≤ L ^ (2 + 2 * (e + 2)) := by
    rw [pow_add, mul_comm 2 (e + 2), pow_mul, sq L]
    gcongr
    · omega
    · exact hfac _ heL
  have hterm : (1 + (e + 2) + (e + 1)) * N ≤ 2 * y * y :=
    Nat.mul_le_mul (by dsimp [y]; omega) (by dsimp [y]; omega)
  have hE : 2 * (e + (e + 1)) + (2 + 2 * (e + 2)) + (1 + (e + 2) + (e + 1)) * N ≤ y ^ 5 := by
    calc
      _ ≤ 6 * y + 2 * y * y := by dsimp only [y] at *; omega
      _ ≤ y ^ 3 := by nlinarith [Nat.mul_le_mul_right y (show 5 ≤ y by omega),
        Nat.mul_le_mul_right (y ^ 2) (show 4 ≤ y by omega)]
      _ ≤ y ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  calc
    _ ≤ L ^ (2 * (e + (e + 1))) * L ^ (2 + 2 * (e + 2)) *
          L ^ ((1 + (e + 2) + (e + 1)) * N) := by gcongr
    _ ≤ L ^ (y ^ 5) := by
      simp only [← pow_add]
      exact Nat.pow_le_pow_right (by positivity) hE
    _ = 2 ^ y ^ 6 := by rw [show L = 2 ^ y from rfl, ← pow_mul, _root_.pow_succ' y 5]

/-- There is a positive integer at most `2 ^ (N + e + 3) ^ 6` which simultaneously:

* is divisible, for every prime `p`, by `(c ^ e - 1) * (c ^ (e + 1) - 1)` for some
  `c > 1` congruent to `1` modulo `N` and prime to `p`;
* is divisible, in every coefficient ring, by the primorial-scaled Bernoulli sum of each
  character of parity `(-1) ^ (e + 1)`, further scaled by `N * (e + 1) * (e + 2)! ^ 2`.

The factorial scale allows the Bernoulli sums with factorial rather than primorial
normalization to be used in Voronoi's congruence. -/
public theorem exists_stickelberger_multiplier (N : ℕ) [NeZero N] {e : ℕ} (he : 0 < e) :
    ∃ X : ℕ, 0 < X ∧ X ≤ 2 ^ (N + e + 3) ^ 6 ∧
      (∀ p : ℕ, p.Prime → ∃ c : ℕ, 1 < c ∧ c ≡ 1 [MOD N] ∧ c.Coprime p ∧
        (c ^ e - 1) * (c ^ (e + 1) - 1) ∣ X) ∧
      ∀ (R : Type*) [CommRing R] (χ : DirichletCharacter R N), χ (-1) = (-1) ^ (e + 1) →
        (N : R) * (e + 1 : ℕ) * ((e + 2)! : R) ^ 2 *
          (∑ u : (ZMod N)ˣ, χ u * (primorialBernoulli N (e + 1) u : R)) ∣ (X : R) := by
  let f (c : ℕ) := (c ^ e - 1) * (c ^ (e + 1) - 1)
  let D := f (N + 1) * f (2 * N + 1)
  let B := bernoulliGroupDet N (e + 1)
  let S := N * (e + 1) * (e + 2)! ^ 2
  have hN := Nat.pos_of_ne_zero (NeZero.ne N)
  have hf {c : ℕ} (hc : 1 < c) : 0 < f c := by
    exact Nat.mul_pos (Nat.sub_pos_of_lt (one_lt_pow₀ hc he.ne'))
      (Nat.sub_pos_of_lt (one_lt_pow₀ hc (by omega)))
  have hB := bernoulliGroupDet_ne_zero N (k := e + 1) (by omega)
  have hsmall : 2 * N + 1 ≤ 2 ^ (N + e + 3) := by
    rw [show N + e + 3 = (N + e + 2) + 1 by omega, _root_.pow_succ']
    have h := (N + e + 2).lt_two_pow_self
    omega
  refine ⟨D * S * B.natAbs, ?_, ?_, ?_, ?_⟩
  · have hD : 0 < D := Nat.mul_pos (hf (by omega)) (hf (by omega))
    exact Nat.mul_pos (Nat.mul_pos hD (by dsimp [S]; positivity)) (Int.natAbs_pos.mpr hB)
  · exact stickelbergerMultiplier_le N he (smoothingFactors_le hsmall)
  · intro p hp
    have hmod (a : ℕ) : a * N + 1 ≡ 1 [MOD N] := by simp [Nat.ModEq, Nat.add_mod]
    have hDX : D ∣ D * S * B.natAbs := (dvd_mul_right _ _).trans (dvd_mul_right _ _)
    by_cases h : p ∣ N + 1
    · have hcop : (N + 1).Coprime (2 * N + 1) := by
        rw [show 2 * N + 1 = N + (N + 1) by omega, Nat.coprime_add_self_right]
        simp
      have hp₂ : (2 * N + 1).Coprime p := (hp.coprime_iff_not_dvd.mpr fun h' ↦
        hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h h')).symm
      exact ⟨2 * N + 1, by omega, hmod 2, hp₂, (dvd_mul_left _ _).trans hDX⟩
    · exact ⟨N + 1, by omega, by simp [Nat.ModEq], (hp.coprime_iff_not_dvd.mpr h).symm,
        (dvd_mul_right _ _).trans hDX⟩
  · intro R _ χ hχ
    classical
    let ψ : (ZMod N)ˣ →* R := (χ : ZMod N →* R).comp (Units.coeHom (ZMod N))
    have hdiv := Matrix.sum_mul_dvd_det_of_div (fun u ↦ (bernoulliGroupEntry N (e + 1) u : R)) ψ
    rw [← intCast_bernoulliGroupDet, sum_mul_bernoulliGroupEntry] at hdiv
    simp only [ψ, MulChar.coe_comp_coeHom_apply, Units.val_neg, Units.val_one,
      hχ, sub_add_cancel] at hdiv
    have hdiv' := (dvd_mul_left _ (2 : R)).trans hdiv
    obtain ⟨z, hz⟩ := Int.dvd_natAbs.mpr (dvd_refl B)
    have habs : (B : R) ∣ (B.natAbs : R) := by
      refine ⟨z, ?_⟩
      simpa only [Int.cast_natCast, Int.cast_mul] using congrArg (fun t : ℤ ↦ (t : R)) hz
    have hscaleD : (S : R) * (B.natAbs : R) ∣ ((D * S * B.natAbs : ℕ) : R) := by
      refine ⟨D, ?_⟩
      push_cast
      ring
    simpa only [S, Nat.cast_mul, Nat.cast_pow] using
      (mul_dvd_mul_left (S : R) (hdiv'.trans habs)).trans hscaleD

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection
import TauCeti.Analysis.Asymptotics.Sum.ThresholdCount
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.OddPart
import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Jacobi
import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.ZeroDetection

/-!
# Zero density for prime quadratic twists in a fixed box

A zero of a quadratic twist by a prime `d ≡ 7 mod 8` forces a large theta tail for the
primitive twist. By quadratic reciprocity this is a Jacobi tail with numerator `-d`.
The mean bound for these tails gives a power saving in the count of bad primes, and hence
arbitrarily large primes in a reduced residue class whose twists are all zero-free in the box.

The argument follows `New.zero_density_quadTwist` and `New.exists_entireL_quadTwist_ne_zero`
in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open Asymptotics DirichletCharacter Filter
open scoped Nat

namespace TauCeti

private theorem exists_thetaTail_lt_of_mul_jacobiChar_LFunction_eq_zero
    {q d : ℕ} [NeZero q] [NeZero d] [NeZero (q.lcm d)]
    {χ : DirichletCharacter ℂ q} {s : ℂ} {T δ H : ℝ}
    (hd : d.Prime) (hd₈ : d % 8 = 7) (hc : q.Coprime d) (hT : (q : ℝ) * d ≤ T ^ 2)
    (hδ : 0 < δ) (hs : (χ.mul (jacobiChar ℂ d)).LFunction s = 0)
    (hdetect : ∀ (j : Fin 2) {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N},
      ψ.IsPrimitive → ψ ≠ 1 → ψ (-1) = (-1) ^ j.val → (N : ℝ) ≤ T ^ 2 →
      ∀ {z : ℂ}, 1 / 2 + 9 * δ ≤ z.re → |z.im| ≤ H → ψ.LFunction z = 0 →
        T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j (fun n ↦ ψ n) T)
    (hβ : 1 / 2 + 9 * δ ≤ s.re) (hH : |s.im| ≤ H) :
    ∃ j : Fin 2, T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j
      (fun n ↦ χ.primitiveCharacter n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T := by
  let : Fact d.Prime := ⟨hd⟩
  let ψ := χ.primitiveCharacter
  let η := ψ.mul (jacobiChar ℂ d)
  have hcop := hc.coprime_dvd_left χ.conductor_dvd_level
  let : NeZero (χ.conductor.lcm d) := ⟨Nat.lcm_ne_zero χ.conductor_ne_zero hd.ne_zero⟩
  have hp := isPrimitive_jacobiChar_of_odd_squarefree (R := ℂ) (by norm_num)
    (hd.odd_of_ne_two (by omega)) hd.squarefree
  have hη := χ.primitiveCharacter_isPrimitive.mul_of_coprime hp hcop
  have hη₁ : η ≠ 1 := by
    rw [ne_eq, eq_one_iff_conductor_eq_one, (isPrimitive_def _).mp hη, hcop.lcm_eq_mul]
    have hpos := Nat.pos_of_ne_zero χ.conductor_ne_zero
    exact ne_of_gt (hd.one_lt.trans_le (Nat.le_mul_of_pos_left _ hpos))
  have hre : 0 < s.re := by linarith
  have hz : η.LFunction s = 0 :=
    (χ.LFunction_mul_primitiveCharacter_eq_zero_iff (jacobiChar ℂ d) hre.ne' (.inl hη₁)).mp hs
  have hlevel : (↑(χ.conductor.lcm d) : ℝ) ≤ T ^ 2 := by
    rw [hcop.lcm_eq_mul, Nat.cast_mul]
    have hle : (χ.conductor : ℝ) ≤ q := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
    exact (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg d)).trans hT
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, η (-1) = (-1) ^ j.val := by
    rcases η.even_or_odd with he | ho
    · exact ⟨0, by simpa [DirichletCharacter.Even] using he⟩
    · exact ⟨1, by simpa [DirichletCharacter.Odd] using ho⟩
  refine ⟨j, (hdetect j hη hη₁ hj hlevel hβ hH hz).trans_le ?_⟩
  apply le_of_eq
  apply quadraticTwistGaussianThetaTailIntegral_congr _ T
  intro n
  rw [mul_natCast, jacobiChar_natCast, jacobiSym_eq_jacobiSym_neg_ordCompl_two hd₈ n.ne_zero]

/-- The number of primes up to `x` in the given class having a twist zero with real part at
least `1/2 + 9δ` and height at most `H` is `O(x^(1-δ/2))`, provided the primes in that
class are `7 mod 8` and coprime to the base modulus. -/
theorem isBigO_ncard_quadraticTwistBadPrimes {q : ℕ} [NeZero q] {a : ZMod q}
    (hclass : ∀ d : ℕ, d.Prime → (d : ZMod q) = a → d % 8 = 7 ∧ q.Coprime d)
    {δ : ℝ} (hδ : 0 < δ) (H : ℝ) :
    (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H | (d : ℝ) ≤ x}.ncard : ℝ))
      =O[atTop] (· ^ (1 - δ / 2)) := by
  let S := quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H
  let w (i : DirichletCharacter ℂ q × Fin 2) (T : ℝ) (d : ℕ) :=
    quadraticTwistGaussianThetaTailIntegral i.2
      (fun n ↦ i.1.primitiveCharacter n * jacobiSym (-(d : ℤ)) (ordCompl[2] n)) T
  have hpos : ∀ᶠ T : ℝ in atTop, ∀ i d, d ∈ Finset.Icc 1 ⌊T ^ 2⌋₊ → 0 ≤ w i T d :=
    .of_forall fun T _ _ _ ↦ quadraticTwistGaussianThetaTailIntegral_nonneg T
  obtain ⟨C, _, hC⟩ := exists_sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le hδ
  have havg (i) : (fun T : ℝ ↦ ∑ n ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, w i T n) =O[atTop] (· ^ (2 + δ)) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hsum : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, w i T n :=
      Finset.sum_nonneg fun _ _ ↦ quadraticTwistGaussianThetaTailIntegral_nonneg T
    rw [Real.norm_of_nonneg hsum, Real.norm_of_nonneg (Real.rpow_nonneg hT.le _)]
    exact hC i.2 (fun n ↦ i.1.primitiveCharacter.norm_le_one n) hT
  have h0 := eventually_rpow_lt_quadraticTwistGaussianThetaTailIntegral 0 H hδ
  have h1 := eventually_rpow_lt_quadraticTwistGaussianThetaTailIntegral 1 H hδ
  have hdet : ∀ᶠ T : ℝ in atTop, ∀ d ∈ S, 1 ≤ d → (q : ℝ) * d ≤ T ^ 2 →
      ∃ i, T ^ (2 * δ) ≤ w i T d := by
    filter_upwards [h0, h1] with T h0 h1 d hdS _ hTd
    obtain ⟨hda, hd, χ, s, hβ, hH, hs⟩ := mem_quadraticTwistBadPrimes_iff.mp hdS
    let : NeZero d := ⟨hd.ne_zero⟩
    let : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
    obtain ⟨hd₈, hc⟩ := hclass d hd hda
    obtain ⟨j, hj⟩ := exists_thetaTail_lt_of_mul_jacobiChar_LFunction_eq_zero
      hd hd₈ hc hTd hδ hs (by
        rw [Fin.forall_fin_two]
        exact ⟨@h0, @h1⟩) hβ hH
    exact ⟨(χ, j), hj.le⟩
  have hcount := S.isBigO_ncard_of_threshold_sums w q (2 + δ) (2 * δ) hpos havg hdet
  have he : (2 + δ - 2 * δ) / 2 = 1 - δ / 2 := by ring
  rw [he] at hcount
  convert hcount using 2 with x
  congr 2
  ext d
  refine ⟨fun hd ↦ ⟨hd.1, ?_, hd.2⟩, fun hd ↦ ⟨hd.1, hd.2.2⟩⟩
  obtain ⟨_, hp, _⟩ := mem_quadraticTwistBadPrimes_iff.mp hd.1
  exact hp.pos

/-- In a reduced residue class whose primes are `7 mod 8`, there are arbitrarily large primes
such that every quadratic twist of a character of the base modulus is zero-free in the box
`β ≤ Re s`, `|Im s| ≤ H`, for any `β > 1/2`. -/
theorem exists_prime_quad_twist_zero_free {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (hclass : ∀ d : ℕ, d.Prime → (d : ZMod q) = a → d % 8 = 7)
    {β : ℝ} (hβ : 1 / 2 < β) (H : ℝ) (N : ℕ) :
    ∃ d > N, ∃ hd : d.Prime, (d : ZMod q) = a ∧
      letI : NeZero d := ⟨hd.ne_zero⟩
      letI : NeZero (q.lcm d) := ⟨Nat.lcm_ne_zero (NeZero.ne q) hd.ne_zero⟩
      ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
        β ≤ s.re → |s.im| ≤ H → (χ.mul (jacobiChar ℂ d)).LFunction s ≠ 0 := by
  let δ := (β - 1 / 2) / 9
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have he : 1 / 2 + 9 * δ = β := by dsimp [δ]; ring
  have hcount := isBigO_ncard_quadraticTwistBadPrimes (a := a) (fun d hd hda ↦
    ⟨hclass d hd hda, ((ZMod.isUnit_iff_coprime d q).mp (hda ▸ ha)).symm⟩) hδ H
  rw [he] at hcount
  exact exists_prime_quad_twist_zero_free_of_density ha (by linarith) hcount N

end TauCeti

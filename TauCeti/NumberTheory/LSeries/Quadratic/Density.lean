/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail
public import TauCeti.NumberTheory.LSeries.Quadratic.TwistSelection
import Mathlib.Order.Interval.Set.Nat
import TauCeti.Analysis.Asymptotics.Sum.ThresholdCount
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Primitive
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Conductor
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.OddPart

/-!
# Counting bad quadratic twists from theta-tail estimates

A zero of a twist of an imprimitive character can be tested after replacing the character by
its primitive inducing character. For primes congruent to `7` modulo `8`, the coefficients of
that primitive twist are the Jacobi-numerator coefficients used in theta-tail mean bounds.
This links the analytic estimates for primitive characters to the set of primes used in the
zero-free twist selection theorem.

The reduction follows `New.zero_density_quadTwist` in lsernau/grh-lean (`72fead1`,
`grh/src/Lib/Analytic/QuadraticTwist.lean`).
-/

public section

open Asymptotics Filter DirichletCharacter
open scoped Nat ArithmeticFunction.Moebius

namespace TauCeti

private theorem exists_large_jacobi_tail_of_mem_badPrimes {q d : ℕ} [NeZero q]
    {a : ZMod q} {δ H T : ℝ} (hβ : 0 < 1 / 2 + 9 * δ)
    (hd : d ∈ quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H) (h₈ : d % 8 = 7)
    (hc : q.Coprime d) (hTd : (q : ℝ) * d ≤ T ^ 2)
    (hdetect : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (j : Fin 2),
      ψ.IsPrimitive → ψ ≠ 1 → ψ (-1) = (-1 : ℂ) ^ j.val → (N : ℝ) ≤ T ^ 2 →
      ∀ s : ℂ, 1 / 2 + 9 * δ ≤ s.re → |s.im| ≤ H → ψ.LFunction s = 0 →
        T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j (fun n ↦ ψ n) T) :
    ∃ (χ : DirichletCharacter ℂ q) (j : Fin 2),
      T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ χ.primitiveCharacter n * (jacobiSym (-(d : ℤ)) (ordCompl[2] n) : ℂ)) T := by
  obtain ⟨_, hp, χ, s, hs, hH, hz⟩ := mem_quadraticTwistBadPrimes_iff.mp hd
  let : NeZero d := ⟨hp.ne_zero⟩
  let N := χ.conductor.lcm d
  let : NeZero N := ⟨Nat.lcm_ne_zero (NeZero.ne _) hp.ne_zero⟩
  let ψ : DirichletCharacter ℂ N := χ.primitiveCharacter.mul (jacobiChar ℂ d)
  have hp' : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive.mul_of_coprime
    (isPrimitive_jacobiChar_of_odd_squarefree (by norm_num) (Nat.odd_iff.mpr (by omega))
      hp.squarefree) (hc.coprime_dvd_left χ.conductor_dvd_level)
  have hψ : ψ ≠ 1 := by
    intro he
    have hN : N = 1 := by
      simpa only [he, conductor_one] using ((isPrimitive_def ψ).mp hp').symm
    exact hp.not_dvd_one (hN ▸ Nat.dvd_lcm_right χ.conductor d)
  have hs₀ : s.re ≠ 0 := (hβ.trans_le hs).ne'
  have hz' : ψ.LFunction s = 0 :=
    (χ.LFunction_mul_primitiveCharacter_eq_zero_iff (jacobiChar ℂ d) hs₀ (.inl hψ)).mp hz
  have hNq : (N : ℝ) ≤ (q : ℝ) * d := by
    rw [← Nat.cast_mul]
    exact_mod_cast (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne q)) hp.pos)
      (Nat.lcm_dvd (χ.conductor_dvd_level.trans (dvd_mul_right q d)) (dvd_mul_left d q)))
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, ψ (-1) = (-1 : ℂ) ^ j.val := by
    rcases ψ.even_or_odd with he | ho
    · exact ⟨0, by simpa [DirichletCharacter.Even] using he⟩
    · exact ⟨1, by simpa [DirichletCharacter.Odd] using ho⟩
  refine ⟨χ, j, (hdetect ψ j hp' hψ hj (hNq.trans hTd) s hs hH hz').trans_le (le_of_eq ?_)⟩
  -- Both series, including the Möbius-weighted one, sum only over positive indices.
  have hcoeff (n : ℕ+) : ψ n =
      χ.primitiveCharacter n * (jacobiSym (-(d : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ) := by
    rw [mul_natCast, jacobiChar_natCast, jacobiSym_eq_jacobiSym_neg_ordCompl_two h₈ n.ne_zero]
  simp only [quadraticTwistGaussianThetaTailIntegral_def, gaussianThetaSeries_def,
    gaussianTheta_def, hcoeff]

/-- The primitive theta-tail zero detector and the mean bound for Jacobi-numerator tails
imply a power-saving count of bad primes for **all** characters of the progression modulus.
The zero detector has conductor cutoff `T²`; the counting argument uses `T = √(q X)` so
it applies to every prime up to `X`. -/
theorem isBigO_ncard_quadraticTwistBadPrimes_of_thetaTails {q : ℕ} [NeZero q]
    {a : ZMod q} {δ H : ℝ}
    (ha : ∀ {d : ℕ}, d.Prime → (d : ZMod q) = a → d % 8 = 7 ∧ q.Coprime d)
    (havg : ∀ (χ : DirichletCharacter ℂ q) (j : Fin 2),
      (fun T : ℝ ↦ ∑ d ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ χ.primitiveCharacter n * (jacobiSym (-(d : ℤ)) (ordCompl[2] n) : ℂ)) T)
        =O[atTop] (· ^ (2 + δ)))
    (hdetect : ∀ᶠ T : ℝ in atTop, ∀ {N : ℕ} [NeZero N]
      (ψ : DirichletCharacter ℂ N) (j : Fin 2),
      ψ.IsPrimitive → ψ ≠ 1 → ψ (-1) = (-1 : ℂ) ^ j.val → (N : ℝ) ≤ T ^ 2 →
      ∀ s : ℂ, 1 / 2 + 9 * δ ≤ s.re → |s.im| ≤ H → ψ.LFunction s = 0 →
        T ^ (2 * δ) < quadraticTwistGaussianThetaTailIntegral j (fun n ↦ ψ n) T) :
    (fun x : ℝ ↦ ({d ∈ quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H | (d : ℝ) ≤ x}.ncard : ℝ))
      =O[atTop] (· ^ (1 - δ / 2)) := by
  let S := quadraticTwistBadPrimes a (1 / 2 + 9 * δ) H
  have hprime {d : ℕ} (hd : d ∈ S) : d.Prime :=
    (mem_quadraticTwistBadPrimes_iff.mp hd).2.choose
  by_cases hδ : δ ≤ 0
  · -- If the exponent is at least one, count all positive integers up to `x`.
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hsub : {d ∈ S | (d : ℝ) ≤ x} ⊆ Set.Icc 1 ⌊x⌋₊ :=
      fun _ hd ↦ ⟨(hprime hd.1).one_lt.le, Nat.le_floor hd.2⟩
    have hcard := Set.ncard_le_ncard hsub (Set.finite_Icc ..)
    rw [Set.ncard_Icc_nat, Nat.add_sub_cancel] at hcard
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hexp : (1 : ℝ) ≤ 1 - δ / 2 := by linarith
    exact (Nat.cast_le.mpr hcard).trans ((Nat.floor_le (by linarith)).trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hexp))
  let w (i : DirichletCharacter ℂ q × Fin 2) (T : ℝ) (d : ℕ) :=
    quadraticTwistGaussianThetaTailIntegral i.2
      (fun n ↦ i.1.primitiveCharacter n * (jacobiSym (-(d : ℤ)) (ordCompl[2] n) : ℂ)) T
  have hcount := Set.isBigO_ncard_of_threshold_sums S w q (2 + δ) (2 * δ)
    (.of_forall fun T _ _ _ ↦ quadraticTwistGaussianThetaTailIntegral_nonneg T)
    (fun i ↦ havg i.1 i.2) (by
      filter_upwards [hdetect] with T hT d hd _ hTd
      obtain ⟨he, hp, _⟩ := mem_quadraticTwistBadPrimes_iff.mp hd
      obtain ⟨h₈, hc⟩ := ha hp he
      have hβ : 0 < 1 / 2 + 9 * δ := by linarith [lt_of_not_ge hδ]
      obtain ⟨χ, j, hj⟩ := exists_large_jacobi_tail_of_mem_badPrimes hβ hd h₈ hc hTd hT
      exact ⟨(χ, j), hj.le⟩)
  have hset (x : ℝ) : {d ∈ S | 1 ≤ d ∧ (d : ℝ) ≤ x} = {d ∈ S | (d : ℝ) ≤ x} := by
    ext d
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, (hprime h.1).one_lt.le, h.2⟩⟩
  have hexp : (2 + δ - 2 * δ) / 2 = 1 - δ / 2 := by ring
  rwa [funext (fun x ↦ congrArg (fun s : Set ℕ ↦ (s.ncard : ℝ)) (hset x)), hexp] at hcount

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
public import TauCeti.NumberTheory.NumberField.Cyclotomic.DifferentSize
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Archimedean different bounds in the quadratic cyclotomic tower

At the scale `2^s ≍ x^11`, the factor `3 l₀(s)` in the tower degree costs only `O(log x)`.
The cyclotomic derivative and the quadratic different factor therefore have product of
size between `x^10` and `x^12` at every complex embedding, uniformly in the tower level.

The interval is the one in `New.Data.hasLogBound_deltaE` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open Filter Polynomial Real Set

namespace TauCeti.OneSidedBound.Parameters

-- Compare the ternary factor with a logarithm; the dyadic factor fixes the polynomial scale.
private theorem towerDeg_bounds {x : ℝ} (hx : 2 ≤ x) {s : ℕ}
    (hlo : x ^ 11 ≤ (2 : ℝ) ^ s) (hhi : (2 : ℝ) ^ s ≤ 4 ^ 11 * x ^ 11) :
    x ^ 11 ≤ (towerDeg s : ℝ) ∧
      (towerDeg s : ℝ) ≤ (243 * (33 / log 2) * 4 ^ 11) * log x * x ^ 11 := by
  have hx₀ : 0 < x := by linarith
  have hlog : log 2 ≤ log x := log_le_log (by norm_num) hx
  have hs : s ≠ 0 := by
    intro hs
    subst s
    have h := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) hx (11 : ℕ)
    norm_num at hlo h
    linarith
  have hslog : (s : ℝ) ≤ (33 / log 2) * log x := by
    have h := log_le_log (pow_pos (by norm_num) s) hhi
    rw [log_pow, log_mul (by norm_num) (pow_ne_zero _ hx₀.ne'), log_pow, log_pow] at h
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      have hpow : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
      rw [hpow, log_pow, Nat.cast_ofNat]
    rw [h4] at h
    have h' : (s : ℝ) ≤ (33 * log x) / log 2 :=
      (le_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr (by push_cast at h; linarith)
    rwa [mul_div_right_comm] at h'
  have hl₀ : (l₀ s : ℝ) ≤ 81 * (s : ℝ) := by exact_mod_cast l₀_le hs
  have hl₁ : 1 ≤ l₀ s := by rw [l₀_def]; exact Nat.one_le_pow _ _ (by decide)
  have hl₁' : (1 : ℝ) ≤ l₀ s := by exact_mod_cast hl₁
  rw [towerDeg_def, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
  refine ⟨hlo.trans (le_mul_of_one_le_left (by positivity) (by linarith)), ?_⟩
  have hternary : 3 * (l₀ s : ℝ) ≤ 3 * (81 * ((33 / log 2) * log x)) := by
    gcongr
    exact hl₀.trans (mul_le_mul_of_nonneg_left hslog (by norm_num))
  calc
    _ ≤ (3 * (81 * ((33 / log 2) * log x))) * (4 ^ 11 * x ^ 11) :=
      mul_le_mul hternary hhi (by positivity) ((by positivity : 0 ≤ 3 * (l₀ s : ℝ)).trans hternary)
    _ = _ := by ring

/-- At all sufficiently large `x`, for any exponent with `x^11 ≤ 2^s ≤ 4^11 x^11`, the
absolute value of the cyclotomic different factor times the quadratic factor lies in
`[x^10, x^12]` at every complex embedding. A root-of-unity correction does not affect the
bound. The threshold depends only on the fixed base modulus and quadratic prime. -/
theorem eventually_norm_cyclotomic_different_factor_mem_Icc (P : Parameters) :
    ∀ᶠ x : ℝ in atTop, ∀ {s : ℕ}, x ^ 11 ≤ (2 : ℝ) ^ s → (2 : ℝ) ^ s ≤ 4 ^ 11 * x ^ 11 →
      ∀ {E : Type*} [Ring E] (σ : E →+* ℂ) {u ζ η : E},
      IsOfFinOrder u → IsPrimitiveRoot (σ ζ) (P.q₁ s) → η ^ 2 = -(P.d : E) →
      ‖σ (u * (cyclotomic (P.q₁ s) E).derivative.eval ζ * η)‖ ∈ Icc (x ^ 10) (x ^ 12) := by
  let C := ∑ w ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval w‖|
  let A₀ := exp (-C) * √(P.d : ℝ)
  let B := exp C * √(P.d : ℝ) * (243 * (33 / log 2) * 4 ^ 11)
  have hd : 0 < P.d := P.prime_d.pos
  have hA₀ : 0 < A₀ := by dsimp only [A₀]; positivity
  have hsmall := (isLittleO_log_id_atTop.const_mul_left B).bound one_pos
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop A₀⁻¹, hsmall]
    with x hx hlarge hlog s hlo hhi E _ σ u ζ η hu hζ hη
  have hsupp : (towerDeg s).primeFactors ⊆ P.q₀.primeFactors := by
    intro p hp
    obtain ⟨hp', hpd, _⟩ := Nat.mem_primeFactors.mp hp
    have hdiv : p ∣ P.q₁ s := by rw [q₁_def]; exact hpd.trans (dvd_mul_left _ _)
    exact hp'.mem_primeFactors (P.dvd_q₀_of_dvd_q₁ hp' hdiv) P.q₀_ne_zero
  have hη' : η ^ 2 = ((-(P.d : ℤ) : ℤ) : E) := by simpa using hη
  have hζ' : IsPrimitiveRoot (σ ζ) (P.q₀ * towerDeg s) := by rwa [q₁_def] at hζ
  obtain ⟨A, hA, heq, hAlog⟩ := σ.exists_pos_norm_apply_cyclotomic_different_eq
    P.q₀_ne_zero hsupp hu hζ' hη'
  have hAlog' : |log A| ≤ C := hAlog
  obtain ⟨hAlow, hAhigh⟩ := abs_le.mp hAlog'
  obtain ⟨hTlow, hThigh⟩ := towerDeg_bounds hx hlo hhi
  have hAx : 1 ≤ A₀ * x := by
    simpa only [mul_comm x A₀] using (inv_le_iff_one_le_mul₀ hA₀).mp hlarge
  have hBx : B * log x ≤ x := by
    simpa [Real.norm_of_nonneg (by linarith : 0 ≤ x)] using (le_norm_self _).trans hlog
  have hsize : ‖σ (u * (cyclotomic (P.q₁ s) E).derivative.eval ζ * η)‖ =
      A * (towerDeg s : ℝ) * √(P.d : ℝ) := by
    simpa only [q₁_def, Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) P.d)] using heq
  rw [hsize]
  constructor
  · calc
      x ^ 10 = 1 * x ^ 10 := (one_mul _).symm
      _ ≤ (A₀ * x) * x ^ 10 := by gcongr
      _ = exp (-C) * x ^ 11 * √(P.d : ℝ) := by dsimp only [A₀]; ring
      _ ≤ _ := by gcongr; exact (le_log_iff_exp_le hA).mp hAlow
  · calc
      _ ≤ exp C * ((243 * (33 / log 2) * 4 ^ 11) * log x * x ^ 11) * √(P.d : ℝ) := by
        gcongr
        exact (log_le_iff_le_exp hA).mp hAhigh
      _ = (B * log x) * x ^ 11 := by dsimp only [B]; ring
      _ ≤ x * x ^ 11 := by gcongr
      _ = x ^ 12 := by ring

end TauCeti.OneSidedBound.Parameters

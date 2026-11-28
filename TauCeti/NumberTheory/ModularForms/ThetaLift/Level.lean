/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.NumberTheory.NumberField.CMField
import TauCeti.NumberTheory.ModularForms.ThetaLift.AuxiliarySize
import TauCeti.NumberTheory.NumberField.CMField.GaussianNorm

/-!
# The logarithmic window for the level of a theta-lift chain

The level prime is chosen in a short logarithmic interval. Its lower endpoint depends on the
length of the chain, the mean of the log weights, the auxiliary level and the root discriminant.
We bound that endpoint and show how a prime-in-windows estimate supplies a level prime together
with an algebraic integer of the prescribed conjugate product.

The endpoint and the choice of a level prime follow `New.Parameters.logLevelMin` and
`New.Parameters.exists_prime_log_mem_Icc_mul_star_eq` in lsernau/grh-lean at `72fead1`.
-/

public noncomputable section

open NumberField NumberField.IsCMField Real Set

namespace TauCeti.ThetaLift

/-- The lower endpoint of the window for the logarithm of the level prime. Here `m` is the length
of the chain, `meanLogWeight` is the mean of the logarithmic weights, `M` is the auxiliary level,
`D` is the root discriminant and `L` is the logarithm of the scale. -/
def logLevelMin (m : ℕ) (meanLogWeight M D L : ℝ) : ℝ :=
  m * meanLogWeight + ((m : ℝ) - 1) * log (M * D / (2 * π)) - (15 / 2) * L

/-- The logarithmic lower endpoint in terms of the weight, auxiliary level and discriminant. -/
theorem logLevelMin_def (m : ℕ) (meanLogWeight M D L : ℝ) :
    logLevelMin m meanLogWeight M D L =
      m * meanLogWeight + ((m : ℝ) - 1) * log (M * D / (2 * π)) - (15 / 2) * L := (rfl)

/-- The lower endpoint is between `m * L` and `24 * m * L` when `2 ≤ m`, `log (2 * π) ≤ L`,
the mean log weight is in `[0,L]`, the auxiliary level is in `[exp(20L),exp(22L)]` and the
root discriminant is in `[1,exp L]`. -/
theorem logLevelMin_mem_Icc {m : ℕ} {w M D L : ℝ} (hm : 2 ≤ m) (hL : log (2 * π) ≤ L)
    (hw : w ∈ Icc 0 L) (hM : M ∈ Icc (exp (20 * L)) (exp (22 * L)))
    (hD : D ∈ Icc 1 (exp L)) : logLevelMin m w M D L ∈ Icc (m * L) (24 * m * L) := by
  have hm' : 2 ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hlo, hhi⟩ := log_M_mul_rootDiscr_div_two_pi_mem_Icc hL hM hD
  have hL₀ : 0 ≤ L := hw.1.trans hw.2
  have hm₀ : 0 ≤ (m : ℝ) - 1 := by linarith
  rw [logLevelMin_def, mem_Icc]
  constructor
  · nlinarith [mul_nonneg (Nat.cast_nonneg m) hw.1,
      mul_le_mul_of_nonneg_left hlo hm₀,
      mul_nonneg (sub_nonneg.mpr hm') hL₀]
  · nlinarith [mul_le_mul_of_nonneg_left hw.2 (Nat.cast_nonneg m),
      mul_le_mul_of_nonneg_left hhi hm₀]

/-- Choose a level prime from the available logarithmic windows of width `W`. If the lower
endpoint lies in the covered range and `W ≤ √L`, this gives a prime in the desired window of
width `√L`. The modulus is divisible by `4`, so the prime is an integral relative norm in the
CM field with the prescribed root of unity. -/
theorem exists_prime_log_mem_Icc_mul_complexConj_eq
    {E : Type*} [Field E] [CharZero E] [Algebra.IsIntegral ℚ E] [IsCMField E]
    {ζ : E} {n q : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (hn₄ : 4 ∣ n) (hq₄ : 4 ∣ q)
    {m : ℕ} {w M D L W B : ℝ} (hU : logLevelMin m w M D L ∈ Icc W B) (hwidth : W ≤ √L)
    (hwindow : ∀ U ∈ Icc W B,
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ log (p : ℝ) ∈ Icc U (U + W)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧
      log (p : ℝ) ∈ Icc (logLevelMin m w M D L) (logLevelMin m w M D L + √L) ∧
      ∃ z : 𝓞 E, z * ringOfIntegersComplexConj E z = p := by
  obtain ⟨p, hp, hpq, hpU⟩ := hwindow _ hU
  have hp₄ : p % 4 = 1 := hpq.of_dvd hq₄
  obtain ⟨a, ha⟩ := hn₄
  have hfour : IsPrimitiveRoot (ζ ^ a) 4 := hζ.pow hn (by simpa [Nat.mul_comm] using ha)
  obtain ⟨z, hz⟩ := hp.exists_mul_ringOfIntegersComplexConj_eq (by omega : p % 4 ≠ 3) hfour
  exact ⟨p, hp, hpq, ⟨hpU.1, hpU.2.trans (add_le_add_right hwidth _)⟩, z, hz⟩

end TauCeti.ThetaLift

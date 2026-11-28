/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.ConstantBound
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.DifferentSize
import TauCeti.NumberTheory.NumberField.Cyclotomic.DiscriminantFormula
import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscr

/-!
# Root discriminant normalization of the cyclotomic different

The root discriminant of the cyclotomic extension of an imaginary quadratic field grows
by exactly the tower factor. Removing this common scale from the archimedean different
expression and the root discriminant bounds their logarithmic discrepancy independently
of the tower level. This is the comparison in `New.Parameters.abs_log_deltaE_sub_log_rootDiscr_le`
in `New/Derivatives/Field/ChosenPlaces.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open Module NumberField NumberField.IsCMField Polynomial Real
open scoped NNReal

namespace TauCeti.OneSidedBound.Parameters

/-- At tower level `s`, the root discriminant is the tower degree times the root
discriminant at the base cyclotomic level times the quadratic contribution `√d`. -/
theorem rootDiscr_eq_towerDeg_mul (P : Parameters) (s : ℕ) (K E : Type*) [Field K] [Field E]
    [NumberField K] [NumberField E] [Algebra K E] [IsCyclotomicExtension {P.q₁ s} K E]
    (hK : finrank ℚ K = 2) (hd : (discr K).natAbs = P.d) :
    rootDiscr E = (towerDeg s : ℝ) * √(P.d : ℝ) * rootDiscr (CyclotomicField P.q₀ ℚ) := by
  have hcop : (discr K).natAbs.Coprime (P.q₁ s) := hd ▸ (P.coprime_q₁_d s).symm
  have hbase : rootDiscr K = √(P.d : ℝ) := by
    rw [rootDiscr_def, hK, ← Int.natCast_natAbs, hd, Int.cast_natCast, sqrt_eq_rpow]
    norm_num
  have : NeZero (towerDeg s) := ⟨(towerDeg_pos s).ne'⟩
  have : NeZero (P.q₀ : ℚ) := ⟨Nat.cast_ne_zero.mpr P.q₀_ne_zero⟩
  have : NeZero ((P.q₀ * towerDeg s : ℕ) : ℚ) :=
    ⟨Nat.cast_ne_zero.mpr (mul_ne_zero P.q₀_ne_zero (towerDeg_pos s).ne')⟩
  have hscale : rootDiscr (CyclotomicField (P.q₁ s) ℚ) =
      (towerDeg s : ℝ) * rootDiscr (CyclotomicField P.q₀ ℚ) := by
    rw [P.q₁_def]
    have : IsCyclotomicExtension {P.q₀} ℚ (CyclotomicField P.q₀ ℚ) :=
      CyclotomicField.isCyclotomicExtension P.q₀ ℚ
    have : IsCyclotomicExtension {P.q₀ * towerDeg s} ℚ (CyclotomicField (P.q₀ * towerDeg s) ℚ) :=
      CyclotomicField.isCyclotomicExtension (P.q₀ * towerDeg s) ℚ
    exact IsCyclotomicExtension.Rat.rootDiscr_mul_level_of_primeFactors_subset
      (CyclotomicField P.q₀ ℚ) (CyclotomicField (P.q₀ * towerDeg s) ℚ)
      (P.primeFactors_towerDeg_subset s)
  rw [IsCyclotomicExtension.rootDiscr_eq_mul_of_coprime_level K E (P.q₁ s) hcop, hbase, hscale]
  ring

/-- The logarithmic size of the different expression at any infinite place differs
from the logarithmic root discriminant by at most twice the fixed parameter constant.
There is no lower bound on the tower level, and no need to assume the expression
generates the different ideal to compare its size. -/
theorem abs_log_different_sub_log_rootDiscr_le (P : Parameters) (s : ℕ) (K : Type*)
    {E : Type*} [Field K] [Field E] [NumberField K] [NumberField E] [IsCMField E]
    [Algebra K E] [IsCyclotomicExtension {P.q₁ s} K E]
    (hK : finrank ℚ K = 2) (hd : (discr K).natAbs = P.d)
    (vacuumBound : ℝ≥0) (v : InfinitePlace E) {ζ u b : E}
    (hζ : IsPrimitiveRoot ζ (P.q₁ s)) (hu : u * complexConj E u = 1)
    (hb : b ^ 2 = -(P.d : E)) :
    |log (v (u * (cyclotomic (P.q₁ s) E).derivative.eval ζ * b)) - log (rootDiscr E)| ≤
      2 * P.constantBound vacuumBound := by
  let F := CyclotomicField P.q₀ ℚ
  have : NeZero (P.q₀ : ℚ) := ⟨Nat.cast_ne_zero.mpr P.q₀_ne_zero⟩
  have : IsCyclotomicExtension {P.q₀} ℚ F := CyclotomicField.isCyclotomicExtension P.q₀ ℚ
  have hF : 1 ≤ rootDiscr F := by
    have h : (1 : ℤ) ≤ |discr F| := abs_pos.mpr (discr_ne_zero F)
    rw [rootDiscr_def, Int.cast_abs]
    exact one_le_rpow (by exact_mod_cast h) (by positivity)
  have hlogF : |log (rootDiscr F)| ≤ P.constantBound vacuumBound := by
    rw [abs_of_nonneg (log_nonneg hF)]
    calc
      _ ≤ log (P.q₀ : ℝ) := log_le_log (by linarith) (IsCyclotomicExtension.Rat.rootDiscr_le _ F)
      _ ≤ P.q₀ := by linarith [log_le_sub_one_of_pos (Nat.cast_pos.mpr P.q₀_pos)]
      _ ≤ _ := (le_max_right _ _).trans ((le_max_right (64 : ℝ) _).trans
        (P.max_le_constantBound vacuumBound))
  obtain ⟨A, hA, hv, hlogA⟩ := P.exists_pos_apply_different_generator s v hζ hu hb rfl
  have hscale : (towerDeg s : ℝ) * √(P.d : ℝ) ≠ 0 := by
    have := towerDeg_pos s
    have := P.prime_d.pos
    positivity
  rw [hv, mul_assoc A, P.rootDiscr_eq_towerDeg_mul s K E hK hd,
    log_mul hA.ne' hscale, log_mul hscale (by linarith : rootDiscr F ≠ 0)]
  have hcancel (a b c : ℝ) : a + b - (b + c) = a - c := by ring
  rw [hcancel]
  calc
    _ ≤ |log A| + |log (rootDiscr F)| := abs_sub _ _
    _ ≤ _ := by
      have := hlogA.trans
        (P.sum_abs_log_norm_eval_cyclotomic_derivative_le_constantBound vacuumBound)
      linarith

end TauCeti.OneSidedBound.Parameters

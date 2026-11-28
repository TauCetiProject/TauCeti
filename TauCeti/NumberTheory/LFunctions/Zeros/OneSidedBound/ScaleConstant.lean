/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.DifferentSize
public import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char

/-!
# A fixed scale constant for the one-sided prime sum bound

Before choosing the cutoffs, collect the quadratic logarithmic derivative at one, the
cyclotomic derivative sizes at the base level, and the vacuum bound into one real constant.
The same constant controls the arithmetic parameters and the error in the placewise size
of a different generator, uniformly through the cyclotomic tower.

The normalization is that of `New.Parameters.constantBound` in
`grh/src/New/Reduction/Data/AdmissibleData.lean` of lsernau/grh-lean (revision `72fead1`). The
placewise bound uses `Parameters.exists_pos_apply_different_generator`.
-/

public section

open NumberField NumberField.IsCMField Polynomial Real

namespace TauCeti.OneSidedBound.Parameters

/-- The fixed scale constant for parameters `P`. The input `cVac` is a bound for the vacuum
contribution. The remaining terms depend only on the base modulus and the twisting prime. -/
noncomputable def constantBound (P : Parameters) (cVac : ℝ) : ℝ :=
  cVac + (2 * (P.d : ℝ) + 6) + P.q₀ +
    |eulerMascheroniConstant - (logDeriv (jacobiChar ℂ P.d).LFunction 1).re| +
    ∑ z ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval z‖|

/-- Expand the scale constant into its vacuum, arithmetic, and logarithmic contributions. -/
theorem constantBound_def (P : Parameters) (cVac : ℝ) :
    P.constantBound cVac = cVac + (2 * (P.d : ℝ) + 6) + P.q₀ +
      |eulerMascheroniConstant - (logDeriv (jacobiChar ℂ P.d).LFunction 1).re| +
      ∑ z ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval z‖| := (rfl)

/-- The scale constant majorizes the modulus, its totient, the twisting prime and `64`. -/
theorem max_le_constantBound (P : Parameters) {cVac : ℝ} (hcVac : 0 ≤ cVac) :
    max (max 64 (P.q₀ : ℝ)) (max (P.d : ℝ) (P.q₀.totient : ℝ)) ≤ P.constantBound cVac := by
  have hq : (18480 : ℝ) ≤ P.q₀ := by exact_mod_cast P.le_q₀
  have hφ : (P.q₀.totient : ℝ) ≤ P.q₀ := by exact_mod_cast Nat.totient_le P.q₀
  have hD : 0 ≤ ∑ z ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval z‖| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  rw [constantBound_def, max_le_iff, max_le_iff, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith [Nat.cast_nonneg (α := ℝ) P.d,
    abs_nonneg (eulerMascheroniConstant - (logDeriv (jacobiChar ℂ P.d).LFunction 1).re)]

/-- The scale constant bounds the logarithmic contribution from the quadratic L-function
and Euler's constant, which together determine the archimedean scale for the lifts. -/
theorem abs_eulerMascheroniConstant_sub_re_logDeriv_le_constantBound
    (P : Parameters) {cVac : ℝ} (hcVac : 0 ≤ cVac) :
    |eulerMascheroniConstant - (logDeriv (jacobiChar ℂ P.d).LFunction 1).re| ≤
      P.constantBound cVac := by
  have hD : 0 ≤ ∑ z ∈ primitiveRoots P.q₀ ℂ, |log ‖(cyclotomic P.q₀ ℂ).derivative.eval z‖| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  rw [constantBound_def]
  linarith [Nat.cast_nonneg (α := ℝ) P.d, Nat.cast_nonneg (α := ℝ) P.q₀]

/-- The scale separation imposed on the large integral cutoff bounds the scale constant
by the logarithm of the cutoff. This estimate does not need the vacuum budget to be nonnegative. -/
theorem constantBound_le_log (P : Parameters) {cVac : ℝ} {b : ℕ}
    (hb : 10 ^ 12 * P.constantBound cVac ≤ log (log b)) : P.constantBound cVac ≤ log b := by
  by_contra! h
  have hlog : 0 ≤ log (b : ℝ) := log_natCast_nonneg b
  have hC : 0 < P.constantBound cVac := hlog.trans_lt h
  rcases hlog.eq_or_lt with hz | hp
  · rw [← hz, log_zero] at hb
    linarith
  · linarith [log_le_sub_one_of_pos hp]

/-- At each infinite place the logarithmic size of the cyclotomic different expression
`u * Φ′(ζ) * b`, where `u` has norm one and `b² = -d`, differs from `log (T * √d)` by at most
the scale constant, uniformly in the tower exponent. -/
theorem abs_log_apply_different_sub_le_constantBound (P : Parameters) (s : ℕ)
    {E : Type*} [Field E] [CharZero E] [IsCMField E] [Algebra.IsIntegral ℚ E]
    (v : InfinitePlace E) {ζ u b : E} (hζ : IsPrimitiveRoot ζ (P.q₁ s))
    (hu : u * complexConj E u = 1) (hb : b ^ 2 = -(P.d : E)) {cVac : ℝ} (hcVac : 0 ≤ cVac) :
    |log (v (u * (cyclotomic (P.q₁ s) E).derivative.eval ζ * b)) -
      log ((towerDeg s : ℝ) * √(P.d : ℝ))| ≤ P.constantBound cVac := by
  obtain ⟨A, hA, hv, hlog⟩ := P.exists_pos_apply_different_generator s v hζ hu hb rfl
  have hscale : 0 < (towerDeg s : ℝ) * √(P.d : ℝ) :=
    mul_pos (by exact_mod_cast towerDeg_pos s) (sqrt_pos.2 (by exact_mod_cast P.prime_d.pos))
  rw [hv, mul_assoc, log_mul hA.ne' hscale.ne', add_sub_cancel_right]
  refine hlog.trans ?_
  rw [constantBound_def]
  linarith [Nat.cast_nonneg (α := ℝ) P.d, Nat.cast_nonneg (α := ℝ) P.q₀,
    abs_nonneg (eulerMascheroniConstant - (logDeriv (jacobiChar ℂ P.d).LFunction 1).re)]

end TauCeti.OneSidedBound.Parameters

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Polynomial

/-!
# Finite measure API for the Chebyshev `T` weight

This file records the finite-measure bookkeeping for Mathlib's Chebyshev
orthogonality measure `Polynomial.Chebyshev.measureT`, together with the
single normalization constant used by the roadmap's Chebyshev Hilbert-basis
target.

The main facts are that `measureT` has total mass `π`, hence is finite and
nonzero, and that the existing Mathlib orthogonality lemmas combine into one
Kronecker-delta statement with squared norms `π` in degree zero and `π / 2` in
positive degree.  The file also records `L²` membership of the normalized `T`
modes and the finite exponential moments used by the later Chebyshev
Hilbert-basis construction.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial.Chebyshev

open scoped ENNReal

/-- The Chebyshev `T` orthogonality measure has total mass `π`. -/
lemma chebyshevMeasureT_univ :
    Polynomial.Chebyshev.measureT Set.univ = ENNReal.ofReal Real.pi := by
  have h := integral_eval_T_real_measureT_zero
  have hreal : Polynomial.Chebyshev.measureT.real Set.univ = Real.pi := by
    simpa using h
  have hfinite : Polynomial.Chebyshev.measureT Set.univ ≠ ∞ := by
    intro htop
    have hzero : Polynomial.Chebyshev.measureT.real Set.univ = 0 := by
      simp [Measure.real, htop]
    linarith [hreal, Real.pi_pos]
  rw [← MeasureTheory.ofReal_measureReal (μ := Polynomial.Chebyshev.measureT)
    (s := Set.univ) hfinite, hreal]

/-- Mathlib's Chebyshev `T` orthogonality measure is finite. -/
noncomputable instance chebyshevMeasureT.instIsFiniteMeasure :
    IsFiniteMeasure Polynomial.Chebyshev.measureT where
  measure_univ_lt_top := by
    rw [chebyshevMeasureT_univ]
    exact ENNReal.ofReal_lt_top

/-- The Chebyshev `T` orthogonality measure has positive total mass. -/
lemma chebyshevMeasureT_univ_pos : 0 < Polynomial.Chebyshev.measureT Set.univ := by
  rw [chebyshevMeasureT_univ]
  exact ENNReal.ofReal_pos.mpr Real.pi_pos

/-- Mathlib's Chebyshev `T` orthogonality measure is nonzero. -/
lemma chebyshevMeasureT_ne_zero : Polynomial.Chebyshev.measureT ≠ 0 :=
  Measure.measure_univ_pos.mp chebyshevMeasureT_univ_pos

/-- The squared `L²(measureT)` norm of the `n`th Chebyshev `T` polynomial. -/
noncomputable def chebyshevTNormSq (n : ℕ) : ℝ :=
  if n = 0 then Real.pi else Real.pi / 2

@[simp]
lemma chebyshevTNormSq_zero : chebyshevTNormSq 0 = Real.pi := by
  simp [chebyshevTNormSq]

@[simp]
lemma chebyshevTNormSq_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    chebyshevTNormSq n = Real.pi / 2 := by
  simp [chebyshevTNormSq, hn]

/-- The squared norm constant for Chebyshev `T` polynomials is positive. -/
lemma chebyshevTNormSq_pos (n : ℕ) : 0 < chebyshevTNormSq n := by
  by_cases hn : n = 0
  · simp [hn, Real.pi_pos]
  · rw [chebyshevTNormSq_of_ne_zero hn]
    positivity

/-- The squared norm constant for Chebyshev `T` polynomials is nonzero. -/
lemma chebyshevTNormSq_ne_zero (n : ℕ) : chebyshevTNormSq n ≠ 0 :=
  ne_of_gt (chebyshevTNormSq_pos n)

/-- The diagonal Chebyshev `T` orthogonality integral, with the degree-zero and
positive-degree cases hidden behind one normalization constant. -/
lemma integral_eval_T_real_mul_self_measureT (n : ℕ) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      chebyshevTNormSq n := by
  by_cases hn : n = 0
  · subst hn
    exact integral_eval_T_real_mul_self_measureT_zero
  · rw [chebyshevTNormSq_of_ne_zero hn]
    exact integral_T_real_mul_self_measureT_of_ne_zero hn

/-- Chebyshev `T` orthogonality in the Kronecker-delta form expected by the
general orthogonality-to-Hilbert-basis bridge. -/
lemma integral_eval_T_real_mul_eval_T_real_measureT_eq_ite (m n : ℕ) :
    ∫ x, (T ℝ m).eval x * (T ℝ n).eval x ∂Polynomial.Chebyshev.measureT =
      if m = n then chebyshevTNormSq n else 0 := by
  by_cases hmn : m = n
  · subst hmn
    simp [integral_eval_T_real_mul_self_measureT]
  · simp [hmn, integral_eval_T_real_mul_eval_T_real_measureT_of_ne hmn]

/-! ### Exponential-moment consumer form -/

/-- The Chebyshev `T` orthogonality measure has all exponential absolute
moments. -/
lemma integrable_exp_mul_abs_measureT (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) Polynomial.Chebyshev.measureT := by
  exact integrable_measureT (by fun_prop)

/-! ### `L²` consumer forms -/

/-- The real normalized Chebyshev `T` mode lies in `L²(measureT)`. -/
lemma memLp_normalized_eval_T_real_measureT (n : ℕ) :
    MemLp (fun x : ℝ => (T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n)) 2
      Polynomial.Chebyshev.measureT := by
  have hcont : Continuous fun x : ℝ =>
      (T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n) :=
    (T ℝ n).continuous.div_const _
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  exact integrable_measureT (hcont.pow 2).continuousOn

/-- The scalar-cast normalized Chebyshev `T` mode lies in `L²(measureT)`, in
the form consumed by the family-generic orthogonality-to-Hilbert-basis bridge. -/
lemma memLp_algebraMap_normalized_eval_T_real_measureT {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    MemLp (fun x : ℝ =>
        (algebraMap ℝ 𝕜) ((T ℝ n).eval x / Real.sqrt (chebyshevTNormSq n))) 2
      Polynomial.Chebyshev.measureT := by
  simpa only [← RCLike.algebraMap_eq_ofReal] using
    (memLp_normalized_eval_T_real_measureT n).ofReal (K := 𝕜)

end TauCeti

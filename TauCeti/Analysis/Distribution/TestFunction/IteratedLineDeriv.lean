/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
public import TauCeti.Analysis.Distribution.TestFunction.Schwartz

/-!
# Iterated directional derivatives of test functions

For directions `m : Fin k → E`, the iterated directional derivative `∂^{m} φ` of a test function
`φ` commutes with the inclusion of test functions in Schwartz space
(`TestFunction.toSchwartzMapCLM_iteratedLineDerivOp`) and with postcomposition by a continuous
linear map (`TestFunction.iteratedLineDerivOp_postcompCLM`), for instance with the embedding of
real test functions into complex ones.

Integrating by parts `k` times moves the derivatives from one test function to the other, in
reverse order and with the sign `(-1) ^ k`: for a continuous bilinear map `L`,

`∫ L (∂^{m} u) φ = (-1) ^ k ∫ L u (∂^{m ∘ rev} φ)`

(`TestFunction.integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right`). This is
the identity behind the formal adjoint `∑ᵢ (-1) ^ kᵢ ∂^{mᵢ ∘ rev} (bᵢ† φ)` of a differential
operator `∑ᵢ bᵢ ∂^{mᵢ}`.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions LineDeriv

namespace TestFunction

open LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Opens E}

/-- The inclusion of test functions in Schwartz space commutes with iterated directional
derivatives. -/
@[simp]
theorem toSchwartzMapCLM_iteratedLineDerivOp {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F] {k : ℕ}
    (m : Fin k → E) (φ : 𝓓(Ω, F)) :
    toSchwartzMapCLM 𝕜 (∂^{m} φ) = ∂^{m} (toSchwartzMapCLM 𝕜 φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, toSchwartzMapCLM_lineDerivOp,
      ih]

/-- Iterated directional derivatives of test functions commute with postcomposition by a
continuous linear map. -/
theorem iteratedLineDerivOp_postcompCLM {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Algebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] {F' : Type*} [NormedAddCommGroup F']
    [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [IsScalarTower ℝ 𝕜 F'] (L : F →L[𝕜] F') {k : ℕ}
    (m : Fin k → E) (φ : 𝓓(Ω, F)) :
    ∂^{m} (postcompCLM L φ) = postcompCLM L (∂^{m} φ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left, ih,
      lineDerivOp_eq_lineDerivCLM 𝕜, lineDerivOp_eq_lineDerivCLM 𝕜, lineDerivCLM_postcompCLM]

/-- Reversing `m : Fin (k + 1) → E` and dropping its last entry is reversing the tail of `m`. -/
private theorem init_comp_rev {α : Type*} {k : ℕ} (m : Fin (k + 1) → α) :
    Fin.init (m ∘ Fin.rev) = Fin.tail m ∘ Fin.rev := by
  funext i
  simp [Fin.init, Fin.tail, Fin.rev_castSucc]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure] {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Iterated integration by parts for test functions.** For a continuous bilinear map `L`,
`∫ L (∂^{m} u) φ = (-1) ^ k ∫ L u (∂^{m ∘ rev} φ)`: the `k` derivatives move to `φ` in reverse
order, each with a minus sign. -/
theorem integral_bilinear_iteratedLineDerivOp_left_eq_neg_one_pow_smul_right
    (L : F →L[ℝ] G →L[ℝ] H) {k : ℕ} (m : Fin k → E) (u : 𝓓(Ω, F)) (φ : 𝓓(Ω, G)) :
    ∫ x, L ((∂^{m} u) x) (φ x) ∂μ = (-1 : ℝ) ^ k • ∫ x, L (u x) ((∂^{m ∘ Fin.rev} φ) x) ∂μ := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    -- One integration by parts in the direction `m 0`, on the Schwartz functions of `u` and `φ`.
    have hstep : ∫ x, L ((∂_{m 0} (∂^{Fin.tail m} u)) x) (φ x) ∂μ =
        -∫ x, L ((∂^{Fin.tail m} u) x) ((∂_{m 0} φ) x) ∂μ := by
      have h := SchwartzMap.integral_bilinear_lineDerivOp_right_eq_neg_left (μ := μ)
        (toSchwartzMapCLM ℝ (∂^{Fin.tail m} u)) (toSchwartzMapCLM ℝ φ) L (m 0)
      rw [← toSchwartzMapCLM_lineDerivOp, ← toSchwartzMapCLM_lineDerivOp] at h
      simp only [toSchwartzMapCLM_apply] at h
      rw [h, neg_neg]
    rw [iteratedLineDerivOp_succ_left m u, hstep, ih, iteratedLineDerivOp_succ_right (m ∘ Fin.rev),
      init_comp_rev, Function.comp_apply, Fin.rev_last, pow_succ, mul_neg_one, neg_smul]

end TestFunction

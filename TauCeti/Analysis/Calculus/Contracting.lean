/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Smooth dependence of fixed points of contractions

For nonzero regularity `n`, a jointly `C^n` family of contractions has a `C^n` fixed point.
The contraction constants
may depend on the parameter: only the constant at the base parameter enters the inverse
function argument. This is useful for integral-equation constructions with auxiliary
parameters, such as families of invariant graphs.
-/

public section

open Filter Function Topology
open scoped ContDiff NNReal

namespace ContractingWith

variable {𝕜 E X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  {F : E → X → X} {c : E → ℝ≥0} (hF : ∀ p, ContractingWith (c p) (F p))
  {p₀ : E} {n : ℕ∞ω} {σ : E → X}

include hF

/-- A family of fixed points of jointly `C^n` contractions is `C^n` in the parameter.
No uniform bound on the contraction constants away from the base parameter is needed. -/
theorem contDiffAt_of_isFixedPt (hσ : ∀ p, IsFixedPt (F p) (σ p)) (hn : n ≠ 0)
    (h : ContDiffAt 𝕜 n (uncurry F) (p₀, σ p₀)) : ContDiffAt 𝕜 n σ p₀ := by
  let x₀ := σ p₀
  let G : E × X → X := fun z ↦ z.2 - F z.1 z.2
  have hG : ContDiffAt 𝕜 n G (p₀, x₀) := contDiffAt_snd.sub h
  have hslice : HasFDerivAt (F p₀)
      (fderiv 𝕜 (uncurry F) (p₀, x₀) ∘L ContinuousLinearMap.inr 𝕜 E X) x₀ :=
    (h.differentiableAt hn).hasFDerivAt.comp x₀
      ((hasFDerivAt_const p₀ x₀).prodMk (hasFDerivAt_id x₀))
  have hnorm : ‖fderiv 𝕜 (uncurry F) (p₀, x₀) ∘L
      ContinuousLinearMap.inr 𝕜 E X‖ < 1 :=
    (hslice.le_of_lipschitz (hF p₀).2).trans_lt (hF p₀).1
  have hpartial : fderiv 𝕜 G (p₀, x₀) ∘L ContinuousLinearMap.inr 𝕜 E X =
      1 - fderiv 𝕜 (uncurry F) (p₀, x₀) ∘L ContinuousLinearMap.inr 𝕜 E X := by
    have hd : HasFDerivAt G
        (ContinuousLinearMap.snd 𝕜 E X - fderiv 𝕜 (uncurry F) (p₀, x₀)) (p₀, x₀) :=
      hasFDerivAt_snd.sub (h.differentiableAt hn).hasFDerivAt
    rw [hd.fderiv]
    ext v
    simp
  have hinv : (fderiv 𝕜 G (p₀, x₀) ∘L ContinuousLinearMap.inr 𝕜 E X).IsInvertible := by
    rw [hpartial]
    exact ⟨ContinuousLinearEquiv.ofUnit (isUnit_one_sub_of_norm_lt_one hnorm).unit, rfl⟩
  have hzero : G (p₀, x₀) = 0 := sub_eq_zero.mpr (hσ p₀).symm
  apply (hG.contDiffAt_implicitFunction hn hinv).congr_of_eventuallyEq
  filter_upwards [hG.eventually_apply_implicitFunction hn hinv] with p hp
  exact (hF p).fixedPoint_unique' (hσ p) (sub_eq_zero.mp (hp.trans hzero)).symm

end ContractingWith

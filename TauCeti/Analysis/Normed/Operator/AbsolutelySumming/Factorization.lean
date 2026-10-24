/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
public import TauCeti.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Pietsch factorization

Let `1 ≤ p < ∞` and let `B` be the closed unit ball of the dual of `E`, with its weak-star
topology. For a finite Borel measure `ν` on `B`, evaluation gives the canonical operator
`jₚ : E →L[𝕜] Lᵖ(ν)`, `x ↦ (f ↦ f x)`, written `WeakDual.evalLp p ν`; its norm at `x` is
`(∫ |f x|ᵖ dν(f))^(1/p)`, and it is a contraction when `ν` is a probability measure.

In these terms, Pietsch domination says that `πₚ(T) ≤ C` exactly when `‖T x‖ ≤ C ‖jₚ x‖` for
some regular Borel probability measure `ν` on `B`. Such a bound is the same as a factorization of
`T` through `jₚ`:

* for any normed target `F`, `πₚ(T) ≤ C` iff `T = S ∘ jₚ` for some `ν` and some operator `S` of
  norm at most `C` on the canonical image `range jₚ ⊆ Lᵖ(ν)`;
* for a Banach target `F`, `πₚ(T) ≤ C` iff the same holds with `S` defined on the closure of
  `range jₚ` in `Lᵖ(ν)`.

## Main declarations

* `WeakDual.evalLp`: the canonical operator `jₚ : E →L[𝕜] Lᵖ(ν)`.
* `WeakDual.norm_evalLp_apply`: `‖jₚ x‖ = (∫ |f x|ᵖ dν(f))^(1/p)`.
* `ContinuousLinearMap.summingENorm_le_ofReal_iff_exists_norm_le_mul_norm_evalLp`: Pietsch
  domination stated with `jₚ`.
* `ContinuousLinearMap.summingENorm_le_ofReal_iff_exists_eq_comp_rangeRestrict`: Pietsch
  factorization through the canonical image.
* `ContinuousLinearMap.summingENorm_le_ofReal_iff_exists_eq_comp_codRestrict_topologicalClosure`:
  Pietsch factorization through the closure of the canonical image, for a Banach target.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 8.2.8.
* J. Diestel, H. Jarchow and A. Tonge, *Absolutely Summing Operators*, Theorem 2.13.
-/

public section

noncomputable section

open Metric MeasureTheory
open scoped ENNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [MeasurableSpace (WeakDual 𝕜 E)] [BorelSpace (WeakDual 𝕜 E)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace WeakDual

section evalLp

variable (ν : Measure (toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1)) [IsFiniteMeasure ν]

variable (p) in
/-- The canonical operator `jₚ : E →L[𝕜] Lᵖ(ν)` sending `x` to the class of `f ↦ f x`, for a
finite measure `ν` on the weak-star closed unit ball of the dual. -/
def evalLp : E →L[𝕜] Lp 𝕜 p ν :=
  (ContinuousMap.toLp p ν 𝕜).comp (evalClosedBall 1)

/-- The canonical operator `jₚ` sends `x` to the class of the evaluation `f ↦ f x`. -/
theorem coeFn_evalLp (x : E) : evalLp p ν x =ᵐ[ν] fun f ↦ (f : WeakDual 𝕜 E) x := by
  rw [evalLp, ContinuousLinearMap.comp_apply]
  exact (ContinuousMap.coeFn_toLp ν _).trans
    (.of_eq (funext fun f ↦ evalClosedBall_apply_apply 1 x f))

/-- The `Lᵖ` norm of `jₚ x` is `(∫ |f x|ᵖ dν(f))^(1/p)`. -/
theorem norm_evalLp_apply (hp : p ≠ ∞) (x : E) :
    ‖evalLp p ν x‖ = (∫ f, ‖(f : WeakDual 𝕜 E) x‖ ^ p.toReal ∂ν) ^ (1 / p.toReal) := by
  have hp0 : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  have hmem : MemLp (fun f : toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1 ↦
      (f : WeakDual 𝕜 E) x) p ν :=
    (Lp.memLp (evalLp p ν x)).ae_eq (coeFn_evalLp ν x)
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_evalLp ν x),
    hmem.eLpNorm_eq_integral_rpow_norm hp0 hp, ENNReal.toReal_ofReal (by positivity), one_div]

/-- For a probability measure `ν`, the canonical operator `jₚ` is a contraction. -/
theorem norm_evalLp_le [IsProbabilityMeasure ν] : ‖(evalLp p ν : E →L[𝕜] Lp 𝕜 p ν)‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc
    _ ≤ (1 : ℝ) * 1 := by
      gcongr
      · have h1 : measureUnivNNReal ν = 1 := by simp [measureUnivNNReal]
        simpa [h1] using ContinuousMap.toLp_norm_le (E := 𝕜) (p := p) (𝕜 := 𝕜) ν
      · exact norm_evalClosedBall_le zero_le_one
    _ = 1 := one_mul 1

end evalLp

end WeakDual

namespace ContinuousLinearMap

section Domination

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch domination** in terms of the canonical operator `jₚ : E →L[𝕜] Lᵖ(ν)`: for
`1 ≤ p < ∞` and `C ≥ 0`, `πₚ(T) ≤ C` iff `‖T x‖ ≤ C ‖jₚ x‖` for all `x`, for some regular Borel
probability measure `ν` on the weak-star compact dual unit ball. -/
theorem summingENorm_le_ofReal_iff_exists_norm_le_mul_norm_evalLp (hp : p ≠ ∞)
    {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1))
        (_ : IsProbabilityMeasure ν), ν.Regular ∧
          ∀ x, ‖T x‖ ≤ C * ‖WeakDual.evalLp p ν x‖ := by
  simp only [WeakDual.norm_evalLp_apply _ hp, summingENorm_le_ofReal_iff_exists_isProbabilityMeasure
    hp hC, exists_prop]

end Domination

section Factorization

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch factorization** through the canonical image: for `1 ≤ p < ∞` and `C ≥ 0`,
`πₚ(T) ≤ C` iff there are a regular Borel probability measure `ν` on the weak-star compact dual
unit ball and an operator `S` of norm at most `C` on the canonical image `range jₚ ⊆ Lᵖ(ν)` such
that `T = S ∘ jₚ`. -/
theorem summingENorm_le_ofReal_iff_exists_eq_comp_rangeRestrict (hp : p ≠ ∞)
    {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1))
        (_ : IsProbabilityMeasure ν), ν.Regular ∧
          ∃ S : LinearMap.range (WeakDual.evalLp p ν : E →ₗ[𝕜] Lp 𝕜 p ν) →L[𝕜] F,
            ‖S‖ ≤ C ∧ T = S.comp (WeakDual.evalLp p ν).rangeRestrict := by
  simp only [summingENorm_le_ofReal_iff_exists_norm_le_mul_norm_evalLp hp hC,
    exists_eq_comp_rangeRestrict_iff hC]

/-- **Pietsch factorization** through the closure of the canonical image: for a Banach space `F`,
`1 ≤ p < ∞` and `C ≥ 0`, `πₚ(T) ≤ C` iff there are a regular Borel probability measure `ν` on the
weak-star compact dual unit ball and an operator `S` of norm at most `C` on the closure of
`range jₚ` in `Lᵖ(ν)` such that `T = S ∘ jₚ`. -/
theorem summingENorm_le_ofReal_iff_exists_eq_comp_codRestrict_topologicalClosure
    [CompleteSpace F] (hp : p ≠ ∞) {T : E →L[𝕜] F} {C : ℝ} (hC : 0 ≤ C) :
    T.summingENorm p ≤ ENNReal.ofReal C ↔
      ∃ (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) 1))
        (_ : IsProbabilityMeasure ν), ν.Regular ∧
          ∃ S : (LinearMap.range (WeakDual.evalLp p ν : E →ₗ[𝕜] Lp 𝕜 p ν)).topologicalClosure
              →L[𝕜] F,
            ‖S‖ ≤ C ∧ T = S.comp ((WeakDual.evalLp p ν).codRestrict _ fun x ↦
              Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)) := by
  simp only [summingENorm_le_ofReal_iff_exists_norm_le_mul_norm_evalLp hp hC,
    exists_eq_comp_codRestrict_topologicalClosure_iff hC]

end Factorization

end ContinuousLinearMap

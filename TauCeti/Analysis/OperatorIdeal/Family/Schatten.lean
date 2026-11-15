/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge
public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Lp
public import TauCeti.Analysis.OperatorIdeal.Family.Carrier

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import TauCeti.Analysis.MeanInequalities

/-!
# Finite-exponent Schatten operator ideals

The Schatten family for a finite real exponent `p ≥ 1` is the operator-ideal family
induced by the ℓᵖ symmetric gauge. Its gauge on a bounded map `T` between real or complex
Hilbert spaces is `(∑' n, aₙ(T)^p)^(1/p)`, where `aₙ` are the zero-based approximation
numbers. In particular, membership is equivalent to summability of their `p`-th powers.

The family inherits the triangle inequality, homogeneity, domination of the operator norm,
two-sided ideal inequalities and adjoint invariance from the symmetric-gauge construction.
Its normed carriers are complete, since the gauge is lower semicontinuous in operator norm.

The Schatten gauges decrease as the exponent grows, because `ℓᵖ` norms do; hence the Schatten
ideals increase with `p`, `S_p ⊆ S_q` for `1 ≤ p ≤ q`. The endpoints `p = 1` and `p = 2` are the
trace-class and Hilbert–Schmidt families, and the operator-norm family is the endpoint `p = ∞`
(`TauCeti.SymmetricGauge.operatorIdealFamily_supGauge`).

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open scoped ENNReal NNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

/-- The Schatten `p` operator-ideal family, induced by the ℓᵖ symmetric gauge. -/
noncomputable def schatten (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    OperatorIdealFamily.{u, v, w} 𝕜 :=
  (SymmetricGauge.lpGauge p hp).operatorIdealFamily 𝕜

/-- The Schatten `p` family is the family induced by the ℓᵖ symmetric gauge. -/
theorem schatten_def (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    schatten.{u, v, w} 𝕜 p hp = (SymmetricGauge.lpGauge p hp).operatorIdealFamily 𝕜 := by
  rw [schatten]

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The Schatten gauge is the ℓᵖ sum of the approximation numbers, with value `∞`
when that power sum diverges. -/
@[simp]
theorem gauge_schatten (p : ℝ) (hp : 1 ≤ p) (T : E →L[𝕜] F) :
    (schatten 𝕜 p hp).gauge T = (∑' n, (T.singularValue n : ℝ≥0∞) ^ p) ^ (1 / p) := by
  rw [schatten, SymmetricGauge.operatorIdealFamily_gauge, SymmetricGauge.opGauge_def,
    SymmetricGauge.extend_lpGauge]

/-- An operator belongs to the Schatten `p` ideal exactly when the `p`-th powers of its
approximation numbers are summable. -/
theorem mem_finiteSubmodule_schatten_iff (p : ℝ) (hp : 1 ≤ p) (T : E →L[𝕜] F) :
    T ∈ ((schatten 𝕜 p hp).operatorGauge E F).finiteSubmodule ↔
      Summable (fun n ↦ T.singularValue n ^ p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply, gauge_schatten, lt_top_iff_ne_top,
    ne_eq, ENNReal.rpow_eq_top_iff_of_pos (one_div_pos.mpr hp0)]
  simp_rw [← ENNReal.coe_rpow_of_nonneg _ hp0.le]
  exact ENNReal.tsum_coe_ne_top_iff_summable

/-- The Schatten gauge is lower semicontinuous in the operator-norm topology. -/
theorem lowerSemicontinuous_gauge_schatten (p : ℝ) (hp : 1 ≤ p) :
    LowerSemicontinuous fun T : E →L[𝕜] F ↦ (schatten 𝕜 p hp).gauge T := by
  simp only [gauge_schatten]
  exact ENNReal.continuous_rpow_const.comp_lowerSemicontinuous
    (lowerSemicontinuous_tsum fun n ↦
      (ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_coe.comp
          (ContinuousLinearMap.continuous_singularValue n))).lowerSemicontinuous)
    (fun _ _ h ↦ ENNReal.rpow_le_rpow h (by positivity))

/-- **Monotonicity of the Schatten scale.** For `1 ≤ p ≤ q`, the Schatten `q` gauge of an operator
is at most its Schatten `p` gauge. -/
theorem gauge_schatten_le_of_le {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q)
    (T : E →L[𝕜] F) : (schatten 𝕜 q hq).gauge T ≤ (schatten 𝕜 p hp).gauge T := by
  simpa only [gauge_schatten] using
    ENNReal.Lq_le_Lp_tsum (fun n ↦ (T.singularValue n : ℝ≥0∞)) (zero_lt_one.trans_le hp) hpq

variable (E F) in
/-- **Inclusion of Schatten ideals.** For `1 ≤ p ≤ q`, every operator in the Schatten `p` ideal
lies in the Schatten `q` ideal. -/
theorem finiteSubmodule_schatten_le_of_le {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p ≤ q) :
    ((schatten 𝕜 p hp).operatorGauge E F).finiteSubmodule ≤
      ((schatten 𝕜 q hq).operatorGauge E F).finiteSubmodule := by
  intro T hT
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply] at hT ⊢
  exact (gauge_schatten_le_of_le hp hq hpq T).trans_lt hT

/-- Every finite-exponent Schatten ideal has complete normed carriers. -/
instance schatten_isComplete (p : ℝ) (hp : 1 ≤ p) :
    (schatten.{u, v, w} 𝕜 p hp).IsComplete :=
  isComplete_of_lowerSemicontinuous fun _ _ _ _ _ _ _ _ ↦
    lowerSemicontinuous_gauge_schatten p hp

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

/-- The adjoint-invariant diagonal-universe Schatten `p` family. -/
noncomputable def schatten (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 :=
  (SymmetricGauge.lpGauge p hp).symmetricOperatorIdealFamily 𝕜

/-- The underlying rectangular family of the symmetric Schatten family. -/
@[simp]
theorem schatten_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] (p : ℝ) (hp : 1 ≤ p) :
    (schatten.{u, v} 𝕜 p hp).toOperatorIdealFamily =
      OperatorIdealFamily.schatten.{u, v, v} 𝕜 p hp :=
  (SymmetricGauge.lpGauge p hp).symmetricOperatorIdealFamily_toOperatorIdealFamily 𝕜

end SymmetricOperatorIdealFamily

end TauCeti

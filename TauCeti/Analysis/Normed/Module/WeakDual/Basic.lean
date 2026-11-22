/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous functions on weak-star dual balls

Banach–Alaoglu makes every closed dual ball `WeakDual.closedBall 𝕜 E r` compact in the weak-star
topology, and evaluation `(x, φ) ↦ φ x` is jointly continuous on `E × WeakDual.closedBall 𝕜 E r`.
The norm of evaluation, raised to a nonnegative exponent, is a continuous real-valued function on
such a ball (`WeakDual.evalRpow`). This bundled function supplies the integrand in Pietsch
domination.

Evaluation at a vector is itself a continuous function on such a ball, and
`WeakDual.evalClosedBall` bundles `x ↦ (φ ↦ φ x)` as a bounded operator from `E` into the
continuous functions on the ball of radius `r`, of norm at most `r`. On the unit ball it is the
canonical map of `E` into `C(B, 𝕜)` through which Pietsch factorization passes to `Lᵖ`.

## Main declarations

* `WeakDual.closedBall`: the weak-star closed ball around `0` of radius `r`, with
  `WeakDual.closedBall_def`, `WeakDual.isClosed_closedBall'`, `WeakDual.isBounded_closedBall'`,
  and `WeakDual.isCompact_closedBall'`.
* `WeakDual.mem_closedBall_iff`, `WeakDual.norm_toStrongDual_le_of_mem_closedBall`,
  `WeakDual.norm_apply_le_of_mem_closedBall`: membership and norm bounds on `WeakDual.closedBall`.
* `WeakDual.continuous_eval_closedBall`: joint evaluation continuity on `E × WeakDual.closedBall`.
* `WeakDual.evalRpow`: the continuous function `φ ↦ ‖φ x‖ ^ p` on `WeakDual.closedBall`.
* `WeakDual.evalClosedBall`: the canonical evaluation operator
  `E →L[𝕜] C(WeakDual.closedBall 𝕜 E r, 𝕜)`.
-/

public section

open scoped ENNReal

namespace WeakDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (𝕜 E) in
/-- The weak-star closed dual ball of radius `r` around `0`, as a set in `WeakDual 𝕜 E`. -/
noncomputable def closedBall (r : ℝ) : Set (WeakDual 𝕜 E) :=
  toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r

variable (𝕜 E) in
/-- `WeakDual.closedBall 𝕜 E r` is the preimage of `Metric.closedBall (0 : StrongDual 𝕜 E) r`
under `WeakDual.toStrongDual`. -/
theorem closedBall_def (r : ℝ) :
    closedBall 𝕜 E r = toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r := by
  rw [closedBall]

@[simp]
theorem mem_closedBall_iff {r : ℝ} {φ : WeakDual 𝕜 E} :
    φ ∈ closedBall 𝕜 E r ↔ ‖toStrongDual φ‖ ≤ r := by
  simp [closedBall]

/-- Elements of `WeakDual.closedBall 𝕜 E r` have operator norm at most `r`. -/
theorem norm_toStrongDual_le_of_mem_closedBall {r : ℝ} (φ : closedBall 𝕜 E r) :
    ‖toStrongDual (φ : WeakDual 𝕜 E)‖ ≤ r :=
  mem_closedBall_iff.1 φ.property

/-- On `WeakDual.closedBall 𝕜 E r`, evaluation at `x` has norm at most `r * ‖x‖`. -/
theorem norm_apply_le_of_mem_closedBall {r : ℝ} (φ : closedBall 𝕜 E r) (x : E) :
    ‖(φ : WeakDual 𝕜 E) x‖ ≤ r * ‖x‖ :=
  (toStrongDual (φ : WeakDual 𝕜 E)).le_of_opNorm_le (norm_toStrongDual_le_of_mem_closedBall φ) x

variable (𝕜 E) in
/-- The weak-star closed dual ball `WeakDual.closedBall 𝕜 E r` is weak-star closed. -/
theorem isClosed_closedBall' (r : ℝ) : IsClosed (closedBall 𝕜 E r) :=
  isClosed_closedBall (0 : StrongDual 𝕜 E) r

variable (𝕜 E) in
/-- The weak-star closed dual ball `WeakDual.closedBall 𝕜 E r` is bounded in `WeakDual 𝕜 E`. -/
theorem isBounded_closedBall' (r : ℝ) :
    Bornology.IsBounded (closedBall 𝕜 E r) :=
  isBounded_closedBall (0 : StrongDual 𝕜 E) r

variable (𝕜 E) in
/-- The weak-star closed dual ball `WeakDual.closedBall 𝕜 E r` is compact by Banach–Alaoglu. -/
theorem isCompact_closedBall' [ProperSpace 𝕜] (r : ℝ) : IsCompact (closedBall 𝕜 E r) :=
  isCompact_closedBall (0 : StrongDual 𝕜 E) r

/-- A closed dual ball, with its weak-star topology, is compact by Banach–Alaoglu. -/
instance [ProperSpace 𝕜] (f : StrongDual 𝕜 E) (r : ℝ) :
    CompactSpace (toStrongDual ⁻¹' Metric.closedBall f r : Set (WeakDual 𝕜 E)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall f r)

/-- The weak-star closed dual ball `WeakDual.closedBall 𝕜 E r` is compact by Banach–Alaoglu. -/
instance [ProperSpace 𝕜] (r : ℝ) : CompactSpace (closedBall 𝕜 E r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall' 𝕜 E r)

/-- Joint evaluation `(x, φ) ↦ φ x` is continuous on `E × WeakDual.closedBall 𝕜 E r`: closed dual
balls are equicontinuous. -/
theorem continuous_eval_closedBall (r : ℝ) :
    Continuous (fun p : E × closedBall 𝕜 E r ↦ (p.2 : WeakDual 𝕜 E) p.1) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, φ₀⟩
  rw [ContinuousAt, nhds_prod_eq, Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := max r 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hx : {x : E | dist x x₀ < ε / (2 * M)} ∈ nhds x₀ :=
    Metric.ball_mem_nhds x₀ (div_pos hε (by positivity))
  have hφ_cont : Continuous (fun φ : closedBall 𝕜 E r ↦ (φ : WeakDual 𝕜 E) x₀) :=
    (eval_continuous x₀).comp continuous_subtypeVal
  have hφ : {φ : closedBall 𝕜 E r |
      dist ((φ : WeakDual 𝕜 E) x₀) ((φ₀ : WeakDual 𝕜 E) x₀) < ε / 2} ∈ nhds φ₀ :=
    (Metric.tendsto_nhds.1 hφ_cont.continuousAt) (ε / 2) (half_pos hε)
  filter_upwards [Filter.prod_mem_prod hx hφ] with ⟨x, φ⟩ ⟨hx', hφ'⟩
  have hdiff : (φ : WeakDual 𝕜 E) x - (φ₀ : WeakDual 𝕜 E) x₀ =
      (φ : WeakDual 𝕜 E) (x - x₀) + ((φ : WeakDual 𝕜 E) x₀ - (φ₀ : WeakDual 𝕜 E) x₀) := by
    rw [map_sub]
    abel
  rw [dist_eq_norm, hdiff]
  calc
    ‖(φ : WeakDual 𝕜 E) (x - x₀) + ((φ : WeakDual 𝕜 E) x₀ - (φ₀ : WeakDual 𝕜 E) x₀)‖
        ≤ ‖(φ : WeakDual 𝕜 E) (x - x₀)‖ +
          ‖(φ : WeakDual 𝕜 E) x₀ - (φ₀ : WeakDual 𝕜 E) x₀‖ := norm_add_le _ _
    _ ≤ r * ‖x - x₀‖ + dist ((φ : WeakDual 𝕜 E) x₀) ((φ₀ : WeakDual 𝕜 E) x₀) := by
      rw [dist_eq_norm ((φ : WeakDual 𝕜 E) x₀)]
      gcongr
      exact norm_apply_le_of_mem_closedBall φ (x - x₀)
    _ ≤ M * dist x x₀ + dist ((φ : WeakDual 𝕜 E) x₀) ((φ₀ : WeakDual 𝕜 E) x₀) := by
      rw [dist_eq_norm x x₀]
      gcongr
      exact le_max_left r 1
    _ < M * (ε / (2 * M)) + ε / 2 :=
      add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx'.le hM.le) hφ'
    _ = ε := by
      field_simp [hM.ne']
      ring

/-- The continuous function `φ ↦ ‖φ x‖ ^ p` on the weak-star closed ball of radius `r`. -/
noncomputable def evalRpow (r : ℝ) (p : ℝ≥0∞) (x : E) :
    C(closedBall 𝕜 E r, ℝ) where
  toFun φ := ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal
  continuous_toFun :=
    ((eval_continuous x).comp continuous_subtypeVal).norm.rpow_const
      fun _ ↦ Or.inr ENNReal.toReal_nonneg

@[simp]
theorem evalRpow_apply (r : ℝ) (p : ℝ≥0∞) (x : E) (φ : closedBall 𝕜 E r) :
    evalRpow r p x φ = ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal := by
  simp [evalRpow]

variable [ProperSpace 𝕜]

/-- Evaluation `x ↦ (φ ↦ φ x)`, as a bounded operator from `E` into the continuous functions on
the weak-star closed dual ball of radius `r`. -/
noncomputable def evalClosedBall (r : ℝ) : E →L[𝕜] C(closedBall 𝕜 E r, 𝕜) :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun φ ↦ (φ : WeakDual 𝕜 E) x, (eval_continuous x).comp continuous_subtypeVal⟩
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
    (max r 0) fun x ↦ (ContinuousMap.norm_le _ (by positivity)).2 fun φ ↦
      ((toStrongDual (φ : WeakDual 𝕜 E)).le_opNorm x).trans <| by
        gcongr
        exact (norm_toStrongDual_le_of_mem_closedBall φ).trans (le_max_left r 0)

@[simp]
theorem evalClosedBall_apply_apply (r : ℝ) (x : E) (φ : closedBall 𝕜 E r) :
    evalClosedBall r x φ = (φ : WeakDual 𝕜 E) x := by
  simp [evalClosedBall]

/-- Evaluation on the dual ball of radius `r ≥ 0` has operator norm at most `r`. -/
theorem norm_evalClosedBall_le {r : ℝ} (hr : 0 ≤ r) :
    ‖(evalClosedBall r : E →L[𝕜] C(closedBall 𝕜 E r, 𝕜))‖ ≤ r := by
  rw [evalClosedBall]
  exact (LinearMap.mkContinuous_norm_le _ (le_max_right r 0) _).trans_eq (max_eq_left hr)

end WeakDual

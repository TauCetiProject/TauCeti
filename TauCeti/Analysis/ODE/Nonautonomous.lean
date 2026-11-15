/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.ODE.Gronwall.TwoSided
import TauCeti.MeasureTheory.Integral.Cosh

/-!
# Global solutions of nonautonomous globally Lipschitz ODEs

Let `E` be a real Banach space and `v : ℝ → E → E` be a time-dependent vector field that is
continuous in time at each fixed state (`∀ x, Continuous (v · x)`) and Lipschitz in the spatial
variable uniformly in time (`∀ t, LipschitzWith K (v t)`). Joint continuity on `ℝ × E` follows
automatically from `continuous_prod_of_continuous_lipschitzWith'`. Unlike
`TauCeti.timeDependentFlow`, no Lipschitz regularity in the time variable is assumed, so `v` may be
driven by a merely continuous path `w : ℝ → E` (such as a Brownian trajectory in an additive-noise
integral equation `X t = x + w t + ∫_0^t F (X s) ds`, reduced by `Z = X - w` to
`Z' t = F (Z t + w t)`).

This file constructs the unique global solution `ODE.nonautonomousSolution v hvc hv t₀ x : ℝ → E`
with prescribed value `x` at initial time `t₀`. When `t ↦ v t x` is bounded on the whole line, the
weighted Picard operator on `ℝ →ᵇ E` with weight `cosh (2 k t)` is a global contraction with factor
`1 / 2`. For general continuous time dependence, clamping time to `[-R, R]` via `Set.projIcc`
produces a bounded-in-time field whose global solutions agree on `(-min R₁ R₂, min R₁ R₂)` by
`ODE_solution_unique_of_mem_Ioo`, and evaluating at radius `|t| + 1` yields a global solution on
`ℝ`.

## Main declarations

* `ODE.nonautonomousSolution`: the unique solution on `ℝ` of `γ' t = v t (γ t)` with `γ t₀ = x`.
* `ODE.hasDerivAt_nonautonomousSolution` and `ODE.nonautonomousSolution_self`: it solves the
  initial value problem.
* `ODE.nonautonomousSolution_eq_integral`: the integral equation from `t₀` to `t`.
* `ODE.eqOn_nonautonomousSolution_of_hasDerivWithinAt` and `ODE.eq_nonautonomousSolution`:
  finite-interval and global uniqueness.
* `ODE.nonautonomousSolution_eq_of_eqOn`: finite-interval congruence in the vector field.
* `ODE.nonautonomousSolution_trans`: two-time evolution composition law.
* `ODE.dist_nonautonomousSolution_le`: two-sided exponential Grönwall bound in the initial state.
* `ODE.continuous_nonautonomousSolution`: joint continuity in `(t₀, x, t)`.

## References

* J. Dieudonné, *Foundations of Modern Analysis*, Academic Press, 1969, Chapter X.
-/

public section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction NNReal

namespace ODE

variable {E : Type*}

section BoundedTime

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Curve carried by a bounded continuous profile `u` with weight `cosh (2 k t)`. -/
private noncomputable def nonautCurve (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) : E :=
  x + Real.cosh (2 * k * t) • u t

private theorem continuous_nonautCurve (k : ℝ) (x : E) (u : ℝ →ᵇ E) :
    Continuous (nonautCurve k x u) := by
  have hu : Continuous (⇑u) := u.continuous
  unfold nonautCurve
  fun_prop

private theorem norm_nonautCurve_sub_le (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖nonautCurve k x u t - x‖ ≤ Real.cosh (2 * k * t) * ‖u‖ := by
  simp only [nonautCurve, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (Real.cosh_pos _).le]
  exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) (Real.cosh_pos _).le

private theorem nonautCurve_sub (k : ℝ) (x : E) (u₁ u₂ : ℝ →ᵇ E) (t : ℝ) :
    nonautCurve k x u₁ t - nonautCurve k x u₂ t = Real.cosh (2 * k * t) • (u₁ t - u₂ t) := by
  simp [nonautCurve, smul_sub]

/-- Plain function underlying the weighted Picard map for a time-dependent vector field. -/
private noncomputable def nonautPicardMap (v : ℝ → E → E) (k : ℝ) (x : E) (u : ℝ →ᵇ E) (t : ℝ) :
    E :=
  (Real.cosh (2 * k * t))⁻¹ • ∫ s in (0 : ℝ)..t, v s (nonautCurve k x u s)

private theorem continuous_nonautPicardMap {v : ℝ → E → E} (hvc : Continuous (Function.uncurry v))
    (k : ℝ) (x : E) (u : ℝ →ᵇ E) : Continuous (nonautPicardMap v k x u) := by
  have hcomp : Continuous fun s : ℝ ↦ v s (nonautCurve k x u s) :=
    hvc.comp (continuous_id.prodMk (continuous_nonautCurve k x u))
  have hint : Continuous fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, v s (nonautCurve k x u s) :=
    intervalIntegral.continuous_primitive (fun a b ↦ hcomp.intervalIntegrable a b) 0
  have hinv : Continuous fun t : ℝ ↦ (Real.cosh (2 * k * t))⁻¹ :=
    Continuous.inv₀ (by fun_prop) fun _ ↦ (Real.cosh_pos _).ne'
  exact hinv.smul hint

private theorem norm_nonautPicardMap_le {v : ℝ → E → E} {k M : ℝ} (hk : 0 < k)
    (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) {x : E} (hx : ∀ s, ‖v s x‖ ≤ M)
    (u : ℝ →ᵇ E) (t : ℝ) :
    ‖nonautPicardMap v k x u t‖ ≤ (M + k * ‖u‖) / (2 * k) := by
  have hM : 0 ≤ M := (norm_nonneg (v 0 x)).trans (hx 0)
  have hCnn : (0 : ℝ) ≤ M + k * ‖u‖ := by positivity
  have hbound : ∀ s : ℝ,
      ‖v s (nonautCurve k x u s)‖ ≤ (M + k * ‖u‖) * Real.cosh (2 * k * s) := by
    intro s
    have h1 : ‖v s (nonautCurve k x u s) - v s x‖ ≤ k * (Real.cosh (2 * k * s) * ‖u‖) :=
      (hv s _ _).trans (mul_le_mul_of_nonneg_left (norm_nonautCurve_sub_le k x u s) hk.le)
    have h2 := norm_sub_norm_le (v s (nonautCurve k x u s)) (v s x)
    have h3 : (1 : ℝ) ≤ Real.cosh (2 * k * s) := Real.one_le_cosh _
    have h4 := hx s
    nlinarith [norm_nonneg u, hk.le, mul_nonneg hk.le (norm_nonneg u)]
  have hstep : ‖∫ s in (0 : ℝ)..t, v s (nonautCurve k x u s)‖ ≤
      (M + k * ‖u‖) * Real.cosh (2 * k * t) / (2 * k) :=
    (TauCeti.norm_intervalIntegral_le_cosh (by positivity) hCnn t (.of_forall hbound)).trans_eq
      (by rw [abs_of_pos (by positivity)])
  have hcosh : (0 : ℝ) < Real.cosh (2 * k * t) := Real.cosh_pos _
  rw [nonautPicardMap, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcosh),
    inv_mul_le_iff₀ hcosh]
  refine hstep.trans_eq ?_
  field_simp

private noncomputable def nonautPicardOp {v : ℝ → E → E} (hvc : Continuous (Function.uncurry v))
    {k M : ℝ} (hk : 0 < k) (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖)
    {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (u : ℝ →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nonautPicardMap v k x u)
    (continuous_nonautPicardMap hvc k x u) _ (norm_nonautPicardMap_le hk hv hx u)

private theorem nonautPicardOp_apply {v : ℝ → E → E} (hvc : Continuous (Function.uncurry v))
    {k M : ℝ} (hk : 0 < k) (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖)
    {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (u : ℝ →ᵇ E) (t : ℝ) :
    nonautPicardOp hvc hk hv hx u t = nonautPicardMap v k x u t :=
  rfl

private theorem contractingWith_nonautPicardOp {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {k M : ℝ} (hk : 0 < k)
    (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) :
    ContractingWith (1 / 2 : ℝ≥0) (nonautPicardOp hvc hk hv hx) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u₁ u₂ ↦ ?_⟩
  have hcast : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  rw [hcast, BoundedContinuousFunction.dist_le (by positivity)]
  intro t
  have hcosh : (0 : ℝ) < Real.cosh (2 * k * t) := Real.cosh_pos _
  have hi₁ : ∀ a b : ℝ, IntervalIntegrable (fun s ↦ v s (nonautCurve k x u₁ s)) volume a b :=
    fun a b ↦ (hvc.comp (continuous_id.prodMk (continuous_nonautCurve k x u₁))).intervalIntegrable
      a b
  have hi₂ : ∀ a b : ℝ, IntervalIntegrable (fun s ↦ v s (nonautCurve k x u₂ s)) volume a b :=
    fun a b ↦ (hvc.comp (continuous_id.prodMk (continuous_nonautCurve k x u₂))).intervalIntegrable
      a b
  have hbound : ∀ s : ℝ, ‖v s (nonautCurve k x u₁ s) - v s (nonautCurve k x u₂ s)‖ ≤
      k * dist u₁ u₂ * Real.cosh (2 * k * s) := by
    intro s
    refine (hv s _ _).trans ?_
    rw [nonautCurve_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _),
      ← dist_eq_norm, ← mul_assoc, mul_right_comm k (Real.cosh _)]
    gcongr
    exact u₁.dist_coe_le_dist s
  have hsub : ∫ s in (0 : ℝ)..t, (v s (nonautCurve k x u₁ s) - v s (nonautCurve k x u₂ s)) =
      (∫ s in (0 : ℝ)..t, v s (nonautCurve k x u₁ s)) -
        ∫ s in (0 : ℝ)..t, v s (nonautCurve k x u₂ s) :=
    intervalIntegral.integral_sub (hi₁ 0 t) (hi₂ 0 t)
  have hint := TauCeti.norm_intervalIntegral_le_cosh
    (F := fun s ↦ v s (nonautCurve k x u₁ s) - v s (nonautCurve k x u₂ s))
    (by positivity) (mul_nonneg hk.le dist_nonneg) t (.of_forall hbound)
  rw [hsub, abs_of_pos (by positivity)] at hint
  rw [dist_eq_norm, nonautPicardOp_apply, nonautPicardOp_apply, nonautPicardMap, nonautPicardMap,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcosh), inv_mul_le_iff₀ hcosh]
  refine hint.trans_eq ?_
  field_simp

variable [CompleteSpace E]

private noncomputable def nonautFixedPoint {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {k M : ℝ} (hk : 0 < k)
    (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) : ℝ →ᵇ E :=
  ContractingWith.fixedPoint _ (contractingWith_nonautPicardOp hvc hk hv hx)

private theorem nonautCurve_fixedPoint {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {k M : ℝ} (hk : 0 < k)
    (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (t : ℝ) :
    nonautCurve k x (nonautFixedPoint hvc hk hv hx) t =
      x + ∫ s in (0 : ℝ)..t, v s (nonautCurve k x (nonautFixedPoint hvc hk hv hx) s) := by
  have hfix : nonautPicardOp hvc hk hv hx (nonautFixedPoint hvc hk hv hx) =
      nonautFixedPoint hvc hk hv hx :=
    ContractingWith.fixedPoint_isFixedPt _
  have hpt := congrArg (fun w : ℝ →ᵇ E ↦ w t) hfix
  simp only [nonautPicardOp_apply, nonautPicardMap] at hpt
  rw [nonautCurve, ← hpt, smul_inv_smul₀ (Real.cosh_pos (2 * k * t)).ne']

/-- Global solution at initial time `0` when `s ↦ v s x` is bounded on `ℝ`. -/
private noncomputable def boundedTimeSolution {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) : ℝ → E :=
  nonautCurve ((K : ℝ) + 1) x
    (nonautFixedPoint hvc (by positivity)
      (fun s ↦ ((hv s).weaken (le_add_of_nonneg_right zero_le_one)).norm_sub_le) hx)

private theorem boundedTimeSolution_eq_integral {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (t : ℝ) :
    boundedTimeSolution hvc hv hx t =
      x + ∫ s in (0 : ℝ)..t, v s (boundedTimeSolution hvc hv hx s) :=
  nonautCurve_fixedPoint _ _ _ hx t

private theorem boundedTimeSolution_zero {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) :
    boundedTimeSolution hvc hv hx 0 = x := by
  simpa using boundedTimeSolution_eq_integral hvc hv hx 0

private theorem hasDerivAt_boundedTimeSolution {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (t : ℝ) :
    HasDerivAt (boundedTimeSolution hvc hv hx)
      (v t (boundedTimeSolution hvc hv hx t)) t := by
  have hcont : Continuous (boundedTimeSolution hvc hv hx) := continuous_nonautCurve _ _ _
  have hcomp : Continuous fun s : ℝ ↦ v s (boundedTimeSolution hvc hv hx s) :=
    hvc.comp (continuous_id.prodMk hcont)
  have hprim : HasDerivAt
      (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, v s (boundedTimeSolution hvc hv hx s))
      (v t (boundedTimeSolution hvc hv hx t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hcomp.intervalIntegrable _ _)
      (hcomp.stronglyMeasurableAtFilter _ _) hcomp.continuousAt
  exact (hprim.const_add x).congr_of_eventuallyEq
    (.of_forall fun r ↦ boundedTimeSolution_eq_integral hvc hv hx r)

/-- Time-dependent vector field clamped to `[-R, R]` via `Set.projIcc`. -/
private noncomputable def clampedField (v : ℝ → E → E) {R : ℝ} (hR : 0 ≤ R) (s : ℝ) (y : E) : E :=
  v (Set.projIcc (-R) R (neg_le_self hR) s) y

/-- Clamping time to `[-R, R]` produces a bounded-in-time field agreeing with `v` on `[-R, R]`. -/
private noncomputable def clampedSolution {v : ℝ → E → E}
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {R : ℝ} (hR : 0 ≤ R) (x : E) : ℝ → E :=
  boundedTimeSolution
    (continuous_prod_of_continuous_lipschitzWith' (Function.uncurry (clampedField v hR)) K
      (fun s ↦ hv (Set.projIcc (-R) R (neg_le_self hR) s))
      fun y ↦ (hvc y).comp (continuous_subtype_val.comp continuous_projIcc))
    (fun s ↦ hv (Set.projIcc (-R) R (neg_le_self hR) s))
    (M := ‖BoundedContinuousFunction.mkOfCompact ⟨fun t : Icc (-R) R ↦ v t x,
      (hvc x).comp continuous_subtype_val⟩‖)
    fun s ↦ (BoundedContinuousFunction.mkOfCompact ⟨fun t : Icc (-R) R ↦ v t x,
      (hvc x).comp continuous_subtype_val⟩).norm_coe_le_norm
        (Set.projIcc (-R) R (neg_le_self hR) s)

private theorem clampedSolution_zero {v : ℝ → E → E}
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {R : ℝ} (hR : 0 ≤ R) (x : E) : clampedSolution hvc hv hR x 0 = x := by
  unfold clampedSolution
  exact boundedTimeSolution_zero _ _ _

private theorem hasDerivAt_clampedSolution_of_mem_Ioo {v : ℝ → E → E}
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {R : ℝ} (hR : 0 ≤ R) (x : E) {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    HasDerivAt (clampedSolution hvc hv hR x) (v t (clampedSolution hvc hv hR x t)) t := by
  unfold clampedSolution
  have hproj : clampedField v hR t = v t := by
    ext y
    simp [clampedField, Set.projIcc_of_mem (neg_le_self hR) (Ioo_subset_Icc_self ht)]
  rw [← hproj]
  exact hasDerivAt_boundedTimeSolution _ _ _ t

private theorem clampedSolution_eq_of_abs_lt {v : ℝ → E → E}
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (x : E) {t : ℝ}
    (ht₁ : |t| < R₁) (ht₂ : |t| < R₂) :
    clampedSolution hvc hv hR₁.le x t = clampedSolution hvc hv hR₂.le x t := by
  set r := min R₁ R₂
  have hr : 0 < r := lt_min hR₁ hR₂
  have htr : t ∈ Ioo (-r) r := abs_lt.1 (lt_min ht₁ ht₂)
  have h0r : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  exact ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ ↦ univ) (K := K)
    (fun s _ ↦ (hv s).lipschitzOnWith) h0r
    (fun s hs ↦ ⟨hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR₁.le x
      ⟨(neg_le_neg (min_le_left _ _)).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩, trivial⟩)
    (fun s hs ↦ ⟨hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR₂.le x
      ⟨(neg_le_neg (min_le_right _ _)).trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩, trivial⟩)
    ((clampedSolution_zero hvc hv hR₁.le x).trans (clampedSolution_zero hvc hv hR₂.le x).symm)
    htr

/-- Global solution at initial time `0` without boundedness in time. -/
private noncomputable def nonautonomousZero (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (x : E) (t : ℝ) : E :=
  clampedSolution hvc hv (by positivity : (0 : ℝ) ≤ |t| + 1) x t

private theorem nonautonomousZero_zero (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (x : E) : nonautonomousZero v hvc hv x 0 = x :=
  clampedSolution_zero hvc hv _ x

private theorem hasDerivAt_nonautonomousZero (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (x : E) (t : ℝ) :
    HasDerivAt (nonautonomousZero v hvc hv x) (v t (nonautonomousZero v hvc hv x t)) t := by
  set R : ℝ := |t| + 2
  have hR : 0 < R := by positivity
  have htR : t ∈ Ioo (-R) R := abs_lt.1 (by linarith : |t| < |t| + 2)
  have hEq : nonautonomousZero v hvc hv x =ᶠ[𝓝 t] clampedSolution hvc hv hR.le x := by
    filter_upwards [Ioo_mem_nhds htR.1 htR.2] with s hs
    exact clampedSolution_eq_of_abs_lt hvc hv (by positivity) hR x
      (lt_add_one |s|) (abs_lt.2 hs)
  have hEqPt : nonautonomousZero v hvc hv x t = clampedSolution hvc hv hR.le x t :=
    hEq.eq_of_nhds
  rw [hEqPt]
  exact (hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR.le x htR).congr_of_eventuallyEq hEq

end BoundedTime

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The global solution of a nonautonomous globally Lipschitz ODE.** For a vector field
`v : ℝ → E → E` that is continuous in time at each fixed state and `K`-Lipschitz in `E` uniformly
in time, `ODE.nonautonomousSolution v hvc hv t₀ x` is the unique curve `γ : ℝ → E` on the whole
real line satisfying `γ t₀ = x` and `γ' t = v t (γ t)` for every `t : ℝ`. -/
noncomputable def nonautonomousSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x : E) (t : ℝ) : E :=
  nonautonomousZero (fun s y ↦ v (t₀ + s) y)
    (fun y ↦ (hvc y).comp (continuous_const.add continuous_id))
    (fun s ↦ hv (t₀ + s)) x (t - t₀)

/-- The nonautonomous global solution takes the prescribed value at the initial time. -/
@[simp]
theorem nonautonomousSolution_self (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x : E) :
    nonautonomousSolution v hvc hv t₀ x t₀ = x := by
  rw [nonautonomousSolution, sub_self]
  exact nonautonomousZero_zero _ _ _ _

/-- **The nonautonomous global solution solves the differential equation** at every time. -/
theorem hasDerivAt_nonautonomousSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (nonautonomousSolution v hvc hv t₀ x)
      (v t (nonautonomousSolution v hvc hv t₀ x t)) t := by
  have h := (hasDerivAt_nonautonomousZero (fun s y ↦ v (t₀ + s) y)
    (fun y ↦ (hvc y).comp (continuous_const.add continuous_id))
    (fun s ↦ hv (t₀ + s)) x (t - t₀)).comp_sub_const t t₀
  rw [add_sub_cancel] at h
  exact h

/-- The nonautonomous global solution is an integral curve of `v`. -/
theorem isIntegralCurve_nonautonomousSolution (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (t₀ : ℝ) (x : E) : IsIntegralCurve (nonautonomousSolution v hvc hv t₀ x) v :=
  hasDerivAt_nonautonomousSolution v hvc hv t₀ x

/-- The nonautonomous global solution is continuous. -/
theorem continuous_nonautonomousSolution_apply (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    (t₀ : ℝ) (x : E) : Continuous (nonautonomousSolution v hvc hv t₀ x) :=
  Differentiable.continuous fun t ↦
    (hasDerivAt_nonautonomousSolution v hvc hv t₀ x t).differentiableAt

/-- **The integral equation** of the nonautonomous global solution:
`γ t = x + ∫ s in t₀..t, v s (γ s)`. -/
theorem nonautonomousSolution_eq_integral (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x : E) (t : ℝ) :
    nonautonomousSolution v hvc hv t₀ x t =
      x + ∫ s in t₀..t, v s (nonautonomousSolution v hvc hv t₀ x s) := by
  have hjoint : Continuous (Function.uncurry v) :=
    continuous_prod_of_continuous_lipschitzWith' (Function.uncurry v) K hv hvc
  have hcont : Continuous fun s : ℝ ↦ v s (nonautonomousSolution v hvc hv t₀ x s) :=
    hjoint.comp (continuous_id.prodMk (continuous_nonautonomousSolution_apply v hvc hv t₀ x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_nonautonomousSolution v hvc hv t₀ x s) (hcont.intervalIntegrable t₀ t),
    nonautonomousSolution_self]
  abel

/-- **Finite-interval uniqueness.** Any curve solving `γ' s = v s (γ s)` within `[a, b]` around
`t₀ ∈ [a, b]` agrees on `[a, b]` with `ODE.nonautonomousSolution` through `γ t₀`. -/
theorem eqOn_nonautonomousSolution_of_hasDerivWithinAt (v : ℝ → E → E)
    (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) {γ : ℝ → E}
    (hγ : ∀ s ∈ Icc a b, HasDerivWithinAt γ (v s (γ s)) (Icc a b) s) :
    EqOn γ (nonautonomousSolution v hvc hv t₀ (γ t₀)) (Icc a b) := by
  intro t ht
  have hle := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le (E := E)
    (f := fun s ↦ γ s - nonautonomousSolution v hvc hv t₀ (γ t₀) s)
    (f' := fun s ↦ v s (γ s) - v s (nonautonomousSolution v hvc hv t₀ (γ t₀) s))
    (δ := 0) (K := K) (ε := 0) ht₀
    (fun s hs ↦ (hγ s hs).sub
      (hasDerivAt_nonautonomousSolution v hvc hv t₀ (γ t₀) s).hasDerivWithinAt)
    (by simp)
    (fun s _ ↦ by simpa only [add_zero] using (hv s).norm_sub_le _ _) t ht
  rw [gronwallBound_ε0_δ0] at hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

/-- **Global uniqueness.** Every curve solving `γ' t = v t (γ t)` on `ℝ` coincides with
`ODE.nonautonomousSolution` through its value at any chosen time `t₀`. -/
theorem eq_nonautonomousSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (v t (γ t)) t) (t₀ : ℝ) :
    γ = nonautonomousSolution v hvc hv t₀ (γ t₀) :=
  funext fun t ↦ eqOn_nonautonomousSolution_of_hasDerivWithinAt v hvc hv
    ⟨min_le_left t₀ t, le_max_left t₀ t⟩ (fun s _ ↦ (hγ s).hasDerivWithinAt)
    ⟨min_le_right t₀ t, le_max_right t₀ t⟩

/-- **Finite-interval congruence in the vector field.** Two vector fields that agree on
`uIcc t₀ t` produce the same solution at time `t` from any initial state `x` at `t₀`. -/
theorem nonautonomousSolution_eq_of_eqOn {v₁ v₂ : ℝ → E → E}
    (hvc₁ : ∀ x, Continuous fun s ↦ v₁ s x) (hvc₂ : ∀ x, Continuous fun s ↦ v₂ s x)
    {K₁ K₂ : ℝ≥0} (hv₁ : ∀ s, LipschitzWith K₁ (v₁ s)) (hv₂ : ∀ s, LipschitzWith K₂ (v₂ s))
    {t₀ t : ℝ} (heq : EqOn v₁ v₂ (uIcc t₀ t)) (x : E) :
    nonautonomousSolution v₁ hvc₁ hv₁ t₀ x t = nonautonomousSolution v₂ hvc₂ hv₂ t₀ x t := by
  have h := eqOn_nonautonomousSolution_of_hasDerivWithinAt v₂ hvc₂ hv₂
    (a := min t₀ t) (b := max t₀ t) ⟨min_le_left t₀ t, le_max_left t₀ t⟩
    (γ := nonautonomousSolution v₁ hvc₁ hv₁ t₀ x)
    (fun s hs ↦ by
      rw [← congrFun (heq hs) _]
      exact (hasDerivAt_nonautonomousSolution v₁ hvc₁ hv₁ t₀ x s).hasDerivWithinAt)
    ⟨min_le_right t₀ t, le_max_right t₀ t⟩
  rwa [nonautonomousSolution_self] at h

/-- **Independence of the Lipschitz constant.** Two uniform Lipschitz bounds for `v` produce the
same global solution. -/
theorem nonautonomousSolution_congr (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K K' : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hv' : ∀ t, LipschitzWith K' (v t)) :
    nonautonomousSolution v hvc hv = nonautonomousSolution v hvc hv' := by
  funext t₀ x t
  exact nonautonomousSolution_eq_of_eqOn hvc hvc hv hv' (fun _ _ ↦ rfl) x

/-- **Two-time evolution composition law.** Evolving from `r` to `s` and then from `s` to `t`
agrees with evolving directly from `r` to `t`. -/
@[simp]
theorem nonautonomousSolution_trans (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (r s t : ℝ) (x : E) :
    nonautonomousSolution v hvc hv s (nonautonomousSolution v hvc hv r x s) t =
      nonautonomousSolution v hvc hv r x t :=
  (congrFun (eq_nonautonomousSolution v hvc hv
    (hasDerivAt_nonautonomousSolution v hvc hv r x) s) t).symm

/-- **Grönwall stability in the initial state.** Two solutions starting at `x` and `y` at time
`t₀` diverge at most exponentially at rate `K` in either time direction. -/
theorem dist_nonautonomousSolution_le (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (t₀ : ℝ) (x y : E) (t : ℝ) :
    dist (nonautonomousSolution v hvc hv t₀ x t) (nonautonomousSolution v hvc hv t₀ y t) ≤
      dist x y * Real.exp (K * |t - t₀|) := by
  have h := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le (E := E)
    (a := min t₀ t) (b := max t₀ t)
    (f := fun s ↦ nonautonomousSolution v hvc hv t₀ x s - nonautonomousSolution v hvc hv t₀ y s)
    (f' := fun s ↦ v s (nonautonomousSolution v hvc hv t₀ x s) -
      v s (nonautonomousSolution v hvc hv t₀ y s))
    (δ := dist x y) (K := K) (ε := 0)
    ⟨min_le_left t₀ t, le_max_left t₀ t⟩
    (fun s _ ↦ (hasDerivAt_nonautonomousSolution v hvc hv t₀ x s).hasDerivWithinAt.sub
      (hasDerivAt_nonautonomousSolution v hvc hv t₀ y s).hasDerivWithinAt)
    (by simp [dist_eq_norm])
    (fun s _ ↦ by simpa only [add_zero] using (hv s).norm_sub_le _ _)
    t ⟨min_le_right t₀ t, le_max_right t₀ t⟩
  rwa [← dist_eq_norm, gronwallBound_ε0] at h

/-- **Joint continuity** of `ODE.nonautonomousSolution` in the initial time, initial state, and
evaluation time. -/
theorem continuous_nonautonomousSolution (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) :
    Continuous fun p : ℝ × E × ℝ ↦ nonautonomousSolution v hvc hv p.1 p.2.1 p.2.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x, t⟩
  have hbound : Tendsto
      (fun p : ℝ × E × ℝ ↦
        dist (nonautonomousSolution v hvc hv t₀ x p.1) p.2.1 * Real.exp (K * |p.2.2 - p.1|))
      (𝓝 (t₀, x, t)) (𝓝 0) := by
    have hsol : Continuous fun p : ℝ × E × ℝ ↦ nonautonomousSolution v hvc hv t₀ x p.1 :=
      (continuous_nonautonomousSolution_apply v hvc hv t₀ x).comp continuous_fst
    have hc : Continuous fun p : ℝ × E × ℝ ↦
        dist (nonautonomousSolution v hvc hv t₀ x p.1) p.2.1 * Real.exp (K * |p.2.2 - p.1|) := by
      fun_prop
    simpa using (hc.continuousAt (x := (t₀, x, t))).tendsto
  refine ((continuous_nonautonomousSolution_apply v hvc hv t₀ x).continuousAt.comp
    (continuous_snd.snd.continuousAt (x := (t₀, x, t)))).congr_dist
      (squeeze_zero (fun _ ↦ dist_nonneg) (fun p ↦ ?_) hbound)
  dsimp only [Function.comp_apply]
  rw [← nonautonomousSolution_trans v hvc hv t₀ p.1 p.2.2 x]
  exact dist_nonautonomousSolution_le v hvc hv p.1 _ p.2.1 p.2.2

end ODE

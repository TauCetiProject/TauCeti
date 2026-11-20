/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Order.ProjIcc
import TauCeti.Analysis.ODE.ExistUnique
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
  interval and global uniqueness.
* `ODE.nonautonomousSolution_eq_of_eqOn`: finite-interval congruence in the vector field.
* `ODE.nonautonomousSolution_trans`: two-time evolution composition law.
* `ODE.nonautonomousSolution_neg`: time reversal.
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
  unfold nonautCurve; fun_prop

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

section PicardOp

variable {v : ℝ → E → E} {k M : ℝ} {x : E}

private theorem continuous_nonautPicardMap (hvc : Continuous (Function.uncurry v)) (u : ℝ →ᵇ E) :
    Continuous (nonautPicardMap v k x u) := by
  have hcomp : Continuous fun s : ℝ ↦ v s (nonautCurve k x u s) :=
    hvc.comp (continuous_id.prodMk (continuous_nonautCurve k x u))
  exact (Continuous.inv₀ (by fun_prop) fun _ ↦ (Real.cosh_pos _).ne').smul
    (intervalIntegral.continuous_primitive (fun a b ↦ hcomp.intervalIntegrable a b) 0)

private theorem norm_nonautPicardMap_le (hk : 0 < k)
    (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) (hx : ∀ s, ‖v s x‖ ≤ M) (u : ℝ →ᵇ E) (t : ℝ) :
    ‖nonautPicardMap v k x u t‖ ≤ (M + k * ‖u‖) / (2 * k) := by
  have hM : 0 ≤ M := (norm_nonneg (v 0 x)).trans (hx 0)
  have hbound (s : ℝ) : ‖v s (nonautCurve k x u s)‖ ≤ (M + k * ‖u‖) * Real.cosh (2 * k * s) := by
    have h1 := (hv s _ _).trans (mul_le_mul_of_nonneg_left (norm_nonautCurve_sub_le k x u s) hk.le)
    nlinarith [norm_sub_norm_le (v s (nonautCurve k x u s)) (v s x), Real.one_le_cosh (2 * k * s),
      hx s, norm_nonneg u, hk.le, mul_nonneg hk.le (norm_nonneg u)]
  have hstep := (TauCeti.norm_intervalIntegral_le_cosh (by positivity) (by positivity) t
    (.of_forall hbound)).trans_eq (by rw [abs_of_pos (by positivity)])
  have hcosh := Real.cosh_pos (2 * k * t)
  rw [nonautPicardMap, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hcosh.le),
    inv_mul_le_iff₀ hcosh]
  exact hstep.trans_eq (by field_simp)

variable (hvc : Continuous (Function.uncurry v)) (hk : 0 < k)
  (hv : ∀ s y z, ‖v s y - v s z‖ ≤ k * ‖y - z‖) (hx : ∀ s, ‖v s x‖ ≤ M)

private noncomputable def nonautPicardOp (u : ℝ →ᵇ E) : ℝ →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (nonautPicardMap v k x u)
    (continuous_nonautPicardMap hvc u) _ (norm_nonautPicardMap_le hk hv hx u)

private theorem nonautPicardOp_apply (u : ℝ →ᵇ E) (t : ℝ) :
    nonautPicardOp hvc hk hv hx u t = nonautPicardMap v k x u t :=
  congrFun (BoundedContinuousFunction.coe_ofNormedAddCommGroup _ _ _ _) t

private theorem contractingWith_nonautPicardOp :
    ContractingWith (1 / 2 : ℝ≥0) (nonautPicardOp hvc hk hv hx) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun u₁ u₂ ↦ ?_⟩
  rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    BoundedContinuousFunction.dist_le (by positivity)]
  intro t
  have hcosh := Real.cosh_pos (2 * k * t)
  have hint (u : ℝ →ᵇ E) : IntervalIntegrable (fun s ↦ v s (nonautCurve k x u s)) volume 0 t :=
    (hvc.comp (continuous_id.prodMk (continuous_nonautCurve k x u))).intervalIntegrable 0 t
  have hbound (s : ℝ) : ‖v s (nonautCurve k x u₁ s) - v s (nonautCurve k x u₂ s)‖ ≤
      k * dist u₁ u₂ * Real.cosh (2 * k * s) := by
    refine (hv s _ _).trans ?_
    rw [nonautCurve_sub, norm_smul, Real.norm_of_nonneg (Real.cosh_pos _).le, ← dist_eq_norm,
      ← mul_assoc, mul_right_comm k (Real.cosh _)]
    gcongr
    exact u₁.dist_coe_le_dist s
  have hstep := TauCeti.norm_intervalIntegral_le_cosh
    (F := fun s ↦ v s (nonautCurve k x u₁ s) - v s (nonautCurve k x u₂ s))
    (by positivity) (mul_nonneg hk.le dist_nonneg) t (.of_forall hbound)
  rw [intervalIntegral.integral_sub (hint u₁) (hint u₂), abs_of_pos (by positivity)] at hstep
  rw [nonautPicardOp_apply, nonautPicardOp_apply, dist_eq_norm, nonautPicardMap, nonautPicardMap,
    ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hcosh.le), inv_mul_le_iff₀ hcosh]
  exact hstep.trans_eq (by field_simp)

variable [CompleteSpace E]

private noncomputable def nonautFixedPoint : ℝ →ᵇ E :=
  ContractingWith.fixedPoint _ (contractingWith_nonautPicardOp hvc hk hv hx)

private theorem nonautCurve_fixedPoint (t : ℝ) :
    nonautCurve k x (nonautFixedPoint hvc hk hv hx) t =
      x + ∫ s in (0 : ℝ)..t, v s (nonautCurve k x (nonautFixedPoint hvc hk hv hx) s) := by
  have hpt : nonautPicardOp hvc hk hv hx (nonautFixedPoint hvc hk hv hx) t =
      nonautFixedPoint hvc hk hv hx t :=
    congrArg (fun w : ℝ →ᵇ E ↦ w t)
      (ContractingWith.fixedPoint_isFixedPt (contractingWith_nonautPicardOp hvc hk hv hx))
  rw [nonautPicardOp_apply] at hpt
  rw [nonautCurve, ← hpt, nonautPicardMap, smul_inv_smul₀ (Real.cosh_pos (2 * k * t)).ne']

end PicardOp

variable [CompleteSpace E]

/-- Global solution at initial time `0` when `s ↦ v s x` is bounded on `ℝ`. -/
private noncomputable def boundedTimeSolution {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) : ℝ → E :=
  nonautCurve ((K : ℝ) + 1) x
    (nonautFixedPoint hvc (by positivity)
      (fun s ↦ ((hv s).weaken (le_add_of_nonneg_right zero_le_one)).norm_sub_le) hx)

private theorem boundedTimeSolution_zero {v : ℝ → E → E} (hvc : Continuous (Function.uncurry v))
    {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) :
    boundedTimeSolution hvc hv hx 0 = x := by
  simpa [boundedTimeSolution] using nonautCurve_fixedPoint hvc (by positivity)
    (fun s ↦ ((hv s).weaken (le_add_of_nonneg_right zero_le_one)).norm_sub_le) hx 0

private theorem hasDerivAt_boundedTimeSolution {v : ℝ → E → E}
    (hvc : Continuous (Function.uncurry v)) {K : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t))
    {M : ℝ} {x : E} (hx : ∀ s, ‖v s x‖ ≤ M) (t : ℝ) :
    HasDerivAt (boundedTimeSolution hvc hv hx) (v t (boundedTimeSolution hvc hv hx t)) t := by
  unfold boundedTimeSolution
  have hcomp : Continuous fun s : ℝ ↦ v s (nonautCurve ((K : ℝ) + 1) x
      (nonautFixedPoint hvc (by positivity)
        (fun r ↦ ((hv r).weaken (le_add_of_nonneg_right zero_le_one)).norm_sub_le) hx) s) :=
    hvc.comp (continuous_id.prodMk (continuous_nonautCurve _ _ _))
  have hprim := intervalIntegral.integral_hasDerivAt_right (hcomp.intervalIntegrable 0 t)
    (hcomp.stronglyMeasurableAtFilter _ _) hcomp.continuousAt
  exact (hprim.const_add x).congr_of_eventuallyEq
    (.of_forall fun r ↦ nonautCurve_fixedPoint hvc (by positivity)
      (fun s ↦ ((hv s).weaken (le_add_of_nonneg_right zero_le_one)).norm_sub_le) hx r)

section Clamped

variable {v : ℝ → E → E} (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0}
  (hv : ∀ t, LipschitzWith K (v t))

/-- Time-dependent vector field clamped to `[-R, R]` via `Set.projIcc`. -/
private noncomputable def clampedField (v : ℝ → E → E) {R : ℝ} (hR : 0 ≤ R) (s : ℝ) (y : E) : E :=
  v (Set.projIcc (-R) R (neg_le_self hR) s) y

private noncomputable def clampedFieldAt {R : ℝ} (x : E) : Icc (-R) R →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Icc (-R) R ↦ v t x, (hvc x).comp continuous_subtypeVal⟩

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem norm_clampedField_le {R : ℝ} (hR : 0 ≤ R) (x : E) (s : ℝ) :
    ‖clampedField v hR s x‖ ≤ ‖clampedFieldAt hvc (R := R) x‖ := by
  have h := (clampedFieldAt hvc (R := R) x).norm_coe_le_norm
    (Set.projIcc (-R) R (neg_le_self hR) s)
  rw [clampedFieldAt, BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] at h
  rwa [clampedField]

/-- Clamping time to `[-R, R]` produces a bounded-in-time field agreeing with `v` on `[-R, R]`. -/
private noncomputable def clampedSolution {R : ℝ} (hR : 0 ≤ R) (x : E) : ℝ → E :=
  boundedTimeSolution
    (continuous_prod_of_continuous_lipschitzWith' (Function.uncurry (clampedField v hR)) K
      (fun s ↦ hv (Set.projIcc (-R) R (neg_le_self hR) s))
      fun y ↦ (hvc y).comp (continuous_subtypeVal.comp continuous_projIcc))
    (fun s ↦ hv (Set.projIcc (-R) R (neg_le_self hR) s))
    (norm_clampedField_le hvc hR x)

private theorem clampedSolution_zero {R : ℝ} (hR : 0 ≤ R) (x : E) :
    clampedSolution hvc hv hR x 0 = x :=
  boundedTimeSolution_zero _ _ _

private theorem hasDerivAt_clampedSolution_of_mem_Ioo {R : ℝ} (hR : 0 ≤ R) (x : E) {t : ℝ}
    (ht : t ∈ Ioo (-R) R) :
    HasDerivAt (clampedSolution hvc hv hR x) (v t (clampedSolution hvc hv hR x t)) t := by
  have hproj : clampedField v hR t = v t := by
    ext y
    simp [clampedField, Set.projIcc_of_mem (neg_le_self hR) (Ioo_subset_Icc_self ht)]
  rw [← hproj, clampedSolution]
  exact hasDerivAt_boundedTimeSolution _ _ _ t

private theorem clampedSolution_eq_of_abs_lt {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (x : E)
    {t : ℝ} (ht₁ : |t| < R₁) (ht₂ : |t| < R₂) :
    clampedSolution hvc hv hR₁.le x t = clampedSolution hvc hv hR₂.le x t := by
  set r := min R₁ R₂
  have h0r : (0 : ℝ) ∈ Ioo (-r) r := ⟨neg_lt_zero.2 (lt_min hR₁ hR₂), lt_min hR₁ hR₂⟩
  exact ODE_solution_unique_of_mem_Ioo (v := v) (s := fun _ ↦ univ) (K := K)
    (fun s _ ↦ (hv s).lipschitzOnWith) h0r
    (fun s hs ↦ ⟨hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR₁.le x
      ⟨(neg_le_neg (min_le_left _ _)).trans_lt hs.1, hs.2.trans_le (min_le_left _ _)⟩, trivial⟩)
    (fun s hs ↦ ⟨hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR₂.le x
      ⟨(neg_le_neg (min_le_right _ _)).trans_lt hs.1, hs.2.trans_le (min_le_right _ _)⟩, trivial⟩)
    ((clampedSolution_zero hvc hv hR₁.le x).trans (clampedSolution_zero hvc hv hR₂.le x).symm)
    (abs_lt.1 (lt_min ht₁ ht₂))

/-- Global solution at initial time `0` without boundedness in time. -/
private noncomputable def nonautonomousZero (x : E) (t : ℝ) : E :=
  clampedSolution hvc hv (by positivity : (0 : ℝ) ≤ |t| + 1) x t

private theorem hasDerivAt_nonautonomousZero (x : E) (t : ℝ) :
    HasDerivAt (nonautonomousZero hvc hv x) (v t (nonautonomousZero hvc hv x t)) t := by
  set R : ℝ := |t| + 2
  have hR : 0 < R := by positivity
  have htR : t ∈ Ioo (-R) R := abs_lt.1 (by linarith : |t| < |t| + 2)
  have hEq : nonautonomousZero hvc hv x =ᶠ[𝓝 t] clampedSolution hvc hv hR.le x := by
    filter_upwards [Ioo_mem_nhds htR.1 htR.2] with s hs
    exact clampedSolution_eq_of_abs_lt hvc hv (by positivity) hR x (lt_add_one |s|) (abs_lt.2 hs)
  rw [hEq.eq_of_nhds]
  exact (hasDerivAt_clampedSolution_of_mem_Ioo hvc hv hR.le x htR).congr_of_eventuallyEq hEq

end Clamped

end BoundedTime

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

section API

variable (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x) {K : ℝ≥0}
  (hv : ∀ t, LipschitzWith K (v t))

/-- **The global solution of a nonautonomous globally Lipschitz ODE.** For a vector field
`v : ℝ → E → E` that is continuous in time at each fixed state and `K`-Lipschitz in `E` uniformly
in time, `ODE.nonautonomousSolution v hvc hv t₀ x` is the unique curve `γ : ℝ → E` on the whole
real line satisfying `γ t₀ = x` and `γ' t = v t (γ t)` for every `t : ℝ`. -/
noncomputable def nonautonomousSolution (t₀ : ℝ) (x : E) (t : ℝ) : E :=
  nonautonomousZero (v := fun s y ↦ v (t₀ + s) y)
    (fun y ↦ (hvc y).comp (continuous_const.add continuous_id))
    (fun s ↦ hv (t₀ + s)) x (t - t₀)

/-- The nonautonomous global solution takes the prescribed value at the initial time. -/
@[simp]
theorem nonautonomousSolution_self (t₀ : ℝ) (x : E) :
    nonautonomousSolution v hvc hv t₀ x t₀ = x := by
  rw [nonautonomousSolution, sub_self, nonautonomousZero]
  exact clampedSolution_zero _ _ _ _

/-- **The nonautonomous global solution solves the differential equation** at every time. -/
theorem hasDerivAt_nonautonomousSolution (t₀ : ℝ) (x : E) (t : ℝ) :
    HasDerivAt (nonautonomousSolution v hvc hv t₀ x)
      (v t (nonautonomousSolution v hvc hv t₀ x t)) t := by
  unfold nonautonomousSolution
  have h := (hasDerivAt_nonautonomousZero (v := fun s y ↦ v (t₀ + s) y)
    (fun y ↦ (hvc y).comp (continuous_const.add continuous_id))
    (fun s ↦ hv (t₀ + s)) x (t - t₀)).comp_sub_const t t₀
  rwa [add_sub_cancel] at h

/-- The nonautonomous global solution is an integral curve of `v`. -/
theorem isIntegralCurve_nonautonomousSolution (t₀ : ℝ) (x : E) :
    IsIntegralCurve (nonautonomousSolution v hvc hv t₀ x) v :=
  hasDerivAt_nonautonomousSolution v hvc hv t₀ x

/-- The nonautonomous global solution is continuous. -/
theorem continuous_nonautonomousSolution_apply (t₀ : ℝ) (x : E) :
    Continuous (nonautonomousSolution v hvc hv t₀ x) :=
  Differentiable.continuous fun t ↦
    (hasDerivAt_nonautonomousSolution v hvc hv t₀ x t).differentiableAt

/-- **The integral equation** of the nonautonomous global solution:
`γ t = x + ∫ s in t₀..t, v s (γ s)`. -/
theorem nonautonomousSolution_eq_integral (t₀ : ℝ) (x : E) (t : ℝ) :
    nonautonomousSolution v hvc hv t₀ x t =
      x + ∫ s in t₀..t, v s (nonautonomousSolution v hvc hv t₀ x s) := by
  have hcont : Continuous fun s : ℝ ↦ v s (nonautonomousSolution v hvc hv t₀ x s) :=
    (continuous_prod_of_continuous_lipschitzWith' (Function.uncurry v) K hv hvc).comp
      (continuous_id.prodMk (continuous_nonautonomousSolution_apply v hvc hv t₀ x))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_nonautonomousSolution v hvc hv t₀ x s) (hcont.intervalIntegrable t₀ t),
    nonautonomousSolution_self]
  abel

/-- **Interval uniqueness.** Any curve solving `γ' s = v s (γ s)` within an order-connected set
`I ⊆ ℝ` containing `t₀` agrees on `I` with `ODE.nonautonomousSolution` through `γ t₀`. -/
theorem eqOn_nonautonomousSolution_of_hasDerivWithinAt {I : Set ℝ} (hI : I.OrdConnected)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) {γ : ℝ → E}
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (v s (γ s)) I s) :
    EqOn γ (nonautonomousSolution v hvc hv t₀ (γ t₀)) I :=
  hI.isPreconnected.ode_eqOn (V := Function.uncurry v)
    (fun _ _ ↦ ⟨K, univ, univ_mem, fun r ↦ (hv r).lipschitzOnWith⟩)
    ht₀ (nonautonomousSolution_self v hvc hv t₀ (γ t₀)).symm hγ
    fun s _ ↦ (hasDerivAt_nonautonomousSolution v hvc hv t₀ (γ t₀) s).hasDerivWithinAt

/-- **Global uniqueness.** Every curve solving `γ' t = v t (γ t)` on `ℝ` coincides with
`ODE.nonautonomousSolution` through its value at any chosen time `t₀`. -/
theorem eq_nonautonomousSolution {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (v t (γ t)) t) (t₀ : ℝ) :
    γ = nonautonomousSolution v hvc hv t₀ (γ t₀) :=
  funext fun t ↦ eqOn_nonautonomousSolution_of_hasDerivWithinAt v hvc hv ordConnected_univ
    (mem_univ t₀) (fun s _ ↦ (hγ s).hasDerivWithinAt) (mem_univ t)

/-- **Two-time evolution composition law.** Evolving from `r` to `s` and then from `s` to `t`
agrees with evolving directly from `r` to `t`. -/
@[simp]
theorem nonautonomousSolution_trans (r s t : ℝ) (x : E) :
    nonautonomousSolution v hvc hv s (nonautonomousSolution v hvc hv r x s) t =
      nonautonomousSolution v hvc hv r x t :=
  (congrFun (eq_nonautonomousSolution v hvc hv
    (hasDerivAt_nonautonomousSolution v hvc hv r x) s) t).symm

/-- **Grönwall stability in the initial state.** Two solutions starting at `x` and `y` at time
`t₀` diverge at most exponentially at rate `K` in either time direction. -/
theorem dist_nonautonomousSolution_le (t₀ : ℝ) (x y : E) (t : ℝ) :
    dist (nonautonomousSolution v hvc hv t₀ x t) (nonautonomousSolution v hvc hv t₀ y t) ≤
      dist x y * Real.exp (K * |t - t₀|) := by
  have h := TauCeti.norm_le_gronwallBound_of_norm_derivWithin_le (E := E)
    (a := min t₀ t) (b := max t₀ t)
    (f := fun s ↦ nonautonomousSolution v hvc hv t₀ x s - nonautonomousSolution v hvc hv t₀ y s)
    (f' := fun s ↦ v s (nonautonomousSolution v hvc hv t₀ x s) -
      v s (nonautonomousSolution v hvc hv t₀ y s))
    (δ := dist x y) (K := K) (ε := 0) ⟨min_le_left t₀ t, le_max_left t₀ t⟩
    (fun s _ ↦ (hasDerivAt_nonautonomousSolution v hvc hv t₀ x s).hasDerivWithinAt.sub
      (hasDerivAt_nonautonomousSolution v hvc hv t₀ y s).hasDerivWithinAt)
    (by simp [dist_eq_norm]) (fun s _ ↦ by simpa only [add_zero] using (hv s).norm_sub_le _ _)
    t ⟨min_le_right t₀ t, le_max_right t₀ t⟩
  rwa [← dist_eq_norm, gronwallBound_ε0] at h

/-- **Joint continuity** of `ODE.nonautonomousSolution` in the initial time, initial state, and
evaluation time. -/
theorem continuous_nonautonomousSolution :
    Continuous fun p : ℝ × E × ℝ ↦ nonautonomousSolution v hvc hv p.1 p.2.1 p.2.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x, t⟩
  have hbound : Tendsto (fun p : ℝ × E × ℝ ↦
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

/-- **Time reversal.** Reflecting time around `0` turns the solution of `γ' t = v t (γ t)` into
the solution of the time-reversed negated field `(u, z) ↦ -v (-u) z` started at time `-t₀`. -/
theorem nonautonomousSolution_neg (t₀ : ℝ) (x : E) (t : ℝ) :
    nonautonomousSolution v hvc hv t₀ x (-t) =
      nonautonomousSolution (fun u z ↦ -v (-u) z) (fun z ↦ ((hvc z).comp continuous_neg).neg)
        (fun u ↦ (hv (-u)).neg) (-t₀) x t := by
  have hγ : ∀ u, HasDerivAt (fun q ↦ nonautonomousSolution v hvc hv t₀ x (-q))
      (-v (-u) (nonautonomousSolution v hvc hv t₀ x (-u))) u := fun u ↦ by
    simpa only [Function.comp_def, neg_smul, one_smul] using
      (hasDerivAt_nonautonomousSolution v hvc hv t₀ x (-u)).scomp u (hasDerivAt_neg u)
  have heq := congrFun (eq_nonautonomousSolution (fun u z ↦ -v (-u) z)
    (fun z ↦ ((hvc z).comp continuous_neg).neg) (fun u ↦ (hv (-u)).neg) hγ (-t₀)) t
  simpa using heq

end API

/-- **Finite-interval congruence in the vector field.** Two vector fields that agree on
`uIcc t₀ t` produce the same solution at time `t` from any initial state `x` at `t₀`. -/
theorem nonautonomousSolution_eq_of_eqOn {v₁ v₂ : ℝ → E → E}
    (hvc₁ : ∀ x, Continuous fun s ↦ v₁ s x) (hvc₂ : ∀ x, Continuous fun s ↦ v₂ s x)
    {K₁ K₂ : ℝ≥0} (hv₁ : ∀ s, LipschitzWith K₁ (v₁ s)) (hv₂ : ∀ s, LipschitzWith K₂ (v₂ s))
    {t₀ t : ℝ} (heq : EqOn v₁ v₂ (uIcc t₀ t)) (x : E) :
    nonautonomousSolution v₁ hvc₁ hv₁ t₀ x t = nonautonomousSolution v₂ hvc₂ hv₂ t₀ x t := by
  have h := eqOn_nonautonomousSolution_of_hasDerivWithinAt v₂ hvc₂ hv₂ ordConnected_uIcc
    left_mem_uIcc (γ := nonautonomousSolution v₁ hvc₁ hv₁ t₀ x)
    (fun s hs ↦ by
      rw [← congrFun (heq hs) _]
      exact (hasDerivAt_nonautonomousSolution v₁ hvc₁ hv₁ t₀ x s).hasDerivWithinAt)
    right_mem_uIcc
  rwa [nonautonomousSolution_self] at h

/-- **Independence of the Lipschitz constant.** Two uniform Lipschitz bounds for `v` produce the
same global solution. -/
theorem nonautonomousSolution_congr (v : ℝ → E → E) (hvc : ∀ x, Continuous fun t ↦ v t x)
    {K K' : ℝ≥0} (hv : ∀ t, LipschitzWith K (v t)) (hv' : ∀ t, LipschitzWith K' (v t)) :
    nonautonomousSolution v hvc hv = nonautonomousSolution v hvc hv' := by
  funext t₀ x t
  exact nonautonomousSolution_eq_of_eqOn hvc hvc hv hv' (fun _ _ ↦ rfl) x

end ODE

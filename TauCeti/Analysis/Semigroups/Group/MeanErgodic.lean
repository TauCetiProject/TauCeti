/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.PhaseShift
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Bochner.CharFun.Bochner
import TauCeti.MeasureTheory.Integral.Exp.Average

/-!
# Continuous-time mean ergodic projection and spectral atomic mass for unitary C₀-groups

For a strongly continuous one-parameter group `U` on a real normed space `X`, the continuous-time
Cesàro average over `[0, T]` is

`U.ergodicAverage T v = T⁻¹ • ∫ t in (0 : ℝ)..T, U t v`.

Because orbits `t ↦ U t v` are continuous on all of `ℝ`, this Bochner integral exists without any
separability assumption on the ambient space. For any uniformly bounded C₀-group, the averages are
uniformly bounded and annihilate coboundaries `U s w - w` at rate `O(1 / T)`, so the vectors whose
averages tend to `0` form a closed linear subspace containing all coboundaries.

When `U` is a unitary C₀-group on a complete complex Hilbert space `H`, every frequency `b : ℝ`
determines a closed common eigenspace

`U.eigenspace hU b = {v : H | ∀ t : ℝ, U t v = exp (i b t) • v}`

with orthogonal projection `U.eigenspaceProjection hU b`. At `b = 0`, the orthogonal complement of
the fixed space is the closed linear span of the coboundaries `U s w - w`, yielding the
continuous-time von Neumann mean ergodic theorem. Passing to the phase-shifted unitary group
`U.phaseShift hU.isComplexLinear b` extends this directly to twisted averages at arbitrary real
frequency `b`:

`T⁻¹ • ∫ t in (0 : ℝ)..T, exp (-i b t) • U t v → U.eigenspaceProjection hU.isComplexLinear b v`.

Finally, `t ↦ ⟪v, U t v⟫_ℂ` is continuous and positive definite, so Bochner's theorem
(`TauCeti.bochner_charFun_real`) provides a unique finite Borel spectral measure `σ` on `ℝ` with
`⟪v, U t v⟫_ℂ = MeasureTheory.charFun σ t`. Fubini's theorem expresses the squared norm of the
twisted average as the `σ`-integral of the squared Fejér-type kernel
`‖T⁻¹ ∫₀ᵀ exp (i t (ξ - b)) dt‖²`, and dominated convergence identifies the squared projection norm
with the spectral atomic mass `σ.real {b}`.

## Main definitions and results

All declarations live in the namespace `TauCeti.Semigroups.StronglyContinuousGroup`:

* `ergodicAverage`: continuous-time Cesàro average `T⁻¹ • ∫ t in 0..T, U t v`.
* `norm_ergodicAverage_sub_le_of_norm_le`: coboundary cancellation bound
  `‖U.ergodicAverage T (U s w - w)‖ ≤ 2 * M * |s| * ‖w‖ / T`.
* `eigenspace` and `eigenspaceProjection`: closed common eigenspace at angular frequency `b` and
  its orthogonal projection.
* `IsUnitary.tendsto_ergodicAverage_eigenspaceProjection_zero` and
  `IsUnitary.tendsto_twistedAverage_eigenspaceProjection`: continuous-time von Neumann mean
  ergodic theorem and its twisted form.
* `IsUnitary.existsUnique_spectralMeasure`: Bochner spectral measure of a vector under a unitary
  C₀-group.
* `IsUnitary.norm_sq_intervalIntegral_orbit_eq_integral`: spectral-measure identity for squared
  norms of orbit integrals over arbitrary intervals `[a, b]`.
* `IsUnitary.norm_sq_eigenspaceProjection_eq_measure_singleton`: spectral atomic-mass identity
  `‖P_b v‖² = σ.real {b}`.
* `IsUnitary.exists_tendsto_twistedAverage`: combined existence, orthogonal-projection
  characterization, norm convergence, and atomic-mass identity.

## References

* J. von Neumann, *Proof of the quasi-ergodic hypothesis*, Proc. Natl. Acad. Sci. USA 18 (1932),
  70–82.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section V.4 (mean ergodic semigroups).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  Theorem II.11 (von Neumann mean ergodic theorem) and Chapter VIII.
* M. Hochman, *Notes on ergodic theory* (2012), Section 6.6 (twisted averages and spectral atoms).
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate ComplexOrder InnerProductSpace Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

/-! ## Continuous-time Cesàro averages on a real normed space -/

section NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The continuous-time Cesàro average `T⁻¹ • ∫ t in 0..T, U t v` of a strongly continuous group
orbit. -/
def ergodicAverage (U : StronglyContinuousGroup X) (T : ℝ) (v : X) : X :=
  T⁻¹ • ∫ t in (0 : ℝ)..T, U t v

/-- Unfolding lemma for `StronglyContinuousGroup.ergodicAverage`. -/
theorem ergodicAverage_def (U : StronglyContinuousGroup X) (T : ℝ) (v : X) :
    U.ergodicAverage T v = T⁻¹ • ∫ t in (0 : ℝ)..T, U t v := by
  rfl

/-- At `T = 0`, the Cesàro average is `0`. -/
@[simp]
theorem ergodicAverage_zero_time (U : StronglyContinuousGroup X) (v : X) :
    U.ergodicAverage 0 v = 0 := by
  simp [ergodicAverage]

/-- The Cesàro average of `0` is `0`. -/
@[simp]
theorem ergodicAverage_zero (U : StronglyContinuousGroup X) (T : ℝ) :
    U.ergodicAverage T 0 = 0 := by
  simp [ergodicAverage]

/-- The Cesàro average is additive in the vector argument. -/
theorem ergodicAverage_add (U : StronglyContinuousGroup X) (T : ℝ) (u v : X) :
    U.ergodicAverage T (u + v) = U.ergodicAverage T u + U.ergodicAverage T v := by
  simp only [ergodicAverage, ContinuousLinearMap.map_add]
  rw [intervalIntegral.integral_add ((U.continuous_orbit u).intervalIntegrable 0 T)
    ((U.continuous_orbit v).intervalIntegrable 0 T), smul_add]

/-- The Cesàro average respects subtraction in the vector argument. -/
theorem ergodicAverage_sub (U : StronglyContinuousGroup X) (T : ℝ) (u v : X) :
    U.ergodicAverage T (u - v) = U.ergodicAverage T u - U.ergodicAverage T v := by
  simp only [ergodicAverage, map_sub]
  rw [intervalIntegral.integral_sub ((U.continuous_orbit u).intervalIntegrable 0 T)
    ((U.continuous_orbit v).intervalIntegrable 0 T), smul_sub]

/-- The Cesàro average is homogeneous with respect to real scalars. -/
theorem ergodicAverage_smul (U : StronglyContinuousGroup X) (T c : ℝ) (v : X) :
    U.ergodicAverage T (c • v) = c • U.ergodicAverage T v := by
  simp only [ergodicAverage, map_smul, intervalIntegral.integral_smul, smul_comm T⁻¹ c]

/-- The Cesàro average fixes any vector fixed by the entire group, at every nonzero time `T`. -/
theorem ergodicAverage_of_forall_eq [CompleteSpace X] (U : StronglyContinuousGroup X) {T : ℝ}
    (hT : T ≠ 0) {v : X} (hv : ∀ t : ℝ, U t v = v) :
    U.ergodicAverage T v = v := by
  simp only [ergodicAverage, hv, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ hT, one_smul]

/-- Uniform norm bound for the Cesàro average of a uniformly bounded C₀-group. -/
theorem norm_ergodicAverage_le_of_norm_le (U : StronglyContinuousGroup X) {M : ℝ}
    (hU : ∀ t : ℝ, ‖U t‖ ≤ M) (T : ℝ) (v : X) :
    ‖U.ergodicAverage T v‖ ≤ M * ‖v‖ := by
  have hM : 0 ≤ M := (norm_nonneg (U 0)).trans (hU 0)
  rcases eq_or_ne T 0 with rfl | hT
  · simp [mul_nonneg hM (norm_nonneg v)]
  · have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) T, ‖U t v‖ ≤ M * ‖v‖ := fun t _ ↦
      ((U t).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hU t) (norm_nonneg v))
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [sub_zero] at hint
    rw [ergodicAverage, norm_smul, Real.norm_eq_abs, abs_inv]
    calc
      |T|⁻¹ * ‖∫ t in (0 : ℝ)..T, U t v‖
          ≤ |T|⁻¹ * (M * ‖v‖ * |T|) := by gcongr
      _ = M * ‖v‖ := by
        rw [mul_comm (M * ‖v‖) |T|, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hT), one_mul]

/-- Coboundary cancellation for a uniformly bounded C₀-group: the Cesàro average of `U s w - w`
decays at rate `2 M |s| ‖w‖ / T` for `T > 0`, without any sign restriction on `s`. -/
theorem norm_ergodicAverage_sub_le_of_norm_le (U : StronglyContinuousGroup X) {M : ℝ}
    (hU : ∀ t : ℝ, ‖U t‖ ≤ M) {T : ℝ} (hT : 0 < T) (s : ℝ) (w : X) :
    ‖U.ergodicAverage T (U s w - w)‖ ≤ 2 * M * |s| * ‖w‖ / T := by
  have hcont := U.continuous_orbit w
  have hint_shift :
      (∫ t in (0 : ℝ)..T, U t (U s w)) = ∫ t in s..(T + s), U t w := by
    have hfun : (fun t : ℝ ↦ U t (U s w)) = fun t : ℝ ↦ U (t + s) w := by
      ext t
      rw [U.map_add_apply]
    rw [hfun, intervalIntegral.integral_comp_add_right (fun t ↦ U t w) s, zero_add]
  have h1 : (∫ t in (0 : ℝ)..s, U t w) + (∫ t in s..(T + s), U t w) =
      ∫ t in (0 : ℝ)..(T + s), U t w :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 s) (hcont.intervalIntegrable s (T + s))
  have h2 : (∫ t in (0 : ℝ)..T, U t w) + (∫ t in T..(T + s), U t w) =
      ∫ t in (0 : ℝ)..(T + s), U t w :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 T) (hcont.intervalIntegrable T (T + s))
  have hdiff :
      (∫ t in (0 : ℝ)..T, U t (U s w - w)) =
        (∫ t in T..(T + s), U t w) - ∫ t in (0 : ℝ)..s, U t w := by
    simp only [map_sub]
    rw [intervalIntegral.integral_sub ((U.continuous_orbit (U s w)).intervalIntegrable 0 T)
      (hcont.intervalIntegrable 0 T), hint_shift]
    have h12 : (∫ t in (0 : ℝ)..s, U t w) + (∫ t in s..(T + s), U t w) =
        (∫ t in (0 : ℝ)..T, U t w) + (∫ t in T..(T + s), U t w) := h1.trans h2.symm
    exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm, h12, add_comm])
  have hbound (a b : ℝ) : ‖∫ t in a..b, U t w‖ ≤ M * ‖w‖ * |b - a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ ↦
      ((U t).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hU t) (norm_nonneg w))
  have htail1 : ‖∫ t in T..(T + s), U t w‖ ≤ M * ‖w‖ * |s| := by
    simpa [add_sub_cancel_left] using hbound T (T + s)
  have htail2 : ‖∫ t in (0 : ℝ)..s, U t w‖ ≤ M * ‖w‖ * |s| := by
    simpa [sub_zero] using hbound 0 s
  rw [ergodicAverage, hdiff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hT,
    inv_mul_eq_div]
  gcongr
  calc
    ‖(∫ t in T..(T + s), U t w) - ∫ t in (0 : ℝ)..s, U t w‖
        ≤ ‖∫ t in T..(T + s), U t w‖ + ‖∫ t in (0 : ℝ)..s, U t w‖ := norm_sub_le _ _
    _ ≤ M * ‖w‖ * |s| + M * ‖w‖ * |s| := add_le_add htail1 htail2
    _ = 2 * M * |s| * ‖w‖ := by ring

/-- For a uniformly bounded C₀-group, the Cesàro average of every coboundary `U s w - w`
converges to `0` as `T → ∞`. -/
theorem tendsto_ergodicAverage_sub_zero (U : StronglyContinuousGroup X) {M : ℝ}
    (hU : ∀ t : ℝ, ‖U t‖ ≤ M) (s : ℝ) (w : X) :
    Tendsto (fun T : ℝ ↦ U.ergodicAverage T (U s w - w)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_
    (by simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.const_mul (2 * M * |s| * ‖w‖)) :
      Tendsto (fun T : ℝ ↦ 2 * M * |s| * ‖w‖ / T) atTop (𝓝 0))
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact U.norm_ergodicAverage_sub_le_of_norm_le hU hT s w

/-- For a uniformly bounded C₀-group, the set of vectors whose Cesàro averages tend to `0` is
closed. -/
theorem isClosed_setOf_tendsto_ergodicAverage_zero (U : StronglyContinuousGroup X) {M : ℝ}
    (hU : ∀ t : ℝ, ‖U t‖ ≤ M) :
    IsClosed {v : X | Tendsto (fun T : ℝ ↦ U.ergodicAverage T v) atTop (𝓝 0)} := by
  have hM : 0 ≤ M := (norm_nonneg (U 0)).trans (hU 0)
  have hM1 : 0 < M + 1 := by linarith
  refine closure_subset_iff_isClosed.mp fun v hv ↦ Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨w, hw, hvw⟩ := Metric.mem_closure_iff.mp hv (ε / (2 * (M + 1))) (by positivity)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp hw (ε / 2) (by positivity)
  refine ⟨T₀, fun T hT ↦ ?_⟩
  simp_rw [dist_zero_right] at hT₀ ⊢
  rw [dist_eq_norm] at hvw
  have hsplit : U.ergodicAverage T v = U.ergodicAverage T (v - w) + U.ergodicAverage T w := by
    rw [← U.ergodicAverage_add, sub_add_cancel]
  calc
    ‖U.ergodicAverage T v‖
        ≤ ‖U.ergodicAverage T (v - w)‖ + ‖U.ergodicAverage T w‖ := by
          rw [hsplit]
          exact norm_add_le _ _
    _ ≤ M * ‖v - w‖ + ‖U.ergodicAverage T w‖ := by
          gcongr
          exact U.norm_ergodicAverage_le_of_norm_le hU T (v - w)
    _ < M * (ε / (2 * (M + 1))) + ε / 2 := by
          have h1 : M * ‖v - w‖ ≤ M * (ε / (2 * (M + 1))) :=
            mul_le_mul_of_nonneg_left hvw.le hM
          exact add_lt_add_of_le_of_lt h1 (hT₀ T hT)
    _ ≤ ε / 2 + ε / 2 := by
          gcongr
          have hfrac : M / (M + 1) ≤ 1 := (div_le_one hM1).mpr (by linarith)
          calc
            M * (ε / (2 * (M + 1))) = (M / (M + 1)) * (ε / 2) := by field_simp
            _ ≤ 1 * (ε / 2) := mul_le_mul_of_nonneg_right hfrac (by positivity)
            _ = ε / 2 := one_mul _
    _ = ε := add_halves ε

end NormedSpace

/-! ## Common eigenspaces and twisted averages of complex-linear C₀-groups -/

section ComplexNormed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- For a complex-linear C₀-group, the Cesàro average is complex linear in the vector argument. -/
theorem ergodicAverage_smul_complex (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (T : ℝ) (z : ℂ) (v : X) :
    U.ergodicAverage T (z • v) = z • U.ergodicAverage T v := by
  simp only [ergodicAverage, U.map_smul_of_isComplexLinear hU, intervalIntegral.integral_smul,
    smul_comm (T⁻¹ : ℝ) z]

/-- The Cesàro average of a phase-shifted C₀-group is the twisted average with factor
`exp (-i b t)`. -/
theorem ergodicAverage_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b T : ℝ) (v : X) :
    (U.phaseShift hU b).ergodicAverage T v =
      (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(b * t) * Complex.I) • U t v := by
  simp only [ergodicAverage, phaseShift_apply_apply]
  rw [← Complex.ofReal_inv, Complex.coe_smul]

/-- The common eigenspace of a complex-linear C₀-group at real angular frequency `b`:
`{v : X | ∀ t : ℝ, U t v = exp (i b t) • v}`. -/
def eigenspace (U : StronglyContinuousGroup X) (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    Submodule ℂ X where
  carrier := {v : X | ∀ t : ℝ, U t v = Complex.exp (b * t * Complex.I) • v}
  zero_mem' := by simp
  add_mem' {x y} hx hy t := by simp [hx t, hy t, smul_add]
  smul_mem' z x hx t := by
    rw [U.map_smul_of_isComplexLinear hU, hx t, smul_comm]

/-- Membership in `U.eigenspace hU b` means transforming by the character `t ↦ exp (i b t)`. -/
@[simp]
theorem mem_eigenspace_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (v : X) :
    v ∈ U.eigenspace hU b ↔ ∀ t : ℝ, U t v = Complex.exp (b * t * Complex.I) • v :=
  Iff.rfl

/-- Membership in the zero-frequency eigenspace means being fixed by every group operator. -/
theorem mem_eigenspace_zero_iff (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (v : X) :
    v ∈ U.eigenspace hU 0 ↔ ∀ t : ℝ, U t v = v := by
  simp

/-- Phase shifting by `b` shifts the eigenspace parameter by `b`. -/
@[simp]
theorem eigenspace_phaseShift (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b c : ℝ) :
    (U.phaseShift hU b).eigenspace (U.phaseShift_isComplexLinear hU b) c =
      U.eigenspace hU (b + c) := by
  ext v
  simp only [mem_eigenspace_iff, phaseShift_apply_apply]
  constructor
  · intro hv t
    have h := congrArg (Complex.exp ((b * t : ℝ) * Complex.I) • ·) (hv t)
    simp only [smul_smul, ← Complex.exp_add] at h
    have h1 : ((b * t : ℝ) : ℂ) * Complex.I + -((b : ℂ) * t) * Complex.I = 0 := by
      push_cast; ring
    have h2 : ((b * t : ℝ) : ℂ) * Complex.I + (c : ℂ) * t * Complex.I =
        ((b + c : ℝ) : ℂ) * t * Complex.I := by
      push_cast; ring
    rw [h1, Complex.exp_zero, one_smul, h2] at h
    exact h
  · intro hv t
    rw [hv t, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- Every common eigenspace of a complex-linear C₀-group is closed. -/
theorem isClosed_eigenspace (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    IsClosed (U.eigenspace hU b : Set X) := by
  have hset : (U.eigenspace hU b : Set X) =
      ⋂ t : ℝ, {v : X | U t v = Complex.exp (b * t * Complex.I) • v} := by
    ext v
    simp
  rw [hset]
  exact isClosed_iInter fun t ↦ isClosed_eq (U t).continuous (continuous_const.smul continuous_id)

instance instCompleteSpaceEigenspace [CompleteSpace X] (U : StronglyContinuousGroup X)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    CompleteSpace (U.eigenspace hU b) :=
  (U.isClosed_eigenspace hU b).completeSpace_coe

end ComplexNormed

/-! ## Orthogonal projections and the continuous-time mean ergodic theorem -/

section UnitaryMeanErgodic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The orthogonal projection onto the closed common eigenspace at angular frequency `b`. -/
def eigenspaceProjection [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) : H →L[ℂ] H :=
  (U.eigenspace hU b).starProjection

/-- Unfolding lemma for `StronglyContinuousGroup.eigenspaceProjection`. -/
theorem eigenspaceProjection_def [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    U.eigenspaceProjection hU b = (U.eigenspace hU b).starProjection := by
  rfl

/-- The eigenspace projection takes values in the common eigenspace at frequency `b`. -/
theorem eigenspaceProjection_mem_eigenspace [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (v : H) :
    U.eigenspaceProjection hU b v ∈ U.eigenspace hU b := by
  rw [eigenspaceProjection]
  exact Submodule.starProjection_apply_mem _ _

/-- The eigenspace projection fixes exactly the vectors in the common eigenspace. -/
@[simp]
theorem eigenspaceProjection_eq_self_iff [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (v : H) :
    U.eigenspaceProjection hU b v = v ↔ v ∈ U.eigenspace hU b := by
  rw [eigenspaceProjection]
  exact Submodule.starProjection_eq_self_iff

/-- The range of the eigenspace projection is the common eigenspace. -/
@[simp]
theorem range_eigenspaceProjection [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) :
    (U.eigenspaceProjection hU b).range = U.eigenspace hU b := by
  rw [eigenspaceProjection]
  exact Submodule.range_starProjection _

/-- The remainder after projecting onto the common eigenspace is orthogonal to it. -/
@[simp]
theorem sub_eigenspaceProjection_mem_orthogonal [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) (v : H) :
    v - U.eigenspaceProjection hU b v ∈ (U.eigenspace hU b)ᗮ := by
  rw [eigenspaceProjection]
  exact Submodule.sub_starProjection_mem_orthogonal _

/-- Every vector in the common eigenspace at frequency `b` is orthogonal to the projection
remainder `v - U.eigenspaceProjection hU b v`. -/
theorem inner_sub_eigenspaceProjection_eq_zero [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b : ℝ) {u : H} (hu : u ∈ U.eigenspace hU b) (v : H) :
    ⟪u, v - U.eigenspaceProjection hU b v⟫_ℂ = 0 :=
  Submodule.inner_right_of_mem_orthogonal hu (U.sub_eigenspaceProjection_mem_orthogonal hU b v)

/-- Phase shifting by `b` shifts the eigenspace projection parameter by `b`. -/
@[simp]
theorem eigenspaceProjection_phaseShift [CompleteSpace H] (U : StronglyContinuousGroup H)
    (hU : U.toSemigroup.IsComplexLinear) (b c : ℝ) :
    (U.phaseShift hU b).eigenspaceProjection (U.phaseShift_isComplexLinear hU b) c =
      U.eigenspaceProjection hU (b + c) := by
  have hcongr : ∀ {K₁ K₂ : Submodule ℂ H} [K₁.HasOrthogonalProjection]
      [K₂.HasOrthogonalProjection], K₁ = K₂ → K₁.starProjection = K₂.starProjection := by
    rintro K _ _ _ rfl
    rfl
  exact hcongr (U.eigenspace_phaseShift hU b c)

/-- For a unitary C₀-group, the orthogonal complement of the coboundaries `U s w - w` is the
fixed-point subspace `U.eigenspace hU.isComplexLinear 0`. -/
theorem IsUnitary.orthogonal_span_coboundary_eq_eigenspace_zero
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) :
    (Submodule.span ℂ {x : H | ∃ (s : ℝ) (w : H), x = U s w - w})ᗮ =
      U.eigenspace hU.isComplexLinear 0 := by
  ext u
  rw [Submodule.mem_orthogonal, mem_eigenspace_zero_iff]
  constructor
  · intro hu t
    apply ext_inner_left ℂ
    intro w
    have h := hu (U (-t) w - w) (Submodule.subset_span ⟨-t, w, rfl⟩)
    rw [inner_sub_left, sub_eq_zero] at h
    calc
      ⟪w, U t u⟫_ℂ = ⟪U (-t) w, U (-t) (U t u)⟫_ℂ := (hU.inner_map_map (-t) w (U t u)).symm
      _ = ⟪U (-t) w, u⟫_ℂ := by rw [U.map_neg_apply_map_apply]
      _ = ⟪w, u⟫_ℂ := h
  · intro hu x hx
    refine Submodule.span_induction ?_ (by simp)
      (fun a b _ _ ha hb ↦ by simp [inner_add_left, ha, hb])
      (fun z a _ ha ↦ by simp [inner_smul_left, ha]) hx
    rintro _ ⟨s, w, rfl⟩
    rw [inner_sub_left, sub_eq_zero]
    calc
      ⟪U s w, u⟫_ℂ = ⟪U s w, U s u⟫_ℂ := by rw [hu s]
      _ = ⟪w, u⟫_ℂ := hU.inner_map_map s w u

/-- For a unitary C₀-group on a complete Hilbert space, the orthogonal complement of the
fixed-point subspace is the closed linear span of the coboundaries `U s w - w`. -/
theorem IsUnitary.orthogonal_eigenspace_zero_eq_topologicalClosure_span [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) :
    (U.eigenspace hU.isComplexLinear 0)ᗮ =
      (Submodule.span ℂ {x : H | ∃ (s : ℝ) (w : H), x = U s w - w}).topologicalClosure := by
  rw [← hU.orthogonal_span_coboundary_eq_eigenspace_zero,
    Submodule.orthogonal_orthogonal_eq_closure]

/-- For a unitary C₀-group on a complete Hilbert space, the Cesàro averages of any vector
orthogonal to the fixed-point subspace converge to `0`. -/
theorem IsUnitary.tendsto_ergodicAverage_zero_of_mem_orthogonal [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    (hv : v ∈ (U.eigenspace hU.isComplexLinear 0)ᗮ) :
    Tendsto (fun T : ℝ ↦ U.ergodicAverage T v) atTop (𝓝 0) := by
  let Z : Submodule ℂ H :=
    { carrier := {x : H | Tendsto (fun T : ℝ ↦ U.ergodicAverage T x) atTop (𝓝 0)}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy ↦ by simpa [U.ergodicAverage_add] using hx.add hy
      smul_mem' := fun z x hx ↦ by
        simpa [U.ergodicAverage_smul_complex hU.isComplexLinear] using hx.const_smul z }
  have hZclosed : IsClosed (Z : Set H) :=
    U.isClosed_setOf_tendsto_ergodicAverage_zero hU.opNorm_le_one
  have hspan : Submodule.span ℂ {x : H | ∃ (s : ℝ) (w : H), x = U s w - w} ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨s, w, rfl⟩
    exact U.tendsto_ergodicAverage_sub_zero hU.opNorm_le_one s w
  have hclos : (Submodule.span ℂ {x : H | ∃ (s : ℝ) (w : H), x = U s w - w}).topologicalClosure ≤
      Z :=
    Submodule.topologicalClosure_minimal _ hspan hZclosed
  rw [hU.orthogonal_eigenspace_zero_eq_topologicalClosure_span] at hv
  exact hclos hv

/-- **Continuous-time von Neumann mean ergodic theorem.** For a unitary C₀-group on a complete
complex Hilbert space, the Cesàro averages `T⁻¹ • ∫ t in 0..T, U t v` converge in norm to the
orthogonal projection onto the fixed-point subspace. -/
theorem IsUnitary.tendsto_ergodicAverage_eigenspaceProjection_zero [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (v : H) :
    Tendsto (fun T : ℝ ↦ U.ergodicAverage T v) atTop
      (𝓝 (U.eigenspaceProjection hU.isComplexLinear 0 v)) := by
  set w := U.eigenspaceProjection hU.isComplexLinear 0 v
  have hw_fix : ∀ t : ℝ, U t w = w :=
    (U.mem_eigenspace_zero_iff hU.isComplexLinear w).mp
      (U.eigenspaceProjection_mem_eigenspace hU.isComplexLinear 0 v)
  have h1 : Tendsto (fun T : ℝ ↦ U.ergodicAverage T w) atTop (𝓝 w) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact (U.ergodicAverage_of_forall_eq hT.ne' hw_fix).symm
  have h2 : Tendsto (fun T : ℝ ↦ U.ergodicAverage T (v - w)) atTop (𝓝 0) :=
    hU.tendsto_ergodicAverage_zero_of_mem_orthogonal
      (U.sub_eigenspaceProjection_mem_orthogonal hU.isComplexLinear 0 v)
  have hsum : Tendsto (fun T : ℝ ↦ U.ergodicAverage T w + U.ergodicAverage T (v - w))
      atTop (𝓝 (w + 0)) := h1.add h2
  simpa [← U.ergodicAverage_add, add_sub_cancel] using hsum

/-- **Twisted continuous-time mean ergodic theorem.** For a unitary C₀-group on a complete
complex Hilbert space and any real angular frequency `b`, the twisted Cesàro averages
`T⁻¹ • ∫ t in 0..T, exp (-i b t) • U t v` converge in norm to the orthogonal projection onto the
common eigenspace at frequency `b`. -/
theorem IsUnitary.tendsto_twistedAverage_eigenspaceProjection [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) (v : H) :
    Tendsto
      (fun T : ℝ ↦ (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(b * t) * Complex.I) • U t v)
      atTop (𝓝 (U.eigenspaceProjection hU.isComplexLinear b v)) := by
  have h := (hU.phaseShift b).tendsto_ergodicAverage_eigenspaceProjection_zero v
  simpa only [U.ergodicAverage_phaseShift hU.isComplexLinear b,
    U.eigenspaceProjection_phaseShift hU.isComplexLinear b 0, add_zero] using h

end UnitaryMeanErgodic

/-! ## Spectral measures and the atomic-mass identity -/

section SpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The autocorrelation function `t ↦ ⟪v, U t v⟫_ℂ` of any vector under a unitary C₀-group is
positive definite. -/
theorem IsUnitary.isPositiveDefiniteSub_inner {U : StronglyContinuousGroup H}
    (hU : U.IsUnitary) (v : H) :
    TauCeti.IsPositiveDefiniteSub fun t : ℝ ↦ ⟪v, U t v⟫_ℂ := by
  rw [TauCeti.isPositiveDefiniteSub_iff_forall_sum_nonneg]
  intro n c t
  let w : H := ∑ i : Fin n, c i • U (t i) v
  have hnonneg : (0 : ℂ) ≤ ⟪w, w⟫_ℂ := by
    have hsq : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by simp
    rw [hsq, Complex.le_def]
    simp only [Complex.zero_re, Complex.ofReal_re, Complex.zero_im, Complex.ofReal_im, sq_nonneg,
      and_self]
  have hform :
      ⟪w, w⟫_ℂ = ∑ i : Fin n, ∑ j : Fin n, c i * conj (c j) * ⟪v, U (t i - t j) v⟫_ℂ := by
    dsimp only [w]
    rw [sum_inner]
    simp_rw [inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    have hinner : ⟪U (t j) v, U (t i) v⟫_ℂ = ⟪v, U (t i - t j) v⟫_ℂ := by
      calc
        ⟪U (t j) v, U (t i) v⟫_ℂ
            = ⟪U (-(t j)) (U (t j) v), U (-(t j)) (U (t i) v)⟫_ℂ :=
          (hU.inner_map_map (-(t j)) _ _).symm
        _ = ⟪v, U (t i - t j) v⟫_ℂ := by
          rw [U.map_neg_apply_map_apply, ← U.map_add_apply, neg_add_eq_sub]
    rw [hinner]
    ring
  rwa [hform] at hnonneg

/-- **Spectral measure of a vector under a unitary C₀-group.** By Bochner's theorem, there is a
unique finite Borel measure `σ` on `ℝ` whose characteristic function equals `t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem IsUnitary.existsUnique_spectralMeasure {U : StronglyContinuousGroup H}
    (hU : U.IsUnitary) (v : H) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have hcont : Continuous fun t : ℝ ↦ ⟪v, U t v⟫_ℂ :=
    continuous_const.inner (U.continuous_orbit v)
  have hboch := (TauCeti.bochner_charFun_real fun t : ℝ ↦ ⟪v, U t v⟫_ℂ).mp
    ⟨hcont, hU.isPositiveDefiniteSub_inner v⟩
  simpa only [charFun_apply_real] using hboch

/-- Phase shifting a unitary C₀-group by `b` translates a Bochner spectral measure by `-b`. -/
theorem IsUnitary.inner_phaseShift_eq_charFun_map {U : StronglyContinuousGroup H}
    (hU : U.IsUnitary) {v : H} {σ : Measure ℝ}
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (b t : ℝ) :
    ⟪v, (U.phaseShift hU.isComplexLinear b) t v⟫_ℂ = charFun (σ.map (· + (-b))) t := by
  rw [phaseShift_apply_apply, inner_smul_right, hσ t, charFun_map_add_const (-b) t, mul_comm]
  congr 2
  simp [mul_comm]

/-- For a unitary C₀-group, the squared norm of an orbit integral equals the iterated integral of
the autocorrelation `⟪v, U (t - s) v⟫_ℂ`. -/
theorem IsUnitary.inner_intervalIntegral_orbit_self [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (a b : ℝ) (v : H) :
    ⟪∫ s in a..b, U s v, ∫ t in a..b, U t v⟫_ℂ =
      ∫ s in a..b, ∫ t in a..b, ⟪v, U (t - s) v⟫_ℂ := by
  let I : H := ∫ t in a..b, U t v
  have hcont : Continuous fun t : ℝ ↦ U t v := U.continuous_orbit v
  have hright (x : H) : ⟪x, I⟫_ℂ = ∫ t in a..b, ⟪x, U t v⟫_ℂ :=
    ((innerSL ℂ x).intervalIntegral_comp_comm (hcont.intervalIntegrable a b)).symm
  have hleft : ⟪I, I⟫_ℂ = ∫ s in a..b, ⟪U s v, I⟫_ℂ := by
    calc
      ⟪I, I⟫_ℂ = conj ⟪I, I⟫_ℂ := (inner_conj_symm I I).symm
      _ = conj (∫ s in a..b, ⟪I, U s v⟫_ℂ) := by rw [hright I]
      _ = ∫ s in a..b, conj ⟪I, U s v⟫_ℂ := intervalIntegral.intervalIntegral_conj.symm
      _ = ∫ s in a..b, ⟪U s v, I⟫_ℂ :=
        intervalIntegral.integral_congr fun s _ ↦ inner_conj_symm _ _
  rw [show ⟪∫ s in a..b, U s v, ∫ t in a..b, U t v⟫_ℂ = ⟪I, I⟫_ℂ from rfl, hleft]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [hright (U s v)]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  calc
    ⟪U s v, U t v⟫_ℂ = ⟪U (-s) (U s v), U (-s) (U t v)⟫_ℂ := (hU.inner_map_map (-s) _ _).symm
    _ = ⟪v, U (t - s) v⟫_ℂ := by
      rw [U.map_neg_apply_map_apply, ← U.map_add_apply, neg_add_eq_sub]

/-- For a unitary C₀-group and a finite Borel spectral measure `σ`, the squared norm of an orbit
integral over any interval `[a, b]` equals the `σ`-integral of `‖∫ t in a..b, exp (i t ξ) dt‖²`. -/
theorem IsUnitary.norm_sq_intervalIntegral_orbit_eq_integral [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (a b : ℝ) :
    ‖∫ t in a..b, U t v‖ ^ 2 =
      ∫ ξ, ‖∫ t in a..b, Complex.exp (t * ξ * Complex.I)‖ ^ 2 ∂σ := by
  wlog hab : a ≤ b generalizing a b
  · have h := this b a (le_of_not_ge hab)
    rw [intervalIntegral.integral_symm a b, norm_neg] at h
    simpa only [intervalIntegral.integral_symm a b, norm_neg] using h
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let g : ℝ → ℂ := fun ξ ↦ ∫ t in a..b, Complex.exp (t * ξ * Complex.I)
  have hg_cont : Continuous g :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) a b
  have hg_bound (ξ : ℝ) : ‖g ξ‖ ≤ b - a := by
    have hb : ∀ t ∈ Set.uIoc a b, ‖Complex.exp (t * ξ * Complex.I)‖ ≤ (1 : ℝ) := fun t _ ↦ by
      rw [Complex.norm_exp]; simp
    simpa [g, one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hstep1 (s : ℝ) :
      (∫ t in a..b, ⟪v, U (t - s) v⟫_ℂ) =
        ∫ ξ, Complex.exp (-(s * ξ) * Complex.I) * g ξ ∂σ := by
    have hsub (t : ℝ) : ⟪v, U (t - s) v⟫_ℂ = ∫ ξ, Complex.exp ((t - s) * ξ * Complex.I) ∂σ := by
      rw [hσ (t - s), charFun_apply_real]
      simp [Complex.ofReal_sub]
    simp_rw [hsub]
    rw [intervalIntegral.integral_of_le hab]
    have hint1 : Integrable (fun p : ℝ × ℝ ↦ Complex.exp ((p.1 - s) * p.2 * Complex.I))
        (μ.prod σ) :=
      Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) 1
        (ae_of_all _ fun p ↦ by rw [Complex.norm_exp]; simp)
    rw [integral_integral_swap hint1]
    refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
    dsimp only
    have hfac : (fun t : ℝ ↦ Complex.exp ((t - s) * ξ * Complex.I)) =
        fun t : ℝ ↦ Complex.exp (-(s * ξ) * Complex.I) * Complex.exp (t * ξ * Complex.I) := by
      ext t; rw [← Complex.exp_add]; congr 1; ring
    rw [hfac, integral_const_mul, ← intervalIntegral.integral_of_le hab]
  have hint2 : Integrable (fun p : ℝ × ℝ ↦ Complex.exp (-(p.1 * p.2) * Complex.I) * g p.2)
      (μ.prod σ) :=
    Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop)) (b - a)
      (ae_of_all _ fun p ↦ by rw [norm_mul, Complex.norm_exp]; simpa using hg_bound p.2)
  apply Complex.ofReal_injective
  have hsq : ((‖∫ t in a..b, U t v‖ ^ 2 : ℝ) : ℂ) =
      ⟪∫ s in a..b, U s v, ∫ t in a..b, U t v⟫_ℂ := by simp
  rw [hsq, hU.inner_intervalIntegral_orbit_self a b v]
  simp_rw [hstep1]
  rw [intervalIntegral.integral_of_le hab, integral_integral_swap hint2, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
  dsimp only
  rw [integral_mul_const]
  have hconj : (∫ s, Complex.exp (-(s * ξ) * Complex.I) ∂μ) = conj (g ξ) := by
    rw [← intervalIntegral.integral_of_le hab]
    have hfun : (fun s : ℝ ↦ Complex.exp (-(s * ξ) * Complex.I)) =
        fun s : ℝ ↦ conj (Complex.exp (s * ξ * Complex.I)) := by
      ext s; rw [← Complex.exp_conj]; simp
    rw [hfun, intervalIntegral.intervalIntegral_conj]
  rw [hconj, RCLike.conj_mul]
  simp [g]

/-- Squared-norm identity for the continuous-time Cesàro average in terms of a Bochner spectral
measure. -/
theorem IsUnitary.norm_sq_ergodicAverage_eq_integral [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (T : ℝ) :
    ‖U.ergodicAverage T v‖ ^ 2 =
      ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 ∂σ := by
  rw [ergodicAverage, norm_smul, mul_pow, Real.norm_eq_abs,
    hU.norm_sq_intervalIntegral_orbit_eq_integral hσ 0 T, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ξ ↦ ?_)
  dsimp only
  rw [norm_mul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv]

/-- Squared-norm identity for twisted continuous-time Cesàro averages in terms of a Bochner
spectral measure. -/
theorem IsUnitary.norm_sq_twistedAverage_eq_integral [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (b T : ℝ) :
    ‖(T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(b * t) * Complex.I) • U t v‖ ^ 2 =
      ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * (ξ - b) * Complex.I)‖ ^ 2 ∂σ := by
  have : IsFiniteMeasure (σ.map (· + (-b))) := Measure.isFiniteMeasure_map σ (· + (-b))
  have h := (hU.phaseShift b).norm_sq_ergodicAverage_eq_integral
    (hU.inner_phaseShift_eq_charFun_map hσ b) T
  rw [U.ergodicAverage_phaseShift hU.isComplexLinear b] at h
  rw [h]
  have hf_cont : Continuous fun ξ : ℝ ↦
      ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 := by
    have : Continuous fun ξ : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T
    fun_prop
  rw [integral_map (by fun_prop) hf_cont.aestronglyMeasurable]
  simp [sub_eq_add_neg]

/-- **Spectral atomic-mass identity at frequency `0`.** The squared norm of the orthogonal
projection onto the fixed-point subspace equals the spectral mass `σ.real {0}`. -/
theorem IsUnitary.norm_sq_eigenspaceProjection_zero_eq_measure_singleton [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) :
    ‖U.eigenspaceProjection hU.isComplexLinear 0 v‖ ^ 2 = σ.real {0} := by
  have hlhs : Tendsto (fun T : ℝ ↦ ‖U.ergodicAverage T v‖ ^ 2) atTop
      (𝓝 (‖U.eigenspaceProjection hU.isComplexLinear 0 v‖ ^ 2)) :=
    ((hU.tendsto_ergodicAverage_eigenspaceProjection_zero v).norm).pow 2
  have hcont (T : ℝ) : Continuous fun ξ : ℝ ↦
      ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 := by
    have : Continuous fun ξ : ℝ ↦ ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by fun_prop) 0 T
    fun_prop
  have hrhs : Tendsto
      (fun T : ℝ ↦
        ∫ ξ, ‖(T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I)‖ ^ 2 ∂σ)
      atTop (𝓝 (∫ ξ, Set.indicator ({0} : Set ℝ) 1 ξ ∂σ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (.of_forall fun T ↦ (hcont T).aestronglyMeasurable)
      (.of_forall fun T ↦ ae_of_all _ fun ξ ↦ ?_)
      (integrable_const (1 : ℝ))
      (ae_of_all _ fun ξ ↦ ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [TauCeti.norm_inv_mul_intervalIntegral_exp_mul_I_le T ξ,
        norm_nonneg ((T⁻¹ : ℂ) * ∫ t in (0 : ℝ)..T, Complex.exp (t * ξ * Complex.I))]
    · have hlim := ((TauCeti.tendsto_inv_mul_intervalIntegral_exp_mul_I ξ).norm).pow 2
      have hval : ‖(if ξ = 0 then (1 : ℂ) else 0)‖ ^ 2 = Set.indicator ({0} : Set ℝ) 1 ξ := by
        by_cases hξ : ξ = 0 <;> simp [hξ]
      rwa [hval] at hlim
  simp_rw [hU.norm_sq_ergodicAverage_eq_integral hσ] at hlhs
  rw [tendsto_nhds_unique hlhs hrhs, integral_indicator_one (measurableSet_singleton 0)]

/-- **Spectral atomic-mass identity.** For any real angular frequency `b`, the squared norm of
the orthogonal projection onto `U.eigenspace hU.isComplexLinear b` equals `σ.real {b}` for any
finite Borel spectral measure `σ` with `⟪v, U t v⟫_ℂ = charFun σ t`. -/
theorem IsUnitary.norm_sq_eigenspaceProjection_eq_measure_singleton [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) {v : H}
    {σ : Measure ℝ} [IsFiniteMeasure σ]
    (hσ : ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) (b : ℝ) :
    ‖U.eigenspaceProjection hU.isComplexLinear b v‖ ^ 2 = σ.real {b} := by
  have : IsFiniteMeasure (σ.map (· + (-b))) := Measure.isFiniteMeasure_map σ (· + (-b))
  have h := (hU.phaseShift b).norm_sq_eigenspaceProjection_zero_eq_measure_singleton
    (hU.inner_phaseShift_eq_charFun_map hσ b)
  rw [U.eigenspaceProjection_phaseShift hU.isComplexLinear b 0, add_zero] at h
  have hpre : (fun ξ : ℝ ↦ ξ + (-b)) ⁻¹' {0} = {b} := by
    ext ξ
    simp
  rw [h, Measure.real, Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hpre]
  rfl

/-- **Continuous-time mean ergodic projection and spectral atomic-mass theorem.** For any unitary
C₀-group `U` on a complete complex Hilbert space `H`, real angular frequency `b`, and vector `v`,
the twisted Cesàro averages `T⁻¹ • ∫ t in 0..T, exp (-i b t) • U t v` converge in norm to a
vector `w` characterized as the orthogonal projection onto the `b`-eigenspace, and `‖w‖²` equals
the spectral mass `σ.real {b}` for every finite Borel measure `σ` with
`⟪v, U t v⟫_ℂ = charFun σ t`. -/
theorem IsUnitary.exists_tendsto_twistedAverage [CompleteSpace H]
    {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) (v : H) :
    ∃ w : H, (∀ t : ℝ, U t w = Complex.exp (b * t * Complex.I) • w) ∧
      (∀ u : H, (∀ t : ℝ, U t u = Complex.exp (b * t * Complex.I) • u) → ⟪u, v - w⟫_ℂ = 0) ∧
      Tendsto
        (fun T : ℝ ↦ (T⁻¹ : ℂ) • ∫ t in (0 : ℝ)..T, Complex.exp (-(b * t) * Complex.I) • U t v)
        atTop (𝓝 w) ∧
      ∀ σ : Measure ℝ, IsFiniteMeasure σ →
        (∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t) →
        ‖w‖ ^ 2 = σ.real {b} :=
  ⟨U.eigenspaceProjection hU.isComplexLinear b v,
    (U.mem_eigenspace_iff hU.isComplexLinear b _).mp
      (U.eigenspaceProjection_mem_eigenspace hU.isComplexLinear b v),
    fun _ hu ↦ U.inner_sub_eigenspaceProjection_eq_zero hU.isComplexLinear b
      ((U.mem_eigenspace_iff hU.isComplexLinear b _).mpr hu) v,
    hU.tendsto_twistedAverage_eigenspaceProjection b v,
    fun _ _ hσ ↦ hU.norm_sq_eigenspaceProjection_eq_measure_singleton hσ b⟩

end SpectralMeasure

end TauCeti.Semigroups.StronglyContinuousGroup

end

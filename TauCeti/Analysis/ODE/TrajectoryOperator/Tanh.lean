/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import TauCeti.Analysis.ODE.Tanh
import TauCeti.MeasureTheory.Integral.Cosh

/-!
# The trajectory operator `d/ds - tanh s`

The coefficient `A(s) = -tanh(s) • id` on a finite-dimensional real inner product space `E` is the
basic example of a trajectory operator with nonzero index. Its trajectory operator

`D u = u' - tanh(s) u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator` of an `L∞` class of `A`) is computed completely here:

* its kernel is zero: a solution of `v' = tanh(s) v` is `cosh(s) v(0)`, which is square integrable
  only when `v(0) = 0`;
* the orthogonal complement of its range, which is its cokernel, consists of the paths
  `(cosh s)⁻¹ • x` for `x ∈ E`: these are the solutions of the formal adjoint equation
  `v' = -tanh(s) v`, all of which are square integrable;
* it is Fredholm of index `-dim E`.

For `E = ℝ` this says that `d/ds - tanh s` has kernel `0`, cokernel spanned by `sech s` and index
`-1`. The family `B = -A = tanh • id` has one eigenvalue, crossing from `-1` to `1` with
multiplicity `dim E`, so its spectral flow is `dim E` when positive crossings count positively;
the index computed here is consistent with `index (d/ds - B(s)) = -SF(B)` in that convention. It
agrees with the Morse-index formula
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`,
since `A` has no negative eigenvalue at `-∞` and the eigenvalue `-1` of multiplicity `dim E` at
`+∞`; the computation here does not use that formula but the explicit solutions.

## Main declarations

* `TauCeti.squareIntegrableSolutions_neg_tanh_smul_id`: the only square-integrable solution of
  `v' = tanh(s) v` is zero.
* `TauCeti.squareIntegrableSolutions_tanh_smul_id`: every solution of `v' = -tanh(s) v` is square
  integrable.
* `TauCeti.WeakDerivStep.ker_trajectoryOperator_neg_tanh_smul_id`: the kernel of `D` is zero.
* `TauCeti.WeakDerivStep.mem_orthogonal_range_trajectoryOperator_neg_tanh_smul_id_iff`: the
  orthogonal complement of the range of `D` consists of the classes of `(cosh s)⁻¹ • x`.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_neg_tanh_smul_id` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_neg_tanh_smul_id`: `D` is Fredholm of index
  `-dim E`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33 (the index of a trajectory operator as a spectral flow).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti

section Solutions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coefficient `s ↦ -tanh(s) • id` is continuous. -/
private theorem continuous_neg_tanh_smul_id :
    Continuous fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ F :=
  Real.continuous_tanh.neg.smul continuous_const

/-- The coefficient `s ↦ tanh(s) • id` is continuous. -/
private theorem continuous_tanh_smul_id :
    Continuous fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ F :=
  Real.continuous_tanh.smul continuous_const

/-- **The equation `v' = tanh(s) v` has no nonzero square-integrable solution.** Every solution is
`cosh(s) v(0)`, whose norm is at least `‖v(0)‖` everywhere. -/
theorem squareIntegrableSolutions_neg_tanh_smul_id :
    squareIntegrableSolutions (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ F) = ⊥ := by
  rw [eq_bot_iff]
  intro _ hx
  obtain ⟨v, rfl, hv, hv2⟩ := mem_squareIntegrableSolutions.1 hx
  have hv' := eq_cosh_smul_of_hasDerivAt (v := v) fun s ↦ by simpa using hv s
  -- The constant path `v 0` is dominated by `v`, so it is square integrable on the line.
  have hconst : MemLp (fun _ : ℝ ↦ v 0) 2 := by
    refine hv2.of_le aestronglyMeasurable_const (.of_forall fun s ↦ ?_)
    rw [congrFun hv' s, norm_smul, Real.norm_of_nonneg (Real.cosh_pos s).le]
    exact le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_cosh s)
  rw [memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top, Real.volume_univ] at hconst
  simpa using hconst

/-- **Every solution of `v' = -tanh(s) v` is square integrable.** The solution with initial value
`x` is `(cosh s)⁻¹ • x`. -/
theorem squareIntegrableSolutions_tanh_smul_id :
    squareIntegrableSolutions (fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ F) = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ mem_squareIntegrableSolutions.2
    ⟨fun s ↦ (Real.cosh s)⁻¹ • x, by simp, fun s ↦ ?_, memLp_inv_cosh.smul (memLp_top_const x)⟩
  exact (hasDerivAt_inv_cosh_smul x s).congr_deriv (by simp [smul_comm (Real.tanh s)])

end Solutions

namespace WeakDerivStep

section Banach

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The trajectory operator `d/ds - tanh s` is injective.** For the `L∞` class `AL` of
`s ↦ -tanh(s) • id` on a real Banach space `F`, the kernel of `u ↦ u' + AL u` on
`W^{1,2}(ℝ, F)` is zero. -/
theorem ker_trajectoryOperator_neg_tanh_smul_id
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ F) :
    (trajectoryOperator (p := 2) AL).ker = ⊥ := by
  have : Subsingleton (squareIntegrableSolutions
      (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ F)) := by
    rw [squareIntegrableSolutions_neg_tanh_smul_id]
    infer_instance
  rw [← Submodule.subsingleton_iff_eq_bot]
  exact (kerTrajectoryOperatorEquiv continuous_neg_tanh_smul_id AL hAL).toEquiv.subsingleton

end Banach

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- The class `-AL` is that of `s ↦ tanh(s) • id`. -/
private theorem neg_ae_eq_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E := by
  filter_upwards [Lp.coeFn_neg AL, hAL] with s hneg hs
  rw [hneg, Pi.neg_apply, hs, neg_smul, neg_neg]

/-- Scalar multiples of the identity are self-adjoint, so `AL` is almost everywhere its own
pointwise adjoint. -/
private theorem ae_eq_adjoint_of_ae_eq_neg_tanh_smul_id [FiniteDimensional ℝ E]
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      AL s = ContinuousLinearMap.adjoint (AL s) := by
  filter_upwards [hAL] with s hs
  rw [hs, map_smulₛₗ, ContinuousLinearMap.adjoint_id]
  simp

/-- **The cokernel of `d/ds - tanh s`.** For the `L∞` class `AL` of `s ↦ -tanh(s) • id`, a path
`v ∈ L²(ℝ, E)` is orthogonal to the range of `u ↦ u' + AL u` exactly when it is almost
everywhere `(cosh s)⁻¹ • x` for some `x ∈ E`. For `E = ℝ` the orthogonal complement of the range
is the line spanned by `sech`. -/
theorem mem_orthogonal_range_trajectoryOperator_neg_tanh_smul_id_iff [FiniteDimensional ℝ E]
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E)
    {v : Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))} :
    v ∈ (trajectoryOperator (p := 2) AL).rangeᗮ ↔
      ∃ x : E, v =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ (Real.cosh s)⁻¹ • x := by
  have hneg := neg_ae_eq_tanh_smul_id hAL
  rw [orthogonal_range_trajectoryOperator_eq_map_ker
    (ae_eq_adjoint_of_ae_eq_neg_tanh_smul_id hAL)]
  constructor
  · -- An element of the kernel of the formal adjoint is a solution of `w' = -tanh(s) w`.
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := exists_hasDerivAt_of_trajectoryOperator_eq_zero
      continuous_tanh_smul_id hneg hz
    refine ⟨w 0, ?_⟩
    rw [eq_inv_cosh_smul_of_hasDerivAt (v := w) fun s ↦ by simpa using hw s] at hzw
    simpa [prevL_apply] using hzw
  · -- Conversely `(cosh s)⁻¹ • x` solves the formal adjoint equation in `W^{1,2}(ℝ, E)`.
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, hux⟩ := exists_trajectoryOperator_eq_zero_of_hasDerivAt (p := 2) hneg
      (fun s ↦ (hasDerivAt_inv_cosh_smul x s).congr_deriv (by simp [smul_comm (Real.tanh s)]))
      (memLp_inv_cosh.smul (memLp_top_const x))
    exact ⟨u, hu, by simpa [prevL_apply] using Lp.ext (hux.trans hx.symm)⟩

/-- The coefficient `s ↦ -tanh(s) • id` satisfies the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, with limits `id` at `-∞`
and `-id` at `+∞`, both symmetric and bounded below by `1`. -/
private theorem neg_tanh_smul_id_hypotheses :
    (ContinuousLinearMap.id ℝ E).HasLyapunovForm ∧
      (-ContinuousLinearMap.id ℝ E).HasLyapunovForm ∧
      Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atBot
        (𝓝 (ContinuousLinearMap.id ℝ E)) ∧
      Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atTop
        (𝓝 (-ContinuousLinearMap.id ℝ E)) :=
  ⟨ContinuousLinearMap.hasLyapunovForm_of_isSymmetric (fun x y ↦ by simp) one_pos (by simp),
    ContinuousLinearMap.hasLyapunovForm_of_isSymmetric
      (fun x y ↦ by simp [inner_neg_left, inner_neg_right]) one_pos (by simp),
    by simpa using Real.tendsto_tanh_atBot.neg.smul_const (ContinuousLinearMap.id ℝ E),
    by simpa using Real.tendsto_tanh_atTop.neg.smul_const (ContinuousLinearMap.id ℝ E)⟩

variable [FiniteDimensional ℝ E]

/-- **The trajectory operator `d/ds - tanh s` is Fredholm.** For the `L∞` class `AL` of
`s ↦ -tanh(s) • id` on a finite-dimensional real inner product space `E`, the operator
`u ↦ u' + AL u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_neg_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  exact isFredholm_trajectoryOperator_of_hasLyapunovForm continuous_neg_tanh_smul_id hminus hplus
    hbot htop AL hAL

/-- **The index of `d/ds - tanh s` is `-dim E`.** For the `L∞` class `AL` of `s ↦ -tanh(s) • id`
on a finite-dimensional real inner product space `E`, the trajectory operator `u ↦ u' + AL u`
from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index `-dim E`: its kernel is zero and its cokernel is
`{(cosh s)⁻¹ • x | x ∈ E}`. For `E = ℝ` the index is `-1`. -/
theorem index_trajectoryOperator_neg_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index = -(Module.finrank ℝ E : ℤ) := by
  obtain ⟨hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  rw [index_trajectoryOperator_of_isClosed_range (ae_eq_adjoint_of_ae_eq_neg_tanh_smul_id hAL)
      (isClosed_range_trajectoryOperator_of_hasLyapunovForm continuous_neg_tanh_smul_id hminus
        hplus hbot htop AL hAL),
    finrank_ker_trajectoryOperator continuous_neg_tanh_smul_id AL hAL,
    finrank_ker_trajectoryOperator continuous_tanh_smul_id (-AL) (neg_ae_eq_tanh_smul_id hAL),
    squareIntegrableSolutions_neg_tanh_smul_id, squareIntegrableSolutions_tanh_smul_id,
    finrank_bot, finrank_top]
  simp

end WeakDerivStep

end TauCeti

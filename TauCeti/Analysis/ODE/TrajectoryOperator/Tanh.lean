/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Reversal
import TauCeti.Analysis.ODE.Tanh
import TauCeti.MeasureTheory.Integral.Cosh

/-!
# The trajectory operators `d/ds - tanh s` and `d/ds + tanh s`

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

Reversing the coefficient, `s ↦ A(-s)† = tanh(s) • id`, gives the trajectory operator
`d/ds + tanh s`, whose kernel and cokernel are exchanged with those of `D`:

* its kernel consists of the paths `(cosh s)⁻¹ • x` for `x ∈ E`, which solve `v' = -tanh(s) v`;
* it is onto, since its cokernel is the kernel of `D`;
* it is Fredholm of index `dim E`, the negative of the index of `D`, by the reversal law
  `TauCeti.WeakDerivStep.index_trajectoryOperator_adjoint_comp_neg`.

For `E = ℝ` this says that `d/ds + tanh s` has kernel spanned by `sech s`, cokernel `0` and
index `1`. Written as `d/ds - B(s)` with `B = tanh • id` run backwards, whose eigenvalue crosses
from `1` to `-1`, this is again `index (d/ds - B(s)) = -SF(B)`.

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
* `TauCeti.WeakDerivStep.mem_ker_trajectoryOperator_tanh_smul_id_iff`: the kernel of
  `d/ds + tanh s` consists of the classes of `(cosh s)⁻¹ • x`.
* `TauCeti.WeakDerivStep.range_trajectoryOperator_tanh_smul_id`: `d/ds + tanh s` is onto.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_tanh_smul_id` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_tanh_smul_id`: `d/ds + tanh s` is Fredholm of
  index `dim E`.

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

/-- **The kernel of `d/ds + tanh s`.** For the `L∞` class `AL` of `s ↦ tanh(s) • id` on a real
Banach space `F`, an element `u` of `W^{1,2}(ℝ, F)` lies in the kernel of `u ↦ u' + AL u` exactly
when its value is almost everywhere `(cosh s)⁻¹ • x` for some `x ∈ F`. For `F = ℝ` the kernel is
the line spanned by `sech`. -/
theorem mem_ker_trajectoryOperator_tanh_smul_id_iff
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ F)
    {u : WeakDerivStep volume ⊤ 2
      (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))} :
    u ∈ (trajectoryOperator (p := 2) AL).ker ↔ ∃ x : F,
      ⇑(prev (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
        =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ (Real.cosh s)⁻¹ • x := by
  constructor
  · -- An element of the kernel is a solution of `v' = -tanh(s) v`, hence `(cosh s)⁻¹ • v 0`.
    intro hu
    obtain ⟨v, hv, huv⟩ := exists_hasDerivAt_of_trajectoryOperator_eq_zero continuous_tanh_smul_id
      hAL hu
    refine ⟨v 0, ?_⟩
    rwa [eq_inv_cosh_smul_of_hasDerivAt (v := v) fun s ↦ by simpa using hv s] at huv
  · -- Conversely `(cosh s)⁻¹ • x` is the value of an element of the kernel, which is `u`.
    rintro ⟨x, hx⟩
    obtain ⟨w, hw, hwx⟩ := exists_trajectoryOperator_eq_zero_of_hasDerivAt (p := 2) hAL
      (fun s ↦ (hasDerivAt_inv_cosh_smul x s).congr_deriv (by simp [smul_comm (Real.tanh s)]))
      (memLp_inv_cosh.smul (memLp_top_const x))
    rwa [show u = w from ext (Lp.ext (hx.trans hwx.symm))]

end Banach

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

/-- If `AL` is the class of `s ↦ c(s) • id`, then `-AL` is the class of `s ↦ -c(s) • id`. -/
private theorem neg_ae_eq_neg_smul_id {c : ℝ → ℝ}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ c s • ContinuousLinearMap.id ℝ E) :
    -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-c s) • ContinuousLinearMap.id ℝ E := by
  filter_upwards [Lp.coeFn_neg AL, hAL] with s hneg hs
  rw [hneg, Pi.neg_apply, hs, neg_smul]

/-- The class `-AL` is that of `s ↦ tanh(s) • id`. -/
private theorem neg_ae_eq_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E := by
  simpa using neg_ae_eq_neg_smul_id hAL

/-- Scalar multiples of the identity are self-adjoint, so the class `AL` of `s ↦ c(s) • id` is
also the class of the adjoint coefficients. -/
private theorem ae_eq_adjoint_of_ae_eq_smul_id [FiniteDimensional ℝ E] {c : ℝ → ℝ}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ c s • ContinuousLinearMap.id ℝ E) :
    ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ), AL s = ContinuousLinearMap.adjoint (AL s) := by
  filter_upwards [hAL] with s hs
  simp [hs, ContinuousLinearMap.adjoint_id]

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
    (ae_eq_adjoint_of_ae_eq_smul_id hAL)]
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

/-- The coefficient `s ↦ -tanh(s) • id` is a continuous family of symmetric operators with limits
`id` at `-∞` and `-id` at `+∞`, both bounded below by `1`. So both limits have Lyapunov forms and
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm` applies. -/
private theorem neg_tanh_smul_id_hypotheses :
    Continuous (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) ∧
      (ContinuousLinearMap.id ℝ E).HasLyapunovForm ∧
      (-ContinuousLinearMap.id ℝ E).HasLyapunovForm ∧
      Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atBot
        (𝓝 (ContinuousLinearMap.id ℝ E)) ∧
      Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atTop
        (𝓝 (-ContinuousLinearMap.id ℝ E)) := by
  have hsym (s : ℝ) : ((-Real.tanh s) • ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric :=
    fun x y ↦ by simp [real_inner_smul_left, real_inner_smul_right]
  have hbot : Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atBot
      (𝓝 (ContinuousLinearMap.id ℝ E)) := by
    simpa using Real.tendsto_tanh_atBot.neg.smul_const (ContinuousLinearMap.id ℝ E)
  have htop : Tendsto (fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) atTop
      (𝓝 (-ContinuousLinearMap.id ℝ E)) := by
    simpa using Real.tendsto_tanh_atTop.neg.smul_const (ContinuousLinearMap.id ℝ E)
  exact ⟨Real.continuous_tanh.neg.smul continuous_const,
    ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym hbot one_pos (by simp),
    ContinuousLinearMap.hasLyapunovForm_of_tendsto_of_isSymmetric hsym htop one_pos (by simp),
    hbot, htop⟩

variable [FiniteDimensional ℝ E]

/-- **The trajectory operator `d/ds - tanh s` is Fredholm.** For the `L∞` class `AL` of
`s ↦ -tanh(s) • id` on a finite-dimensional real inner product space `E`, the operator
`u ↦ u' + AL u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_neg_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨hA, hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  exact isFredholm_trajectoryOperator_of_hasLyapunovForm hA
    hminus hplus hbot htop AL hAL

/-- **The index of `d/ds - tanh s` is `-dim E`.** For the `L∞` class `AL` of `s ↦ -tanh(s) • id`
on a finite-dimensional real inner product space `E`, the trajectory operator `u ↦ u' + AL u`
from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index `-dim E`: its kernel is zero and its cokernel is
`{(cosh s)⁻¹ • x | x ∈ E}`. For `E = ℝ` the index is `-1`. -/
theorem index_trajectoryOperator_neg_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ (-Real.tanh s) • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index = -(Module.finrank ℝ E : ℤ) := by
  obtain ⟨hA, hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  -- The coefficients are symmetric, so `AL` is also the class of their adjoints.
  have hadj : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ContinuousLinearMap.adjoint ((-Real.tanh s) • ContinuousLinearMap.id ℝ E) := by
    filter_upwards [hAL] with s hs
    simp [hs, ContinuousLinearMap.adjoint_id]
  rw [index_trajectoryOperator_of_hasLyapunovForm hA
      hminus hplus hbot htop AL AL hAL hadj,
    finrank_ker_trajectoryOperator continuous_neg_tanh_smul_id AL hAL,
    finrank_ker_trajectoryOperator continuous_tanh_smul_id (-AL) (neg_ae_eq_tanh_smul_id hAL),
    squareIntegrableSolutions_neg_tanh_smul_id, squareIntegrableSolutions_tanh_smul_id,
    finrank_bot, finrank_top]
  simp

/-- The class `AL` of `s ↦ tanh(s) • id` is that of the reversal `s ↦ A(-s)†` of the coefficient
`A(s) = -tanh(s) • id` of `d/ds - tanh s`. -/
private theorem ae_eq_adjoint_neg_tanh_smul_id_neg
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E) :
    AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ ContinuousLinearMap.adjoint ((-Real.tanh (-s)) • ContinuousLinearMap.id ℝ E) := by
  filter_upwards [hAL] with s hs
  simp [hs, ContinuousLinearMap.adjoint_id]

/-- **The trajectory operator `d/ds + tanh s` is Fredholm.** For the `L∞` class `AL` of
`s ↦ tanh(s) • id` on a finite-dimensional real inner product space `E`, the operator
`u ↦ u' + AL u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm. Its coefficient is the reversal of
that of `d/ds - tanh s`. -/
theorem isFredholm_trajectoryOperator_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨hA, hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  exact isFredholm_trajectoryOperator_adjoint_comp_neg hA
    hminus hplus hbot htop AL (ae_eq_adjoint_neg_tanh_smul_id_neg hAL)

/-- **The trajectory operator `d/ds + tanh s` is onto.** For the `L∞` class `AL` of
`s ↦ tanh(s) • id` on a finite-dimensional real inner product space `E`, the operator
`u ↦ u' + AL u` maps `W^{1,2}(ℝ, E)` onto `L²(ℝ, E)`: its cokernel is the kernel of
`d/ds - tanh s`, which is zero. -/
theorem range_trajectoryOperator_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).range = ⊤ :=
  LinearMap.range_eq_top.2 <| (surjective_trajectoryOperator_iff_ker_neg_eq_bot
    (ae_eq_adjoint_of_ae_eq_smul_id hAL)
    (isFredholm_trajectoryOperator_tanh_smul_id hAL).isClosed_range).2
    (ker_trajectoryOperator_neg_tanh_smul_id (neg_ae_eq_neg_smul_id hAL))

/-- **The index of `d/ds + tanh s` is `dim E`.** For the `L∞` class `AL` of `s ↦ tanh(s) • id`
on a finite-dimensional real inner product space `E`, the trajectory operator `u ↦ u' + AL u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index `dim E`: its kernel is `{(cosh s)⁻¹ • x | x ∈ E}` and its
cokernel is zero. This is minus the index of `d/ds - tanh s`, the trajectory operator of the
reversed coefficient. For `E = ℝ` the index is `1`. -/
theorem index_trajectoryOperator_tanh_smul_id
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ Real.tanh s • ContinuousLinearMap.id ℝ E) :
    (trajectoryOperator (p := 2) AL).index = Module.finrank ℝ E := by
  obtain ⟨hA, hminus, hplus, hbot, htop⟩ := neg_tanh_smul_id_hypotheses (E := E)
  have hneg := neg_ae_eq_neg_smul_id hAL
  rw [index_trajectoryOperator_adjoint_comp_neg hA
      hminus hplus hbot htop (-AL) AL hneg (ae_eq_adjoint_neg_tanh_smul_id_neg hAL),
    index_trajectoryOperator_neg_tanh_smul_id hneg, neg_neg]

end WeakDerivStep

end TauCeti

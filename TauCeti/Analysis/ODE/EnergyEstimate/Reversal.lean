/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel

/-!
# Time reversal of trajectory operators

Let `A` be a continuous family of operators. Reflecting time, `s ↦ -s`, shows that the trajectory
operator `D_A u = u' + A u` and the trajectory operator `d/ds - A(-s)` of the reflected coefficient
`s ↦ -A(-s)` have kernels of the same dimension
(`TauCeti.WeakDerivStep.finrank_ker_trajectoryOperator_neg_comp_neg`, which holds on any real
Banach space).

On a finite-dimensional real inner product space `E`, the cokernel of `D_A` is the kernel of its
formal adjoint `-d/ds + A†`, which is `-D_{-A†}`. Reflecting time in that kernel gives the kernel
of `D_R` for the **reversed coefficient** `R(s) = A(-s)†`. Reversal therefore exchanges the kernel
and the cokernel of the trajectory operator:

* when the limits `A±` of `A` at `±∞` are hyperbolic (have Lyapunov forms), so are the limits
  `A∓†` of `R` at `±∞`, and `D_R` is Fredholm
  (`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_adjoint_comp_neg`);
* its index is the negative of the index of `D_A`
  (`TauCeti.WeakDerivStep.index_trajectoryOperator_adjoint_comp_neg`).

For a family of symmetric operators, `R(s) = A(-s)` is the path `A` run backwards, and the index of
`d/ds + A` is its spectral flow
(`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finsum_sigPos_sub_sigNeg_crossingForm`). So
this is the operator form of the reversal law of spectral flow (`TauCeti.spectralFlow_comp_neg`):
running the path backwards negates the spectral flow and the index. For instance, `d/ds + tanh s`
has index `dim E`, the negative of the index `-dim E` of `d/ds - tanh s`
(`TauCeti.WeakDerivStep.index_trajectoryOperator_tanh_smul_id`).

## Main results

* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_adjoint_comp_neg`: the trajectory operator
  of the reversed coefficient `s ↦ A(-s)†` is Fredholm when the limits of `A` are hyperbolic.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_adjoint_comp_neg`: its index is minus that of
  `D_A`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33 (the index of `d/ds + A(s)` is the spectral flow of `A`, which changes sign
  when the path is reversed).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter ContinuousLinearMap
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- The reversed coefficient `s ↦ A(-s)†` is continuous and has the limits `A⁺†` at `-∞` and `A⁻†`
at `+∞`. -/
private theorem adjoint_comp_neg_hypotheses (hA : Continuous A) {Aminus Aplus : E →L[ℝ] E}
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus)) :
    Continuous (fun s ↦ adjoint (A (-s))) ∧
      Tendsto (fun s ↦ adjoint (A (-s))) atBot (𝓝 (adjoint Aplus)) ∧
      Tendsto (fun s ↦ adjoint (A (-s))) atTop (𝓝 (adjoint Aminus)) :=
  ⟨adjoint.continuous.comp (hA.comp continuous_neg),
    (adjoint.continuous.tendsto Aplus).comp (htop.comp tendsto_neg_atBot_atTop),
    (adjoint.continuous.tendsto Aminus).comp (hbot.comp tendsto_neg_atTop_atBot)⟩

/-- **The reversed trajectory operator is Fredholm.** Let `A` be a continuous family of operators on
a finite-dimensional real inner product space whose limits `A±` at `±∞` have Lyapunov forms. Then
the trajectory operator `u ↦ u' + A(-s)† u` of the reversed coefficient, from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)`, is Fredholm. -/
theorem isFredholm_trajectoryOperator_adjoint_comp_neg (hA : Continuous A)
    {Aminus Aplus : E →L[ℝ] E} (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (RL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hRL : RL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ adjoint (A (-s))) :
    (trajectoryOperator (p := 2) RL).IsFredholm := by
  obtain ⟨hR, hRbot, hRtop⟩ := adjoint_comp_neg_hypotheses hA hbot htop
  exact isFredholm_trajectoryOperator_of_hasLyapunovForm hR hplus.adjoint hminus.adjoint hRbot
    hRtop RL hRL

/-- **Reversing the coefficient negates the index.** Let `A` be a continuous family of operators on
a finite-dimensional real inner product space whose limits `A±` at `±∞` have Lyapunov forms. Then
the index of the trajectory operator `u ↦ u' + A(-s)† u` of the reversed coefficient is minus the
index of `D_A u = u' + A u`, both from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)`: reflecting time identifies
the kernel of each operator with the cokernel of the other. For symmetric `A` the reversed
coefficient is `s ↦ A(-s)`, the path run backwards, and through the identification of the index
with the spectral flow this is the reversal law of spectral flow. -/
theorem index_trajectoryOperator_adjoint_comp_neg (hA : Continuous A)
    {Aminus Aplus : E →L[ℝ] E} (hminus : Aminus.HasLyapunovForm) (hplus : Aplus.HasLyapunovForm)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (AL RL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hRL : RL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ adjoint (A (-s))) :
    (trajectoryOperator (p := 2) RL).index = -(trajectoryOperator (p := 2) AL).index := by
  obtain ⟨hR, hRbot, hRtop⟩ := adjoint_comp_neg_hypotheses hA hbot htop
  -- `L∞` classes of the pointwise adjoints of `A` and of the reversed coefficient.
  obtain ⟨BL, hBL⟩ := exists_ae_eq_adjoint AL hAL
  obtain ⟨SL, hSL⟩ := exists_ae_eq_adjoint RL hRL
  have hnegBL : -BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ -adjoint (A s) := by
    filter_upwards [Lp.coeFn_neg BL, hBL] with s hs hBs
    rw [hs, Pi.neg_apply, hBs]
  have hnegSL : -SL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ -A (-s) := by
    filter_upwards [Lp.coeFn_neg SL, hSL] with s hs hSs
    rw [hs, Pi.neg_apply, hSs, adjoint_adjoint]
  -- The kernel of `D_R` is the reflection of the cokernel `ker D_{-A†}` of `D_A`, and the cokernel
  -- `ker D_{-A(-·)}` of `D_R` is the reflection of the kernel of `D_A`.
  have hRadj : RL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ -(fun t ↦ -adjoint (A t)) (-s) :=
    hRL.trans (.of_forall fun s ↦ (neg_neg _).symm)
  have hker := finrank_ker_trajectoryOperator_neg_comp_neg (A := fun t ↦ -adjoint (A t))
    (adjoint.continuous.comp hA).neg (-BL) RL hnegBL hRadj
  have hcoker := finrank_ker_trajectoryOperator_neg_comp_neg hA AL (-SL) hAL hnegSL
  have hR' := index_trajectoryOperator_of_hasLyapunovForm hR hplus.adjoint hminus.adjoint hRbot
    hRtop RL SL hRL hSL
  rw [hker, hcoker] at hR'
  rw [hR', index_trajectoryOperator_of_hasLyapunovForm hA hminus hplus hbot htop AL BL hAL hBL]
  ring

end TauCeti.WeakDerivStep

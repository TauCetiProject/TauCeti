/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Analysis.ODE.EnergyEstimate.Fredholm
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel

/-!
# The index of the trajectory operator

Let `A : ℝ → End(E)` be a `C¹` family of symmetric operators on a finite-dimensional real inner
product space `E`, with invertible limits `A±` at `±∞` and with `A'` tending to zero at both ends.
The trajectory operator `D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)` is then Fredholm
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`). This file proves:

* the index of `D_A` depends only on the limits `A±`: two such families with the same limits give
  operators of the same index;
* the index vanishes when the two limits agree;
* the index is the dimension of the space of square-integrable solutions of `v' = -A v` minus that
  of `v' = A v`, and this holds for every continuous symmetric `A` for which `D_A` has closed range.

For the first statement, the affine family `(1 - t) A + t B` has the same limits as `A` and `B` for
every real `t`, so each of its trajectory operators is Fredholm. The trajectory operator depends
continuously on its `L∞` coefficient (`TauCeti.WeakDerivStep.lipschitzWith_trajectoryOperator`),
so the index is constant along this family. For the second, a constant coefficient `A₀` with a
spectral gap gives an injective `D_{A₀}` and an injective formal adjoint `D_{-A₀}`, by the
coercive estimate `TauCeti.WeakDerivStep.ker_trajectoryOperator_eq_bot`, so `D_{A₀}` has index
zero; a family with equal limits `A₀` has the index of the constant family.

The first statement is the invariance of the index under deformations of the coefficient family
that fix its limits; the second is its value when the limits agree. Together they reduce the
computation of the index for arbitrary limits to that of one family for each pair of limits. That
computation, which identifies the index with the difference of the numbers of negative eigenvalues
of `A⁻` and `A⁺`, is not proved here. The third statement is the form it takes: the kernel of
`D_A` is the space of square-integrable solutions of `v' + A v = 0`
(`TauCeti.WeakDerivStep.kerTrajectoryOperatorEquiv`), and the cokernel is the kernel of the formal
adjoint `D_{-A}`.

## Main declarations

* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_of_tendsto`: families with the same limits
  have trajectory operators of the same index.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_zero_of_tendsto`: a family with equal limits
  at both ends gives index zero.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_sub_finrank_of_isClosed_range`: when
  the range of `D_A` is closed, the index of `D_A` is the dimension of the square-integrable
  solutions of `v' = -A v` minus that of `v' = A v`.
* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_sub_finrank`: the same formula under
  the hypotheses of `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (stability of the Fredholm index).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33 (the index of `d/ds + A(s)` as a spectral flow, and its homotopy invariance).
* M. Schwarz, *Morse Homology*, Chapter 2 (the index of linearized trajectory operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology InnerProductSpace

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For two coefficient families satisfying the hypotheses of
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator` with the same limits, the affine combination
`(1 - t) A + t B` satisfies them too, for every real `t`, so its trajectory operator is Fredholm. -/
private theorem isFredholm_trajectoryOperator_one_sub_smul_add_smul {A B : ℝ → E →L[ℝ] E}
    (hA : ContDiff ℝ 1 A) (hAsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    (hB : ContDiff ℝ 1 B) (hBsym : ∀ s, (B s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hAbot : Tendsto A atBot (𝓝 Aminus)) (hAtop : Tendsto A atTop (𝓝 Aplus))
    (hBbot : Tendsto B atBot (𝓝 Aminus)) (hBtop : Tendsto B atTop (𝓝 Aplus))
    (hdAbot : Tendsto (deriv A) atBot (𝓝 0)) (hdAtop : Tendsto (deriv A) atTop (𝓝 0))
    (hdBbot : Tendsto (deriv B) atBot (𝓝 0)) (hdBtop : Tendsto (deriv B) atTop (𝓝 0))
    (AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B) (t : ℝ) :
    (trajectoryOperator (p := 2) ((1 - t) • AL + t • BL)).IsFredholm := by
  set C : ℝ → E →L[ℝ] E := fun s ↦ (1 - t) • A s + t • B s
  have hC : ContDiff ℝ 1 C := (hA.const_smul _).add (hB.const_smul _)
  have hCsym : ∀ s, (C s).toLinearMap.IsSymmetric := fun s x y ↦ by
    simp only [C, ContinuousLinearMap.coe_coe, add_apply,
      smul_apply, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, (hAsym s).apply_clm, (hBsym s).apply_clm]
  have hdC : deriv C = fun s ↦ (1 - t) • deriv A s + t • deriv B s := funext fun s ↦ by
    have hAd := ((hA.differentiable one_ne_zero s).hasDerivAt).const_smul (1 - t)
    have hBd := ((hB.differentiable one_ne_zero s).hasDerivAt).const_smul t
    exact (hAd.add hBd).deriv
  -- The combination of two families tending to the same limit tends to that limit.
  have hlim : ∀ {l : Filter ℝ} {L : E →L[ℝ] E} {F G : ℝ → E →L[ℝ] E},
      Tendsto F l (𝓝 L) → Tendsto G l (𝓝 L) →
        Tendsto (fun s ↦ (1 - t) • F s + t • G s) l (𝓝 L) := fun hF hG ↦ by
    simpa only [← add_smul, sub_add_cancel, one_smul] using
      (hF.const_smul (1 - t)).add (hG.const_smul t)
  refine isFredholm_trajectoryOperator hC hCsym hα hminus hplus (hlim hAbot hBbot)
    (hlim hAtop hBtop) (hdC ▸ hlim hdAbot hdBbot) (hdC ▸ hlim hdAtop hdBtop) _ ?_
  filter_upwards [Lp.coeFn_add ((1 - t) • AL) (t • BL), Lp.coeFn_smul (1 - t) AL,
    Lp.coeFn_smul t BL, hAL, hBL] with s hs h1 h2 hAs hBs
  simp only [hs, Pi.add_apply, h1, h2, Pi.smul_apply, hAs, hBs, C]

/-- **The index of the trajectory operator depends only on the limits.** Let `A` and `B` be `C¹`
families of symmetric operators on a finite-dimensional real inner product space with the same
invertible limits `A±` at `±∞`, and with derivatives tending to zero at both ends. Then the
trajectory operators `u ↦ u' + A u` and `u ↦ u' + B u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` have the
same Fredholm index. -/
theorem index_trajectoryOperator_eq_of_tendsto {A B : ℝ → E →L[ℝ] E}
    (hA : ContDiff ℝ 1 A) (hAsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    (hB : ContDiff ℝ 1 B) (hBsym : ∀ s, (B s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hAbot : Tendsto A atBot (𝓝 Aminus)) (hAtop : Tendsto A atTop (𝓝 Aplus))
    (hBbot : Tendsto B atBot (𝓝 Aminus)) (hBtop : Tendsto B atTop (𝓝 Aplus))
    (hdAbot : Tendsto (deriv A) atBot (𝓝 0)) (hdAtop : Tendsto (deriv A) atTop (𝓝 0))
    (hdBbot : Tendsto (deriv B) atBot (𝓝 0)) (hdBtop : Tendsto (deriv B) atTop (𝓝 0))
    (AL BL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hBL : BL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] B) :
    (trajectoryOperator (p := 2) AL).index = (trajectoryOperator (p := 2) BL).index := by
  have hcont : Continuous fun t : ℝ ↦ trajectoryOperator (p := 2) ((1 - t) • AL + t • BL) :=
    (lipschitzWith_trajectoryOperator (F := E) (mu := volume) (Omega := ⊤) (p := 2)).continuous.comp
      (by fun_prop)
  simpa using Continuous.index_eq_of_preconnectedSpace hcont
    (isFredholm_trajectoryOperator_one_sub_smul_add_smul hA hAsym hB hBsym hα hminus hplus hAbot
      hAtop hBbot hBtop hdAbot hdAtop hdBbot hdBtop AL BL hAL hBL) 0 1

/-- A constant coefficient gives index zero. For a symmetric operator `A₀` on a
finite-dimensional real inner product space with `α ‖v‖ ≤ ‖A₀ v‖` for some `α > 0`, the trajectory
operator `u ↦ u' + A₀ u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index zero. Both it and its formal
adjoint `-d/ds + A₀` are injective. -/
private theorem index_trajectoryOperator_const {A₀ : E →L[ℝ] E}
    (hsym : (A₀ : E →ₗ[ℝ] E).IsSymmetric) {α : ℝ} (hα : 0 < α) (hgap : ∀ v, α * ‖v‖ ≤ ‖A₀ v‖)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun _ ↦ A₀) :
    (trajectoryOperator (p := 2) AL).index = 0 := by
  have hderiv : deriv (fun _ : ℝ ↦ A₀) = 0 := funext fun _ ↦ deriv_const _ _
  have hker := ker_trajectoryOperator_eq_bot (A := fun _ ↦ A₀) contDiff_const (fun _ ↦ hsym)
    hα.le (fun _ ↦ hgap) (β := 0) (fun _ v ↦ by simp) (by positivity) AL hAL
  have hnker := ker_trajectoryOperator_eq_bot (A := fun _ ↦ -A₀) contDiff_const
    (fun _ x y ↦ by simp [hsym.apply_clm]) hα.le (fun _ v ↦ by simpa using hgap v) (β := 0)
    (fun _ v ↦ by simp) (by positivity) (-AL)
    (by filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs; simp only [hs, Pi.neg_apply, hAs])
  rw [index_trajectoryOperator contDiff_const (fun _ ↦ hsym) hα hgap hgap tendsto_const_nhds
    tendsto_const_nhds (hderiv ▸ tendsto_const_nhds) (hderiv ▸ tendsto_const_nhds) AL hAL, hker,
    hnker]
  simp

/-- **Equal limits give index zero.** Let `A` be a `C¹` family of symmetric operators on a
finite-dimensional real inner product space with the same invertible limit `A₀` at `-∞` and at
`+∞`, and with derivative tending to zero at both ends. Then the trajectory operator
`u ↦ u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` has index zero. -/
theorem index_trajectoryOperator_eq_zero_of_tendsto {A : ℝ → E →L[ℝ] E}
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric) {A₀ : E →L[ℝ] E} {α : ℝ}
    (hα : 0 < α) (hgap : ∀ v, α * ‖v‖ ≤ ‖A₀ v‖)
    (hbot : Tendsto A atBot (𝓝 A₀)) (htop : Tendsto A atTop (𝓝 A₀))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).index = 0 := by
  -- The limit of symmetric operators is symmetric, since self-adjointness is a closed condition.
  have hsym₀ : (A₀ : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp <|
      (isClosed_eq continuous_star continuous_id).mem_of_tendsto htop
        (Eventually.of_forall fun s ↦ ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
          (hsym s))
  let A₀L := (memLp_top_const (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) A₀).toLp
  have hA₀L : A₀L =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun _ ↦ A₀ := MemLp.coeFn_toLp _
  rw [index_trajectoryOperator_eq_of_tendsto hA hsym contDiff_const (fun _ ↦ hsym₀) hα hgap hgap
    hbot htop tendsto_const_nhds tendsto_const_nhds hdbot hdtop (by simp) (by simp) AL A₀L hAL
    hA₀L]
  exact index_trajectoryOperator_const hsym₀ hα hgap A₀L hA₀L

variable {A : ℝ → E →L[ℝ] E}

/-- **The index of a trajectory operator with closed range counts square-integrable solutions.**
For a continuous family `A` of symmetric operators on a finite-dimensional real inner product
space `E` such that the range of `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is closed,
the index of `D_A` is the dimension of the space of square-integrable solutions of `v' = -A v`
minus the dimension of the space of square-integrable solutions of `v' = A v`. -/
theorem index_trajectoryOperator_eq_finrank_sub_finrank_of_isClosed_range
    (hA : Continuous A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hclosed : IsClosed ((trajectoryOperator (p := 2) AL).range :
      Set (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (squareIntegrableSolutions A) : ℤ) -
        Module.finrank ℝ (squareIntegrableSolutions (-A)) := by
  have hALsym : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      (AL s).toLinearMap.IsSymmetric := by
    filter_upwards [hAL] with s hs
    rw [hs]
    exact hsym s
  have hnegAL : -AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] -A := by
    filter_upwards [Lp.coeFn_neg AL, hAL] with s hs hAs
    simp only [hs, Pi.neg_apply, hAs]
  rw [index_trajectoryOperator_of_isClosed_range hALsym hclosed,
    finrank_ker_trajectoryOperator hA AL hAL, finrank_ker_trajectoryOperator hA.neg (-AL) hnegAL]

/-- **The index of the trajectory operator counts square-integrable solutions.** Under the
hypotheses of `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`, the index of
`D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is the dimension of the space of
square-integrable solutions of `v' = -A v` minus the dimension of the space of square-integrable
solutions of `v' = A v`. This specializes
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_sub_finrank_of_isClosed_range`. -/
theorem index_trajectoryOperator_eq_finrank_sub_finrank
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (squareIntegrableSolutions A) : ℤ) -
        Module.finrank ℝ (squareIntegrableSolutions (-A)) :=
  index_trajectoryOperator_eq_finrank_sub_finrank_of_isClosed_range hA.continuous hsym AL hAL
    (isClosed_range_trajectoryOperator hA hsym hα hminus hplus hbot htop hdbot hdtop AL hAL)

end TauCeti.WeakDerivStep

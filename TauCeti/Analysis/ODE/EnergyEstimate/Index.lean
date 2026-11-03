/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Symmetric.Basic
public import TauCeti.Analysis.ODE.EnergyEstimate.Fredholm
public import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.ExpDecay

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
  of `v' = A v`, and this holds for every continuous symmetric `A` for which `D_A` has closed range;
* the index is `n⁻(A⁻) - n⁻(A⁺)`, where `n⁻(B)` is the number of negative eigenvalues of `B`
  counted with multiplicity, that is, the dimension of the sum of its eigenspaces at negative
  eigenvalues.

For the first statement, the affine family `(1 - t) A + t B` has the same limits as `A` and `B` for
every real `t`, so each of its trajectory operators is Fredholm. The trajectory operator depends
continuously on its `L∞` coefficient (`TauCeti.WeakDerivStep.lipschitzWith_trajectoryOperator`),
so the index is constant along this family. For the second, a constant coefficient `A₀` with a
spectral gap gives an injective `D_{A₀}` and an injective formal adjoint `D_{-A₀}`, by the
coercive estimate `TauCeti.WeakDerivStep.ker_trajectoryOperator_eq_bot`, so `D_{A₀}` has index
zero; a family with equal limits `A₀` has the index of the constant family.

The first statement is the invariance of the index under deformations of the coefficient family
that fix its limits; the second is its value when the limits agree. Together they reduce the
computation of the index for arbitrary limits to that of one family for each pair of limits. The
third statement is the form that computation takes: the kernel of `D_A` is the space of
square-integrable solutions of `v' + A v = 0` (`TauCeti.WeakDerivStep.kerTrajectoryOperatorEquiv`),
and the cokernel is the kernel of the formal adjoint `D_{-A}`.

For the fourth statement we use the model family `ψ(-s) A⁻ + ψ(s) A⁺`, where `ψ` is Mathlib's
`Real.smoothTransition`. On `[0, ∞)` it is `ψ(s) A⁺`, a scalar multiple of one symmetric operator,
so a solution of `v' = -ψ(s) A⁺ v` multiplies the coordinate of `v` along an eigenvector of `A⁺`
with eigenvalue `λ` by `exp (-λ ∫₀ˢ ψ)`. It is square integrable on `(0, ∞)` exactly when `v 0`
lies in the positive spectral subspace `W` of `A⁺`. Likewise it is square integrable on `(-∞, 0)`
exactly when `v 0` lies in the negative spectral subspace `U` of `A⁻`. So the kernel of the model
operator is `W ⊓ U`, and the same argument for `-A` identifies its cokernel with `Wᗮ ⊓ Uᗮ`,
because the positive and negative spectral subspaces of an invertible symmetric operator are
orthogonal complements. Hence the index is `dim (W ⊓ U) - dim (W ⊔ U)ᗮ = dim W + dim U - dim E`,
which is `n⁻(A⁻) - n⁻(A⁺)`.

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
* `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`:
  the index is the number of negative eigenvalues of `A⁻` minus that of `A⁺`.

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
  have hsym₀ : (A₀ : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isClosed_setOf_isSymmetric.mem_of_tendsto htop (.of_forall hsym)
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

/-! ### The index as a difference of Morse indices -/

namespace TauCeti

open Set NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primitive `G(t) = ∫₀ᵗ ψ` of Mathlib's smooth transition function `ψ`, which vanishes on
`(-∞, 0]` and equals `1` on `[1, ∞)`. So `G` vanishes on `(-∞, 0]` and has slope `1` on
`[1, ∞)`. -/
private def transitionIntegral (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.smoothTransition s

private theorem hasDerivAt_transitionIntegral (t : ℝ) :
    HasDerivAt transitionIntegral (Real.smoothTransition t) t :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem continuous_transitionIntegral : Continuous transitionIntegral :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_transitionIntegral t).continuousAt

private theorem transitionIntegral_of_nonpos {t : ℝ} (ht : t ≤ 0) : transitionIntegral t = 0 := by
  have h : EqOn Real.smoothTransition (fun _ ↦ (0 : ℝ)) (uIcc 0 t) := fun s hs ↦ by
    rw [uIcc_of_ge ht] at hs
    exact Real.smoothTransition.zero_of_nonpos hs.2
  rw [transitionIntegral, intervalIntegral.integral_congr h, intervalIntegral.integral_zero]

private theorem transitionIntegral_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ transitionIntegral t :=
  intervalIntegral.integral_nonneg ht fun s _ ↦ Real.smoothTransition.nonneg s

/-- Since `ψ = 1` on `[1, ∞)`, the primitive `G` grows at unit speed there. -/
private theorem sub_one_le_transitionIntegral {t : ℝ} (ht : 0 ≤ t) :
    t - 1 ≤ transitionIntegral t := by
  rcases le_total t 1 with h | h
  · linarith [transitionIntegral_nonneg ht]
  have hint (a b : ℝ) : IntervalIntegrable Real.smoothTransition MeasureTheory.volume a b :=
    Real.smoothTransition.continuous.intervalIntegrable a b
  have h1 : EqOn Real.smoothTransition (fun _ ↦ (1 : ℝ)) (uIcc 1 t) := fun s hs ↦ by
    rw [uIcc_of_le h] at hs
    exact Real.smoothTransition.one_of_one_le hs.1
  rw [transitionIntegral, ← intervalIntegral.integral_add_adjacent_intervals (hint 0 1) (hint 1 t),
    intervalIntegral.integral_congr h1]
  simpa using intervalIntegral.integral_nonneg zero_le_one fun s _ ↦ Real.smoothTransition.nonneg s

/-- The model coefficient `ψ(-s) A⁻ + ψ(s) A⁺`, equal to `A⁻` on `(-∞, -1]` and to `A⁺` on
`[1, ∞)`. On each half-line it is a scalar multiple of a single operator, so the solutions of
`v' = -A(s) v` there are explicit in the eigenbasis of that operator. -/
private def modelCoefficient (Aminus Aplus : E →L[ℝ] E) (s : ℝ) : E →L[ℝ] E :=
  Real.smoothTransition (-s) • Aminus + Real.smoothTransition s • Aplus

variable {Aminus Aplus : E →L[ℝ] E}

private theorem modelCoefficient_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    modelCoefficient Aminus Aplus s = Real.smoothTransition s • Aplus := by
  simp [modelCoefficient, Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr hs)]

private theorem modelCoefficient_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    modelCoefficient Aminus Aplus s = Real.smoothTransition (-s) • Aminus := by
  simp [modelCoefficient, Real.smoothTransition.zero_of_nonpos hs]

private theorem neg_modelCoefficient :
    -modelCoefficient Aminus Aplus = modelCoefficient (-Aminus) (-Aplus) := by
  funext s
  simp only [modelCoefficient, Pi.neg_apply, neg_add, smul_neg]

private theorem contDiff_modelCoefficient : ContDiff ℝ 1 (modelCoefficient Aminus Aplus) :=
  ((Real.smoothTransition.contDiff.comp contDiff_neg).smul contDiff_const).add
    (Real.smoothTransition.contDiff.smul contDiff_const)

private theorem isSymmetric_modelCoefficient (hminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric)
    (hplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric) (s : ℝ) :
    (modelCoefficient Aminus Aplus s : E →ₗ[ℝ] E).IsSymmetric := fun x y ↦ by
  simp only [modelCoefficient, ContinuousLinearMap.coe_coe, add_apply, smul_apply, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, hminus.apply_clm,
    hplus.apply_clm]

private theorem modelCoefficient_of_le_neg_one {s : ℝ} (hs : s ≤ -1) :
    modelCoefficient Aminus Aplus s = Aminus := by
  rw [modelCoefficient_of_nonpos (by linarith), Real.smoothTransition.one_of_one_le (by linarith),
    one_smul]

private theorem modelCoefficient_of_one_le {s : ℝ} (hs : 1 ≤ s) :
    modelCoefficient Aminus Aplus s = Aplus := by
  rw [modelCoefficient_of_nonneg (by linarith), Real.smoothTransition.one_of_one_le hs, one_smul]

private theorem tendsto_modelCoefficient_atBot :
    Tendsto (modelCoefficient Aminus Aplus) atBot (𝓝 Aminus) :=
  tendsto_const_nhds.congr' <| (eventually_le_atBot (-1)).mono fun _ hs ↦
    (modelCoefficient_of_le_neg_one hs).symm

private theorem tendsto_modelCoefficient_atTop :
    Tendsto (modelCoefficient Aminus Aplus) atTop (𝓝 Aplus) :=
  tendsto_const_nhds.congr' <| (eventually_ge_atTop 1).mono fun _ hs ↦
    (modelCoefficient_of_one_le hs).symm

private theorem tendsto_deriv_modelCoefficient_atBot :
    Tendsto (deriv (modelCoefficient Aminus Aplus)) atBot (𝓝 0) :=
  tendsto_const_nhds.congr' <| (eventually_lt_atBot (-1)).mono fun s hs ↦ by
    rw [(eventuallyEq_of_mem (Iio_mem_nhds hs) fun x (hx : x < -1) ↦
      modelCoefficient_of_le_neg_one hx.le).deriv_eq, deriv_const]

private theorem tendsto_deriv_modelCoefficient_atTop :
    Tendsto (deriv (modelCoefficient Aminus Aplus)) atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop 1).mono fun s hs ↦ by
    rw [(eventuallyEq_of_mem (Ioi_mem_nhds hs) fun x (hx : 1 < x) ↦
      modelCoefficient_of_one_le hx.le).deriv_eq, deriv_const]

private theorem memLp_top_modelCoefficient {μ : Measure ℝ} :
    MemLp (modelCoefficient Aminus Aplus) ∞ μ :=
  memLp_top_of_bound contDiff_modelCoefficient.continuous.aestronglyMeasurable
    (‖Aminus‖ + ‖Aplus‖) (Eventually.of_forall fun s ↦ by
      have hψ (x : ℝ) : ‖Real.smoothTransition x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg x)]
        exact Real.smoothTransition.le_one x
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
        exact mul_le_of_le_one_left (norm_nonneg _) (hψ _))

variable [FiniteDimensional ℝ E] {T : E →L[ℝ] E} {v : ℝ → E}

/-- Along a solution of `v' = -ψ(t) T v` on `[0, ∞)`, for a symmetric `T`, the eigencoordinate of
`v` at an eigenvalue `λ` of `T` is multiplied by `exp (-λ G(t))`. -/
private theorem inner_eigenvectorBasis_eq (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (-(Real.smoothTransition t • T (v t))) t)
    (i : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : 0 ≤ t) :
    ⟪hT.eigenvectorBasis rfl i, v t⟫_ℝ =
      Real.exp (-(hT.eigenvalues rfl i * transitionIntegral t)) *
        ⟪hT.eigenvectorBasis rfl i, v 0⟫_ℝ := by
  set e := hT.eigenvectorBasis rfl i
  set lam := hT.eigenvalues rfl i
  set f : ℝ → ℝ := fun s ↦ Real.exp (lam * transitionIntegral s) * ⟪e, v s⟫_ℝ
  -- The rescaled coordinate `f` has derivative zero on `[0, ∞)`.
  have hf (s : ℝ) (hs : 0 ≤ s) : HasDerivAt f 0 s := by
    have hexp := (Real.hasDerivAt_exp _).comp s ((hasDerivAt_transitionIntegral s).const_mul lam)
    have hinner := (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt s (hv s hs)
    have hTe : ⟪e, T (v s)⟫_ℝ = lam * ⟪e, v s⟫_ℝ := by
      have heig : T e = lam • e := hT.apply_eigenvectorBasis rfl i
      rw [← hT.apply_clm, heig, real_inner_smul_left]
    refine (hexp.mul hinner).congr_deriv ?_
    simp only [Function.comp_apply, innerSL_apply_apply, inner_neg_right, real_inner_smul_right,
      hTe]
    ring
  have hconst := constant_of_has_deriv_right_zero
    (fun s hs ↦ (hf s hs.1).continuousAt.continuousWithinAt)
    (fun s hs ↦ (hf s hs.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  calc ⟪e, v t⟫_ℝ = Real.exp (-(lam * transitionIntegral t)) * f t := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-(lam * transitionIntegral t)) * ⟪e, v 0⟫_ℝ := by
        rw [hconst]
        simp [f, transitionIntegral_of_nonpos le_rfl]

/-- A square-integrable solution of `v' = -ψ(t) T v` on `[0, ∞)`, for a symmetric `T`, starts in
the positive spectral subspace of `T`: a coordinate at a nonpositive eigenvalue does not decay. -/
private theorem mem_pointSpectralSubspace_Ioi_of_integrableOn
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (-(Real.smoothTransition t • T (v t))) t)
    (hint : IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Ioi 0)) :
    v 0 ∈ Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Ioi 0) := by
  have hcoord := inner_eigenvectorBasis_eq hT hv
  set b := hT.eigenvectorBasis rfl
  set lam := hT.eigenvalues rfl
  rw [hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.mem_eigenvectorSpan_iff]
  intro i hi
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply] at hi
  by_contra hlam
  simp only [mem_ofPred_eq, mem_Ioi, not_lt] at hlam
  -- A nonzero coordinate at a nonpositive eigenvalue does not decay, so it is not in `L²`.
  have hconst : IntegrableOn (fun _ : ℝ ↦ ⟪b i, v 0⟫_ℝ ^ 2) (Ioi 0) := by
    refine hint.mono' aestronglyMeasurable_const ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t (ht : 0 < t) ↦ ?_))
    have h1 : 1 ≤ Real.exp (-(lam i * transitionIntegral t)) :=
      Real.one_le_exp (by nlinarith [transitionIntegral_nonneg ht.le])
    have h2 : |⟪b i, v t⟫_ℝ| ≤ |‖v t‖| := by
      simpa [b.orthonormal.1 i] using abs_real_inner_le_norm (b i) (v t)
    calc ‖⟪b i, v 0⟫_ℝ ^ 2‖ = ⟪b i, v 0⟫_ℝ ^ 2 := by simp
      _ ≤ ⟪b i, v t⟫_ℝ ^ 2 := by
        rw [hcoord i ht.le, mul_pow]
        exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ h1)
      _ ≤ ‖v t‖ ^ 2 := sq_le_sq.mpr h2
  rw [integrableOn_const_iff] at hconst
  exact hi (by simpa [Real.volume_Ioi] using hconst)

/-- A solution of `v' = -ψ(t) T v` on `[0, ∞)`, for a symmetric `T`, starting in the positive
spectral subspace of `T` decays exponentially, so it is square integrable on `(0, ∞)`. -/
private theorem integrableOn_Ioi_norm_sq_of_mem (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (-(Real.smoothTransition t • T (v t))) t)
    (hmem : v 0 ∈ Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Ioi 0)) :
    IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Ioi 0) := by
  have hcoord := inner_eigenvectorBasis_eq hT hv
  set b := hT.eigenvectorBasis rfl
  set lam := hT.eigenvalues rfl
  rw [hT.pointSpectralSubspace_eq_eigenvectorSpan rfl,
    LinearMap.IsSymmetric.mem_eigenvectorSpan_iff] at hmem
  have hsum : EqOn (fun t ↦ ∑ i, (Real.exp (-(lam i * transitionIntegral t)) *
      ⟪b i, v 0⟫_ℝ) ^ 2) (fun t ↦ ‖v t‖ ^ 2) (Ioi 0) := fun t (ht : 0 < t) ↦ by
    simp only [← b.sum_sq_norm_inner_right (v t), Real.norm_eq_abs, sq_abs, hcoord _ ht.le]
  refine IntegrableOn.congr_fun ?_ hsum measurableSet_Ioi
  refine integrable_finsetSum _ fun i _ ↦ ?_
  by_cases hc : ⟪b i, v 0⟫_ℝ = 0
  · simp [hc]
  have hpos : 0 < lam i := hmem (by
    simpa [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply] using hc)
  -- At a positive eigenvalue the coordinate decays exponentially.
  refine ((exp_neg_integrableOn_Ioi 0 (by positivity : 0 < 2 * lam i)).const_mul
    (⟪b i, v 0⟫_ℝ ^ 2 * Real.exp (2 * lam i))).mono'
    (((Real.continuous_exp.comp (continuous_const.mul continuous_transitionIntegral).neg).mul
      continuous_const).pow 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t (ht : 0 < t) ↦ ?_)
  have key : Real.exp (-(lam i * transitionIntegral t)) ^ 2 ≤
      Real.exp (2 * lam i) * Real.exp (-(2 * lam i) * t) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [sub_one_le_transitionIntegral ht.le])
  calc ‖(Real.exp (-(lam i * transitionIntegral t)) * ⟪b i, v 0⟫_ℝ) ^ 2‖
      = Real.exp (-(lam i * transitionIntegral t)) ^ 2 * ⟪b i, v 0⟫_ℝ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    _ ≤ Real.exp (2 * lam i) * Real.exp (-(2 * lam i) * t) * ⟪b i, v 0⟫_ℝ ^ 2 :=
        mul_le_mul_of_nonneg_right key (sq_nonneg _)
    _ = ⟪b i, v 0⟫_ℝ ^ 2 * Real.exp (2 * lam i) * Real.exp (-(2 * lam i) * t) := by ring

/-- A solution of `v' = -ψ(t) T v` on `[0, ∞)`, for a symmetric `T`, is square integrable on
`(0, ∞)` exactly when its value at `0` lies in the positive spectral subspace of `T`. -/
private theorem integrableOn_Ioi_norm_sq_iff (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hv : ∀ t, 0 ≤ t → HasDerivAt v (-(Real.smoothTransition t • T (v t))) t) :
    IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Ioi 0) ↔
      v 0 ∈ Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Ioi 0) :=
  ⟨mem_pointSpectralSubspace_Ioi_of_integrableOn hT hv, integrableOn_Ioi_norm_sq_of_mem hT hv⟩

/-- The reflection of `TauCeti.integrableOn_Ioi_norm_sq_iff`: a solution of `v' = -ψ(-t) T v` on
`(-∞, 0]`, for a symmetric `T`, is square integrable on `(-∞, 0)` exactly when its value at `0`
lies in the negative spectral subspace of `T`. -/
private theorem integrableOn_Iio_norm_sq_iff (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hv : ∀ t, t ≤ 0 → HasDerivAt v (-(Real.smoothTransition (-t) • T (v t))) t) :
    IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Iio 0) ↔
      v 0 ∈ Module.End.pointSpectralSubspace (T : E →ₗ[ℝ] E) (Iio 0) := by
  have hw (t : ℝ) (ht : 0 ≤ t) : HasDerivAt (fun s ↦ v (-s))
      (-(Real.smoothTransition t • (-T) (v (-t)))) t := by
    simpa [Function.comp_def] using (hv (-t) (neg_nonpos.mpr ht)).scomp t (hasDerivAt_neg t)
  have h := integrableOn_Ioi_norm_sq_iff hT.neg hw
  rw [ContinuousLinearMap.toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi,
    neg_zero] at h
  rw [← h, ← (Measure.measurePreserving_neg volume).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding]
  simp [Function.comp_def]

/-- The square-integrable solutions of `v' = -A(s) v` for the model coefficient `A` are the
initial values in the positive spectral subspace of `A⁺` and the negative spectral subspace of
`A⁻`: square integrability on `(0, ∞)` and on `(-∞, 0)` impose the two conditions separately. -/
private theorem squareIntegrableSolutions_modelCoefficient
    (hminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric) (hplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric) :
    squareIntegrableSolutions (modelCoefficient Aminus Aplus) =
      Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0) ⊓
        Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0) := by
  -- A solution on the whole line splits into solutions on the two half-lines.
  have hsplit {v : ℝ → E} (hv : ∀ t, HasDerivAt v (-modelCoefficient Aminus Aplus t (v t)) t) :
      (IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Ioi 0) ↔
        v 0 ∈ Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)) ∧
      (IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Iio 0) ↔
        v 0 ∈ Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) :=
    ⟨integrableOn_Ioi_norm_sq_iff hplus fun t ht ↦ by
        simpa [modelCoefficient_of_nonneg ht] using hv t,
      integrableOn_Iio_norm_sq_iff hminus fun t ht ↦ by
        simpa [modelCoefficient_of_nonpos ht] using hv t⟩
  have hmemLp {v : ℝ → E} (hv : ∀ t, HasDerivAt v (-modelCoefficient Aminus Aplus t (v t)) t) :
      MemLp v 2 ↔ IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Iio 0) ∧
        IntegrableOn (fun t ↦ ‖v t‖ ^ 2) (Ioi 0) := by
    have hcont : Continuous v := continuous_iff_continuousAt.2 fun t ↦ (hv t).continuousAt
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable, ← integrableOn_univ,
      ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  ext x
  rw [mem_squareIntegrableSolutions, Submodule.mem_inf]
  constructor
  · rintro ⟨v, rfl, hv, hv2⟩
    obtain ⟨hminus2, hplus2⟩ := (hmemLp hv).1 hv2
    exact ⟨(hsplit hv).1.1 hplus2, (hsplit hv).2.1 hminus2⟩
  · rintro ⟨hxplus, hxminus⟩
    -- The explicit solution `exp (-G(t) A⁺) exp (G(-t) A⁻) x`: one factor is the identity on each
    -- half-line.
    set v : ℝ → E := fun t ↦
      exp ((-transitionIntegral t) • Aplus) (exp (transitionIntegral (-t) • Aminus) x)
    have hv0 : v 0 = x := by simp [v, transitionIntegral_of_nonpos le_rfl]
    have hv (t : ℝ) : HasDerivAt v (-modelCoefficient Aminus Aplus t (v t)) t := by
      have hP := (hasDerivAt_exp_smul_const' Aplus (-transitionIntegral t)).scomp t
        (hasDerivAt_transitionIntegral t).neg
      have hG : HasDerivAt (fun s ↦ transitionIntegral (-s)) (-Real.smoothTransition (-t)) t := by
        simpa [Function.comp_def] using
          (hasDerivAt_transitionIntegral (-t)).scomp t (hasDerivAt_neg t)
      have hQ := (hasDerivAt_exp_smul_const' Aminus (transitionIntegral (-t))).scomp t hG
      refine (hP.clm_apply (hQ.clm_apply (hasDerivAt_const t x))).congr_deriv ?_
      rcases le_or_gt t 0 with ht | ht
      · simp [v, transitionIntegral_of_nonpos ht, Real.smoothTransition.zero_of_nonpos ht,
          modelCoefficient_of_nonpos ht]
      · simp [v, transitionIntegral_of_nonpos (neg_nonpos.mpr ht.le),
          Real.smoothTransition.zero_of_nonpos (neg_nonpos.mpr ht.le),
          modelCoefficient_of_nonneg ht.le]
    exact ⟨v, hv0, hv, (hmemLp hv).2 ⟨(hsplit hv).2.2 (hv0 ▸ hxminus),
      (hsplit hv).1.2 (hv0 ▸ hxplus)⟩⟩

end TauCeti

namespace TauCeti.WeakDerivStep

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {A : ℝ → E →L[ℝ] E}

/-- **The index of the trajectory operator is a difference of Morse indices.** Let `A` be a `C¹`
family of symmetric operators on a finite-dimensional real inner product space with invertible
limits `A±` at `±∞`, and with derivative tending to zero at both ends. Then the index of the
trajectory operator `u ↦ u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is the number of negative
eigenvalues of `A⁻` minus the number of negative eigenvalues of `A⁺`, counted with multiplicity:
the dimensions of the sums of their eigenspaces at negative eigenvalues. -/
theorem index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E} {α : ℝ} (hα : 0 < α)
    (hminus : ∀ v, α * ‖v‖ ≤ ‖Aminus v‖) (hplus : ∀ v, α * ‖v‖ ≤ ‖Aplus v‖)
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)) : ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0)) := by
  have hsymminus : (Aminus : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isClosed_setOf_isSymmetric.mem_of_tendsto hbot (.of_forall hsym)
  have hsymplus : (Aplus : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isClosed_setOf_isSymmetric.mem_of_tendsto htop (.of_forall hsym)
  have hker {B : E →L[ℝ] E} (hB : ∀ v, α * ‖v‖ ≤ ‖B v‖) : LinearMap.ker (B : E →ₗ[ℝ] E) = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun v hv ↦ by
      have h := hB v
      rw [ContinuousLinearMap.coe_coe] at hv
      rw [hv, norm_zero] at h
      exact norm_eq_zero.1 (le_antisymm (by nlinarith [norm_nonneg v]) (norm_nonneg v))
  -- Replace `A` by the model coefficient with the same limits, whose index is computable.
  set M := modelCoefficient Aminus Aplus
  set ML := (memLp_top_modelCoefficient (Aminus := Aminus) (Aplus := Aplus)
    (μ := volume.restrict ((⊤ : Opens ℝ) : Set ℝ))).toLp M
  have hML : ML =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] M := MemLp.coeFn_toLp _
  have hMsym := isSymmetric_modelCoefficient hsymminus hsymplus
  have hMbot : Tendsto M atBot (𝓝 Aminus) := tendsto_modelCoefficient_atBot
  have hMtop : Tendsto M atTop (𝓝 Aplus) := tendsto_modelCoefficient_atTop
  rw [index_trajectoryOperator_eq_of_tendsto hA hsym contDiff_modelCoefficient hMsym hα hminus
      hplus hbot htop hMbot hMtop hdbot hdtop tendsto_deriv_modelCoefficient_atBot
      tendsto_deriv_modelCoefficient_atTop AL ML hAL hML,
    index_trajectoryOperator_eq_finrank_sub_finrank contDiff_modelCoefficient hMsym hα hminus
      hplus hMbot hMtop tendsto_deriv_modelCoefficient_atBot tendsto_deriv_modelCoefficient_atTop
      ML hML,
    neg_modelCoefficient, squareIntegrableSolutions_modelCoefficient hsymminus hsymplus]
  rw [squareIntegrableSolutions_modelCoefficient hsymminus.neg hsymplus.neg,
    ContinuousLinearMap.toLinearMap_neg, ContinuousLinearMap.toLinearMap_neg,
    Module.End.pointSpectralSubspace_neg, Module.End.pointSpectralSubspace_neg, neg_Ioi, neg_Iio,
    neg_zero]
  -- For an invertible symmetric operator the positive and negative spectral subspaces are
  -- orthogonal complements, so the kernel and cokernel are `W ⊓ U` and `Wᗮ ⊓ Uᗮ`.
  set W := Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Ioi 0)
  set U := Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Iio 0)
  have hW : Module.End.pointSpectralSubspace (Aplus : E →ₗ[ℝ] E) (Iio 0) = Wᗮ := by
    rw [hsymplus.orthogonal_pointSpectralSubspace, compl_Ioi, ← Iio_insert,
      Module.End.pointSpectralSubspace_insert_zero (hker hplus)]
  have hU : Module.End.pointSpectralSubspace (Aminus : E →ₗ[ℝ] E) (Ioi 0) = Uᗮ := by
    rw [hsymminus.orthogonal_pointSpectralSubspace, compl_Iio, ← Ioi_insert,
      Module.End.pointSpectralSubspace_insert_zero (hker hminus)]
  rw [hW, hU, Submodule.inf_orthogonal]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W U
  have h2 := (W ⊔ U).finrank_add_finrank_orthogonal
  have h3 := W.finrank_add_finrank_orthogonal
  omega

end TauCeti.WeakDerivStep

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Energy
public import TauCeti.Analysis.Calculus.Morse.SpectralSplitting
public import TauCeti.Analysis.ODE.EnergyEstimate.Index
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The linearized operator along a gradient trajectory

Let `f` be a function on a finite-dimensional real inner product space `E` and let `γ` be a
trajectory of its negative gradient, `γ' = -∇f(γ)`, running from a nondegenerate critical point
`p` at `-∞` to a nondegenerate critical point `q` at `+∞`. Linearizing the equation
`γ' + ∇f(γ) = 0` at `γ` gives the trajectory operator

`D_γ ξ = ξ' + Hess f(γ) ξ : W^{1,2}(ℝ, E) → L²(ℝ, E)`,

the operator `TauCeti.WeakDerivStep.trajectoryOperator` for the coefficient family
`s ↦ hessianOperator f (γ s)`. In Schwarz's functional-analytic construction of Morse homology the
trajectories from `p` to `q` are the zeros of a section whose linearization at `γ` is `D_γ`, so the
Fredholm property and index of `D_γ` give the expected dimension of the space of trajectories.

This file proves that for a `C³` function `D_γ` is Fredholm of index `ind(p) - ind(q)`, the
difference of the Morse indices of the endpoints. The coefficient family is `C¹` with
invertible limits `Hess f(p)` and `Hess f(q)`, and its derivative
`D(Hess f)(γ) (-∇f(γ))` tends to zero because the gradient vanishes at the endpoints. So
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator` applies, and
`TauCeti.WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`
identifies the index with the difference of the numbers of negative eigenvalues of the two
Hessians, which are the Morse indices.

The kernel of `D_γ` contains the velocity of `γ`: differentiating `γ' = -∇f(γ)` shows that
`s ↦ ∇f(γ s)` solves `v' + Hess f(γ) v = 0`, and it is square integrable because the energy of a
trajectory is finite. This reflects the invariance of the trajectory equation under time shifts.
When `p ≠ q` the trajectory is not constant, so the kernel is nonzero. Hence if `D_γ` is
surjective, its index is the positive dimension of its kernel, and `ind(q) < ind(p)`: a trajectory
along which the linearized operator is onto can only lower the Morse index. Surjectivity of `D_γ`
is the analytic form of the transversality of the unstable set of `p` and the stable set of `q`
along `γ`; that equivalence is not proved here.

## Main results

* `ContDiff.memLp_top_hessianOperator_comp`: the Hessian along a connecting trajectory is
  essentially bounded, so it has an `L∞` class to which the trajectory operator applies.
* `IsIntegralCurve.isFredholm_trajectoryOperator_hessianOperator`: the linearized operator is
  Fredholm.
* `IsIntegralCurve.index_trajectoryOperator_hessianOperator`: its index is
  `morseIndex f p - morseIndex f q`.
* `IsIntegralCurve.exists_trajectoryOperator_hessianOperator_eq_zero`: the gradient along `γ`, that
  is, minus its velocity, is the value of an element of the kernel.
* `IsIntegralCurve.finrank_ker_trajectoryOperator_hessianOperator_pos`: for `p ≠ q` the kernel is
  nonzero.
* `IsIntegralCurve.morseIndex_lt_morseIndex_of_surjective`: if the linearized operator is
  surjective and `p ≠ q`, then the Morse index of `q` is less than that of `p`.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics **111**, Birkhäuser, 1993, Chapter 2
  (the linearized trajectory operator, its Fredholm property and its index).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 10 (the linearized operator along a gradient trajectory as a Fredholm operator).
-/

public section

open Filter InnerProductSpace MeasureTheory Set TopologicalSpace
open scoped ENNReal Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ} {γ : ℝ → E} {p q : E}

namespace ContDiff

open TauCeti

/-- **The Hessian along a path with limits is essentially bounded.** For a `C²` function `f` and a
continuous path `γ` with limits at both ends, `s ↦ hessianOperator f (γ s)` is a continuous family
with limits at both ends, hence bounded. In particular the Hessian along a connecting gradient
trajectory has an `L∞` class, to which the trajectory operator applies. -/
theorem memLp_top_hessianOperator_comp (hf : ContDiff ℝ 2 f) (hγ : Continuous γ)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) (μ : Measure ℝ) :
    MemLp (fun s ↦ hessianOperator f (γ s)) ∞ μ := by
  have hH := (hf.contDiff_hessianOperator (m := 0) (by norm_num)).continuous
  have hcont : Continuous fun s ↦ hessianOperator f (γ s) := hH.comp hγ
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1
    (hcont.isBounded_range_iff_isBigO_atTop_atBot.2
      ⟨((hH.tendsto q).comp htop).isBigO_one ℝ, ((hH.tendsto p).comp hbot).isBigO_one ℝ⟩)
  exact memLp_top_of_bound hcont.aestronglyMeasurable C (.of_forall fun s ↦ hC _ ⟨s, rfl⟩)

end ContDiff

namespace IsIntegralCurve

open TauCeti TauCeti.WeakDerivStep

/-- **The gradient along a trajectory lies in the kernel of the linearized operator.** For a `C²`
function and a negative gradient trajectory `γ` with limits at both ends, `s ↦ ∇f(γ s)`, which is
minus the velocity of `γ`, is the value of an element of the kernel of
`ξ ↦ ξ' + Hess f(γ) ξ` on `W^{1,2}(ℝ, E)`. It is square integrable because the energy of `γ` is
finite. -/
theorem exists_trajectoryOperator_hessianOperator_eq_zero
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 2 f)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ hessianOperator f (γ s)) :
    ∃ u : WeakDerivStep volume ⊤ 2
        (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      trajectoryOperator AL u = 0 ∧
        ⇑(prev (ContinuousLinearMap.id ℝ (Lp E 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) u)
          =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ ∇ f (γ s) := by
  have hcont : Continuous fun s ↦ ∇ f (γ s) :=
    (hf.gradient_right (m := 1) (by norm_num)).continuous.comp hγ.continuous
  have hmem : MemLp (fun s ↦ ∇ f (γ s)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
    exact hγ.integrable_norm_gradient_sq
      (fun t ↦ hf.differentiable (by norm_num) (γ t))
      ((hf.continuous.tendsto p).comp hbot) ((hf.continuous.tendsto q).comp htop)
  exact exists_trajectoryOperator_eq_zero_of_hasDerivAt hAL
    (fun s ↦ by simpa only [map_neg] using hf.contDiffAt.hasDerivAt_gradient_comp (hγ s)) hmem

/-- **The linearized operator along a nonconstant trajectory has a nonzero kernel.** For a `C²`
function and a negative gradient trajectory from `p` to `q ≠ p`, the kernel of
`ξ ↦ ξ' + Hess f(γ) ξ` on `W^{1,2}(ℝ, E)` has positive dimension: it contains the velocity
of `γ`, which is not identically zero. -/
theorem finrank_ker_trajectoryOperator_hessianOperator_pos
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 2 f)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) (hpq : p ≠ q)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ hessianOperator f (γ s)) :
    0 < Module.finrank ℝ (trajectoryOperator (p := 2) AL).ker := by
  have hA : Continuous fun s ↦ hessianOperator f (γ s) :=
    (hf.contDiff_hessianOperator (m := 0) (by norm_num)).continuous.comp hγ.continuous
  have := (kerTrajectoryOperatorEquiv hA AL hAL).symm.finiteDimensional
  obtain ⟨u, hu, hux⟩ := exists_trajectoryOperator_hessianOperator_eq_zero hγ hf hbot htop hAL
  obtain ⟨t, ht⟩ := hγ.exists_gradient_ne_zero hbot htop hpq
  refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨u, hu⟩, fun h0 ↦ ht ?_⟩
  have hu0 : u = 0 := congrArg Subtype.val h0
  -- The continuous representative `s ↦ ∇f(γ s)` of `u = 0` vanishes everywhere.
  rw [hu0, prev_zero] at hux
  have hae : (fun s ↦ ∇ f (γ s)) =ᵐ[volume] (0 : ℝ → E) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      hux.symm.trans (Lp.coeFn_zero _ _ _)
  have hzero := (Continuous.ae_eq_iff_eq volume
    ((hf.gradient_right (m := 1) (by norm_num)).continuous.comp hγ.continuous)
    continuous_const).1 hae
  exact congrFun hzero t

/-- The Hessians at two nondegenerate critical points are bounded below by a common constant. -/
private theorem exists_pos_mul_norm_le_hessianOperator (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) :
    ∃ α > 0, (∀ v, α * ‖v‖ ≤ ‖hessianOperator f p v‖) ∧
      ∀ v, α * ‖v‖ ≤ ‖hessianOperator f q v‖ := by
  obtain ⟨e₁, he₁⟩ := hp.isInvertible_hessianOperator
  obtain ⟨e₂, he₂⟩ := hq.isInvertible_hessianOperator
  obtain ⟨c₁, hc₁, h₁⟩ := antilipschitzWith_iff_exists_mul_le_norm.1 ⟨_, e₁.antilipschitzWith⟩
  obtain ⟨c₂, hc₂, h₂⟩ := antilipschitzWith_iff_exists_mul_le_norm.1 ⟨_, e₂.antilipschitzWith⟩
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun v ↦ ?_, fun v ↦ ?_⟩
  · rw [← he₁]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (h₁ v)
  · rw [← he₂]
    exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (h₂ v)

/-- The coefficient family `s ↦ Hess f(γ s)` of the linearized operator satisfies the hypotheses
of `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`: it is a `C¹` family of symmetric
operators with invertible limits `Hess f(p)` and `Hess f(q)` and derivative tending to zero at both
ends. -/
private theorem trajectory_hypotheses (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x))
    (hf : ContDiff ℝ 3 f) (hp : IsNondegenerateCriticalPoint f p)
    (hq : IsNondegenerateCriticalPoint f q) (hbot : Tendsto γ atBot (𝓝 p))
    (htop : Tendsto γ atTop (𝓝 q)) :
    ContDiff ℝ 1 (fun s ↦ hessianOperator f (γ s)) ∧
      (∀ s, (hessianOperator f (γ s)).toLinearMap.IsSymmetric) ∧
      (∃ α > 0, (∀ v, α * ‖v‖ ≤ ‖hessianOperator f p v‖) ∧
        ∀ v, α * ‖v‖ ≤ ‖hessianOperator f q v‖) ∧
      Tendsto (fun s ↦ hessianOperator f (γ s)) atBot (𝓝 (hessianOperator f p)) ∧
      Tendsto (fun s ↦ hessianOperator f (γ s)) atTop (𝓝 (hessianOperator f q)) ∧
      Tendsto (deriv fun s ↦ hessianOperator f (γ s)) atBot (𝓝 0) ∧
      Tendsto (deriv fun s ↦ hessianOperator f (γ s)) atTop (𝓝 0) := by
  have hgrad : ContDiff ℝ 2 (∇ f) := hf.gradient_right (by norm_num)
  have hH : ContDiff ℝ 1 (hessianOperator f) := hf.contDiff_hessianOperator (by norm_num)
  have hγ1 : ContDiff ℝ 1 γ := by
    refine contDiff_one_iff_deriv.2 ⟨fun t ↦ (hγ t).differentiableAt, ?_⟩
    rw [show deriv γ = fun t ↦ -∇ f (γ t) from funext fun t ↦ (hγ t).deriv]
    exact (hgrad.continuous.comp hγ.continuous).neg
  -- The derivative of the coefficient family is `D(Hess f)(γ) (-∇f(γ))`, a continuous function of
  -- `γ` that vanishes at the critical points.
  set G : E → E →L[ℝ] E := fun x ↦ fderiv ℝ (hessianOperator f) x (-∇ f x)
  have hG : Continuous G :=
    (hH.continuous_fderiv one_ne_zero).clm_apply hgrad.continuous.neg
  have hderiv : deriv (fun s ↦ hessianOperator f (γ s)) = G ∘ γ := funext fun s ↦
    (((hH.differentiable one_ne_zero (γ s)).hasFDerivAt).comp_hasDerivAt s (hγ s)).deriv
  have hGp : G p = 0 := by simp [G, hp.gradient_eq_zero]
  have hGq : G q = 0 := by simp [G, hq.gradient_eq_zero]
  refine ⟨hH.comp hγ1, fun s ↦ ?_, exists_pos_mul_norm_le_hessianOperator hp hq,
    (hH.continuous.tendsto p).comp hbot, (hH.continuous.tendsto q).comp htop, ?_, ?_⟩
  · exact ((hf.of_le (by norm_num)).contDiffAt.isSelfAdjoint_hessianOperator).isSymmetric
  · rw [hderiv, ← hGp]
    exact (hG.tendsto p).comp hbot
  · rw [hderiv, ← hGq]
    exact (hG.tendsto q).comp htop

/-- **The linearized operator along a gradient trajectory is Fredholm.** Let `f` be a `C³` function
on a finite-dimensional real inner product space and `γ` a negative gradient trajectory from a
nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at `+∞`. Then the
linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_hessianOperator
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 3 f)
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ hessianOperator f (γ s)) :
    (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨hA, hsym, ⟨α, hα, hminus, hplus⟩, hAbot, hAtop, hdbot, hdtop⟩ :=
    trajectory_hypotheses hγ hf hp hq hbot htop
  exact isFredholm_trajectoryOperator hA hsym hα hminus hplus hAbot hAtop hdbot hdtop AL hAL

/-- **The index of the linearized operator is the difference of the Morse indices.** Let `f` be a
`C³` function on a finite-dimensional real inner product space and `γ` a negative gradient
trajectory from a nondegenerate critical point `p` at `-∞` to a nondegenerate critical point `q` at
`+∞`. Then the Fredholm index of the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is `morseIndex f p - morseIndex f q`. -/
theorem index_trajectoryOperator_hessianOperator
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 3 f)
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q))
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ hessianOperator f (γ s)) :
    (trajectoryOperator (p := 2) AL).index = (morseIndex f p : ℤ) - morseIndex f q := by
  obtain ⟨hA, hsym, ⟨α, hα, hminus, hplus⟩, hAbot, hAtop, hdbot, hdtop⟩ :=
    trajectory_hypotheses hγ hf hp hq hbot htop
  rw [index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank hA hsym hα hminus
      hplus hAbot hAtop hdbot hdtop AL hAL,
    hp.contDiffAt.morseIndex_eq_finrank_pointSpectralSubspace,
    hq.contDiffAt.morseIndex_eq_finrank_pointSpectralSubspace]

/-- **A surjective linearized operator lowers the Morse index.** Let `f` be a `C³` function on a
finite-dimensional real inner product space and `γ` a negative gradient trajectory from a
nondegenerate critical point `p` at `-∞` to a different nondegenerate critical point `q` at `+∞`.
If the linearized operator `ξ ↦ ξ' + Hess f(γ) ξ` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is surjective,
then `morseIndex f q < morseIndex f p`: its index `morseIndex f p - morseIndex f q` is then the
dimension of its kernel, which contains the nonzero velocity of `γ`. -/
theorem morseIndex_lt_morseIndex_of_surjective
    (hγ : IsIntegralCurve γ (fun _ x ↦ -∇ f x)) (hf : ContDiff ℝ 3 f)
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hbot : Tendsto γ atBot (𝓝 p)) (htop : Tendsto γ atTop (𝓝 q)) (hpq : p ≠ q)
    {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ hessianOperator f (γ s))
    (hsurj : Function.Surjective (trajectoryOperator (p := 2) AL)) :
    morseIndex f q < morseIndex f p := by
  have hindex := index_trajectoryOperator_hessianOperator hγ hf hp hq hbot htop hAL
  rw [ContinuousLinearMap.index_of_surjective _ hsurj] at hindex
  have hpos := finrank_ker_trajectoryOperator_hessianOperator_pos hγ (hf.of_le (by norm_num)) hbot
    htop hpq hAL
  omega

end IsIntegralCurve

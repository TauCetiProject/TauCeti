/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
public import Mathlib.Analysis.ODE.Basic
import TauCeti.Analysis.Calculus.MeanValue

/-!
# The trajectory section of a vector field on Sobolev paths

Let `V` be a vector field on a real Banach space `F` and `γ : ℝ → F` a reference path, typically
an integral curve of `V`. A path near `γ` is written `γ + ξ` with `ξ` in the Sobolev space
`W^{1,p}(ℝ, F)`, `1 ≤ p < ∞`, and `γ + ξ` is an integral curve of `V` exactly when

`ξ' - (V (γ + ξ) - V γ) = 0`.

The left side is the **trajectory section** `TauCeti.WeakDerivStep.trajectorySection`, a map from
`W^{1,p}(ℝ, F)` to `Lᵖ(ℝ, F)`. It is the expression, in the chart `ξ ↦ γ + ξ` around `γ`, of the
section `u ↦ u' - V (u)` whose zeros are the trajectories of `V`; for `V = -∇f` these are the
negative gradient trajectories of Schwarz's construction of Morse homology. Here `ξ` is evaluated
through its continuous representative `TauCeti.WeakDerivStep.toZeroAtInfty`, and `V` is assumed
Lipschitz, so that `V (γ + ξ) - V γ` is bounded by `K ‖ξ‖` pointwise and lies in `Lᵖ`.

The two main results are:

* **Zeros are trajectories** (`TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`). If `γ` is an
  integral curve of `V`, then `ξ` is a zero of the section exactly when `γ + ξ` is an integral
  curve of `V`. Both directions rest on the identification of the weak derivative of `ξ` with the
  classical derivative of its continuous representative
  (`TauCeti.WeakDerivStep.hasDerivAt_toZeroAtInfty_iff`).
* **The linearization is the trajectory operator**
  (`TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection`). If `V` is differentiable on a
  set `s` with a uniformly continuous derivative `V'`, and the path `γ + ξ₀` stays a fixed
  distance inside `s`, then the section is strictly differentiable at `ξ₀`, with derivative the
  trajectory operator `ξ ↦ ξ' - V' (γ + ξ₀) ξ` of `TauCeti.WeakDerivStep.trajectoryOperator`.
  Pointwise, the mean value inequality on balls around `γ + ξ₀` bounds the remainder by the
  oscillation of `V'` times `‖ξ₁ - ξ₂‖`; the uniform bound on the continuous representative by the
  Sobolev norm keeps all nearby paths inside these balls, so one modulus of continuity of `V'`
  serves at every time.

Strict differentiability is what the implicit function theorem needs: when the trajectory operator
is moreover Fredholm and surjective, the zeros of the section near `ξ₀` form a manifold whose
dimension is its index (`TauCeti.levelSetChart`). Along a negative gradient trajectory this is
`IsIntegralCurve.exists_openPartialHomeomorph_trajectorySection_neg_gradient`, in
`TauCeti.Analysis.Calculus.Morse.Fredholm`.

## Main declarations

* `TauCeti.WeakDerivStep.trajectorySection`: the section `ξ ↦ ξ' - (V (γ + ξ) - V γ)`.
* `TauCeti.WeakDerivStep.trajectorySection_apply_ae`: its pointwise formula.
* `TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`: its zeros are the paths `ξ` for which
  `γ + ξ` is an integral curve of `V`.
* `TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection`: its strict derivative is the
  trajectory operator.

## References

* M. Schwarz, *Morse Homology*, Progress in Mathematics 111, Birkhäuser, 1993, Chapter 2 (the
  trajectory section on Sobolev paths and its linearization).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix A
  (Fredholm sections and the implicit function theorem).
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology ZeroAtInfty

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {V : F → F} {K : ℝ≥0} {γ : ℝ → F}

/-- For a Lipschitz field `V`, the difference `s ↦ V (γ s + ξ s) - V (γ s)` along a Sobolev path
`ξ`, evaluated through its continuous representative, lies in `Lᵖ`. -/
theorem memLp_comp_add_toZeroAtInfty_sub (hp : p ≠ ∞) (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    MemLp (fun s ↦ V (γ s + toZeroAtInfty (F := F) hp ξ s) - V (γ s)) p
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by
  refine (Lp.memLp (prev _ ξ)).of_le_mul (c := K) ?_ ?_
  · exact ((hV.continuous.comp_aestronglyMeasurable
      (hγ.add (toZeroAtInfty (F := F) hp ξ).continuous.aestronglyMeasurable)).sub
      (hV.continuous.comp_aestronglyMeasurable hγ)).restrict
  · filter_upwards [ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty (F := F) hp ξ)] with s hs
    rw [hs, ← dist_eq_norm]
    exact (hV.dist_le_mul _ _).trans_eq (by rw [dist_self_add_left])

/-- **The trajectory section** `ξ ↦ ξ' - (V (γ + ξ) - V γ)` of a Lipschitz vector field `V` around
a reference path `γ`, from `W^{1,p}(ℝ, F)` to `Lᵖ(ℝ, F)`. The path `ξ` enters through its
continuous representative. When `γ` is an integral curve of `V`, its zeros are the paths `ξ` for
which `γ + ξ` is again an integral curve (`TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`). -/
def trajectorySection (V : F → F) (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _ (weakFDerivL _ ξ) -
    (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ).toLp _

/-- The pointwise formula for the trajectory section: almost everywhere,
`trajectorySection V hV hγ hp ξ s = ξ' s - (V (γ s + ξ s) - V (γ s))`. -/
theorem trajectorySection_apply_ae (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V hV hγ hp ξ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦
      weakFDeriv _ ξ s 1 - (V (γ s + toZeroAtInfty (F := F) hp ξ s) - V (γ s)) := by
  rw [trajectorySection]
  filter_upwards [Lp.coeFn_sub ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _
      (weakFDerivL _ ξ)) ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ).toLp _),
    (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLpL (weakFDerivL _ ξ),
    (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ).coeFn_toLp] with s hs hd hN
  rw [hs, Pi.sub_apply, hd, hN, weakFDerivL_apply, ContinuousLinearMap.apply_apply]

/-- The trajectory section vanishes at the reference path. -/
@[simp]
theorem trajectorySection_zero (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞) : trajectorySection V hV hγ hp 0 = 0 := by
  rw [trajectorySection, map_zero, map_zero, zero_sub, neg_eq_zero]
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [(memLp_comp_add_toZeroAtInfty_sub hp hV hγ 0).coeFn_toLp] with s hs
  rw [hs]
  simp

/-! ### Zeros of the section -/

/-- **Zeros of the trajectory section are trajectories.** Let `γ` be an integral curve of a
Lipschitz vector field `V`. A Sobolev path `ξ` is a zero of the trajectory section exactly when
`γ + ξ`, with `ξ` read through its continuous representative, is again an integral curve of
`V`. -/
theorem trajectorySection_eq_zero_iff (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞) (hγV : IsIntegralCurve γ fun _ ↦ V)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V hV hγ hp ξ = 0 ↔
      IsIntegralCurve (γ + ⇑(toZeroAtInfty (F := F) hp ξ)) fun _ ↦ V := by
  set ξc := toZeroAtInfty (F := F) hp ξ
  have hγc : Continuous γ := hγV.continuous
  have hg : Continuous fun s ↦ V (γ s + ξc s) - V (γ s) :=
    (hV.continuous.comp (hγc.add ξc.continuous)).sub (hV.continuous.comp hγc)
  constructor
  · intro h0
    have hae : (fun s ↦ weakFDeriv _ ξ s 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ V (γ s + ξc s) - V (γ s) := by
      filter_upwards [trajectorySection_apply_ae hV hγ hp ξ, Lp.coeFn_zero F p
        (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))] with s hs hz
      rw [h0, hz, Pi.zero_apply, eq_comm, sub_eq_zero] at hs
      exact hs
    have hξd := (hasDerivAt_toZeroAtInfty_iff hp ξ hg).2
      ((ae_restrict_iff' MeasurableSet.univ).1 hae |>.mono fun x hx ↦ hx (mem_univ x))
    intro t
    convert (hγV t).add (hξd t) using 1
    simp [ξc]
  · intro hc
    have hξd : ∀ t, HasDerivAt ξc (V (γ t + ξc t) - V (γ t)) t := fun t ↦ by
      convert (hc t).sub (hγV t) using 1
      ext r
      simp
    refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [trajectorySection_apply_ae hV hγ hp ξ,
      ae_restrict_of_ae ((hasDerivAt_toZeroAtInfty_iff hp ξ hg).1 hξd)] with s hs hd
    rw [hs, hd, sub_self, Pi.zero_apply]

/-! ### The linearization -/

omit [CompleteSpace F] in
/-- The pointwise remainder of the trajectory section: if the first-order remainder of `V` against
its derivative at the centre is at most `c` times the increment on balls of radius `r` inside `s`
(`UniformContinuousOn.exists_pos_norm_image_sub_le_of_hasFDerivAt`), and the ball of radius `r`
around `γ t + a₀ t` lies in `s`, then for `a₁`, `a₂` uniformly `r`-close to `a₀` the first-order
remainder of `V` at time `t` is at most `c ‖a₁ t - a₂ t‖`. -/
private theorem norm_sub_sub_le_of_norm_sub_lt {s : Set F} {V' : F → F →L[ℝ] F} {c η r : ℝ}
    (hη : ∀ x₀ r, r ≤ η → ball x₀ r ⊆ s → ∀ x₁ ∈ ball x₀ r, ∀ x₂ ∈ ball x₀ r,
      ‖V x₁ - V x₂ - V' x₀ (x₁ - x₂)‖ ≤ c * ‖x₁ - x₂‖) (hr : r ≤ η)
    {a₀ a₁ a₂ : C₀(ℝ, F)} {t : ℝ} (hs : ball (γ t + a₀ t) r ⊆ s) (h₁ : ‖a₁ - a₀‖ < r)
    (h₂ : ‖a₂ - a₀‖ < r) :
    ‖V (γ t + a₁ t) - V (γ t + a₂ t) - V' (γ t + a₀ t) (a₁ t - a₂ t)‖ ≤ c * ‖a₁ t - a₂ t‖ := by
  have hmem : ∀ a : C₀(ℝ, F), ‖a - a₀‖ < r → γ t + a t ∈ ball (γ t + a₀ t) r := fun a ha ↦ by
    rw [mem_ball, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_apply]
    exact (BoundedContinuousFunction.norm_coe_le_norm (a - a₀).toBCF t).trans_lt
      (by rwa [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm])
  have h := hη _ r hr hs _ (hmem a₁ h₁) _ (hmem a₂ h₂)
  rwa [add_sub_add_left_eq_sub] at h

/-- Paths close to `ξ₀` in `W^{1,p}` have continuous representatives uniformly close to that of
`ξ₀`. -/
private theorem norm_toZeroAtInfty_sub_lt (hp : p ≠ ∞)
    {ξ ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {r : ℝ} (h : ‖ξ - ξ₀‖ < r / 2) :
    ‖toZeroAtInfty (F := F) hp ξ - toZeroAtInfty (F := F) hp ξ₀‖ < r := by
  have h2 : √2 < 2 := (Real.sqrt_lt' two_pos).2 (by norm_num)
  rw [← map_sub]
  calc ‖toZeroAtInfty (F := F) hp (ξ - ξ₀)‖ ≤ √2 * ‖ξ - ξ₀‖ :=
        norm_toZeroAtInfty_le_sqrt_two_mul_norm hp _
    _ < r := by nlinarith [norm_nonneg (ξ - ξ₀), Real.sqrt_nonneg 2]

/-- The first-order remainder `S ξ₁ - S ξ₂ - D (ξ₁ - ξ₂)` of the trajectory section `S`, for the
trajectory operator `D` with coefficient `-V' (γ + ξ₀)`, is pointwise minus the first-order
remainder of `V` along the continuous representatives. -/
private theorem trajectorySection_sub_sub_trajectoryOperator_ae (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) {V' : F → F →L[ℝ] F}
    {ξ₀ ξ₁ ξ₂ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) :
    trajectorySection V hV hγ hp ξ₁ - trajectorySection V hV hγ hp ξ₂ -
      trajectoryOperator AL (ξ₁ - ξ₂) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun t ↦
        -(V (γ t + toZeroAtInfty (F := F) hp ξ₁ t) - V (γ t + toZeroAtInfty (F := F) hp ξ₂ t) -
          V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)
            (toZeroAtInfty (F := F) hp ξ₁ t - toZeroAtInfty (F := F) hp ξ₂ t)) := by
  have hw : weakFDeriv _ (ξ₁ - ξ₂) = weakFDeriv _ ξ₁ - weakFDeriv _ ξ₂ := by
    simp only [← weakFDerivL_apply, map_sub]
  have hz : toZeroAtInfty (F := F) hp (ξ₁ - ξ₂) =
      toZeroAtInfty (F := F) hp ξ₁ - toZeroAtInfty (F := F) hp ξ₂ := map_sub _ _ _
  filter_upwards [Lp.coeFn_sub (trajectorySection V hV hγ hp ξ₁ - trajectorySection V hV hγ hp ξ₂)
      (trajectoryOperator AL (ξ₁ - ξ₂)),
    Lp.coeFn_sub (trajectorySection V hV hγ hp ξ₁) (trajectorySection V hV hγ hp ξ₂),
    trajectorySection_apply_ae hV hγ hp ξ₁, trajectorySection_apply_ae hV hγ hp ξ₂,
    trajectoryOperator_apply_ae AL (ξ₁ - ξ₂), Lp.coeFn_sub (weakFDeriv _ ξ₁) (weakFDeriv _ ξ₂),
    ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty (F := F) hp (ξ₁ - ξ₂)), hAL]
    with t h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.sub_apply] at h₀ h₁ h₅
  simp only [h₀, h₁, h₂, h₃, h₄, hw, h₅, h₆, h₇, hz, sub_apply, neg_apply]
  abel

/-- A pointwise bound by `c` on the first-order remainder of `V` along the continuous
representatives bounds the first-order remainder of the trajectory section by `c ‖ξ₁ - ξ₂‖`. -/
private theorem norm_trajectorySection_sub_sub_le (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) {V' : F → F →L[ℝ] F}
    {ξ₀ ξ₁ ξ₂ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t, ‖V (γ t + toZeroAtInfty (F := F) hp ξ₁ t) -
      V (γ t + toZeroAtInfty (F := F) hp ξ₂ t) - V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)
        (toZeroAtInfty (F := F) hp ξ₁ t - toZeroAtInfty (F := F) hp ξ₂ t)‖ ≤
          c * ‖toZeroAtInfty (F := F) hp ξ₁ t - toZeroAtInfty (F := F) hp ξ₂ t‖) :
    ‖trajectorySection V hV hγ hp ξ₁ - trajectorySection V hV hγ hp ξ₂ -
      trajectoryOperator AL (ξ₁ - ξ₂)‖ ≤ c * ‖ξ₁ - ξ₂‖ := by
  have hz : toZeroAtInfty (F := F) hp (ξ₁ - ξ₂) =
      toZeroAtInfty (F := F) hp ξ₁ - toZeroAtInfty (F := F) hp ξ₂ := map_sub _ _ _
  rw [← norm_neg]
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev _ (ξ₁ - ξ₂)) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ _) hc)
  filter_upwards [Lp.coeFn_neg (trajectorySection V hV hγ hp ξ₁ -
      trajectorySection V hV hγ hp ξ₂ - trajectoryOperator AL (ξ₁ - ξ₂)),
    trajectorySection_sub_sub_trajectoryOperator_ae hV hγ hp (ξ₁ := ξ₁) (ξ₂ := ξ₂) hAL,
    ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty (F := F) hp (ξ₁ - ξ₂))] with t hn hs hp'
  simp only [hn, Pi.neg_apply, hs, neg_neg, hp', hz, sub_apply]
  exact h t

/-- **The linearization of the trajectory section is the trajectory operator.** Let `V` be a
Lipschitz vector field which on a set `s` has derivative `V'`, uniformly continuous on `s`, and let
`ξ₀` be a Sobolev path such that `γ + ξ₀` stays at distance at least `δ > 0` from the complement of
`s`. Then the trajectory section is strictly differentiable at `ξ₀`, and its derivative is the
trajectory operator `ξ ↦ ξ' + A ξ` for the coefficient `A = -V' (γ + ξ₀)`. -/
theorem hasStrictFDerivAt_trajectorySection (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) {s : Set F} {V' : F → F →L[ℝ] F}
    (hV' : ∀ x ∈ s, HasFDerivAt V (V' x) x) (hV's : UniformContinuousOn V' s)
    {ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {δ : ℝ} (hδ : 0 < δ) (hs : ∀ t, ball (γ t + toZeroAtInfty (F := F) hp ξ₀ t) δ ⊆ s)
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) :
    HasStrictFDerivAt (trajectorySection V hV hγ hp) (trajectoryOperator AL) ξ₀ := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- A modulus for `V'` at the scale `c`, and a radius `r` within which it applies.
  obtain ⟨η, hη, hηc⟩ := hV's.exists_pos_norm_image_sub_le_of_hasFDerivAt hV' hc
  obtain ⟨r, hr0, hrη, hrδ⟩ : ∃ r, 0 < r ∧ r ≤ η ∧ r ≤ δ :=
    ⟨min η δ, lt_min hη hδ, min_le_left _ _, min_le_right _ _⟩
  -- Paths `r / 2`-close to `ξ₀` in `W^{1,p}` stay uniformly `r`-close to `ξ₀`, where the mean
  -- value inequality on balls around `γ + ξ₀` bounds the remainder pointwise.
  refine Metric.eventually_nhds_iff.2 ⟨r / 2, by positivity, ?_⟩
  rintro ⟨ξ₁, ξ₂⟩ hξ
  rw [dist_eq_norm] at hξ
  exact norm_trajectorySection_sub_sub_le hV hγ hp hAL hc.le fun t ↦
    norm_sub_sub_le_of_norm_sub_lt hηc hrη ((ball_subset_ball hrδ).trans (hs t))
      (norm_toZeroAtInfty_sub_lt hp ((norm_fst_le _).trans_lt hξ))
      (norm_toZeroAtInfty_sub_lt hp ((norm_snd_le _).trans_lt hξ))

end TauCeti.WeakDerivStep

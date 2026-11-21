/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.ZeroAtInfty
public import Mathlib.Analysis.ODE.Basic
public import TauCeti.Analysis.Calculus.ContDiff.UniformOn
import TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# The trajectory section of a vector field on Sobolev paths

Let `V` be a vector field on a real Banach space `F` and `γ : ℝ → F` a reference path. A path near
`γ` is written `γ + ξ` with `ξ` in the Sobolev space `W^{1,p}(ℝ, F)`, `1 ≤ p < ∞`. The
**trajectory section** `TauCeti.WeakDerivStep.trajectorySection` is the map

`ξ ↦ ξ' - (V (γ + ξ) - V γ)`

from `W^{1,p}(ℝ, F)` to `Lᵖ(ℝ, F)`. It differs from the expression `(γ + ξ)' - V (γ + ξ)`, in the
chart `ξ ↦ γ + ξ`, of the section `u ↦ u' - V (u)` by the residual `γ' - V γ` of the reference
path, which does not depend on `ξ`. So `γ + ξ` is an integral curve of `V` exactly when the
section takes the value `V γ - γ'` at `ξ`. When `γ` is itself an integral curve of `V`, the
residual vanishes, and the zeros of the section are the trajectories `γ + ξ` of `V`; for
`V = -∇f` these are the negative gradient trajectories of Schwarz's construction of Morse
homology. Here `ξ` is evaluated through its continuous representative
`TauCeti.WeakDerivStep.toZeroAtInfty`, and `V` is assumed Lipschitz, so that `V (γ + ξ) - V γ` is
bounded by `K ‖ξ‖` pointwise and lies in `Lᵖ`. The section is then Lipschitz with constant
`1 + K` (`TauCeti.WeakDerivStep.lipschitzWith_trajectorySection`).

The three main results are:

* **Level sets are trajectories**
  (`TauCeti.WeakDerivStep.trajectorySection_eq_iff_isIntegralCurve`). If `γ` is `C¹` with
  derivative `γ'`, then the section takes the value `V γ - γ'` at `ξ` exactly when `γ + ξ` is an
  integral curve of `V`. In particular, if `γ` is an integral curve of `V`, then `ξ` is a zero of
  the section exactly when `γ + ξ` is an integral curve of `V`
  (`TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`). Both directions rest on the
  identification of the weak derivative of `ξ` with the classical derivative of its continuous
  representative (`TauCeti.WeakDerivStep.forall_hasDerivAt_toZeroAtInfty_iff`).
* **The linearization is the trajectory operator**
  (`TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection`). If `V` is differentiable on a
  set `s` with a uniformly continuous derivative `V'`, and the path `γ + ξ₀` stays a fixed
  distance inside `s`, then the section is strictly differentiable at `ξ₀`, with derivative the
  trajectory operator `ξ ↦ ξ' - V' (γ + ξ₀) ξ` of `TauCeti.WeakDerivStep.trajectoryOperator`.
  Pointwise, the mean value inequality on balls around `γ + ξ₀` bounds the remainder by the
  oscillation of `V'` times `‖ξ₁ - ξ₂‖`; the uniform bound on the continuous representative by the
  Sobolev norm keeps all nearby paths inside these balls, so one modulus of continuity of `V'`
  serves at every time. If `γ` has bounded range, it suffices that `V'` be uniformly continuous on
  balls around `0`
  (`TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection_of_isBounded_range`), for instance
  continuous on a proper space
  (`TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection_of_isBounded_range_of_continuous`).
* **Higher regularity** (`TauCeti.WeakDerivStep.contDiffAt_trajectorySection`). If `γ` is
  continuous with bounded range and `V` is uniformly `C^{n+1}` (`TauCeti.UniformContDiffOn`) on a
  set that `γ + ξ₀` stays a fixed distance inside, then the section is `C^{n+1}` at `ξ₀`. Its
  derivative at nearby `ξ` is the trajectory operator with coefficient `-V' (γ + ξ)`, and this
  coefficient depends `Cⁿ` on `ξ`: the Sobolev embedding `W^{1,p} → C₀` makes `ξ ↦ γ + ξ` an
  affine map into bounded continuous paths, on which the superposition operator `f ↦ -V' ∘ f` is
  `Cⁿ` (`BoundedContinuousFunction.contDiffAt_of_forall_apply_eq`). On a proper space a `Cⁿ`
  field, `n ≤ ∞`, therefore gives a `Cⁿ` section
  (`TauCeti.WeakDerivStep.contDiff_trajectorySection_of_contDiff`). The Sard--Smale theorem asks
  for this finite-order regularity of a Fredholm map, above its index.

Strict differentiability is what the implicit function theorem needs: when the trajectory operator
is moreover Fredholm and surjective, a neighbourhood of `ξ₀` in the level set of the section
through `ξ₀` (its zero set, when the section vanishes at `ξ₀`) is homeomorphic to an open subset
of `ℝ^n`, `n` the index, by a chart (`TauCeti.levelSetChartModel`). Along a negative gradient
trajectory this is
`IsIntegralCurve.exists_openPartialHomeomorph_setOf_trajectorySection_neg_gradient_eq_zero`, in
`TauCeti.Analysis.Calculus.Morse.Fredholm`.

## Main declarations

* `TauCeti.WeakDerivStep.trajectorySection`: the section `ξ ↦ ξ' - (V (γ + ξ) - V γ)`.
* `TauCeti.WeakDerivStep.trajectorySection_apply_ae`: its pointwise formula.
* `TauCeti.WeakDerivStep.trajectorySection_congr`: it does not depend on the Lipschitz constant
  used to construct it.
* `TauCeti.WeakDerivStep.lipschitzWith_trajectorySection`: it is `(1 + K)`-Lipschitz.
* `TauCeti.WeakDerivStep.trajectorySection_eq_iff_isIntegralCurve`: its level set at `V γ - γ'`
  consists of the paths `ξ` for which `γ + ξ` is an integral curve of `V`.
* `TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`: when `γ` is an integral curve of `V`, its
  zeros are the paths `ξ` for which `γ + ξ` is again an integral curve of `V`.
* `TauCeti.WeakDerivStep.norm_trajectorySection_sub_sub_le`: a pointwise bound on the first-order
  remainder of `V` bounds the first-order remainder of the section.
* `TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection`: its strict derivative is the
  trajectory operator.
* `TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection_of_isBounded_range`: the same along
  a reference path with bounded range.
* `TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection_of_isBounded_range_of_continuous`:
  the same for a continuous derivative on a proper space.
* `TauCeti.WeakDerivStep.contDiffAt_trajectorySection`: it is `C^{n+1}` at `ξ₀` when `V` is
  uniformly `C^{n+1}` near `γ + ξ₀`.
* `TauCeti.WeakDerivStep.contDiff_trajectorySection`: it is `C^{n+1}` when `V` is uniformly
  `C^{n+1}` on all of `F`.
* `TauCeti.WeakDerivStep.contDiff_trajectorySection_of_contDiff`: on a proper space, it is `Cⁿ`
  when `V` is.

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
open scoped BoundedContinuousFunction ENNReal NNReal Topology ZeroAtInfty

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
which `γ + ξ` is again an integral curve (`TauCeti.WeakDerivStep.trajectorySection_eq_zero_iff`);
for a general `C¹` reference path the trajectories `γ + ξ` form the level set at `V γ - γ'`
(`TauCeti.WeakDerivStep.trajectorySection_eq_iff_isIntegralCurve`). -/
def trajectorySection (V : F → F) (γ : ℝ → F) (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) :=
  (ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _ (weakFDerivL _ ξ) -
    (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ).toLp _

/-- The trajectory section is the weak derivative, evaluated on the unit vector, minus the class
of `s ↦ V (γ s + ξ s) - V (γ s)` in `Lᵖ`. -/
theorem trajectorySection_def (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V γ hV hγ hp ξ =
      (ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _ (weakFDerivL _ ξ) -
        (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ).toLp _ :=
  (rfl)

/-- The trajectory section does not depend on the Lipschitz constant of `V` used to construct it:
sections built from two Lipschitz witnesses for the same field agree. -/
theorem trajectorySection_congr {K₁ K₂ : ℝ≥0} (hV₁ : LipschitzWith K₁ V)
    (hV₂ : LipschitzWith K₂ V) (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) :
    trajectorySection V γ hV₁ hγ hp = trajectorySection V γ hV₂ hγ hp :=
  (rfl)

/-- The pointwise formula for the trajectory section: almost everywhere,
`trajectorySection V γ hV hγ hp ξ s = ξ' s - (V (γ s + ξ s) - V (γ s))`. -/
theorem trajectorySection_apply_ae (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V γ hV hγ hp ξ =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦
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
    (hp : p ≠ ∞) : trajectorySection V γ hV hγ hp 0 = 0 := by
  rw [trajectorySection, map_zero, map_zero, zero_sub, neg_eq_zero]
  refine Lp.eq_zero_iff_ae_eq_zero.2 ?_
  filter_upwards [(memLp_comp_add_toZeroAtInfty_sub hp hV hγ 0).coeFn_toLp] with s hs
  rw [hs]
  simp

/-- The trajectory section is Lipschitz with constant `1 + K`: the derivative part is
`1`-Lipschitz for the graph norm and the field part is `K`-Lipschitz. -/
theorem lipschitzWith_trajectorySection (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) :
    LipschitzWith (1 + K) (trajectorySection V γ hV hγ hp) := by
  refine LipschitzWith.of_dist_le_mul fun ξ₁ ξ₂ ↦ ?_
  -- The difference splits into the derivative part along `ξ₁ - ξ₂` and the field part.
  have hS : trajectorySection V γ hV hγ hp ξ₁ - trajectorySection V γ hV hγ hp ξ₂ =
      (ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _ (weakFDerivL _ (ξ₁ - ξ₂)) -
        ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).toLp _ -
          (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).toLp _) := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_sub (trajectorySection V γ hV hγ hp ξ₁)
        (trajectorySection V γ hV hγ hp ξ₂),
      Lp.coeFn_sub ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p _
        (weakFDerivL _ (ξ₁ - ξ₂))) ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).toLp _ -
          (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).toLp _),
      Lp.coeFn_sub ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).toLp _)
        ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).toLp _),
      (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLpL (weakFDerivL _ (ξ₁ - ξ₂)),
      Lp.coeFn_sub (weakFDeriv _ ξ₁) (weakFDeriv _ ξ₂),
      trajectorySection_apply_ae hV hγ hp ξ₁, trajectorySection_apply_ae hV hγ hp ξ₂,
      (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).coeFn_toLp,
      (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).coeFn_toLp]
      with t h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    have hw : weakFDeriv _ (ξ₁ - ξ₂) = weakFDeriv _ ξ₁ - weakFDeriv _ ξ₂ := by
      simp only [← weakFDerivL_apply, map_sub]
    simp only [Pi.sub_apply] at h₁ h₂ h₃ h₅
    simp only [h₁, h₂, h₃, h₄, h₆, h₇, h₈, h₉]
    simp only [weakFDerivL_apply, hw, h₅, ContinuousLinearMap.apply_apply, sub_apply]
    abel
  rw [NNReal.coe_add, NNReal.coe_one, add_mul, dist_eq_norm, dist_eq_norm, hS]
  refine norm_sub_le_of_le ?_ ?_
  · refine (Lp.norm_le_mul_norm_of_ae_le_mul (c := 1) (g := weakFDeriv _ (ξ₁ - ξ₂)) ?_).trans
      (mul_le_mul_of_nonneg_left (norm_weakFDeriv_le _ _) zero_le_one)
    filter_upwards [(ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLpL
      (weakFDerivL _ (ξ₁ - ξ₂))] with s hs
    rw [hs, weakFDerivL_apply, ContinuousLinearMap.apply_apply, one_mul]
    simpa using (weakFDeriv _ (ξ₁ - ξ₂) s).le_opNorm 1
  · refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev _ (ξ₁ - ξ₂)) ?_).trans
      (mul_le_mul_of_nonneg_left (norm_prev_le _ _) K.coe_nonneg)
    filter_upwards [Lp.coeFn_sub ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).toLp _)
        ((memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).toLp _),
      (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₁).coeFn_toLp,
      (memLp_comp_add_toZeroAtInfty_sub hp hV hγ ξ₂).coeFn_toLp,
      ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty (F := F) hp (ξ₁ - ξ₂))] with s hs h₁ h₂ hd
    have hz : toZeroAtInfty (F := F) hp (ξ₁ - ξ₂) =
        toZeroAtInfty (F := F) hp ξ₁ - toZeroAtInfty (F := F) hp ξ₂ := map_sub _ _ _
    simp only [hs, Pi.sub_apply, h₁, h₂, hd, hz, sub_sub_sub_cancel_right, sub_apply]
    exact (hV.norm_sub_le _ _).trans_eq (by rw [add_sub_add_left_eq_sub])

/-- The trajectory section is continuous. -/
@[fun_prop]
theorem continuous_trajectorySection (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) :
    Continuous (trajectorySection V γ hV hγ hp) :=
  (lipschitzWith_trajectorySection hV hγ hp).continuous

/-! ### Level sets of the section -/

/-- **Level sets of the trajectory section are trajectories.** Let `V` be a Lipschitz vector field
and `γ` a reference path with continuous derivative `γ'`, and let `c` be the class of the
residual `V γ - γ'` in `Lᵖ`. A Sobolev path `ξ` is mapped to `c` by the trajectory section exactly
when `γ + ξ`, with `ξ` read through its continuous representative, is an integral curve of `V`. -/
theorem trajectorySection_eq_iff_isIntegralCurve (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) {γ' : ℝ → F}
    (hγ' : ∀ t, HasDerivAt γ (γ' t) t) (hγ'c : Continuous γ')
    {c : Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hc : c =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ V (γ s) - γ' s)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V γ hV hγ hp ξ = c ↔
      IsIntegralCurve (γ + ⇑(toZeroAtInfty (F := F) hp ξ)) fun _ ↦ V := by
  set ξc := toZeroAtInfty (F := F) hp ξ
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t ↦ (hγ' t).continuousAt
  have hg : Continuous fun s ↦ V (γ s + ξc s) - γ' s :=
    (hV.continuous.comp (hγc.add ξc.continuous)).sub hγ'c
  -- The section takes the value `c` exactly when the weak derivative of `ξ` is
  -- `V (γ + ξ) - γ'` almost everywhere, that is, when `ξ` has this classical derivative.
  have hiff : trajectorySection V γ hV hγ hp ξ = c ↔
      ∀ t, HasDerivAt ξc (V (γ t + ξc t) - γ' t) t := by
    rw [forall_hasDerivAt_toZeroAtInfty_iff hp ξ hg]
    constructor
    · intro h
      have hae : (fun s ↦ weakFDeriv _ ξ s 1) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          fun s ↦ V (γ s + ξc s) - γ' s := by
        filter_upwards [trajectorySection_apply_ae hV hγ hp ξ, hc] with s hs hcs
        rw [h, hcs, eq_comm, sub_eq_iff_eq_add] at hs
        rw [hs]
        abel
      exact (ae_restrict_iff' MeasurableSet.univ).1 hae |>.mono fun x hx ↦ hx (mem_univ x)
    · intro h
      refine Lp.ext ?_
      filter_upwards [trajectorySection_apply_ae hV hγ hp ξ, hc, ae_restrict_of_ae h]
        with s hs hcs hd
      rw [hs, hcs, hd]
      abel
  rw [hiff]
  constructor
  · intro h t
    convert (hγ' t).add (h t) using 1
    simp [ξc]
  · intro h t
    convert (h t).sub (hγ' t) using 1
    ext r
    simp

/-- **Zeros of the trajectory section are trajectories.** Let `γ` be an integral curve of a
Lipschitz vector field `V`. A Sobolev path `ξ` is a zero of the trajectory section exactly when
`γ + ξ`, with `ξ` read through its continuous representative, is again an integral curve of
`V`. -/
theorem trajectorySection_eq_zero_iff (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hp : p ≠ ∞) (hγV : IsIntegralCurve γ fun _ ↦ V)
    (ξ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    trajectorySection V γ hV hγ hp ξ = 0 ↔
      IsIntegralCurve (γ + ⇑(toZeroAtInfty (F := F) hp ξ)) fun _ ↦ V :=
  trajectorySection_eq_iff_isIntegralCurve hV hγ hp (γ' := fun t ↦ V (γ t)) hγV
    (hV.continuous.comp hγV.continuous)
    (by filter_upwards [Lp.coeFn_zero F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))] with s hs
        rw [hs, Pi.zero_apply, sub_self]) ξ

/-! ### The linearization -/

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- If `a` is uniformly `r`-close to `a₀`, then `γ t + a t` is `r`-close to `γ t + a₀ t`. -/
private theorem add_apply_mem_ball_add_apply {a a₀ : C₀(ℝ, F)} {r : ℝ} (h : ‖a - a₀‖ < r)
    (t : ℝ) : γ t + a t ∈ ball (γ t + a₀ t) r := by
  rw [mem_ball, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_apply]
  exact ((a - a₀).norm_coe_le_norm t).trans_lt h

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- If `γ` is bounded by `C`, then `γ + a` is bounded by `C + ‖a‖`. -/
private theorem norm_add_apply_le {C : ℝ} (hC : ∀ x ∈ range γ, ‖x‖ ≤ C) (a : C₀(ℝ, F)) (t : ℝ) :
    ‖γ t + a t‖ ≤ C + ‖a‖ :=
  (norm_add_le _ _).trans (add_le_add (hC _ (mem_range_self t)) (a.norm_coe_le_norm t))

omit [CompleteSpace F] in
/-- The pointwise remainder of the trajectory section: if the first-order remainder of `V` against
its derivative at the centre is at most `c` times the increment on balls of radius `r` inside `s`
(`UniformContinuousOn.exists_pos_norm_image_sub_sub_le_of_hasFDerivAt`), and the ball of radius `r`
around `γ t + a₀ t` lies in `s`, then for `a₁`, `a₂` uniformly `r`-close to `a₀` the first-order
remainder of `V` at time `t` is at most `c ‖a₁ t - a₂ t‖`. -/
private theorem norm_sub_sub_le_of_norm_sub_lt {s : Set F} {V' : F → F →L[ℝ] F} {c η r : ℝ}
    (hη : ∀ x₀ r, r ≤ η → ball x₀ r ⊆ s → ∀ x₁ ∈ ball x₀ r, ∀ x₂ ∈ ball x₀ r,
      ‖V x₁ - V x₂ - V' x₀ (x₁ - x₂)‖ ≤ c * ‖x₁ - x₂‖) (hr : r ≤ η)
    {a₀ a₁ a₂ : C₀(ℝ, F)} {t : ℝ} (hs : ball (γ t + a₀ t) r ⊆ s) (h₁ : ‖a₁ - a₀‖ < r)
    (h₂ : ‖a₂ - a₀‖ < r) :
    ‖V (γ t + a₁ t) - V (γ t + a₂ t) - V' (γ t + a₀ t) (a₁ t - a₂ t)‖ ≤ c * ‖a₁ t - a₂ t‖ := by
  have h := hη _ r hr hs _ (add_apply_mem_ball_add_apply h₁ t) _
    (add_apply_mem_ball_add_apply h₂ t)
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
theorem trajectorySection_sub_sub_trajectoryOperator_ae (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hp : p ≠ ∞) {V' : F → F →L[ℝ] F}
    {ξ₀ ξ₁ ξ₂ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) :
    trajectorySection V γ hV hγ hp ξ₁ - trajectorySection V γ hV hγ hp ξ₂ -
      trajectoryOperator AL (ξ₁ - ξ₂) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun t ↦
        -(V (γ t + toZeroAtInfty (F := F) hp ξ₁ t) - V (γ t + toZeroAtInfty (F := F) hp ξ₂ t) -
          V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)
            (toZeroAtInfty (F := F) hp ξ₁ t - toZeroAtInfty (F := F) hp ξ₂ t)) := by
  have hw : weakFDeriv _ (ξ₁ - ξ₂) = weakFDeriv _ ξ₁ - weakFDeriv _ ξ₂ := by
    simp only [← weakFDerivL_apply, map_sub]
  have hz : toZeroAtInfty (F := F) hp (ξ₁ - ξ₂) =
      toZeroAtInfty (F := F) hp ξ₁ - toZeroAtInfty (F := F) hp ξ₂ := map_sub _ _ _
  filter_upwards [Lp.coeFn_sub
      (trajectorySection V γ hV hγ hp ξ₁ - trajectorySection V γ hV hγ hp ξ₂)
      (trajectoryOperator AL (ξ₁ - ξ₂)),
    Lp.coeFn_sub (trajectorySection V γ hV hγ hp ξ₁) (trajectorySection V γ hV hγ hp ξ₂),
    trajectorySection_apply_ae hV hγ hp ξ₁, trajectorySection_apply_ae hV hγ hp ξ₂,
    trajectoryOperator_apply_ae AL (ξ₁ - ξ₂), Lp.coeFn_sub (weakFDeriv _ ξ₁) (weakFDeriv _ ξ₂),
    ae_restrict_of_ae (prev_ae_eq_toZeroAtInfty (F := F) hp (ξ₁ - ξ₂)), hAL]
    with t h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Pi.sub_apply] at h₀ h₁ h₅
  simp only [h₀, h₁, h₂, h₃, h₄, hw, h₅, h₆, h₇, hz, sub_apply, neg_apply]
  abel

/-- A pointwise bound by `c` on the first-order remainder of `V` along the continuous
representatives bounds the first-order remainder of the trajectory section by `c ‖ξ₁ - ξ₂‖`. -/
theorem norm_trajectorySection_sub_sub_le (hV : LipschitzWith K V)
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
    ‖trajectorySection V γ hV hγ hp ξ₁ - trajectorySection V γ hV hγ hp ξ₂ -
      trajectoryOperator AL (ξ₁ - ξ₂)‖ ≤ c * ‖ξ₁ - ξ₂‖ := by
  have hz : toZeroAtInfty (F := F) hp (ξ₁ - ξ₂) =
      toZeroAtInfty (F := F) hp ξ₁ - toZeroAtInfty (F := F) hp ξ₂ := map_sub _ _ _
  rw [← norm_neg]
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev _ (ξ₁ - ξ₂)) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ _) hc)
  filter_upwards [Lp.coeFn_neg (trajectorySection V γ hV hγ hp ξ₁ -
      trajectorySection V γ hV hγ hp ξ₂ - trajectoryOperator AL (ξ₁ - ξ₂)),
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
    HasStrictFDerivAt (trajectorySection V γ hV hγ hp) (trajectoryOperator AL) ξ₀ := by
  rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  -- A modulus for `V'` at the scale `c`, and a radius `r` within which it applies.
  obtain ⟨η, hη, hηc⟩ := hV's.exists_pos_norm_image_sub_sub_le_of_hasFDerivAt hV' hc
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

/-- **The linearization along a bounded reference path.** Let `V` be a Lipschitz vector field with
derivative `V'` everywhere, uniformly continuous on every ball around `0`, and let `γ` have
bounded range. Then at every Sobolev path `ξ₀` the trajectory section is strictly
differentiable, and its derivative is the trajectory operator `ξ ↦ ξ' + A ξ` for the coefficient
`A = -V' (γ + ξ₀)`. -/
theorem hasStrictFDerivAt_trajectorySection_of_isBounded_range (hV : LipschitzWith K V)
    (hγ : AEStronglyMeasurable γ volume) (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞)
    {V' : F → F →L[ℝ] F} (hV' : ∀ x, HasFDerivAt V (V' x) x)
    (hV's : ∀ r, UniformContinuousOn V' (ball 0 r))
    {ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) :
    HasStrictFDerivAt (trajectorySection V γ hV hγ hp) (trajectoryOperator AL) ξ₀ := by
  -- The path `γ + ξ₀` stays in a ball around `0`, whose unit thickening serves as `s`.
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  set ξc := toZeroAtInfty (F := F) hp ξ₀
  refine hasStrictFDerivAt_trajectorySection hV hγ hp (s := ball 0 (C + ‖ξc‖ + 1))
    (fun x _ ↦ hV' x) (hV's _) one_pos (fun t ↦ ball_subset_ball' ?_) hAL
  rw [dist_zero_right]
  linarith [norm_add_apply_le hC ξc t]

/-- **The linearization along a bounded reference path, continuous case.** On a proper
space, a continuous derivative `V'` is uniformly continuous on balls, so
`TauCeti.WeakDerivStep.hasStrictFDerivAt_trajectorySection_of_isBounded_range` applies. -/
theorem hasStrictFDerivAt_trajectorySection_of_isBounded_range_of_continuous [ProperSpace F]
    (hV : LipschitzWith K V) (hγ : AEStronglyMeasurable γ volume)
    (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞) {V' : F → F →L[ℝ] F}
    (hV' : ∀ x, HasFDerivAt V (V' x) x) (hV'c : Continuous V')
    {ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun t ↦ -V' (γ t + toZeroAtInfty (F := F) hp ξ₀ t)) :
    HasStrictFDerivAt (trajectorySection V γ hV hγ hp) (trajectoryOperator AL) ξ₀ :=
  hasStrictFDerivAt_trajectorySection_of_isBounded_range hV hγ hb hp hV'
    (fun r ↦ ((isCompact_closedBall 0 r).uniformContinuousOn_of_continuous
      hV'c.continuousOn).mono ball_subset_closedBall) hAL

/-! ### Higher regularity -/

/-- For a continuous reference path `γ` with bounded range, `ξ ↦ γ + ξ` is a smooth map from
`W^{1,p}(ℝ, F)` into bounded continuous paths: the sum of a constant and the Sobolev embedding. -/
private theorem exists_contDiff_add_toZeroAtInfty (hγ : Continuous γ)
    (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞) :
    ∃ ι : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))) → ℝ →ᵇ F,
      ContDiff ℝ ω ι ∧ ∀ ξ t, ι ξ t = γ t + toZeroAtInfty (F := F) hp ξ t := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  exact ⟨fun ξ ↦ BoundedContinuousFunction.ofNormedAddCommGroup γ hγ C
      (fun t ↦ hC _ (mem_range_self t)) + ZeroAtInftyContinuousMap.toBCFₗᵢ ℝ (toZeroAtInfty hp ξ),
    contDiff_const.add ((ZeroAtInftyContinuousMap.toBCFₗᵢ ℝ).toContinuousLinearMap.comp
      (toZeroAtInfty (F := F) hp)).contDiff, fun ξ t ↦ by simp⟩

/-- Around a path `δ / 4`-close to `ξ₀` in `W^{1,p}`, balls of radius `δ / 2` lie in the balls of
radius `δ` around `γ + ξ₀`. -/
private theorem ball_add_toZeroAtInfty_subset (hp : p ≠ ∞)
    {ξ ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {δ : ℝ} (hξ : ξ ∈ ball ξ₀ (δ / 4)) (t : ℝ) :
    ball (γ t + toZeroAtInfty (F := F) hp ξ t) (δ / 2) ⊆
      ball (γ t + toZeroAtInfty (F := F) hp ξ₀ t) δ := by
  have hz := norm_toZeroAtInfty_sub_lt hp (r := δ / 2) (ξ := ξ) (ξ₀ := ξ₀)
    (by rw [← dist_eq_norm]; linarith [mem_ball.1 hξ])
  refine ball_subset_ball' ?_
  linarith [mem_ball.1 (add_apply_mem_ball_add_apply (γ := γ) hz t)]

/-- **The trajectory section is `C^{n+1}`.** Let `V` be a Lipschitz vector field which is uniformly
`C^{n+1}` on a set `s` (`TauCeti.UniformContDiffOn`), let `γ` be a continuous reference path with
bounded range, and let `ξ₀` be a Sobolev path such that `γ + ξ₀` stays at distance at least
`δ > 0` from the complement of `s`. Then the trajectory section is `C^{n+1}` at `ξ₀`.

Near `ξ₀` the derivative at `ξ` is the trajectory operator with coefficient `-V' (γ + ξ)`. -/
theorem contDiffAt_trajectorySection (hV : LipschitzWith K V) (hγ : Continuous γ)
    (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞) {s : Set F} {n : ℕ}
    (hVs : UniformContDiffOn ℝ (n + 1) V s)
    {ξ₀ : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp F p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}
    {δ : ℝ} (hδ : 0 < δ) (hs : ∀ t, ball (γ t + toZeroAtInfty (F := F) hp ξ₀ t) δ ⊆ s) :
    ContDiffAt ℝ (n + 1) (trajectorySection V γ hV hγ.aestronglyMeasurable hp) ξ₀ := by
  obtain ⟨-, V', hV', -, hV'n⟩ := uniformContDiffOn_succ_iff.1 hVs
  -- The coefficient `t ↦ -V' (f t)` along bounded continuous paths `f` with values in `s`.
  have hΘ : ∀ f : ℝ →ᵇ F, ∃ Φ : ℝ →ᵇ (F →L[ℝ] F), (∀ t, f t ∈ s) → ∀ t, Φ t = -V' (f t) := by
    intro f
    by_cases hf : ∀ t, f t ∈ s
    · obtain ⟨Φ, hΦ⟩ := BoundedContinuousFunction.exists_eq_comp hV hV' hV'n.continuousOn hf
      exact ⟨-Φ, fun _ t ↦ by rw [neg_apply, hΦ]⟩
    · exact ⟨0, fun h ↦ absurd h hf⟩
  choose Θ hΘ using hΘ
  -- The Sobolev embedding sends `ξ` affinely to the bounded continuous path `γ + ξ`.
  obtain ⟨ι, hιc, hι⟩ := exists_contDiff_add_toZeroAtInfty hγ hb hp
  -- Paths `δ / 4`-close to `ξ₀` stay `δ / 2` inside `s`.
  have hsξ : ∀ ξ ∈ ball ξ₀ (δ / 4), ∀ t,
      ball (γ t + toZeroAtInfty (F := F) hp ξ t) (δ / 2) ⊆ s := fun ξ hξ t ↦
    (ball_add_toZeroAtInfty_subset hp hξ t).trans (hs t)
  refine contDiffAt_succ_iff_hasFDerivAt.2
    ⟨fun ξ ↦ trajectoryOperator (BoundedContinuousFunction.toLpTop
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) ℝ (Θ (ι ξ))),
      ⟨ball ξ₀ (δ / 4), ball_mem_nhds _ (by positivity), fun ξ hξ ↦ ?_⟩, ?_⟩
  · -- The derivative at `ξ` is the trajectory operator with coefficient `-V' (γ + ξ)`.
    refine (hasStrictFDerivAt_trajectorySection hV hγ.aestronglyMeasurable hp hV'
      hV'n.uniformContinuousOn (half_pos hδ) (hsξ ξ hξ) ?_).hasFDerivAt
    filter_upwards [BoundedContinuousFunction.coeFn_toLpTop (𝕜 := ℝ)
      (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) (Θ (ι ξ))] with t ht
    rw [ht, hΘ _ (fun t ↦ by rw [hι]; exact hsξ ξ hξ t (mem_ball_self (half_pos hδ))) t, hι]
  · -- It depends `Cⁿ` on `ξ`, through the superposition operator `f ↦ -V' ∘ f`
    -- (`BoundedContinuousFunction.contDiffAt_of_forall_apply_eq`), since the trajectory operator
    -- depends smoothly on its `L∞` coefficient (`contDiff_trajectoryOperator`).
    have hΘc : ContDiffAt ℝ n Θ (ι ξ₀) :=
      BoundedContinuousFunction.contDiffAt_of_forall_apply_eq hV'n.neg hδ
        (fun t ↦ by rw [hι]; exact hs t) fun f hf t ↦ hΘ f (fun t ↦ hs t <| by
          rw [← hι]
          exact (BoundedContinuousFunction.dist_coe_le_dist t).trans_lt hf) t
    exact (contDiff_trajectoryOperator (F := F) (mu := volume) (Omega := ⊤)
      (p := p)).contDiffAt.comp ξ₀ ((ContinuousLinearMap.contDiff _).contDiffAt.comp ξ₀
        (hΘc.comp ξ₀ (hιc.of_le le_top).contDiffAt))

/-- **The trajectory section is `C^{n+1}`, global form.** If the Lipschitz field `V` is uniformly
`C^{n+1}` on all of `F`, then the trajectory section around a continuous reference path with
bounded range is `C^{n+1}`. -/
theorem contDiff_trajectorySection (hV : LipschitzWith K V) (hγ : Continuous γ)
    (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞) {n : ℕ}
    (hVn : UniformContDiffOn ℝ (n + 1) V univ) :
    ContDiff ℝ (n + 1) (trajectorySection V γ hV hγ.aestronglyMeasurable hp) :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    contDiffAt_trajectorySection hV hγ hb hp hVn one_pos fun _ ↦ subset_univ _

/-- **The trajectory section of a `Cⁿ` field is `Cⁿ`.** On a proper space, let `V` be a Lipschitz
vector field which is `Cⁿ` for some `n ≤ ∞`, and let `γ` be a continuous reference path with
bounded range. Then the trajectory section is `Cⁿ`. -/
theorem contDiff_trajectorySection_of_contDiff [ProperSpace F] (hV : LipschitzWith K V)
    (hγ : Continuous γ) (hb : Bornology.IsBounded (range γ)) (hp : p ≠ ∞) {n : ℕ∞}
    (hVn : ContDiff ℝ n V) :
    ContDiff ℝ n (trajectorySection V γ hV hγ.aestronglyMeasurable hp) := by
  -- Continuity holds for every Lipschitz field (`lipschitzWith_trajectorySection`). For each
  -- `m + 1 ≤ n`, along each Sobolev path `ξ₀` the field is uniformly `C^{m+1}` on a compact ball
  -- containing a neighbourhood of `γ + ξ₀` (`ContDiffOn.uniformContDiffOn`), so
  -- `contDiffAt_trajectorySection` applies.
  refine contDiff_iff_forall_nat_le.2 fun m hm ↦ ?_
  rcases m with _ | m
  · exact contDiff_zero.2 (lipschitzWith_trajectorySection hV _ hp).continuous
  refine contDiff_iff_contDiffAt.2 fun ξ₀ ↦ ?_
  -- The path `γ + ξ₀` lies in the ball of radius `R - 1` about `0`.
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  set R := C + ‖toZeroAtInfty (F := F) hp ξ₀‖ + 1
  have hVs : UniformContDiffOn ℝ (m + 1) V (closedBall 0 R) :=
    ((hVn.of_le (by exact_mod_cast hm)).contDiffOn (s := ball 0 (R + 1))).uniformContDiffOn
      isOpen_ball (closedBall_subset_ball (lt_add_one R)) (isCompact_closedBall 0 R)
  refine contDiffAt_trajectorySection hV hγ hb hp hVs one_pos fun t ↦
    ball_subset_closedBall.trans (closedBall_subset_closedBall' ?_)
  rw [dist_zero_right]
  linarith [norm_add_apply_le hC (toZeroAtInfty (F := F) hp ξ₀) t]

end TauCeti.WeakDerivStep

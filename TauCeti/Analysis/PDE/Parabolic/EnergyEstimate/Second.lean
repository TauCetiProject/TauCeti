/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Galerkin
import TauCeti.Analysis.ODE.Gronwall

/-!
# The second energy estimate for symmetric parabolic equations

Testing a parabolic equation against the time derivative controls that derivative in the
pivot space and the solution in the energy space, uniformly in the Galerkin dimension.
Here the energy form may depend differentiably on time. Its time derivative contributes
an additional integral; a coercivity bound and Grönwall absorb this term.

The estimates apply to any continuously differentiable trial curve in a real normed space
`V`, with a continuous linear map `ι : V →L[ℝ] H` into a real inner product space. The energy
estimates need neither finite dimensionality nor injectivity. On a Galerkin trial space,
use the restricted energy form and the composite of the trial map with the pivot inclusion.
The forcing lies in `H`, not merely in the dual of `V`: this stronger data assumption is
what permits testing against the time derivative with a dimension-independent bound.

Symmetry is essential to this argument. No estimate for a nonsymmetric energy form is
asserted. In the autonomous case, no coercivity is needed for the energy inequality itself.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5
  (the second Galerkin energy estimate).
* J.-L. Lions, *Équations différentielles opérationnelles et problèmes aux limites*,
  Chapter III.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti.PDE

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {ι : V →L[ℝ] H} {A : ℝ → V →L[ℝ] StrongDual ℝ V}
  {u : ℝ → V} {f : ℝ → H} {a b α M : ℝ}

/-- Differentiating the diagonal of a time-dependent symmetric form along a trial curve. -/
private theorem hasDerivAt_energy (hA : ContDiff ℝ 1 A) (hu : ContDiff ℝ 1 u)
    (t : ℝ) (hsym : ∀ x y, A t x y = A t y x) :
    HasDerivAt (fun s ↦ A s (u s) (u s))
      (deriv A t (u t) (u t) + 2 * A t (u t) (deriv u t)) t := by
  convert (((hA.differentiable one_ne_zero t).hasDerivAt.clm_apply
    (hu.differentiable one_ne_zero t).hasDerivAt).clm_apply
    (hu.differentiable one_ne_zero t).hasDerivAt) using 1
  simp only [add_apply, hsym (deriv u t) (u t)]
  ring

/-- **The second energy inequality before absorption.** Testing a symmetric parabolic
Galerkin equation against `u'` bounds the accumulated squared pivot norm of `u'` and the
terminal energy by the initial energy, the squared pivot norm of the forcing, and the
integral of the time derivative of the energy form. -/
theorem energy_add_integral_norm_deriv_sq_le (hA : ContDiff ℝ 1 A)
    (hu : ContDiff ℝ 1 u) (hf : Continuous f)
    (hsym : ∀ t ∈ Icc a b, ∀ x y, A t x y = A t y x)
    (heq : ∀ t ∈ Icc a b, ∀ v,
      ⟪ι (deriv u t), ι v⟫_ℝ + A t (u t) v = ⟪f t, ι v⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (u t) (u t) + (∫ s in a..t, ‖ι (deriv u s)‖ ^ 2) ≤
      A a (u a) (u a) + (∫ s in a..t, ‖f s‖ ^ 2) +
        ∫ s in a..t, deriv A s (u s) (u s) := by
  have hD : Continuous (fun s ↦ ‖ι (deriv u s)‖ ^ 2) :=
    (ι.continuous.comp hu.continuous_deriv_one).norm.pow 2
  have hF : Continuous (fun s ↦ ‖f s‖ ^ 2) := hf.norm.pow 2
  have hE' : Continuous (fun s ↦ deriv A s (u s) (u s)) :=
    (hA.continuous_deriv_one.clm_apply hu.continuous).clm_apply hu.continuous
  have hcross : Continuous (fun s ↦ 2 * A s (u s) (deriv u s)) :=
    ((hA.continuous.clm_apply hu.continuous).clm_apply hu.continuous_deriv_one).const_mul 2
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (((hA.continuous.clm_apply hu.continuous).clm_apply hu.continuous).continuousOn)
    (fun s hs ↦ hasDerivAt_energy hA hu s (hsym s ⟨hs.1.le, hs.2.le.trans ht.2⟩))
    ((hE'.add hcross).intervalIntegrable a t)
  have hpoint (s : ℝ) (hs : s ∈ Icc a t) :
      (deriv A s (u s) (u s) + 2 * A s (u s) (deriv u s)) +
        ‖ι (deriv u s)‖ ^ 2 ≤ ‖f s‖ ^ 2 + deriv A s (u s) (u s) := by
    have he := heq s (Icc_subset_Icc_right ht.2 hs) (deriv u s)
    rw [real_inner_self_eq_norm_sq] at he
    have hyoung := real_inner_le_norm (f s) (ι (deriv u s))
    nlinarith [sq_nonneg (‖f s‖ - ‖ι (deriv u s)‖)]
  have hint := intervalIntegral.integral_mono_on (μ := volume) ht.1
    ((hE'.add hcross).add hD |>.intervalIntegrable a t)
    ((hF.add hE').intervalIntegrable a t) hpoint
  have hsplit := intervalIntegral.integral_add (μ := volume)
    (hE'.add hcross |>.intervalIntegrable a t) (hD.intervalIntegrable a t)
  simp only [Pi.add_apply] at hint hsplit
  rw [hsplit, hid,
    intervalIntegral.integral_add (hF.intervalIntegrable a t) (hE'.intervalIntegrable a t)] at hint
  linarith

/-- **The second parabolic energy estimate.** Suppose the symmetric energy form is coercive
with constant `α > 0` and its time derivative is bounded above by `M ‖v‖²`, with `M ≥ 0`.
A classical solution with pivot-space forcing satisfies an estimate for its energy and the
accumulated squared pivot norm of its time derivative. The constants are independent of any
Galerkin dimension. -/
theorem energy_add_integral_norm_deriv_sq_le_mul_exp (hA : ContDiff ℝ 1 A)
    (hu : ContDiff ℝ 1 u) (hf : Continuous f)
    (hsym : ∀ t ∈ Icc a b, ∀ x y, A t x y = A t y x) (hα : 0 < α) (hM : 0 ≤ M)
    (hcoer : ∀ t ∈ Icc a b, ∀ v, α * ‖v‖ ^ 2 ≤ A t v v)
    (hbound : ∀ t ∈ Icc a b, ∀ v, deriv A t v v ≤ M * ‖v‖ ^ 2)
    (heq : ∀ t ∈ Icc a b, ∀ v,
      ⟪ι (deriv u t), ι v⟫_ℝ + A t (u t) v = ⟪f t, ι v⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    A t (u t) (u t) + (∫ s in a..t, ‖ι (deriv u s)‖ ^ 2) ≤
      (A a (u a) (u a) + ∫ s in a..t, ‖f s‖ ^ 2) * Real.exp (M / α * (t - a)) := by
  let X : ℝ → ℝ := fun s ↦ A s (u s) (u s) + ∫ r in a..s, ‖ι (deriv u r)‖ ^ 2
  have hD : Continuous (fun s ↦ ‖ι (deriv u s)‖ ^ 2) :=
    (ι.continuous.comp hu.continuous_deriv_one).norm.pow 2
  have hF : Continuous (fun s ↦ ‖f s‖ ^ 2) := hf.norm.pow 2
  have hE' : Continuous (fun s ↦ deriv A s (u s) (u s)) :=
    (hA.continuous_deriv_one.clm_apply hu.continuous).clm_apply hu.continuous
  have hprim : ContinuousOn (fun s ↦ ∫ r in a..s, ‖ι (deriv u r)‖ ^ 2) (Icc a t) := by
    rw [← uIcc_of_le ht.1]
    exact intervalIntegral.continuousOn_primitive_interval hD.continuousOn.integrableOn_uIcc
  have hX : ContinuousOn X (Icc a t) :=
    ((hA.continuous.clm_apply hu.continuous).clm_apply hu.continuous).continuousOn.add hprim
  have hEX (s : ℝ) (hs : s ∈ Icc a t) : A s (u s) (u s) ≤ X s :=
    le_add_of_nonneg_right (intervalIntegral.integral_nonneg hs.1 fun _ _ ↦ sq_nonneg _)
  have hderiv (s : ℝ) (hs : s ∈ Icc a t) :
      deriv A s (u s) (u s) ≤ M / α * X s := by
    have hc := hcoer s (Icc_subset_Icc_right ht.2 hs) (u s)
    have hb := hbound s (Icc_subset_Icc_right ht.2 hs) (u s)
    calc
      deriv A s (u s) (u s) ≤ M * ‖u s‖ ^ 2 := hb
      _ ≤ M * (X s / α) := by
        gcongr
        exact (le_div_iff₀ hα).2 (by nlinarith [hEX s hs])
      _ = M / α * X s := by ring
  have hgr : ∀ s ∈ Icc a t,
      X s ≤ (A a (u a) (u a) + ∫ r in a..t, ‖f r‖ ^ 2) + M / α * ∫ r in a..s, X r := by
    intro s hs
    have hst := Icc_subset_Icc_right ht.2 hs
    have henergy := energy_add_integral_norm_deriv_sq_le hA hu hf hsym heq hst
    have hfmono := intervalIntegral.integral_mono_interval (μ := volume) le_rfl hs.1 hs.2
      (Filter.Eventually.of_forall fun r ↦ sq_nonneg ‖f r‖) (hF.intervalIntegrable a t)
    have hderivint := intervalIntegral.integral_mono_on (μ := volume) hs.1
      (hE'.intervalIntegrable a s)
      ((hX.const_mul (M / α)).mono (Icc_subset_Icc_right hs.2) |>.intervalIntegrable_of_Icc hs.1)
      (fun r hr ↦ hderiv r (Icc_subset_Icc_right hs.2 hr))
    rw [intervalIntegral.integral_const_mul] at hderivint
    exact henergy.trans (by linarith)
  exact TauCeti.le_mul_exp_of_le_add_mul_integral hX (div_nonneg hM hα.le) hgr t
    (right_mem_Icc.2 ht.1)

/-- **Autonomous second energy estimate.** For a fixed symmetric energy form, no coercivity
is needed to bound terminal energy plus the time-derivative integral. In particular, for a
coercive form the estimate controls the solution uniformly in the energy norm. -/
theorem energy_add_integral_norm_deriv_sq_le_of_constant
    {B : V →L[ℝ] StrongDual ℝ V} (hsym : ∀ x y, B x y = B y x)
    (hu : ContDiff ℝ 1 u) (hf : Continuous f)
    (heq : ∀ t ∈ Icc a b, ∀ v,
      ⟪ι (deriv u t), ι v⟫_ℝ + B (u t) v = ⟪f t, ι v⟫_ℝ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    B (u t) (u t) + (∫ s in a..t, ‖ι (deriv u s)‖ ^ 2) ≤
      B (u a) (u a) + ∫ s in a..t, ‖f s‖ ^ 2 := by
  have hd (s : ℝ) : deriv (fun _ : ℝ ↦ B) s = 0 := (hasDerivAt_const s B).deriv
  simpa [hd] using energy_add_integral_norm_deriv_sq_le
    (A := fun _ ↦ B) contDiff_const hu hf (fun _ _ ↦ hsym) heq ht

/-- **Galerkin approximations with the second energy estimate.** For a fixed symmetric
energy form and continuous pivot-space forcing, each finite-dimensional trial map injective
into the pivot space admits a global classical Galerkin solution. On every forward interval,
its terminal energy plus the squared time-derivative integral is bounded by the initial
energy plus the squared forcing integral, with constant one independent of the trial space. -/
theorem exists_galerkinSolution_energy_add_integral_norm_deriv_sq_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {B : V →L[ℝ] StrongDual ℝ V} (hsym : ∀ x y, B x y = B y x)
    (e : F →L[ℝ] V) (he : Function.Injective (ι.comp e)) (hf : Continuous f) (x : F) (a : ℝ) :
    ∃ c : ℝ → F, c a = x ∧ ContDiff ℝ 1 c ∧
      (∀ t v, ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + B (e (c t)) (e v) =
        ⟪f t, ι (e v)⟫_ℝ) ∧
      ∀ t ∈ Ici a, B (e (c t)) (e (c t)) +
          (∫ s in a..t, ‖ι (e (deriv c s))‖ ^ 2) ≤
        B (e x) (e x) + ∫ s in a..t, ‖f s‖ ^ 2 := by
  obtain ⟨c, hc, _⟩ := existsUnique_galerkinSolution ι B e he
    (ι.gelfandDual.continuous.comp hf) x a
  have hceq (t : ℝ) (v : F) :
      ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + B (e (c t)) (e v) = ⟪f t, ι (e v)⟫_ℝ := by
    simpa only [Function.comp_apply, ContinuousLinearMap.gelfandDual_apply] using hc.2.2 t v
  refine ⟨c, hc.1, hc.2.1, hceq, fun t ht ↦ ?_⟩
  have htrial : ∀ s ∈ Icc a t, ∀ v,
      ⟪(ι.comp e) (deriv c s), (ι.comp e) v⟫_ℝ +
        B.bilinearComp e e (c s) v = ⟪f s, (ι.comp e) v⟫_ℝ := by
    intro s _ v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply]
      using hceq s v
  have henergy := energy_add_integral_norm_deriv_sq_le_of_constant
    (fun v w ↦ hsym (e v) (e w)) hc.2.1 hf htrial (right_mem_Icc.2 ht)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.bilinearComp_apply, hc.1]
    using henergy

end TauCeti.PDE

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integration by parts for directional derivatives

## Bilinear pairings of two directional derivatives of a compactly supported map

For a compactly supported `C²` map `u` on a finite-dimensional real space and a continuous
bilinear map `B`, the integral of `B (∂_v u) (∂_w u)` against a Haar measure does not change when
the two directions are exchanged. Integrating by parts in the direction `w` turns it into
`-∫ B (∂_w ∂_v u) u`, and the exchanged integral into `-∫ B (∂_v ∂_w u) u`; the two agree because
the second derivative is symmetric.

Consequently the integral vanishes whenever `B` is alternating. That is the vanishing of the
integral over the whole space of the pullback of a constant two-form along a compactly supported
map — the "null Lagrangian" phenomenon: for a map from the plane to the plane, with `B` the
standard area form and the two coordinate directions, the integrand is the Jacobian determinant.
It is what makes the energy of a compactly supported map into a symplectic vector space equal the
square of the `L²` norm of its Cauchy--Riemann defect.

## The uncertainty inequality

For a symmetric positive semidefinite bilinear form `B`, a linear functional `ℓ` and a direction
`v` with `ℓ v = 1`, every compactly supported `C¹` map `u` satisfies
`|ω| ∫ B(u, u) ≤ ∫ B(∂_v u, ∂_v u) + ω² ∫ ℓ² B(u, u)`. It comes from expanding
`0 ≤ ∫ B(∂_v u + ω ℓ u, ∂_v u + ω ℓ u)` and integrating the cross term by parts. For a function on
the line this is the lower bound `|ω|` for the harmonic oscillator `-d²/dx² + ω² x²`.

## Integration by parts against a Lipschitz function

For an open set `U`, a function `f` that is `C¹` on `U`, and a Lipschitz function `g` with
compact support in `U`, the identity `∫ (∂_v g) f = -∫ g (∂_v f)` holds, with `∂_v g` the
directional derivative of `g`, which exists almost everywhere by Rademacher's theorem. A cutoff
equal to one near the support of `g` reduces it to Mathlib's integration by parts for two
Lipschitz functions. This is the smooth case of integration by parts in `W^{1,p}` against a
Lipschitz test function.

## Main results

* `TauCeti.integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply`: integration by
  parts `∫ B (∂_v f) (∂_w g) = -∫ B (∂_w ∂_v f) g` against a compactly supported map `g`, for `f`
  that is `C²` near the support of `g`.
* `TauCeti.integral_neg_fderiv_fderiv_apply_mul_eq_integral_sq`: for a continuous linear
  functional `L`, `∫ -L (∂_v² u) * L u = ∫ L (∂_v u) ^ 2`.
  `TauCeti.integrable_neg_fderiv_fderiv_apply_mul_of_hasCompactSupport`,
  `TauCeti.integrable_mul_sq_of_hasCompactSupport` and
  `TauCeti.integrable_sq_of_hasCompactSupport` record the integrability of `-L (∂_w ∂_v u) * L u`
  and of the weighted squares `g · (L u) ^ 2`.
* `TauCeti.integral_bilinear_fderiv_apply_comm`: the integral of `B (∂_v u) (∂_w u)` is symmetric
  in the two directions, and `TauCeti.integral_bilinForm_fderiv_apply_comm` its form for a
  bilinear form on a finite-dimensional space.
* `TauCeti.integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`: for an alternating bilinear form
  the integral vanishes.
* `TauCeti.integral_fderiv_apply_eq_zero_of_hasCompactSupport`: the integral of a directional
  derivative of a compactly supported `C¹` map vanishes.
  `TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport` is the same statement for the whole
  derivative, and `TauCeti.setIntegral_fderiv_apply_sub_fderiv_apply_eq_zero` its form for a
  difference of two directional derivatives over a set containing both supports.
  `TauCeti.integrable_fderiv_apply_of_hasCompactSupport` records the integrability.
* `TauCeti.abs_mul_integral_bilinear_le_integral_bilinear_fderiv_apply_add`: the uncertainty
  inequality, with `TauCeti.integral_mul_bilinear_fderiv_apply_eq_neg_integral_div_two` the
  integration by parts behind it, and
  `TauCeti.abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add` its consequence for
  the harmonic oscillator `-∂_v² + ω² ℓ²` acting on a coordinate `L u`.
* `TauCeti.integral_sum_neg_fderiv_fderiv_apply_mul_eq_integral_sum_sq`: the Dirichlet energy
  identity `∫ ⟨-∂_v² φ, φ⟩ = ∫ |∂_v φ|²` for a compactly supported `C²` map into finite coordinate
  vectors.
* `TauCeti.integral_lineDeriv_mul_eq_neg_of_contDiffOn`: integration by parts between a function
  `C¹` on an open set and a Lipschitz function with compact support in it.

## References

* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`, theorem
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: the integration by parts in a single
  direction that every proof here is built on.
* G. B. Folland and A. Sitaram, *The uncertainty principle: a mathematical survey*, J. Fourier
  Anal. Appl. **3** (1997), 207–238, §1, for the proof of the uncertainty inequality by
  integration by parts.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped Topology

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → V}

/-- A function vanishing wherever a compactly supported function vanishes has compact support. -/
private theorem hasCompactSupport_of_eq_zero {α β γ : Type*} [TopologicalSpace α] [Zero β]
    [Zero γ] {f : α → β} {F : α → γ} (hf : HasCompactSupport f)
    (hF : ∀ x, f x = 0 → F x = 0) : HasCompactSupport F :=
  hf.mono <| Function.support_subset_iff'.2 fun x hx ↦ hF x (Function.notMem_support.1 hx)

/-- **Integration by parts against a directional derivative.** For a continuous bilinear map `B`,
a compactly supported `C¹` map `g` and a map `f` that is `C²` at every point of the support of
`g`, integrating by parts in the direction `w` gives `∫ B (∂_v f) (∂_w g) = -∫ B (∂_w ∂_v f) g`.
Nothing is assumed about `f` away from the support of `g`: a cutoff equal to one near it reduces
the statement to a globally `C²` map. -/
theorem integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply {V' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (B : V →L[ℝ] V' →L[ℝ] W) {f : E → V}
    {g : E → V'} (hf : ∀ x ∈ tsupport g, ContDiffAt ℝ 2 f x) (hg : ContDiff ℝ 1 g)
    (hsupp : HasCompactSupport g) (v w : E) :
    ∫ x, B (fderiv ℝ f x v) (fderiv ℝ g x w) ∂μ =
      -∫ x, B (fderiv ℝ (fderiv ℝ f) x w v) (g x) ∂μ := by
  -- A globally `C²` map `F` agreeing with `f` near the support of `g`.
  obtain ⟨F, hF, hFf⟩ : ∃ F : E → V, ContDiff ℝ 2 F ∧ ∀ x ∈ tsupport g, F =ᶠ[𝓝 x] f := by
    have hU : IsOpen {x | ContDiffAt ℝ 2 f x} :=
      isOpen_iff_mem_nhds.2 fun x hx ↦ ContDiffAt.eventually hx (by simp)
    obtain ⟨χ, hχ, -, hχ1, -, hχs⟩ := hsupp.exists_contDiff_cutoff_eventuallyEq_one hU hf
    refine ⟨fun x ↦ χ x • f x, ContDiffOn.contDiff_smul_of_tsupport_subset
      (fun x hx ↦ ContDiffAt.contDiffWithinAt hx) hU (hχ.of_le (by simp)).contDiffOn hχs,
      fun x hx ↦ ?_⟩
    filter_upwards [hχ1 x hx] with y hy
    simp [hy]
  -- Off the support of `g` both integrands vanish, and on it `F` and `f` have the same derivatives.
  have hFf₁ : ∀ x, B (fderiv ℝ F x v) (fderiv ℝ g x w) = B (fderiv ℝ f x v) (fderiv ℝ g x w) :=
    fun x ↦ by
      by_cases hx : x ∈ tsupport g
      · rw [(hFf x hx).fderiv_eq]
      · simp [fderiv_of_notMem_tsupport ℝ hx]
  have hFf₂ : ∀ x, B (fderiv ℝ (fderiv ℝ F) x w v) (g x) =
      B (fderiv ℝ (fderiv ℝ f) x w v) (g x) := fun x ↦ by
    by_cases hx : x ∈ tsupport g
    · rw [(hFf x hx).fderiv.fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp only [← hFf₁, ← hFf₂]
  clear hFf₁ hFf₂ hFf hf
  have hF' : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hcv : Continuous fun x ↦ fderiv ℝ F x v :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  -- a bilinear pairing whose right factor has compact support has compact support
  have hcs : ∀ (P : E → V) (Q : E → V'), HasCompactSupport Q →
      HasCompactSupport fun x ↦ B (P x) (Q x) :=
    fun P Q hQ ↦ hQ.mono fun x hx ↦ by
      simp only [Function.mem_support] at hx ⊢
      contrapose hx
      simp [hx]
  -- the derivative in the direction `w` of the derivative of `F` in the direction `v`
  have hsnd : ∀ x, fderiv ℝ (fun y ↦ fderiv ℝ F y v) x w = fderiv ℝ (fderiv ℝ F) x w v := by
    intro x
    rw [fderiv_clm_apply (hF'.differentiable one_ne_zero x) (differentiableAt_const v)]
    simp
  have h1 : Integrable (fun x ↦ B (fderiv ℝ (fun y ↦ fderiv ℝ F y v) x w) (g x)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (hcs _ _ hsupp)
    simp only [hsnd]
    exact (B.continuous.comp (((hF'.continuous_fderiv one_ne_zero).clm_apply
      continuous_const).clm_apply continuous_const)).clm_apply hg.continuous
  have h2 : Integrable (fun x ↦ B (fderiv ℝ F x v) (fderiv ℝ g x w)) μ :=
    Continuous.integrable_of_hasCompactSupport
      ((B.continuous.comp hcv).clm_apply
        ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const))
      (hcs _ _ (hsupp.fderiv_apply (𝕜 := ℝ) w))
  have h3 : Integrable (fun x ↦ B (fderiv ℝ F x v) (g x)) μ :=
    Continuous.integrable_of_hasCompactSupport
      ((B.continuous.comp hcv).clm_apply hg.continuous) (hcs _ _ hsupp)
  have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ) (B := B)
    (f := fun x ↦ fderiv ℝ F x v) (g := g) (v := w) h1 h2 h3
    (fun x _ ↦ (hF'.differentiable one_ne_zero x).clm_apply (differentiableAt_const v))
    (fun x _ ↦ hg.differentiable one_ne_zero x)
  simpa only [hsnd] using this

/-- **Integration by parts for a coordinate of a second derivative.** For a compactly supported
`C²` map `u` and a continuous linear functional `L`, the pairing of `-L (∂_v² u)` with `L u`
integrates to the integral of `L (∂_v u) ^ 2`. -/
theorem integral_neg_fderiv_fderiv_apply_mul_eq_integral_sq (L : V →L[ℝ] ℝ)
    (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) (v : E) :
    ∫ x, -L (fderiv ℝ (fderiv ℝ u) x v v) * L (u x) ∂μ = ∫ x, L (fderiv ℝ u x v) ^ 2 ∂μ := by
  have h := integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply (μ := μ)
    ((ContinuousLinearMap.mul ℝ ℝ).bilinearComp L L) (fun x _ ↦ hu.contDiffAt)
    (hu.of_le (by norm_num)) hsupp v v
  simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply'] at h
  simp only [sq, h, neg_mul, integral_neg]

/-- Exchanging the two differentiation directions does not change the integral of a continuous
bilinear pairing of two directional derivatives of a compactly supported `C²` map. -/
theorem integral_bilinear_fderiv_apply_comm (B : V →L[ℝ] V →L[ℝ] W) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      ∫ x, B (fderiv ℝ u x w) (fderiv ℝ u x v) ∂μ := by
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hsymm : ∀ x : E, fderiv ℝ (fderiv ℝ u) x w v = fderiv ℝ (fderiv ℝ u) x v w :=
    fun x ↦ (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v
  rw [integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply B
      (fun x _ ↦ hu.contDiffAt) hu₁ hsupp v w,
    integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply B
      (fun x _ ↦ hu.contDiffAt) hu₁ hsupp w v]
  simp only [hsymm]

/-- The integral of a directional derivative of a compactly supported `C¹` map vanishes. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) (v : E) : ∫ x, fderiv ℝ u x v ∂μ = 0 := by
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable (μ := μ)
    (f := fun _ ↦ (1 : ℝ)) (g := u) (v := v) (by simp)
    (by simpa using ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      |>.integrable_of_hasCompactSupport (hsupp.fderiv_apply (𝕜 := ℝ) v))
    (by simpa using hu.continuous.integrable_of_hasCompactSupport hsupp)
    (fun _ _ ↦ differentiableAt_const _)
    (fun _ _ ↦ (hu.differentiable one_ne_zero).differentiableAt)
  simpa using h

omit [FiniteDimensional ℝ E] in
/-- A directional derivative of a compactly supported `C¹` map is integrable. -/
theorem integrable_fderiv_apply_of_hasCompactSupport (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) (v : E) : Integrable (fun x ↦ fderiv ℝ u x v) μ :=
  ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hsupp.fderiv_apply (𝕜 := ℝ) v)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A continuous weight times the square of a continuous linear functional of a compactly
supported continuous map is integrable. -/
theorem integrable_mul_sq_of_hasCompactSupport (L : V →L[ℝ] ℝ) {g : E → ℝ} (hg : Continuous g)
    (hu : Continuous u) (hsupp : HasCompactSupport u) :
    Integrable (fun x ↦ g x * L (u x) ^ 2) μ :=
  (hg.mul ((L.continuous.comp hu).pow 2)).integrable_of_hasCompactSupport <|
    hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The square of a continuous linear functional of a compactly supported continuous map is
integrable. -/
theorem integrable_sq_of_hasCompactSupport (L : V →L[ℝ] ℝ) (hu : Continuous u)
    (hsupp : HasCompactSupport u) : Integrable (fun x ↦ L (u x) ^ 2) μ := by
  simpa using integrable_mul_sq_of_hasCompactSupport (μ := μ) L continuous_const hu hsupp
    (g := fun _ ↦ 1)

omit [FiniteDimensional ℝ E] in
/-- For a compactly supported `C²` map `u` and a continuous linear functional `L`, the pairing
`-L (∂_w ∂_v u) * L u` is integrable. -/
theorem integrable_neg_fderiv_fderiv_apply_mul_of_hasCompactSupport (L : V →L[ℝ] ℝ)
    (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) (v w : E) :
    Integrable (fun x ↦ -L (fderiv ℝ (fderiv ℝ u) x w v) * L (u x)) μ :=
  ((L.continuous.comp ((((hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
    one_ne_zero).clm_apply continuous_const).clm_apply continuous_const)).neg.mul
      (L.continuous.comp hu.continuous)).integrable_of_hasCompactSupport <|
    hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx]

/-- For compactly supported `C¹` maps `f` and `g` whose supports lie in a set `D`, the integral
over `D` of the difference of directional derivatives `x ↦ f'(x) v - g'(x) w` vanishes. -/
theorem setIntegral_fderiv_apply_sub_fderiv_apply_eq_zero {f g : E → V} {D : Set E}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hfD : tsupport f ⊆ D)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (hgD : tsupport g ⊆ D) (v w : E) :
    ∫ x in D, (fderiv ℝ f x v - fderiv ℝ g x w) ∂μ = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_,
    integral_sub (integrable_fderiv_apply_of_hasCompactSupport hf hfc v)
      (integrable_fderiv_apply_of_hasCompactSupport hg hgc w),
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hf hfc,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hg hgc, sub_zero]
  rw [fderiv_of_notMem_tsupport ℝ fun h ↦ hx (hfD h),
    fderiv_of_notMem_tsupport ℝ fun h ↦ hx (hgD h), zero_apply, zero_apply,
    sub_zero]

/-- The integral of the derivative of a compactly supported `C¹` map vanishes. -/
theorem integral_fderiv_eq_zero_of_hasCompactSupport (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) : ∫ x, fderiv ℝ u x ∂μ = 0 := by
  ext v
  rw [ContinuousLinearMap.integral_apply ((hu.continuous_fderiv one_ne_zero)
    |>.integrable_of_hasCompactSupport (hsupp.fderiv (𝕜 := ℝ))) v,
    integral_fderiv_apply_eq_zero_of_hasCompactSupport hu hsupp v, zero_apply]

/-- **The Dirichlet energy by parts.** For a compactly supported `C²` map `φ` into a space of
finite coordinate vectors and a direction `v`, `∫ ⟨-∂_v² φ, φ⟩ = ∫ |∂_v φ|²` for the coordinatewise
pairing `⟨a, b⟩ = ∑ₖ aₖ bₖ`. This is
`TauCeti.integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply` for the dot product. -/
theorem integral_sum_neg_fderiv_fderiv_apply_mul_eq_integral_sum_sq {κ : Type*} [Fintype κ]
    {φ : E → κ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : HasCompactSupport φ) (v : E) :
    ∫ x, ∑ k, -fderiv ℝ (fderiv ℝ φ) x v v k * φ x k ∂μ = ∫ x, ∑ k, fderiv ℝ φ x v k ^ 2 ∂μ := by
  have h := integral_bilinear_fderiv_apply_eq_neg_integral_fderiv_fderiv_apply (μ := μ)
    (∑ k, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.proj k)
      (ContinuousLinearMap.proj k)) (fun x _ ↦ hφ.contDiffAt) (hφ.of_le (by norm_num)) hsupp v v
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply] at h
  simp only [neg_mul, Finset.sum_neg_distrib, integral_neg, sq, h]

section Uncertainty

variable {B : V →L[ℝ] V →L[ℝ] ℝ} {ℓ : E →L[ℝ] ℝ} {v : E}

omit [FiniteDimensional ℝ E] in
/-- For a compactly supported `C¹` map `u`, the pairing `ℓ · B(u, ∂_v u)` is integrable. -/
private theorem integrable_mul_bilinear_fderiv_apply (hu : ContDiff ℝ 1 u)
    (hsupp : HasCompactSupport u) : Integrable (fun x ↦ ℓ x * B (u x) (fderiv ℝ u x v)) μ :=
  Continuous.integrable_of_hasCompactSupport (ℓ.continuous.mul
    ((B.continuous.comp hu.continuous).clm_apply
      ((hu.continuous_fderiv one_ne_zero).clm_apply continuous_const)))
    (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx])

/-- For a symmetric continuous bilinear form `B`, a continuous linear functional `ℓ` with
`ℓ v = 1` and a compactly supported `C¹` map `u`, the integral of `ℓ · B(u, ∂_v u)` is
`-(1/2) ∫ B(u, u)`: the integral of the derivative `∂_v (ℓ · B(u, u)) = B(u, u) + 2 ℓ B(u, ∂_v u)`
vanishes. -/
theorem integral_mul_bilinear_fderiv_apply_eq_neg_integral_div_two (hB : ∀ y z, B y z = B z y)
    (hv : ℓ v = 1) (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u) :
    ∫ x, ℓ x * B (u x) (fderiv ℝ u x v) ∂μ = -(∫ x, B (u x) (u x) ∂μ) / 2 := by
  have hcu : Continuous u := hu.continuous
  have hcdu : Continuous fun x ↦ fderiv ℝ u x v :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv : ∀ x, HasFDerivAt (fun y ↦ ℓ y • u y)
      (ℓ x • fderiv ℝ u x + ℓ.smulRight (u x)) x := fun x ↦
    ℓ.hasFDerivAt.smul (hu.differentiable one_ne_zero x).hasFDerivAt
  have hibp := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := μ) (B := B)
    (f := u) (f' := fderiv ℝ u) (g := fun y ↦ ℓ y • u y)
    (g' := fun x ↦ ℓ x • fderiv ℝ u x + ℓ.smulRight (u x)) (v := v)
    (Continuous.integrable_of_hasCompactSupport ((B.continuous.comp hcdu).clm_apply
      (ℓ.continuous.smul hcu)) (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx]))
    (Continuous.integrable_of_hasCompactSupport ((B.continuous.comp hcu).clm_apply
      ((ℓ.continuous.smul hcdu).add (continuous_const.smul hcu)))
      (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx]))
    (Continuous.integrable_of_hasCompactSupport ((B.continuous.comp hcu).clm_apply
      (ℓ.continuous.smul hcu)) (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx]))
    (fun x _ ↦ (hu.differentiable one_ne_zero x).hasFDerivAt) (fun x _ ↦ hderiv x)
  have hI₁ : Integrable (fun x ↦ ℓ x * B (u x) (fderiv ℝ u x v)) μ :=
    integrable_mul_bilinear_fderiv_apply hu hsupp
  have hI₂ : Integrable (fun x ↦ B (u x) (u x)) μ :=
    Continuous.integrable_of_hasCompactSupport ((B.continuous.comp hcu).clm_apply hcu)
      (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx])
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, hv, one_smul, map_add, map_smul, smul_eq_mul] at hibp
  rw [integral_add hI₁ hI₂] at hibp
  simp only [hB (fderiv ℝ u _ v)] at hibp
  linarith

/-- **The uncertainty inequality** for a directional derivative and a linear weight. Let `B` be a
symmetric positive semidefinite continuous bilinear form, `ℓ` a continuous linear functional and
`v` a direction with `ℓ v = 1`. For a compactly supported `C¹` map `u` and every real `ω`,
`|ω| ∫ B(u, u) ≤ ∫ B(∂_v u, ∂_v u) + ω² ∫ ℓ² B(u, u)`.

For a function on the line, with `B` the product, `ℓ = v = 1`, this says that the harmonic
oscillator `-d²/dx² + ω² x²` is bounded below by `|ω|`, the energy of its ground state
`e^{-|ω| x² / 2}`. -/
theorem abs_mul_integral_bilinear_le_integral_bilinear_fderiv_apply_add
    (hB : ∀ y z, B y z = B z y) (hBnonneg : ∀ y, 0 ≤ B y y) (hv : ℓ v = 1)
    (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u) (ω : ℝ) :
    |ω| * ∫ x, B (u x) (u x) ∂μ ≤
      ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x v) ∂μ + ω ^ 2 * ∫ x, ℓ x ^ 2 * B (u x) (u x) ∂μ := by
  have hcu : Continuous u := hu.continuous
  have hcdu : Continuous fun x ↦ fderiv ℝ u x v :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hP : Integrable (fun x ↦ B (fderiv ℝ u x v) (fderiv ℝ u x v)) μ :=
    Continuous.integrable_of_hasCompactSupport ((B.continuous.comp hcdu).clm_apply hcdu)
      (hasCompactSupport_of_eq_zero (hsupp.fderiv_apply (𝕜 := ℝ) v) fun x hx ↦ by simp [hx])
  have hY : Integrable (fun x ↦ ℓ x * B (u x) (fderiv ℝ u x v)) μ :=
    integrable_mul_bilinear_fderiv_apply hu hsupp
  have hX : Integrable (fun x ↦ ℓ x ^ 2 * B (u x) (u x)) μ :=
    Continuous.integrable_of_hasCompactSupport ((ℓ.continuous.pow 2).mul
      ((B.continuous.comp hcu).clm_apply hcu))
      (hasCompactSupport_of_eq_zero hsupp fun x hx ↦ by simp [hx])
  have hhalf := integral_mul_bilinear_fderiv_apply_eq_neg_integral_div_two (μ := μ) hB hv hu hsupp
  -- `0 ≤ ∫ B(∂_v u + r ℓ u, ∂_v u + r ℓ u)` for every real `r`
  have key : ∀ r : ℝ, r * ∫ x, B (u x) (u x) ∂μ ≤
      ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x v) ∂μ + r ^ 2 * ∫ x, ℓ x ^ 2 * B (u x) (u x) ∂μ := by
    intro r
    have hexp : ∀ x, B (fderiv ℝ u x v + (r * ℓ x) • u x) (fderiv ℝ u x v + (r * ℓ x) • u x) =
        B (fderiv ℝ u x v) (fderiv ℝ u x v) + (2 * r) * (ℓ x * B (u x) (fderiv ℝ u x v)) +
          r ^ 2 * (ℓ x ^ 2 * B (u x) (u x)) := fun x ↦ by
      simp only [map_add, map_smul, add_apply, smul_apply,
        smul_eq_mul, hB (fderiv ℝ u x v) (u x)]
      ring
    have hnonneg : 0 ≤ ∫ x, B (fderiv ℝ u x v + (r * ℓ x) • u x)
        (fderiv ℝ u x v + (r * ℓ x) • u x) ∂μ :=
      integral_nonneg fun x ↦ hBnonneg _
    simp only [hexp] at hnonneg
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, hhalf] at hnonneg
    · linarith
    · exact hP
    · exact hY.const_mul _
    · exact hP.add (hY.const_mul _)
    · exact hX.const_mul _
  rcases abs_cases ω with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
    exact key ω
  · rw [h, ← neg_sq ω]
    simpa using key (-ω)

/-- **The harmonic-oscillator lower bound** for a coordinate of a compactly supported `C²` map
`u`. For a continuous linear functional `L`, a continuous linear functional `ℓ` with `ℓ v = 1` and
every real `ω`, `⟨(-∂_v² + ω² ℓ²) L u, L u⟩ ≥ |ω| ‖L u‖²`: the uncertainty inequality for the
form `(y, z) ↦ L y * L z`, with the derivative term integrated by parts. -/
theorem abs_mul_integral_sq_le_integral_neg_fderiv_fderiv_apply_mul_add (L : V →L[ℝ] ℝ)
    (hv : ℓ v = 1) (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) (ω : ℝ) :
    |ω| * ∫ x, L (u x) ^ 2 ∂μ ≤
      ∫ x, -L (fderiv ℝ (fderiv ℝ u) x v v) * L (u x) ∂μ +
        ω ^ 2 * ∫ x, ℓ x ^ 2 * L (u x) ^ 2 ∂μ := by
  rw [integral_neg_fderiv_fderiv_apply_mul_eq_integral_sq L hu hsupp]
  have h := abs_mul_integral_bilinear_le_integral_bilinear_fderiv_apply_add (μ := μ)
    (B := (ContinuousLinearMap.mul ℝ ℝ).bilinearComp L L) (fun y z ↦ by simp [mul_comm])
    (fun y ↦ by simpa using mul_self_nonneg (L y)) hv (hu.of_le (by norm_num)) hsupp ω
  simpa only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply', ← sq] using h

end Uncertainty

variable [FiniteDimensional ℝ V]

/-- Exchanging the two differentiation directions does not change the integral of a bilinear form
evaluated on two directional derivatives of a compactly supported `C²` map into a
finite-dimensional space. -/
theorem integral_bilinForm_fderiv_apply_comm (b : LinearMap.BilinForm ℝ V) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, b (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      ∫ x, b (fderiv ℝ u x w) (fderiv ℝ u x v) ∂μ := by
  simpa using integral_bilinear_fderiv_apply_comm b.toContinuousBilinearMap hu hsupp v w

/-- The integral of an alternating bilinear form evaluated on two directional derivatives of a
compactly supported `C²` map vanishes: the pullback of a constant two-form along a compactly
supported map integrates to zero. -/
theorem integral_bilinForm_fderiv_apply_eq_zero_of_isAlt {b : LinearMap.BilinForm ℝ V}
    (hb : b.IsAlt) (hu : ContDiff ℝ 2 u) (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, b (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ = 0 := by
  have hneg : ∀ x : E, b (fderiv ℝ u x w) (fderiv ℝ u x v) =
      -b (fderiv ℝ u x v) (fderiv ℝ u x w) := fun x ↦ (hb.neg_eq _ _).symm
  have h := integral_bilinForm_fderiv_apply_comm (μ := μ) b hu hsupp v w
  simp only [hneg, integral_neg] at h
  linarith

section Lipschitz

open Filter Set
open scoped NNReal Topology

variable {g : E → ℝ} {L : ℝ≥0}

omit [FiniteDimensional ℝ E] in
/-- The directional derivative of a Lipschitz function `g` with compact support lies in every
`Lq`, being bounded with compact support. -/
theorem _root_.LipschitzWith.memLp_lineDeriv_of_hasCompactSupport {q : ENNReal} {ν : Measure E}
    [IsFiniteMeasureOnCompacts ν] (hg : LipschitzWith L g) (hgc : HasCompactSupport g) (v : E) :
    MemLp (fun x => lineDeriv ℝ g x v) q ν := by
  have hdgc : HasCompactSupport fun x => lineDeriv ℝ g x v :=
    hgc.mono' fun x hx => by_contra fun h => hx (lineDeriv_of_notMem_tsupport h v)
  exact hdgc.memLp_of_bound (aestronglyMeasurable_lineDeriv hg.continuous ν) (L * ‖v‖)
    (.of_forall fun _ => norm_lineDeriv_le_of_lipschitz ℝ hg)

/-- **Integration by parts against a Lipschitz function.** For an open set `U`, a function `f`
that is `C¹` on `U`, and a Lipschitz function `g` with compact support in `U`,
`∫ (∂_v g) f = -∫ g (∂_v f)`, where `∂_v g = lineDeriv ℝ g · v` exists almost everywhere by
Rademacher's theorem. Nothing is assumed about `f` outside `U`: a cutoff equal to one near
`tsupport g` reduces this to Mathlib's integration by parts for two Lipschitz functions,
`LipschitzWith.integral_lineDeriv_mul_eq`. -/
theorem integral_lineDeriv_mul_eq_neg_of_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hg : LipschitzWith L g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ U) (v : E) :
    ∫ x, lineDeriv ℝ g x v * f x ∂μ = -∫ x, g x * fderiv ℝ f x v ∂μ := by
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := hgc.exists_contDiff_cutoff_eventuallyEq_one hU hgs
  set F : E → ℝ := fun x => χ x * f x
  -- `F = χ f` is `C¹` on the whole space: near a point outside `U` it vanishes identically.
  have hF : ContDiff ℝ 1 F := by
    simpa only [F, smul_eq_mul] using
      hf.contDiff_smul_of_tsupport_subset hU (hχ.of_le (by simp)).contDiffOn hχs
  obtain ⟨C, hFC⟩ : ∃ C, LipschitzWith C F :=
    hF.lipschitzWith_of_hasCompactSupport hχc.mul_right one_ne_zero
  have hibp := hFC.integral_lineDeriv_mul_eq (μ := μ) hg hgc v
  -- On a neighbourhood of each point of `tsupport g` the cutoff is one, so `F` agrees with `f`.
  have hnear : ∀ x ∈ tsupport g, F =ᶠ[𝓝 x] f := fun x hx => by
    filter_upwards [hχ1 x hx] with y hy
    simp [F, hy]
  have h1 : ∀ x, lineDeriv ℝ F x v * g x = g x * fderiv ℝ f x v := fun x => by
    by_cases hx : x ∈ tsupport g
    · have hfx : DifferentiableAt ℝ f x :=
        (hf.differentiableOn one_ne_zero x (hgs hx)).differentiableAt (hU.mem_nhds (hgs hx))
      rw [(hnear x hx).lineDeriv_eq, hfx.lineDeriv_eq_fderiv, mul_comm]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have h2 : ∀ x, lineDeriv ℝ g x (-v) * F x = -(lineDeriv ℝ g x v * f x) := fun x => by
    rw [lineDeriv_neg]
    by_cases hx : x ∈ tsupport g
    · rw [(hnear x hx).eq_of_nhds]
      ring
    · simp [lineDeriv_of_notMem_tsupport hx]
  simp only [h1, h2, integral_neg] at hibp
  linarith

end Lipschitz

end TauCeti

end

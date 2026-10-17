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

## Integration by parts against a Lipschitz function

For an open set `U`, a function `f` that is `C¹` on `U`, and a Lipschitz function `g` with
compact support in `U`, the identity `∫ (∂_v g) f = -∫ g (∂_v f)` holds, with `∂_v g` the
directional derivative of `g`, which exists almost everywhere by Rademacher's theorem. A cutoff
equal to one near the support of `g` reduces it to Mathlib's integration by parts for two
Lipschitz functions. This is the smooth case of integration by parts in `W^{1,p}` against a
Lipschitz test function.

## Main results

* `TauCeti.integral_bilinear_fderiv_apply_comm`: the integral of `B (∂_v u) (∂_w u)` is symmetric
  in the two directions, and `TauCeti.integral_bilinForm_fderiv_apply_comm` its form for a
  bilinear form on a finite-dimensional space.
* `TauCeti.integral_bilinForm_fderiv_apply_eq_zero_of_isAlt`: for an alternating bilinear form
  the integral vanishes.
* `TauCeti.integral_lineDeriv_mul_eq_neg_of_contDiffOn`: integration by parts between a function
  `C¹` on an open set and a Lipschitz function with compact support in it.

## References

* Sébastien Gouëzel, `Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`, theorem
  `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`: the integration by parts in a single
  direction that every proof here is built on.
-/

public section

namespace TauCeti

open MeasureTheory

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → V}

/-- Exchanging the two differentiation directions does not change the integral of a continuous
bilinear pairing of two directional derivatives of a compactly supported `C²` map. -/
theorem integral_bilinear_fderiv_apply_comm (B : V →L[ℝ] V →L[ℝ] W) (hu : ContDiff ℝ 2 u)
    (hsupp : HasCompactSupport u) (v w : E) :
    ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      ∫ x, B (fderiv ℝ u x w) (fderiv ℝ u x v) ∂μ := by
  have hu' : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hcdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hcd2u : Continuous (fderiv ℝ (fderiv ℝ u)) := hu'.continuous_fderiv (by norm_num)
  -- a bilinear pairing whose right factor has compact support has compact support
  have hcs : ∀ F G : E → V, HasCompactSupport G → HasCompactSupport fun x ↦ B (F x) (G x) :=
    fun F G hG ↦ hG.mono fun x hx ↦ by
      simp only [Function.mem_support] at hx ⊢
      contrapose! hx
      simp [hx]
  -- the derivative in the direction `w` of the derivative of `u` in the direction `v`
  have hsnd : ∀ (v w : E) (x : E),
      fderiv ℝ (fun y ↦ fderiv ℝ u y v) x w = fderiv ℝ (fderiv ℝ u) x w v := by
    intro v w x
    rw [fderiv_clm_apply (hu'.differentiable (by norm_num) x) (differentiableAt_const v)]
    simp
  -- integration by parts in the direction `w`, for each ordered pair of directions
  have step : ∀ v w : E, ∫ x, B (fderiv ℝ u x v) (fderiv ℝ u x w) ∂μ =
      -∫ x, B (fderiv ℝ (fderiv ℝ u) x w v) (u x) ∂μ := by
    intro v w
    have hcv : Continuous fun x ↦ fderiv ℝ u x v := hcdu.clm_apply continuous_const
    have h1 : Integrable
        (fun x ↦ B (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x w) (u x)) μ := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (hcs _ _ hsupp)
      simp only [hsnd v w]
      exact (B.continuous.comp ((hcd2u.clm_apply continuous_const).clm_apply
        continuous_const)).clm_apply hu.continuous
    have h2 : Integrable (fun x ↦ B (fderiv ℝ u x v) (fderiv ℝ u x w)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hcv).clm_apply (hcdu.clm_apply continuous_const))
        (hcs _ _ (hsupp.fderiv_apply (𝕜 := ℝ) w))
    have h3 : Integrable (fun x ↦ B (fderiv ℝ u x v) (u x)) μ :=
      Continuous.integrable_of_hasCompactSupport
        ((B.continuous.comp hcv).clm_apply hu.continuous) (hcs _ _ hsupp)
    have := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ) (B := B)
      (f := fun x ↦ fderiv ℝ u x v) (g := u) (v := w) h1 h2 h3
      (fun x _ ↦ ((hu'.differentiable (by norm_num) x).clm_apply
        (differentiableAt_const v)))
      (fun x _ ↦ hu.differentiable (by norm_num) x)
    simpa only [hsnd v w] using this
  have hsymm : ∀ x : E, fderiv ℝ (fderiv ℝ u) x w v = fderiv ℝ (fderiv ℝ u) x v w :=
    fun x ↦ (hu.contDiffAt.isSymmSndFDerivAt (by simp)).eq w v
  rw [step v w, step w v]
  simp only [hsymm]

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
      -b (fderiv ℝ u x v) (fderiv ℝ u x w) := fun x ↦ (hb.neg _ _).symm
  have h := integral_bilinForm_fderiv_apply_comm (μ := μ) b hu hsupp v w
  simp only [hneg, integral_neg] at h
  linarith

section Lipschitz

open Filter Set
open scoped NNReal Topology

variable {g : E → ℝ} {L : ℝ≥0}

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
  obtain ⟨χ, hχ, -, hχ1, hχc, hχs⟩ := hgc.exists_contDiff_cutoff hU hgs
  set F : E → ℝ := fun x => χ x * f x
  -- `F = χ f` is `C¹` on the whole space: near a point outside `U` it vanishes identically.
  have hF : ContDiff ℝ 1 F := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.mul (hf.contDiffAt (hU.mem_nhds hx))
    · have h0 : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hχs h)
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (h0.mono fun y hy => by simp [F, hy])
  obtain ⟨C, hFC⟩ : ∃ C, LipschitzWith C F :=
    hF.lipschitzWith_of_hasCompactSupport hχc.mul_right one_ne_zero
  have hibp := hFC.integral_lineDeriv_mul_eq (μ := μ) hg hgc v
  -- On a neighbourhood of each point of `tsupport g` the cutoff is one, so `F` agrees with `f`.
  have hnear : ∀ x ∈ tsupport g, F =ᶠ[𝓝 x] f := fun x hx => by
    filter_upwards [isOpen_interior.mem_nhds (hχ1 hx)] with y hy
    have hy1 : y ∈ χ ⁻¹' {1} := interior_subset hy
    have hχy : χ y = 1 := Set.mem_singleton_iff.mp (Set.mem_preimage.mp hy1)
    simp [F, hχy]
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

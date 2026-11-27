/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.LinearAlgebra.Trace
import TauCeti.Analysis.Calculus.Divergence
import TauCeti.Analysis.Calculus.FDeriv.Integral
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Topology.Algebra.Module.Trace

/-!
# Compactly supported divergence on a vector space

The divergence of a globally `C¹`, compactly supported vector field is integrable and has zero
integral over the whole space: each summand is a directional derivative of a compactly supported
component, so it integrates to zero by
`TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable`.

It also localizes the divergence integral over a set of unique differentiability to a box
containing the part of the support inside that set, which the half-space and quadrant divergence
theorems share, and provides the compactly supported rescaled-field integral identity
`TauCeti.integral_mul_trace_fderiv_comp_mul_eq_neg`.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- Let `f` be `C¹` on a measurable set `s` of unique differentiability, and let the part of its
support inside `s` lie in a box `Icc a b ⊆ s`. Then its divergence within `s` is integrable on the
box and on `s`, and its integrals over both agree. -/
theorem _root_.ContDiffOn.integrableOn_divergence_and_setIntegral_eq_Icc {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)} {s : Set (Fin (n + 1) → ℝ)}
    (hf : ContDiffOn ℝ 1 f s) (hs : UniqueDiffOn ℝ s) (hsm : MeasurableSet s)
    {a b : Fin (n + 1) → ℝ} (hab : Icc a b ⊆ s)
    (hsupp : ∀ x ∈ s, x ∈ tsupport f → x ∈ Icc a b) :
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1),
      fderivWithin ℝ f s x (Pi.single i 1) i) (Icc a b) ∧
    IntegrableOn (fun x ↦ ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i) s ∧
    (∫ x in s, ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i) =
      ∫ x in Icc a b, ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i := by
  let D (x : Fin (n + 1) → ℝ) := ∑ i : Fin (n + 1), fderivWithin ℝ f s x (Pi.single i 1) i
  have hDzero {x : Fin (n + 1) → ℝ} (hx : x ∈ s) (hk : x ∉ Icc a b) : D x = 0 := by
    have hn : x ∉ tsupport f := fun hx' ↦ hk (hsupp x hx hx')
    have hd := (HasFDerivWithinAt.of_notMem_tsupport ℝ (s := s) hn).fderivWithin (hs x hx)
    simp [D, hd]
  have hDc : ContinuousOn D s := by
    apply continuousOn_finsetSum
    intro i _
    exact (continuous_apply i).comp_continuousOn
      ((hf.continuousOn_fderivWithin hs (by simp)).clm_apply continuousOn_const)
  have hDi : IntegrableOn D (Icc a b) := (hDc.mono hab).integrableOn_compact isCompact_Icc
  exact ⟨hDi, hDi.of_forall_sdiff_eq_zero hsm fun x hx ↦ hDzero hx.1 hx.2,
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hsm hab fun x hx ↦ hDzero hx.1 hx.2⟩

/-- The divergence of a globally `C¹`, compactly supported coordinate vector field, with
components in a real normed space `F`, is integrable and has zero integral on the whole space. -/
theorem integral_divergence_eq_zero {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin (n + 1) → ℝ) → (Fin (n + 1) → F)}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) ∧
      (∫ x, ∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) i) = 0 := by
  -- Each summand is continuous with compact support, hence integrable.
  have hint (i : Fin (n + 1)) : Integrable fun x ↦ fderiv ℝ f x (Pi.single i 1) i :=
    ((continuous_apply i).comp ((hf.continuous_fderiv (by simp)).clm_apply continuous_const))
      |>.integrable_of_hasCompactSupport ((hc.fderiv_apply ℝ _).comp_left rfl)
  refine ⟨integrable_finsetSum _ fun i _ ↦ hint i, ?_⟩
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  -- The `i`-th summand is the derivative of the `i`-th component `x ↦ f x i` in direction
  -- `Pi.single i 1`, whose integral vanishes.
  have h := TauCeti.integral_apply_eq_zero_of_hasFDerivAt_off_countable (μ := volume)
    (D := fun x ↦ (ContinuousLinearMap.proj i).comp (fderiv ℝ f x)) countable_empty
    ((continuous_apply i).comp hf.continuous) (hc.comp_left rfl)
    (fun x _ ↦ hasFDerivAt_pi'.1 (hf.differentiable one_ne_zero x).hasFDerivAt i) (Pi.single i 1)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h

end MeasureTheory

namespace TauCeti

/-- For any fixed parameter `u : ℝ`, when `A` is `C¹` and vanishes outside a compact set `K`, and
`a` is `C¹`, integrating the rescaled divergence piece `a y * div_y (A · (a y * u))` against an
additive Haar measure equals minus the integral of the `u`-derivative term, since their sum is the
divergence of the compactly supported `C¹` field `y ↦ a y • A y (a y * u)`. -/
theorem integral_mul_trace_fderiv_comp_mul_eq_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E} [μ.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) {A : E → ℝ → E} (hA : ContDiff ℝ 1 (Function.uncurry A))
    (hA0 : ∀ {y : E}, y ∉ K → ∀ t, A y t = 0) {a : E → ℝ} (ha : ContDiff ℝ 1 a) (u : ℝ) :
    (∫ y : E, a y * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) ∂μ) =
      -∫ y : E, deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u ∂μ := by
  let W : E → E := fun y => a y • A y (a y * u)
  have hW : ContDiff ℝ 1 W :=
    ha.smul (hA.comp (contDiff_id.prodMk (ha.mul contDiff_const)))
  have hWc : HasCompactSupport W := .of_support_subset_isCompact hK fun y hy => by
    by_contra hyK
    exact hy (by simp [W, hA0 hyK])
  have hW_int : MeasureTheory.Integrable (fderiv ℝ W) μ :=
    (hW.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (hWc.fderiv (𝕜 := ℝ))
  have hW0 : ∫ y : E, LinearMap.trace ℝ E (fderiv ℝ W y : E →ₗ[ℝ] E) ∂μ = 0 := by
    simp_rw [← traceCLM_apply]
    rw [(traceCLM ℝ E).integral_comp_comm hW_int,
      integral_fderiv_eq_zero_of_hasCompactSupport hW hWc, map_zero]
  obtain ⟨hP1c, hP2c⟩ := continuous_trace_fderiv_comp_mul hA ha
  have hi1 : MeasureTheory.Integrable (fun y : E => a y * LinearMap.trace ℝ E
      (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E)) μ :=
    (hP1c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by
        by_contra hyK
        exact hy (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hyK).1)
  have hi2 : MeasureTheory.Integrable (fun y : E =>
      deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u) μ :=
    (hP2c.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (.of_support_subset_isCompact hK fun y hy => by
        by_contra hyK
        exact hy (trace_fderiv_comp_mul_eq_zero_of_notMem hK.isClosed hA0 a u hyK).2)
  have hsum : (∫ y : E, a y * LinearMap.trace ℝ E
        (fderiv ℝ (fun z : E => A z (a y * u)) y : E →ₗ[ℝ] E) ∂μ) +
      (∫ y : E, deriv (fun s : ℝ => fderiv ℝ a y (s • A y (a y * s))) u ∂μ) =
      ∫ y : E, LinearMap.trace ℝ E (fderiv ℝ W y : E →ₗ[ℝ] E) ∂μ := by
    rw [← MeasureTheory.integral_add hi1 hi2]
    exact MeasureTheory.integral_congr_ae (.of_forall fun y =>
      (trace_fderiv_smul_comp_mul (hA.differentiable one_ne_zero (y, a y * u))
        (ha.differentiable one_ne_zero y)).symm)
  linarith

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
public import TauCeti.Geometry.Manifold.Riemannian.Killing.Flow
public import TauCeti.Geometry.Manifold.Flow.FlowOut

/-!
# Potential translation along unit-gradient flows

A complete unit gradient translates its potential, and a Killing gradient preserves level pairings.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)] {f : M → ℝ}

/-- A unit gradient translates its potential at unit speed along its complete `C¹` flow. -/
theorem apply_globalFlow_mgradient_eq_add
    (hv : ContMDiff I I.tangent 1 (T% (mgradient I f)))
    (hc : IsCompleteVectorField (mgradient I f))
    (hunit : ∀ x, inner ℝ (mgradient I f x) (mgradient I f x) = 1)
    (t : ℝ) (x : M) :
    f (globalFlow (mgradient I f) hv hc t x) = f x + t := by
  let φ := globalFlow (mgradient I f) hv hc
  have hd (s : ℝ) : HasDerivAt (fun r ↦ f (φ r x) - r) 0 s := by
    have hf : MDifferentiableAt I 𝓘(ℝ) f (φ s x) :=
      mdifferentiableAt_of_mvfderiv_apply_ne_zero
        (v := mgradient I f (φ s x)) (by rw [mvfderiv_apply_mgradient, hunit]; exact one_ne_zero)
    have h := hasDerivAt_comp_curve hf (isMIntegralCurve_globalFlow hv hc x s)
    rw [mvfderiv_apply_mgradient, hunit] at h
    have h' := h.sub (hasDerivAt_id s)
    -- A scalar derivative subtracts in ℝ; the identity derivative is one.
    change HasDerivAt (fun r ↦ f (φ r x) - r) (1 - 1) s at h'
    simpa only [sub_self] using h'
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa only [φ, Flow.map_zero_apply, sub_zero] using (sub_eq_iff_eq_add.mp hconst)

end Flow

section FlowMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] {f : M → ℝ}

/-- The flow-out of a level by a complete Killing unit gradient has the product metric. -/
theorem inner_mfderiv_globalFlow_mgradient_comp
    {F K S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ F K} [TopologicalSpace S] [ChartedSpace K S]
    {ι : S → M} (hc : IsCompleteVectorField (mgradient I f))
    (hkill : IsKillingField I (mgradient I f))
    (hunit : ∀ x, inner ℝ (mgradient I f x) (mgradient I f x) = 1)
    (p : ℝ × S) (hι : MDifferentiableAt J I ι p.2)
    {c : ℝ} (hlevel : f ∘ ι =ᶠ[𝓝 p.2] fun _ ↦ c)
    (a b : ℝ) (v w : TangentSpace J p.2) :
    let φ := globalFlow (mgradient I f) (hkill.contMDiff.of_le (by simp)) hc
    inner ℝ
        (mfderiv (𝓘(ℝ).prod J) I (fun z : ℝ × S ↦ φ z.1 (ι z.2)) p
          ((tangentSpaceProdEquiv p).symm (a, v)))
        (mfderiv (𝓘(ℝ).prod J) I (fun z : ℝ × S ↦ φ z.1 (ι z.2)) p
          ((tangentSpaceProdEquiv p).symm (b, w))) =
      a * b + inner ℝ (mfderiv J I ι p.2 v) (mfderiv J I ι p.2 w) := by
  dsimp only
  rw [mfderiv_globalFlow_comp_apply hc _ p hι, mfderiv_globalFlow_comp_apply hc _ p hι]
  rw [← flowOf_eq_globalFlow, hkill.inner_mfderiv_flowOf (hc.mem_flowDomain _ _)]
  have hv := inner_mgradient_mfderiv_eq_zero_of_eventuallyEq_const
    (I := I) (J := J) (ι := ι) p.2 v hlevel
  have hw := inner_mgradient_mfderiv_eq_zero_of_eventuallyEq_const
    (I := I) (J := J) (ι := ι) p.2 w hlevel
  have hv' : inner ℝ (mfderiv J I ι p.2 v) (mgradient I f (ι p.2)) = 0 := by
    rw [real_inner_comm]
    exact hv
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hunit, hv', hw]
  ring


end FlowMetric

end TauCeti.Manifold

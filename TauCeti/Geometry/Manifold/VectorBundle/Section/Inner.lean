/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Pointwise inner products of sections of Riemannian bundles

Let `V` be a real vector bundle over a manifold `M` whose fibres carry inner products. Two sections
`s` and `t` of `V` have a pointwise inner product `x ↦ ⟪s x, t x⟫`. If one of them has compact
support, so does this function, and for a continuous Riemannian bundle it is continuous, hence
integrable for every measure that is finite on compact sets.

For a locally finite measure that is positive on open sets of a Hausdorff σ-compact manifold, the
pairing `∫ ⟪s, u⟫ dμ` with compactly supported smooth sections `s` separates smooth sections
(`ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero`): pairing `u` with `φ u` for compactly
supported smooth functions `φ` shows that the continuous function `⟪u, u⟫` vanishes.

## Main results

* `ContMDiffSection.integrable_inner`: the pointwise inner product of two sections, one of which
  has compact support, is integrable.
* `ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero`: the fundamental lemma for sections,
  a smooth section pairing to zero with every compactly supported smooth section vanishes.
-/

public section

open MeasureTheory Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] {n : ℕ∞ω}

omit [VectorBundle ℝ F V] in
/-- The pointwise inner product of two sections, one of which has compact support, has compact
support. -/
theorem hasCompactSupport_inner {s t : Cₛ^n⟮I; F, V⟯}
    (h : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    HasCompactSupport fun x ↦ ⟪s x, t x⟫ := by
  rcases h with h | h
  · exact .intro' h s.isClosed_tsupport fun x hx ↦ by simp [s.eq_zero_of_notMem_tsupport hx]
  · exact .intro' h t.isClosed_tsupport fun x hx ↦ by simp [t.eq_zero_of_notMem_tsupport hx]

variable [IsContinuousRiemannianBundle F V]

/-- The pointwise inner product of two continuous sections of a continuous Riemannian bundle is
continuous. -/
theorem continuous_inner (s t : Cₛ^n⟮I; F, V⟯) : Continuous fun x ↦ ⟪s x, t x⟫ :=
  s.contMDiff.continuous.inner_bundle t.contMDiff.continuous

/-- The pointwise inner product of two sections of a continuous Riemannian bundle, one of which has
compact support, is integrable for a measure that is finite on compact sets. -/
theorem integrable_inner [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M}
    [IsFiniteMeasureOnCompacts μ]
    {s t : Cₛ^n⟮I; F, V⟯} (h : IsCompact s.tsupport ∨ IsCompact t.tsupport) :
    Integrable (fun x ↦ ⟪s x, t x⟫) μ :=
  (continuous_inner s t).integrable_of_hasCompactSupport (hasCompactSupport_inner h)

/-- **The fundamental lemma for sections.** For a locally finite measure that is positive on open
sets of a Hausdorff σ-compact manifold, a smooth section of a continuous Riemannian bundle that
pairs to zero with every compactly supported smooth section vanishes. -/
theorem eq_zero_of_forall_integral_inner_eq_zero [MeasurableSpace M] [FiniteDimensional ℝ E]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [BorelSpace M] {μ : Measure M}
    [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure] {u : Cₛ^∞⟮I; F, V⟯}
    (h : ∀ s : Cₛ^∞⟮I; F, V⟯, IsCompact s.tsupport → ∫ x, ⟪s x, u x⟫ ∂μ = 0) : u = 0 := by
  have hcont := continuous_inner u u
  -- The continuous function `⟪u, u⟫` has zero integral against every test function `φ`, since
  -- this integral is the pairing of `u` with the compactly supported section `φ u`.
  have hae : ∀ᵐ x ∂μ, ⟪u x, u x⟫ = 0 := by
    refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
      fun φ hφ hφc ↦ ?_
    let ψ : C^∞⟮I, M; ℝ⟯ := ⟨φ, hφ⟩
    have hc := smul_function_mem_compactlySupported_of_hasCompactSupport ψ hφc u
    rw [← h _ (mem_compactlySupported.1 hc)]
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp only [smul_apply, real_inner_smul_left, smul_eq_mul]
    simp only [ψ, ContMDiffMap.coeFn_mk]
  have hu := (hcont.ae_eq_iff_eq μ continuous_const).1 hae
  exact ext fun x ↦ inner_self_eq_zero.1 (congr_fun hu x)

end ContMDiffSection

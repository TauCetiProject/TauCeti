/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Pointwise inner products of sections of Riemannian bundles

Let `V` be a real vector bundle over a manifold `M` whose fibres carry inner products. Two sections
`s` and `t` of `V` have a pointwise inner product `x ↦ ⟪s x, t x⟫`. If one of them has compact
support, so does this function, and for a continuous Riemannian bundle it is continuous, hence
integrable for every measure that is finite on compact sets. For a `C^n` Riemannian bundle, pairing
with a fixed `C^n` section `τ` is a map `t ↦ ⟪t, τ⟫` from `C^n` sections to `C^n` functions, linear
over `C^n(M)` (`ContMDiffSection.innerSection`).

For a locally finite measure that is positive on open sets of a Hausdorff σ-compact manifold, the
pairing `∫ ⟪s, u⟫ dμ` with compactly supported smooth sections `s` separates smooth sections
(`ContMDiffSection.eq_zero_of_forall_integral_inner_eq_zero`): pairing `u` with `φ u` for compactly
supported smooth functions `φ` shows that the continuous function `⟪u, u⟫` vanishes.

## Main results

* `ContMDiffSection.innerSection`: pairing with a fixed section, linear over the smooth functions.
* `ContMDiffSection.integrable_inner`: the pointwise inner product of two sections, one of which
  has compact support, is integrable; `ContMDiff.integrable_inner_bundle` is its form for sections
  given as functions.
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

section InnerSection

variable [IsContMDiffRiemannianBundle I n F V]

/-- Pairing with a fixed `C^n` section `τ` of a `C^n` Riemannian bundle, `t ↦ ⟪t, τ⟫`, as a map
from `C^n` sections to `C^n` functions, linear over the `C^n` functions. -/
def innerSection (τ : Cₛ^n⟮I; F, V⟯) : Cₛ^n⟮I; F, V⟯ →ₗ[C^n⟮I, M; ℝ⟯] C^n⟮I, M; ℝ⟯ where
  toFun t := ⟨fun x ↦ ⟪t x, τ x⟫, t.contMDiff.inner_bundle τ.contMDiff⟩
  -- On the right, the functions built by the anonymous constructor elaborate as subtype elements,
  -- which `ContMDiffMap.coe_add` and `ContMDiffMap.coe_mul` do not match, so the pointwise sum and
  -- product of the two sides are identified by unfolding.
  map_add' t₁ t₂ := by
    ext x
    simp only [coe_add, Pi.add_apply, ContMDiffMap.coeFn_mk, inner_add_left]
    rfl
  map_smul' g t := by
    ext x
    simp only [smul_apply, ContMDiffMap.coeFn_mk, RingHom.id_apply, real_inner_smul_left]
    rfl

@[simp]
theorem innerSection_apply (τ t : Cₛ^n⟮I; F, V⟯) (x : M) : innerSection τ t x = ⟪t x, τ x⟫ :=
  (rfl)

end InnerSection

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

/-- The pointwise inner product of two `C^n` sections of a continuous Riemannian bundle, given as
functions, one of which has compact support, is integrable for a measure that is finite on compact
sets. This is `ContMDiffSection.integrable_inner` for sections that are not bundled. -/
theorem _root_.ContMDiff.integrable_inner_bundle [MeasurableSpace M] [OpensMeasurableSpace M]
    {μ : Measure M} [IsFiniteMeasureOnCompacts μ] {s t : Π x, V x} (hs : CMDiff n (T% s))
    (ht : CMDiff n (T% t))
    (h : IsCompact (closure {x | s x ≠ 0}) ∨ IsCompact (closure {x | t x ≠ 0})) :
    Integrable (fun x ↦ ⟪s x, t x⟫) μ :=
  integrable_inner (s := ⟨s, hs⟩) (t := ⟨t, ht⟩)
    (by simpa only [tsupport_def, coeFn_mk] using h)

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

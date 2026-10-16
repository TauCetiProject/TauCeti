/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import TauCeti.Analysis.PositiveDefinite.Kernel.Universal
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.ContinuousMap

/-!
# Kernel mean embeddings and universal kernels

Let `k : X → X → 𝕜` be a positive-definite kernel, with canonical feature map
`Φ = hk.kolmogorovFeature` into its Kolmogorov space `H`, so that `⟪Φ x, Φ y⟫ = k x y`. The
*kernel mean embedding* of a measure `μ` on `X` is the Bochner integral `m μ = ∫ Φ dμ ∈ H`. When
`Φ` is integrable for `μ` and `ν`, inner products of mean embeddings are double integrals of the
kernel,

`⟪m μ, m ν⟫ = ∫ y, ∫ x, k x y ∂μ ∂ν`,

so the *kernel energy* of the difference `μ - ν`, the double integral of `k` against
`(μ - ν) ⊗ (μ - ν)`, is the squared norm `‖m μ - m ν‖ ^ 2` and is nonnegative. The distance
`‖m μ - m ν‖` is the maximum mean discrepancy of Gretton et al. Every finite signed measure is such
a difference `μ - ν` of finite measures, so this is the energy of a signed measure against a
positive-definite kernel. The mean embedding is defined for real kernels, whose Kolmogorov space is
a real Hilbert space in which Bochner integrals are taken.

A kernel is *universal* (`TauCeti.IsUniversalKernel`, defined in
`TauCeti.Analysis.PositiveDefinite.Kernel.Universal`) when its continuous sections `k x` span a
dense subspace of `C(X, 𝕜)`. On a compact metrizable space the integrals of the sections against a
finite Borel measure determine the measure, for any universal kernel. For a continuous universal
positive-definite kernel the mean embedding is therefore injective on finite Borel measures, so the
kernel energy of `μ - ν` vanishes only when `μ = ν`. Positive-definiteness, universality and
pointwise positivity of the kernel are distinct conditions; separation of measures needs the first
two. On a finite discrete space every positive-definite kernel is universal, while the constant
kernel `1`, which is positive semidefinite and pointwise positive, is not universal on two points.

These are the energy and separation facts behind the definiteness of Sinkhorn divergences, whose
Gibbs kernels `exp (-c / ε)` are required to be positive definite and universal.

## Main definitions

* `Matrix.PosSemidef.kernelMeanEmbedding`: the kernel mean embedding `∫ Φ dμ` of a measure.

## Main results

* `Matrix.PosSemidef.inner_kernelMeanEmbedding`: `⟪m μ, m ν⟫ = ∫ y, ∫ x, k x y ∂μ ∂ν`.
* `Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`: the kernel energy of `μ - ν` is
  `‖m μ - m ν‖ ^ 2`, hence nonnegative.
* `Matrix.PosSemidef.integrable_kolmogorovFeature`: on a compact space the feature map of a
  continuous kernel is integrable for every finite measure.
* `TauCeti.IsUniversalKernel.ext_of_forall_integral_eq`: on a compact metrizable space, finite
  Borel measures with the same integrals of the sections of a universal kernel are equal.
* `Matrix.PosSemidef.kernelMeanEmbedding_inj`: for a continuous universal positive-definite kernel
  on a compact metrizable space, the mean embedding separates finite Borel measures.

## References

* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*,
  J. Mach. Learn. Res. 13 (2012), 723--773, Lemma 4 and Theorem 5.
* B. K. Sriperumbudur, K. Fukumizu and G. R. G. Lanckriet, *Universality, characteristic kernels
  and RKHS embedding of measures*, J. Mach. Learn. Res. 12 (2011), 2389--2410.
* J. Feydy, T. Séjourné, F.-X. Vialard, S. Amari, A. Trouvé and G. Peyré, *Interpolating between
  optimal transport and MMD using Sinkhorn divergences*, AISTATS 2019, §2 and Theorem 1.
-/

public section

noncomputable section

open MeasureTheory Set Function
open scoped InnerProductSpace ComplexOrder

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [TopologicalSpace X]

/-- **Universal kernels separate finite measures.** On a compact metrizable space, two finite
Borel measures against which every section `k x` of a universal kernel has the same integral are
equal. -/
theorem IsUniversalKernel.ext_of_forall_integral_eq [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] [HasOuterApproxClosed X] {k : X → X → 𝕜} (hk : IsUniversalKernel k)
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x, ∫ y, k x y ∂μ = ∫ y, k x y ∂ν) : μ = ν := by
  -- The two integrals agree on the span of the sections, hence on its closure `C(X, 𝕜)`.
  have hspan : EqOn (fun f : C(X, 𝕜) ↦ ∫ x, f x ∂μ) (fun f ↦ ∫ x, f x ∂ν)
      (Submodule.span 𝕜 {f : C(X, 𝕜) | ∃ x, ⇑f = k x}) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨x, hx⟩ := hf
      simpa only [hx] using h x
    | zero => simp
    | add f g _ _ hf hg =>
      simp only [ContinuousMap.coe_add, Pi.add_apply] at hf hg ⊢
      rw [integral_add (f.integrable μ) (g.integrable μ),
        integral_add (f.integrable ν) (g.integrable ν), hf, hg]
    | smul c f _ hf =>
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, integral_const_mul] at hf ⊢
      rw [hf]
  have htop := Continuous.ext_on ((isUniversalKernel_def k).1 hk)
    continuous_integral_continuousMap continuous_integral_continuousMap hspan
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
  have hf := congrFun htop ⟨fun x ↦ (f x : 𝕜), RCLike.continuous_ofReal.comp f.continuous⟩
  simp only [ContinuousMap.coe_mk, integral_ofReal] at hf
  exact_mod_cast hf

end TauCeti

namespace Matrix.PosSemidef

variable {X : Type*} [MeasurableSpace X]

/-- On a compact space, the canonical feature map of a jointly continuous positive-definite kernel
is integrable for every finite measure, so the mean embedding of a finite measure is a genuine
Bochner integral. -/
theorem integrable_kolmogorovFeature {𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X] [CompactSpace X]
    [OpensMeasurableSpace X] {k : X → X → 𝕜} (hk : Matrix.PosSemidef k)
    (hkc : Continuous (uncurry k)) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable hk.kolmogorovFeature μ :=
  ContinuousMap.integrable ⟨_, hk.continuous_kolmogorovFeature hkc⟩ μ

variable {k : X → X → ℝ}

/-- The *kernel mean embedding* of a measure `μ` for a real positive-definite kernel `k`: the
Bochner integral `∫ Φ dμ` of the canonical feature map `Φ` in the Kolmogorov space of `k`. It is
meaningful when `Φ` is `μ`-integrable, for example for a continuous kernel on a compact space and a
finite measure (`Matrix.PosSemidef.integrable_kolmogorovFeature`). -/
def kernelMeanEmbedding (hk : Matrix.PosSemidef k) (μ : Measure X) : KolmogorovSpace hk :=
  ∫ x, hk.kolmogorovFeature x ∂μ

theorem kernelMeanEmbedding_def (hk : Matrix.PosSemidef k) (μ : Measure X) :
    hk.kernelMeanEmbedding μ = ∫ x, hk.kolmogorovFeature x ∂μ :=
  (rfl)

@[simp]
theorem kernelMeanEmbedding_zero (hk : Matrix.PosSemidef k) :
    hk.kernelMeanEmbedding (0 : Measure X) = 0 := by
  simp [kernelMeanEmbedding]

/-- The mean embedding of a Dirac mass is the feature vector of its point. -/
@[simp]
theorem kernelMeanEmbedding_dirac [MeasurableSingletonClass X] (hk : Matrix.PosSemidef k)
    (x : X) : hk.kernelMeanEmbedding (Measure.dirac x) = hk.kolmogorovFeature x := by
  simp [kernelMeanEmbedding]

@[simp]
theorem kernelMeanEmbedding_smul_measure (hk : Matrix.PosSemidef k) (c : ENNReal)
    (μ : Measure X) : hk.kernelMeanEmbedding (c • μ) = c.toReal • hk.kernelMeanEmbedding μ := by
  simp [kernelMeanEmbedding, integral_smul_measure]

theorem kernelMeanEmbedding_add_measure (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    hk.kernelMeanEmbedding (μ + ν) = hk.kernelMeanEmbedding μ + hk.kernelMeanEmbedding ν :=
  integral_add_measure hμ hν

/-- The inner product of a feature vector with a mean embedding is the integral of the
corresponding kernel section. -/
theorem inner_kolmogorovFeature_kernelMeanEmbedding (hk : Matrix.PosSemidef k) {μ : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (x : X) :
    ⟪hk.kolmogorovFeature x, hk.kernelMeanEmbedding μ⟫_ℝ = ∫ y, k x y ∂μ := by
  rw [kernelMeanEmbedding, ← integral_inner hμ]
  simp only [inner_kolmogorovFeature]

/-- **Inner products of kernel mean embeddings** are double integrals of the kernel:
`⟪m μ, m ν⟫ = ∫ y, ∫ x, k x y ∂μ ∂ν`. -/
theorem inner_kernelMeanEmbedding (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    ⟪hk.kernelMeanEmbedding μ, hk.kernelMeanEmbedding ν⟫_ℝ = ∫ y, ∫ x, k x y ∂μ ∂ν := by
  conv_lhs => rw [kernelMeanEmbedding_def hk ν, ← integral_inner hν]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  dsimp only
  rw [real_inner_comm, inner_kolmogorovFeature_kernelMeanEmbedding hk hμ]
  exact integral_congr_ae (ae_of_all _ fun x ↦ hk.isHermitian.apply x y)

/-- **The kernel energy of a difference of measures.** The squared distance of two kernel mean
embeddings is the double integral of `k` against `(μ - ν) ⊗ (μ - ν)`, written out as
`∫∫ k dμ dμ - 2 ∫∫ k dμ dν + ∫∫ k dν dν`, the two cross terms being equal by symmetry of `k`; in
particular this energy is nonnegative. -/
theorem norm_kernelMeanEmbedding_sub_sq (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    ‖hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν‖ ^ 2 =
      ∫ y, ∫ x, k x y ∂μ ∂μ - 2 * ∫ y, ∫ x, k x y ∂μ ∂ν + ∫ y, ∫ x, k x y ∂ν ∂ν := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_kernelMeanEmbedding hk hμ hμ, inner_kernelMeanEmbedding hk hμ hν,
    inner_kernelMeanEmbedding hk hν hν]

section Universal

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X]

/-- **The mean embedding of a universal kernel is injective.** For a jointly continuous universal
positive-definite kernel on a compact metrizable space, two finite Borel measures have the same
mean embedding exactly when they are equal. -/
theorem kernelMeanEmbedding_inj (hk : Matrix.PosSemidef k) (hkc : Continuous (uncurry k))
    (hku : TauCeti.IsUniversalKernel k) {μ ν : Measure X} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : hk.kernelMeanEmbedding μ = hk.kernelMeanEmbedding ν ↔ μ = ν := by
  refine ⟨fun h ↦ hku.ext_of_forall_integral_eq fun x ↦ ?_, fun h ↦ h ▸ rfl⟩
  rw [← inner_kolmogorovFeature_kernelMeanEmbedding hk (hk.integrable_kolmogorovFeature hkc μ),
    ← inner_kolmogorovFeature_kernelMeanEmbedding hk (hk.integrable_kolmogorovFeature hkc ν), h]

end Universal

end Matrix.PosSemidef

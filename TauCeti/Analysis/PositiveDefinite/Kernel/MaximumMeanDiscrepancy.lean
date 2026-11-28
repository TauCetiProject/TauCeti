/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel.MeanEmbedding
import TauCeti.Analysis.InnerProductSpace.UnitVector

/-!
# The maximum mean discrepancy

Let `k : X → X → ℝ` be a positive-definite kernel with canonical feature map
`Φ = hk.kolmogorovFeature` into its Kolmogorov space `H` and kernel mean embedding
`m μ = ∫ Φ dμ`. The *maximum mean discrepancy* of two measures is the distance of their mean
embeddings, `MMD(μ, ν) = ‖m μ - m ν‖`. It is a pseudometric on measures, and it vanishes exactly
when the two mean embeddings agree. It need not separate probability measures: for the constant
kernel `1` all their mean embeddings coincide.

When `Φ` is integrable for `μ` and `ν`, every `f ∈ H` integrates against `μ` through the
embedding, `⟪f, m μ⟫ = ∫ ⟪f, Φ x⟫ dμ`
(`Matrix.PosSemidef.inner_kernelMeanEmbedding_eq_integral_inner`), so the MMD is the integral
probability metric of the unit ball of `H`:

`MMD(μ, ν) = ⨆ ‖f‖ ≤ 1, (∫ ⟪f, Φ x⟫ dμ - ∫ ⟪f, Φ x⟫ dν)`.

The *witness function* `m μ - m ν` is the function `x ↦ ∫ k x y dμ - ∫ k x y dν`, in the sense
that `⟪Φ x, m μ - m ν⟫ = ∫ k x y dμ - ∫ k x y dν`
(`Matrix.PosSemidef.inner_kolmogorovFeature_kernelMeanEmbedding_sub`), and the supremum is
attained at the normalized witness `MMD(μ, ν)⁻¹ • (m μ - m ν)`. Since `MMD(μ, ν) ^ 2` unfolds to
`‖m μ - m ν‖ ^ 2`, its double integral form `∫∫ k dμ dμ - 2 ∫∫ k dμ dν + ∫∫ k dν dν` is
`Matrix.PosSemidef.norm_kernelMeanEmbedding_sub_sq`.

Without integrability the Bochner integral defining `m μ` is the junk value `0`, so the statements
that relate the MMD to integrals carry `Integrable hk.kolmogorovFeature μ`; the metric properties
need no hypothesis.

## Main definitions

* `Matrix.PosSemidef.mmd`: the maximum mean discrepancy `‖m μ - m ν‖`.

## Main results

* `Matrix.PosSemidef.mmd_eq_dist`: `MMD(μ, ν) = dist (m μ) (m ν)`; hence `mmd_nonneg`,
  `mmd_self`, `mmd_comm`, `mmd_triangle` and `mmd_eq_zero_iff`.
* `Matrix.PosSemidef.mmd_dirac_dirac_sq`: `MMD(δ x, δ y) ^ 2 = k x x - 2 k x y + k y y`.
* `Matrix.PosSemidef.abs_integral_inner_sub_integral_inner_le`: the unit-ball bound
  `|∫ ⟪f, Φ⟫ dμ - ∫ ⟪f, Φ⟫ dν| ≤ ‖f‖ * MMD(μ, ν)`.
* `Matrix.PosSemidef.mmd_eq_iSup_integral_inner_sub`: the MMD is the supremum over the unit ball.
* `Matrix.PosSemidef.integral_inner_inv_mmd_smul_sub`: the normalized witness attains the
  supremum.
* `Matrix.PosSemidef.mmd_eq_iSup`: the integral form of the mean embedding, the unit-ball
  supremum, the witness function and the normalized witness, bundled in one statement.

## References

* A. Berlinet and C. Thomas-Agnan, *Reproducing Kernel Hilbert Spaces in Probability and
  Statistics*, Kluwer, 2004, §4.6, p. 210.
* A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*,
  J. Mach. Learn. Res. 13 (2012), 723--773, Lemmas 4 and 6.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Matrix.PosSemidef

variable {X : Type*} [MeasurableSpace X] {k : X → X → ℝ}

/-- The *maximum mean discrepancy* `‖m μ - m ν‖` of two measures, the distance of their kernel
mean embeddings. It is meaningful when the feature map is integrable for both measures (otherwise
the embedding of that measure is the junk value `0`). -/
def mmd (hk : Matrix.PosSemidef k) (μ ν : Measure X) : ℝ :=
  ‖hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν‖

/-- The defining formula of the MMD. -/
theorem mmd_def (hk : Matrix.PosSemidef k) (μ ν : Measure X) :
    hk.mmd μ ν = ‖hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν‖ :=
  (rfl)

/-! ### Metric properties -/

/-- The MMD is the distance of the mean embeddings in the Kolmogorov space. -/
theorem mmd_eq_dist (hk : Matrix.PosSemidef k) (μ ν : Measure X) :
    hk.mmd μ ν = dist (hk.kernelMeanEmbedding μ) (hk.kernelMeanEmbedding ν) :=
  (dist_eq_norm _ _).symm

/-- The MMD is nonnegative. -/
theorem mmd_nonneg (hk : Matrix.PosSemidef k) (μ ν : Measure X) : 0 ≤ hk.mmd μ ν :=
  norm_nonneg _

/-- The MMD of a measure with itself is `0`. -/
@[simp]
theorem mmd_self (hk : Matrix.PosSemidef k) (μ : Measure X) : hk.mmd μ μ = 0 := by
  simp [mmd]

/-- The MMD is symmetric. -/
theorem mmd_comm (hk : Matrix.PosSemidef k) (μ ν : Measure X) : hk.mmd μ ν = hk.mmd ν μ :=
  norm_sub_rev _ _

/-- The triangle inequality for the MMD. -/
theorem mmd_triangle (hk : Matrix.PosSemidef k) (μ ν ρ : Measure X) :
    hk.mmd μ ρ ≤ hk.mmd μ ν + hk.mmd ν ρ := by
  simpa only [mmd_eq_dist] using dist_triangle _ _ _

/-- The MMD vanishes exactly when the two mean embeddings agree. -/
@[simp]
theorem mmd_eq_zero_iff (hk : Matrix.PosSemidef k) {μ ν : Measure X} :
    hk.mmd μ ν = 0 ↔ hk.kernelMeanEmbedding μ = hk.kernelMeanEmbedding ν := by
  rw [mmd, norm_sub_eq_zero_iff]

/-- The MMD from the zero measure is the norm of the mean embedding. -/
@[simp]
theorem mmd_zero_right (hk : Matrix.PosSemidef k) (μ : Measure X) :
    hk.mmd μ 0 = ‖hk.kernelMeanEmbedding μ‖ := by
  simp [mmd]

/-- The MMD from the zero measure is the norm of the mean embedding. -/
@[simp]
theorem mmd_zero_left (hk : Matrix.PosSemidef k) (ν : Measure X) :
    hk.mmd 0 ν = ‖hk.kernelMeanEmbedding ν‖ := by
  simp [mmd]

/-- Scaling both measures by `c` scales the MMD by `c.toReal`. -/
@[simp]
theorem mmd_smul_measure (hk : Matrix.PosSemidef k) (c : ENNReal) (μ ν : Measure X) :
    hk.mmd (c • μ) (c • ν) = c.toReal * hk.mmd μ ν := by
  simp [mmd, ← smul_sub, norm_smul]

/-! ### Closed forms -/

/-- The MMD of two Dirac masses is the distance of the feature vectors of their points. -/
@[simp]
theorem mmd_dirac_dirac [MeasurableSingletonClass X] (hk : Matrix.PosSemidef k) (x y : X) :
    hk.mmd (Measure.dirac x) (Measure.dirac y) =
      ‖hk.kolmogorovFeature x - hk.kolmogorovFeature y‖ := by
  simp [mmd]

/-- The squared MMD of two Dirac masses: `MMD(δ x, δ y) ^ 2 = k x x - 2 k x y + k y y`. -/
theorem mmd_dirac_dirac_sq [MeasurableSingletonClass X] (hk : Matrix.PosSemidef k) (x y : X) :
    hk.mmd (Measure.dirac x) (Measure.dirac y) ^ 2 = k x x - 2 * k x y + k y y := by
  simp

/-! ### The unit-ball supremum and the witness function -/

/-- **The unit-ball bound.** The integrals of `x ↦ ⟪f, Φ x⟫` against `μ` and `ν` differ by at
most `‖f‖ * MMD(μ, ν)`. -/
theorem abs_integral_inner_sub_integral_inner_le (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν)
    (f : hk.KolmogorovSpace) :
    |∫ x, ⟪f, hk.kolmogorovFeature x⟫_ℝ ∂μ - ∫ x, ⟪f, hk.kolmogorovFeature x⟫_ℝ ∂ν| ≤
      ‖f‖ * hk.mmd μ ν := by
  rw [hk.integral_inner_sub_integral_inner hμ hν]
  exact abs_real_inner_le_norm _ _

/-- **The MMD is an integral probability metric**: it is the supremum, over the closed unit ball
of the Kolmogorov space, of the differences `∫ ⟪f, Φ x⟫ dμ - ∫ ⟪f, Φ x⟫ dν`. -/
theorem mmd_eq_iSup_integral_inner_sub (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    hk.mmd μ ν = ⨆ f : {f : hk.KolmogorovSpace // ‖f‖ ≤ 1},
      (∫ x, ⟪f.val, hk.kolmogorovFeature x⟫_ℝ ∂μ - ∫ x, ⟪f.val, hk.kolmogorovFeature x⟫_ℝ ∂ν) := by
  simp only [hk.integral_inner_sub_integral_inner hμ hν]
  exact TauCeti.norm_eq_iSup_real_inner _

/-- The normalized witness `MMD(μ, ν)⁻¹ • (m μ - m ν)` is a unit vector when the MMD is
nonzero. -/
theorem norm_inv_mmd_smul_sub (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (h : hk.mmd μ ν ≠ 0) :
    ‖(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν)‖ = 1 := by
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (hk.mmd_nonneg μ ν)]
  exact inv_mul_cancel₀ h

/-- **The normalized witness attains the supremum**: integrated against `μ` and `ν`, the
normalized witness `w = MMD(μ, ν)⁻¹ • (m μ - m ν)` gives `∫ ⟪w, Φ⟫ dμ - ∫ ⟪w, Φ⟫ dν = MMD(μ, ν)`.
When the MMD is `0` both sides vanish, since then `w = 0`. -/
theorem integral_inner_inv_mmd_smul_sub (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    ∫ x, ⟪(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν),
        hk.kolmogorovFeature x⟫_ℝ ∂μ -
      ∫ x, ⟪(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν),
        hk.kolmogorovFeature x⟫_ℝ ∂ν = hk.mmd μ ν := by
  rw [hk.integral_inner_sub_integral_inner hμ hν]
  exact TauCeti.real_inner_inv_norm_smul_self _

/-- **The MMD and its witness**: the integral form of the mean embedding, the unit-ball
supremum form of the MMD, the witness function, and, when the MMD is nonzero, the normalized
witness, a unit vector attaining the supremum. -/
theorem mmd_eq_iSup (hk : Matrix.PosSemidef k) {μ ν : Measure X}
    (hμ : Integrable hk.kolmogorovFeature μ) (hν : Integrable hk.kolmogorovFeature ν) :
    (∀ f : hk.KolmogorovSpace,
      ⟪f, hk.kernelMeanEmbedding μ⟫_ℝ = ∫ x, ⟪f, hk.kolmogorovFeature x⟫_ℝ ∂μ) ∧
    hk.mmd μ ν = ⨆ f : {f : hk.KolmogorovSpace // ‖f‖ ≤ 1},
      (∫ x, ⟪f.val, hk.kolmogorovFeature x⟫_ℝ ∂μ - ∫ x, ⟪f.val, hk.kolmogorovFeature x⟫_ℝ ∂ν) ∧
    (∀ x, ⟪hk.kolmogorovFeature x, hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν⟫_ℝ =
      ∫ y, k x y ∂μ - ∫ y, k x y ∂ν) ∧
    (hk.mmd μ ν ≠ 0 →
      ‖(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν)‖ = 1 ∧
      ∫ x, ⟪(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν),
          hk.kolmogorovFeature x⟫_ℝ ∂μ -
        ∫ x, ⟪(hk.mmd μ ν)⁻¹ • (hk.kernelMeanEmbedding μ - hk.kernelMeanEmbedding ν),
          hk.kolmogorovFeature x⟫_ℝ ∂ν = hk.mmd μ ν) :=
  ⟨hk.inner_kernelMeanEmbedding_eq_integral_inner hμ, hk.mmd_eq_iSup_integral_inner_sub hμ hν,
    hk.inner_kolmogorovFeature_kernelMeanEmbedding_sub hμ hν,
    fun h ↦ ⟨hk.norm_inv_mmd_smul_sub h, hk.integral_inner_inv_mmd_smul_sub hμ hν⟩⟩

end Matrix.PosSemidef

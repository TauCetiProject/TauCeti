/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.FourierTransform
public import TauCeti.Analysis.Fourier.Torus.LittlewoodPaley.Basic
public import TauCeti.Analysis.Fourier.Torus.Periodization
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Fourier.PoissonSummation
import TauCeti.Analysis.Fourier.Torus.Convolution
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.MeasureTheory.Function.Lp.CompactConvolution
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The periodic Littlewood–Paley blocks on `Lᵖ` of the torus

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d` and `ψ₀ = φ, ψ₁, ψ₂, …` the
inhomogeneous Littlewood–Paley partition built from it. The periodic Littlewood–Paley block `Δⱼ`
multiplies the `n`-th Fourier coefficient of a function on the torus `𝕋ᵈ = UnitAddTorus d` by
`ψⱼ(n)`; on `L²(𝕋ᵈ)` it is the Fourier multiplier `TauCeti.UnitAddTorus.littlewoodPaleyBlock`.
This file extends the blocks to `Lᵖ(𝕋ᵈ)` for every `1 ≤ p ≤ ∞` and proves that they are bounded
there **uniformly in `j` and `p`**
(`TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_le`). This is the periodic counterpart of
`TemperedDistribution.exists_littlewoodPaleyBlock_eq_and_norm_le` on `ℝᵈ`, and the input for the
periodic Bernstein inequalities and the periodic Besov norms `‖(2^{js} ‖Δⱼ f‖_p)ⱼ‖_{ℓ^q}`.

## The kernel

Since `ψⱼ` has compact support, only finitely many `ψⱼ(n)` are nonzero, and the block is the
convolution with the trigonometric polynomial

`kⱼ = ∑ₙ ψⱼ(n) e_n`

(`TauCeti.UnitAddTorus.littlewoodPaleyKernel`), where `e_n = mFourier n`: convolution with `e_n`
picks out the `n`-th Fourier mode (`UnitAddTorus.mFourier_convolution`), so `kⱼ ⋆ f` is the
trigonometric polynomial `∑ₙ ψⱼ(n) f̂(n) e_n`
(`TauCeti.UnitAddTorus.littlewoodPaleyKernel_convolution`).

The `L¹` norms of the kernels `kⱼ` are bounded uniformly in `j`. By Poisson summation
(`SchwartzMap.tsum_eq_tsum_fourier_span_orthonormalBasis`), `kⱼ` is the periodization of the
kernel `𝓕⁻ ψⱼ` of the block on `ℝᵈ`
(`TauCeti.UnitAddTorus.littlewoodPaleyKernel_eq_periodize`), and periodization does not increase
the `L¹` norm (`UnitAddTorus.lintegral_enorm_periodize_le`). So `‖kⱼ‖_{L¹(𝕋ᵈ)} ≤ ‖𝓕⁻ ψⱼ‖_{L¹(ℝᵈ)}`
(`TauCeti.UnitAddTorus.integral_norm_littlewoodPaleyKernel_le`), and the right side is bounded
uniformly in `j`, since `𝓕⁻ ψ_{j+1}` is an `L¹`-normalised dilate of `𝓕⁻ ψ₁`.

## The blocks on `Lᵖ`

By Young's inequality `‖k ⋆ f‖_p ≤ ‖k‖₁ ‖f‖_p` (`MeasureTheory.eLpNorm_convolution_le`),
convolution with a continuous kernel `k` is a bounded operator on `Lᵖ(𝕋ᵈ)` of norm at most `‖k‖₁`
(`ContinuousMap.convolutionLp`). The block `Δⱼ` is this operator for the kernel `kⱼ`
(`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp`,
`TauCeti.UnitAddTorus.norm_littlewoodPaleyBlockLp_le`). It multiplies the Fourier coefficients by
`ψⱼ(n)` (`TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlockLp`), so for `p = 2` it is the
block on `L²` (`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp_two`).

As in `TauCeti.Analysis.Fourier.Torus.LittlewoodPaley.Basic`, `Lᵖ(𝕋ᵈ)` is taken for the product of
the Haar probability measures on the circle factors.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.2.
* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 3.1 (convolution and Fourier coefficients on the torus) and
  Theorem 3.1.17 (Poisson summation).
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap Set Submodule
open scoped ENNReal Convolution FourierTransform

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- As in `TauCeti.Analysis.Fourier.Torus.LittlewoodPaley.Basic`, work with the product of the Haar
-- probability measures on the circle factors, on which Mathlib's Fourier basis lives.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs AddCircle.haarAddCircle.IsAddHaarMeasure

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-! ### The kernel -/

/-- Only finitely many lattice points lie in the support of `ψⱼ`. -/
theorem finite_support_inhomogeneousLittlewoodPaley_latticePoint (j : ℕ) :
    (Function.support fun n : d → ℤ ↦ φ.inhomogeneousLittlewoodPaley j (latticePoint n)).Finite :=
  (finite_setOf_norm_latticePoint_lt (2 ^ j * φ.rOut)).subset fun n hn ↦ by
    by_contra h
    exact hn (φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm (not_lt.1 h))

private theorem inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem {j : ℕ} {n : d → ℤ}
    (hn : n ∉ (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) :
    φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 := by
  simpa using hn

/-- For any coefficients `c n`, only finitely many of the products `ψⱼ(n) c n` are nonzero, so
they are absolutely summable. -/
theorem summable_norm_inhomogeneousLittlewoodPaley_latticePoint_mul (j : ℕ)
    (c : (d → ℤ) → ℂ) :
    Summable fun n : d → ℤ ↦ ‖(φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n‖ :=
  summable_of_ne_finset_zero
    (s := (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) fun n hn ↦ by
      simp [inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem φ hn]

/-- The kernel of the `j`-th periodic Littlewood–Paley block: the trigonometric polynomial
`kⱼ = ∑ₙ ψⱼ(n) e_n`, a finite sum since `ψⱼ` has compact support. -/
def littlewoodPaleyKernel (j : ℕ) : C(UnitAddTorus d, ℂ) :=
  ∑' n : d → ℤ, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) • mFourier n

/-- The series defining the kernel `kⱼ` has only finitely many nonzero terms. -/
theorem summable_littlewoodPaleyKernel (j : ℕ) :
    Summable fun n : d → ℤ ↦ (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) • mFourier n :=
  .of_norm <| by
    simpa [norm_smul, mFourier_norm] using
      summable_norm_inhomogeneousLittlewoodPaley_latticePoint_mul φ j 1

/-- The values of the kernel `kⱼ = ∑ₙ ψⱼ(n) e_n`. -/
theorem littlewoodPaleyKernel_apply (j : ℕ) (z : UnitAddTorus d) :
    littlewoodPaleyKernel φ j z =
      ∑' n : d → ℤ, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * mFourier n z :=
  (ContinuousMap.evalCLM ℂ z).map_tsum (summable_littlewoodPaleyKernel φ j)

/-- The Fourier coefficients of the kernel `kⱼ` are the values `ψⱼ(n)`. -/
@[simp]
theorem mFourierCoeff_littlewoodPaleyKernel (j : ℕ) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyKernel φ j) n =
      φ.inhomogeneousLittlewoodPaley j (latticePoint n) := by
  have hc : Summable fun n : d → ℤ ↦ ‖(φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ)‖ := by
    simpa using summable_norm_inhomogeneousLittlewoodPaley_latticePoint_mul φ j 1
  have h := mFourierCoeff_tsum_smul_mFourier hc n
  simp only [smul_eq_mul] at h
  rw [← h]
  congr 1 with z
  exact littlewoodPaleyKernel_apply φ j z

/-- **The kernel is a periodization.** The kernel `kⱼ = ∑ₙ ψⱼ(n) e_n` of the `j`-th periodic
Littlewood–Paley block is the periodization `∑_{ℓ ∈ ℤᵈ} 𝓕⁻ ψⱼ (· + ℓ)` of the kernel `𝓕⁻ ψⱼ` of
the `j`-th Littlewood–Paley block on `ℝᵈ`: this is Poisson's summation formula. -/
theorem littlewoodPaleyKernel_eq_periodize (j : ℕ) :
    ⇑(littlewoodPaleyKernel φ j) = periodize fun x ↦
      𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (WithLp.toLp 2 x) := by
  set K : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hFK : 𝓕 (K : EuclideanSpace ℝ d → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq,
      φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  ext z
  obtain ⟨x, rfl⟩ := surjective_coe z
  have h := K.tsum_eq_tsum_fourier_span_orthonormalBasis (EuclideanSpace.basisFun d ℝ)
    (WithLp.toLp 2 x)
  set e := ((EuclideanSpace.basisFun d ℝ).toBasis.zspanEquiv).toEquiv
  rw [← OrthonormalBasis.coe_toBasis, ← e.tsum_eq, ← e.tsum_eq] at h
  simp only [e, LinearEquiv.coe_toEquiv, coe_zspanEquiv_basisFun_apply, hFK] at h
  beta_reduce
  rw [periodize_coe, littlewoodPaleyKernel_apply,
    ← ContDiffBump.coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz]
  convert h.symm using 2
  · refine funext fun n ↦ ?_
    rw [mFourier_coe_apply, EuclideanSpace.inner_eq_star_dotProduct]
    congr 2
    simp [dotProduct, mul_comm]
  · refine funext fun n ↦ congr_arg K ?_
    rw [← WithLp.toLp_add]
    congr 1
    ext i
    simp

/-- **The kernels are bounded in `L¹`.** The `L¹(𝕋ᵈ)` norm of the kernel `kⱼ` is at most the
`L¹(ℝᵈ)` norm of the kernel `𝓕⁻ ψⱼ` of the `j`-th Littlewood–Paley block on `ℝᵈ`. -/
theorem integral_norm_littlewoodPaleyKernel_le (j : ℕ) :
    ∫ z, ‖littlewoodPaleyKernel φ j z‖ ≤
      ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) x‖ := by
  set K : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hK : ⇑K = 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) :=
    φ.coe_fourierInv_inhomogeneousLittlewoodPaleySchwartz j
  rw [← hK]
  have hper := lintegral_enorm_periodize_le
    (K.continuous.comp (PiLp.continuous_toLp 2 _)).aemeasurable
  rw [volume_eq_pi_haarAddCircle] at hper
  simp only [Function.comp_apply] at hper
  rw [(PiLp.volume_preserving_toLp d).lintegral_comp K.continuous.eNorm.measurable] at hper
  rw [integral_norm_eq_lintegral_eNorm (littlewoodPaleyKernel φ j).continuous.aestronglyMeasurable,
    integral_norm_eq_lintegral_eNorm K.continuous.aestronglyMeasurable]
  refine ENNReal.toReal_mono (K.integrable.hasFiniteIntegral.ne) ?_
  rw [littlewoodPaleyKernel_eq_periodize, ← hK]
  -- In this file `volume` on the torus is the product of the local instance
  -- `volume = haarAddCircle` on `UnitAddCircle`, which is the measure in `hper`.
  exact hper

/-- **The kernels are bounded in `L¹` uniformly in `j`.** There is `C`, depending only on `φ`,
with `‖kⱼ‖_{L¹(𝕋ᵈ)} ≤ C` for every `j`. -/
theorem exists_integral_norm_littlewoodPaleyKernel_le :
    ∃ C : ℝ, ∀ j, ∫ z, ‖littlewoodPaleyKernel φ j z‖ ≤ C := by
  obtain ⟨C, hC⟩ := φ.exists_integral_norm_pow_mul_norm_fourierInv_inhomogeneousLittlewoodPaley_le 0
  exact ⟨C, fun j ↦ (integral_norm_littlewoodPaleyKernel_le φ j).trans (by simpa using hC j)⟩

/-! ### Convolution with the kernel -/

/-- **Convolution with the kernel is the Fourier multiplier by `ψⱼ`.** For an integrable `f` on
the torus, `kⱼ ⋆ f` is the trigonometric polynomial `∑ₙ ψⱼ(n) f̂(n) e_n`. -/
theorem littlewoodPaleyKernel_convolution (j : ℕ) {f : UnitAddTorus d → ℂ} (hf : Integrable f) :
    ⇑(littlewoodPaleyKernel φ j) ⋆[lsmul ℂ ℂ] f = fun z ↦
      ∑' n : d → ℤ, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n) •
        mFourier n z := by
  set s := (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset
  have hs (n : d → ℤ) (hn : n ∉ s) : φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 :=
    inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem φ hn
  have hk : ⇑(littlewoodPaleyKernel φ j) =
      fun t ↦ ∑ n ∈ s, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * mFourier n t :=
    funext fun t ↦ by
      rw [littlewoodPaleyKernel_apply, tsum_eq_sum (s := s) fun n hn ↦ by simp [hs n hn]]
  rw [hk, sum_mul_mFourier_convolution s _ hf]
  ext x
  rw [tsum_eq_sum (s := s) fun n hn ↦ by simp [hs n hn]]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [mFourierCoeff, smul_eq_mul, smul_eq_mul]
  ring

/-! ### The blocks on `Lᵖ` -/

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The `j`-th **periodic Littlewood–Paley block on `Lᵖ(𝕋ᵈ)`**, `1 ≤ p ≤ ∞`: convolution with the
kernel `kⱼ = ∑ₙ ψⱼ(n) e_n` (`ContinuousMap.convolutionLp`). It multiplies the `n`-th Fourier
coefficient by `ψⱼ(n)` (`TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlockLp`), and for
`p = 2` it is `TauCeti.UnitAddTorus.littlewoodPaleyBlock`
(`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp_two`). -/
def littlewoodPaleyBlockLp (j : ℕ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  (littlewoodPaleyKernel φ j).convolutionLp volume p

/-- The block `Δⱼ` on `Lᵖ(𝕋ᵈ)` is convolution with the kernel `kⱼ`. -/
theorem coeFn_littlewoodPaleyBlockLp (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    littlewoodPaleyBlockLp φ p j f =ᵐ[volume]
      ⇑(littlewoodPaleyKernel φ j) ⋆[lsmul ℂ ℂ] (f : UnitAddTorus d → ℂ) :=
  (littlewoodPaleyKernel φ j).coeFn_convolutionLp volume f

/-- The block `Δⱼ` on `Lᵖ(𝕋ᵈ)` has operator norm at most `‖kⱼ‖₁`. -/
theorem norm_littlewoodPaleyBlockLp_le (j : ℕ) :
    ‖littlewoodPaleyBlockLp φ p j‖ ≤ ∫ z, ‖littlewoodPaleyKernel φ j z‖ :=
  (littlewoodPaleyKernel φ j).norm_convolutionLp_le volume p

/-- **The periodic Littlewood–Paley blocks are bounded on `Lᵖ` uniformly in `j` and `p`.** There is
`C`, depending only on `φ`, such that for every `1 ≤ p ≤ ∞` and every `j`, the block `Δⱼ` on
`Lᵖ(𝕋ᵈ)` has operator norm at most `C`. -/
theorem exists_norm_littlewoodPaleyBlockLp_le :
    ∃ C : ℝ, ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ), ‖littlewoodPaleyBlockLp φ p j‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_integral_norm_littlewoodPaleyKernel_le φ
  exact ⟨C, fun p _ j ↦ (norm_littlewoodPaleyBlockLp_le φ p j).trans (hC j)⟩

/-- The block `Δⱼ f` of `f ∈ Lᵖ(𝕋ᵈ)` is the trigonometric polynomial `∑ₙ ψⱼ(n) f̂(n) e_n`. -/
theorem littlewoodPaleyBlockLp_ae_eq_tsum (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    littlewoodPaleyBlockLp φ p j f =ᵐ[volume] fun z ↦
      ∑' n : d → ℤ, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n) •
        mFourier n z := by
  rw [← littlewoodPaleyKernel_convolution φ j ((Lp.memLp f).integrable Fact.out)]
  exact coeFn_littlewoodPaleyBlockLp φ p j f

/-- **The block `Δⱼ` on `Lᵖ(𝕋ᵈ)` is the Fourier multiplier by `ψⱼ`:**
`(Δⱼ f)^(n) = ψⱼ(n) f̂(n)`. -/
@[simp]
theorem mFourierCoeff_littlewoodPaleyBlockLp (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyBlockLp φ p j f) n =
      φ.inhomogeneousLittlewoodPaley j (latticePoint n) * mFourierCoeff f n := by
  rw [← mFourierCoeff_tsum_smul_mFourier
    (summable_norm_inhomogeneousLittlewoodPaley_latticePoint_mul φ j (mFourierCoeff f)) n]
  refine integral_congr_ae ?_
  filter_upwards [littlewoodPaleyBlockLp_ae_eq_tsum φ p j f] with z hz
  rw [hz]

/-- **Agreement with the block on `L²`.** For `p = 2`, the block `Δⱼ` on `Lᵖ(𝕋ᵈ)` is the Fourier
multiplier `TauCeti.UnitAddTorus.littlewoodPaleyBlock` on `L²(𝕋ᵈ)`. -/
theorem littlewoodPaleyBlockLp_two (j : ℕ) :
    littlewoodPaleyBlockLp φ 2 j = littlewoodPaleyBlock φ j := by
  ext1 f
  refine mFourierBasis.repr.injective (lp.ext (funext fun n ↦ ?_))
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_littlewoodPaleyBlockLp,
    mFourierCoeff_littlewoodPaleyBlock]

end TauCeti.UnitAddTorus

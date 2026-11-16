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
import TauCeti.Analysis.Convolution.Young
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
import TauCeti.Analysis.Fourier.PoissonSummation
import TauCeti.Analysis.Fourier.Torus.Convolution
import TauCeti.Analysis.Fourier.Torus.Decay
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
convolution with `kⱼ` is a bounded operator on `Lᵖ(𝕋ᵈ)` of norm at most `‖kⱼ‖₁`
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

/-- `ψⱼ` vanishes at the lattice points outside the finite set
`TauCeti.UnitAddTorus.finite_support_inhomogeneousLittlewoodPaley_latticePoint`. -/
theorem inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem {j : ℕ} {n : d → ℤ}
    (hn : n ∉ (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) :
    φ.inhomogeneousLittlewoodPaley j (latticePoint n) = 0 := by
  simpa using hn

/-- The kernel of the `j`-th periodic Littlewood–Paley block: the trigonometric polynomial
`kⱼ = ∑ₙ ψⱼ(n) e_n`, a finite sum since `ψⱼ` has compact support. -/
def littlewoodPaleyKernel (j : ℕ) : C(UnitAddTorus d, ℂ) :=
  ∑' n : d → ℤ, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) • mFourier n

/-- The series defining the kernel `kⱼ` has only finitely many nonzero terms. -/
theorem summable_littlewoodPaleyKernel (j : ℕ) :
    Summable fun n : d → ℤ ↦ (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) • mFourier n :=
  summable_of_ne_finset_zero
    (s := (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) fun n hn ↦ by
      ext z
      simp [inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem φ hn]

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
  have hc : Summable fun n : d → ℤ ↦ ‖(φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ)‖ :=
    summable_of_ne_finset_zero
      (s := (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) fun n hn ↦ by
        simp [inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem φ hn]
  have h := mFourierCoeff_tsum_smul_mFourier hc n
  simp only [smul_eq_mul] at h
  rw [← h]
  congr 1 with z
  exact littlewoodPaleyKernel_apply φ j z

omit [Fintype d] in
private theorem sum_zsmul_basisFun [Fintype d] (n : d → ℤ) :
    ∑ i, n i • EuclideanSpace.basisFun d ℝ i = latticePoint n := by
  classical
  ext j
  simp [Pi.single_apply]

/-- The lattice `ℤᵈ ⊆ EuclideanSpace ℝ d`, indexed by the integer vectors. -/
private def latticeEquiv : (d → ℤ) ≃ span ℤ (range (EuclideanSpace.basisFun d ℝ)) :=
  Equiv.ofBijective
    (fun n ↦ ⟨latticePoint n, (mem_span_range_iff_exists_fun ℤ).2 ⟨n, sum_zsmul_basisFun n⟩⟩)
    ⟨fun n m h ↦ funext fun i ↦ by
      simpa using congr_arg (fun x : span ℤ _ ↦ (x : EuclideanSpace ℝ d) i) h,
     fun ℓ ↦ by
      obtain ⟨n, hn⟩ := (mem_span_range_iff_exists_fun ℤ).1 ℓ.2
      exact ⟨n, Subtype.ext (by simpa [sum_zsmul_basisFun] using hn)⟩⟩

private theorem coe_latticeEquiv (n : d → ℤ) :
    ((latticeEquiv n : _) : EuclideanSpace ℝ d) = latticePoint n :=
  rfl

/-- **The kernel is a periodization.** The kernel `kⱼ = ∑ₙ ψⱼ(n) e_n` of the `j`-th periodic
Littlewood–Paley block is the periodization `∑_{ℓ ∈ ℤᵈ} 𝓕⁻ ψⱼ (· + ℓ)` of the kernel `𝓕⁻ ψⱼ` of
the `j`-th Littlewood–Paley block on `ℝᵈ`: this is Poisson's summation formula. -/
theorem littlewoodPaleyKernel_eq_periodize (j : ℕ) :
    ⇑(littlewoodPaleyKernel φ j) = periodize fun x ↦
      𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (WithLp.toLp 2 x) := by
  set K : SchwartzMap (EuclideanSpace ℝ d) ℂ := 𝓕⁻ (φ.inhomogeneousLittlewoodPaleySchwartz j)
  have hK : ⇑K = 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) := by
    rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  have hFK : 𝓕 (K : EuclideanSpace ℝ d → ℂ) = fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq,
      φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  ext z
  obtain ⟨x, rfl⟩ := surjective_coe z
  have h := K.tsum_eq_tsum_fourier_span_orthonormalBasis (EuclideanSpace.basisFun d ℝ)
    (WithLp.toLp 2 x)
  rw [← latticeEquiv.tsum_eq, ← latticeEquiv.tsum_eq] at h
  simp only [coe_latticeEquiv, hFK] at h
  beta_reduce
  rw [periodize_coe, littlewoodPaleyKernel_apply, ← hK]
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
  have hK : ⇑K = 𝓕⁻ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) := by
    rw [SchwartzMap.fourierInv_coe, φ.coe_inhomogeneousLittlewoodPaleySchwartz]
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
  have hk (t : UnitAddTorus d) : littlewoodPaleyKernel φ j t =
      ∑ n ∈ s, (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * mFourier n t := by
    rw [littlewoodPaleyKernel_apply, tsum_eq_sum (s := s) fun n hn ↦ by simp [hs n hn]]
  ext x
  rw [tsum_eq_sum (s := s) fun n hn ↦ by simp [hs n hn], convolution_def]
  simp_rw [lsmul_apply, hk, Finset.sum_smul]
  rw [integral_finsetSum _ fun n _ ↦ ?_]
  · refine Finset.sum_congr rfl fun n _ ↦ ?_
    have h := congr_fun (mFourier_convolution (μ := volume) n f) x
    simp only [convolution_def, lsmul_apply, smul_eq_mul] at h
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, h]
    -- The remaining integral is the Fourier coefficient `mFourierCoeff f n`.
    change _ = _ * ((∫ t, mFourier (-n) t • f t) * _)
    simp only [smul_eq_mul]
    ring
  · have h1 : Integrable (fun t ↦ mFourier n t * f (x - t)) :=
      (hf.comp_sub_left x).bdd_smul 1 (mFourier n).continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t ↦ (norm_mFourier_apply n t).le)
    refine (h1.const_mul (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ)).congr
      (.of_forall fun t ↦ ?_)
    simp only [smul_eq_mul, mul_assoc]

/-! ### The blocks on `Lᵖ` -/

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Convolution with the kernel `kⱼ` maps `Lᵖ(𝕋ᵈ)` to itself, with
`‖kⱼ ⋆ f‖_p ≤ ‖kⱼ‖₁ ‖f‖_p`. -/
theorem memLp_littlewoodPaleyKernel_convolution (j : ℕ)
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    MemLp (⇑(littlewoodPaleyKernel φ j) ⋆[lsmul ℂ ℂ] (f : UnitAddTorus d → ℂ)) p volume ∧
      eLpNorm (⇑(littlewoodPaleyKernel φ j) ⋆[lsmul ℂ ℂ] (f : UnitAddTorus d → ℂ)) p volume ≤
        ENNReal.ofReal (∫ z, ‖littlewoodPaleyKernel φ j z‖) * eLpNorm f p volume := by
  set k := littlewoodPaleyKernel φ j
  have hL : ‖lsmul ℂ ℂ (E := ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_one.2 opNorm_lsmul_le
  have hk : eLpNorm k 1 volume = ENNReal.ofReal (∫ z, ‖k z‖) := by
    rw [eLpNorm_one_eq_lintegral_eNorm k.continuous.aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_eNorm
      (k.continuous.integrable_of_hasCompactSupport (.of_compactSpace _))]
  have hbound : eLpNorm (⇑k ⋆[lsmul ℂ ℂ] (f : UnitAddTorus d → ℂ)) p volume ≤
      ENNReal.ofReal (∫ z, ‖k z‖) * eLpNorm f p volume :=
    calc _ ≤ ‖lsmul ℂ ℂ (E := ℂ)‖ₑ * eLpNorm k 1 volume * eLpNorm f p volume :=
          eLpNorm_convolution_le _ k.continuous.aestronglyMeasurable
            (Lp.aestronglyMeasurable f) Fact.out
      _ ≤ _ := by
          rw [hk, mul_assoc]
          exact mul_le_of_le_one_left zero_le hL
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)), hbound⟩

/-- The `j`-th **periodic Littlewood–Paley block on `Lᵖ(𝕋ᵈ)`**, `1 ≤ p ≤ ∞`: convolution with the
kernel `kⱼ = ∑ₙ ψⱼ(n) e_n`. It multiplies the `n`-th Fourier coefficient by `ψⱼ(n)`
(`TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlockLp`), and for `p = 2` it is
`TauCeti.UnitAddTorus.littlewoodPaleyBlock` (`TauCeti.UnitAddTorus.littlewoodPaleyBlockLp_two`). -/
def littlewoodPaleyBlockLp (j : ℕ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] Lp ℂ p (volume : Measure (UnitAddTorus d)) :=
  LinearMap.mkContinuous
    { toFun f := (memLp_littlewoodPaleyKernel_convolution φ p j f).1.toLp _
      map_add' f g := by
        have hk := (littlewoodPaleyKernel φ j).continuous
        have hex (h : Lp ℂ p (volume : Measure (UnitAddTorus d))) :=
          (HasCompactSupport.of_compactSpace _).convolutionExists_left (lsmul ℂ ℂ) hk
            ((Lp.memLp h).integrable Fact.out).locallyIntegrable
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ (.of_eq ?_)
        rw [convolution_congr _ (.rfl) (Lp.coeFn_add f g)]
        exact (hex f).distrib_add (hex g)
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ (.of_eq ?_)
        rw [convolution_congr _ (.rfl) (Lp.coeFn_smul c f)]
        exact convolution_smul }
    (∫ z, ‖littlewoodPaleyKernel φ j z‖) fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp]
      rw [Lp.norm_def, ← ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _),
        ← ENNReal.toReal_mul]
      exact ENNReal.toReal_mono (by finiteness) (memLp_littlewoodPaleyKernel_convolution φ p j f).2

/-- The block `Δⱼ` on `Lᵖ(𝕋ᵈ)` is convolution with the kernel `kⱼ`. -/
theorem coeFn_littlewoodPaleyBlockLp (j : ℕ) (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) :
    littlewoodPaleyBlockLp φ p j f =ᵐ[volume]
      ⇑(littlewoodPaleyKernel φ j) ⋆[lsmul ℂ ℂ] (f : UnitAddTorus d → ℂ) :=
  (memLp_littlewoodPaleyKernel_convolution φ p j f).1.coeFn_toLp

/-- The block `Δⱼ` on `Lᵖ(𝕋ᵈ)` has operator norm at most `‖kⱼ‖₁`. -/
theorem norm_littlewoodPaleyBlockLp_le (j : ℕ) :
    ‖littlewoodPaleyBlockLp φ p j‖ ≤ ∫ z, ‖littlewoodPaleyKernel φ j z‖ :=
  LinearMap.mkContinuous_norm_le _ (integral_nonneg fun _ ↦ norm_nonneg _) _

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
  have hc : Summable fun n : d → ℤ ↦
      ‖(φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * mFourierCoeff f n‖ :=
    summable_of_ne_finset_zero
      (s := (finite_support_inhomogeneousLittlewoodPaley_latticePoint φ j).toFinset) fun n hn ↦ by
        simp [inhomogeneousLittlewoodPaley_latticePoint_eq_zero_of_notMem φ hn]
  rw [← mFourierCoeff_tsum_smul_mFourier hc n]
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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.Analysis.Fourier.Torus.SchwartzMultiplier
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The periodic Hölder–Zygmund spaces of non-integer order are the Hölder spaces

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d` and let `𝒞^s(𝕋ᵈ) = B^s_{∞,∞}(𝕋ᵈ)` be the
periodic Hölder–Zygmund space built from it (`TauCeti.UnitAddTorus.MemBesov`), a space of formal
Fourier series `c : ℤᵈ → ℂ`. A function on the torus `𝕋ᵈ = UnitAddTorus d` is read through its
lift `x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d`, the `ℤᵈ`-periodic function whose derivatives and
Hölder seminorms are those of `f`. This file proves that, for `k : ℕ` and `0 < α < 1`,

`𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)` with equivalent norms:

`c ∈ 𝒞^{k+α}(𝕋ᵈ)` exactly when `c` is the coefficient sequence `f̂` of a continuous `f` on the torus
whose lift is `C^k` with `α`-Hölder `k`-th derivative
(`TauCeti.UnitAddTorus.memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith`), and the
norm of `c` bounds the derivatives through order `k` and the Hölder constant of the lift, and
conversely (`exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith` and
`exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`, in the namespace
`TauCeti.UnitAddTorus`). This is the periodic
form of the identification `𝒞^{k+α}(ℝᵈ) = C_b^{k,α}(ℝᵈ)` of
`TauCeti.Analysis.Holder.Zygmund`.

## The argument: transference

The identification is transferred from `ℝᵈ` rather than proved again. Let `σ` be a Schwartz
function on `ℝᵈ`. For a continuous `f` on the torus with lift `F`, convolving `F` with `𝓕⁻ σ`
gives the lift of the absolutely convergent Fourier series `∑ₙ σ(n) f̂(n) eₙ`
(`TauCeti.UnitAddTorus.integral_fourierInv_mul_eq_tsum`): both sides are continuous linear
functionals of `f` for the supremum norm, they agree on the monomials `eₙ`, since
`∫ 𝓕⁻ σ(y) eₙ(x - y) dy = σ(n) eₙ(x)`, and the monomials span a dense subspace of `C(𝕋ᵈ, ℂ)`. So
the Fourier multiplier with symbol `σ`, applied to `F` as a tempered distribution, is the lift of
the periodic multiplier with the same symbol
(`TauCeti.UnitAddTorus.fourierMultiplierCLM_toLpTop_eq_toLpTop`). For the symbols `ψⱼ` of the
Littlewood–Paley partition, the Euclidean blocks `Δⱼ F` are the lifts of the periodic blocks
`Δⱼ f̂`, which have the same supremum norm. Hence `f̂ ∈ B^s_{∞,q}(𝕋ᵈ)` exactly when
`F ∈ B^s_{∞,q}(ℝᵈ)` (`TauCeti.UnitAddTorus.memBesov_mFourierCoeff_iff`), with the same norm
(`TauCeti.UnitAddTorus.norm_eq_norm_of_coeff_eq_mFourierCoeff`).

It remains to see that every element of `𝒞^s(𝕋ᵈ)`, `s > 0`, is the coefficient sequence of a
continuous function: its blocks are trigonometric polynomials whose supremum norms decay like
`2^{-js}`, so they sum uniformly. With the Bernstein embedding the same holds in `B^s_{p,q}(𝕋ᵈ)`
for `s > d/p` (`TauCeti.UnitAddTorus.MemBesov.exists_mFourierCoeff_eq`).

## Main declarations

* `TauCeti.UnitAddTorus.integral_fourierInv_mul_eq_tsum` and
  `TauCeti.UnitAddTorus.fourierMultiplierCLM_toLpTop_eq_toLpTop`: transference of Fourier
  multipliers with Schwartz symbols from `ℝᵈ` to the torus.
* `TauCeti.UnitAddTorus.memBesov_mFourierCoeff_iff` and
  `TauCeti.UnitAddTorus.norm_eq_norm_of_coeff_eq_mFourierCoeff`: a continuous function lies in
  `B^s_{∞,q}(𝕋ᵈ)` exactly when its lift lies in `B^s_{∞,q}(ℝᵈ)`, with the same norm.
* `TauCeti.UnitAddTorus.MemBesov.exists_mFourierCoeff_eq`: the elements of `B^s_{p,q}(𝕋ᵈ)`,
  `s > d/p`, are continuous functions.
* `exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith`, in the
  namespace `TauCeti.UnitAddTorus`: `𝒞^{k+α}(𝕋ᵈ) ⊆ C^{k,α}(𝕋ᵈ)`, for `0 < α < 1`, with a norm
  bound.
* `TauCeti.UnitAddTorus.exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`:
  `C^{k,α}(𝕋ᵈ) ⊆ 𝒞^{k+α}(𝕋ᵈ)`, for `α ≥ 0`, with a norm bound.
* `TauCeti.UnitAddTorus.memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith`: the
  identification `𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)`, `0 < α < 1`.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press, 1971, Chapter VII, Section 3 (transference of multipliers to the torus).
* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (the periodic Besov spaces and the periodic Hölder–Zygmund spaces).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
-/

public section

noncomputable section

open Complex MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap RealInnerProductSpace
  BoundedContinuousFunction

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The value of the Fourier monomial `eₙ` at the image of `x` on the torus. -/
private theorem mFourier_euclidean_apply (n : d → ℤ) (x : EuclideanSpace ℝ d) :
    mFourier n (fun i ↦ (x i : UnitAddCircle)) = 𝐞 ⟪x, latticePoint n⟫ := by
  rw [mFourier_coe_apply (x := fun i ↦ x i), Real.fourierChar_apply]
  congr 1
  simp only [PiLp.inner_apply, latticePoint_apply, RCLike.inner_apply, conj_trivial]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

-- The Fourier coefficients and the periodic Besov spaces live on `Lᵖ` for the product of the Haar
-- probability measures on the circle factors, given by this instance; use it here as well.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The `n`-th Fourier coefficient of a continuous function on the torus, as a continuous linear
functional for the supremum norm. -/
private def mFourierCoeffCLM' (n : d → ℤ) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  (mFourierCoeffCLM ∞ n).comp (ContinuousMap.toLp (E := ℂ) ∞ volume ℂ)

private theorem mFourierCoeffCLM'_apply (n : d → ℤ) (f : C(UnitAddTorus d, ℂ)) :
    mFourierCoeffCLM' n f = mFourierCoeff f n := by
  rw [mFourierCoeffCLM', ContinuousLinearMap.comp_apply, mFourierCoeffCLM_apply,
    mFourierCoeff_congr_ae (ContinuousMap.coeFn_toLp volume f)]

variable (σ : 𝓢(EuclideanSpace ℝ d, ℂ))

/-- The convolution of `𝓕⁻ σ` with the lift of the monomial `eₙ` is `σ(n) eₙ`. -/
private theorem integral_fourierInv_mul_mFourier_sub (n : d → ℤ) (x : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y * mFourier n (fun i ↦ ((x - y) i : UnitAddCircle)) =
      σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle)) := by
  have h : 𝓕 (𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ)) = σ := by
    rw [← SchwartzMap.fourierInv_coe, ← SchwartzMap.fourier_coe,
      FourierTransform.fourier_fourierInv_eq]
  simp_rw [mFourier_euclidean_apply, inner_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul,
    Circle.coe_mul]
  rw [← congrFun h (latticePoint n), Real.fourier_eq, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [Circle.smul_def, smul_eq_mul]
  ring

omit [Fintype d] in
/-- The reduction modulo `ℤᵈ` from `EuclideanSpace ℝ d` onto the torus is continuous. -/
private theorem continuous_euclidean_coe :
    Continuous fun x : EuclideanSpace ℝ d ↦ (fun i ↦ (x i : UnitAddCircle) : UnitAddTorus d) :=
  isOpenQuotientMap_coe.continuous.comp (PiLp.continuous_ofLp 2 _)

private theorem integrable_fourierInv : Integrable (𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ)) := by
  rw [← SchwartzMap.fourierInv_coe]
  exact (𝓕⁻ σ).integrable

private theorem integrable_fourierInv_mul (f : C(UnitAddTorus d, ℂ)) (x : EuclideanSpace ℝ d) :
    Integrable fun y ↦
      𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y * f (fun i ↦ ((x - y) i : UnitAddCircle)) :=
  (integrable_fourierInv σ).mul_bdd (c := ‖f‖)
    ((f.continuous.comp (continuous_euclidean_coe.comp
      (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun _ ↦ f.norm_coe_le_norm _)

/-- Convolution of the lift of `f` with `𝓕⁻ σ`, evaluated at `x`, as a continuous linear
functional of `f` for the supremum norm. -/
private def convolutionCLM (x : EuclideanSpace ℝ d) : C(UnitAddTorus d, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := ∫ y, 𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y * f (fun i ↦ ((x - y) i : UnitAddCircle))
      map_add' f g := by
        simp only [ContinuousMap.add_apply, mul_add]
        exact integral_add (integrable_fourierInv_mul σ f x) (integrable_fourierInv_mul σ g x)
      map_smul' a f := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
        exact integral_const_mul a _ }
    (∫ y, ‖𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y‖) fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [← integral_mul_const]
      refine norm_integral_le_of_norm_le ((integrable_fourierInv σ).norm.mul_const _)
        (Eventually.of_forall fun y ↦ ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)

private theorem norm_mFourierCoeffCLM'_le (n : d → ℤ) : ‖mFourierCoeffCLM' (d := d) n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f ↦ by
    rw [one_mul, mFourierCoeffCLM'_apply]
    exact norm_mFourierCoeff_le f.norm_coe_le_norm n

private theorem summable_multiplierCLM (x : EuclideanSpace ℝ d) :
    Summable fun n : d → ℤ ↦
      (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) • mFourierCoeffCLM' n := by
  refine Summable.of_norm (E := C(UnitAddTorus d, ℂ) →L[ℂ] ℂ) ?_
  refine σ.summable_norm_apply_latticePoint.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [norm_mul, norm_mFourier_apply, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourierCoeffCLM'_le n)

private theorem tsum_multiplierCLM_apply (x : EuclideanSpace ℝ d) (f : C(UnitAddTorus d, ℂ)) :
    (∑' n : d → ℤ, (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) •
      mFourierCoeffCLM' n) f = ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n *
        mFourier n (fun i ↦ (x i : UnitAddCircle)) := by
  have := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_multiplierCLM σ x)
  simpa only [ContinuousLinearMap.apply_apply, smul_apply,
    mFourierCoeffCLM'_apply, smul_eq_mul, mul_right_comm _ (mFourierCoeff f _)] using this

/-- **Transference of a Schwartz multiplier to the torus.** Convolving the lift of a continuous
function `f` on the torus with `𝓕⁻ σ` gives the lift of the absolutely convergent Fourier series
`∑ₙ σ(n) f̂(n) eₙ`. -/
theorem integral_fourierInv_mul_eq_tsum (f : C(UnitAddTorus d, ℂ)) (x : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y * f (fun i ↦ ((x - y) i : UnitAddCircle)) =
      ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n *
        mFourier n (fun i ↦ (x i : UnitAddCircle)) := by
  have h : convolutionCLM σ x = ∑' n : d → ℤ,
      (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) • mFourierCoeffCLM' n := by
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.2 span_mFourier_closure_eq_top)
      ?_
    rintro _ ⟨m, rfl⟩
    rw [tsum_multiplierCLM_apply, tsum_eq_single m fun n hn ↦ by simp [hn]]
    simp only [convolutionCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
      integral_fourierInv_mul_mFourier_sub, mFourierCoeff_mFourier, Pi.single_eq_same, mul_one]
  simpa only [convolutionCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    tsum_multiplierCLM_apply] using congr($h f)

open TemperedDistribution ContinuousLinearMap in
open scoped Convolution in
/-- **Transference of a Schwartz multiplier to the torus**, for tempered distributions. If `F` is
the lift to `EuclideanSpace ℝ d` of a continuous function `f` on the torus, the Fourier multiplier
with symbol `σ` maps `F` to the lift `G` of the periodic multiplier `∑ₙ σ(n) f̂(n) eₙ`. -/
theorem fourierMultiplierCLM_toLpTop_eq_toLpTop (f : C(UnitAddTorus d, ℂ))
    {F G : EuclideanSpace ℝ d →ᵇ ℂ} (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle)))
    (hG : ∀ x, G x = ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n *
      mFourier n (fun i ↦ (x i : UnitAddCircle))) :
    fourierMultiplierCLM ℂ σ
        (BoundedContinuousFunction.toLpTop volume ℂ F : 𝓢'(EuclideanSpace ℝ d, ℂ)) =
      (BoundedContinuousFunction.toLpTop volume ℂ G : 𝓢'(EuclideanSpace ℝ d, ℂ)) := by
  obtain ⟨g, hg, -⟩ := exists_fourierMultiplierCLM_eq_and_norm_le σ
    (BoundedContinuousFunction.toLpTop volume ℂ F)
  rw [hg]
  congr 1
  refine Lp.ext ((ae_eq_fourierInv_convolution_of_fourierMultiplierCLM_eq hg).trans ?_)
  refine EventuallyEq.trans ?_ (BoundedContinuousFunction.coeFn_toLpTop volume G).symm
  rw [convolution_congr (lsmul ℂ ℂ) (EventuallyEq.refl _ _)
    (BoundedContinuousFunction.coeFn_toLpTop volume F)]
  refine Eventually.of_forall fun x ↦ ?_
  simp only [convolution_def, lsmul_apply, smul_eq_mul, hF, hG]
  exact integral_fourierInv_mul_eq_tsum σ f x

/-! ### The blocks of a periodic function -/

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-- The finite set of frequencies of norm at most `2^j φ.rOut`, outside of which `ψⱼ` vanishes
(`TauCeti.UnitAddTorus.inhomogeneousLittlewoodPaley_eq_zero_of_notMem`). -/
private def frequencies (j : ℕ) : Finset (d → ℤ) :=
  (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset

/-- The block `Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ` as a continuous function on the torus. -/
private def blockFun (j : ℕ) (c : (d → ℤ) → ℂ) : C(UnitAddTorus d, ℂ) :=
  ∑ n ∈ frequencies φ j, ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) •
    mFourier n

private theorem blockFun_apply (j : ℕ) (c : (d → ℤ) → ℂ) (z : UnitAddTorus d) :
    blockFun φ j c z = ∑ n ∈ frequencies φ j,
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n * mFourier n z := by
  simp [blockFun, ContinuousMap.sum_apply]

private theorem littlewoodPaleyBlockLp_top_eq_toLp (j : ℕ) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ ∞ j c = ContinuousMap.toLp (E := ℂ) ∞ volume ℂ (blockFun φ j c) :=
  Lp.ext <| (coeFn_littlewoodPaleyBlockLp
    (fun _ hn ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn) c).trans <|
      EventuallyEq.trans (Eventually.of_forall fun z ↦ (blockFun_apply φ j c z).symm)
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) volume (blockFun φ j c)).symm

private theorem norm_littlewoodPaleyBlockLp_top (j : ℕ) (c : (d → ℤ) → ℂ) :
    ‖littlewoodPaleyBlockLp φ ∞ j c‖ = ‖blockFun φ j c‖ := by
  rw [littlewoodPaleyBlockLp_top_eq_toLp, ContinuousMap.norm_toLp_top]

omit [Fintype d] in
/-- The lift of a continuous function on the torus to a bounded continuous function on
`EuclideanSpace ℝ d`. -/
private def lift (f : C(UnitAddTorus d, ℂ)) : EuclideanSpace ℝ d →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ f fun i ↦ (x i : UnitAddCircle))
    (f.continuous.comp continuous_euclidean_coe) ‖f‖ fun _ ↦ f.norm_coe_le_norm _

omit [Fintype d] in
private theorem lift_apply (f : C(UnitAddTorus d, ℂ)) (x : EuclideanSpace ℝ d) :
    lift f x = f fun i ↦ (x i : UnitAddCircle) := (rfl)

omit [Fintype d] in
private theorem norm_lift (f : C(UnitAddTorus d, ℂ)) : ‖lift f‖ = ‖f‖ := by
  refine le_antisymm ((BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x ↦
    f.norm_coe_le_norm _) ((ContinuousMap.norm_le f (norm_nonneg _)).2 fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := surjective_coe (d := d) z
  simpa [lift_apply] using (lift f).norm_coe_le_norm (WithLp.toLp 2 x)

open TemperedDistribution in
/-- The Euclidean blocks of the lift of `f` are the lifts of the periodic blocks of `f`. -/
private theorem littlewoodPaleyBlock_toLpTop_eq (f : C(UnitAddTorus d, ℂ))
    {F : EuclideanSpace ℝ d →ᵇ ℂ} (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) (j : ℕ) :
    TemperedDistribution.littlewoodPaleyBlock ℂ φ j
        (BoundedContinuousFunction.toLpTop volume ℂ F : 𝓢'(EuclideanSpace ℝ d, ℂ)) =
      (BoundedContinuousFunction.toLpTop volume ℂ (lift (blockFun φ j (mFourierCoeff f))) :
        𝓢'(EuclideanSpace ℝ d, ℂ)) := by
  rw [littlewoodPaleyBlock_apply, ← φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  refine fourierMultiplierCLM_toLpTop_eq_toLpTop _ f hF fun x ↦ ?_
  rw [lift_apply, blockFun_apply, tsum_eq_sum (s := frequencies φ j) fun n hn ↦ by
    simp [inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn]]
  simp only [φ.coe_inhomogeneousLittlewoodPaleySchwartz]

private theorem norm_toLpTop_lift_blockFun (j : ℕ) (c : (d → ℤ) → ℂ) :
    ‖BoundedContinuousFunction.toLpTop volume ℂ (lift (blockFun φ j c))‖ =
      ‖littlewoodPaleyBlockLp φ ∞ j c‖ := by
  rw [BoundedContinuousFunction.norm_toLpTop, norm_lift, norm_littlewoodPaleyBlockLp_top]

/-- **Periodic and Euclidean Besov spaces of a continuous function agree.** Let `F` be the lift
to `EuclideanSpace ℝ d` of a continuous function `f` on the torus. The Fourier coefficients of `f`
lie in the periodic Besov space `B^s_{∞,q}(𝕋ᵈ)` exactly when `F` lies in `B^s_{∞,q}(ℝᵈ)`. -/
theorem memBesov_mFourierCoeff_iff (f : C(UnitAddTorus d, ℂ)) {F : EuclideanSpace ℝ d →ᵇ ℂ}
    (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) {s : ℝ} {q : ℝ≥0∞} :
    MemBesov φ s ∞ q (mFourierCoeff f) ↔
      (BoundedContinuousFunction.toLpTop volume ℂ F : 𝓢'(EuclideanSpace ℝ d, ℂ)).MemBesov
        φ s ∞ q := by
  rw [memBesov_def, TemperedDistribution.memBesov_iff]
  constructor
  · refine fun h ↦ ⟨fun j ↦ BoundedContinuousFunction.toLpTop volume ℂ
      (lift (blockFun φ j (mFourierCoeff f))), littlewoodPaleyBlock_toLpTop_eq φ f hF, ?_⟩
    simpa only [norm_toLpTop_lift_blockFun] using h
  · rintro ⟨g, hg, hmem⟩
    have hgj (j : ℕ) : g j = BoundedContinuousFunction.toLpTop volume ℂ
        (lift (blockFun φ j (mFourierCoeff f))) :=
      Lp.toTemperedDistribution_injective ((hg j).symm.trans
        (littlewoodPaleyBlock_toLpTop_eq φ f hF j))
    simpa only [hgj, norm_toLpTop_lift_blockFun] using hmem

/-- **The norms agree.** If `u ∈ 𝒞^s(𝕋ᵈ)` has the Fourier coefficients of a continuous function
`f` on the torus and `w ∈ 𝒞^s(ℝᵈ)` is the lift of `f`, then `‖u‖ = ‖w‖`. -/
theorem norm_eq_norm_of_coeff_eq_mFourierCoeff {f : C(UnitAddTorus d, ℂ)}
    {F : EuclideanSpace ℝ d →ᵇ ℂ} (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) {s : ℝ}
    {u : BesovSpace φ s ∞ ∞} {w : TauCeti.BesovSpace ℂ φ s ∞ ∞}
    (hu : u.coeff = mFourierCoeff f)
    (hw : w.toDistr = BoundedContinuousFunction.toLpTop volume ℂ F) : ‖u‖ = ‖w‖ := by
  rw [BesovSpace.norm_eq_ciSup, TauCeti.BesovSpace.norm_eq_ciSup]
  congr 1 with j
  have hj : w.block j = BoundedContinuousFunction.toLpTop volume ℂ
      (lift (blockFun φ j (mFourierCoeff f))) :=
    Lp.toTemperedDistribution_injective (by
      beta_reduce
      rw [TauCeti.BesovSpace.coe_block, hw, littlewoodPaleyBlock_toLpTop_eq φ f hF])
  rw [hj, norm_toLpTop_lift_blockFun, hu]

/-- The Fourier coefficients of the block `Δⱼ c` are `ψⱼ(n) c(n)`. -/
private theorem mFourierCoeff_blockFun (j : ℕ) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    mFourierCoeff (blockFun φ j c) n = φ.inhomogeneousLittlewoodPaley j (latticePoint n) * c n := by
  have h : ⇑(blockFun φ j c) = fun z ↦ ∑ m ∈ frequencies φ j,
      (φ.inhomogeneousLittlewoodPaley j (latticePoint m) : ℂ) * c m * mFourier m z :=
    funext (blockFun_apply φ j c)
  rw [h, mFourierCoeff_sum_mul_mFourier]
  split_ifs with hn
  · rfl
  · simp [inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn]

variable {φ} in
/-- For `s > 0`, the blocks of `c ∈ B^s_{∞,q}(𝕋ᵈ)` decay like `2^{-js}` in the supremum norm, so
their sum converges uniformly to a continuous function whose Fourier coefficients are `c`. -/
private theorem MemBesov.exists_mFourierCoeff_eq_of_top {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    {c : (d → ℤ) → ℂ} (hc : MemBesov φ s ∞ q c) :
    ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c := by
  obtain ⟨M, hM⟩ := memℓp_infty_iff.1 (memBesov_def.1 (hc.mono le_rfl le_top))
  set r : ℝ := ((2 : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hs)
  -- The blocks decay geometrically: `‖Δⱼ c‖_∞ ≤ M 2^{-js}`.
  have hblock (j : ℕ) : ‖blockFun φ j c‖ ≤ M * r ^ j := by
    have h := hM ⟨j, rfl⟩
    beta_reduce at h
    rw [Real.norm_of_nonneg (by positivity), norm_littlewoodPaleyBlockLp_top] at h
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), mul_comm]
    exact h
  have hsum : Summable fun j ↦ blockFun φ j c :=
    .of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left M) hblock
  refine ⟨∑' j, blockFun φ j c, funext fun n ↦ ?_⟩
  rw [← mFourierCoeffCLM'_apply, (mFourierCoeffCLM' n).map_tsum hsum]
  simp only [mFourierCoeffCLM'_apply, mFourierCoeff_blockFun]
  exact ((Complex.ofRealCLM.hasSum (φ.hasSum_inhomogeneousLittlewoodPaley
    (latticePoint n))).mul_right (c n)).tsum_eq.trans (by simp)

variable {φ} in
/-- **Elements of `B^s_{p,q}(𝕋ᵈ)` of order `s > d/p` are continuous functions.** If
`d (1/p) < s`, which for `p = ∞` reads `0 < s`, every `c ∈ B^s_{p,q}(𝕋ᵈ)` is the coefficient
sequence of a continuous function on the torus. -/
theorem MemBesov.exists_mFourierCoeff_eq {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {c : (d → ℤ) → ℂ}
    (hs : Fintype.card d * p.toReal⁻¹ < s) (hc : MemBesov φ s p q c) :
    ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c := by
  -- The Bernstein embedding `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d/p}_{∞,q}(𝕋ᵈ)` reduces to `p = ∞`.
  have h := hc.mono_exponent (r := ∞) le_top
  rw [ENNReal.toReal_top, inv_zero, sub_zero] at h
  exact h.exists_mFourierCoeff_eq_of_top (sub_pos.2 hs)

omit [Fintype d] in
/-- The lift of a function on the torus is invariant under translation by the integer points. -/
private theorem periodic_lift {X : Type*} (f : UnitAddTorus d → X) (m : d → ℤ) :
    Function.Periodic (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle))
      (latticePoint m) := fun x ↦
  congrArg f ((coe_eq_coe_iff (x := WithLp.ofLp x) (y := WithLp.ofLp (x + latticePoint m))).2
    ⟨m, by ext i; simp⟩).symm

omit [Fintype d] in
/-- A continuous function on `EuclideanSpace ℝ d` invariant under translation by the integer
points is bounded: it descends to the compact torus. -/
private theorem exists_norm_le_of_periodic {X : Type*} [SeminormedAddCommGroup X]
    {G : EuclideanSpace ℝ d → X} (hG : Continuous G)
    (hper : ∀ m : d → ℤ, Function.Periodic G (latticePoint m)) : ∃ M, ∀ x, ‖G x‖ ≤ M := by
  obtain ⟨g, hg, hgG⟩ := exists_continuous_comp_coe_eq
    (G := fun y : d → ℝ ↦ G (WithLp.toLp 2 y)) (hG.comp (PiLp.continuous_toLp 2 _))
    fun m y ↦ by
      have hy : WithLp.toLp 2 (y + fun i ↦ (m i : ℝ)) = WithLp.toLp 2 y + latticePoint m := by
        ext i
        simp
      beta_reduce
      rw [hy]
      exact hper m _
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  exact ⟨M, fun x ↦ by simpa [hgG] using hM _ (Set.mem_univ (fun i ↦ (x i : UnitAddCircle)))⟩

/-! ### The identification `𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)` -/

/-- **Periodic Hölder–Zygmund classes of non-integer order are `C^{k,α}` functions.** Let `k : ℕ`
and `0 < α < 1`. There is `C` such that every `u ∈ 𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` is the
coefficient sequence of a continuous function `f` on the torus whose lift
`x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d` is `C^k`, with derivatives through order `k` bounded
by `C ‖u‖` and `α`-Hölder `k`-th derivative with constant `C ‖u‖`. -/
theorem exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (k : ℕ)
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ u : BesovSpace φ (k + α) ∞ ∞, ∃ f : C(UnitAddTorus d, ℂ),
      mFourierCoeff f = u.coeff ∧
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) ∧
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i
        (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ C * ‖u‖) ∧
      HolderWith (C * ‖u‖₊) α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) := by
  obtain ⟨C, hC⟩ :=
    TauCeti.BesovSpace.exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith
      (F := ℂ) φ k hα0 hα1
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨f, hf⟩ := u.memBesov_coeff.exists_mFourierCoeff_eq_of_top
    (add_pos_of_nonneg_of_pos k.cast_nonneg (by exact_mod_cast hα0))
  have hmem := (memBesov_mFourierCoeff_iff φ f (lift_apply f)).1 (hf ▸ u.memBesov_coeff)
  have hnorm : ‖u‖ = ‖hmem.toBesovSpace‖ :=
    norm_eq_norm_of_coeff_eq_mFourierCoeff φ (lift_apply f) hf.symm hmem.toDistr_toBesovSpace
  obtain ⟨g, hg, hgk, hgb, hgH⟩ := hC hmem.toBesovSpace
  obtain rfl : g = lift f := BoundedContinuousFunction.toTemperedDistribution_toLpTop_injective
    (hg.trans hmem.toDistr_toBesovSpace)
  have hnnorm : ‖u‖₊ = ‖hmem.toBesovSpace‖₊ := NNReal.eq (by rw [coe_nnNorm, coe_nnNorm, hnorm])
  rw [← hnorm] at hgb
  rw [← hnnorm] at hgH
  exact ⟨f, hf, hgk, hgb, hgH⟩

/-- **`C^{k,α}` functions on the torus are periodic Hölder–Zygmund classes.** Let `k : ℕ` and
`α ≥ 0`. There is `C` such that if the lift `x ↦ f (x mod ℤᵈ)` of a continuous function `f` on the
torus is `C^k`, with derivatives through order `k` bounded by `M` and `α`-Hölder `k`-th derivative
with constant `H`, then the Fourier coefficients of `f` form an element of
`𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` of norm at most `C (M + H)`. -/
theorem exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith (k : ℕ) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C(UnitAddTorus d, ℂ),
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) →
      ∀ {M : ℝ} {H : ℝ≥0}, (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i
        (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M) →
      HolderWith H α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) →
      ∃ u : BesovSpace φ (k + α) ∞ ∞, u.coeff = mFourierCoeff f ∧ ‖u‖ ≤ C * (M + H) := by
  obtain ⟨C, hC0, hC⟩ :=
    TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := ℂ) φ k α
  refine ⟨C, hC0, fun f hf M H hM hH ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hC (lift f) hf hM hH
  have hmem := (memBesov_mFourierCoeff_iff φ f (lift_apply f)).2 (hw ▸ w.memBesov_toDistr)
  exact ⟨⟨_, hmem⟩, rfl,
    (norm_eq_norm_of_coeff_eq_mFourierCoeff φ (lift_apply f) rfl hw).trans_le hwn⟩

/-- **`𝒞^{k+α}(𝕋ᵈ)` is the space of `C^{k,α}` functions on the torus.** For `k : ℕ` and
`0 < α < 1`, a formal Fourier series `c` lies in the periodic Hölder–Zygmund space
`𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` exactly when it is the coefficient sequence of a continuous
function `f` on the torus whose lift `x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d` is `C^k` with
`α`-Hölder `k`-th derivative. The two quantitative inclusions, which make the norms equivalent,
are `exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith` and
`exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`. -/
theorem memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith (k : ℕ) {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) {c : (d → ℤ) → ℂ} :
    MemBesov φ (k + α) ∞ ∞ c ↔ ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c ∧
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) ∧
      ∃ H : ℝ≥0, HolderWith H α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) := by
  constructor
  · intro hc
    obtain ⟨C, hC⟩ :=
      exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith φ k hα0 hα1
    obtain ⟨f, hf, hfk, -, hfH⟩ := hC ⟨c, hc⟩
    exact ⟨f, hf, hfk, _, hfH⟩
  · rintro ⟨f, rfl, hf, H, hH⟩
    -- The derivatives of the lift are continuous and periodic, hence bounded.
    have hbound (i : Fin (k + 1)) : ∃ M, ∀ x, ‖iteratedFDeriv ℝ i
        (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M :=
      exists_norm_le_of_periodic (hf.continuous_iteratedFDeriv (by exact_mod_cast i.is_le))
        fun m ↦ (periodic_lift f m).iteratedFDeriv i
    choose M hM using hbound
    obtain ⟨C, -, hC⟩ := exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith φ k α
    obtain ⟨u, hu, -⟩ := hC f hf (M := Finset.univ.sup' Finset.univ_nonempty M)
      (fun i hi x ↦ (hM ⟨i, Nat.lt_succ_of_le hi⟩ x).trans
        (Finset.le_sup' M (Finset.mem_univ _))) hH
    exact hu ▸ u.memBesov_coeff

end TauCeti.UnitAddTorus

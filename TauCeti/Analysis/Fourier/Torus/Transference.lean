/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.Analysis.Fourier.Torus.SchwartzMultiplier
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# Transference of Schwartz Fourier multipliers from `ℝᵈ` to the torus

A function `f` on the torus `𝕋ᵈ = UnitAddTorus d` is read on `EuclideanSpace ℝ d` through its lift
`x ↦ f (x mod ℤᵈ)`, a `ℤᵈ`-periodic function. Let `σ` be a Schwartz function on `ℝᵈ`. For a
continuous `f` on the torus with lift `F`, convolving `F` with `𝓕⁻ σ` gives the lift of the
absolutely convergent Fourier series `∑ₙ σ(n) f̂(n) eₙ`
(`TauCeti.UnitAddTorus.integral_fourierInv_mul_eq_tsum`). Both sides are continuous linear
functionals of `f` for the supremum norm, they agree on the monomials `eₙ`, since
`∫ 𝓕⁻ σ(y) eₙ(x - y) dy = σ(n) eₙ(x)`, and the monomials span a dense subspace of `C(𝕋ᵈ, ℂ)`. So
the Fourier multiplier with symbol `σ`, applied to `F` as a tempered distribution, is the lift of
the periodic multiplier with the same symbol
(`TauCeti.UnitAddTorus.fourierMultiplierCLM_toLpTop_eq_toLpTop`).

The lift to `EuclideanSpace ℝ d`, rather than to `d → ℝ` as in
`TauCeti.Topology.Instances.AddCircle.UnitAddTorus`, is the one on which the Fourier transform and
the tempered distributions of Mathlib live; this file records the facts about it that transference
uses.

## Main declarations

* `TauCeti.UnitAddTorus.euclideanLift`: the lift of a continuous function on the torus to a bounded
  continuous function on `EuclideanSpace ℝ d`, with the same supremum norm
  (`TauCeti.UnitAddTorus.norm_euclideanLift`).
* `TauCeti.UnitAddTorus.exists_forall_norm_iteratedFDeriv_euclidean_le`: if the lift of a function
  on the torus to `EuclideanSpace ℝ d` is `C^k`, its derivatives through order `k` are bounded.
* `TauCeti.UnitAddTorus.integral_fourierInv_mul_eq_tsum` and
  `TauCeti.UnitAddTorus.fourierMultiplierCLM_toLpTop_eq_toLpTop`: transference of Fourier
  multipliers with Schwartz symbols from `ℝᵈ` to the torus.

## References

* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press, 1971, Chapter VII, Section 3 (transference of multipliers to the torus).
-/

public section

noncomputable section

open Complex MeasureTheory Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace BoundedContinuousFunction

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

section Lift

variable {E : Type*} [NormedAddCommGroup E]

omit [Fintype d] in
/-- The lift `x ↦ f (x mod ℤᵈ)` of a continuous function on the torus to a bounded continuous
function on `EuclideanSpace ℝ d`. -/
def euclideanLift (f : C(UnitAddTorus d, E)) : EuclideanSpace ℝ d →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ f fun i ↦ (x i : UnitAddCircle))
    (f.continuous.comp continuous_euclidean_coe) ‖f‖ fun _ ↦ f.norm_coe_le_norm _

omit [Fintype d] in
theorem coe_euclideanLift (f : C(UnitAddTorus d, E)) :
    ⇑(euclideanLift f) = fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle) := (rfl)

omit [Fintype d] in
@[simp]
theorem euclideanLift_apply (f : C(UnitAddTorus d, E)) (x : EuclideanSpace ℝ d) :
    euclideanLift f x = f fun i ↦ (x i : UnitAddCircle) := (rfl)

omit [Fintype d] in
/-- The lift of a continuous function on the torus has the same supremum norm. -/
@[simp]
theorem norm_euclideanLift (f : C(UnitAddTorus d, E)) : ‖euclideanLift f‖ = ‖f‖ := by
  refine le_antisymm ((BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x ↦
    f.norm_coe_le_norm _) ((ContinuousMap.norm_le f (norm_nonneg _)).2 fun z ↦ ?_)
  obtain ⟨x, rfl⟩ := surjective_coe (d := d) z
  simpa [euclideanLift_apply] using (euclideanLift f).norm_coe_le_norm (WithLp.toLp 2 x)

end Lift

section IteratedFDeriv

omit [Fintype d] in
/-- The lift of `f` to `EuclideanSpace ℝ d` is its lift to `d → ℝ` composed with the identification
`EuclideanSpace ℝ d ≃L[ℝ] (d → ℝ)`. -/
theorem comp_euclidean_coe_eq_comp {X : Type*} (f : UnitAddTorus d → X) :
    (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) =
      (fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle)) ∘
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d ↦ ℝ) : EuclideanSpace ℝ d →L[ℝ] (d → ℝ)) := by
  funext x
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **The derivatives of a `C^k` lift are bounded.** If the lift `x ↦ f (x mod ℤᵈ)` of a function
`f` on the torus to `EuclideanSpace ℝ d` is `C^k`, then its derivatives through order `k` are
bounded, as for the lift to `d → ℝ` (`TauCeti.UnitAddTorus.exists_forall_norm_iteratedFDeriv_le`).
-/
theorem exists_forall_norm_iteratedFDeriv_euclidean_le (f : UnitAddTorus d → E) {k : ℕ}
    (hf : ContDiff ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) :
    ∃ M, ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i
      (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M := by
  let e := PiLp.continuousLinearEquiv 2 ℝ fun _ : d ↦ ℝ
  have hf' : ContDiff ℝ k fun y : d → ℝ ↦ f fun i ↦ (y i : UnitAddCircle) := by
    have h := hf.comp e.symm.contDiff
    rwa [comp_euclidean_coe_eq_comp, Function.comp_assoc, ContinuousLinearEquiv.coe_coe,
      e.self_comp_symm, Function.comp_id] at h
  refine exists_forall_norm_iteratedFDeriv_le_of_forall_exists fun i hi ↦ ?_
  obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le f
    (hf'.continuous_iteratedFDeriv (by exact_mod_cast hi))
  refine ⟨M * ‖(e : EuclideanSpace ℝ d →L[ℝ] (d → ℝ))‖ ^ i, fun x ↦ ?_⟩
  rw [comp_euclidean_coe_eq_comp, (e : EuclideanSpace ℝ d →L[ℝ] (d → ℝ)).iteratedFDeriv_comp_right
    hf' x (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hM _

end IteratedFDeriv

/-! ### Transference -/

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

private theorem summable_multiplierCLM (x : EuclideanSpace ℝ d) :
    Summable fun n : d → ℤ ↦ (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) •
      mFourierCoeffContinuousMapCLM n := by
  refine Summable.of_norm (E := C(UnitAddTorus d, ℂ) →L[ℂ] ℂ) ?_
  refine σ.summable_norm_apply_latticePoint.of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦ ?_
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [norm_mul, norm_mFourier_apply, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_mFourierCoeffContinuousMapCLM_le n)

private theorem tsum_multiplierCLM_apply (x : EuclideanSpace ℝ d) (f : C(UnitAddTorus d, ℂ)) :
    (∑' n : d → ℤ, (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) •
      mFourierCoeffContinuousMapCLM n) f = ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n *
        mFourier n (fun i ↦ (x i : UnitAddCircle)) := by
  have := (ContinuousLinearMap.apply ℂ ℂ f).map_tsum (summable_multiplierCLM σ x)
  simpa only [ContinuousLinearMap.apply_apply, smul_apply,
    mFourierCoeffContinuousMapCLM_apply, smul_eq_mul, mul_right_comm _ (mFourierCoeff f _)]
    using this

/-- **Transference of a Schwartz multiplier to the torus.** Convolving the lift of a continuous
function `f` on the torus with `𝓕⁻ σ` gives the lift of the absolutely convergent Fourier series
`∑ₙ σ(n) f̂(n) eₙ`. -/
theorem integral_fourierInv_mul_eq_tsum (f : C(UnitAddTorus d, ℂ)) (x : EuclideanSpace ℝ d) :
    ∫ y, 𝓕⁻ (σ : EuclideanSpace ℝ d → ℂ) y * f (fun i ↦ ((x - y) i : UnitAddCircle)) =
      ∑' n : d → ℤ, σ (latticePoint n) * mFourierCoeff f n *
        mFourier n (fun i ↦ (x i : UnitAddCircle)) := by
  have h : convolutionCLM σ x = ∑' n : d → ℤ,
      (σ (latticePoint n) * mFourier n (fun i ↦ (x i : UnitAddCircle))) •
        mFourierCoeffContinuousMapCLM n := by
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

end TauCeti.UnitAddTorus

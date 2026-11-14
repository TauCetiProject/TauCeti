/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import TauCeti.Analysis.Distribution.SchwartzSpace.ChangeOfVariables
public import TauCeti.Analysis.Distribution.TemperateGrowth
public import TauCeti.MeasureTheory.Function.Lp.Precomposition
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Pullback of tempered distributions along a change of variables

Let `φ : E ≃ E` be a bijection of a finite-dimensional real normed space such that `φ` and `φ⁻¹`
both have temperate growth, for instance a diffeomorphism whose derivatives of positive order, and
those of its inverse, are bounded. A tempered distribution `T` pulls back along `φ` to

`(φ^* T) f = T (φ_* f)`,

where `(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)` is the pushforward of Schwartz densities
`SchwartzMap.pushforwardCLM`. This is `TemperedDistribution.compCLM φ`, a continuous linear map
`𝓢'(E, F) →L[ℂ] 𝓢'(E, F)`. The Jacobian factor makes it extend composition with `φ`: for a Schwartz
function, an `Lᵖ` function when `|det Dφ⁻¹|` is bounded, or a function of temperate growth, `u`,
the pullback of the distribution of `u` is the distribution of `u ∘ φ`, for every additive Haar
measure (`compCLM_toTemperedDistributionCLM`,
`MeasureTheory.Lp.compCLM_toTemperedDistribution_eq_compOfMapLeSmul`,
`compCLM_toTemperedDistribution`). The point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹` times the
point mass at `x` (`compCLM_delta`).

The pullback is contravariantly functorial, `(χ ∘ φ)^* = φ^* ∘ χ^*` (`compCLM_trans`), so pulling
back along `φ⁻¹` inverts it (`compCLM_symm_compCLM`, `compCLM_compCLM_symm`). It turns
multiplication by `g` into multiplication by `g ∘ φ` (`compCLM_smulLeftCLM`), and satisfies the
distributional chain rules `∂_w (φ^* T) = ∑ᵢ bᵢ^*(Dφ(·) w) • φ^* (∂_{bᵢ} T)`
(`lineDerivOp_compCLM`) and `φ^* (∂_v T) = ∑ᵢ bᵢ^*(Dφ⁻¹(φ ·) v) • ∂_{bᵢ} (φ^* T)`
(`compCLM_lineDerivOp`).

This is the global change of variables on `𝓢'` against which the Bessel-potential spaces `H^s` and
Besov spaces `B^s_{p, q}`, which are subspaces of `𝓢'`, are compared under diffeomorphisms of `E`.
It needs no bound on the derivatives beyond temperate growth: the shear `(x, y) ↦ (x, y + x³)` of
`ℝ²` and its inverse are polynomial, with unbounded derivatives, and they pull back tempered
distributions.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 and §7.1.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {φ : E ≃ E}

section TVS

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

variable (F) in
/-- The **pullback of tempered distributions** along a bijection `φ` such that `φ` and `φ⁻¹` have
temperate growth: `(φ^* T) f = T (φ_* f)`, the transpose of the pushforward of Schwartz densities
`(φ_* f)(y) = |det Dφ⁻¹(y)| f(φ⁻¹ y)`. On functions it is composition with `φ`
(`TemperedDistribution.compCLM_toTemperedDistribution`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.pushforwardCLM ℂ φ hφ hψ)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem compCLM_apply_apply (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (T : 𝓢'(E, F)) (f : 𝓢(E, ℂ)) :
    compCLM F φ hφ hψ T f = T (SchwartzMap.pushforwardCLM ℂ φ hφ hψ f) :=
  (rfl)

/-- **Functoriality of the pullback**: `(χ ∘ φ)^* = φ^* ∘ χ^*`. -/
theorem compCLM_trans {χ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hχ : (χ : E → E).HasTemperateGrowth)
    (hχs : (χ.symm : E → E).HasTemperateGrowth) (h₁ : (φ.trans χ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans χ).symm : E → E).HasTemperateGrowth) :
    compCLM F (φ.trans χ) h₁ h₂ = compCLM F φ hφ hψ ∘L compCLM F χ hχ hχs := by
  ext T f
  simp [SchwartzMap.pushforwardCLM_trans ℂ hφ hψ hχ hχs h₁ h₂]

/-- The pullback along the identity is the identity. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth) :
    compCLM F (Equiv.refl E) h₁ h₂ = ContinuousLinearMap.id ℂ _ := by
  ext T f
  simp

/-- Pulling back along `φ` and then along `φ⁻¹` gives back the distribution. -/
@[simp]
theorem compCLM_symm_compCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) : compCLM F φ.symm hψ hφ' (compCLM F φ hφ hψ T) = T := by
  rw [← ContinuousLinearMap.comp_apply, ← compCLM_trans hψ hφ' hφ hψ
    (by simpa using Function.HasTemperateGrowth.id (E := E))
    (by simpa using Function.HasTemperateGrowth.id (E := E))]
  simp only [Equiv.symm_trans_self, compCLM_refl, ContinuousLinearMap.id_apply]

/-- Pulling back along `φ⁻¹` and then along `φ` gives back the distribution. -/
@[simp]
theorem compCLM_compCLM_symm (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) : compCLM F φ hφ hψ (compCLM F φ.symm hψ hφ' T) = T := by
  rw [← ContinuousLinearMap.comp_apply, ← compCLM_trans hφ hψ hψ hφ'
    (by simpa using Function.HasTemperateGrowth.id (E := E))
    (by simpa using Function.HasTemperateGrowth.id (E := E))]
  simp only [Equiv.self_trans_symm, compCLM_refl, ContinuousLinearMap.id_apply]

/-- The pullback of `g T` is `(g ∘ φ) φ^* T`. -/
theorem compCLM_smulLeftCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (T : 𝓢'(E, F)) :
    compCLM F φ hφ hψ (smulLeftCLM F g T) = smulLeftCLM F (g ∘ φ) (compCLM F φ hφ hψ T) := by
  ext f
  simp [SchwartzMap.pushforwardCLM_smulLeftCLM ℂ hφ hψ hg]

/-- **Chain rule for the pullback of a tempered distribution.** Differentiating `φ^* T` in
direction `w` expands along any basis `b` of `E` as
`∂_w (φ^* T) = ∑ᵢ bᵢ^*(Dφ(·) w) • φ^* (∂_{bᵢ} T)`. -/
theorem lineDerivOp_compCLM {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) (w : E) :
    ∂_{w} (compCLM F φ hφ hψ T) = ∑ i,
      smulLeftCLM F (fun x ↦ ((b.coord i (fderiv ℝ φ x w) : ℝ) : ℂ))
        (compCLM F φ hφ hψ (∂_{b i} T)) := by
  ext f
  simp [SchwartzMap.pushforwardCLM_lineDerivOp ℂ b hφ hψ f w]

/-- **Pullback of a directional derivative.** Pulling back `∂_v T` along `φ` expresses it in terms
of directional derivatives of `φ^* T` along any basis `b` of `E`:
`φ^* (∂_v T) = ∑ᵢ bᵢ^*(Dφ⁻¹(φ ·) v) • ∂_{bᵢ} (φ^* T)`. -/
theorem compCLM_lineDerivOp {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (T : 𝓢'(E, F)) (v : E) :
    compCLM F φ hφ hψ (∂_{v} T) = ∑ i,
      smulLeftCLM F (fun x ↦ ((b.coord i (fderiv ℝ φ.symm (φ x) v) : ℝ) : ℂ))
        (∂_{b i} (compCLM F φ hφ hψ T)) := by
  have hb (i : ι) : (fun y ↦ ((b.coord i (fderiv ℝ φ.symm y v) : ℝ) : ℂ)).HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal ℂ).comp
      ((b.coord i).toContinuousLinearMap.hasTemperateGrowth.comp (hψ.fderiv_apply v))
  have h := congrArg (compCLM F φ hφ hψ) (lineDerivOp_compCLM b hψ hφ (compCLM F φ hφ hψ T) v)
  rw [compCLM_symm_compCLM hφ hψ hφ T, map_sum] at h
  refine h.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
  rw [compCLM_smulLeftCLM hφ hψ (hb i), compCLM_compCLM_symm hφ hψ hφ]
  rfl

end TVS

section Normed

variable [NormedAddCommGroup F] [NormedSpace ℂ F] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The pullback of the distribution of a Schwartz function `u` is the distribution of `u ∘ φ`,
for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistributionCLM (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (u : 𝓢(E, F)) :
    compCLM F φ hφ hψ (SchwartzMap.toTemperedDistributionCLM E F μ u) =
      SchwartzMap.toTemperedDistributionCLM E F μ
        (SchwartzMap.compCLM ℂ hφ (hψ.exists_norm_le_of_leftInverse φ.left_inv) u) := by
  ext f
  simp only [compCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply,
    SchwartzMap.integral_pushforwardCLM_smul, SchwartzMap.compCLM_apply, Function.comp_apply]

/-- The pullback of the distribution of a function `u` of temperate growth is the distribution
of `u ∘ φ`, for every additive Haar measure. -/
@[simp]
theorem compCLM_toTemperedDistribution (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) {u : E → F} (hu : u.HasTemperateGrowth) :
    compCLM F φ hφ hψ (hu.toTemperedDistribution μ) = (hu.comp hφ).toTemperedDistribution μ := by
  ext f
  simp only [compCLM_apply_apply, Function.HasTemperateGrowth.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul, Function.comp_apply]

section Lp

variable [CompleteSpace F] {μ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

private theorem addHaar_map_le_smul_of_abs_det_fderiv_symm_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    {J : ℝ} (hJ : ∀ y, |(fderiv ℝ φ.symm y).det| ≤ J) :
    μ.map φ ≤ ENNReal.ofReal J • μ := by
  refine Measure.le_iff.2 fun t ht ↦ ?_
  rw [Measure.map_apply hφ.1.continuous.measurable ht, ← Equiv.image_symm_eq_preimage]
  calc μ (φ.symm '' t)
      ≤ ∫⁻ y in t, ENNReal.ofReal |(fderiv ℝ φ.symm y).det| ∂μ :=
        addHaar_image_le_lintegral_abs_det_fderiv μ ht
          fun y _ ↦ (hψ.1.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt
    _ ≤ ∫⁻ _ in t, ENNReal.ofReal J ∂μ :=
        setLIntegral_mono' ht fun y _ ↦ ENNReal.ofReal_le_ofReal (hJ y)
    _ = (ENNReal.ofReal J • μ) t := by simp

/-- Pulling back the tempered distribution of an `Lᵖ` function `u` along `φ` agrees with the
`Lᵖ` precomposition `Lp.compOfMapLeSmul`, for every additive Haar measure `μ` and every
`1 ≤ p ≤ ∞`. -/
theorem _root_.MeasureTheory.Lp.compCLM_toTemperedDistribution_eq_compOfMapLeSmul {C : ℝ≥0∞}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hC : C ≠ ∞) (hmap : μ.map φ ≤ C • μ) (u : Lp F p μ) :
    compCLM F φ hφ hψ (u : 𝓢'(E, F)) =
      (Lp.compOfMapLeSmul ℂ hφ.1.continuous.measurable hC hmap u : 𝓢'(E, F)) := by
  ext f
  rw [compCLM_apply_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul]
  refine integral_congr_ae
    ((Lp.coeFn_compOfMapLeSmul (𝕜 := ℂ) hφ.1.continuous.measurable hC hmap u).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx, Function.comp_apply]

/-- If `|det Dφ⁻¹| ≤ J` everywhere, pulling back the tempered distribution of `u ∈ Lᵖ(μ)` along
`φ` gives an `Lᵖ(μ)` function of norm at most `max 1 J * ‖u‖_p`, uniformly in `1 ≤ p ≤ ∞`. -/
theorem _root_.MeasureTheory.Lp.exists_compCLM_toTemperedDistribution_eq_and_norm_le_of_abs_det_le
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    {J : ℝ} (hJ : ∀ y, |(fderiv ℝ φ.symm y).det| ≤ J) (u : Lp F p μ) :
    ∃ v : Lp F p μ, compCLM F φ hφ hψ (u : 𝓢'(E, F)) = v ∧ ‖v‖ ≤ max 1 J * ‖u‖ := by
  have hmap := addHaar_map_le_smul_of_abs_det_fderiv_symm_le μ hφ hψ hJ
  refine ⟨Lp.compOfMapLeSmul ℂ hφ.1.continuous.measurable ENNReal.ofReal_ne_top hmap u,
    Lp.compCLM_toTemperedDistribution_eq_compOfMapLeSmul hφ hψ ENNReal.ofReal_ne_top hmap u,
    (Lp.norm_compOfMapLeSmul_le hφ.1.continuous.measurable ENNReal.ofReal_ne_top hmap u).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg u)
  set M : ℝ≥0∞ := ENNReal.ofReal (max 1 J)
  have h1M : 1 ≤ M := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (le_max_left 1 J)
  have hr : (1 / p).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top (by simpa using ENNReal.inv_le_one.2 hp.out)
  have hpow : ENNReal.ofReal J ^ (1 / p).toReal ≤ M :=
    calc ENNReal.ofReal J ^ (1 / p).toReal
        ≤ M ^ (1 / p).toReal :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_max_right 1 J)) ENNReal.toReal_nonneg
      _ ≤ M ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h1M hr
      _ = M := ENNReal.rpow_one M
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hpow).trans_eq
    (ENNReal.toReal_ofReal (zero_le_one.trans (le_max_left 1 J)))

/-- If `‖Dφ⁻¹‖ ≤ L` everywhere, pulling back the tempered distribution of `u ∈ Lᵖ(μ)` along `φ`
gives an `Lᵖ(μ)` function of norm at most `max 1 L ^ finrank ℝ E * ‖u‖_p`, uniformly in
`1 ≤ p ≤ ∞`. -/
theorem _root_.MeasureTheory.Lp.exists_compCLM_toTemperedDistribution_eq_and_norm_le
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    {L : ℝ} (hL : ∀ y, ‖fderiv ℝ φ.symm y‖ ≤ L) (u : Lp F p μ) :
    ∃ v : Lp F p μ, compCLM F φ hφ hψ (u : 𝓢'(E, F)) = v ∧
      ‖v‖ ≤ max 1 L ^ Module.finrank ℝ E * ‖u‖ := by
  have hdet (y : E) : |(fderiv ℝ φ.symm y).det| ≤ max 1 L ^ Module.finrank ℝ E :=
    (fderiv ℝ φ.symm y).abs_det_le_opNorm_pow.trans
      (pow_le_pow_left₀ (norm_nonneg _) ((hL y).trans (le_max_right 1 L)) _)
  obtain ⟨v, hv, hnorm⟩ :=
    Lp.exists_compCLM_toTemperedDistribution_eq_and_norm_le_of_abs_det_le hφ hψ hdet u
  exact ⟨v, hv, by rwa [max_eq_right (one_le_pow₀ (le_max_left 1 L))] at hnorm⟩

end Lp

end Normed

/-- The point mass at `φ x` pulls back to `|det Dφ(x)|⁻¹` times the point mass at `x`. -/
theorem compCLM_delta (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth) (x : E) :
    compCLM ℂ φ hφ hψ (delta (φ x)) = ((|(fderiv ℝ φ x).det|⁻¹ : ℝ) : ℂ) • delta x := by
  have h := φ.det_fderiv_symm_mul_det_fderiv (y := φ x) (hφ.1.differentiable (by simp) _)
    (hψ.1.differentiable (by simp) _)
  rw [Equiv.symm_apply_apply] at h
  ext f
  simp [eq_inv_of_mul_eq_one_left h, abs_inv]

end TemperedDistribution

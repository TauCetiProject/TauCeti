/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Sobolev.Wkp.Local.Approximation
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The weak Cauchy–Riemann equation in divergence form

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Let `ξ` be a weak solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`
(`TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`), where `J` is continuous with `J² = -1`, `DJ` is a
weak derivative of `J`, and `J`, `DJ`, `S` are locally `Lᵖ` for some finite `p > 2` with
`1/p + 1/q ≤ 1`. This file proves that `ξ` solves, in the sense of distributions, the Poisson
equation in divergence form

`Δ ξ = ∂_s f + ∂_t g`, with `f = η - S ξ + (∂_t J) ξ` and `g = -J (η - S ξ) - (∂_s J) ξ`,

where `∂_s J = DJ · 1` and `∂_t J = DJ · I`. These are `TauCeti.crDivergenceFst` and
`TauCeti.crDivergenceSnd`. This is the rewriting step in the proof of McDuff–Salamon's
Lemma B.4.6: for smooth data it follows by applying `∂_s - J ∂_t` to the equation and using
`J² = -1`, and the second derivatives of `J` cancel.

For rough `J` the proof tests the weak equation against `ψ = ∂_s Φ - Jᵀ ∂_t Φ`. Its formal
adjoint is `-Δ Φ` plus terms of order at most one in `Φ`, using `Jᵀ Jᵀ = -1`; the term
`((∂_t J) J + J (∂_t J))ᵀ ∂_t Φ` vanishes because `(∂ J) J + J (∂ J) = 0` is the weak derivative
of `J² = -1`. Since `ψ` is not smooth, `Jᵀ` is replaced by smooth approximations converging
uniformly near the support of `Φ`, with derivatives converging in `Lᵖ`, and the identity passes
to the limit.

## Main results

* `TauCeti.IsSobolevCRCoefficients.ae_deriv_comp_add_comp_deriv_eq_zero`: if `J² = -1` on `Ω`
  and `p > 2`, then `DJ v ∘ J + J ∘ DJ v = 0` almost everywhere on `Ω`, for every direction `v`.
* `TauCeti.HasWeakFDerivOn.exists_contDiff_tendsto_of_continuousOn`: a continuous map with a
  locally `Lᵖ` weak derivative is approximated near a compact subset of `Ω` by smooth maps,
  uniformly, with derivatives converging in `Lᵖ`.
* `TauCeti.IsWeakCRSolution.integral_inner_laplacian_eq`: for every test function
  `Φ ∈ 𝓓(Ω, V)`, `∫ ⟪Δ Φ, ξ⟫ = -∫ (⟪∂_s Φ, f⟫ + ⟪∂_t Φ, g⟫)`.
* `TauCeti.IsWeakCRSolution.integral_laplacian_smul_eq`: the same identity for real test
  functions `φ ∈ 𝓓(Ω, ℝ)`, `∫ Δ φ • ξ = -∫ (∂_s φ • f + ∂_t φ • g)`, in the form consumed by
  the divergence-form Laplace regularity
  `TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`.
* `TauCeti.IsSobolevCRCoefficients.memLpLoc_crDivergenceFst` and
  `TauCeti.IsSobolevCRCoefficients.memLpLoc_crDivergenceSnd`: if `ξ` is locally `L^q` and `η`
  is locally `Lʳ` with `1/p + 1/q = 1/r`, then `f` and `g` are locally `Lʳ`.

For the standard structure `J = i` and `S = 0` on `V = ℂ`, the data are `f = η` and `g = -i η`
(`TauCeti.crDivergenceFst_zero_zero`, `TauCeti.crDivergenceSnd_mul_I`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6).
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Filter Set
open scoped InnerProductSpace ContDiff Distributions ENNReal Topology Laplacian Convolution

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-! ### The divergence-form data -/

/-- The `s`-component `f = η - S ξ + (∂_t J) ξ` of the divergence-form rewriting
`Δ ξ = ∂_s f + ∂_t g` of the weak equation `∂_s ξ + J ∂_t ξ + S ξ = η`, with `∂_t J = DJ · I`. -/
def crDivergenceFst (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) (z : ℂ) :
    V :=
  η z - S z (ξ z) + DJ z I (ξ z)

/-- The `t`-component `g = -J (η - S ξ) - (∂_s J) ξ` of the divergence-form rewriting
`Δ ξ = ∂_s f + ∂_t g` of the weak equation `∂_s ξ + J ∂_t ξ + S ξ = η`, with `∂_s J = DJ · 1`. -/
def crDivergenceSnd (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (ξ η : ℂ → V) (z : ℂ) : V :=
  -J z (η z - S z (ξ z)) - DJ z 1 (ξ z)

/-- The pointwise defining equation of `TauCeti.crDivergenceFst`. -/
theorem crDivergenceFst_apply (z : ℂ) :
    crDivergenceFst DJ S ξ η z = η z - S z (ξ z) + DJ z I (ξ z) := (rfl)

/-- The pointwise defining equation of `TauCeti.crDivergenceSnd`. -/
theorem crDivergenceSnd_apply (z : ℂ) :
    crDivergenceSnd J DJ S ξ η z = -J z (η z - S z (ξ z)) - DJ z 1 (ξ z) := (rfl)

/-- For constant `J` (so `DJ = 0`) and `S = 0` the `s`-component is the right-hand side `η`. -/
@[simp]
theorem crDivergenceFst_zero_zero : crDivergenceFst (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) 0 ξ η = η := by
  funext z
  simp [crDivergenceFst]

/-- For constant `J` (so `DJ = 0`) and `S = 0` the `t`-component is `-J η`. -/
@[simp]
theorem crDivergenceSnd_zero_zero :
    crDivergenceSnd J (0 : ℂ → ℂ →L[ℝ] V →L[ℝ] V) 0 ξ η = fun z => -J z (η z) := by
  funext z
  simp [crDivergenceSnd]

/-- For the standard structure `J = i` on `ℂ` and `S = 0` the `t`-component is `-i η`. -/
theorem crDivergenceSnd_mul_I {ξ η : ℂ → ℂ} :
    crDivergenceSnd (fun _ => ContinuousLinearMap.mul ℝ ℂ I) 0 0 ξ η = fun z => -(I * η z) := by
  simp

/-! ### Integrability of the data -/

section Integrability

/-- A field of operators continuous on `Ω`, applied to a locally `Lᵖ` field, is locally `Lᵖ`. -/
private theorem memLpLoc_apply_of_continuousOn {A : ℂ → V →L[ℝ] V} {w : ℂ → V}
    (hA : ContinuousOn A Ω) (hw : MemLpLoc p Ω w) : MemLpLoc p Ω (fun z => A z (w z)) :=
  memLpLoc_iff.2 fun K hKΩ hK => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).memLp_of_bilin p
    ((hA.mono hKΩ).memLp_top_restrict_of_subset_isCompact hK hK.measurableSet subset_rfl)
    (memLpLoc_iff.1 hw K hKΩ hK)

/-- Hölder's inequality for a locally `Lᵖ` field of operators applied to a locally `L^q` field,
with `1/p + 1/q = 1/r`. -/
private theorem memLpLoc_apply_of_memLpLoc {A : ℂ → V →L[ℝ] V} {w : ℂ → V}
    (hA : MemLpLoc p Ω A) (hw : MemLpLoc q Ω w) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) :
    MemLpLoc r Ω (fun z => A z (w z)) :=
  have : ENNReal.HolderTriple p q r := ⟨hpqr⟩
  memLpLoc_iff.2 fun K hKΩ hK => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).memLp_of_bilin r
    (memLpLoc_iff.1 hA K hKΩ hK) (memLpLoc_iff.1 hw K hKΩ hK)

/-- The coefficient `∂_v J = DJ · v` inherits local `Lᵖ` membership from `DJ`. -/
private theorem memLpLoc_deriv_apply {D : ℂ → ℂ →L[ℝ] V →L[ℝ] V} (hD : MemLpLoc p Ω D)
    (v : ℂ) : MemLpLoc p Ω (fun z => D z v) :=
  hD.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)

/-- If `ξ` is locally `L^q` and `η` locally `Lʳ` with `1/p + 1/q = 1/r`, the `s`-component
`f = η - S ξ + (∂_t J) ξ` of the divergence form is locally `Lʳ`. -/
theorem IsSobolevCRCoefficients.memLpLoc_crDivergenceFst
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hξ : MemLpLoc q Ω ξ) (hη : MemLpLoc r Ω η)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹) : MemLpLoc r Ω (crDivergenceFst DJ S ξ η) :=
  (hη.sub (memLpLoc_apply_of_memLpLoc hc.memLpLoc_zeroth hξ hpqr)).add
    (memLpLoc_apply_of_memLpLoc (memLpLoc_deriv_apply hc.memLpLoc_deriv I) hξ hpqr)

/-- If `J` is continuous, `ξ` is locally `L^q` and `η` locally `Lʳ` with `1/p + 1/q = 1/r`, the
`t`-component `g = -J (η - S ξ) - (∂_s J) ξ` of the divergence form is locally `Lʳ`. -/
theorem IsSobolevCRCoefficients.memLpLoc_crDivergenceSnd
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω) (hξ : MemLpLoc q Ω ξ)
    (hη : MemLpLoc r Ω η) (hpqr : p⁻¹ + q⁻¹ = r⁻¹) :
    MemLpLoc r Ω (crDivergenceSnd J DJ S ξ η) :=
  (memLpLoc_apply_of_continuousOn hJc
    (hη.sub (memLpLoc_apply_of_memLpLoc hc.memLpLoc_zeroth hξ hpqr))).neg.sub
    (memLpLoc_apply_of_memLpLoc (memLpLoc_deriv_apply hc.memLpLoc_deriv 1) hξ hpqr)

/-- Under the hypotheses of the weak equation, the `s`-component of the divergence form is locally
integrable. -/
private theorem locallyIntegrableOn_crDivergenceFst
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hξ : MemLpLoc q Ω ξ)
    (hη : LocallyIntegrableOn η Ω) : LocallyIntegrableOn (crDivergenceFst DJ S ξ η) Ω := by
  have hloc := Ω.isOpen.isLocallyClosed
  exact (hη.sub (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ hpq hloc)).add
    ((memLpLoc_deriv_apply hc.memLpLoc_deriv I).locallyIntegrableOn_clm_apply hξ hpq hloc)

/-- Under the hypotheses of the weak equation and continuity of `J`, the `t`-component of the
divergence form is locally integrable. -/
private theorem locallyIntegrableOn_crDivergenceSnd
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hJc : ContinuousOn J Ω) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hξ : MemLpLoc q Ω ξ) (hη : LocallyIntegrableOn η Ω) :
    LocallyIntegrableOn (crDivergenceSnd J DJ S ξ η) Ω := by
  have hloc := Ω.isOpen.isLocallyClosed
  have h1 : MemLpLoc 1 Ω (fun z => η z - S z (ξ z)) :=
    (memLpLoc_one_iff_locallyIntegrableOn hloc).2
      (hη.sub (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ hpq hloc))
  exact ((memLpLoc_apply_of_continuousOn hJc h1).locallyIntegrableOn le_rfl hloc).neg.sub
    ((memLpLoc_deriv_apply hc.memLpLoc_deriv 1).locallyIntegrableOn_clm_apply hξ hpq hloc)

end Integrability

/-! ### The derivative of `J² = -1` -/

/-- **The weak derivative of `J² = -1`.** If `J² = -1` on `Ω`, `DJ` is a weak derivative of `J`,
and `J`, `DJ` are locally `Lᵖ` for a finite `p > 2`, then `DJ v ∘ J + J ∘ DJ v = 0` almost
everywhere on `Ω`, for every direction `v`. The weak Leibniz rule computes the weak derivative of
`J ∘ J`, and the constant `-1` has weak derivative zero. -/
theorem IsSobolevCRCoefficients.ae_deriv_comp_add_comp_deriv_eq_zero [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -1) :
    ∀ᵐ z ∂volume.restrict Ω, ∀ v : ℂ, DJ z v ∘L J z + J z ∘L DJ z v = 0 := by
  lift p to NNReal using hp_top
  have hp2 : (2 : NNReal) < p := by exact_mod_cast hp
  have hp1 : (1 : NNReal) < p := one_lt_two.trans hp2
  have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp1.le⟩
  -- the conjugate exponent `p'` is at most `p`, since `p ≥ 2`
  have hconj : (p : ℝ≥0∞).conjExponent ≤ p := by
    have h1 := ENNReal.HolderConjugate.inv_add_inv_eq_one (p : ℝ≥0∞) (p : ℝ≥0∞).conjExponent
    have h2 : (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞)⁻¹ ≤ (p : ℝ≥0∞)⁻¹ + (p : ℝ≥0∞).conjExponent⁻¹ := by
      rw [h1, ← ENNReal.inv_two_add_inv_two]
      have : (p : ℝ≥0∞)⁻¹ ≤ 2⁻¹ := ENNReal.inv_le_inv.2 (by exact_mod_cast hp2.le)
      exact add_le_add this this
    exact ENNReal.inv_le_inv.1
      ((ENNReal.add_le_add_iff_left (ENNReal.inv_ne_top.2 (by positivity))).1 h2)
  have hL := HasWeakFDerivOn.bilin_of_memLpLoc (ContinuousLinearMap.compL ℝ V V V) hp2 hp1 le_rfl
    hc.hasWeakFDerivOn (hc.memLpLoc_coeff.mono_exponent hconj) hc.memLpLoc_deriv
    hc.hasWeakFDerivOn hc.memLpLoc_coeff hc.memLpLoc_deriv
  have h0 : HasWeakFDerivOn volume Ω (fun z => J z ∘L J z) 0 := by
    have hconst : HasWeakFDerivOn volume Ω (fun _ : ℂ => (-1 : V →L[ℝ] V)) 0 :=
      hasWeakFDerivOn_iff.2 fun v => by
        simpa using hasWeakLineDerivOn_const (μ := volume) (Ω := Ω) (v := v) (-1 : V →L[ℝ] V)
    refine hconst.congr_ae ?_
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with z hz
    exact (hJ z hz).symm
  filter_upwards [hL.ae_eq h0] with z hz v
  simpa using congrArg (fun T : ℂ →L[ℝ] V →L[ℝ] V => T v) hz

/-! ### Smooth approximation of continuous Sobolev maps near a compact set -/

/-- **Smooth approximation near a compact set.** Let `A` be continuous on `Ω` with a weak
derivative `DA` that is locally `Lᵖ`, `1 ≤ p < ∞`. For every compact `K ⊆ Ω` there are smooth maps
`A' n` with `A' n → A` uniformly on `K` and `fderiv (A' n) → DA` in `Lᵖ(K)`. The maps are
mollifications of `A`, extended by zero off a neighbourhood of `K`. -/
theorem HasWeakFDerivOn.exists_contDiff_tendsto_of_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {A : ℂ → E} {DA : ℂ → ℂ →L[ℝ] E} (hA : HasWeakFDerivOn volume Ω A DA)
    (hAc : ContinuousOn A Ω) (hDA : MemLpLoc p Ω DA) {K : Set ℂ} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    ∃ A' : ℕ → ℂ → E, (∀ n, ContDiff ℝ ∞ (A' n)) ∧
      Tendsto (fun n => eLpNorm (A' n - A) ∞ (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fderiv ℝ (A' n) - DA) p (volume.restrict K)) atTop (𝓝 0) := by
  obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  let U : Opens ℂ := ⟨W, hWo⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hWΩ
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hWo hKW
  have hAp : MemLp A p (volume.restrict (U : Set ℂ)) :=
    hAc.memLpLoc.memLp_of_closure_subset hWc hWΩ
  have hDAp : MemLp DA p (volume.restrict (U : Set ℂ)) := hDA.memLp_of_closure_subset hWc hWΩ
  let φ : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨((n : ℝ) + 1)⁻¹ / 2, ((n : ℝ) + 1)⁻¹, by positivity, half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  set fA : Lp E p (volume.restrict (U : Set ℂ)) := hAp.toLp A
  set fD : Lp (ℂ →L[ℝ] E) p (volume.restrict (U : Set ℂ)) := hDAp.toLp DA
  have hfA : (fA : ℂ → E) =ᵐ[volume.restrict (U : Set ℂ)] A := hAp.coeFn_toLp
  have hfD : (fD : ℂ → ℂ →L[ℝ] E) =ᵐ[volume.restrict (U : Set ℂ)] DA := hDAp.coeFn_toLp
  have hball : ∀ᶠ n in atTop, ∀ x ∈ K, Metric.closedBall x (φ n).rOut ⊆ U := by
    filter_upwards [(tendsto_order.1 hφ).2 δ hδ] with n hn x hx
    exact (Metric.closedBall_subset_closedBall hn.le).trans
      ((Metric.closedBall_subset_cthickening hx δ).trans hKδ)
  refine ⟨fun n => Wkp.smoothField (φ n) fA, fun n => Wkp.contDiff_smoothField _ _, ?_, ?_⟩
  · -- uniform convergence on `K`, from the uniform continuity of `A` near `K`
    have hAu : UniformContinuousOn A (closure W) :=
      hWc.uniformContinuousOn_of_continuous (hAc.mono hWΩ)
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    rcases eq_top_or_lt_top ε with rfl | hεt
    · exact Eventually.of_forall fun _ => le_top
    have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt.ne
    obtain ⟨δ', hδ', hu⟩ := Metric.uniformContinuousOn_iff_le.1 hAu ε.toReal hε'
    filter_upwards [hball, (tendsto_order.1 hφ).2 δ' hδ'] with n hn hn'
    rw [← ENNReal.ofReal_toReal hεt.ne]
    rw [eLpNorm_exponent_top (((Wkp.contDiff_smoothField _ _).continuous.aestronglyMeasurable).sub
      ((hAc.mono hKΩ).aestronglyMeasurable hK.measurableSet))]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    rw [Pi.sub_apply, ← dist_eq_norm]
    refine Wkp.dist_smoothField_le (φ n) hfA
      (Metric.ball_subset_closedBall.trans (hn x hx)) fun y hy => ?_
    have hyx : dist y x ≤ δ' := (Metric.mem_ball.1 hy).le.trans hn'.le
    exact hu y (subset_closure (Metric.ball_subset_closedBall.trans (hn x hx) hy)) x
      (subset_closure (hKW hx)) hyx
  · -- convergence of the derivatives in `Lᵖ(K)`, from the `Lᵖ` approximate identity
    have hA' : HasWeakFDerivOn volume U (fA : ℂ → E) (fD : ℂ → ℂ →L[ℝ] E) :=
      ((hA.mono hUΩ).congr_ae hfA.symm).congr_ae_deriv hfD.symm
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (Wkp.tendsto_eLpNorm_smoothField_sub hp hφ fD) (Eventually.of_forall fun _ => by simp) ?_
    filter_upwards [hball] with n hn
    have hae : fderiv ℝ (Wkp.smoothField (φ n) fA) - DA =ᵐ[volume.restrict K]
        Wkp.smoothField (φ n) fD - (fD : ℂ → ℂ →L[ℝ] E) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hKW hfD,
        ae_restrict_mem hK.measurableSet] with x hx hxK
      simp only [Pi.sub_apply, hx]
      congr 1
      simpa only [Wkp.smoothField_def, convolution_flip] using
        hA'.fderiv_indicator_convolution_normed (Lp.memLp fA) (Lp.memLp fD) Fact.out Fact.out
          (φ n) x (hn x hxK)
    rw [eLpNorm_congr_ae hae]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono hKW le_rfl)

/-! ### The divergence form of the weak equation -/

section DivergenceForm

/-! #### Calculus of a test function -/

/-- The mixed second derivatives of a test function agree. -/
private theorem fderiv_fderiv_I_one (Φ : 𝓓(Ω, V)) (z : ℂ) :
    fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I 1 = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I :=
  (Φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)) I 1

/-- The Laplacian on `ℂ` in the coordinates `z = s + i t`. -/
private theorem laplacian_testFunction (Φ : 𝓓(Ω, V)) (z : ℂ) :
    Δ (Φ : ℂ → V) z = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 1 +
      fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The first derivative in the direction `I` and the second derivatives in the directions
`(1, I)` and `(I, I)` of a test function are bounded. -/
private theorem exists_bound_fderiv_testFunction (Φ : 𝓓(Ω, V)) :
    ∃ C, ∀ z, ‖fderiv ℝ (Φ : ℂ → V) z I‖ ≤ C ∧ ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I‖ ≤ C := by
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ (Φ : ℂ → V)) := Φ.contDiff.fderiv_right (m := 1) (by simp)
  have hΦ2 : Continuous (fderiv ℝ (fderiv ℝ (Φ : ℂ → V))) := hΦ1.continuous_fderiv one_ne_zero
  have hs1 : HasCompactSupport (fderiv ℝ (Φ : ℂ → V)) := Φ.hasCompactSupport.fderiv ℝ
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ (Φ : ℂ → V))) := hs1.fderiv ℝ
  have hbd : ∀ F : ℂ → V, Continuous F → HasCompactSupport F → ∃ C, ∀ z, ‖F z‖ ≤ C :=
    fun F hF hs => by
      obtain ⟨C, hC⟩ := hF.norm.bddAbove_range_of_hasCompactSupport hs.norm
      exact ⟨C, fun z => hC (Set.mem_range_self z)⟩
  obtain ⟨C₁, hC₁⟩ := hbd (fun z => fderiv ℝ (Φ : ℂ → V) z I)
    (hΦ1.continuous.clm_apply continuous_const)
    (hs1.comp_left (g := fun T : ℂ →L[ℝ] V => T I) rfl)
  obtain ⟨C₂, hC₂⟩ := hbd (fun z => fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z 1 I)
    ((hΦ2.clm_apply continuous_const).clm_apply continuous_const)
    (hs2.comp_left (g := fun T : ℂ →L[ℝ] ℂ →L[ℝ] V => T 1 I) rfl)
  obtain ⟨C₃, hC₃⟩ := hbd (fun z => fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I)
    ((hΦ2.clm_apply continuous_const).clm_apply continuous_const)
    (hs2.comp_left (g := fun T : ℂ →L[ℝ] ℂ →L[ℝ] V => T I I) rfl)
  exact ⟨max C₁ (max C₂ C₃), fun z => ⟨(hC₁ z).trans (le_max_left _ _),
    (hC₂ z).trans ((le_max_left _ _).trans (le_max_right _ _)),
    (hC₃ z).trans ((le_max_right _ _).trans (le_max_right _ _))⟩⟩

/-- The test function `∂_s Φ - M ∂_t Φ` for a smooth field of operators `M`. -/
private def crTestField (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M) : 𝓓(Ω, V) :=
  TestFunction.lineDerivCLM ℝ 1 Φ -
    TestFunction.bilinLeftCLM (ContinuousLinearMap.apply ℝ V) hM (TestFunction.lineDerivCLM ℝ I Φ)

private theorem crTestField_apply (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M)
    (z : ℂ) :
    crTestField Φ hM z = fderiv ℝ (Φ : ℂ → V) z 1 - M z (fderiv ℝ (Φ : ℂ → V) z I) := by
  simp [crTestField, TestFunction.lineDeriv_eq_fderiv]

private theorem fderiv_crTestField (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V} (hM : ContDiff ℝ ∞ M)
    (z v : ℂ) :
    fderiv ℝ (crTestField Φ hM : ℂ → V) z v = fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z v 1 -
      fderiv ℝ M z v (fderiv ℝ (Φ : ℂ → V) z I) -
      M z (fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z v I) := by
  have hD : DifferentiableAt ℝ (fderiv ℝ (Φ : ℂ → V)) z :=
    ((Φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable (by simp)).differentiableAt
  have hMd : DifferentiableAt ℝ M z := (hM.differentiable (by simp)).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ (Φ : ℂ → V) y 1) z :=
    hD.clm_apply (differentiableAt_const _)
  have hI : DifferentiableAt ℝ (fun y => fderiv ℝ (Φ : ℂ → V) y I) z :=
    hD.clm_apply (differentiableAt_const _)
  have hfun : (crTestField Φ hM : ℂ → V) =
      fun y => fderiv ℝ (Φ : ℂ → V) y 1 - M y (fderiv ℝ (Φ : ℂ → V) y I) :=
    funext (crTestField_apply Φ hM)
  rw [hfun, fderiv_fun_sub h1 (hMd.clm_apply hI), fderiv_clm_apply hMd hI,
    fderiv_clm_apply hD (differentiableAt_const _), fderiv_clm_apply hD (differentiableAt_const _)]
  simp
  abel

/-- The terms of the pairing `⟪D* ψ, ξ⟫ - ⟪ψ, η⟫`, for `ψ = ∂_s Φ - M ∂_t Φ`, that depend on the
operator `M` and its derivative `N`. -/
private def remainder (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (ξ η : ℂ → V) (Φ : ℂ → V) (z : ℂ) (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) : ℝ :=
  ⟪N 1 (fderiv ℝ Φ z I), ξ z⟫_ℝ + ⟪M (fderiv ℝ (fderiv ℝ Φ) z 1 I), ξ z⟫_ℝ +
    ⟪N I (fderiv ℝ Φ z I), (J z : V →L[ℝ] V) (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ (fderiv ℝ Φ) z I I), (J z : V →L[ℝ] V) (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ Φ z I), (DJ z I : V →L[ℝ] V) (ξ z)⟫_ℝ - ⟪M (fderiv ℝ Φ z I), S z (ξ z)⟫_ℝ +
    ⟪M (fderiv ℝ Φ z I), η z⟫_ℝ

/-- A bound for the remainder term, given a bound `C` for the first and second derivatives of
`Φ` that enter it. -/
private theorem abs_remainder_le {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {Φ : ℂ → V} {z : ℂ} {C : ℝ} (hC1 : ‖fderiv ℝ Φ z I‖ ≤ C)
    (hC2 : ‖fderiv ℝ (fderiv ℝ Φ) z 1 I‖ ≤ C) (hC3 : ‖fderiv ℝ (fderiv ℝ Φ) z I I‖ ≤ C)
    (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) :
    |remainder J DJ S ξ η Φ z M N| ≤ ‖N‖ * (C * (‖ξ z‖ + ‖J z (ξ z)‖)) +
      ‖M‖ * (C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)) := by
  have hT : ∀ (T : V →L[ℝ] V) (a b : V) (c : ℝ), ‖a‖ ≤ c → |⟪T a, b⟫_ℝ| ≤ ‖T‖ * (c * ‖b‖) :=
    fun T a b c hac => (abs_real_inner_le_norm _ _).trans (by
      calc ‖T a‖ * ‖b‖ ≤ ‖T‖ * ‖a‖ * ‖b‖ := by gcongr; exact T.le_opNorm a
        _ ≤ ‖T‖ * (c * ‖b‖) := by rw [mul_assoc]; gcongr)
  have hN1 : ‖N 1‖ ≤ ‖N‖ := by simpa using N.le_opNorm 1
  have hNI : ‖N I‖ ≤ ‖N‖ := by simpa using N.le_opNorm I
  have h1 := hT (N 1) _ (ξ z) C hC1
  have h2 := hT M _ (ξ z) C hC2
  have h3 := hT (N I) _ (J z (ξ z)) C hC1
  have h4 := hT M _ (J z (ξ z)) C hC3
  have h5 := hT M _ (DJ z I (ξ z)) C hC1
  have h6 := hT M _ (S z (ξ z)) C hC1
  have h7 := hT M _ (η z) C hC1
  have hC : 0 ≤ C := (norm_nonneg _).trans hC1
  have e1 : ‖N 1‖ * (C * ‖ξ z‖) ≤ ‖N‖ * (C * ‖ξ z‖) := by gcongr
  have e3 : ‖N I‖ * (C * ‖J z (ξ z)‖) ≤ ‖N‖ * (C * ‖J z (ξ z)‖) := by gcongr
  unfold remainder
  obtain ⟨l1, u1⟩ := abs_le.1 h1
  obtain ⟨l2, u2⟩ := abs_le.1 h2
  obtain ⟨l3, u3⟩ := abs_le.1 h3
  obtain ⟨l4, u4⟩ := abs_le.1 h4
  obtain ⟨l5, u5⟩ := abs_le.1 h5
  obtain ⟨l6, u6⟩ := abs_le.1 h6
  obtain ⟨l7, u7⟩ := abs_le.1 h7
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

/-- The bound for the remainder term, in extended nonnegative reals. -/
private theorem enorm_remainder_le {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    {Φ : ℂ → V} {z : ℂ} {C : ℝ} (hC1 : ‖fderiv ℝ Φ z I‖ ≤ C)
    (hC2 : ‖fderiv ℝ (fderiv ℝ Φ) z 1 I‖ ≤ C) (hC3 : ‖fderiv ℝ (fderiv ℝ Φ) z I I‖ ≤ C)
    (M : V →L[ℝ] V) (N : ℂ →L[ℝ] V →L[ℝ] V) :
    ‖remainder J DJ S ξ η Φ z M N‖ₑ ≤ ‖N‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ +
      ‖M‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hC1
  have hbd := abs_remainder_le (J := J) (DJ := DJ) (S := S) (ξ := ξ) (η := η) hC1 hC2 hC3 M N
  have hb1 : 0 ≤ C * (‖ξ z‖ + ‖J z (ξ z)‖) := mul_nonneg hC0 (by positivity)
  have hb2 : 0 ≤ C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖) :=
    mul_nonneg hC0 (by positivity)
  refine (Real.eNorm_eq_ofReal_abs _).trans_le ((ENNReal.ofReal_le_ofReal hbd).trans_eq ?_)
  rw [ENNReal.ofReal_add (mul_nonneg (norm_nonneg N) hb1) (mul_nonneg (norm_nonneg M) hb2),
    ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm,
    ofReal_norm, ← Real.eNorm_of_nonneg hb1, ← Real.eNorm_of_nonneg hb2]

/-- Hölder's inequality along a sequence: if `X n → 0` in `L^a` and `g ∈ L^b` with
`1/a + 1/b = 1`, then `∫⁻ ‖X n‖ ‖g‖ → 0`. -/
private theorem tendsto_lintegral_enorm_mul {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {a b : ℝ≥0∞} [ENNReal.HolderTriple a b 1]
    {X : ℕ → α → E} {g : α → F} (hg : eLpNorm g b μ ≠ ⊤)
    (hX : Tendsto (fun n => eLpNorm (X n) a μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ z, ‖X n z‖ₑ * ‖g z‖ₑ ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using ENNReal.Tendsto.mul_const hX (Or.inr hg)) (fun _ => by simp) fun n => ?_
  calc ∫⁻ z, ‖X n z‖ₑ * ‖g z‖ₑ ∂μ = ∫⁻ z, ‖‖X n z‖ * ‖g z‖‖ₑ ∂μ := by
        simp only [eNorm_mul, eNorm_norm]
    _ ≤ eLpNorm (fun z => ‖X n z‖ * ‖g z‖) 1 μ := lintegral_eNorm_le_eLpNorm_one
    _ ≤ 1 * eLpNorm (X n) a μ * eLpNorm g b μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (fun (x : E) (y : F) => ‖x‖ * ‖y‖) 1
          (fun hf hg => hf.norm.mul hg.norm) (Eventually.of_forall fun _ => by simp [eNorm_mul])
          one_pos
    _ = eLpNorm (X n) a μ * eLpNorm g b μ := by rw [one_mul]

variable [CompleteSpace V]

/-- The Hilbert adjoint on `V →L[ℝ] V`, as a real continuous linear map. -/
private def adjointCLM : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V where
  toFun := ContinuousLinearMap.adjoint
  map_add' := map_add _
  map_smul' c T := by simp
  cont := ContinuousLinearMap.adjoint.continuous

private theorem adjointCLM_apply (T : V →L[ℝ] V) : adjointCLM T = ContinuousLinearMap.adjoint T :=
  (rfl)

/-- The linear algebra behind the comparison of the two pairings, at a single point. -/
private theorem pairing_algebra (a₁ a d₁₁ d₁₂ d₂₂ x y : V) (j dj₁ dj₂ s M N₁ N₂ : V →L[ℝ] V) :
    (-⟪d₁₁ - N₁ a - M d₁₂, x⟫_ℝ - ⟪d₁₂ - N₂ a - M d₂₂, j x⟫_ℝ - ⟪a₁ - M a, dj₂ x⟫_ℝ +
        ⟪a₁ - M a, s x⟫_ℝ - ⟪a₁ - M a, y⟫_ℝ) +
      (⟪d₁₁ + d₂₂, x⟫_ℝ + (⟪a₁, y - s x + dj₂ x⟫_ℝ + ⟪a, -j (y - s x) - dj₁ x⟫_ℝ)) =
    (⟪(N₁ - ContinuousLinearMap.adjoint dj₁) a, x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) d₁₂, x⟫_ℝ +
        ⟪(N₂ - ContinuousLinearMap.adjoint dj₂) a, j x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) d₂₂, j x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) a, dj₂ x⟫_ℝ -
        ⟪(M - ContinuousLinearMap.adjoint j) a, s x⟫_ℝ +
        ⟪(M - ContinuousLinearMap.adjoint j) a, y⟫_ℝ) +
      (⟪a, dj₂ (j x) + j (dj₂ x)⟫_ℝ + ⟪d₂₂, j (j x) + x⟫_ℝ) := by
  simp only [sub_apply, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_right, ContinuousLinearMap.adjoint_inner_left]
  ring

/-- The pairing `⟪D* ψ, ξ⟫ - ⟪ψ, η⟫` for `ψ = ∂_s Φ - M ∂_t Φ`, compared with the
divergence-form pairing: the difference is the remainder term at `(M - Jᵀ, ∂M - (∂J)ᵀ)` plus a
term that vanishes when `J² = -1` and `(∂_t J) J + J (∂_t J) = 0`. -/
private theorem pairing_crTestField_add_eq (Φ : 𝓓(Ω, V)) {M : ℂ → V →L[ℝ] V}
    (hM : ContDiff ℝ ∞ M) (z : ℂ) :
    (⟪crFormalAdjoint J DJ S (crTestField Φ hM) z, ξ z⟫_ℝ - ⟪crTestField Φ hM z, η z⟫_ℝ) +
        (⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ + (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
          ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ)) =
      remainder J DJ S ξ η Φ z (M z - adjointCLM (J z)) (fderiv ℝ M z - adjointCLM.comp (DJ z)) +
        (⟪fderiv ℝ (Φ : ℂ → V) z I, (DJ z I ∘L J z + J z ∘L DJ z I) (ξ z)⟫_ℝ +
          ⟪fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I, (J z ∘L J z + 1) (ξ z)⟫_ℝ) := by
  rw [inner_crFormalAdjoint, fderiv_crTestField, fderiv_crTestField, crTestField_apply,
    laplacian_testFunction, fderiv_fderiv_I_one, crDivergenceFst_apply, crDivergenceSnd_apply]
  simp only [remainder, sub_apply, ContinuousLinearMap.comp_apply, adjointCLM_apply, add_apply,
    one_apply_eq_self]
  exact pairing_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The weak equation in divergence form, tested against vector fields.** Let `ξ` be a weak
solution of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, where `J` is continuous with `J² = -1`, the
coefficients are locally `W^{1,p}` and `Lᵖ` for a finite `p > 2`, and `1/p + 1/q ≤ 1`. Then for
every test function `Φ ∈ 𝓓(Ω, V)`,

`∫ ⟪Δ Φ, ξ⟫ = -∫ (⟪∂_s Φ, f⟫ + ⟪∂_t Φ, g⟫)`

with `f = TauCeti.crDivergenceFst DJ S ξ η` and `g = TauCeti.crDivergenceSnd J DJ S ξ η`. -/
theorem IsWeakCRSolution.integral_inner_laplacian_eq [FiniteDimensional ℝ V]
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJc : ContinuousOn J Ω)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -1) (Φ : 𝓓(Ω, V)) :
    ∫ z, ⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ =
      -∫ z, (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
        ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξ := h.memLpLoc
  have hξi : LocallyIntegrableOn ξ Ω := hξ.locallyIntegrableOn hq1 hloc
  have hf := locallyIntegrableOn_crDivergenceFst hc hpq hξ h.locallyIntegrableOn
  have hg := locallyIntegrableOn_crDivergenceSnd hc hJc hpq hξ h.locallyIntegrableOn
  obtain ⟨K, hKdef⟩ : ∃ K, K = tsupport (Φ : ℂ → V) := ⟨_, rfl⟩
  have hK : IsCompact K := hKdef ▸ Φ.hasCompactSupport
  have hKΩ : K ⊆ Ω := hKdef ▸ Φ.tsupport_subset
  have hKm : MeasurableSet K := hK.measurableSet
  have hΦ0 : ∀ z ∉ K, fderiv ℝ (Φ : ℂ → V) z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport ℝ (hKdef ▸ hz)
  have hΦ00 : ∀ z ∉ K, fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z = 0 := fun z hz =>
    fderiv_of_notMem_tsupport ℝ fun h' => hz (hKdef ▸ tsupport_fderiv_subset ℝ h')
  obtain ⟨C, hC⟩ := exists_bound_fderiv_testFunction Φ
  -- the adjoint field `A = Jᵀ` and its smooth approximations `A' n`
  have hA : HasWeakFDerivOn volume Ω (fun z => adjointCLM (J z))
      (fun z => adjointCLM.comp (DJ z)) := hc.hasWeakFDerivOn.clm_comp adjointCLM
  have hAc : ContinuousOn (fun z => adjointCLM (J z)) Ω :=
    adjointCLM.continuous.comp_continuousOn hJc
  have hDA : MemLpLoc p Ω (fun z => adjointCLM.comp (DJ z)) :=
    hc.memLpLoc_deriv.continuousOn_clm_comp continuousOn_const
  obtain ⟨A', hA's, hA'u, hA'd⟩ :=
    hA.exists_contDiff_tendsto_of_continuousOn hp_top hAc hDA hK hKΩ
  -- the integrands
  let Fl : ℂ → ℝ := fun z => -(⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ +
    (⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
      ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ))
  let Fn : ℕ → ℂ → ℝ := fun n z => ⟪crFormalAdjoint J DJ S (crTestField Φ (hA's n)) z, ξ z⟫_ℝ -
    ⟪crTestField Φ (hA's n) z, η z⟫_ℝ
  have hΔi : Integrable (fun z => ⟪Δ (Φ : ℂ → V) z, ξ z⟫_ℝ) := by
    have := (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, V) Φ).integrable_inner hξi
    simpa only [TestFunction.laplacianCLM_apply] using this
  have hfgi : Integrable (fun z => ⟪fderiv ℝ (Φ : ℂ → V) z 1, crDivergenceFst DJ S ξ η z⟫_ℝ +
      ⟪fderiv ℝ (Φ : ℂ → V) z I, crDivergenceSnd J DJ S ξ η z⟫_ℝ) :=
    (Φ.integrable_inner_fderiv hf 1).add (Φ.integrable_inner_fderiv hg I)
  have hFl : Integrable Fl := (hΔi.add hfgi).neg
  have hFni : ∀ n, Integrable (Fn n) := fun n =>
    (h.integrable_inner_crFormalAdjoint _).sub ((crTestField Φ (hA's n)).integrable_inner
      h.locallyIntegrableOn)
  have hFn0 : ∀ n, ∫ z, Fn n z = 0 := fun n => by
    simp only [Fn]
    rw [integral_sub (h.integrable_inner_crFormalAdjoint _)
      ((crTestField Φ (hA's n)).integrable_inner h.locallyIntegrableOn),
      h.integral_inner_crFormalAdjoint, sub_self]
  -- the error term, which vanishes by `J² = -1` and its derivative
  let E : ℂ → ℝ := fun z =>
    ⟪fderiv ℝ (Φ : ℂ → V) z I, (DJ z I ∘L J z + J z ∘L DJ z I) (ξ z)⟫_ℝ +
      ⟪fderiv ℝ (fderiv ℝ (Φ : ℂ → V)) z I I, (J z ∘L J z + 1) (ξ z)⟫_ℝ
  have hE : ∀ᵐ z, E z = 0 := by
    have hda := hc.ae_deriv_comp_add_comp_deriv_eq_zero hp hp_top hJ
    rw [ae_restrict_iff' Ω.isOpen.measurableSet] at hda
    filter_upwards [hda] with z hz
    by_cases hzK : z ∈ K
    · have hzΩ : z ∈ (Ω : Set ℂ) := hKΩ hzK
      simp only [E]
      rw [hz hzΩ I, hJ z hzΩ]
      simp
    · simp [E, hΦ0 z hzK, hΦ00 z hzK]
  have hdecomp : ∀ n, ∀ᵐ z, Fn n z - Fl z = remainder J DJ S ξ η Φ z
      (A' n z - adjointCLM (J z)) (fderiv ℝ (A' n) z - adjointCLM.comp (DJ z)) := fun n => by
    filter_upwards [hE] with z hz
    have := pairing_crTestField_add_eq (J := J) (DJ := DJ) (S := S) (ξ := ξ) (η := η) Φ (hA's n) z
    simp only [E] at hz
    rw [hz, add_zero] at this
    simp only [Fn, Fl, sub_neg_eq_add]
    exact this
  -- the bounds
  have hb : ∀ n, ∀ᵐ z, ‖Fn n z - Fl z‖ₑ ≤ K.indicator (fun z =>
      ‖fderiv ℝ (A' n) z - adjointCLM.comp (DJ z)‖ₑ * ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ +
        ‖A' n z - adjointCLM (J z)‖ₑ *
          ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ) z := fun n => by
    filter_upwards [hdecomp n] with z hz
    rw [hz]
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
      obtain ⟨hC1, hC2, hC3⟩ := hC z
      exact enorm_remainder_le hC1 hC2 hC3 _ _
    · rw [indicator_of_notMem hzK]
      simp [remainder, hΦ0 z hzK, hΦ00 z hzK]
  -- the weights are in `L^{p'}(K)` and `L¹(K)`
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hξK : MemLp ξ q (volume.restrict K) := memLpLoc_iff.1 hξ K hKΩ hK
  have hJξK : MemLp (fun z => J z (ξ z)) q (volume.restrict K) :=
    memLpLoc_iff.1 (memLpLoc_apply_of_continuousOn hJc hξ) K hKΩ hK
  have hqp : p.conjExponent ≤ q := by
    rw [← ENNReal.inv_le_inv, ← ENNReal.HolderConjugate.one_sub_inv p p.conjExponent]
    exact ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_two.trans hp).ne') hpq
  have hw₁ : MemLp (fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖)) p.conjExponent (volume.restrict K) :=
    ((hξK.mono_exponent hqp).norm.add (hJξK.mono_exponent hqp).norm).const_mul C
  have hint : ∀ {w : ℂ → V}, LocallyIntegrableOn w Ω →
      MemLp (fun z => ‖w z‖) 1 (volume.restrict K) := fun hw =>
    (memLp_one_iff_integrable.2 (hw.integrableOn_compact_subset hKΩ hK)).norm
  have hw₂ : MemLp (fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)) 1
      (volume.restrict K) :=
    (((((hξK.mono_exponent hq1).norm.add (hJξK.mono_exponent hq1).norm).add
      (hint ((memLpLoc_deriv_apply hc.memLpLoc_deriv I).locallyIntegrableOn_clm_apply hξ hpq
        hloc))).add
      (hint (hc.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ hpq hloc))).add
      (hint h.locallyIntegrableOn)).const_mul C
  have hmeas : ∀ n, AEMeasurable (fun z => ‖fderiv ℝ (A' n) z - adjointCLM.comp (DJ z)‖ₑ *
      ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ) (volume.restrict K) := fun n =>
    ((((hA's n).continuous_fderiv (by simp)).aestronglyMeasurable.sub
      (memLpLoc_iff.1 hDA K hKΩ hK).aestronglyMeasurable).eNorm).mul
      hw₁.aestronglyMeasurable.eNorm
  -- the two error terms tend to zero
  have hlim₁ : Tendsto (fun n => ∫⁻ z in K, ‖fderiv ℝ (A' n) z - adjointCLM.comp (DJ z)‖ₑ *
      ‖C * (‖ξ z‖ + ‖J z (ξ z)‖)‖ₑ) atTop (𝓝 0) :=
    tendsto_lintegral_enorm_mul (a := p) (b := p.conjExponent)
      (X := fun n => fderiv ℝ (A' n) - fun z => adjointCLM.comp (DJ z))
      (g := fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖)) hw₁.eLpNorm_ne_top hA'd
  have hlim₂ : Tendsto (fun n => ∫⁻ z in K, ‖A' n z - adjointCLM (J z)‖ₑ *
      ‖C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖)‖ₑ) atTop (𝓝 0) :=
    tendsto_lintegral_enorm_mul (a := ∞) (b := 1) (X := fun n => A' n - fun z => adjointCLM (J z))
      (g := fun z => C * (‖ξ z‖ + ‖J z (ξ z)‖ + ‖DJ z I (ξ z)‖ + ‖S z (ξ z)‖ + ‖η z‖))
      hw₂.eLpNorm_ne_top hA'u
  have hL1 : Tendsto (fun n => ∫⁻ z, ‖Fn n z - Fl z‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [add_zero] using hlim₁.add hlim₂) (fun _ => by simp) fun n => ?_
    refine (lintegral_mono_ae (hb n)).trans_eq ?_
    rw [lintegral_indicator hKm, lintegral_add_left' (hmeas n)]
  -- pass to the limit in `∫ Fn n = 0`
  have hlim := tendsto_integral_of_L1 Fl hFl.aestronglyMeasurable (Eventually.of_forall hFni) hL1
  simp only [hFn0] at hlim
  have h0 : ∫ z, Fl z = 0 := (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  simp only [Fl] at h0
  rw [integral_neg, neg_eq_zero, integral_add hΔi hfgi] at h0
  linarith

/-- **The weak equation in divergence form.** Let `ξ` be a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω`, where `J` is continuous with `J² = -1`, the coefficients are
locally `W^{1,p}` and `Lᵖ` for a finite `p > 2`, and `1/p + 1/q ≤ 1`. Then `ξ` solves
`Δ ξ = ∂_s f + ∂_t g` in the sense of distributions: for every real test function
`φ ∈ 𝓓(Ω, ℝ)`,

`∫ Δ φ • ξ = -∫ (∂_s φ • f + ∂_t φ • g)`

with `f = TauCeti.crDivergenceFst DJ S ξ η` and `g = TauCeti.crDivergenceSnd J DJ S ξ η`. This
is the hypothesis of the divergence-form Laplace regularity
`TauCeti.exists_memLpLoc_weaklyHarmonicOn_sub_of_integral_laplacian_smul_eq`. -/
theorem IsWeakCRSolution.integral_laplacian_smul_eq [FiniteDimensional ℝ V]
    (h : IsWeakCRSolution q Ω J DJ S ξ η) (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJc : ContinuousOn J Ω)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -1) (φ : 𝓓(Ω, ℝ)) :
    ∫ z, Δ (φ : ℂ → ℝ) z • ξ z =
      -∫ z, (fderiv ℝ (φ : ℂ → ℝ) z 1 • crDivergenceFst DJ S ξ η z +
        fderiv ℝ (φ : ℂ → ℝ) z I • crDivergenceSnd J DJ S ξ η z) := by
  have hq1 : 1 ≤ q := ENNReal.inv_le_one.1 (le_add_self.trans hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hξi : LocallyIntegrableOn ξ Ω := h.memLpLoc.locallyIntegrableOn hq1 hloc
  have hf := locallyIntegrableOn_crDivergenceFst hc hpq h.memLpLoc h.locallyIntegrableOn
  have hg := locallyIntegrableOn_crDivergenceSnd hc hJc hpq h.memLpLoc h.locallyIntegrableOn
  have hΔi : Integrable (fun z => Δ (φ : ℂ → ℝ) z • ξ z) := by
    have := (LineDeriv.laplacianCLM ℝ ℂ 𝓓(Ω, ℝ) φ).integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ) hξi
    simpa only [TestFunction.laplacianCLM_apply, ContinuousLinearMap.lsmul_apply] using this
  have hfgi : Integrable (fun z => fderiv ℝ (φ : ℂ → ℝ) z 1 • crDivergenceFst DJ S ξ η z +
      fderiv ℝ (φ : ℂ → ℝ) z I • crDivergenceSnd J DJ S ξ η z) := by
    have h1 := (TestFunction.lineDerivCLM ℝ 1 φ : 𝓓(Ω, ℝ)).integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ) hf
    have h2 := (TestFunction.lineDerivCLM ℝ I φ : 𝓓(Ω, ℝ)).integrable_bilin
      (ContinuousLinearMap.lsmul ℝ ℝ) hg
    simp only [TestFunction.coe_lineDerivCLM, TestFunction.lineDeriv_eq_fderiv,
      ContinuousLinearMap.lsmul_apply] at h1 h2
    exact h1.add h2
  refine ext_inner_left ℝ fun w => ?_
  have key := h.integral_inner_laplacian_eq hc hp hp_top hpq hJc hJ
    (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) φ)
  have hcoe : ((TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ w) φ :
      𝓓(Ω, V)) : ℂ → V) = fun z => φ z • w := by
    funext z
    simp
  have hΔ : ∀ z, Δ (fun z => φ z • w) z = Δ (φ : ℂ → ℝ) z • w := fun z => by
    have hφ2 : ContDiff ℝ 2 (φ : ℂ → ℝ) := φ.contDiff.of_le (by simp)
    have := hφ2.contDiffAt.laplacian_CLM_comp_left
      (l := ContinuousLinearMap.toSpanSingleton ℝ w) (x := z)
    simpa [Function.comp_def] using this
  have hd : ∀ z v, fderiv ℝ (fun z => φ z • w) z v = fderiv ℝ (φ : ℂ → ℝ) z v • w := fun z v => by
    rw [fderiv_smul_const ((φ.contDiff.differentiable (by simp)).differentiableAt)]
    simp
  rw [hcoe] at key
  simp only [hΔ, hd, real_inner_smul_left] at key
  rw [← integral_inner hΔi w, inner_neg_right, ← integral_inner hfgi w]
  simpa only [real_inner_smul_right, inner_add_right] using key

end DivergenceForm

end TauCeti

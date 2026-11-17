/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Prod

/-!
# Non-stationary phase in several variables, uniformly in a parameter

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let `F` be
a real normed space of parameters. For a smooth amplitude `a : F × E → ℂ` and a smooth real phase
`θ : F × E → ℝ`, consider the oscillatory integrals

`I(p, t) = ∫ a(p, x) 𝐞(t θ(p, x)) dμ(x)`,

where `𝐞 s = exp (2πi s)`. If the amplitudes are supported, in `x`, in a fixed compact set and the
phase has no critical point in `x` on the support of `a`, then `I(p, t)` decays faster than every
power of `t`, uniformly for `p` in a compact set:

`|t| ^ N ‖I(p, t)‖ ≤ C_N` for `p ∈ P` and all real `t`

(`TauCeti.exists_forall_abs_pow_mul_norm_integral_le`). This is the principle of non-stationary
phase. The proof integrates by parts in `x`. Fix a basis `b` of `E`, write `∂_k` for the partial
derivative in the direction `b k`, and put `S = ∑ k (∂_k θ) ^ 2`, which does not vanish on the
support of `a`. Since `∂_k 𝐞(t θ) = 2πi t (∂_k θ) 𝐞(t θ)`,

`2πi t ∫ a 𝐞(t θ) = ∑ k ∫ (a ∂_k θ / S) ∂_k 𝐞(t θ) = -∑ k ∫ ∂_k (a ∂_k θ / S) 𝐞(t θ)`,

so `I(p, t) = t⁻¹ ∫ (D a)(p, x) 𝐞(t θ(p, x)) dμ(x)` for the amplitude
`D a = -(2πi)⁻¹ ∑ k ∂_k (a ∂_k θ / S)`. This amplitude is again smooth, with support in that of `a`,
so `N` steps give `I(p, t) = t ^ (-N) ∫ (D ^ N a) 𝐞(t θ)`. The remaining integral is bounded
uniformly in `p ∈ P` because `D ^ N a` is continuous and the set of `(p, x)` with `p ∈ P` and `x` in
the fixed compact set is compact. No bookkeeping of the derivatives of `D ^ N a` is needed.

Uniformity in the parameter is what applications use: there the phase is a family such as
`θ((s, w), x) = s φ(x) + ⟪x, w⟫` over a compact set of directions `(s, w)`.

## Main results

* `TauCeti.exists_forall_abs_pow_mul_norm_integral_le`: rapid decay of `I(p, t)` in `t`,
  uniformly for `p` in a compact set.
* `TauCeti.exists_forall_abs_pow_mul_norm_integral_le_of_isCompact`: the same for an amplitude
  `ψ(x)` independent of the parameter, when the phase is only known to have no critical points
  over the compact parameter set; a cutoff in the parameter reduces it to the previous case.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 7.7.1.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter VIII, §2.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set Function Complex Real
open scoped ContDiff FourierTransform Topology

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace NonstationaryPhase

/-- The partial derivative of `f : F × E → G` at `q` in its second variable, in the direction `v`:
the derivative of the slice `y ↦ f (q.1, y)` at `q.2`. -/
private def partialDeriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (f : F × E → G)
    (v : E) (q : F × E) : G :=
  fderiv ℝ (fun y ↦ f (q.1, y)) q.2 v

private theorem contDiff_partialDeriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F × E → G} (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (partialDeriv f v) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hf.contDiffAt.fderiv_snd_apply le_rfl v

omit [NormedSpace ℝ F] in
private theorem tsupport_partialDeriv_subset {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (f : F × E → G) (v : E) : tsupport (partialDeriv f v) ⊆ tsupport f := by
  refine closure_minimal (fun q hq ↦ by_contra fun hqf ↦ hq ?_) (isClosed_tsupport f)
  -- Near a point outside the support of `f`, the slice through it vanishes.
  have h : (fun y ↦ f (q.1, y)) =ᶠ[𝓝 q.2] fun _ ↦ 0 :=
    (notMem_tsupport_iff_eventuallyEq.1 hqf).comp_tendsto
      (continuous_const.prodMk continuous_id).continuousAt
  simp [partialDeriv, h.fderiv_eq]

variable [FiniteDimensional ℝ E]

variable (E) in
/-- The basis of `E` in which the partial derivatives are taken. -/
private abbrev basis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E

/-- The sum of the squares of the partial derivatives of `θ` along the basis. -/
private def gradSq (θ : F × E → ℝ) (q : F × E) : ℝ :=
  ∑ k, partialDeriv θ (basis E k) q ^ 2

private theorem contDiff_gradSq {θ : F × E → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ (gradSq θ) :=
  ContDiff.sum fun _ _ ↦ (contDiff_partialDeriv hθ _).pow 2

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- `gradSq θ` vanishes only where the partial derivative of `θ` in its second variable does. -/
private theorem gradSq_ne_zero {θ : F × E → ℝ} {q : F × E}
    (h : fderiv ℝ (fun x ↦ θ (q.1, x)) q.2 ≠ 0) : gradSq θ q ≠ 0 := by
  intro h0
  have hk : ∀ k, partialDeriv θ (basis E k) q = 0 := fun k ↦
    pow_eq_zero_iff two_ne_zero |>.1 <| (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      sq_nonneg (partialDeriv θ (basis E i) q)).1 (by simpa only [gradSq] using h0) k
        (Finset.mem_univ k)
  exact h (ContinuousLinearMap.coe_injective ((basis E).ext fun k ↦ by
    simpa [partialDeriv] using hk k))

/-- The amplitude `a ∂_k θ / gradSq θ` integrated by parts against the `k`-th partial derivative. -/
private def flux (θ : F × E → ℝ) (a : F × E → ℂ) (k : Fin (Module.finrank ℝ E)) (q : F × E) : ℂ :=
  ((partialDeriv θ (basis E k) q / gradSq θ q : ℝ) : ℂ) * a q

private theorem contDiff_flux {θ : F × E → ℝ} {a : F × E → ℂ} (hθ : ContDiff ℝ ∞ θ)
    (ha : ContDiff ℝ ∞ a) (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) (k : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ ∞ (flux θ a k) := by
  have hs : IsOpen {q : F × E | gradSq θ q ≠ 0} :=
    isOpen_ne_fun (contDiff_gradSq hθ).continuous continuous_const
  have hr : ContDiffOn ℝ ∞ (fun q ↦ ((partialDeriv θ (basis E k) q / gradSq θ q : ℝ) : ℂ))
      {q | gradSq θ q ≠ 0} :=
    ofRealCLM.contDiff.comp_contDiffOn
      ((contDiff_partialDeriv hθ _).contDiffOn.div (contDiff_gradSq hθ).contDiffOn fun _ hq ↦ hq)
  exact (ContinuousLinearMap.mul ℝ ℂ).contDiff_of_tsupport_subset_right hr ha.contDiffOn hs hθa

omit [NormedSpace ℝ F] in
private theorem tsupport_flux_subset (θ : F × E → ℝ) (a : F × E → ℂ)
    (k : Fin (Module.finrank ℝ E)) :
    tsupport (flux θ a k) ⊆ tsupport a :=
  tsupport_mul_subset_right

/-- The transposed amplitude `D a = -(2πi)⁻¹ ∑ k ∂_k (a ∂_k θ / gradSq θ)`: integrating `a` against
`𝐞(t θ)` is integrating `D a` against `𝐞(t θ)` and dividing by `t`. -/
private def transposeAmp (θ : F × E → ℝ) (a : F × E → ℂ) (q : F × E) : ℂ :=
  -(2 * π * I)⁻¹ * ∑ k, partialDeriv (flux θ a k) (basis E k) q

private theorem contDiff_transposeAmp {θ : F × E → ℝ} {a : F × E → ℂ} (hθ : ContDiff ℝ ∞ θ)
    (ha : ContDiff ℝ ∞ a) (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) :
    ContDiff ℝ ∞ (transposeAmp θ a) :=
  contDiff_const.mul <| ContDiff.sum fun k _ ↦
    contDiff_partialDeriv (contDiff_flux hθ ha hθa k) _

omit [NormedSpace ℝ F] in
private theorem tsupport_transposeAmp_subset (θ : F × E → ℝ) (a : F × E → ℂ) :
    tsupport (transposeAmp θ a) ⊆ tsupport a := by
  refine closure_minimal (fun q hq ↦ by_contra fun hqa ↦ hq ?_) (isClosed_tsupport a)
  have hk (k) : partialDeriv (flux θ a k) (basis E k) q = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦
      hqa ((tsupport_partialDeriv_subset _ _).trans (tsupport_flux_subset θ a k) h)
  simp [transposeAmp, hk]

omit [FiniteDimensional ℝ E] in
/-- The derivative in `x` of the oscillating factor `𝐞(t θ(p, x))`. -/
private theorem hasFDerivAt_fourierChar {θ : F × E → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : F) (t : ℝ)
    (x : E) :
    HasFDerivAt (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ))
      (((2 * π * t * I) * (𝐞 (t * θ (p, x)) : ℂ)) •
        (ofRealCLM.comp (fderiv ℝ (fun y ↦ θ (p, y)) x))) x := by
  have hθx : HasFDerivAt (fun y ↦ θ (p, y)) (fderiv ℝ (fun y ↦ θ (p, y)) x) x :=
    ((hθ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x).hasFDerivAt
  have h := ((ofRealCLM.hasFDerivAt.comp x ((hθx.const_mul (2 * π * t)))).mul_const I).cexp
  convert h using 1
  · ext y
    simp [Real.fourierChar_apply]
    ring_nf
  · ext v
    simp [Real.fourierChar_apply]
    ring_nf

omit [FiniteDimensional ℝ E] in
private theorem fderiv_fourierChar_apply {θ : F × E → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : F) (t : ℝ)
    (x v : E) :
    fderiv ℝ (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ)) x v =
      2 * π * t * I * partialDeriv θ v (p, x) * 𝐞 (t * θ (p, x)) := by
  rw [(hasFDerivAt_fourierChar hθ p t x).fderiv]
  simp [partialDeriv]
  ring

omit [FiniteDimensional ℝ E] in
private theorem contDiff_fourierChar_slice {θ : F × E → ℝ} (hθ : ContDiff ℝ ∞ θ) (p : F)
    (t : ℝ) : ContDiff ℝ ∞ fun y ↦ (𝐞 (t * θ (p, y)) : ℂ) := by
  have h : (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ)) =
      fun y ↦ cexp (((2 * π * (t * θ (p, y)) : ℝ) : ℂ) * I) := by
    ext y
    simp [Real.fourierChar_apply]
  rw [h]
  exact Complex.contDiff_exp.comp ((ofRealCLM.contDiff.comp (contDiff_const.mul
    (contDiff_const.mul (hθ.comp (contDiff_const.prodMk contDiff_id))))).mul contDiff_const)

/-- The pointwise identity behind the integration by parts:
`∑ k (a ∂_k θ / gradSq θ) ∂_k 𝐞(t θ) = 2πi t a 𝐞(t θ)`. -/
private theorem sum_flux_mul_fderiv {θ : F × E → ℝ} {a : F × E → ℂ} (hθ : ContDiff ℝ ∞ θ)
    (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) (p : F) (t : ℝ) (x : E) :
    ∑ k, flux θ a k (p, x) * fderiv ℝ (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ)) x (basis E k) =
      2 * π * t * I * (a (p, x) * 𝐞 (t * θ (p, x))) := by
  by_cases ha : a (p, x) = 0
  · simp [flux, ha]
  have hS := hθa _ (subset_tsupport _ ha)
  simp_rw [fderiv_fourierChar_apply hθ, flux]
  have hsum : ∑ k, ((partialDeriv θ (basis E k) (p, x) / gradSq θ (p, x) : ℝ) : ℂ) * a (p, x) *
      (2 * π * t * I * partialDeriv θ (basis E k) (p, x) * 𝐞 (t * θ (p, x))) =
      ((∑ k, partialDeriv θ (basis E k) (p, x) ^ 2 : ℝ) : ℂ) / (gradSq θ (p, x) : ℂ) *
        (2 * π * t * I * (a (p, x) * 𝐞 (t * θ (p, x)))) := by
    rw [ofReal_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  rw [hsum, show (∑ k, partialDeriv θ (basis E k) (p, x) ^ 2 : ℝ) = gradSq θ (p, x) from rfl,
    div_self (ofReal_ne_zero.2 hS), one_mul]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] in
/-- A function of `x` that is the restriction of `f` to a slice, where the topological support of
`f` lies over the compact set `K`, has compact support. -/
private theorem hasCompactSupport_slice {G : Type*} [NormedAddCommGroup G] {f : F × E → G}
    {K : Set E} (hK : IsCompact K) (hfK : tsupport f ⊆ univ ×ˢ K) (p : F) :
    HasCompactSupport fun x ↦ f (p, x) :=
  HasCompactSupport.intro hK fun _ hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hfK h).2

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **One integration by parts.** For `t ≠ 0`,
`∫ a(p, x) 𝐞(t θ(p, x)) = t⁻¹ ∫ (D a)(p, x) 𝐞(t θ(p, x))`. -/
private theorem integral_eq_inv_mul_integral_transposeAmp {θ : F × E → ℝ} {a : F × E → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (ha : ContDiff ℝ ∞ a) {K : Set E} (hK : IsCompact K)
    (haK : tsupport a ⊆ univ ×ˢ K) (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) (p : F) {t : ℝ}
    (ht : t ≠ 0) :
    ∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ =
      t⁻¹ * ∫ x, transposeAmp θ a (p, x) * 𝐞 (t * θ (p, x)) ∂μ := by
  set g : E → ℂ := fun y ↦ (𝐞 (t * θ (p, y)) : ℂ) with hg_def
  have hg : ContDiff ℝ ∞ g := contDiff_fourierChar_slice hθ p t
  have hfl (k : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ fun x ↦ flux θ a k (p, x) :=
    (contDiff_flux hθ ha hθa k).comp (contDiff_const.prodMk contDiff_id)
  have hflK (k : Fin (Module.finrank ℝ E)) : HasCompactSupport fun x ↦ flux θ a k (p, x) :=
    hasCompactSupport_slice hK ((tsupport_flux_subset θ a k).trans haK) p
  have hint₁ (k : Fin (Module.finrank ℝ E)) :
      Integrable (fun x ↦ fderiv ℝ (fun y ↦ flux θ a k (p, y)) x (basis E k) * g x) μ :=
    ((((hfl k).continuous_fderiv (by simp)).clm_apply continuous_const).mul
      hg.continuous).integrable_of_hasCompactSupport ((hflK k).fderiv_apply (𝕜 := ℝ) _).mul_right
  have hint₂ (k : Fin (Module.finrank ℝ E)) :
      Integrable (fun x ↦ flux θ a k (p, x) * fderiv ℝ g x (basis E k)) μ :=
    ((hfl k).continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport (hflK k).mul_right
  have hint₃ (k : Fin (Module.finrank ℝ E)) :
      Integrable (fun x ↦ flux θ a k (p, x) * g x) μ :=
    ((hfl k).continuous.mul hg.continuous).integrable_of_hasCompactSupport (hflK k).mul_right
  -- One integration by parts in each basis direction.
  have hibp (k : Fin (Module.finrank ℝ E)) :
      ∫ x, flux θ a k (p, x) * fderiv ℝ g x (basis E k) ∂μ =
        -∫ x, partialDeriv (flux θ a k) (basis E k) (p, x) * g x ∂μ := by
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint₁ k) (hint₂ k) (hint₃ k)
      (fun x _ ↦ (hfl k).differentiable (by simp) x) (fun x _ ↦ hg.differentiable (by simp) x)]
    rfl
  have hsum : ∫ x, ∑ k, partialDeriv (flux θ a k) (basis E k) (p, x) * g x ∂μ =
      -(2 * π * t * I * ∫ x, a (p, x) * g x ∂μ) := by
    rw [← neg_eq_iff_eq_neg, eq_comm, ← integral_const_mul]
    simp_rw [hg_def, ← sum_flux_mul_fderiv hθ hθa p t, ← hg_def]
    rw [integral_finsetSum _ fun k _ ↦ hint₂ k, integral_finsetSum _ fun k _ ↦ ?_,
      ← Finset.sum_neg_distrib]
    · exact Finset.sum_congr rfl fun k _ ↦ hibp k
    · exact hint₁ k
  have hD : ∫ x, transposeAmp θ a (p, x) * g x ∂μ =
      -(2 * π * I)⁻¹ * ∫ x, ∑ k, partialDeriv (flux θ a k) (basis E k) (p, x) * g x ∂μ := by
    rw [← integral_const_mul]
    congr 1
    ext x
    simp [transposeAmp, Finset.sum_mul, mul_assoc]
  rw [hD, hsum]
  field_simp
  rw [one_div, ofReal_inv, inv_mul_cancel₀ (ofReal_ne_zero.2 ht), one_mul]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ E] in
/-- The integrals are bounded, uniformly in `p ∈ P` and `t`: by the supremum of `‖a‖` over
`P × K` times the measure of `K`. -/
private theorem exists_forall_norm_integral_le {a : F × E → ℂ} (ha : Continuous a) {K : Set E}
    (hK : IsCompact K) (haK : tsupport a ⊆ univ ×ˢ K) {P : Set F} (hP : IsCompact P)
    (θ : F × E → ℝ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, ‖∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
  obtain ⟨M, hM⟩ := (hP.prod hK).exists_bound_of_continuousOn ha.continuousOn
  refine ⟨M * μ.real K, fun p hp t ↦ ?_⟩
  have hle (x : E) : ‖a (p, x) * 𝐞 (t * θ (p, x))‖ ≤ K.indicator (fun _ ↦ M) x := by
    by_cases hx : x ∈ K
    · simpa [hx] using hM (p, x) ⟨hp, hx⟩
    · have h0 : a (p, x) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (haK h).2
      simp [hx, h0]
  calc ‖∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ ∫ x, K.indicator (fun _ ↦ M) x ∂μ :=
        norm_integral_le_of_norm_le ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator
          hK.measurableSet) (Filter.Eventually.of_forall hle)
    _ = M * μ.real K := by rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, mul_comm]

end NonstationaryPhase

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

open NonstationaryPhase in
/-- **Non-stationary phase, uniformly in a parameter.** Let `a : F × E → ℂ` and `θ : F × E → ℝ` be
smooth, with the support of `a` lying over a compact set `K` in the second variable, and suppose
that `x ↦ θ (p, x)` has no critical point at any `(p, x)` in the support of `a`. Then for every
`N` the oscillatory integral `∫ a(p, x) 𝐞(t θ(p, x)) dμ(x)` is `O(|t| ^ (-N))`, uniformly for `p`
in a compact set `P`. -/
theorem exists_forall_abs_pow_mul_norm_integral_le {a : F × E → ℂ} {θ : F × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hθ : ContDiff ℝ ∞ θ) {K : Set E} (hK : IsCompact K)
    (haK : tsupport a ⊆ univ ×ˢ K)
    (hθa : ∀ q ∈ tsupport a, fderiv ℝ (fun x ↦ θ (q.1, x)) q.2 ≠ 0) {P : Set F}
    (hP : IsCompact P) (N : ℕ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, |t| ^ N * ‖∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
  replace hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0 := fun q hq ↦ gradSq_ne_zero (hθa q hq)
  induction N generalizing a with
  | zero => simpa using exists_forall_norm_integral_le ha.continuous hK haK hP θ
  | succ N ih =>
    -- Integrate by parts once, and apply the bound for `N` to the transposed amplitude.
    have hD := tsupport_transposeAmp_subset θ a
    obtain ⟨C, hC⟩ := ih (contDiff_transposeAmp hθ ha hθa) (hD.trans haK)
      fun q hq ↦ hθa q (hD hq)
    refine ⟨max C 0, fun p hp t ↦ ?_⟩
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    rw [integral_eq_inv_mul_integral_transposeAmp hθ ha hK haK hθa p ht, norm_mul,
      Complex.norm_real, norm_inv, Real.norm_eq_abs, pow_succ, mul_assoc, ← mul_assoc |t|,
      mul_inv_cancel₀ (abs_ne_zero.2 ht), one_mul]
    exact (hC p hp t).trans (le_max_left _ _)


/-- **Non-stationary phase for an amplitude independent of the parameter.** Let `ψ` be smooth with
compact support and let `θ : F × E → ℝ` be smooth, with a finite-dimensional parameter space `F`.
If `x ↦ θ (p, x)` has no critical point on the support of `ψ` for `p` in a compact set `P`, then
`∫ ψ(x) 𝐞(t θ(p, x)) dμ(x)` is `O(|t| ^ (-N))` for every `N`, uniformly for `p ∈ P`. -/
theorem exists_forall_abs_pow_mul_norm_integral_le_of_isCompact [FiniteDimensional ℝ F]
    {ψ : E → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {θ : F × E → ℝ}
    (hθ : ContDiff ℝ ∞ θ) {P : Set F} (hP : IsCompact P)
    (hθP : ∀ p ∈ P, ∀ x ∈ tsupport ψ, fderiv ℝ (fun y ↦ θ (p, y)) x ≠ 0) (N : ℕ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, |t| ^ N * ‖∫ x, ψ x * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
  -- The critical points of `θ` in `x` form a closed set, disjoint from `P × tsupport ψ`; cut off
  -- in the parameter to an open neighbourhood `u` of `P` that avoids them over `tsupport ψ`.
  have ho : IsOpen {q : F × E | fderiv ℝ (fun y ↦ θ (q.1, y)) q.2 ≠ 0} :=
    isOpen_ne_fun (continuous_iff_continuousAt.2 fun _ ↦
      (hθ.contDiffAt.fderiv_slice (m := 0) (by simp)).continuousAt) continuous_const
  obtain ⟨u, v, hu, -, hPu, hψv, huv⟩ := generalized_tube_lemma hP hψc.isCompact ho
    fun q hq ↦ hθP q.1 hq.1 q.2 hq.2
  obtain ⟨ρ, hρ, -, hρ1, -, hρu⟩ := hP.exists_contDiff_cutoff hu hPu
  let a : F × E → ℂ := fun q ↦ (ρ q.1 : ℂ) * ψ q.2
  have hsupp : tsupport a ⊆ tsupport ρ ×ˢ tsupport ψ :=
    closure_minimal (fun q hq ↦ ⟨subset_tsupport _ fun h ↦ hq (by simp [a, h]),
      subset_tsupport _ fun h ↦ hq (by simp [a, h])⟩)
      ((isClosed_tsupport _).prod (isClosed_tsupport _))
  obtain ⟨C, hC⟩ := exists_forall_abs_pow_mul_norm_integral_le (μ := μ)
    ((ofRealCLM.contDiff.comp (hρ.comp contDiff_fst)).mul (hψ.comp contDiff_snd)) hθ
    hψc.isCompact (hsupp.trans (prod_mono (subset_univ _) subset_rfl))
    (fun q hq ↦ huv ⟨hρu (hsupp hq).1, hψv (hsupp hq).2⟩) hP N
  refine ⟨C, fun p hp t ↦ ?_⟩
  have hρp : ρ p = 1 := interior_subset (hρ1 hp)
  simpa [a, hρp] using hC p hp t

end TauCeti

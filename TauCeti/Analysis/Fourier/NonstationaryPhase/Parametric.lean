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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Fourier.FourierChar.Deriv
import TauCeti.Topology.Algebra.Support

/-!
# Non-stationary phase in several variables, uniformly in a parameter

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let `F` be
a real normed space of parameters. For a smooth amplitude `a : F × E → ℂ` and a smooth real phase
`θ : F × E → ℝ`, consider the oscillatory integrals

`I(p, t) = ∫ a(p, x) 𝐞(t θ(p, x)) dμ(x)`,

where `𝐞 s = exp (2πi s)`. Let `P` be a compact set of parameters. If the amplitudes are
supported, in `x`, in a fixed compact set and the phase has no critical point in `x` at the points
`(p, x)` of the support of `a` with `p ∈ P`, then `I(p, t)` decays faster than every power of `t`,
uniformly for `p ∈ P`:

`|t| ^ N ‖I(p, t)‖ ≤ C_N` for `p ∈ P` and all real `t`

(`TauCeti.exists_forall_abs_pow_mul_norm_integral_le`). This is the principle of non-stationary
phase. The proof integrates by parts in `x`. Fix a basis `b` of `E`, write `∂_k` for the partial
derivative in the direction `b k`, and put `S = ∑ k (∂_k θ) ^ 2`. By compactness `S ≥ c > 0` on the
support of `a` over `P`; multiplying `a` by a smooth function of `S` that is one where `S ≥ c` and
zero where `S ≤ c / 2` does not change `I(p, t)` for `p ∈ P`, so we may assume that `S` does not
vanish on the support of `a`. Since `∂_k 𝐞(t θ) = 2πi t (∂_k θ) 𝐞(t θ)`,

`2πi t ∫ a 𝐞(t θ) = ∑ k ∫ (a ∂_k θ / S) ∂_k 𝐞(t θ) = -∑ k ∫ ∂_k (a ∂_k θ / S) 𝐞(t θ)`,

so `I(p, t) = t⁻¹ ∫ (D a)(p, x) 𝐞(t θ(p, x)) dμ(x)` for the amplitude
`D a = -(2πi)⁻¹ ∑ k ∂_k (a ∂_k θ / S)`. This amplitude is again smooth, with support in that of `a`,
so `N` steps give `I(p, t) = t ^ (-N) ∫ (D ^ N a) 𝐞(t θ)`. The remaining integral is bounded
uniformly in `p ∈ P` because `D ^ N a` is continuous and the set of `(p, x)` with `p ∈ P` and `x` in
the fixed compact set is compact. No bookkeeping of the derivatives of `D ^ N a` is needed.

Uniformity in the parameter is what applications use: there the phase is a family such as
`θ((s, w), x) = s φ(x) + ⟪x, w⟫` over a compact set of directions `(s, w)`. The phase may depend
nonlinearly on the parameter; `TauCeti.exists_one_add_norm_pow_mul_norm_integral_fourierChar_le`
(`NonstationaryPhase/Basic.lean`) treats the phases `Λ ∘ Φ` that are linear in a covector `Λ`.

## Main results

* `TauCeti.exists_forall_abs_pow_mul_norm_integral_le`: rapid decay of `I(p, t)` in `t`,
  uniformly for `p` in a compact set, when the phase has no critical point in `x` on the support
  of `a` over that set.
* `TauCeti.exists_forall_abs_pow_mul_norm_integral_mul_fourierChar_le`: the same for an amplitude
  `ψ(x)` independent of the parameter.

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
    [NormedSpace ℝ G] (f : F × E → G) (v : E) : tsupport (partialDeriv f v) ⊆ tsupport f :=
  (tsupport_comp_subset (g := fun L : E →L[ℝ] G ↦ L v) rfl _).trans
    (tsupport_fderiv_slice_right_subset (𝕜 := ℝ) fun p y ↦ f (p, y))

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

/-- The pointwise identity behind the integration by parts:
`∑ k (a ∂_k θ / gradSq θ) ∂_k 𝐞(t θ) = 2πi t a 𝐞(t θ)`. -/
private theorem sum_flux_mul_fderiv {θ : F × E → ℝ} {a : F × E → ℂ} (hθ : ContDiff ℝ ∞ θ)
    (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) (p : F) (t : ℝ) (x : E) :
    ∑ k, flux θ a k (p, x) * fderiv ℝ (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ)) x (basis E k) =
      2 * π * t * I * (a (p, x) * 𝐞 (t * θ (p, x))) := by
  by_cases ha : a (p, x) = 0
  · simp [flux, ha]
  have hS := hθa _ (subset_tsupport _ ha)
  have hθp : Differentiable ℝ fun y ↦ θ (p, y) :=
    (hθ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hd (v : E) : fderiv ℝ (fun y ↦ (𝐞 (t * θ (p, y)) : ℂ)) x v =
      2 * π * t * I * partialDeriv θ v (p, x) * 𝐞 (t * θ (p, x)) := by
    rw [Real.fderiv_fourierChar_comp_apply ((hθp x).const_mul t), fderiv_const_mul (hθp x)]
    simp [partialDeriv]
    ring
  simp_rw [hd, flux]
  have hsum : ∑ k, ((partialDeriv θ (basis E k) (p, x) / gradSq θ (p, x) : ℝ) : ℂ) * a (p, x) *
      (2 * π * t * I * partialDeriv θ (basis E k) (p, x) * 𝐞 (t * θ (p, x))) =
      ((∑ k, partialDeriv θ (basis E k) (p, x) ^ 2 : ℝ) : ℂ) / (gradSq θ (p, x) : ℂ) *
        (2 * π * t * I * (a (p, x) * 𝐞 (t * θ (p, x)))) := by
    rw [ofReal_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    ring
  rw [hsum, ← gradSq, div_self (ofReal_ne_zero.2 hS), one_mul]

/-- **Cutting off the nearly stationary points.** If `gradSq θ` vanishes nowhere on the part of the
support of `a` over a compact set `P`, then multiplying `a` by a smooth function of `gradSq θ` gives
an amplitude `b`, equal to `a` over `P`, with `gradSq θ` vanishing nowhere on its support. -/
private theorem exists_eq_and_gradSq_ne_zero {a : F × E → ℂ} {θ : F × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hθ : ContDiff ℝ ∞ θ) {K : Set E} (hK : IsCompact K)
    (haK : tsupport a ⊆ univ ×ˢ K) {P : Set F} (hP : IsCompact P)
    (hθa : ∀ q ∈ tsupport a, q.1 ∈ P → gradSq θ q ≠ 0) :
    ∃ b : F × E → ℂ, ContDiff ℝ ∞ b ∧ tsupport b ⊆ tsupport a ∧
      (∀ q ∈ tsupport b, gradSq θ q ≠ 0) ∧ ∀ p ∈ P, ∀ x, b (p, x) = a (p, x) := by
  have hg := contDiff_gradSq hθ
  -- `gradSq θ` is at least some `c > 0` on the compact part of `tsupport a` over `P`.
  have hS : IsCompact (tsupport a ∩ P ×ˢ univ) :=
    (hP.prod hK).of_isClosed_subset ((isClosed_tsupport a).inter (hP.isClosed.prod isClosed_univ))
      fun q hq ↦ ⟨hq.2.1, (haK hq.1).2⟩
  obtain ⟨c, hc, hcS⟩ := hS.exists_forall_le' hg.continuous.continuousOn (a := 0) fun q hq ↦
    (by simp only [gradSq]; positivity : 0 ≤ gradSq θ q).lt_of_ne' (hθa q hq.1 hq.2.1)
  -- The cutoff is one where `gradSq θ ≥ c` and zero where `gradSq θ ≤ c / 2`.
  let ρ : F × E → ℂ := fun q ↦ (Real.smoothTransition (2 * gradSq θ q / c - 1) : ℂ)
  have hρ : tsupport ρ ⊆ {q | c / 2 ≤ gradSq θ q} := by
    refine closure_minimal (fun q hq ↦ mem_ofPred.2 (not_lt.1 fun h ↦ hq ?_))
      (isClosed_le continuous_const hg.continuous)
    simp only [ρ, ofReal_eq_zero]
    exact Real.smoothTransition.zero_of_nonpos
      (sub_nonpos.2 ((div_le_one hc).2 (by linarith)))
  refine ⟨fun q ↦ ρ q * a q, ?_, tsupport_mul_subset_right, fun q hq ↦ ?_, fun p hp x ↦ ?_⟩
  · exact (ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul hg).div_const c).sub contDiff_const))).mul ha
  · exact (lt_of_lt_of_le (half_pos hc) (hρ (tsupport_mul_subset_left hq))).ne'
  · by_cases ha0 : a (p, x) = 0
    · simp [ha0]
    have h1 : 1 ≤ 2 * gradSq θ (p, x) / c - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hc]
      linarith [hcS (p, x) ⟨subset_tsupport _ ha0, hp, mem_univ _⟩]
    simp [ρ, Real.smoothTransition.one_of_one_le h1]

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
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_const.mul (hθ.comp (contDiff_const.prodMk contDiff_id))).fourierChar
  have hfl (k : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ fun x ↦ flux θ a k (p, x) :=
    (contDiff_flux hθ ha hθa k).comp (contDiff_const.prodMk contDiff_id)
  have hflK (k : Fin (Module.finrank ℝ E)) : HasCompactSupport fun x ↦ flux θ a k (p, x) :=
    .comp_of_forall_mem_imp_mem hK (fun _ hx ↦ (((tsupport_flux_subset θ a k).trans haK) hx).2)
      fun _ ↦ image_eq_zero_of_notMem_tsupport
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
    simp only [partialDeriv]
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

/-- **Non-stationary phase where `gradSq θ` vanishes nowhere on the support of `a`.** This is
`N` integrations by parts; `TauCeti.exists_forall_abs_pow_mul_norm_integral_le` reduces to it by a
cutoff. -/
private theorem exists_forall_abs_pow_mul_norm_integral_le_of_gradSq_ne_zero {a : F × E → ℂ}
    {θ : F × E → ℝ} (ha : ContDiff ℝ ∞ a) (hθ : ContDiff ℝ ∞ θ) {K : Set E} (hK : IsCompact K)
    (haK : tsupport a ⊆ univ ×ˢ K) (hθa : ∀ q ∈ tsupport a, gradSq θ q ≠ 0) {P : Set F}
    (hP : IsCompact P) (N : ℕ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, |t| ^ N * ‖∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
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

end NonstationaryPhase

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

open NonstationaryPhase in
/-- **Non-stationary phase, uniformly in a parameter.** Let `a : F × E → ℂ` and `θ : F × E → ℝ` be
smooth, with the support of `a` lying over a compact set `K` in the second variable, and let `P` be
a compact set of parameters. Suppose that `x ↦ θ (p, x)` has no critical point at any `(p, x)` in
the support of `a` with `p ∈ P`. Then for every `N` the oscillatory integral
`∫ a(p, x) 𝐞(t θ(p, x)) dμ(x)` is `O(|t| ^ (-N))`, uniformly for `p ∈ P`. -/
theorem exists_forall_abs_pow_mul_norm_integral_le {a : F × E → ℂ} {θ : F × E → ℝ}
    (ha : ContDiff ℝ ∞ a) (hθ : ContDiff ℝ ∞ θ) {K : Set E} (hK : IsCompact K)
    (haK : tsupport a ⊆ univ ×ˢ K) {P : Set F} (hP : IsCompact P)
    (hθa : ∀ q ∈ tsupport a, q.1 ∈ P → fderiv ℝ (fun x ↦ θ (q.1, x)) q.2 ≠ 0) (N : ℕ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, |t| ^ N * ‖∫ x, a (p, x) * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
  -- Cut `a` off near the critical points of the phase, which all lie over parameters outside `P`.
  obtain ⟨b, hb, hba, hθb, hab⟩ := exists_eq_and_gradSq_ne_zero ha hθ hK haK hP
    fun q hq hqP ↦ gradSq_ne_zero (hθa q hq hqP)
  obtain ⟨C, hC⟩ := exists_forall_abs_pow_mul_norm_integral_le_of_gradSq_ne_zero (μ := μ) hb hθ hK
    (hba.trans haK) hθb hP N
  exact ⟨C, fun p hp t ↦ by simpa only [hab p hp] using hC p hp t⟩

/-- **Non-stationary phase for an amplitude independent of the parameter.** Let `ψ` be smooth with
compact support and let `θ : F × E → ℝ` be smooth. If `x ↦ θ (p, x)` has no critical point on the
support of `ψ` for `p` in a compact set `P`, then `∫ ψ(x) 𝐞(t θ(p, x)) dμ(x)` is `O(|t| ^ (-N))` for
every `N`, uniformly for `p ∈ P`. -/
theorem exists_forall_abs_pow_mul_norm_integral_mul_fourierChar_le {ψ : E → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {θ : F × E → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {P : Set F} (hP : IsCompact P)
    (hθP : ∀ p ∈ P, ∀ x ∈ tsupport ψ, fderiv ℝ (fun y ↦ θ (p, y)) x ≠ 0) (N : ℕ) :
    ∃ C, ∀ p ∈ P, ∀ t : ℝ, |t| ^ N * ‖∫ x, ψ x * 𝐞 (t * θ (p, x)) ∂μ‖ ≤ C := by
  have hsupp : tsupport (fun q : F × E ↦ ψ q.2) ⊆ univ ×ˢ tsupport ψ :=
    closure_minimal (fun q hq ↦ ⟨mem_univ _, subset_tsupport _ hq⟩)
      (isClosed_univ.prod (isClosed_tsupport ψ))
  exact exists_forall_abs_pow_mul_norm_integral_le (hψ.comp contDiff_snd) hθ hψc.isCompact hsupp
    hP (fun q hq hqP ↦ hθP q.1 hqP q.2 (hsupp hq).2) N

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.TotalVariation
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import TauCeti.Analysis.Distribution.TestFunction.Translation
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov

/-!
# Compactness of families of bounded variation

Let `Ω` be an open set of a finite-dimensional real inner product space `E` with an additive Haar
measure. This file proves that a family of functions bounded in `L¹(Ω)` and in total variation on
`Ω` is relatively compact in `L¹_loc(Ω)`: its restrictions to any compact `K ⊆ Ω` form a totally
bounded subset of `L¹(K)`. This is the compactness theorem for functions of bounded variation
used to extract convergent subsequences in the direct method and in blow-up arguments for sets of
finite perimeter; lower semicontinuity of the variation
(`TauCeti.totalVariationOn_le_liminf`) then controls the variation of the limit.

The proof follows the Fréchet–Kolmogorov criterion
(`TauCeti.totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl`), whose hypotheses
come from two estimates of independent interest.

* **The translation estimate.** If the segments `x + [0, 1] h` starting in `V` lie in `Ω`, then
  `∫_V |u (x + h) - u x| dx ≤ ‖h‖ |Du|(Ω)`. By the duality `∫_V |w| = sup ∫ w g` over scalar test
  functions `|g| ≤ 1` on `V`, it suffices to bound `∫ (u (x + h) - u x) g x dx`. Translation
  invariance turns this into `∫ u (g (· - h) - g)`, and `g (y - h) - g y = div ψ y` for the test
  vector field `ψ y = -(∫₀¹ g (y - t h) dt) h`, of norm at most `‖h‖`.
* **Multiplication by a smooth cutoff.** For smooth `χ` with `|χ| ≤ c`,
  `|D(χ u)|(Ω') ≤ c |Du|(Ω) + ∫_{Ω'} ‖Dχ‖ |u|` whenever `tsupport χ ∩ Ω' ⊆ Ω`, by the product
  rule `div (χ φ) = χ div φ + Dχ φ` for test vector fields.

A cutoff equal to one near `K` and supported in `Ω` turns the family into one supported in a fixed
compact set, bounded in `L¹` and in variation on the whole space, to which the translation
estimate and the Fréchet–Kolmogorov criterion apply.

## Main results

* `TauCeti.setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn`: the local translation
  estimate `∫_V |u (· + h) - u| ≤ ‖h‖ |Du|(Ω)`.
* `TauCeti.lintegral_enorm_comp_add_sub_le_mul_totalVariationOn`: the translation estimate on the
  whole space.
* `TauCeti.totalVariationOn_mul_le`: the variation of `χ u` for a smooth bounded `χ`.
* `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le` and
  `TauCeti.isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le`: a family bounded in
  `L¹(Ω)` and in variation on `Ω` is totally bounded, and relatively compact, in `L¹(K)` for every
  compact `K ⊆ Ω`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Theorem 3.23.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2,
  Theorem 5.5.
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 12.26.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Function Metric Set TopologicalSpace TestFunction
open scoped ENNReal NNReal ContDiff Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω V : Opens E}
  {u : E → ℝ} {h : E}

/-! ### The translation estimate -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- A difference of translates of a scalar test function is a divergence: for `g ∈ 𝓓(V, ℝ)` with
`|g| ≤ 1`, the vector field `ψ y = -(∫₀¹ g (y - t h) dt) h` is a test vector field on `Ω` of norm
at most `‖h‖` with `div ψ y = g (y - h) - g y`, as soon as the segments `x + [0, 1] h` starting
in `V` lie in `Ω`. -/
private theorem exists_divergenceCLM_eq_sub
    (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω) (g : 𝓓(V, ℝ)) (hg : ∀ x, ‖g x‖ ≤ 1) :
    ∃ ψ : 𝓓(Ω, E), (∀ y, ‖ψ y‖ ≤ ‖h‖) ∧ ∀ y, divergenceCLM ψ y = g (y - h) - g y := by
  set Φ : E → ℝ := fun y => ∫ t in (0 : ℝ)..1, g (y - t • h) with hΦ_def
  have hΦs : ContDiff ℝ ∞ Φ := by
    have hΦIcc : Φ = fun y => ∫ t in Icc (0 : ℝ) 1, g (y - t • h) := by
      funext y
      simp only [hΦ_def]
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
    rw [hΦIcc]
    exact contDiff_integral_Icc_of_contDiff (⊤ : ℕ∞) (fun y t => g (y - t • h))
      (g.contDiff.comp (contDiff_fst.sub (contDiff_snd.smul contDiff_const)))
  -- `Φ` vanishes off the compact set `C ⊆ Ω` swept out by `tsupport g` along `[0, 1] h`.
  set C : Set E := (fun p : E × ℝ => p.1 + p.2 • h) '' (tsupport g ×ˢ Icc 0 1)
  have hCc : IsCompact C :=
    (g.hasCompactSupport.isCompact.prod isCompact_Icc).image (by fun_prop)
  have hCΩ : C ⊆ Ω := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact hVΩ t ht (g.tsupport_subset hx)
  have hΦC (y : E) (hy : y ∉ C) : Φ y = 0 := by
    refine (intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_).trans
      (by simp)
    rw [uIcc_of_le zero_le_one] at ht
    exact image_eq_zero_of_notMem_tsupport fun hmem =>
      hy ⟨(y - t • h, t), ⟨hmem, ht⟩, by simp⟩
  have hsupp : support (fun y => Φ y • -h) ⊆ C := fun y hy => by
    by_contra hyC
    exact hy (by simp [hΦC y hyC])
  let ψ : 𝓓(Ω, E) := ⟨fun y => Φ y • -h, hΦs.smul contDiff_const,
    HasCompactSupport.intro hCc fun y hy => by simp [hΦC y hy],
    (closure_minimal hsupp hCc.isClosed).trans hCΩ⟩
  have hψ : (ψ : E → E) = fun y => Φ y • -h := rfl
  refine ⟨ψ, fun y => ?_, fun y => ?_⟩
  · -- `|Φ y| ≤ 1` since `|g| ≤ 1`.
    have hΦ1 : ‖Φ y‖ ≤ 1 := by
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => g (y - t • h)) (a := 0) (b := 1) (C := 1) fun t _ => hg _
    rw [hψ, norm_smul, norm_neg]
    exact mul_le_of_le_one_left (norm_nonneg _) hΦ1
  · -- `div (Φ • (-h)) = DΦ (-h)`, and `s ↦ Φ (y - s h)` differentiates by the fundamental theorem
    -- of calculus, as `Φ (y - s h) = ∫ₛ^{s+1} g (y - t h) dt`.
    rw [divergenceCLM_apply, hψ, fderiv_smul_const (hΦs.differentiable (by simp) y)]
    -- The trace of the rank-one map `v ↦ DΦ v • (-h)` is `DΦ (-h)`.
    rw [show ((fderiv ℝ Φ y).smulRight (-h) : E →ₗ[ℝ] E) =
      (fderiv ℝ Φ y : E →ₗ[ℝ] ℝ).smulRight (-h) from rfl, LinearMap.trace_smulRight]
    set f : ℝ → ℝ := fun t => g (y - t • h)
    have hf : Continuous f := g.continuous.comp (by fun_prop)
    have hline : (fun s : ℝ => Φ (y + s • -h)) =
        fun s => (∫ t in (0 : ℝ)..s + 1, f t) - ∫ t in (0 : ℝ)..s, f t := by
      funext s
      rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _), hΦ_def]
      have hshift := intervalIntegral.integral_comp_add_right f s (a := 0) (b := 1)
      rw [zero_add, add_comm 1 s] at hshift
      rw [← hshift]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [f, smul_neg, add_smul]
      congr 1
      abel
    have hderiv : HasDerivAt (fun s : ℝ => Φ (y + s • -h)) (f 1 - f 0) 0 := by
      rw [hline]
      have h1 := (hf.integral_hasStrictDerivAt 0 (0 + 1)).hasDerivAt.comp_add_const 0 1
      exact h1.sub (hf.integral_hasStrictDerivAt 0 0).hasDerivAt |>.congr_deriv (by simp)
    have hlin : HasLineDerivAt ℝ Φ (f 1 - f 0) y (-h) := hderiv
    rw [ContinuousLinearMap.coe_coe, ← (hΦs.differentiable (by simp) y).lineDeriv_eq_fderiv,
      hlin.lineDeriv]
    simp [f]

/-- **The translation estimate for functions of bounded variation.** If the segments
`x + [0, 1] h` starting at the points `x ∈ V` lie in `Ω`, then every `u` locally integrable on `Ω`
satisfies `∫_V |u (x + h) - u x| dx ≤ ‖h‖ |Du|(Ω)`, finite or infinite. -/
theorem setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn
    (hu : LocallyIntegrableOn u Ω μ) (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω) :
    ∫⁻ x in V, ‖u (x + h) - u x‖ₑ ∂μ ≤ ‖h‖ₑ * totalVariationOn μ Ω u := by
  have hV0 : (V : Set E) ⊆ Ω := fun x hx => by simpa using hVΩ 0 (by simp) hx
  have hV1 : MapsTo (· + h) V Ω := by simpa using hVΩ 1 (by simp)
  -- By duality, `∫_V |w|` for `w = u (· + h) - u` is the supremum of the pairings of `w` with
  -- scalar test functions on `V` bounded by one.
  set w : E → ℝ := fun x => u (x + h) - u x
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  set G : E → ℝ →L[ℝ] ℝ := fun x => L (w x)
  have hw : LocallyIntegrableOn w V μ := (hu.comp_add_right_of_mapsTo hV1).sub (hu.mono_set hV0)
  have hG : LocallyIntegrableOn G V μ := L.locallyIntegrableOn_comp hw
  calc ∫⁻ x in V, ‖w x‖ₑ ∂μ ≤ ∫⁻ x in V, ‖G x‖ₑ ∂μ := lintegral_mono fun x => by
        simp [G, L]
    _ = ⨆ (g : 𝓓(V, ℝ)) (_ : ∀ x, ‖g x‖ ≤ 1), ENNReal.ofReal (∫ x, G x (g x) ∂μ) :=
        hG.iSup_ofReal_integral_apply_eq_setLIntegral_enorm.symm
    _ ≤ ‖h‖ₑ * totalVariationOn μ Ω u := iSup₂_le fun g hg => ?_
  -- Each pairing is `∫ div ψ * u` for the field `ψ` above, by translation invariance of `μ`.
  obtain ⟨ψ, hψh, hψ⟩ := exists_divergenceCLM_eq_sub hVΩ g hg
  have hg₀ : Integrable (fun x => g x * u x) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn (hu.mono_set hV0) g
  have hgh : Integrable (fun y => g (y - h) * u y) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn hu (translateTestFunction hV1 g)
  have hgh' : Integrable (fun x => g x * u (x + h)) μ := by
    simpa using hgh.comp_add_right h
  have htrans : ∫ x, g x * u (x + h) ∂μ = ∫ y, g (y - h) * u y ∂μ := by
    simpa using integral_add_right_eq_self (μ := μ) (fun y => g (y - h) * u y) h
  have hpair : ∫ x, G x (g x) ∂μ = ∫ y, divergenceCLM ψ y * u y ∂μ := by
    simp only [G, w, L, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hψ]
    calc ∫ x, (u (x + h) - u x) * g x ∂μ = ∫ x, g x * u (x + h) ∂μ - ∫ x, g x * u x ∂μ := by
          rw [← integral_sub hgh' hg₀]
          congr 1 with x
          ring
      _ = ∫ y, (g (y - h) - g y) * u y ∂μ := by
          rw [htrans, ← integral_sub hgh hg₀]
          congr 1 with x
          ring
  rw [hpair, ← ofReal_norm]
  exact ofReal_integral_le_mul_totalVariationOn ψ hψh

/-- **The translation estimate on the whole space.** Every locally integrable `u` satisfies
`∫ |u (x + h) - u x| dx ≤ ‖h‖ |Du|(E)`, finite or infinite. -/
theorem lintegral_enorm_comp_add_sub_le_mul_totalVariationOn (hu : LocallyIntegrable u μ)
    (h : E) : ∫⁻ x, ‖u (x + h) - u x‖ₑ ∂μ ≤ ‖h‖ₑ * totalVariationOn μ ⊤ u := by
  simpa using setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn (V := ⊤)
    (hu.locallyIntegrableOn _) fun _ _ => mapsTo_univ _ _

/-! ### Multiplication by a smooth cutoff -/

omit [μ.IsAddHaarMeasure] in
/-- **Multiplication by a smooth function.** Let `χ` be smooth with `|χ| ≤ c`, and let `Ω'` be an
open set with `tsupport χ ∩ Ω' ⊆ Ω`. Every `u` locally integrable on `Ω` satisfies

`|D(χ u)|(Ω') ≤ c |Du|(Ω) + ∫_{Ω'} ‖Dχ‖ |u|`.

For `Ω' = Ω` this is the Leibniz bound on `Ω`. For a cutoff with `tsupport χ ⊆ Ω` and `Ω'` the
whole space, it bounds the variation on the whole space of `χ u`, which vanishes off `Ω`. -/
theorem totalVariationOn_mul_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hχc : ∀ x, |χ x| ≤ c) {Ω' : Opens E} (hΩ' : tsupport χ ∩ Ω' ⊆ Ω)
    (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ Ω' (χ * u) ≤
      ENNReal.ofReal c * totalVariationOn μ Ω u + ∫⁻ x in Ω', ‖fderiv ℝ χ x‖ₑ * ‖u x‖ₑ ∂μ := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  have hφd : ContDiff ℝ ∞ (φ : E → E) := φ.contDiff
  -- The test vector field `χ φ` and the test function `Dχ φ` on `Ω`.
  let χφ : 𝓓(Ω, E) := ⟨fun x => χ x • φ x, hχ.smul hφd, φ.hasCompactSupport.smul_left,
    (subset_inter (tsupport_smul_subset_left _ _) (tsupport_smul_subset_right _ _)).trans
      ((inter_subset_inter_right _ φ.tsupport_subset).trans hΩ')⟩
  have hsupp : support (fun x => fderiv ℝ χ x (φ x)) ⊆ support (fderiv ℝ χ) ∩ support φ :=
    fun x hx => ⟨fun h0 => hx (by simp [h0]), fun h0 => hx (by simp [h0])⟩
  let a : 𝓓(Ω, ℝ) := ⟨fun x => fderiv ℝ χ x (φ x), (hχ.fderiv_right le_rfl).clm_apply hφd,
    φ.hasCompactSupport.mono fun x hx => (hsupp hx).2,
    (closure_mono hsupp |>.trans (closure_inter_subset_inter_closure _ _)).trans
      ((inter_subset_inter (tsupport_fderiv_subset ℝ) φ.tsupport_subset).trans hΩ')⟩
  have hχφ_apply : (χφ : E → E) = fun x => χ x • φ x := rfl
  have ha : (a : E → ℝ) = fun x => fderiv ℝ χ x (φ x) := rfl
  -- The product rule `div (χ φ) = χ div φ + Dχ φ`.
  have hdiv (x : E) : divergenceCLM χφ x = χ x * divergenceCLM φ x + a x := by
    rw [divergenceCLM_apply, divergenceCLM_apply, hχφ_apply, ha,
      fderiv_fun_smul (hχ.differentiable (by simp) x) (hφd.differentiable (by simp) x),
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
      show ((fderiv ℝ χ x).smulRight (φ x) : E →ₗ[ℝ] E) =
        (fderiv ℝ χ x : E →ₗ[ℝ] ℝ).smulRight (φ x) from rfl, LinearMap.trace_smulRight,
      ContinuousLinearMap.coe_coe, smul_eq_mul]
  have hχφ (x : E) : ‖χφ x‖ ≤ c := by
    rw [hχφ_apply, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hφ x)).trans (hχc x)
  have hint (ψ : 𝓓(Ω, ℝ)) : Integrable (fun x => ψ x * u x) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn hu ψ
  have hsplit : ∫ x, divergenceCLM φ x * (χ * u) x ∂μ =
      ∫ x, divergenceCLM χφ x * u x ∂μ - ∫ x, a x * u x ∂μ := by
    rw [← integral_sub (hint _) (hint a)]
    congr 1 with x
    rw [hdiv, Pi.mul_apply]
    ring
  -- The remainder `∫ Dχ φ u` is at most `∫_{Ω'} ‖Dχ‖ |u|`.
  have hrem : ENNReal.ofReal |∫ x, a x * u x ∂μ| ≤
      ∫⁻ x in Ω', ‖fderiv ℝ χ x‖ₑ * ‖u x‖ₑ ∂μ := by
    rw [← Real.enorm_eq_ofReal_abs, ← lintegral_indicator Ω'.isOpen.measurableSet]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun x => ?_)
    by_cases hx : x ∈ (Ω' : Set E)
    · rw [indicator_of_mem hx, enorm_mul]
      gcongr
      rw [ha, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal <| ((fderiv ℝ χ x).le_opNorm _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (hφ x))
    · have hφx : φ x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)
      simp [ha, hφx, hx]
  rw [hsplit]
  calc ENNReal.ofReal (∫ x, divergenceCLM χφ x * u x ∂μ - ∫ x, a x * u x ∂μ)
      ≤ ENNReal.ofReal (∫ x, divergenceCLM χφ x * u x ∂μ) +
          ENNReal.ofReal |∫ x, a x * u x ∂μ| := by
        refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
        linarith [neg_abs_le (∫ x, a x * u x ∂μ)]
    _ ≤ _ := add_le_add (ofReal_integral_le_mul_totalVariationOn χφ hχφ) hrem

omit [μ.IsAddHaarMeasure] in
/-- **Variation of a cut-off function on the whole space.** If `χ` is smooth with `|χ| ≤ c`,
`‖Dχ‖ ≤ C` and `tsupport χ ⊆ Ω`, then every `u` locally integrable on `Ω` satisfies
`|D(χ u)|(E) ≤ c |Du|(Ω) + C ∫_Ω |u|`. -/
theorem totalVariationOn_top_mul_le {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) {c : ℝ}
    (hχc : ∀ x, |χ x| ≤ c) (hχΩ : tsupport χ ⊆ Ω) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ χ x‖ ≤ C)
    (hu : LocallyIntegrableOn u Ω μ) :
    totalVariationOn μ ⊤ (χ * u) ≤
      ENNReal.ofReal c * totalVariationOn μ Ω u + ENNReal.ofReal C * ∫⁻ x in Ω, ‖u x‖ₑ ∂μ := by
  refine (totalVariationOn_mul_le hχ hχc (Ω' := ⊤) (by simpa using hχΩ) hu).trans
    (add_le_add le_rfl ?_)
  rw [Opens.coe_top, Measure.restrict_univ, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator Ω.isOpen.measurableSet]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ (Ω : Set E)
  · rw [indicator_of_mem hx, ← ofReal_norm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hC x)) le_rfl
  · have h0 : fderiv ℝ χ x = 0 :=
      image_eq_zero_of_notMem_tsupport fun hmem => hx (hχΩ (tsupport_fderiv_subset ℝ hmem))
    rw [indicator_of_notMem hx, h0, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero, zero_mul]

/-! ### Compactness -/

variable {K : Set E} {S : Set (E → ℝ)} {M : ℝ≥0∞}

/-- **Compactness of families of bounded variation.** Let `S` be a family of functions on `Ω`
that is bounded in `L¹(Ω)` and in variation on `Ω`: `∫_Ω |u| ≤ M` and `|Du|(Ω) ≤ M` for every
`u ∈ S`, with `M < ∞`. Then for every compact `K ⊆ Ω` the restrictions to `K` of the members of
`S` form a totally bounded subset of `L¹(K)`.

Since only a neighbourhood of `K` enters, a family that is merely locally bounded in `L¹` and in
variation is totally bounded in `L¹(K)` for every compact `K ⊆ Ω`: apply this to an open
neighbourhood of `K` with compact closure in `Ω`. -/
theorem totallyBounded_of_setLIntegral_le_of_totalVariationOn_le (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hM : M ≠ ⊤) (hmeas : ∀ u ∈ S, AEStronglyMeasurable u (μ.restrict Ω))
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M) (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    TotallyBounded {f : Lp ℝ 1 (μ.restrict K) | ∃ u ∈ S, f =ᵐ[μ.restrict K] u} := by
  -- Multiply by a smooth cutoff `χ` equal to one near `K` and supported in `Ω`.
  obtain ⟨χ, hχ, hχ01, hχK, hχc, hχΩ⟩ := hK.exists_contDiff_cutoff Ω.isOpen hKΩ
  obtain ⟨C, hC⟩ := (hχ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hχc.fderiv ℝ).norm
  have hχ1 (x : E) : |χ x| ≤ 1 := by
    obtain ⟨h0, h1⟩ := hχ01 (mem_range_self x)
    rwa [abs_of_nonneg h0]
  -- The cut-off functions `χ u` are integrable, and bounded in `L¹` and in variation on the
  -- whole space.
  have hχ0 (x : E) (hx : x ∉ (Ω : Set E)) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun hmem => hx (hχΩ hmem)
  have hnorm (u : E → ℝ) : ∫⁻ x, ‖(χ * u) x‖ₑ ∂μ ≤ ∫⁻ x in Ω, ‖u x‖ₑ ∂μ := by
    rw [← lintegral_indicator Ω.isOpen.measurableSet]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ (Ω : Set E)
    · rw [indicator_of_mem hx, Pi.mul_apply, enorm_mul]
      exact mul_le_of_le_one_left' (by simpa [← ofReal_norm] using hχ1 x)
    · simp [hχ0 x hx]
  have huΩ (u : E → ℝ) (hu : u ∈ S) : IntegrableOn u Ω μ :=
    ⟨hmeas u hu, (hbdd u hu).trans_lt hM.lt_top⟩
  have hint (u : E → ℝ) (hu : u ∈ S) : Integrable (χ * u) μ := by
    refine ⟨?_, (hnorm u).trans_lt (huΩ u hu).2⟩
    have hind : χ * u = (Ω : Set E).indicator (χ * u) := by
      ext x
      by_cases hx : x ∈ (Ω : Set E) <;> simp [hx, hχ0]
    rw [hind, aestronglyMeasurable_indicator_iff Ω.isOpen.measurableSet]
    exact hχ.continuous.aestronglyMeasurable.mul (hmeas u hu)
  have hB : M + ENNReal.ofReal C * M ≠ ⊤ := by finiteness
  have hvarχ (u : E → ℝ) (hu : u ∈ S) :
      totalVariationOn μ ⊤ (χ * u) ≤ M + ENNReal.ofReal C * M :=
    (totalVariationOn_top_mul_le hχ hχ1 hχΩ (fun x => hC (mem_range_self x))
      (huΩ u hu).locallyIntegrableOn).trans (by gcongr <;> simp [hvar u hu, hbdd u hu])
  -- The Fréchet--Kolmogorov criterion applies to the family of the `χ u` in `L¹`.
  set T : Set (Lp ℝ 1 μ) := {f | ∃ u ∈ S, f =ᵐ[μ] χ * u}
  have hT : TotallyBounded T := by
    refine totallyBounded_of_comp_add_sub_of_isBounded_of_ae_eq_zero_compl ENNReal.one_ne_top
      hχc.isCompact.isBounded ?_ hM ?_ ?_
    · rintro f ⟨u, -, hf⟩
      filter_upwards [hf] with x hx hxs
      rw [hx, Pi.mul_apply, image_eq_zero_of_notMem_tsupport hxs, zero_mul]
    · rintro f ⟨u, hu, hf⟩
      rw [eLpNorm_congr_ae hf, eLpNorm_one_eq_lintegral_enorm (hint u hu).aestronglyMeasurable]
      exact (hnorm u).trans (hbdd u hu)
    · intro ε hε
      obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hB hε.ne'
      refine ⟨δ, by exact_mod_cast hδ, fun f ⟨u, hu, hf⟩ h hh => ?_⟩
      have hfh : (fun x => f (x + h)) =ᵐ[μ] fun x => (χ * u) (x + h) :=
        (measurePreserving_add_right μ h).quasiMeasurePreserving.ae_eq_comp hf
      have hinc : (fun x => f (x + h) - f x) =ᵐ[μ] fun x => (χ * u) (x + h) - (χ * u) x := by
        filter_upwards [hfh, hf] with x h₁ h₂
        rw [h₁, h₂]
      rw [eLpNorm_congr_ae hinc, eLpNorm_one_eq_lintegral_enorm
        (f := fun x => (χ * u) (x + h) - (χ * u) x)
        (((hint u hu).comp_add_right h).sub (hint u hu)).aestronglyMeasurable]
      refine (lintegral_enorm_comp_add_sub_le_mul_totalVariationOn
        (hint u hu).locallyIntegrable h).trans ?_
      refine (mul_le_mul' ?_ (hvarχ u hu)).trans hδε.le
      exact enorm_le_coe.mpr (by exact_mod_cast hh.le)
  -- Restricting to `K`, where `χ = 1`, recovers the members of `S`.
  let res : Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 (μ.restrict K) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (by simpa using Measure.restrict_le_self)
  refine (hT.image res.uniformContinuous).subset ?_
  rintro f ⟨u, hu, hfu⟩
  refine ⟨(hint u hu).toL1 _, ⟨u, hu, Integrable.coeFn_toL1 _⟩, ?_⟩
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul (μ := μ.restrict K) ENNReal.one_ne_top
      (by simpa using Measure.restrict_le_self) ((hint u hu).toL1 _),
    ae_restrict_of_ae (Integrable.coeFn_toL1 (hint u hu)), ae_restrict_mem hK.measurableSet,
    hfu] with x h₁ h₂ hx h₃
  have hχx : χ x = 1 := interior_subset (hχK hx)
  rw [h₁, h₂, h₃, Pi.mul_apply, hχx, one_mul]

/-- **Compactness of families of bounded variation**, in the form of a compact embedding: under
the hypotheses of `TauCeti.totallyBounded_of_setLIntegral_le_of_totalVariationOn_le`, the closure in
`L¹(K)` of the restrictions to `K` of the members of `S` is compact. -/
theorem isCompact_closure_of_setLIntegral_le_of_totalVariationOn_le (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (hM : M ≠ ⊤) (hmeas : ∀ u ∈ S, AEStronglyMeasurable u (μ.restrict Ω))
    (hbdd : ∀ u ∈ S, ∫⁻ x in Ω, ‖u x‖ₑ ∂μ ≤ M) (hvar : ∀ u ∈ S, totalVariationOn μ Ω u ≤ M) :
    IsCompact (closure {f : Lp ℝ 1 (μ.restrict K) | ∃ u ∈ S, f =ᵐ[μ.restrict K] u}) :=
  (totallyBounded_of_setLIntegral_le_of_totalVariationOn_le hK hKΩ hM hmeas hbdd
    hvar).closure.isCompact_of_isClosed isClosed_closure

end TauCeti

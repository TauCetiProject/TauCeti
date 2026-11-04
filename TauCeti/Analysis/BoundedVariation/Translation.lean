/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.Distribution.TestFunction.Translation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Distribution.AELeOfIntegral
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.NormDuality
import TauCeti.MeasureTheory.Constructions.UnitInterval
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Translation of distributional total variation and perimeter

Distributional total variation is unchanged when the function and its open domain are translated
by the same vector. More generally, translating a function from an open set `Ω` back to an open
set `V` does not increase its variation whenever `V + h ⊆ Ω`. The equality follows when the two
open sets are exact translates. The corresponding statements for perimeter transport sets by the
same translation.

The proof translates each admissible compactly supported test vector field in the opposite
direction. Translation preserves both its pointwise norm and its divergence, and a
right-invariant measure, such as an additive Haar measure, makes the resulting distributional
pairings equal.

These results give the translation part of affine-isometric transport for BV functions and sets of
finite perimeter. No integrability, measurability, boundedness, or finiteness assumption is needed.

The file also proves the translation estimate `∫_V |u (x + h) - u x| dx ≤ ‖h‖ |Du|(Ω)` for `u`
locally integrable on `Ω`, when the segments `x + [0, 1] h` starting in `V` lie in `Ω`. By the
duality `∫_V |w| = sup ∫ w g` over scalar test functions `|g| ≤ 1` on `V`, it suffices to bound
`∫ (u (x + h) - u x) g x dx`. Translation invariance turns this into `∫ u (g (· - h) - g)`, and
`g (y - h) - g y = -∂_h Φ y` for the test function `Φ y = ∫₀¹ g (y - t h) dt`, and `∂_h Φ` is the
divergence of the test vector field `Φ h`, of norm at most `‖h‖`.

The same identity shows that a function whose distributional derivative in the direction `h` is
nonnegative is nondecreasing along `h`: `u x ≤ u (x + h)` for almost every `x ∈ V`. Indeed `Φ` is
nonnegative when `g` is, so `u (· + h) - u` has nonnegative pairings with nonnegative test
functions.

## Main declarations

* `TauCeti.totalVariationOn_comp_add_right_le`: translation into a larger open set does not
  increase total variation.
* `TauCeti.totalVariationOn_comp_add_right`: total variation is invariant under exact translation
  of its open domain.
* `TauCeti.perimeter_preimage_add_right_le` and `TauCeti.perimeter_preimage_add_right`: the
  corresponding transport results for perimeter.
* `TauCeti.totalVariationOn_comap_add_right` and `TauCeti.perimeter_comap_add_right`: convenient
  exact-translation forms using the canonical preimage open set.
* `TauCeti.setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn`: the local translation
  estimate `∫_V |u (· + h) - u| ≤ ‖h‖ |Du|(Ω)`.
* `TauCeti.lintegral_enorm_comp_add_sub_le_mul_totalVariationOn`: the translation estimate on the
  whole space.
* `TauCeti.ae_le_comp_add_of_forall_integral_lineDeriv_mul_nonpos`: monotonicity along a direction
  in which the distributional derivative is nonnegative.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §5.2,
  Theorem 5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Function Set TestFunction TopologicalSpace
open scoped ContDiff Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω V : Opens E} {h : E}

section Variation

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddRightInvariant]
  {u : E → ℝ} {s : Set E}

/-- Translating a function from `Ω` back to `V` does not increase its total variation when
`V + h ⊆ Ω`. -/
theorem totalVariationOn_comp_add_right_le (hVO : MapsTo (· + h) V Ω) :
    totalVariationOn μ V (fun x => u (x + h)) ≤ totalVariationOn μ Ω u := by
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ : 𝓓(Ω, E) := translateTestFunction hVO φ
  have hpair :
      (∫ x, divergenceCLM φ x * u (x + h) ∂μ) =
        ∫ y, divergenceCLM ψ y * u y ∂μ := by
    simpa only [ψ, divergenceCLM_translateTestFunction, translateTestFunction_apply,
      add_sub_cancel_right] using
      integral_add_right_eq_self (fun y => divergenceCLM ψ y * u y) h
  rw [hpair]
  exact ofReal_integral_le_totalVariationOn ψ fun y => by
    simpa only [ψ, translateTestFunction_apply] using hφ (y - h)

/-- **Translation invariance of total variation.** If translation by `h` maps `V` into `Ω` and
translation by `-h` maps `Ω` back into `V`, then translating the function and its domain together
does not change its total variation. -/
theorem totalVariationOn_comp_add_right (hVO : MapsTo (· + h) V Ω)
    (hOV : MapsTo (· - h) Ω V) :
    totalVariationOn μ V (fun x => u (x + h)) = totalVariationOn μ Ω u := by
  apply le_antisymm (totalVariationOn_comp_add_right_le hVO)
  have hle := totalVariationOn_comp_add_right_le (μ := μ)
    (u := fun x => u (x + h)) (h := -h) (V := Ω) (Ω := V) (by simpa [sub_eq_add_neg] using hOV)
  simpa using hle

/-- Total variation is invariant when the translated domain is written canonically as the
preimage open set. -/
theorem totalVariationOn_comap_add_right :
    totalVariationOn μ
        (Opens.comap (ContinuousMap.addRight h) Ω)
        (fun x => u (x + h)) =
      totalVariationOn μ Ω u := by
  apply totalVariationOn_comp_add_right
  · intro x hx
    exact Opens.mem_comap.mp hx
  · intro y hy
    simpa [Opens.mem_comap] using hy

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The indicator of a translated set is the translated indicator. -/
private theorem indicator_one_preimage_add_right :
    ((· + h) ⁻¹' s).indicator (1 : E → ℝ) = fun x => s.indicator 1 (x + h) := by
  funext x
  simpa only [Function.comp_def, Pi.one_def] using
    (Set.indicator_comp_right (s := s) (g := fun _ => (1 : ℝ)) (fun y : E => y + h) (x := x))

/-- Translating a set and an open domain together cannot increase perimeter when the translated
domain lies in the original domain. -/
theorem perimeter_preimage_add_right_le (hVO : MapsTo (· + h) V Ω) :
    perimeter μ V ((· + h) ⁻¹' s) ≤ perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comp_add_right_le hVO

/-- **Translation invariance of perimeter.** If translation by `h` identifies `V` with `Ω`, then
the perimeter in `V` of the translate by `-h` of `s` equals the perimeter of `s` in `Ω`. -/
theorem perimeter_preimage_add_right (hVO : MapsTo (· + h) V Ω)
    (hOV : MapsTo (· - h) Ω V) :
    perimeter μ V ((· + h) ⁻¹' s) = perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comp_add_right hVO hOV

/-- Perimeter is invariant when a set and its ambient open set are both pulled back by the same
translation. -/
theorem perimeter_comap_add_right :
    perimeter μ (Opens.comap (ContinuousMap.addRight h) Ω)
        ((· + h) ⁻¹' s) =
      perimeter μ Ω s := by
  rw [perimeter_def, perimeter_def, indicator_one_preimage_add_right]
  exact totalVariationOn_comap_add_right

end Variation

section Estimate

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ}

/-! ### The translation estimate -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A difference of translates of a scalar test function is a directional derivative: for
`g ∈ 𝓓(V, ℝ)`, the function `Φ y = ∫₀¹ g (y - t h) dt` is a test function on `Ω` with
`∂_h Φ y = g y - g (y - h)`, as soon as the segments `x + [0, 1] h` starting in `V` lie in `Ω`.
It is bounded by one if `g` is, and nonnegative if `g` is. -/
private theorem exists_lineDeriv_eq_sub
    (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω) (g : 𝓓(V, ℝ)) :
    ∃ Φ : 𝓓(Ω, ℝ), ((∀ x, ‖g x‖ ≤ 1) → ∀ y, ‖Φ y‖ ≤ 1) ∧ ((∀ x, 0 ≤ g x) → ∀ y, 0 ≤ Φ y) ∧
      ∀ y, lineDeriv ℝ (Φ : E → ℝ) y h = g y - g (y - h) := by
  set Φ : E → ℝ := fun y => ∫ t in (0 : ℝ)..1, g (y - t • h) with hΦ_def
  have hΦs : ContDiff ℝ ∞ Φ := by
    rw [← contDiffOn_univ]
    refine (contDiffOn_integral_smul_of_contDiffOn (n := (⊤ : ℕ∞))
      (F := fun p : E × ℝ => g (p.1 - p.2 • h)) (μ := (volume : Measure unitInterval))
      (integrable_const (1 : ℝ)) continuous_subtype_val isOpen_univ
      (g.contDiff.comp (contDiff_fst.sub (contDiff_snd.smul contDiff_const))).contDiffOn
      isOpen_univ fun _ _ _ => mem_univ _).congr fun y _ => ?_
    simp [hΦ_def, intervalIntegral_eq_integral_unitInterval]
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
  have hsupp : support Φ ⊆ C := fun y hy => by
    by_contra hyC
    exact hy (hΦC y hyC)
  let Ψ : 𝓓(Ω, ℝ) := ⟨Φ, hΦs, HasCompactSupport.intro hCc hΦC,
    (closure_minimal hsupp hCc.isClosed).trans hCΩ⟩
  have hΨ : (Ψ : E → ℝ) = Φ := rfl
  refine ⟨Ψ, fun hg y => ?_, fun hg y => ?_, fun y => ?_⟩
  · -- `|Φ y| ≤ 1` since `|g| ≤ 1`.
    simpa [hΨ] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => g (y - t • h)) (a := 0) (b := 1) (C := 1) fun t _ => hg _
  · exact intervalIntegral.integral_nonneg zero_le_one fun t _ => hg _
  · -- `s ↦ Φ (y + s h)` differentiates by the fundamental theorem of calculus, as
    -- `Φ (y + s h) = ∫_{-s}^{1-s} g (y - t h) dt`.
    set f : ℝ → ℝ := fun t => g (y - t • h)
    have hf : Continuous f := g.continuous.comp (by fun_prop)
    have hline : (fun s : ℝ => Φ (y + s • h)) =
        fun s => (∫ t in (0 : ℝ)..1 - s, f t) - ∫ t in (0 : ℝ)..-s, f t := by
      funext s
      rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _), hΦ_def]
      have hshift := intervalIntegral.integral_comp_sub_right f s (a := 0) (b := 1)
      rw [zero_sub, sub_eq_add_neg 1 s, ← sub_eq_add_neg] at hshift
      rw [← hshift]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [f, sub_smul]
      congr 1
      abel
    -- `HasLineDerivAt` is by definition the derivative at `0` of `s ↦ Φ (y + s • h)`.
    have hlin : HasLineDerivAt ℝ Φ (f 0 - f 1) y h := by
      unfold HasLineDerivAt
      rw [hline]
      have h1 := ((hf.integral_hasStrictDerivAt 0 (1 - 0)).hasDerivAt.comp 0
        ((hasDerivAt_id 0).const_sub 1))
      have h2 := ((hf.integral_hasStrictDerivAt 0 (-0)).hasDerivAt.comp 0 (hasDerivAt_id 0).neg)
      exact (h1.sub h2).congr_deriv (by simp only [sub_zero, neg_zero, mul_neg, mul_one]; ring)
    rw [hΨ, hlin.lineDeriv]
    simp [f]

omit [FiniteDimensional ℝ E] in
/-- Pairing the difference `u (· + h) - u` with a test function `g` on `V` amounts to pairing `u`
with `-∂_h Φ` for a test function `Φ` on `Ω` that is bounded by one if `g` is, and nonnegative if
`g` is, as soon as the segments `x + [0, 1] h` starting in `V` lie in `Ω`. -/
private theorem exists_integral_comp_add_sub_mul_eq (hu : LocallyIntegrableOn u Ω μ)
    (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω) (g : 𝓓(V, ℝ)) :
    ∃ Φ : 𝓓(Ω, ℝ), ((∀ x, ‖g x‖ ≤ 1) → ∀ y, ‖Φ y‖ ≤ 1) ∧ ((∀ x, 0 ≤ g x) → ∀ y, 0 ≤ Φ y) ∧
      ∫ x, (u (x + h) - u x) * g x ∂μ = -∫ y, lineDeriv ℝ (Φ : E → ℝ) y h * u y ∂μ := by
  have hV0 : (V : Set E) ⊆ Ω := fun x hx => by simpa using hVΩ 0 (by simp) hx
  have hV1 : MapsTo (· + h) V Ω := by simpa using hVΩ 1 (by simp)
  obtain ⟨Φ, hΦ1, hΦ0, hΦ⟩ := exists_lineDeriv_eq_sub hVΩ g
  refine ⟨Φ, hΦ1, hΦ0, ?_⟩
  -- By translation invariance of `μ`, `∫ g u (· + h) = ∫ g (· - h) u`.
  have hg₀ : Integrable (fun x => g x * u x) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn (hu.mono_set hV0) g
  have hgh : Integrable (fun y => g (y - h) * u y) μ := by
    simpa using integrable_smul_of_locallyIntegrableOn hu (translateTestFunction hV1 g)
  have hgh' : Integrable (fun x => g x * u (x + h)) μ := by
    simpa using hgh.comp_add_right h
  have htrans : ∫ x, g x * u (x + h) ∂μ = ∫ y, g (y - h) * u y ∂μ := by
    simpa using integral_add_right_eq_self (μ := μ) (fun y => g (y - h) * u y) h
  simp only [hΦ]
  calc ∫ x, (u (x + h) - u x) * g x ∂μ = ∫ x, g x * u (x + h) ∂μ - ∫ x, g x * u x ∂μ := by
        rw [← integral_sub hgh' hg₀]
        congr 1 with x
        ring
    _ = -∫ y, (g y - g (y - h)) * u y ∂μ := by
        rw [htrans, ← integral_sub hgh hg₀, ← integral_neg]
        congr 1 with x
        ring

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
  -- Each pairing is `-∫ u div ψ` for the test vector field `ψ = Φ h`, of norm at most `‖h‖`.
  obtain ⟨Φ, hΦ1, -, hpair⟩ := exists_integral_comp_add_sub_mul_eq hu hVΩ g
  set ψ : 𝓓(Ω, E) := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ h) Φ
  have hψh (y : E) : ‖ψ y‖ ≤ ‖h‖ := by
    simpa [ψ, norm_smul] using mul_le_of_le_one_left (norm_nonneg h) (hΦ1 hg y)
  have hdiv (y : E) : divergenceCLM ψ y = lineDeriv ℝ (Φ : E → ℝ) y h := by
    simp [ψ, lineDerivOp_apply]
  have hG' : ∫ x, G x (g x) ∂μ = -∫ y, divergenceCLM ψ y * u y ∂μ := by
    simpa only [G, w, L, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hdiv] using hpair
  rw [hG', ← ofReal_norm]
  exact (ENNReal.ofReal_le_ofReal (neg_le_abs _)).trans
    (ofReal_abs_integral_le_ofReal_mul_totalVariationOn ψ hψh)

/-- **Monotonicity from a nonnegative directional derivative.** Let `u` be locally integrable on
`Ω`, and suppose that its distributional derivative in the direction `h` is nonnegative:
`∫ u ∂_h φ ≤ 0` for every nonnegative test function `φ` on `Ω`. Then `u x ≤ u (x + h)` for almost
every `x ∈ V`, as soon as the segments `x + [0, 1] h` starting in `V` lie in `Ω`. -/
theorem ae_le_comp_add_of_forall_integral_lineDeriv_mul_nonpos (hu : LocallyIntegrableOn u Ω μ)
    (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω)
    (H : ∀ φ : 𝓓(Ω, ℝ), (∀ x, 0 ≤ φ x) → ∫ x, lineDeriv ℝ (φ : E → ℝ) x h * u x ∂μ ≤ 0) :
    ∀ᵐ x ∂μ.restrict V, u x ≤ u (x + h) := by
  have hV0 : (V : Set E) ⊆ Ω := fun x hx => by simpa using hVΩ 0 (by simp) hx
  have hV1 : MapsTo (· + h) V Ω := by simpa using hVΩ 1 (by simp)
  have hVm := V.isOpen.measurableSet
  -- Test `w = u (· + h) - u` against nonnegative test functions on `V`, seen on the subtype `V`.
  set w : E → ℝ := fun x => u (x + h) - u x
  have hw : LocallyIntegrableOn w V μ := (hu.comp_add_right_of_mapsTo hV1).sub (hu.mono_set hV0)
  have hpos := ae_nonneg_of_forall_integral_mul_nonneg ((locallyIntegrable_comap hVm).2 hw)
    fun g hg => ?_
  · rw [ae_restrict_iff_subtype hVm]
    filter_upwards [hpos] with x hx
    exact sub_nonneg.1 hx
  obtain ⟨Φ, -, hΦ0, hpair⟩ := exists_integral_comp_add_sub_mul_eq hu hVΩ g
  have hsub : ∫ x : V, g x * w x ∂μ.comap (↑) = ∫ x in V, g x * w x ∂μ :=
    integral_subtype_comap hVm fun x => g x * w x
  refine le_of_le_of_eq ?_ hsub.symm
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hmem => hx (g.tsupport_subset hmem), zero_mul]]
  simp only [w, mul_comm (g _), hpair, neg_nonneg]
  exact H Φ (hΦ0 hg)

/-- **The translation estimate on the whole space.** Every locally integrable `u` satisfies
`∫ |u (x + h) - u x| dx ≤ ‖h‖ |Du|(E)`, finite or infinite. -/
theorem lintegral_enorm_comp_add_sub_le_mul_totalVariationOn (hu : LocallyIntegrable u μ)
    (h : E) : ∫⁻ x, ‖u (x + h) - u x‖ₑ ∂μ ≤ ‖h‖ₑ * totalVariationOn μ ⊤ u := by
  simpa using setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn (V := ⊤)
    (hu.locallyIntegrableOn _) fun _ _ => mapsTo_univ _ _

end Estimate

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.Analysis.BoundedVariation.Space
public import TauCeti.Analysis.Distribution.TestFunction.Dilation
public import TauCeti.Topology.Algebra.ConstMulAction
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.BoundedVariation.Translation

/-!
# Dilation of distributional variation, perimeter, and BV functions

Pulling a function and its open domain back by a dilation of ratio `r` multiplies its variation
by `|r| / |r| ^ n`, where `n` is the dimension. Equivalently, for a nonzero ratio `r`, dilating a
set and its ambient open domain multiplies its perimeter by `|r| ^ (n - 1)`, with truncated
subtraction, hence by `1` in dimension zero.

The quantities are extended nonnegative reals, so the statements apply to infinite perimeter
and do not require finite volume. The pullback coefficient written as a quotient also covers
dimension zero and the degenerate dilation `r = 0`, where both sides vanish. A one-sided domain
inclusion gives the corresponding localization inequality.

Combined with translation invariance, pulling `s` and an open domain back together by
`y ↦ x + r • y` multiplies the perimeter by `|r| / |r| ^ n`
(`TauCeti.perimeter_comap_add_smul`). In particular the perimeter in `ball 0 R` of the blow-up
`(fun y => x + r • y) ⁻¹' s` is `|r| / |r| ^ n` times the perimeter of `s` in `ball x (|r| * R)`
(`TauCeti.perimeter_ball_zero_preimage_add_smul`), that is, the perimeter of `s` in
`ball x (|r| * R)` divided by `|r| ^ (n - 1)`
(`TauCeti.perimeter_ball_zero_preimage_add_smul_eq_div`).

For a nonzero ratio `r` and `V = (r • ·) ⁻¹' Ω`, a function belongs to BV on `Ω` exactly when
its pullback `x ↦ u (r • x)` belongs to BV on `V` (`TauCeti.memBV_comp_smul_iff`). On classes this
gives the continuous linear equivalence `TauCeti.BV.compSmul : BV μ Ω ≃L[ℝ] BV μ V`, which
multiplies the `L¹` norm by `(|r| ^ n)⁻¹` and the variation by `|r| / |r| ^ n`
(`TauCeti.BV.norm_compSmul`). In general it is not an isometry, since the two parts of the BV
norm scale by different powers of `|r|`.

The proof uses the divergence of a dilated test vector field and change of variables for an
additive Haar measure; it does not require a derivative measure or boundary regularity.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, §12.1.
* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TestFunction TopologicalSpace
open scoped Distributions ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω V : Opens E} {r : ℝ} {u : E → ℝ} {s : Set E}

/-- Pullback by a dilation scales variation by at most its inverse surface factor when the dilated
domain lies in the original domain. -/
theorem totalVariationOn_comp_smul_le (hVO : MapsTo (fun x : E => r • x) V Ω) :
    totalVariationOn μ V (fun x => u (r • x)) ≤
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (Ω := V) (u 0)]
  refine totalVariationOn_le_iff.mpr fun φ hφ => ?_
  let ψ := dilateTestFunction hr hVO φ
  have hpair : (∫ y, divergenceCLM ψ y * u y ∂μ) =
      (|r| ^ Module.finrank ℝ E / r) * ∫ x, divergenceCLM φ x * u (r • x) ∂μ := by
    calc
      (∫ y, divergenceCLM ψ y * u y ∂μ) =
          r⁻¹ * ∫ y, divergenceCLM φ (r⁻¹ • y) * u y ∂μ := by
        simp only [ψ, divergenceCLM_dilateTestFunction, IsSMulApply.smul_apply,
          dilateTestFunction_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      _ = r⁻¹ * (|r| ^ Module.finrank ℝ E * ∫ x, divergenceCLM φ x * u (r • x) ∂μ) := by
        congr 1
        simpa only [smul_inv_smul₀ hr, smul_eq_mul, abs_pow] using
          μ.integral_comp_inv_smul (fun x => divergenceCLM φ x * u (r • x)) r
      _ = _ := by ring
  have hinv : (∫ x, divergenceCLM φ x * u (r • x) ∂μ) =
      (r / |r| ^ Module.finrank ℝ E) * ∫ y, divergenceCLM ψ y * u y ∂μ := by
    rw [hpair]
    field_simp
  calc
    ENNReal.ofReal (∫ x, divergenceCLM φ x * u (r • x) ∂μ) ≤
        ENNReal.ofReal |∫ x, divergenceCLM φ x * u (r • x) ∂μ| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
        ENNReal.ofReal |∫ y, divergenceCLM ψ y * u y ∂μ| := by
      rw [hinv, abs_mul, abs_div, abs_pow, abs_abs, ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := mul_le_mul_right (ofReal_abs_integral_le_totalVariationOn ψ fun y => by
      simpa only [ψ, dilateTestFunction_apply] using hφ (r⁻¹ • y)) _

/-- Pulling a function and its open domain back by a dilation gives the exact inverse surface
scaling of its distributional variation. The quotient coefficient includes dimension zero and the
degenerate dilation `r = 0`, where both sides vanish. -/
theorem totalVariationOn_comp_smul (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    totalVariationOn μ V (fun x => u (r • x)) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (Ω := V) (u 0)]
  refine le_antisymm (totalVariationOn_comp_smul_le hVO) ?_
  have hle := totalVariationOn_comp_smul_le (μ := μ) hOV (u := fun x => u (r • x))
  simp only [smul_inv_smul₀ hr] at hle
  have hcancel : ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
      ENNReal.ofReal (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    have habs : |r| ≠ 0 := abs_ne_zero.mpr hr
    have hreal : (|r| / |r| ^ Module.finrank ℝ E) *
        (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) = 1 := by
      simp only [abs_inv, inv_pow, div_eq_mul_inv, inv_inv]
      field_simp
    rw [hreal, ENNReal.ofReal_one]
  calc
    ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u ≤
        ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
          (ENNReal.ofReal (|r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E) *
            totalVariationOn μ V (fun x => u (r • x))) := mul_le_mul_right hle _
    _ = _ := by rw [← mul_assoc, hcancel, one_mul]

/-- Canonical preimage-domain form of the variation scaling law. -/
theorem totalVariationOn_comap_smul :
    totalVariationOn μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) (fun x => u (r • x)) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [totalVariationOn_const (μ := μ) (u 0)]
  apply totalVariationOn_comp_smul
  · intro x hx
    exact Opens.mem_comap.mp hx
  · intro y hy
    apply Opens.mem_comap.mpr
    simpa [smul_inv_smul₀ hr] using hy

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem perimeter_preimage_smul_eq_totalVariationOn :
    perimeter μ V ((r • ·) ⁻¹' s) = totalVariationOn μ V (fun x => s.indicator 1 (r • x)) := by
  simp only [perimeter_def, ← Set.indicator_comp_right, Function.comp_def, Pi.one_def]

/-- Pulling a set back by a dilation bounds perimeter by its inverse surface factor when the
dilated domain is contained in the original domain. -/
theorem perimeter_preimage_smul_le (hVO : MapsTo (fun x : E => r • x) V Ω) :
    perimeter μ V ((r • ·) ⁻¹' s) ≤
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul_le hVO

/-- Pulling back a set and its open domain by a dilation scales perimeter by the inverse surface
factor. No finite-volume assumption is needed. -/
theorem perimeter_preimage_smul (hVO : MapsTo (fun x : E => r • x) V Ω)
    (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ V ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comp_smul hVO hOV

/-- Perimeter scaling with the preimage domain written canonically. -/
theorem perimeter_comap_smul :
    perimeter μ (Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) ((r • ·) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  rw [perimeter_preimage_smul_eq_totalVariationOn, perimeter_def]
  exact totalVariationOn_comap_smul

/-- Dilating a set and its ambient open domain by a nonzero ratio `r` scales perimeter by
`|r| ^ (n - 1)`, with truncated subtraction, so the factor is `1` in dimension zero. This includes
sets of infinite volume or perimeter. -/
theorem perimeter_smul (hr : r ≠ 0)
    (hVO : MapsTo (fun x : E => r • x) V Ω) (hOV : MapsTo (fun y : E => r⁻¹ • y) Ω V) :
    perimeter μ Ω (r • s) =
      ENNReal.ofReal (|r| ^ (Module.finrank ℝ E - 1)) * perimeter μ V s := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp
  have h := perimeter_preimage_smul (μ := μ) (s := s) hOV (by simpa only [inv_inv] using hVO)
  rw [preimage_smul_inv₀ hr] at h
  have hfactor : |r⁻¹| / |r⁻¹| ^ Module.finrank ℝ E = |r| ^ (Module.finrank ℝ E - 1) := by
    rw [abs_inv, inv_pow, div_inv_eq_mul,
      pow_sub₀ |r| (abs_ne_zero.mpr hr) (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos.ne'))]
    simp [mul_comm]
  rwa [hfactor] at h

/-- **The perimeter of a blow-up.** Against an additive Haar measure, pulling a set and an open
domain back together by `y ↦ x + r • y` multiplies the perimeter by `|r| / |r| ^ n`, where
`n = dim E`. -/
theorem perimeter_comap_add_smul (x : E) :
    perimeter μ (Opens.comap ⟨fun y => x + r • y, by fun_prop⟩ Ω) ((fun y => x + r • y) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * perimeter μ Ω s := by
  have hΩ : Opens.comap ⟨fun y => x + r • y, by fun_prop⟩ Ω =
      Opens.comap ⟨(r • ·), by fun_prop⟩ (Opens.comap (ContinuousMap.addRight x) Ω) := by
    ext y
    simp [add_comm]
  have hs : (fun y => x + r • y) ⁻¹' s = (r • ·) ⁻¹' ((· + x) ⁻¹' s) := by
    ext y
    simp [add_comm]
  rw [hΩ, hs, perimeter_comap_smul, perimeter_comap_add_right]

/-- **The perimeter of a blow-up in a ball.** Against an additive Haar measure, the perimeter in
`ball 0 R` of the blow-up `(fun y => x + r • y) ⁻¹' s` is `|r| / |r| ^ n` times the perimeter of
`s` in `ball x (|r| * R)`, where `n = dim E`. For `r = 0` both sides vanish. -/
theorem perimeter_ball_zero_preimage_add_smul {x : E} (R : ℝ) :
    perimeter μ ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) *
        perimeter μ ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩ s := by
  rcases eq_or_ne r 0 with rfl | hr
  · by_cases hx : x ∈ s <;> simp [hx]
  have hΩ : (⟨Metric.ball 0 R, Metric.isOpen_ball⟩ : Opens E) =
      Opens.comap ⟨fun y => x + r • y, by fun_prop⟩
        ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩ := by
    ext y
    simp [dist_eq_norm, norm_smul, mul_lt_mul_iff_right₀ (abs_pos.mpr hr)]
  rw [hΩ, perimeter_comap_add_smul]

/-- **The perimeter of a blow-up in a ball, normalized.** Against an additive Haar measure on a
space of dimension `n`, the perimeter in `ball 0 R` of the blow-up `(fun y => x + r • y) ⁻¹' s` is
the perimeter of `s` in `ball x (|r| * R)` divided by `|r| ^ (n - 1)`. For `r = 0` both sides
vanish: the blow-up is `∅` or the whole space, and `ball x 0` is empty. -/
theorem perimeter_ball_zero_preimage_add_smul_eq_div {x : E} (R : ℝ) :
    perimeter μ ⟨Metric.ball 0 R, Metric.isOpen_ball⟩ ((fun y => x + r • y) ⁻¹' s) =
      perimeter μ ⟨Metric.ball x (|r| * R), Metric.isOpen_ball⟩ s /
        ENNReal.ofReal (|r| ^ (Module.finrank ℝ E - 1)) := by
  rw [perimeter_ball_zero_preimage_add_smul]
  rcases eq_or_ne r 0 with rfl | hr
  · rw [perimeter_congr_of_inter_eq (t := ∅) (by simp)]
    simp
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank ℝ E = m + 1 :=
    ⟨_, (Nat.sub_add_cancel Module.finrank_pos).symm⟩
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 2
  rw [hm, Nat.add_sub_cancel, pow_succ]
  field_simp

section BV

/-- **Dilation of BV functions.** For a nonzero ratio `r` and `V = (r • ·) ⁻¹' Ω`, the pullback
`x ↦ u (r • x)` belongs to BV on `V` exactly when `u` belongs to BV on `Ω`. -/
theorem memBV_comp_smul_iff (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) :
    MemBV μ V (fun x => u (r • x)) ↔ MemBV μ Ω u := by
  have hind : (V : Set E).indicator (fun x => u (r • x)) =
      fun x => (Ω : Set E).indicator u (r • x) :=
    funext fun x => by rw [hVO]; exact indicator_comp_right (r • ·)
  have hc : ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  rw [memBV_iff, memBV_iff]
  refine and_congr ?_ ?_
  · refine (integrable_indicator_iff V.isOpen.measurableSet).symm.trans ?_
    rw [hind, integrable_comp_smul_iff μ _ hr]
    exact integrable_indicator_iff Ω.isOpen.measurableSet
  · rw [totalVariationOn_comp_smul (mapsTo_iff_subset_preimage.mpr hVO.subset)
      (mapsTo_iff_subset_preimage.mpr
        (eq_preimage_inv_smul_of_eq_preimage_smul₀ hr hVO).subset)]
    simp only [lt_top_iff_ne_top, ne_eq, ENNReal.mul_eq_top, hc, ENNReal.ofReal_ne_top, false_and,
      or_false, not_false_eq_true, true_and]

/-- Pulling a BV function back by a dilation of nonzero ratio gives a BV function on any open
domain that the dilation maps into the original domain. -/
theorem MemBV.comp_smul (hu : MemBV μ Ω u) (hr : r ≠ 0) (hVO : MapsTo (fun x : E => r • x) V Ω) :
    MemBV μ V (fun x => u (r • x)) :=
  memBV_iff.mpr ⟨((memBV_comp_smul_iff (V := Opens.comap ⟨(r • ·), by fun_prop⟩ Ω) hr rfl).mpr
      hu).integrableOn.mono_set (mapsTo_iff_subset_preimage.mp hVO),
    (totalVariationOn_comp_smul_le hVO).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu.totalVariationOn_lt_top)⟩

namespace BV

private theorem quasiMeasurePreserving_smul_restrict (hr : r ≠ 0)
    (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) :
    QuasiMeasurePreserving (r • · : E → E) (μ.restrict V) (μ.restrict Ω) :=
  (Measure.quasiMeasurePreserving_smul μ hr).restrict
    (mapsTo_iff_subset_preimage.mpr hVO.subset)

/-- Pull a BV class back by the dilation of ratio `r`. -/
private def compSmulAux (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (u : BV μ Ω) :
    BV μ V :=
  ofFunction (fun x => u (r • x))
    (u.memBV.comp_smul hr (mapsTo_iff_subset_preimage.mpr hVO.subset))

private theorem coeFn_compSmulAux (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    (compSmulAux hr hVO u : E → ℝ) =ᵐ[μ.restrict V] fun x => u (r • x) :=
  coeFn_ofFunction _ _

private theorem compSmulAux_add (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u v : BV μ Ω) :
    compSmulAux hr hVO (u + v) = compSmulAux hr hVO u + compSmulAux hr hVO v := ext <| by
  filter_upwards [coeFn_compSmulAux hr hVO (u + v),
    coeFn_add (compSmulAux hr hVO u) (compSmulAux hr hVO v), coeFn_compSmulAux hr hVO u,
    coeFn_compSmulAux hr hVO v,
    (quasiMeasurePreserving_smul_restrict hr hVO).ae_eq_comp (coeFn_add u v)]
    with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply, Function.comp_apply] at h₂ h₅ ⊢
  rw [h₁, h₂, h₃, h₄, h₅]

private theorem compSmulAux_smul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (c : ℝ) (u : BV μ Ω) :
    compSmulAux hr hVO (c • u) = c • compSmulAux hr hVO u := ext <| by
  filter_upwards [coeFn_compSmulAux hr hVO (c • u), coeFn_smul c (compSmulAux hr hVO u),
    coeFn_compSmulAux hr hVO u,
    (quasiMeasurePreserving_smul_restrict hr hVO).ae_eq_comp (coeFn_smul c u)]
    with x h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul] at h₂ h₄ ⊢
  rw [h₁, h₂, h₃, h₄]

/-- Dilating by `s` and then by `t` with `s * t = 1` gives back the original class. -/
private theorem compSmulAux_compSmulAux {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (hts : s * t = 1)
    (hVO : (V : Set E) = (s • ·) ⁻¹' Ω) (hOV : (Ω : Set E) = (t • ·) ⁻¹' V) (u : BV μ Ω) :
    compSmulAux ht hOV (compSmulAux hs hVO u) = u := ext <| by
  filter_upwards [coeFn_compSmulAux ht hOV (compSmulAux hs hVO u),
    (quasiMeasurePreserving_smul_restrict ht hOV).ae_eq_comp (coeFn_compSmulAux hs hVO u)]
    with y h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, smul_smul, hts, one_smul]

private theorem norm_toL1_compSmulAux (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    ‖(compSmulAux hr hVO u).toL1‖ = (|r| ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ := by
  rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
  refine (integral_congr_ae ((coeFn_compSmulAux hr hVO u).fun_comp norm)).trans ?_
  simp only [Function.comp_apply]
  rw [Measure.setIntegral_comp_smul μ (fun y => ‖u y‖) _ hr, hVO, preimage_smul₀ hr,
    smul_inv_smul₀ hr, abs_inv, abs_pow, smul_eq_mul]

private theorem totalVariationOn_compSmulAux (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    totalVariationOn μ V (compSmulAux hr hVO u) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u :=
  (totalVariationOn_congr_ae (coeFn_compSmulAux hr hVO u)).trans <|
    totalVariationOn_comp_smul (mapsTo_iff_subset_preimage.mpr hVO.subset)
      (mapsTo_iff_subset_preimage.mpr (eq_preimage_inv_smul_of_eq_preimage_smul₀ hr hVO).subset)

private theorem norm_compSmulAux (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    ‖compSmulAux hr hVO u‖ = (|r| ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ +
      |r| / |r| ^ Module.finrank ℝ E * (totalVariationOn μ Ω u).toReal := by
  rw [norm_def, norm_toL1_compSmulAux, totalVariationOn_compSmulAux, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

private theorem norm_compSmulAux_le (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    ‖compSmulAux hr hVO u‖ ≤
      max (|r| ^ Module.finrank ℝ E)⁻¹ (|r| / |r| ^ Module.finrank ℝ E) * ‖u‖ := by
  rw [norm_compSmulAux, norm_def, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)

/-- **Dilation of BV classes.** For a nonzero ratio `r` and `V = (r • ·) ⁻¹' Ω`, precomposition
with `x ↦ r • x` is a continuous linear equivalence `BV μ Ω ≃L[ℝ] BV μ V`. Its inverse is
precomposition with `y ↦ r⁻¹ • y` (`TauCeti.BV.compSmul_symm`). -/
def compSmul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) : BV μ Ω ≃L[ℝ] BV μ V :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun := compSmulAux hr hVO
      invFun := compSmulAux (inv_ne_zero hr) (eq_preimage_inv_smul_of_eq_preimage_smul₀ hr hVO)
      map_add' := compSmulAux_add hr hVO
      map_smul' := compSmulAux_smul hr hVO
      left_inv := compSmulAux_compSmulAux hr (inv_ne_zero hr) (mul_inv_cancel₀ hr) hVO _
      right_inv := compSmulAux_compSmulAux (inv_ne_zero hr) hr (inv_mul_cancel₀ hr) _ hVO }
    _ _ (norm_compSmulAux_le hr hVO)
    (norm_compSmulAux_le (inv_ne_zero hr) (eq_preimage_inv_smul_of_eq_preimage_smul₀ hr hVO))

private theorem compSmul_apply (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (u : BV μ Ω) :
    compSmul hr hVO u = compSmulAux hr hVO u := by
  unfold compSmul
  rfl

/-- The dilation of a BV class is represented by the dilated representative almost everywhere
on `V`. -/
theorem coeFn_compSmul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (u : BV μ Ω) :
    (compSmul hr hVO u : E → ℝ) =ᵐ[μ.restrict V] fun x => u (r • x) := by
  rw [compSmul_apply]
  exact coeFn_compSmulAux hr hVO u

/-- The dilation of the class of a BV function is the class of its dilation. -/
@[simp]
theorem compSmul_ofFunction (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (hu : MemBV μ Ω u) :
    compSmul hr hVO (ofFunction u hu) = ofFunction (fun x => u (r • x))
      (hu.comp_smul hr (mapsTo_iff_subset_preimage.mpr hVO.subset)) :=
  ext <| by
    filter_upwards [coeFn_compSmul hr hVO (ofFunction u hu),
      coeFn_ofFunction (fun x => u (r • x))
        (hu.comp_smul hr (mapsTo_iff_subset_preimage.mpr hVO.subset)),
      (quasiMeasurePreserving_smul_restrict hr hVO).ae_eq_comp (coeFn_ofFunction u hu)]
      with x h₁ h₂ h₃
    simp only [Function.comp_apply] at h₃
    rw [h₁, h₂, h₃]

/-- The inverse of the dilation by `r` is the dilation by `r⁻¹`. -/
@[simp]
theorem compSmul_symm (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) :
    (compSmul hr hVO).symm = compSmul (μ := μ) (inv_ne_zero hr)
      (eq_preimage_inv_smul_of_eq_preimage_smul₀ hr hVO) := by
  refine ContinuousLinearEquiv.ext (funext fun v => (compSmul hr hVO).injective ?_)
  rw [ContinuousLinearEquiv.apply_symm_apply, compSmul_apply, compSmul_apply]
  exact (compSmulAux_compSmulAux (inv_ne_zero hr) hr (inv_mul_cancel₀ hr) _ hVO v).symm

/-- Dilating a BV class by a nonzero ratio `r` multiplies its total variation by
`|r| / |r| ^ n`, where `n` is the dimension. -/
@[simp]
theorem totalVariationOn_compSmul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω)
    (u : BV μ Ω) :
    totalVariationOn μ V (compSmul hr hVO u) =
      ENNReal.ofReal (|r| / |r| ^ Module.finrank ℝ E) * totalVariationOn μ Ω u := by
  rw [compSmul_apply]
  exact totalVariationOn_compSmulAux hr hVO u

/-- Dilating a BV class by a nonzero ratio `r` multiplies its `L¹` norm by `(|r| ^ n)⁻¹`, where
`n` is the dimension. -/
@[simp]
theorem norm_toL1_compSmul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (u : BV μ Ω) :
    ‖(compSmul hr hVO u).toL1‖ = (|r| ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ := by
  rw [compSmul_apply]
  exact norm_toL1_compSmulAux hr hVO u

/-- **The BV norm of a dilation.** Dilating by a nonzero ratio `r` multiplies the `L¹` part of the
BV norm by `(|r| ^ n)⁻¹` and the variation part by `|r| / |r| ^ n`, where `n` is the dimension. -/
theorem norm_compSmul (hr : r ≠ 0) (hVO : (V : Set E) = (r • ·) ⁻¹' Ω) (u : BV μ Ω) :
    ‖compSmul hr hVO u‖ = (|r| ^ Module.finrank ℝ E)⁻¹ * ‖u.toL1‖ +
      |r| / |r| ^ Module.finrank ℝ E * (totalVariationOn μ Ω u).toReal := by
  rw [compSmul_apply]
  exact norm_compSmulAux hr hVO u

end BV

end BV

end TauCeti

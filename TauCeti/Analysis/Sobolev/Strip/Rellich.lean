/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.Strip.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# Rellich's theorem on the strip

Let `V` be a finite-dimensional real normed space and `F₀`, `F₁` subspaces of `V`. This file
proves that the value of an element of the Sobolev space `W^{1,2}_F(ℝ × [0, 1], V)` of the strip
(`TauCeti.StripSobolev.H1 F₀ F₁`) on a compact piece `[-T, T] × [0, 1]` depends compactly on it:
the restriction `TauCeti.StripSobolev.restrictValue T`, composed with the inclusion of `H1 F₀ F₁`
into `L²` jets, is a compact operator to `L²([-T, T] × [0, 1], V)`
(`TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`). This is the compactness
behind Peetre's argument for operators `∂s + J ∂t + S` on strips with Lagrangian boundary
conditions: a semi-Fredholm estimate with a compact error term on `[-T, T] × [0, 1]` gives a
finite-dimensional kernel and a closed range.

Unlike the cylinder, the strip has a boundary, so a section cannot be cut off near
`[-T, T] × [0, 1]` inside the strip. The proof instead cuts it off near the smaller piece
`[-T, T] × [δ, 1 - δ]`, inside the open strip, and controls the remaining layers
`[-T, T] × ([0, δ) ∪ (1 - δ, 1])` along the boundary separately.

* **Interior.** A smooth cutoff `χ` equal to `1` on `[-T, T] × [δ, 1 - δ]` and supported in a
  bounded subset of the open strip turns a test section `ξ` into a `C¹` function `χ ξ` on the
  plane, supported in a fixed bounded set, whose value and derivative are bounded in `L²(ℝ²)` by
  the `W^{1,2}` norm of `ξ` on the strip (`TauCeti.StripSobolev.eLpNorm_fderiv_smul_le`). These
  form a totally bounded family by the Fréchet–Kolmogorov criterion, in the form
  `TauCeti.totallyBounded_of_contDiff_of_eLpNorm_fderiv_le`.
* **Boundary layers.** On every segment `{s} × [0, 1]` the squared norm of `ξ` is at most
  `2 ∫₀¹ (‖ξ‖² + ‖∂t ξ‖²)`, by the fundamental theorem of calculus
  (`TauCeti.ofReal_mul_eNorm_sq_le_lintegral_eNorm_sq_add_lintegral_eNorm_deriv_sq`). Integrating
  over `s` and over a set `L ⊆ [0, 1]` of times bounds `∫_{ℝ × L} ‖ξ‖²` by `4 |L|` times the
  squared `W^{1,2}` norm of `ξ`, which is small when `L` is the union of the two layers of
  width `δ`.

Hence the restricted values of the unit ball lie within any `ε > 0` of a totally bounded set, and
are totally bounded. No boundary condition is used, so the theorem holds for every `F₀` and `F₁`.

## Main results

* `TauCeti.StripSobolev.isCompactOperator_restrictValue_comp_subtypeL`: **Rellich's theorem on the
  strip.**

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces, Rellich's theorem and the semi-Fredholm estimate.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 9.16 (Rellich–Kondrachov) and Theorem 4.26 (Fréchet–Kolmogorov).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The boundary layers -/

/-- **The boundary-layer estimate.** For a `C¹` map `ξ` and a measurable set `L ⊆ [0, 1]` of
times, `∫_{ℝ × L} ‖ξ‖² ≤ 4 |L| ∫_{ℝ × [0, 1]} ‖jet ξ‖²`. -/
private theorem lintegral_enorm_sq_le {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) {L : Set ℝ}
    (hL : MeasurableSet L) (hL₁ : L ⊆ Icc 0 1) :
    ∫⁻ z in univ ×ˢ L, ‖ξ z‖ₑ ^ 2 ≤ 4 * volume L * ∫⁻ z, ‖jet ξ z‖ₑ ^ 2 ∂stripMeasure := by
  have hjm : Measurable fun z ↦ ‖jet ξ z‖ₑ ^ 2 := (continuous_jet hξ).eNorm.measurable.pow_const 2
  have hm : Measurable fun z ↦ ‖ξ z‖ₑ ^ 2 := hξ.continuous.eNorm.measurable.pow_const 2
  have hrestrict : (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ L) =
      (volume : Measure ℝ).prod (volume.restrict L) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  -- On each segment `{s} × [0, 1]`, the squared norm is bounded by the jet energy there.
  have hslice : ∀ s, ∫⁻ t in L, ‖ξ (s, t)‖ₑ ^ 2 ≤
      volume L * (4 * ∫⁻ u in Icc (0 : ℝ) 1, ‖jet ξ (s, u)‖ₑ ^ 2) := by
    intro s
    have hv : ContDiff ℝ 1 fun t ↦ ξ (s, t) := hξ.comp (contDiff_const.prodMk contDiff_id)
    have hderiv : ∀ t, deriv (fun t ↦ ξ (s, t)) t = fderiv ℝ ξ (s, t) (0, 1) := fun t ↦
      (hasDerivAt_slice_right ((hξ.differentiable one_ne_zero) (s, t))).deriv
    have hbound : ∀ t ∈ L, ‖ξ (s, t)‖ₑ ^ 2 ≤ 4 * ∫⁻ u in Icc (0 : ℝ) 1, ‖jet ξ (s, u)‖ₑ ^ 2 := by
      intro t ht
      have h := ofReal_mul_eNorm_sq_le_lintegral_eNorm_sq_add_lintegral_eNorm_deriv_sq
        (a := 0) (b := 1) hv.contDiffOn (hL₁ ht)
      simp only [sub_zero, ENNReal.ofReal_one, one_mul, one_pow, mul_one] at h
      refine h.trans ?_
      simp only [hderiv]
      rw [show (4 : ℝ≥0∞) = 2 + 2 by norm_num, add_mul]
      gcongr with u u
      · exact eNorm_le_iff_norm_le.2 (norm_le_norm_jet ξ (s, u))
      · exact eNorm_le_iff_norm_le.2 (norm_fderiv_zero_one_le_norm_jet ξ (s, u))
    calc ∫⁻ t in L, ‖ξ (s, t)‖ₑ ^ 2
        ≤ ∫⁻ _ in L, 4 * ∫⁻ u in Icc (0 : ℝ) 1, ‖jet ξ (s, u)‖ₑ ^ 2 :=
          setLIntegral_mono' hL hbound
      _ = volume L * (4 * ∫⁻ u in Icc (0 : ℝ) 1, ‖jet ξ (s, u)‖ₑ ^ 2) := by
          rw [setLIntegral_const, mul_comm]
  calc ∫⁻ z in univ ×ˢ L, ‖ξ z‖ₑ ^ 2
      = ∫⁻ s, ∫⁻ t in L, ‖ξ (s, t)‖ₑ ^ 2 := by
        rw [hrestrict, lintegral_prod _ hm.aemeasurable]
    _ ≤ ∫⁻ s, volume L * (4 * ∫⁻ u in Icc (0 : ℝ) 1, ‖jet ξ (s, u)‖ₑ ^ 2) :=
        lintegral_mono hslice
    _ = 4 * volume L * ∫⁻ z, ‖jet ξ z‖ₑ ^ 2 ∂stripMeasure := by
        rw [lintegral_const_mul _ (hjm.lintegral_prod_right'.const_mul 4),
          lintegral_const_mul _ hjm.lintegral_prod_right', stripMeasure_eq_prod,
          lintegral_prod _ hjm.aemeasurable]
        ring

/-! ### The interior cutoff -/

/-- A smooth cutoff on `ℝ × ℝ`, equal to `1` on `[-T, T] × [δ, 1 - δ]` and supported in a bounded
subset of the open strip, multiplies `C¹` maps into `C¹` maps whose value and derivative are
bounded in `L²(ℝ × ℝ)` by the jet on the strip. -/
private theorem exists_cutoff (T : ℝ) {δ : ℝ} (hδ : 0 < δ) : ∃ (χ : ℝ × ℝ → ℝ) (A : ℝ),
    (∀ z ∈ Icc (-T) T ×ˢ Icc δ (1 - δ), χ z = 1) ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ Continuous χ ∧
    (∀ z, χ z ≠ 0 → z ∈ Icc (-(|T| + 1)) (|T| + 1) ×ˢ Icc (0 : ℝ) 1) ∧
    ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 1 ξ → ContDiff ℝ 1 (fun z ↦ χ z • ξ z) ∧
      eLpNorm (fun z ↦ χ z • ξ z) 2 volume ≤ eLpNorm (jet ξ) 2 stripMeasure ∧
      eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure := by
  set U : Set (ℝ × ℝ) := Ioo (-(|T| + 1)) (|T| + 1) ×ˢ Ioo 0 1
  have hKU : Icc (-T) T ×ˢ Icc δ (1 - δ) ⊆ U :=
    prod_mono (Icc_subset_Ioo (by linarith [le_abs_self T]) (by linarith [le_abs_self T]))
      (Icc_subset_Ioo (by linarith) (by linarith))
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχU⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_contDiff_cutoff_eventuallyEq_one
      (isOpen_Ioo.prod isOpen_Ioo) hKU
  have hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := fun z ↦ hχr (mem_range_self z)
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖fderiv ℝ χ z‖ ≤ C :=
    (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hχc.fderiv (𝕜 := ℝ))
  have hχP : tsupport χ ⊆ univ ×ˢ Icc 0 1 :=
    hχU.trans (prod_mono (subset_univ _) Ioo_subset_Icc_self)
  refine ⟨χ, C + 2, fun z hz ↦ (hχ1 z hz).self_of_nhds, hχ01, hχ.continuous,
    fun z hz ↦ prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self (hχU (subset_tsupport χ hz)),
    fun ξ hξ ↦ ⟨(hχ.of_le (by simp)).smul hξ, ?_,
      eLpNorm_fderiv_smul_le (hχ.of_le (by simp))
        (fun z ↦ abs_le.2 ⟨by linarith [(hχ01 z).1], (hχ01 z).2⟩) hC
        (MeasurableSet.univ.prod measurableSet_Icc) hχP hξ⟩⟩
  have hf : Continuous fun z ↦ χ z • ξ z := hχ.continuous.smul hξ.continuous
  have hsub : Function.support (fun z ↦ χ z • ξ z) ⊆ univ ×ˢ Icc 0 1 := fun z hz ↦
    hχP (subset_tsupport χ (left_ne_zero_of_smul hz))
  rw [← eLpNorm_restrict_eq_of_support_subset hf.aestronglyMeasurable hsub]
  refine eLpNorm_mono hf.aestronglyMeasurable fun z ↦ ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ01 z).1]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hχ01 z).2).trans (norm_le_norm_jet ξ z)

/-! ### Rellich's theorem -/

/-- The cut-off test sections of jet norm at most `1` form a totally bounded subset of
`L²(ℝ × ℝ, V)`, by the Fréchet–Kolmogorov criterion. -/
private theorem totallyBounded_setOf_smul [FiniteDimensional ℝ V] (F₀ F₁ : Submodule ℝ V)
    {χ : ℝ × ℝ → ℝ} {A : ℝ} {B : Set (ℝ × ℝ)} (hB : Bornology.IsBounded B)
    (hχB : ∀ z, χ z ≠ 0 → z ∈ B)
    (hest : ∀ ξ : ℝ × ℝ → V, ContDiff ℝ 1 ξ → ContDiff ℝ 1 (fun z ↦ χ z • ξ z) ∧
      eLpNorm (fun z ↦ χ z • ξ z) 2 volume ≤ eLpNorm (jet ξ) 2 stripMeasure ∧
      eLpNorm (fderiv ℝ (fun z ↦ χ z • ξ z)) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure) :
    TotallyBounded {f : Lp V 2 (volume : Measure (ℝ × ℝ)) | ∃ ξ ∈ testSection F₀ F₁,
      eLpNorm (jet ξ) 2 stripMeasure ≤ 1 ∧ f =ᵐ[volume] fun z ↦ χ z • ξ z} := by
  refine totallyBounded_of_contDiff_of_eLpNorm_fderiv_le (p := 2) (by norm_num) hB
    (M := 1 ⊔ ENNReal.ofReal A) (by finiteness) ?_
  rintro f ⟨ξ, hξ, hξ1, hf⟩
  have h := hest ξ (contDiff_one_of_mem_testSection hξ)
  refine ⟨fun z ↦ χ z • ξ z, h.1, fun z hz ↦ ?_, le_sup_of_le_left (h.2.1.trans hξ1),
    le_sup_of_le_right (h.2.2.trans ?_), hf⟩
  · by_contra h'
    exact hz (hχB z (left_ne_zero_of_smul h'))
  · calc ENNReal.ofReal A * eLpNorm (jet ξ) 2 stripMeasure ≤ ENNReal.ofReal A * 1 := by gcongr
      _ = ENNReal.ofReal A := mul_one _

/-- **Cutting off away from the boundary.** If `χ` takes values in `[0, 1]` and equals `1` on
`[-T, T] × [δ, 1 - δ]`, then on `[-T, T] × [0, 1]` the map `ξ - χ ξ` lives on the two boundary
layers of width `δ`, so its squared `L²` norm is at most `8 δ` times the squared `W^{1,2}` norm. -/
private theorem eLpNorm_sub_smul_sq_le {χ : ℝ × ℝ → ℝ} {T δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hχ1 : ∀ z ∈ Icc (-T) T ×ˢ Icc δ (1 - δ), χ z = 1) (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχ : Continuous χ) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    eLpNorm (fun z ↦ ξ z - χ z • ξ z) 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)) ^ 2 ≤
      ENNReal.ofReal (8 * δ) * eLpNorm (jet ξ) 2 stripMeasure ^ 2 := by
  set L : Set ℝ := Ico 0 δ ∪ Ioc (1 - δ) 1
  have hL : MeasurableSet L := measurableSet_Ico.union measurableSet_Ioc
  have hL₁ : L ⊆ Icc 0 1 := union_subset (fun t ht ↦ ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩)
  have hξsq : eLpNorm ξ 2 (volume.restrict (univ ×ˢ L)) ^ 2 = ∫⁻ z in univ ×ˢ L, ‖ξ z‖ₑ ^ 2 := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero
      hξ.continuous.aestronglyMeasurable
  have hjsq : eLpNorm (jet ξ) 2 stripMeasure ^ 2 = ∫⁻ z, ‖jet ξ z‖ₑ ^ 2 ∂stripMeasure := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero
      (continuous_jet hξ).aestronglyMeasurable
  -- Off the boundary layers `χ = 1`, and on them `‖ξ - χ ξ‖ ≤ ‖ξ‖`.
  have hlayer : eLpNorm (fun z ↦ ξ z - χ z • ξ z) 2 (stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1))
      ≤ eLpNorm ξ 2 (volume.restrict (univ ×ˢ L)) := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict (MeasurableSet.univ.prod hL).nullMeasurableSet]
    refine (eLpNorm_mono_ae (hξ.continuous.sub (hχ.smul hξ.continuous)).aestronglyMeasurable
      ?_).trans (eLpNorm_mono_measure _ (Measure.restrict_le_self.trans Measure.restrict_le_self))
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
    simp only [Pi.sub_apply, Pi.smul_apply']
    by_cases hzL : z.2 ∈ L
    · rw [indicator_of_mem (mk_mem_prod (mem_univ z.1) hzL : (z.1, z.2) ∈ univ ×ˢ L)]
      calc ‖ξ z - χ z • ξ z‖ = |1 - χ z| * ‖ξ z‖ := by
            rw [← Real.norm_eq_abs, ← norm_smul, sub_smul, one_smul]
        _ ≤ 1 * ‖ξ z‖ := by
            gcongr
            rw [abs_le]
            constructor <;> linarith [hχ01 z]
        _ = _ := one_mul _
    · have hz' : z ∈ Icc (-T) T ×ˢ Icc δ (1 - δ) :=
        ⟨hz.1, not_lt.1 fun h ↦ hzL (Or.inl ⟨hz.2.1, h⟩), not_lt.1 fun h ↦ hzL (Or.inr ⟨h, hz.2.2⟩)⟩
      rw [hχ1 z hz', one_smul, sub_self, norm_zero]
      exact norm_nonneg _
  have hvol : volume L ≤ ENNReal.ofReal (2 * δ) := by
    calc volume L ≤ volume (Ico (0 : ℝ) δ) + volume (Ioc (1 - δ) 1) := measure_union_le _ _
      _ = ENNReal.ofReal (2 * δ) := by
          rw [Real.volume_Ico, Real.volume_Ioc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  calc _ ≤ eLpNorm ξ 2 (volume.restrict (univ ×ˢ L)) ^ 2 := by gcongr
    _ = ∫⁻ z in univ ×ˢ L, ‖ξ z‖ₑ ^ 2 := hξsq
    _ ≤ 4 * volume L * ∫⁻ z, ‖jet ξ z‖ₑ ^ 2 ∂stripMeasure := lintegral_enorm_sq_le hξ hL hL₁
    _ ≤ 4 * ENNReal.ofReal (2 * δ) * eLpNorm (jet ξ) 2 stripMeasure ^ 2 := by
        rw [hjsq]
        gcongr
    _ = ENNReal.ofReal (8 * δ) * eLpNorm (jet ξ) 2 stripMeasure ^ 2 := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        ring_nf

/-- On `[-T, T] × [0, 1]`, the restricted value of a test section differs from the restriction of
its cut-off by `ξ - χ ξ`. -/
private theorem restrictValue_sub_ae_eq {F₀ F₁ : Submodule ℝ V} {T : ℝ} {χ : ℝ × ℝ → ℝ}
    (ξ : testSection F₀ F₁) (hmem : MemLp (fun z ↦ χ z • (ξ : ℝ × ℝ → V) z) 2 volume) :
    (restrictValue T (jetLp (testSection F₀ F₁) ξ) -
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 (Icc (-T) T ×ˢ Icc 0 1)).comp
        (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1)) (hmem.toLp _) : Lp V 2 _)
      =ᵐ[stripMeasure.restrict (Icc (-T) T ×ˢ Icc 0 1)]
      fun z ↦ (ξ : ℝ × ℝ → V) z - χ z • (ξ : ℝ × ℝ → V) z := by
  set rect : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc 0 1
  have h₂ : (jetLp (testSection F₀ F₁) ξ : ℝ × ℝ → V × V × V) =ᵐ[stripMeasure.restrict rect]
      jet (ξ : ℝ × ℝ → V) := ae_restrict_of_ae (coeFn_jetLp ξ)
  have h₃ : (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 rect).comp
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1)) (hmem.toLp _)
        =ᵐ[stripMeasure.restrict rect] hmem.toLp _ :=
    (LpToLpRestrictCLM_coeFn ℝ _ _).trans (ae_restrict_of_ae (LpToLpRestrictCLM_coeFn ℝ _ _))
  have h₄ : (hmem.toLp _ : ℝ × ℝ → V) =ᵐ[stripMeasure.restrict rect]
      fun z ↦ χ z • (ξ : ℝ × ℝ → V) z :=
    ae_restrict_of_ae (ae_restrict_of_ae hmem.coeFn_toLp)
  filter_upwards [Lp.coeFn_sub (restrictValue T (jetLp (testSection F₀ F₁) ξ))
      ((LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 rect).comp
        (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1)) (hmem.toLp _)),
      coeFn_restrictValue T (jetLp (testSection F₀ F₁) ξ), h₂, h₃, h₄]
    with z h₀ h₁ h₂ h₃ h₄
  rw [h₀, Pi.sub_apply, h₁, h₂, h₃, h₄, jet_apply]

/-- The restricted values of the jets of test sections of norm less than `1` form a totally
bounded set: up to `ε`, they are the restrictions of the cut-off sections of
`totallyBounded_setOf_smul`, with boundary layers of width `δ = min (ε² / 64) 1`. -/
private theorem totallyBounded_image_restrictValue [FiniteDimensional ℝ V]
    (F₀ F₁ : Submodule ℝ V) (T : ℝ) :
    TotallyBounded (restrictValue T ''
      (jetLp (testSection F₀ F₁) '' {ξ | ‖jetLp (testSection F₀ F₁) ξ‖ < 1})) := by
  set rect : Set (ℝ × ℝ) := Icc (-T) T ×ˢ Icc 0 1
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ : ℝ := min (ε ^ 2 / 64) 1
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  obtain ⟨χ, A, hχ1, hχ01, hχc, hχB, hest⟩ := exists_cutoff (V := V) T hδ
  -- Restriction from `L²(ℝ × ℝ)` to `L²([-T, T] × [0, 1])`.
  let Res : Lp V 2 (volume : Measure (ℝ × ℝ)) →L[ℝ] Lp V 2 (stripMeasure.restrict rect) :=
    (LpToLpRestrictCLM (ℝ × ℝ) V ℝ stripMeasure 2 rect).comp
      (LpToLpRestrictCLM (ℝ × ℝ) V ℝ volume 2 (univ ×ˢ Icc 0 1))
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.1 ((totallyBounded_setOf_smul F₀ F₁
    ((isBounded_Icc (-(|T| + 1)) (|T| + 1)).prod (isBounded_Icc (0 : ℝ) 1)) hχB hest).image
    Res.uniformContinuous) (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨_, ⟨ξ, hξ, rfl⟩, rfl⟩
  have hc : ContDiff ℝ 1 (ξ : ℝ × ℝ → V) := contDiff_one_of_mem_testSection ξ.property
  have hξ1 : eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ≤ 1 := by
    have h : ‖jetLp (testSection F₀ F₁) ξ‖ ≤ 1 := le_of_lt hξ
    rw [jetLp_apply, Lp.norm_toLp] at h
    simpa using
      (ENNReal.le_ofReal_iff_toReal_le (memLp_jet ξ.property).eLpNorm_ne_top zero_le_one).2 h
  have hmem : MemLp (fun z ↦ χ z • (ξ : ℝ × ℝ → V) z) 2 volume :=
    (hest _ hc).2.1.trans_lt (hξ1.trans_lt ENNReal.one_lt_top)
  obtain ⟨y, hy, hyd⟩ := mem_iUnion₂.1
    (hcover ⟨hmem.toLp _, ⟨ξ, ξ.property, hξ1, hmem.coeFn_toLp⟩, rfl⟩)
  refine mem_iUnion₂.2 ⟨y, hy, ?_⟩
  have hdiff := restrictValue_sub_ae_eq (T := T) ξ hmem
  have hclose :
      dist (restrictValue T (jetLp (testSection F₀ F₁) ξ)) (Res (hmem.toLp _)) ≤ ε / 2 := by
    rw [dist_eq_norm, Lp.norm_def, eLpNorm_congr_ae hdiff]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity)
      ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_)
    calc _ ≤ ENNReal.ofReal (8 * δ) * eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure ^ 2 :=
          eLpNorm_sub_smul_sq_le hδ (min_le_right _ _) hχ1 hχ01 hχc hc
      _ ≤ ENNReal.ofReal (8 * δ) * 1 := by
          gcongr
          calc _ ≤ (1 : ℝ≥0∞) ^ 2 := by gcongr
            _ = 1 := one_pow 2
      _ ≤ ENNReal.ofReal (ε / 2) ^ 2 := by
          rw [mul_one, ← ENNReal.ofReal_pow (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have : δ ≤ ε ^ 2 / 64 := min_le_left _ _
          nlinarith
  rw [mem_ball] at hyd ⊢
  calc _ ≤ dist (restrictValue T (jetLp (testSection F₀ F₁) ξ)) (Res (hmem.toLp _)) +
        dist (Res (hmem.toLp _)) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hclose hyd
    _ = ε := add_halves ε

/-- **Rellich's theorem on the strip.** The value on the compact piece `[-T, T] × [0, 1]` is a
compact operator from `W^{1,2}_F(ℝ × [0, 1], V)` to `L²`, for every pair of boundary conditions
`F₀`, `F₁`. -/
theorem isCompactOperator_restrictValue_comp_subtypeL [FiniteDimensional ℝ V]
    (F₀ F₁ : Submodule ℝ V) (T : ℝ) :
    IsCompactOperator ((restrictValue (V := V) T).comp (H1 F₀ F₁).subtypeL) := by
  refine (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).2
    ⟨ball 0 1, ball_mem_nhds 0 one_pos, _,
      (totallyBounded_image_restrictValue F₀ F₁ T).closure.isCompact_of_isClosed isClosed_closure,
      ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  -- An element of the unit ball of `H1` is a limit of jets of norm less than `1`.
  have hxc : (x : Lp (V × V × V) 2 stripMeasure) ∈
      closure (jetLp (testSection F₀ F₁) '' {ξ | ‖jetLp (testSection F₀ F₁) ξ‖ < 1}) := by
    have h : (x : Lp (V × V × V) 2 stripMeasure) ∈
        ball 0 1 ∩ closure (range (jetLp (testSection F₀ F₁))) := by
      refine ⟨by simpa using hx, ?_⟩
      rw [← coe_jetClosure]
      exact x.property
    refine closure_mono ?_ (isOpen_ball.inter_closure h)
    rintro _ ⟨hb, ξ, rfl⟩
    exact ⟨ξ, by simpa using hb, rfl⟩
  exact image_closure_subset_closure_image (restrictValue T).continuous ⟨_, hxc, rfl⟩

end TauCeti.StripSobolev

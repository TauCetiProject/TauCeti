/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.ODE.BoundaryValue.Sobolev
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Analysis.Sobolev.Poincare.TransverseBoundary
import TauCeti.MeasureTheory.Function.Lp.FrechetKolmogorov

/-!
# Rellich's theorem for paths on `[0, 1]`

Let `X` be a finite-dimensional real normed space and `F₀`, `F₁` two subspaces of `X`. This file
proves that the Sobolev space `TauCeti.PathSobolev.H1 F₀ F₁` of paths on `[0, 1]` with boundary
values in `F₀` and `F₁` embeds compactly into `L²((0, 1], X)`: the value map
`TauCeti.PathSobolev.valueL`, `(w, w') ↦ w`, is a compact operator
(`TauCeti.PathSobolev.isCompactOperator_valueL`).

This is the compactness hypothesis on the embedding `ι` of the common domain in the Fredholm theory
of trajectory operators `u ↦ (ι ∘ u)' + A u`
(`TauCeti.WeakDerivStep.isFredholm_familyDomainTrajectoryOperator`), for the domain of the
asymptotic operators of a Floer strip between two Lagrangians.

The proof follows the one on the strip (`TauCeti.Analysis.Sobolev.Strip.Rellich`), with the
interval `[0, 1]` in place of `[-T, T] × [0, 1]`.

* **Interior.** A smooth cutoff `χ` equal to `1` on `[δ, 1 - δ]` and supported in `(0, 1)` turns a
  classical path `w` into a `C¹` function `χ w` on the line, vanishing off `[0, 1]`, whose value
  and derivative are bounded in `L²(ℝ)` by the `W^{1,2}` norm of `w` on `(0, 1]`
  (`TauCeti.eLpNorm_fderiv_smul_le_of_tsupport_subset`). These form a totally bounded family by
  the Fréchet–Kolmogorov criterion, in the form `TauCeti.totallyBounded_setOf_ae_eq_smul`.
* **Boundary layers.** By the fundamental theorem of calculus, `‖w t‖²` is at most four times
  the squared `L²((0, 1])` norm of the jet `(w, w')` for every `t ∈ [0, 1]`
  (`TauCeti.ofReal_mul_eNorm_sq_le_lintegral_eNorm_sq_add_lintegral_eNorm_deriv_sq`). Integrating
  over the two layers `(0, δ)` and `(1 - δ, 1]` bounds the squared `L²` norm of `w - χ w` by
  `8 δ` times the squared norm of the jet, which is small for small `δ`.

Hence the values of the jets of norm less than `1` lie within any `ε > 0` of a totally bounded set,
and the jets are dense in `H1`, so `valueL` is compact
(`isCompactOperator_of_denseRange_of_forall_exists_dist_le`). No boundary condition is used, so the
theorem holds for every pair `F₀`, `F₁`.

## Main results

* `TauCeti.PathSobolev.isCompactOperator_valueL`: **Rellich's theorem on `[0, 1]`.**

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.8 (the compact embedding `W^{1,p}(I) ⊆ Lᵖ(I)` on a bounded interval) and Theorem 4.26
  (Fréchet–Kolmogorov).
-/

public section

noncomputable section

open Function MeasureTheory Metric Set Filter Topology
open scoped ENNReal ContDiff

namespace TauCeti

namespace PathSobolev

local notation "μ₁" => (volume.restrict (Ioc (0 : ℝ) 1))

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {F₀ F₁ : Submodule ℝ X}

/-! ### The cutoff -/

/-- The value and the derivative of a path are bounded by its jet. -/
private theorem norm_le_norm_pathJet (w : ℝ → X) (t : ℝ) :
    ‖w t‖ ≤ ‖pathJet w t‖ ∧ ‖deriv w t‖ ≤ ‖pathJet w t‖ := by
  rw [pathJet_apply]
  exact ⟨norm_fst_le (w t, deriv w t), norm_snd_le (w t, deriv w t)⟩

/-- **The cutoff.** For `δ > 0` there is a continuous `χ` with values in `[0, 1]`, equal to `1` on
`[δ, 1 - δ]` and vanishing off `[0, 1]`, such that for every `C¹` path `w` the product `χ w` is
`C¹`, its `L²(ℝ)` norm is at most the `L²((0, 1])` norm of the jet of `w`, and the `L²(ℝ)` norm of
its derivative is at most `A` times that norm. -/
private theorem exists_cutoff {δ : ℝ} (hδ : 0 < δ) : ∃ (χ : ℝ → ℝ) (A : ℝ),
    (∀ t ∈ Icc δ (1 - δ), χ t = 1) ∧ (∀ t, 0 ≤ χ t ∧ χ t ≤ 1) ∧ Continuous χ ∧
    (∀ t, χ t ≠ 0 → t ∈ Icc (0 : ℝ) 1) ∧
    ∀ w : ℝ → X, ContDiff ℝ 1 w → ContDiff ℝ 1 (fun t ↦ χ t • w t) ∧
      eLpNorm (fun t ↦ χ t • w t) 2 volume ≤ eLpNorm (pathJet w) 2 μ₁ ∧
      eLpNorm (fderiv ℝ (fun t ↦ χ t • w t)) 2 volume ≤
        ENNReal.ofReal A * eLpNorm (pathJet w) 2 μ₁ := by
  obtain ⟨χ, hχ, hχr, hχ1, hχc, hχU⟩ := isCompact_Icc.exists_contDiff_cutoff_eventuallyEq_one
    isOpen_Ioo (Icc_subset_Ioo (by linarith) (by linarith) : Icc δ (1 - δ) ⊆ Ioo (0 : ℝ) 1)
  have hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1 := fun t ↦ hχr (mem_range_self t)
  obtain ⟨C, hC⟩ : ∃ C, ∀ t, ‖fderiv ℝ χ t‖ ≤ C :=
    (hχ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hχc.fderiv (𝕜 := ℝ))
  have hχP : tsupport χ ⊆ Ioc 0 1 := hχU.trans Ioo_subset_Ioc_self
  have hχ' : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  refine ⟨χ, C + 1, fun t ht ↦ (hχ1 t ht).self_of_nhds, hχ01, hχ.continuous,
    fun t ht ↦ Ioo_subset_Icc_self (hχU (subset_tsupport χ ht)), fun w hw ↦
      ⟨hχ'.smul hw, ?_, eLpNorm_fderiv_smul_le_of_tsupport_subset hχ'
        (fun t ↦ abs_le.2 ⟨by linarith [(hχ01 t).1], (hχ01 t).2⟩) hC measurableSet_Ioc hχP hw
        (fun t ↦ (norm_le_norm_pathJet w t).1)
        (fun t ↦ by rw [one_mul, ← norm_deriv_eq_norm_fderiv]; exact (norm_le_norm_pathJet w t).2)
        2⟩⟩
  have hf : Continuous fun t ↦ χ t • w t := hχ.continuous.smul hw.continuous
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet]
  refine eLpNorm_mono hf.aestronglyMeasurable fun t ↦ ?_
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem ht, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ01 t).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hχ01 t).2).trans (norm_le_norm_pathJet w t).1
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ ht (hχP h), zero_smul, norm_zero]
    exact norm_nonneg _

/-! ### The boundary layers -/

/-- A `C¹` path is bounded on `[0, 1]` by its jet: `‖w t‖² ≤ 4 ∫₀¹ (‖w‖² ⊔ ‖w'‖²)`, by the
fundamental theorem of calculus. -/
private theorem enorm_sq_le_four_mul_lintegral {w : ℝ → X} (hw : ContDiff ℝ 1 w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖w t‖ₑ ^ 2 ≤ 4 * ∫⁻ u, ‖(w u, deriv w u)‖ₑ ^ 2 ∂μ₁ := by
  have hIcc : (volume.restrict (Icc (0 : ℝ) 1)) = μ₁ :=
    (Measure.restrict_congr_set Ioc_ae_eq_Icc).symm
  have h := ofReal_mul_eNorm_sq_le_lintegral_eNorm_sq_add_lintegral_eNorm_deriv_sq
    hw.contDiffOn ht
  simp only [sub_zero, ENNReal.ofReal_one, one_mul, one_pow, mul_one, hIcc] at h
  refine h.trans ?_
  rw [show (4 : ℝ≥0∞) = 2 + 2 by norm_num, add_mul]
  gcongr with u u
  · exact eNorm_le_iff_norm_le.2 (norm_fst_le (w u, deriv w u))
  · exact eNorm_le_iff_norm_le.2 (norm_snd_le (w u, deriv w u))

/-- **The boundary layers.** If `χ` takes values in `[0, 1]` and equals `1` on `[δ, 1 - δ]`, then
the squared `L²((0, 1])` norm of `w - χ w` is at most `8 δ` times the squared `L²((0, 1])` norm of
the jet of a `C¹` path `w`. -/
private theorem eLpNorm_sub_smul_sq_le {χ : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hχ1 : ∀ t ∈ Icc δ (1 - δ), χ t = 1) (hχ01 : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1) (hχ : Continuous χ)
    {w : ℝ → X} (hw : ContDiff ℝ 1 w) :
    eLpNorm (fun t ↦ w t - χ t • w t) 2 μ₁ ^ 2 ≤
      ENNReal.ofReal (8 * δ) * eLpNorm (pathJet w) 2 μ₁ ^ 2 := by
  set L : Set ℝ := Ioo 0 δ ∪ Ioc (1 - δ) 1
  have hL : MeasurableSet L := measurableSet_Ioo.union measurableSet_Ioc
  set E : ℝ≥0∞ := ∫⁻ t, ‖(w t, deriv w t)‖ₑ ^ 2 ∂μ₁
  have hjm : Continuous (pathJet w) := by
    rw [show pathJet w = fun t ↦ (w t, deriv w t) from funext (pathJet_apply w)]
    exact hw.continuous.prodMk (hw.continuous_deriv le_rfl)
  have hjsq : eLpNorm (pathJet w) 2 μ₁ ^ 2 = E := by
    simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hjm.aestronglyMeasurable
  have hsq : eLpNorm (fun t ↦ w t - χ t • w t) 2 μ₁ ^ 2 = ∫⁻ t, ‖w t - χ t • w t‖ₑ ^ 2 ∂μ₁ := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
      eLpNorm_nnreal_pow_eq_lintegral (μ := μ₁) (p := 2) two_ne_zero
        (f := fun t ↦ w t - χ t • w t)
        (hw.continuous.sub (hχ.smul hw.continuous)).aestronglyMeasurable
  -- Off the boundary layers `χ = 1`, and on them `‖w - χ w‖ ≤ ‖w‖`.
  have hlayer : ∀ᵐ t ∂μ₁, ‖w t - χ t • w t‖ₑ ^ 2 ≤ L.indicator (fun _ ↦ 4 * E) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    by_cases htL : t ∈ L
    · rw [indicator_of_mem htL]
      refine le_trans ?_ (enorm_sq_le_four_mul_lintegral hw (Ioc_subset_Icc_self ht))
      gcongr
      calc ‖w t - χ t • w t‖ₑ = ‖(1 - χ t) • w t‖ₑ := by rw [sub_smul, one_smul]
        _ = ‖1 - χ t‖ₑ * ‖w t‖ₑ := eNorm_smul _ _
        _ ≤ 1 * ‖w t‖ₑ := by
            gcongr
            rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_le_one, abs_le]
            constructor <;> linarith [hχ01 t]
        _ = ‖w t‖ₑ := one_mul _
    · have ht' : t ∈ Icc δ (1 - δ) :=
        ⟨not_lt.1 fun h ↦ htL (Or.inl ⟨ht.1, h⟩), not_lt.1 fun h ↦ htL (Or.inr ⟨h, ht.2⟩)⟩
      rw [hχ1 t ht', one_smul, sub_self, eNorm_zero]
      simp
  have hvol : volume L ≤ ENNReal.ofReal (2 * δ) := by
    calc volume L ≤ volume (Ioo (0 : ℝ) δ) + volume (Ioc (1 - δ) 1) := measure_union_le _ _
      _ = ENNReal.ofReal (2 * δ) := by
          rw [Real.volume_Ioo, Real.volume_Ioc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          congr 1
          ring
  calc _ = ∫⁻ t, ‖w t - χ t • w t‖ₑ ^ 2 ∂μ₁ := hsq
    _ ≤ ∫⁻ t, L.indicator (fun _ ↦ 4 * E) t ∂μ₁ := lintegral_mono_ae hlayer
    _ = 4 * E * μ₁ L := lintegral_indicator_const hL _
    _ ≤ 4 * E * ENNReal.ofReal (2 * δ) := by
        gcongr
        exact (Measure.restrict_apply_le _ _).trans hvol
    _ = ENNReal.ofReal (8 * δ) * eLpNorm (pathJet w) 2 μ₁ ^ 2 := by
        rw [hjsq, show 8 * δ = 4 * (2 * δ) by ring, ENNReal.ofReal_mul (p := 4) (by norm_num),
          ENNReal.ofReal_ofNat]
        ring

/-! ### Rellich's theorem -/

/-- On `(0, 1]`, the value of the jet of a classical path `w` differs from the restriction of the
cut-off path `χ w` by `w - χ w`. -/
private theorem valueL_jetH1_sub_ae_eq {χ : ℝ → ℝ} (w : boundaryPath F₀ F₁)
    (hmem : MemLp (fun t ↦ χ t • (w : ℝ → X) t) 2 volume) :
    (valueL F₀ F₁ (jetH1 F₀ F₁ w) - LpToLpRestrictCLM ℝ X ℝ volume 2 (Ioc 0 1) (hmem.toLp _) :
      Lp X 2 μ₁) =ᵐ[μ₁] fun t ↦ (w : ℝ → X) t - χ t • (w : ℝ → X) t := by
  filter_upwards [Lp.coeFn_sub (valueL F₀ F₁ (jetH1 F₀ F₁ w))
      (LpToLpRestrictCLM ℝ X ℝ volume 2 (Ioc 0 1) (hmem.toLp _)),
    (memLp_coe w).coeFn_toLp, LpToLpRestrictCLM_coeFn ℝ (Ioc (0 : ℝ) 1) (hmem.toLp _),
    ae_restrict_of_ae hmem.coeFn_toLp] with t h₀ h₁ h₂ h₃
  rw [h₀, Pi.sub_apply, valueL_jetH1, h₁, h₂, h₃]

/-- **Rellich's theorem on `[0, 1]`.** For a finite-dimensional `X`, the value map
`(w, w') ↦ w` from the Sobolev space `H1 F₀ F₁` of paths on `[0, 1]` to `L²((0, 1], X)` is a
compact operator, for every pair of boundary conditions `F₀`, `F₁`. -/
theorem isCompactOperator_valueL [FiniteDimensional ℝ X] :
    IsCompactOperator (valueL F₀ F₁) := by
  refine isCompactOperator_of_denseRange_of_forall_exists_dist_le _ denseRange_jetH1
    fun ε hε ↦ ?_
  -- Cut off with boundary layers of width `δ`, so that the layers contribute at most `ε`.
  set δ : ℝ := min (ε ^ 2 / 8) 1
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  obtain ⟨χ, A, hχ1, hχ01, hχc, hχB, hest⟩ := exists_cutoff (X := X) hδ
  refine ⟨_, (totallyBounded_setOf_ae_eq_smul (p := 2) (by norm_num) (isBounded_Icc 0 1) hχB
    ENNReal.ofReal_ne_top hest).image
      (LpToLpRestrictCLM ℝ X ℝ volume 2 (Ioc 0 1)).uniformContinuous, fun w hw ↦ ?_⟩
  have hc : ContDiff ℝ 1 (w : ℝ → X) := contDiff_coe w
  have hw1 : eLpNorm (pathJet (w : ℝ → X)) 2 μ₁ ≤ 1 := by
    rw [eLpNorm_pathJet_eq]
    exact ENNReal.ofReal_le_one.2 hw.le
  have hmem : MemLp (fun t ↦ χ t • (w : ℝ → X) t) 2 volume :=
    (hest _ hc).2.1.trans_lt (hw1.trans_lt ENNReal.one_lt_top)
  refine ⟨_, ⟨hmem.toLp _, ⟨w, hc, hw1, hmem.coeFn_toLp⟩, rfl⟩, ?_⟩
  rw [dist_eq_norm, Lp.norm_def, eLpNorm_congr_ae (valueL_jetH1_sub_ae_eq w hmem)]
  refine ENNReal.toReal_le_of_le_ofReal hε.le ((ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_)
  calc _ ≤ ENNReal.ofReal (8 * δ) * eLpNorm (pathJet (w : ℝ → X)) 2 μ₁ ^ 2 :=
        eLpNorm_sub_smul_sq_le hδ hχ1 hχ01 hχc hc
    _ ≤ ENNReal.ofReal (8 * δ) * 1 := by
        gcongr
        exact pow_le_one₀ bot_le hw1
    _ ≤ ENNReal.ofReal ε ^ 2 := by
        rw [mul_one, ← ENNReal.ofReal_pow hε.le]
        refine ENNReal.ofReal_le_ofReal ?_
        have : δ ≤ ε ^ 2 / 8 := min_le_left _ _
        linarith

end PathSobolev

end TauCeti

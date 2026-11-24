/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import TauCeti.MeasureTheory.Measure.AEMeasurable

/-!
# Outer Lebesgue integrals

Given a measure `μ` on a measurable space `α` and an arbitrary (not necessarily measurable)
extended nonnegative function `f : α → ℝ≥0∞`, the outer Lebesgue integral
`TauCeti.outerLIntegral μ f` is the infimum of `∫⁻ ω, g ω ∂μ` over measurable majorants `g ≥ f`.

Unlike the real-valued outer integral (`TauCeti.outerIntegral`), there is no integrability side
condition, so `outerLIntegral μ f = ∞` whenever `f` admits no integrable measurable majorant.

## Main definitions

* `TauCeti.outerLIntegral`: extended-real outer Lebesgue integral.

## Main results

* `TauCeti.meas_ge_le_outerLIntegral_div`: Markov's inequality for `outerLIntegral`, measuring
  superlevel sets by Mathlib's outer measure `μ`.
* `TauCeti.outerLIntegral_indicator_const` and `TauCeti.outerLIntegral_indicator_one`: the outer
  Lebesgue integral of a constant indicator recovers the outer measure `c * μ s`.
* `TauCeti.exists_measurable_ge_outerLIntegral_eq`: existence of an attaining measurable majorant
  for any function `f`.
* `TauCeti.exists_measurable_ge_outerLIntegral_eq_of_lt_top` and
  `TauCeti.exists_measurable_ge_outerLIntegral_eq_of_sFinite`: existence of an attaining
  measurable majorant that is minimal almost everywhere whenever the outer integral is finite or `μ`
  is s-finite.
* `TauCeti.outerLIntegral_iSup` and `TauCeti.outerLIntegral_liminf_le`: monotone convergence and
  Fatou's lemma for `outerLIntegral`.
* `TauCeti.outerLIntegral_add_le`, `TauCeti.outerLIntegral_tsum_le`, and
  `TauCeti.outerLIntegral_const_mul`: subadditivity and homogeneity of `outerLIntegral`.

## References

* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes*, 2nd edition,
  Springer, 2023, §1.2, Lemma 1.2.1, p. 6.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α]

/-- The outer Lebesgue integral of a nonnegative extended-real function `f : α → ℝ≥0∞` with respect
to `μ`, defined as the infimum of `∫⁻ ω, g ω ∂μ` over measurable majorants `g ≥ f`.

Unlike `outerIntegral`, there is no integrability side condition, so `outerLIntegral μ f = ∞`
whenever `f` admits no integrable measurable majorant. -/
noncomputable def outerLIntegral (μ : Measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ

/-- Unfolding lemma for `outerLIntegral`. -/
theorem outerLIntegral_def (μ : Measure α) (f : α → ℝ≥0∞) :
    outerLIntegral μ f = ⨅ (g : α → ℝ≥0∞) (_ : Measurable g) (_ : f ≤ g), ∫⁻ ω, g ω ∂μ :=
  (rfl)

/-- `outerLIntegral μ f` is bounded above by the lower Lebesgue integral of any measurable
majorant `g ≥ f`. -/
theorem outerLIntegral_le_lintegral {μ : Measure α} {f g : α → ℝ≥0∞}
    (hg : Measurable g) (hfg : f ≤ g) :
    outerLIntegral μ f ≤ ∫⁻ ω, g ω ∂μ :=
  iInf_le_of_le g <| iInf_le_of_le hg <| iInf_le_of_le hfg le_rfl

/-- `outerLIntegral μ f` is bounded above by the lower Lebesgue integral of any a.e.-measurable
function `g` with `f ≤ᵐ[μ] g`. -/
theorem outerLIntegral_le_lintegral_of_ae {μ : Measure α} {f g : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (hfg : f ≤ᵐ[μ] g) :
    outerLIntegral μ f ≤ ∫⁻ ω, g ω ∂μ := by
  obtain ⟨h, hh_meas, hfh, hh_ae⟩ :=
    hg.exists_measurable_ge_ae_eq_of_ae_le hfg measurable_const fun _ ↦ le_top
  calc outerLIntegral μ f ≤ ∫⁻ ω, h ω ∂μ := outerLIntegral_le_lintegral hh_meas hfh
    _ = ∫⁻ ω, g ω ∂μ := lintegral_congr_ae hh_ae.symm

/-- Universal lower bound for `outerLIntegral`: if `c ≤ ∫⁻ g ∂μ` for every measurable `g ≥ f`,
then `c ≤ outerLIntegral μ f`. -/
theorem le_outerLIntegral {μ : Measure α} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ g, Measurable g → f ≤ g → c ≤ ∫⁻ ω, g ω ∂μ) :
    c ≤ outerLIntegral μ f :=
  le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ h g hg hfg

/-- Universal lower-bound characterization for `outerLIntegral`. -/
theorem le_outerLIntegral_iff {μ : Measure α} {f : α → ℝ≥0∞} {c : ℝ≥0∞} :
    c ≤ outerLIntegral μ f ↔ ∀ g, Measurable g → f ≤ g → c ≤ ∫⁻ ω, g ω ∂μ :=
  ⟨fun h _ hg hfg ↦ h.trans (outerLIntegral_le_lintegral hg hfg), le_outerLIntegral⟩

/-- The lower Lebesgue integral is always bounded above by `outerLIntegral`. -/
theorem lintegral_le_outerLIntegral (μ : Measure α) (f : α → ℝ≥0∞) :
    ∫⁻ ω, f ω ∂μ ≤ outerLIntegral μ f :=
  le_outerLIntegral fun _ _ hfg ↦ lintegral_mono hfg

/-- For an a.e.-measurable function, `outerLIntegral` agrees with `lintegral`. -/
theorem outerLIntegral_eq_lintegral {μ : Measure α} {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    outerLIntegral μ f = ∫⁻ ω, f ω ∂μ :=
  le_antisymm (outerLIntegral_le_lintegral_of_ae hf EventuallyEq.rfl.le)
    (lintegral_le_outerLIntegral μ f)

/-- `outerLIntegral` is monotone with respect to almost-everywhere inequality. -/
theorem outerLIntegral_mono_ae {μ : Measure α} {f₁ f₂ : α → ℝ≥0∞} (h : f₁ ≤ᵐ[μ] f₂) :
    outerLIntegral μ f₁ ≤ outerLIntegral μ f₂ :=
  le_outerLIntegral fun _ hg h₂g ↦
    outerLIntegral_le_lintegral_of_ae hg.aemeasurable (h.trans (ae_of_all _ h₂g))

/-- `outerLIntegral` is monotone. -/
theorem outerLIntegral_mono {μ : Measure α} {f₁ f₂ : α → ℝ≥0∞} (h : f₁ ≤ f₂) :
    outerLIntegral μ f₁ ≤ outerLIntegral μ f₂ :=
  outerLIntegral_mono_ae (ae_of_all _ h)

/-- Functions equal almost everywhere have equal `outerLIntegral`. -/
theorem outerLIntegral_congr_ae {μ : Measure α} {f₁ f₂ : α → ℝ≥0∞} (h : f₁ =ᵐ[μ] f₂) :
    outerLIntegral μ f₁ = outerLIntegral μ f₂ :=
  le_antisymm (outerLIntegral_mono_ae h.le) (outerLIntegral_mono_ae h.symm.le)

/-- `outerLIntegral` of the constant zero function is `0`. -/
@[simp]
theorem outerLIntegral_zero (μ : Measure α) : outerLIntegral μ (fun _ ↦ 0) = 0 := by
  rw [outerLIntegral_eq_lintegral aemeasurable_const, lintegral_zero]

/-- `outerLIntegral` of the zero function is `0`. -/
@[simp]
theorem outerLIntegral_zero_fun (μ : Measure α) : outerLIntegral μ 0 = 0 := by
  rw [Pi.zero_def, outerLIntegral_zero]

/-- `outerLIntegral` of a constant function `c` is `c * μ Set.univ`. -/
@[simp]
theorem outerLIntegral_const (μ : Measure α) (c : ℝ≥0∞) :
    outerLIntegral μ (fun _ ↦ c) = c * μ Set.univ := by
  rw [outerLIntegral_eq_lintegral aemeasurable_const, lintegral_const]

/-- `outerLIntegral` with respect to the zero measure is `0`. -/
@[simp]
theorem outerLIntegral_zero_measure (f : α → ℝ≥0∞) :
    outerLIntegral (0 : Measure α) f = 0 := by
  rw [outerLIntegral_eq_lintegral aemeasurable_zero_measure, lintegral_zero_measure]

/-- Multiplicative form of Markov's inequality for `outerLIntegral`. -/
theorem mul_meas_ge_le_outerLIntegral (μ : Measure α) (f : α → ℝ≥0∞) (t : ℝ≥0∞) :
    t * μ {ω | t ≤ f ω} ≤ outerLIntegral μ f :=
  le_outerLIntegral fun g hg hfg ↦
    have hsub : {ω | t ≤ f ω} ⊆ {ω | t ≤ g ω} := fun _ hω ↦ le_trans hω (hfg _)
    (mul_le_mul_right (measure_mono hsub) t).trans (mul_meas_ge_le_lintegral hg t)

/-- **Markov's inequality for outer Lebesgue integrals.** The measure of a possibly non-measurable
superlevel set is Mathlib's outer measure. -/
theorem meas_ge_le_outerLIntegral_div (μ : Measure α) (f : α → ℝ≥0∞)
    {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ⊤) :
    μ {ω | t ≤ f ω} ≤ outerLIntegral μ f / t := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl ht) (Or.inl ht'), mul_comm]
  exact mul_meas_ge_le_outerLIntegral μ f t

/-- The outer Lebesgue integral of a constant indicator `s.indicator (fun _ ↦ c)` is `c * μ s`,
for any (not necessarily measurable) set `s`. -/
@[simp]
theorem outerLIntegral_indicator_const (μ : Measure α) (s : Set α) (c : ℝ≥0∞) :
    outerLIntegral μ (s.indicator fun _ ↦ c) = c * μ s := by
  apply le_antisymm
  · let g : α → ℝ≥0∞ := (toMeasurable μ s).indicator fun _ ↦ c
    have hg : Measurable g := measurable_const.indicator (measurableSet_toMeasurable μ s)
    have hle : s.indicator (fun _ ↦ c) ≤ g :=
      Set.indicator_le_indicator_of_subset (subset_toMeasurable μ s) (fun _ ↦ zero_le)
    calc outerLIntegral μ (s.indicator fun _ ↦ c) ≤ ∫⁻ ω, g ω ∂μ :=
          outerLIntegral_le_lintegral hg hle
      _ = c * μ (toMeasurable μ s) := lintegral_indicator_const (measurableSet_toMeasurable μ s) c
      _ = c * μ s := by rw [measure_toMeasurable]
  · refine (mul_le_mul_right (measure_mono ?_) c).trans
      (mul_meas_ge_le_outerLIntegral μ (s.indicator fun _ ↦ c) c)
    intro ω hω
    simp [hω]

/-- The outer Lebesgue integral of `s.indicator 1` is the outer measure `μ s`. -/
@[simp]
theorem outerLIntegral_indicator_one (μ : Measure α) (s : Set α) :
    outerLIntegral μ (s.indicator 1) = μ s := by
  simp [Pi.one_def]

/-- Any a.e.-measurable majorant attaining a finite `outerLIntegral μ f` is minimal almost
everywhere among all a.e.-measurable a.e. majorants of `f`. -/
theorem ae_le_of_lintegral_eq_outerLIntegral {μ : Measure α} {f g h : α → ℝ≥0∞}
    (hg : AEMeasurable g μ) (hfg : f ≤ᵐ[μ] g) (hg_eq : ∫⁻ ω, g ω ∂μ = outerLIntegral μ f)
    (hfin : outerLIntegral μ f < ⊤) (hh : AEMeasurable h μ) (hfh : f ≤ᵐ[μ] h) :
    g ≤ᵐ[μ] h := by
  have hmin_ae : f ≤ᵐ[μ] fun ω ↦ min (g ω) (h ω) :=
    hfg.and hfh |>.mono fun _ ⟨h1, h2⟩ ↦ le_min h1 h2
  have hmin_le : ∫⁻ ω, min (g ω) (h ω) ∂μ ≤ ∫⁻ ω, g ω ∂μ :=
    lintegral_mono fun _ ↦ min_le_left _ _
  have hmin_ge : ∫⁻ ω, g ω ∂μ ≤ ∫⁻ ω, min (g ω) (h ω) ∂μ := by
    rw [hg_eq]
    exact outerLIntegral_le_lintegral_of_ae (hg.min hh) hmin_ae
  have heq : (fun ω ↦ min (g ω) (h ω)) =ᵐ[μ] g :=
    ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ fun _ ↦ min_le_left _ _)
      (lt_of_le_of_lt hmin_le (hg_eq ▸ hfin)).ne hg hmin_ge
  exact heq.symm.le.trans (ae_of_all _ fun _ ↦ min_le_right _ _)

/-- When `outerLIntegral μ f < ∞`, there exists a measurable majorant `g ≥ f` whose lower integral
equals `outerLIntegral μ f` and which is minimal a.e. among all a.e.-measurable a.e. majorants. -/
theorem exists_measurable_ge_outerLIntegral_eq_of_lt_top {μ : Measure α} {f : α → ℝ≥0∞}
    (hfin : outerLIntegral μ f < ⊤) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ ω, g ω ∂μ = outerLIntegral μ f ∧
      ∀ h : α → ℝ≥0∞, AEMeasurable h μ → f ≤ᵐ[μ] h → g ≤ᵐ[μ] h := by
  have hstep : ∀ n : ℕ, ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧
      ∫⁻ ω, g ω ∂μ < outerLIntegral μ f + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro n
    have hlt : outerLIntegral μ f < outerLIntegral μ f + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
      ENNReal.lt_add_right hfin.ne (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    rw [outerLIntegral_def] at hlt
    obtain ⟨g, hg, hfg, hlt'⟩ := by simpa only [iInf_lt_iff] using hlt
    exact ⟨g, hg, hfg, by rwa [← outerLIntegral_def] at hlt'⟩
  choose u hu_meas hfu hu_int using hstep
  let g : α → ℝ≥0∞ := fun ω ↦ ⨅ n, u n ω
  have hg_meas : Measurable g := Measurable.iInf hu_meas
  have hfg : f ≤ g := fun ω ↦ le_iInf fun n ↦ hfu n ω
  have hg_eq : ∫⁻ ω, g ω ∂μ = outerLIntegral μ f := by
    refine le_antisymm ?_ (outerLIntegral_le_lintegral hg_meas hfg)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.mpr hε.ne')
    calc ∫⁻ ω, g ω ∂μ ≤ ∫⁻ ω, u n ω ∂μ := lintegral_mono fun ω ↦ iInf_le (fun k ↦ u k ω) n
      _ ≤ outerLIntegral μ f + ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := (hu_int n).le
      _ ≤ outerLIntegral μ f + ε := by
        gcongr
        exact le_trans (ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ n)) hn.le
  exact ⟨g, hg_meas, hfg, hg_eq, fun h hh hfh ↦
    ae_le_of_lintegral_eq_outerLIntegral hg_meas.aemeasurable (ae_of_all _ hfg) hg_eq hfin hh hfh⟩

/-- `outerLIntegral μ f` is finite if and only if `f` admits a measurable pointwise majorant
with finite lower Lebesgue integral. -/
theorem outerLIntegral_lt_top_iff {μ : Measure α} {f : α → ℝ≥0∞} :
    outerLIntegral μ f < ⊤ ↔ ∃ g, Measurable g ∧ f ≤ g ∧ ∫⁻ ω, g ω ∂μ < ⊤ := by
  refine ⟨fun hfin ↦ ?_, fun ⟨g, hg, hfg, hg_fin⟩ ↦
    (outerLIntegral_le_lintegral hg hfg).trans_lt hg_fin⟩
  obtain ⟨g, hg, hfg, heq, _⟩ := exists_measurable_ge_outerLIntegral_eq_of_lt_top hfin
  exact ⟨g, hg, hfg, heq.symm ▸ hfin⟩

/-- Every function `f : α → ℝ≥0∞` admits a measurable majorant `g ≥ f` whose lower integral equals
`outerLIntegral μ f`. -/
theorem exists_measurable_ge_outerLIntegral_eq (μ : Measure α) (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ ω, g ω ∂μ = outerLIntegral μ f := by
  rcases lt_or_eq_of_le (le_top : outerLIntegral μ f ≤ ⊤) with hfin | htop
  · obtain ⟨g, hg, hfg, heq, _⟩ := exists_measurable_ge_outerLIntegral_eq_of_lt_top hfin
    exact ⟨g, hg, hfg, heq⟩
  · have hμ : μ Set.univ ≠ 0 := by
      intro h0
      have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.mp h0
      rw [hμ0, outerLIntegral_zero_measure] at htop
      exact ENNReal.zero_ne_top htop
    refine ⟨fun _ ↦ ⊤, measurable_const, fun _ ↦ le_top, ?_⟩
    rw [lintegral_const, ENNReal.top_mul hμ, htop]

/-- For an s-finite measure `μ`, every function `f : α → ℝ≥0∞` (even with infinite outer integral)
admits a measurable majorant `g ≥ f` attaining `outerLIntegral μ f` that is minimal a.e. among all
a.e.-measurable a.e. majorants. -/
theorem exists_measurable_ge_outerLIntegral_eq_of_sFinite (μ : Measure α) [SFinite μ]
    (f : α → ℝ≥0∞) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ ω, g ω ∂μ = outerLIntegral μ f ∧
      ∀ h : α → ℝ≥0∞, AEMeasurable h μ → f ≤ᵐ[μ] h → g ≤ᵐ[μ] h := by
  obtain ⟨ν, hν_fin, hμν, hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous (μ := μ)
  let φ : ℝ≥0∞ → ℝ≥0∞ := fun x ↦ (ENNReal.orderIsoIicOneBirational x).val
  have hφ_meas : Measurable φ := by
    simp only [φ, ENNReal.orderIsoIicOneBirational_apply_coe]
    exact (measurable_id.inv.add_const (1 : ℝ≥0∞)).inv
  have hφ_mono : Monotone φ := fun _ _ hxy ↦
    Subtype.coe_le_coe.mpr (ENNReal.orderIsoIicOneBirational.monotone hxy)
  have hφ_le_one : ∀ x, φ x ≤ 1 := fun x ↦ (ENNReal.orderIsoIicOneBirational x).property
  have hfin : outerLIntegral ν (φ ∘ f) < ⊤ :=
    lt_of_le_of_lt
      ((outerLIntegral_mono (f₂ := fun _ ↦ 1) fun ω ↦ hφ_le_one (f ω)).trans_eq (by simp))
      (measure_lt_top ν Set.univ)
  obtain ⟨g₁, hg₁_meas, hfg₁, _, hg₁_min⟩ := exists_measurable_ge_outerLIntegral_eq_of_lt_top hfin
  let g₂ : α → ℝ≥0∞ := fun ω ↦ min (g₁ ω) 1
  have hg₂_meas : Measurable g₂ := hg₁_meas.min measurable_const
  let g : α → ℝ≥0∞ := fun ω ↦
    ENNReal.orderIsoIicOneBirational.symm ⟨g₂ ω, mem_Iic.mpr (min_le_right _ _)⟩
  have hg_meas : Measurable g := by
    simp only [g, ENNReal.orderIsoIicOneBirational_symm_apply]
    exact (hg₂_meas.inv.sub_const (1 : ℝ≥0∞)).inv
  have hfg : f ≤ g := fun ω ↦ by
    have hle : ENNReal.orderIsoIicOneBirational (f ω) ≤
        (⟨g₂ ω, mem_Iic.mpr (min_le_right _ _)⟩ : Iic (1 : ℝ≥0∞)) :=
      Subtype.coe_le_coe.mp (le_min (hfg₁ ω) (hφ_le_one (f ω)))
    exact (OrderIso.le_symm_apply ENNReal.orderIsoIicOneBirational).mpr hle
  have hg_min : ∀ h : α → ℝ≥0∞, AEMeasurable h μ → f ≤ᵐ[μ] h → g ≤ᵐ[μ] h := by
    intro h hh hfh
    have hφh_ae : φ ∘ f ≤ᵐ[ν] φ ∘ h :=
      Filter.Eventually.mono (hνμ.ae_le hfh) fun ω hω ↦ hφ_mono hω
    have hg₁h : g₁ ≤ᵐ[ν] φ ∘ h :=
      hg₁_min (φ ∘ h) (hφ_meas.comp_aemeasurable (hh.mono_ac hνμ)) hφh_ae
    refine Filter.Eventually.mono (hμν.ae_le hg₁h) fun ω hω ↦ ?_
    have hle : (⟨g₂ ω, mem_Iic.mpr (min_le_right _ _)⟩ : Iic (1 : ℝ≥0∞)) ≤
        ENNReal.orderIsoIicOneBirational (h ω) :=
      Subtype.coe_le_coe.mp ((min_le_left _ _).trans hω)
    exact (OrderIso.symm_apply_le ENNReal.orderIsoIicOneBirational).mpr hle
  refine ⟨g, hg_meas, hfg, le_antisymm ?_ (outerLIntegral_le_lintegral hg_meas hfg), hg_min⟩
  exact le_outerLIntegral fun h hh hfh ↦
    lintegral_mono_ae (hg_min h hh.aemeasurable (ae_of_all _ hfh))

/-- `outerLIntegral μ f = 0` if and only if `f =ᵐ[μ] 0`. -/
@[simp]
theorem outerLIntegral_eq_zero_iff {μ : Measure α} {f : α → ℝ≥0∞} :
    outerLIntegral μ f = 0 ↔ f =ᵐ[μ] 0 := by
  constructor
  · intro h0
    obtain ⟨g, hg_meas, hfg, hg_eq⟩ := exists_measurable_ge_outerLIntegral_eq μ f
    rw [h0] at hg_eq
    have hg0 : g =ᵐ[μ] 0 := (lintegral_eq_zero_iff hg_meas).mp hg_eq
    exact hg0.mono fun ω hω ↦ le_antisymm ((hfg ω).trans_eq hω) zero_le
  · intro h0
    rw [outerLIntegral_congr_ae h0, outerLIntegral_zero_fun]

/-- Subadditivity of `outerLIntegral`. -/
theorem outerLIntegral_add_le (μ : Measure α) (f g : α → ℝ≥0∞) :
    outerLIntegral μ (f + g) ≤ outerLIntegral μ f + outerLIntegral μ g := by
  obtain ⟨f', hf'_meas, hff', hf'_eq⟩ := exists_measurable_ge_outerLIntegral_eq μ f
  obtain ⟨g', hg'_meas, hgg', hg'_eq⟩ := exists_measurable_ge_outerLIntegral_eq μ g
  calc outerLIntegral μ (f + g) ≤ ∫⁻ ω, (f' + g') ω ∂μ :=
        outerLIntegral_le_lintegral (hf'_meas.add hg'_meas) (add_le_add hff' hgg')
    _ = ∫⁻ ω, f' ω ∂μ + ∫⁻ ω, g' ω ∂μ := lintegral_add_left hf'_meas g'
    _ = outerLIntegral μ f + outerLIntegral μ g := by rw [hf'_eq, hg'_eq]

/-- Finite subadditivity of `outerLIntegral`. -/
theorem outerLIntegral_finsetSum_le {ι : Type*} (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) :
    outerLIntegral μ (fun ω ↦ ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, outerLIntegral μ (f i) := by
  classical
  choose g hg_meas hfg hg_eq using fun i ↦ exists_measurable_ge_outerLIntegral_eq μ (f i)
  calc outerLIntegral μ (fun ω ↦ ∑ i ∈ s, f i ω)
      ≤ ∫⁻ ω, ∑ i ∈ s, g i ω ∂μ :=
        outerLIntegral_le_lintegral (Finset.measurable_sum s fun i _ ↦ hg_meas i)
          fun ω ↦ Finset.sum_le_sum fun i _ ↦ hfg i ω
    _ = ∑ i ∈ s, ∫⁻ ω, g i ω ∂μ := lintegral_finsetSum s fun i _ ↦ hg_meas i
    _ = ∑ i ∈ s, outerLIntegral μ (f i) := by simp_rw [hg_eq]

/-- Countable subadditivity of `outerLIntegral`. -/
theorem outerLIntegral_tsum_le {ι : Type*} [Countable ι] (μ : Measure α) (f : ι → α → ℝ≥0∞) :
    outerLIntegral μ (fun ω ↦ ∑' i, f i ω) ≤ ∑' i, outerLIntegral μ (f i) := by
  classical
  choose g hg_meas hfg hg_eq using fun i ↦ exists_measurable_ge_outerLIntegral_eq μ (f i)
  calc outerLIntegral μ (fun ω ↦ ∑' i, f i ω)
      ≤ ∫⁻ ω, ∑' i, g i ω ∂μ :=
        outerLIntegral_le_lintegral (Measurable.tsum hg_meas)
          fun ω ↦ tsum_le_tsum fun i ↦ hfg i ω
    _ = ∑' i, ∫⁻ ω, g i ω ∂μ := lintegral_tsum fun i ↦ (hg_meas i).aemeasurable
    _ = ∑' i, outerLIntegral μ (f i) := by simp_rw [hg_eq]

/-- Positive homogeneity of `outerLIntegral` for all extended nonnegative scalars `c : ℝ≥0∞`. -/
theorem outerLIntegral_const_mul (μ : Measure α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    outerLIntegral μ (fun ω ↦ c * f ω) = c * outerLIntegral μ f := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rcases eq_or_ne c ⊤ with rfl | hctop
  · rcases eq_or_ne (outerLIntegral μ f) 0 with hf0 | hfpos
    · have hfae : f =ᵐ[μ] 0 := outerLIntegral_eq_zero_iff.mp hf0
      have htop_ae : (fun ω ↦ ⊤ * f ω) =ᵐ[μ] fun _ ↦ 0 := hfae.mono fun ω hω ↦ by simp [hω]
      rw [hf0, mul_zero, outerLIntegral_congr_ae htop_ae, outerLIntegral_const, zero_mul]
    · rw [ENNReal.top_mul hfpos, eq_top_iff]
      let s : Set α := {ω | f ω ≠ 0}
      have hspos : μ s ≠ 0 := by
        intro hs0
        apply hfpos
        refine outerLIntegral_eq_zero_iff.mpr ?_
        rwa [Filter.EventuallyEq, ae_iff]
      calc ⊤ = ⊤ * μ s := (ENNReal.top_mul hspos).symm
        _ = outerLIntegral μ (s.indicator fun _ ↦ ⊤) := (outerLIntegral_indicator_const μ s ⊤).symm
        _ ≤ outerLIntegral μ (fun ω ↦ ⊤ * f ω) := outerLIntegral_mono fun ω ↦ by
          by_cases hω : ω ∈ s
          · simp [hω, ENNReal.top_mul hω]
          · simp [hω]
  · apply le_antisymm
    · obtain ⟨g, hg_meas, hfg, hg_eq⟩ := exists_measurable_ge_outerLIntegral_eq μ f
      calc outerLIntegral μ (fun ω ↦ c * f ω) ≤ ∫⁻ ω, c * g ω ∂μ :=
            outerLIntegral_le_lintegral (hg_meas.const_mul c) fun ω ↦ mul_le_mul_right (hfg ω) c
        _ = c * ∫⁻ ω, g ω ∂μ := lintegral_const_mul c hg_meas
        _ = c * outerLIntegral μ f := by rw [hg_eq]
    · obtain ⟨h, hh_meas, hcfh, hh_eq⟩ :=
        exists_measurable_ge_outerLIntegral_eq μ (fun ω ↦ c * f ω)
      have hle : outerLIntegral μ f ≤ c⁻¹ * outerLIntegral μ (fun ω ↦ c * f ω) := by
        calc outerLIntegral μ f ≤ ∫⁻ ω, c⁻¹ * h ω ∂μ :=
              outerLIntegral_le_lintegral (hh_meas.const_mul c⁻¹) fun ω ↦ by
                calc f ω = c⁻¹ * (c * f ω) := by
                      rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
                  _ ≤ c⁻¹ * h ω := mul_le_mul_right (hcfh ω) c⁻¹
          _ = c⁻¹ * ∫⁻ ω, h ω ∂μ := lintegral_const_mul c⁻¹ hh_meas
          _ = c⁻¹ * outerLIntegral μ (fun ω ↦ c * f ω) := by rw [hh_eq]
      calc c * outerLIntegral μ f ≤ c * (c⁻¹ * outerLIntegral μ (fun ω ↦ c * f ω)) :=
            mul_le_mul_right hle c
        _ = outerLIntegral μ (fun ω ↦ c * f ω) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]

/-- **Monotone convergence theorem for `outerLIntegral`.** -/
theorem outerLIntegral_iSup (μ : Measure α) {f : ℕ → α → ℝ≥0∞} (hf : Monotone f) :
    outerLIntegral μ (fun ω ↦ ⨆ n, f n ω) = ⨆ n, outerLIntegral μ (f n) := by
  refine le_antisymm ?_ (iSup_le fun n ↦ outerLIntegral_mono fun ω ↦ le_iSup (fun k ↦ f k ω) n)
  rcases eq_or_ne (⨆ n, outerLIntegral μ (f n)) ⊤ with htop | hfin
  · rw [htop]; exact le_top
  have hfn_fin : ∀ n, outerLIntegral μ (f n) < ⊤ := fun n ↦
    lt_of_le_of_lt (le_iSup (fun k ↦ outerLIntegral μ (f k)) n) (lt_top_iff_ne_top.mpr hfin)
  choose g hg_meas hfg hg_eq hg_min using fun n ↦
    exists_measurable_ge_outerLIntegral_eq_of_lt_top (hfn_fin n)
  have hg_ae : ∀ n, g n ≤ᵐ[μ] g (n + 1) := fun n ↦
    hg_min n (g (n + 1)) (hg_meas (n + 1)).aemeasurable
      (ae_of_all _ fun ω ↦ (hf (Nat.le_succ n) ω).trans (hfg (n + 1) ω))
  calc outerLIntegral μ (fun ω ↦ ⨆ n, f n ω)
      ≤ ∫⁻ ω, ⨆ n, g n ω ∂μ :=
        outerLIntegral_le_lintegral (Measurable.iSup hg_meas) fun ω ↦ iSup_mono fun n ↦ hfg n ω
    _ = ⨆ n, ∫⁻ ω, g n ω ∂μ := lintegral_iSup_ae hg_meas hg_ae
    _ = ⨆ n, outerLIntegral μ (f n) := iSup_congr hg_eq

/-- **Fatou's lemma for `outerLIntegral`.** -/
theorem outerLIntegral_liminf_le (μ : Measure α) (f : ℕ → α → ℝ≥0∞) :
    outerLIntegral μ (fun ω ↦ liminf (fun n ↦ f n ω) atTop) ≤
      liminf (fun n ↦ outerLIntegral μ (f n)) atTop := by
  simp_rw [liminf_eq_iSup_iInf_of_nat]
  have hmono : Monotone fun n ω ↦ ⨅ i, ⨅ (_ : n ≤ i), f i ω := fun m n hmn ω ↦
    iInf₂_mono' fun k hk ↦ ⟨k, hmn.trans hk, le_rfl⟩
  rw [outerLIntegral_iSup μ hmono]
  exact iSup_mono fun n ↦ le_iInf₂ fun k hk ↦
    outerLIntegral_mono fun ω ↦ iInf₂_le k hk

end TauCeti

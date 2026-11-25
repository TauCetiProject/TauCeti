/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import TauCeti.Probability.LargeDeviations.Basic
public import TauCeti.Probability.Process.EmpiricalMeasure
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Data.EReal.Operations
import TauCeti.Data.EReal.Quantale
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.Topology.Instances.EReal

/-!
# Logarithmic energy on the real line

For a real external potential `V`, the weighted logarithmic kernel is
`(V x + V y) / 2 - log |x - y|`, with value `∞` at a collision.
The logarithmic energy of a probability measure integrates this kernel against its square.
A real lower bound allows the integral to be expressed as a nonnegative lower integral after a
shift. This also handles measures of infinite energy, including every measure with an atom.

The confinement estimate comes from bounding the distance between two points by
`(1 + |x|) (1 + |y|)`. When `V x / 2 - log (1 + |x|)` tends to infinity outside compact sets,
the energy controls tightness and, for continuous `V`, attains a finite minimum. Upper truncations
of the kernel give lower semicontinuous approximations for lower semicontinuous potentials and
continuous approximations for continuous potentials. On an empirical
measure their diagonal contribution is explicit, which gives a lower limit bound for the
off-diagonal energies of finite particle configurations.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*,
  §2.6.1 and Lemma 2.6.2.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti.Probability

/-- The weighted logarithmic interaction of two real points. A collision has infinite cost. -/
def logarithmicEnergyKernel (V : ℝ → ℝ) (z : ℝ × ℝ) : EReal :=
  ((V z.1 + V z.2) / 2 : ℝ) - ENNReal.log (ENNReal.ofReal |z.1 - z.2|)

@[simp]
theorem logarithmicEnergyKernel_diag (V : ℝ → ℝ) (x : ℝ) :
    logarithmicEnergyKernel V (x, x) = ⊤ := by
  simp [logarithmicEnergyKernel]

/-- Away from collisions the kernel is the ordinary real logarithmic interaction. -/
theorem logarithmicEnergyKernel_of_ne (V : ℝ → ℝ) {x y : ℝ} (h : x ≠ y) :
    logarithmicEnergyKernel V (x, y) =
      ((V x + V y) / 2 - Real.log |x - y| : ℝ) := by
  rw [logarithmicEnergyKernel, ENNReal.log_ofReal_of_pos (abs_pos.mpr (sub_ne_zero.mpr h))]
  exact EReal.coe_sub .. |>.symm

/-- The weighted kernel is symmetric in its two coordinates. -/
theorem logarithmicEnergyKernel_swap (V : ℝ → ℝ) (z : ℝ × ℝ) :
    logarithmicEnergyKernel V z.swap = logarithmicEnergyKernel V z := by
  simp [logarithmicEnergyKernel, add_comm, abs_sub_comm]

@[simp]
theorem logarithmicEnergyKernel_eq_top_iff (V : ℝ → ℝ) (z : ℝ × ℝ) :
    logarithmicEnergyKernel V z = ⊤ ↔ z.1 = z.2 := by
  obtain ⟨x, y⟩ := z
  by_cases h : x = y
  · simp [h]
  · rw [logarithmicEnergyKernel_of_ne V h, iff_false_intro h]
    exact iff_false_intro (EReal.coe_ne_top _)

@[simp]
theorem logarithmicEnergyKernel_ne_bot (V : ℝ → ℝ) (z : ℝ × ℝ) :
    logarithmicEnergyKernel V z ≠ ⊥ := by
  obtain ⟨x, y⟩ := z
  by_cases h : x = y
  · simp [h]
  · rw [logarithmicEnergyKernel_of_ne V h]
    exact EReal.coe_ne_bot _

private theorem continuous_log_ofReal_abs_sub :
    Continuous (fun z : ℝ × ℝ ↦ ENNReal.log (ENNReal.ofReal |z.1 - z.2|)) :=
  ENNReal.continuous_log.comp (ENNReal.continuous_ofReal.comp
    (continuous_fst.sub continuous_snd).abs)

/-- The weighted kernel is continuous into the extended reals, also at a collision. -/
theorem continuous_logarithmicEnergyKernel {V : ℝ → ℝ} (hV : Continuous V) :
    Continuous (logarithmicEnergyKernel V) := by
  have h₁ : Continuous (fun z : ℝ × ℝ ↦ (((V z.1 + V z.2) / 2 : ℝ) : EReal)) :=
    continuous_coe_real_ereal.comp
      (((hV.comp continuous_fst).add (hV.comp continuous_snd)).div_const 2)
  exact continuous_iff_continuousAt.mpr fun z ↦
    (EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))).comp
      ((h₁.prodMk continuous_log_ofReal_abs_sub.neg).continuousAt (x := z))

/-- A lower semicontinuous potential gives a lower semicontinuous weighted kernel. -/
theorem lowerSemicontinuous_logarithmicEnergyKernel {V : ℝ → ℝ} (hV : LowerSemicontinuous V) :
    LowerSemicontinuous (logarithmicEnergyKernel V) := by
  have hsum := (hV.comp continuous_fst).add (hV.comp continuous_snd)
  have hhalf : LowerSemicontinuous (fun z : ℝ × ℝ ↦ (V z.1 + V z.2) / 2) :=
    (continuous_id.div_const 2).comp_lowerSemicontinuous hsum
      (fun _ _ h ↦ div_le_div_of_nonneg_right h (by norm_num))
  exact (continuous_coe_real_ereal.comp_lowerSemicontinuous hhalf
    EReal.coe_strictMono.monotone).ereal_add continuous_log_ofReal_abs_sub.neg.lowerSemicontinuous

/-- A measurable potential gives a measurable weighted logarithmic kernel. -/
theorem measurable_logarithmicEnergyKernel {V : ℝ → ℝ} (hV : Measurable V) :
    Measurable (logarithmicEnergyKernel V) :=
  (((hV.comp measurable_fst).add (hV.comp measurable_snd)).div_const 2).coe_real_ereal.add
    continuous_log_ofReal_abs_sub.neg.measurable

/-- The part of the weighted kernel that controls escape of either coordinate to infinity. -/
def logarithmicConfinement (V : ℝ → ℝ) (x : ℝ) : ℝ :=
  V x / 2 - Real.log (1 + |x|)

theorem logarithmicConfinement_def (V : ℝ → ℝ) (x : ℝ) :
    logarithmicConfinement V x = V x / 2 - Real.log (1 + |x|) :=
  (rfl)

private theorem continuous_log_one_add_abs : Continuous (fun x : ℝ ↦ Real.log (1 + |x|)) := by
  have hpos (x : ℝ) : 0 < 1 + |x| := by positivity
  exact (continuous_const.add continuous_abs).log fun x ↦ (hpos x).ne'

theorem continuous_logarithmicConfinement {V : ℝ → ℝ} (hV : Continuous V) :
    Continuous (logarithmicConfinement V) :=
  (hV.div_const 2).sub continuous_log_one_add_abs

/-- A lower semicontinuous potential gives a lower semicontinuous confinement term. -/
theorem lowerSemicontinuous_logarithmicConfinement {V : ℝ → ℝ} (hV : LowerSemicontinuous V) :
    LowerSemicontinuous (logarithmicConfinement V) := by
  have hhalf : LowerSemicontinuous (fun x ↦ V x / 2) :=
    (continuous_id.div_const 2).comp_lowerSemicontinuous hV (monotone_id.div_const (by norm_num))
  exact hhalf.add continuous_log_one_add_abs.neg.lowerSemicontinuous

/-- A measurable potential gives a measurable confinement term. -/
theorem measurable_logarithmicConfinement {V : ℝ → ℝ} (hV : Measurable V) :
    Measurable (logarithmicConfinement V) :=
  (hV.div_const 2).sub (Real.measurable_log.comp (measurable_const.add continuous_abs.measurable))

/-- The sum of the two one-coordinate confinement terms bounds the interaction from below. -/
theorem coe_logarithmicConfinement_add_le_kernel (V : ℝ → ℝ) (z : ℝ × ℝ) :
    ((logarithmicConfinement V z.1 + logarithmicConfinement V z.2 : ℝ) : EReal) ≤
      logarithmicEnergyKernel V z := by
  obtain ⟨x, y⟩ := z
  by_cases h : x = y
  · simp [h]
  rw [logarithmicEnergyKernel_of_ne V h, EReal.coe_le_coe_iff]
  have hx : 0 < 1 + |x| := by positivity
  have hy : 0 < 1 + |y| := by positivity
  have hdist : |x - y| ≤ (1 + |x|) * (1 + |y|) := by
    have hprod := mul_nonneg (abs_nonneg x) (abs_nonneg y)
    linarith [abs_sub x y]
  have hlog := Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr h)) hdist
  rw [Real.log_mul hx.ne' hy.ne'] at hlog
  simp only [logarithmicConfinement]
  linarith

/-- A common lower bound `b` for the confinement term gives a kernel lower bound of `2 * b`. -/
theorem coe_two_mul_le_logarithmicEnergyKernel {V : ℝ → ℝ} {b : ℝ}
    (hb : ∀ x, b ≤ logarithmicConfinement V x) (z : ℝ × ℝ) :
    ((2 * b : ℝ) : EReal) ≤ logarithmicEnergyKernel V z := by
  refine le_trans ?_ (coe_logarithmicConfinement_add_le_kernel V z)
  rw [EReal.coe_le_coe_iff, two_mul]
  exact add_le_add (hb z.1) (hb z.2)

/-- An eventual lower bound strictly above two on the ratio of the external potential to
`log |x|` gives confinement. -/
theorem tendsto_logarithmicConfinement_of_eventually_le_div_log {V : ℝ → ℝ} {c : ℝ}
    (hc : 2 < c) (hV : ∀ᶠ x in cocompact ℝ, c ≤ V x / Real.log |x|) :
    Tendsto (logarithmicConfinement V) (cocompact ℝ) atTop := by
  have habs : Tendsto (fun x : ℝ ↦ |x|) (cocompact ℝ) atTop := by
    exact (tendsto_norm_cocompact_atTop (E := ℝ)).congr Real.norm_eq_abs
  have hcoeff : 0 < c / 2 - 1 := by linarith
  have hlead := (Real.tendsto_log_atTop.comp habs).atTop_mul_const hcoeff
  have herr : Tendsto (fun x : ℝ ↦ -(Real.log (|x| + 1) - Real.log |x|))
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_def, neg_zero] using
      ((Real.tendsto_log_comp_add_sub_log 1).comp habs).neg
  refine tendsto_atTop_mono' _ ?_ (hlead.atTop_add herr)
  filter_upwards [hV, habs.eventually_ge_atTop 2] with x hx hx'
  have hl := Real.log_pos (one_lt_two.trans_le hx')
  have hmul := (le_div_iff₀ hl).mp hx
  rw [logarithmicConfinement_def, add_comm (1 : ℝ) |x|]
  simp only [Function.comp_apply]
  nlinarith

/-- The quadratic potential of the Gaussian beta gas is confining. -/
theorem tendsto_logarithmicConfinement_sq_div_two :
    Tendsto (logarithmicConfinement (fun x : ℝ ↦ x ^ 2 / 2)) (cocompact ℝ) atTop := by
  have habs : Tendsto (fun x : ℝ ↦ |x|) (cocompact ℝ) atTop := by
    exact (tendsto_norm_cocompact_atTop (E := ℝ)).congr Real.norm_eq_abs
  refine tendsto_atTop_mono' _ ?_ habs
  filter_upwards [habs.eventually_ge_atTop 8] with x hx
  have hpos : 0 < 1 + |x| := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [logarithmicConfinement_def, ← sq_abs]
  nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hx)]

/-- A lower semicontinuous confinement term tending to infinity at infinity is bounded below. -/
theorem bddBelow_range_logarithmicConfinement {V : ℝ → ℝ} (hV : LowerSemicontinuous V)
    (hconf : Tendsto (logarithmicConfinement V) (cocompact ℝ) atTop) :
    BddBelow (range (logarithmicConfinement V)) := by
  obtain ⟨K, hK, hle⟩ := mem_cocompact.mp
    (hconf.eventually_ge_atTop (logarithmicConfinement V 0))
  obtain ⟨x, _, hx⟩ := LowerSemicontinuousOn.exists_isMinOn (insert_nonempty 0 K)
    (hK.insert 0) ((lowerSemicontinuous_logarithmicConfinement hV).lowerSemicontinuousOn _)
  refine ⟨logarithmicConfinement V x, ?_⟩
  rintro _ ⟨y, rfl⟩
  by_cases hy : y ∈ K
  · exact hx (mem_insert_of_mem 0 hy)
  · exact (hx (mem_insert 0 K)).trans (hle hy)

/-- Weighted logarithmic energy. For a kernel bounded below by a real constant, the energy
is its extended integral against the square of `μ`. The kernel is shifted by its infimum
before taking the nonnegative lower integral. -/
def logarithmicEnergy (V : ℝ → ℝ) (μ : ProbabilityMeasure ℝ) : EReal :=
  let b := (sInf (range (logarithmicEnergyKernel V))).toReal
  ((∫⁻ z, (logarithmicEnergyKernel V z - (b : EReal)).toENNReal ∂(μ.prod μ).toMeasure :
    ℝ≥0∞) : EReal) + (b : EReal)

private theorem lowerSemicontinuous_logarithmicEnergyKernel_sub_toENNReal {V : ℝ → ℝ}
    (hV : LowerSemicontinuous V) (a : ℝ) :
    LowerSemicontinuous (fun z ↦ (logarithmicEnergyKernel V z - (a : EReal)).toENNReal) := by
  simp only [sub_eq_add_neg, ← EReal.coe_neg]
  exact EReal.continuous_toENNReal.comp_lowerSemicontinuous
    ((lowerSemicontinuous_logarithmicEnergyKernel hV).ereal_add lowerSemicontinuous_const)
    (fun _ _ h ↦ EReal.toENNReal_le_toENNReal h)

/-- A shift by any real lower bound for the kernel gives the same energy. -/
theorem logarithmicEnergy_eq_lintegral_sub_add {V : ℝ → ℝ} (μ : ProbabilityMeasure ℝ)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z) :
    logarithmicEnergy V μ =
      ((∫⁻ z, (logarithmicEnergyKernel V z - (a : EReal)).toENNReal ∂(μ.prod μ).toMeasure :
        ℝ≥0∞) : EReal) + (a : EReal) := by
  let b := (sInf (range (logarithmicEnergyKernel V))).toReal
  have htop : sInf (range (logarithmicEnergyKernel V)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (sInf_le (mem_range_self ((0, 1) : ℝ × ℝ)))
    rw [logarithmicEnergyKernel_of_ne V zero_ne_one]
    exact EReal.coe_ne_top _
  have hb (z : ℝ × ℝ) : (b : EReal) ≤ logarithmicEnergyKernel V z :=
    (EReal.coe_toReal htop (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
      (le_sInf (by simpa only [forall_mem_range] using ha)))).le.trans
      (sInf_le (mem_range_self z))
  let ν := (μ.prod μ).toMeasure
  let J (r : ℝ) : EReal :=
    ((∫⁻ z, (logarithmicEnergyKernel V z - (r : EReal)).toENNReal ∂ν :
      ℝ≥0∞) : EReal) + (r : EReal)
  have heq (l u : ℝ) (hlu : l ≤ u) (hu : ∀ z, (u : EReal) ≤ logarithmicEnergyKernel V z) :
      J l = J u := by
    have hsub (z : ℝ × ℝ) :
        (logarithmicEnergyKernel V z - (l : EReal)).toENNReal =
          (logarithmicEnergyKernel V z - (u : EReal)).toENNReal + ENNReal.ofReal (u - l) := by
      rw [← EReal.real_coe_toENNReal, ← EReal.toENNReal_add,
        EReal.coe_sub, add_comm (logarithmicEnergyKernel V z - (u : EReal)),
        EReal.sub_coe_add_eq_add_sub, add_comm (u : EReal), EReal.sub_add_cancel]
      · exact EReal.sub_nonneg (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _)) |>.mpr
          (hu z)
      · exact EReal.coe_nonneg.mpr (sub_nonneg.mpr hlu)
    dsimp [J]
    simp_rw [hsub]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      EReal.coe_ennreal_add, ← EReal.real_coe_toENNReal, EReal.coe_toENNReal
        (EReal.coe_nonneg.mpr (sub_nonneg.mpr hlu)), add_assoc, EReal.coe_sub, EReal.sub_add_cancel]
  exact (heq (min a b) b (min_le_right ..) hb).symm.trans
    (heq (min a b) a (min_le_left ..) ha)

/-- The weighted logarithmic energy is lower semicontinuous for weak convergence. -/
theorem lowerSemicontinuous_logarithmicEnergy {V : ℝ → ℝ} (hV : LowerSemicontinuous V) :
    LowerSemicontinuous (logarithmicEnergy V) := by
  let b := (sInf (range (logarithmicEnergyKernel V))).toReal
  have hprod : Continuous (fun μ : ProbabilityMeasure ℝ ↦ μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  have hlin := (lowerSemicontinuous_lintegral_probabilityMeasure
    (lowerSemicontinuous_logarithmicEnergyKernel_sub_toENNReal hV b)).comp
    hprod
  exact (continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hlin
    EReal.coe_ennreal_strictMono.monotone).ereal_add lowerSemicontinuous_const

/-- A one-coordinate confinement moment is controlled by the energy above a global floor. -/
theorem lintegral_logarithmicConfinement_le_logarithmicEnergy {V : ℝ → ℝ}
    (hV : Measurable V) {b : ℝ} (hb : ∀ x, b ≤ logarithmicConfinement V x)
    (μ : ProbabilityMeasure ℝ) :
    ((∫⁻ x, ENNReal.ofReal (logarithmicConfinement V x - b) ∂μ.toMeasure :
      ℝ≥0∞) : EReal) +
      ((2 * b : ℝ) : EReal) ≤ logarithmicEnergy V μ := by
  rw [logarithmicEnergy_eq_lintegral_sub_add μ (coe_two_mul_le_logarithmicEnergyKernel hb)]
  have hm : Measurable (fun x ↦ ENNReal.ofReal (logarithmicConfinement V x - b)) :=
    ((measurable_logarithmicConfinement hV).sub measurable_const).ennreal_ofReal
  rw [ProbabilityMeasure.toMeasure_prod,
    ← (measurePreserving_fst (ν := μ.toMeasure)).lintegral_comp hm]
  gcongr
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  refine lintegral_mono fun z ↦ ?_
  rw [← EReal.real_coe_toENNReal]
  apply EReal.toENNReal_le_toENNReal
  apply (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr
  refine le_trans ?_ (coe_logarithmicConfinement_add_le_kernel V z)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith [hb z.2]

/-- Under confinement, the weak sublevel sets of the weighted energy are compact at every
finite level. -/
theorem isCompact_sublevel_logarithmicEnergy {V : ℝ → ℝ} (hV : LowerSemicontinuous V)
    (hconf : Tendsto (logarithmicConfinement V) (cocompact ℝ) atTop) (a : ℝ) :
    IsCompact {μ | logarithmicEnergy V μ ≤ (a : EReal)} := by
  let S := {μ | logarithmicEnergy V μ ≤ (a : EReal)}
  have hclosed : IsClosed S := (lowerSemicontinuous_logarithmicEnergy hV).isClosed_preimage _
  refine (isCompact_closure_of_isTightMeasureSet (S := S) ?_).of_isClosed_subset
    hclosed subset_closure
  refine isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr fun ε hε ↦ ?_
  by_cases ht : ε = ∞
  · exact ⟨∅, isCompact_empty, by simp [ht]⟩
  obtain ⟨b, hb⟩ := bddBelow_range_logarithmicConfinement hV hconf
  have hb' (x : ℝ) : b ≤ logarithmicConfinement V x := hb (mem_range_self x)
  let B := ENNReal.ofReal (a - 2 * b)
  let T := (B + 1) / ε
  have hTtop : T ≠ ∞ := ENNReal.div_ne_top (by simp [B]) hε.ne'
  have hT0 : T ≠ 0 := by simp [T, ht]
  obtain ⟨K, hK, hK'⟩ := mem_cocompact.mp (hconf.eventually_ge_atTop (b + T.toReal))
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hmoment :=
    (lintegral_logarithmicConfinement_le_logarithmicEnergy hV.measurable hb' μ).trans hμ
  have hbound : ∫⁻ x, ENNReal.ofReal (logarithmicConfinement V x - b) ∂μ.toMeasure ≤ B := by
    simpa only [B, EReal.toENNReal_coe, ← EReal.coe_sub, EReal.real_coe_toENNReal] using
      EReal.toENNReal_le_toENNReal ((EReal.le_sub_iff_add_le
        (.inl (EReal.coe_ne_bot _)) (.inl (EReal.coe_ne_top _))).mpr hmoment)
  have htail : T * μ.toMeasure Kᶜ ≤ B := by
    refine le_trans (mul_le_mul_right (measure_mono ?_) _) <| le_trans
      (mul_meas_ge_le_lintegral (((measurable_logarithmicConfinement hV.measurable).sub
        measurable_const).ennreal_ofReal) T) hbound
    intro x hx
    simp only [mem_ofPred_eq, Pi.sub_apply]
    rw [← ENNReal.ofReal_toReal hTtop]
    have hxK : b + T.toReal ≤ logarithmicConfinement V x := hK' hx
    exact ENNReal.ofReal_le_ofReal (le_sub_iff_add_le.mpr (add_comm b T.toReal ▸ hxK))
  calc
    μ.toMeasure Kᶜ ≤ B / T := (ENNReal.le_div_iff_mul_le (.inl hT0) (.inl hTtop)).mpr
      (by simpa only [mul_comm T] using htail)
    _ ≤ ε := (ENNReal.div_le_iff hT0 hTtop).mpr (by
      dsimp only [T]
      rw [ENNReal.mul_div_cancel hε.ne' ht]
      exact le_self_add)

/-- A probability measure with an atom has infinite weighted energy. -/
theorem logarithmicEnergy_eq_top_of_atom (V : ℝ → ℝ)
    (μ : ProbabilityMeasure ℝ) {x : ℝ} (hx : μ.toMeasure {x} ≠ 0) :
    logarithmicEnergy V μ = ⊤ := by
  let b := (sInf (range (logarithmicEnergyKernel V))).toReal
  let ν := (μ.prod μ).toMeasure
  let f (z : ℝ × ℝ) := (logarithmicEnergyKernel V z - (b : EReal)).toENNReal
  let A : Set (ℝ × ℝ) := ({x} : Set ℝ) ×ˢ {x}
  have hA : MeasurableSet A := (measurableSet_singleton x).prod (measurableSet_singleton x)
  have hμA : ν A ≠ 0 := by
    dsimp only [ν, A]
    rw [ProbabilityMeasure.toMeasure_prod, Measure.prod_prod]
    exact mul_ne_zero hx hx
  have hint : ∫⁻ z, f z ∂ν = ∞ := by
    apply top_unique
    calc
      ∞ = ∫⁻ z, A.indicator (fun _ ↦ ∞) z ∂ν := by
        rw [lintegral_indicator_const hA, ENNReal.top_mul]
        simp [hμA]
      _ ≤ ∫⁻ z, f z ∂ν := by
        apply lintegral_mono
        rintro ⟨p, q⟩
        by_cases hz : (p, q) ∈ A
        · obtain ⟨hp, hq⟩ := hz
          simp only [mem_singleton_iff] at hp hq
          simp [hp, hq, f]
        · simp [indicator_of_notMem hz]
  dsimp only [logarithmicEnergy]
  rw [hint, EReal.coe_ennreal_top, EReal.top_add_coe]

/-- When the potential and the pair logarithm are integrable and collisions have measure zero,
the weighted energy agrees with the difference of the two ordinary integrals. -/
theorem logarithmicEnergy_eq_integral_sub {V : ℝ → ℝ} (μ : ProbabilityMeasure ℝ)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (hV : Integrable V μ.toMeasure)
    (hlog : Integrable (fun z : ℝ × ℝ ↦ Real.log |z.1 - z.2|) (μ.prod μ).toMeasure)
    (hne : ∀ᵐ z ∂(μ.prod μ).toMeasure, z.1 ≠ z.2) :
    logarithmicEnergy V μ =
      ((∫ x, V x ∂μ.toMeasure) -
        ∫ z : ℝ × ℝ, Real.log |z.1 - z.2| ∂(μ.prod μ).toMeasure : ℝ) := by
  let ν := (μ.prod μ).toMeasure
  let F (z : ℝ × ℝ) := (V z.1 + V z.2) / 2 - Real.log |z.1 - z.2|
  have hs₁ : MeasurePreserving Prod.fst ν μ.toMeasure := measurePreserving_fst
  have hs₂ : MeasurePreserving Prod.snd ν μ.toMeasure := measurePreserving_snd
  have hi₁ : Integrable (V ∘ Prod.fst) ν :=
    (hs₁.integrable_comp hV.aestronglyMeasurable).mpr hV
  have hi₂ : Integrable (V ∘ Prod.snd) ν :=
    (hs₂.integrable_comp hV.aestronglyMeasurable).mpr hV
  have hsum : Integrable (fun z : ℝ × ℝ ↦ V z.1 + V z.2) ν := hi₁.add hi₂
  have hhalf : Integrable (fun z : ℝ × ℝ ↦ (V z.1 + V z.2) / 2) ν := hsum.div_const 2
  have hF : Integrable F ν := hhalf.sub hlog
  have hdiff : Integrable (fun z ↦ F z - a) ν := hF.sub (integrable_const a)
  have heq : ∀ᵐ z ∂ν, logarithmicEnergyKernel V z = (F z : EReal) :=
    hne.mono fun ⟨x, y⟩ h ↦ logarithmicEnergyKernel_of_ne V h
  have hnonneg : ∀ᵐ z ∂ν, 0 ≤ F z - a :=
    heq.mono fun z hz ↦ sub_nonneg.mpr (EReal.coe_le_coe_iff.mp (hz ▸ ha z))
  have hshift :
      (∫⁻ z, (logarithmicEnergyKernel V z - (a : EReal)).toENNReal ∂ν) =
        ENNReal.ofReal (∫ z, (F z - a) ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hdiff hnonneg]
    apply lintegral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  rw [logarithmicEnergy_eq_lintegral_sub_add μ ha, hshift, ← EReal.real_coe_toENNReal,
    EReal.coe_toENNReal (EReal.coe_nonneg.mpr (integral_nonneg_of_ae hnonneg)),
    ← EReal.coe_add, integral_sub hF (integrable_const a)]
  simp only [integral_const, probReal_univ, one_smul, sub_add_cancel, F]
  have hi₁' : Integrable (fun z : ℝ × ℝ ↦ V z.1) ν := hi₁
  have hi₂' : Integrable (fun z : ℝ × ℝ ↦ V z.2) ν := hi₂
  rw [integral_sub hhalf hlog, integral_div, integral_add hi₁' hi₂']
  simp only [ν, ProbabilityMeasure.toMeasure_prod, integral_fun_fst, integral_fun_snd,
    probReal_univ, one_smul]
  congr 1
  ring

/-- The energy attains a finite global minimum for a continuous confining potential.
Normalized Lebesgue measure on the unit interval supplies a finite-energy competitor. -/
theorem exists_isMinOn_logarithmicEnergy {V : ℝ → ℝ} (hV : Continuous V)
    (hconf : Tendsto (logarithmicConfinement V) (cocompact ℝ) atTop) :
    ∃ μ : ProbabilityMeasure ℝ,
      IsMinOn (logarithmicEnergy V) univ μ ∧ logarithmicEnergy V μ < ⊤ := by
  let ν : Measure ℝ := volume.restrict (Icc 0 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Icc]⟩
  let μ₀ : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  obtain ⟨b, hb⟩ := bddBelow_range_logarithmicConfinement hV.lowerSemicontinuous hconf
  have hne : ∀ᵐ z ∂(μ₀.prod μ₀).toMeasure, z.1 ≠ z.2 := by
    rw [ProbabilityMeasure.toMeasure_prod]
    have hm : MeasurableSet {z : ℝ × ℝ | z.1 ≠ z.2} :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    refine Eventually.of_forall fun x ↦ ?_
    have hzero : μ₀.toMeasure {x} = 0 := by
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans_eq Real.volume_singleton) bot_le
    have hset : {y : ℝ | x = y} = {x} := by ext y; simp [eq_comm]
    simpa only [ae_iff, not_not, hset] using hzero
  have hv : Integrable V ν := hV.continuousOn.integrableOn_compact isCompact_Icc
  have hval := logarithmicEnergy_eq_integral_sub μ₀
    (coe_two_mul_le_logarithmicEnergyKernel fun x ↦ hb (mem_range_self x)) hv
    (integrable_log_abs_sub_restrict_Icc_prod 0 1 0 1) hne
  have hfin : logarithmicEnergy V μ₀ < ⊤ := hval.symm ▸ EReal.coe_lt_top _
  let S := {μ | logarithmicEnergy V μ ≤ logarithmicEnergy V μ₀}
  have hS : IsCompact S := by
    dsimp only [S]
    rw [hval]
    exact isCompact_sublevel_logarithmicEnergy hV.lowerSemicontinuous hconf _
  have hμ₀ : μ₀ ∈ S := by simp [S]
  obtain ⟨μ, hμ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨μ₀, hμ₀⟩ hS
    ((lowerSemicontinuous_logarithmicEnergy hV.lowerSemicontinuous).lowerSemicontinuousOn S)
  refine ⟨μ, ?_, lt_of_le_of_lt hμ hfin⟩
  intro η _
  by_cases hη : η ∈ S
  · exact hmin hη
  · have hn : ¬ logarithmicEnergy V η ≤ logarithmicEnergy V μ₀ := hη
    exact hμ.trans (le_of_not_ge hn)

/-- The weighted energy centered at its infimum. For confining continuous potentials it
is the nonnegative part of the beta gas rate before multiplication by `β / 2`. -/
def logarithmicEnergyRate (V : ℝ → ℝ) (μ : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  (logarithmicEnergy V μ - ⨅ ν, logarithmicEnergy V ν).toENNReal

theorem logarithmicEnergyRate_def (V : ℝ → ℝ) (μ : ProbabilityMeasure ℝ) :
    logarithmicEnergyRate V μ = (logarithmicEnergy V μ - ⨅ ν, logarithmicEnergy V ν).toENNReal :=
  (rfl)

/-- The infimum of the weighted logarithmic energy over probability measures is above `-∞`. -/
theorem iInf_logarithmicEnergy_ne_bot (V : ℝ → ℝ) :
    (⨅ ν, logarithmicEnergy V ν) ≠ ⊥ := by
  let b := (sInf (range (logarithmicEnergyKernel V))).toReal
  have hb (μ : ProbabilityMeasure ℝ) : (b : EReal) ≤ logarithmicEnergy V μ :=
    le_add_of_nonneg_left (EReal.coe_ennreal_nonneg _)
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot b) (le_iInf hb)

/-- The energy infimum is real whenever a probability measure has finite energy. -/
theorem coe_toReal_iInf_logarithmicEnergy {V : ℝ → ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : logarithmicEnergy V μ < ⊤) :
    ((⨅ ν, logarithmicEnergy V ν).toReal : EReal) = ⨅ ν, logarithmicEnergy V ν :=
  EReal.coe_toReal (ne_top_of_le_ne_top hμ.ne (iInf_le _ μ)) (iInf_logarithmicEnergy_ne_bot V)

/-- With a finite-energy competitor, the centered rate subtracts the real energy infimum. -/
theorem logarithmicEnergyRate_eq_sub_toReal_iInf {V : ℝ → ℝ} {μ : ProbabilityMeasure ℝ}
    (hμ : logarithmicEnergy V μ < ⊤) (ν : ProbabilityMeasure ℝ) :
    logarithmicEnergyRate V ν =
      (logarithmicEnergy V ν - ((⨅ η, logarithmicEnergy V η).toReal : EReal)).toENNReal := by
  rw [logarithmicEnergyRate_def, coe_toReal_iInf_logarithmicEnergy hμ]

/-- A rate sublevel is the energy sublevel with threshold shifted by the energy infimum. -/
theorem logarithmicEnergyRate_le_iff {V : ℝ → ℝ} {μ : ProbabilityMeasure ℝ} {α : ℝ≥0∞} :
    logarithmicEnergyRate V μ ≤ α ↔
      logarithmicEnergy V μ ≤ (α : EReal) + ⨅ ν, logarithmicEnergy V ν := by
  rw [logarithmicEnergyRate_def, ← EReal.coe_ennreal_le_coe_ennreal_iff,
    EReal.coe_toENNReal_eq_max, max_le_iff, and_iff_right (EReal.coe_ennreal_nonneg α)]
  exact EReal.sub_le_iff_le_add (.inl (iInf_logarithmicEnergy_ne_bot V))
    (.inr (EReal.coe_ennreal_ne_bot α))

/-- The centered rate vanishes exactly at the global minimizers of the weighted energy. -/
@[simp]
theorem logarithmicEnergyRate_eq_zero_iff {V : ℝ → ℝ} {μ : ProbabilityMeasure ℝ} :
    logarithmicEnergyRate V μ = 0 ↔ IsMinOn (logarithmicEnergy V) univ μ := by
  rw [← nonpos_iff_eq_zero, logarithmicEnergyRate_le_iff, EReal.coe_ennreal_zero, zero_add,
    le_iInf_iff, isMinOn_iff]
  simp

/-- Centering the weighted energy at its minimum gives a good rate function. -/
theorem isGoodRateFunction_logarithmicEnergyRate {V : ℝ → ℝ} (hV : Continuous V)
    (hconf : Tendsto (logarithmicConfinement V) (cocompact ℝ) atTop) :
    IsGoodRateFunction (logarithmicEnergyRate V) := by
  obtain ⟨μ, _, hfin⟩ := exists_isMinOn_logarithmicEnergy hV hconf
  let m := (⨅ ν, logarithmicEnergy V ν).toReal
  have hm : (m : EReal) = ⨅ ν, logarithmicEnergy V ν :=
    coe_toReal_iInf_logarithmicEnergy hfin
  constructor
  · rw [funext (logarithmicEnergyRate_eq_sub_toReal_iInf hfin)]
    simp only [sub_eq_add_neg, ← EReal.coe_neg]
    apply EReal.continuous_toENNReal.comp_lowerSemicontinuous _
      (fun _ _ h ↦ EReal.toENNReal_le_toENNReal h)
    exact (lowerSemicontinuous_logarithmicEnergy hV.lowerSemicontinuous).ereal_add
      lowerSemicontinuous_const
  · intro α hα
    simpa only [logarithmicEnergyRate_le_iff, ← hm, ← EReal.coe_ennreal_toReal hα,
      ← EReal.coe_add] using
      isCompact_sublevel_logarithmicEnergy hV.lowerSemicontinuous hconf (α.toReal + m)

/-- The real-valued kernel capped at height `M`, including on the diagonal. -/
def truncatedLogarithmicEnergyKernel (V : ℝ → ℝ) (M : ℝ) (z : ℝ × ℝ) : ℝ :=
  (min (logarithmicEnergyKernel V z) (M : EReal)).toReal

/-- Coercing the capped kernel to the extended reals recovers the minimum. -/
theorem coe_truncatedLogarithmicEnergyKernel (V : ℝ → ℝ) (M : ℝ) (z : ℝ × ℝ) :
    (truncatedLogarithmicEnergyKernel V M z : EReal) =
      min (logarithmicEnergyKernel V z) (M : EReal) := by
  apply EReal.coe_toReal
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) (min_le_right ..)
  · exact (lt_min (bot_lt_iff_ne_bot.mpr (logarithmicEnergyKernel_ne_bot V z))
      (bot_lt_iff_ne_bot.mpr (EReal.coe_ne_bot M))).ne'

@[simp]
theorem truncatedLogarithmicEnergyKernel_diag (V : ℝ → ℝ) (M x : ℝ) :
    truncatedLogarithmicEnergyKernel V M (x, x) = M :=
  EReal.coe_injective (by simp [coe_truncatedLogarithmicEnergyKernel])

/-- The capped kernel is continuous in the ordinary real topology. -/
theorem continuous_truncatedLogarithmicEnergyKernel {V : ℝ → ℝ} (hV : Continuous V) (M : ℝ) :
    Continuous (truncatedLogarithmicEnergyKernel V M) := by
  refine EReal.continuousOn_toReal.comp_continuous
    ((continuous_logarithmicEnergyKernel hV).min continuous_const) fun z ↦ ?_
  have h := coe_truncatedLogarithmicEnergyKernel V M z
  rw [← h]
  simp

/-- Integrating the capped kernel yields the truncated energy. -/
def truncatedLogarithmicEnergy (V : ℝ → ℝ) (M : ℝ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  ∫ z, truncatedLogarithmicEnergyKernel V M z ∂(μ.prod μ).toMeasure

theorem truncatedLogarithmicEnergy_def (V : ℝ → ℝ) (M : ℝ) (μ : ProbabilityMeasure ℝ) :
    truncatedLogarithmicEnergy V M μ =
      ∫ z, truncatedLogarithmicEnergyKernel V M z ∂(μ.prod μ).toMeasure :=
  (rfl)

/-- With kernel floor `a` and cutoff `M`, the capped kernel takes values in `[min a M, M]`. -/
theorem truncatedLogarithmicEnergyKernel_bounds {V : ℝ → ℝ} (M : ℝ) {a : ℝ}
    (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z) (z : ℝ × ℝ) :
    min a M ≤ truncatedLogarithmicEnergyKernel V M z ∧
      truncatedLogarithmicEnergyKernel V M z ≤ M := by
  constructor <;> rw [← EReal.coe_le_coe_iff, coe_truncatedLogarithmicEnergyKernel]
  · exact le_min ((EReal.coe_le_coe_iff.mpr (min_le_left ..)).trans (ha z))
      (EReal.coe_le_coe_iff.mpr (min_le_right ..))
  · exact min_le_right ..

private def boundedTruncatedLogarithmicEnergyKernel {V : ℝ → ℝ} (hV : Continuous V)
    (M : ℝ) {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z) :
    BoundedContinuousFunction (ℝ × ℝ) ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨_, continuous_truncatedLogarithmicEnergyKernel hV M⟩
    (M - min a M) fun x y ↦ by
      have hx := truncatedLogarithmicEnergyKernel_bounds M ha x
      have hy := truncatedLogarithmicEnergyKernel_bounds M ha y
      rw [Real.dist_eq, abs_le]
      simp only [ContinuousMap.coe_mk]
      exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

/-- For a measurable potential with a lower-bounded kernel, the capped kernel is integrable
against any finite measure on the pair space. -/
theorem integrable_truncatedLogarithmicEnergyKernel {V : ℝ → ℝ} (hV : Measurable V)
    (M : ℝ) {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (ν : Measure (ℝ × ℝ)) [IsFiniteMeasure ν] :
    Integrable (truncatedLogarithmicEnergyKernel V M) ν := by
  have hm : Measurable (truncatedLogarithmicEnergyKernel V M) :=
    ((measurable_logarithmicEnergyKernel hV).min measurable_const).ereal_toReal
  refine (integrable_const (max (-min a M) M)).mono' hm.aestronglyMeasurable
    (.of_forall fun z ↦ ?_)
  obtain ⟨hl, hu⟩ := truncatedLogarithmicEnergyKernel_bounds M ha z
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨neg_le.mp ((neg_le_neg hl).trans (le_max_left ..)), hu.trans (le_max_right ..)⟩

/-- At every finite cutoff height the truncated energy is weakly continuous. -/
theorem continuous_truncatedLogarithmicEnergy {V : ℝ → ℝ} (hV : Continuous V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z) (M : ℝ) :
    Continuous (truncatedLogarithmicEnergy V M) :=
  (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (boundedTruncatedLogarithmicEnergyKernel hV M ha)).comp
    (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id))

/-- The truncated energies increase with the cutoff height. -/
theorem monotone_truncatedLogarithmicEnergy {V : ℝ → ℝ} (hV : Measurable V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z) (μ : ProbabilityMeasure ℝ) :
    Monotone fun M ↦ truncatedLogarithmicEnergy V M μ := by
  intro M N hMN
  dsimp only [truncatedLogarithmicEnergy]
  apply integral_mono (integrable_truncatedLogarithmicEnergyKernel hV M ha (μ.prod μ).toMeasure)
    (integrable_truncatedLogarithmicEnergyKernel hV N ha (μ.prod μ).toMeasure)
  intro z
  rw [← EReal.coe_le_coe_iff, coe_truncatedLogarithmicEnergyKernel,
    coe_truncatedLogarithmicEnergyKernel]
  exact min_le_min_left _ (EReal.coe_le_coe_iff.mpr hMN)

private theorem truncatedLogarithmicEnergy_sub_eq_lintegral {V : ℝ → ℝ} (hV : Measurable V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (μ : ProbabilityMeasure ℝ) {M : ℝ} (hM : a ≤ M) :
    (truncatedLogarithmicEnergy V M μ : EReal) - (a : EReal) =
      ((∫⁻ z, min ((logarithmicEnergyKernel V z - (a : EReal)).toENNReal)
        (ENNReal.ofReal (M - a))
        ∂(μ.prod μ).toMeasure : ℝ≥0∞) : EReal) := by
  let ν := (μ.prod μ).toMeasure
  let g := truncatedLogarithmicEnergyKernel V M
  have hi : Integrable g ν := integrable_truncatedLogarithmicEnergyKernel hV M ha ν
  have hpoint (z : ℝ × ℝ) :
      (g z : EReal) - (a : EReal) =
        min (logarithmicEnergyKernel V z - (a : EReal)) ((M - a : ℝ) : EReal) := by
    have hmono : Monotone (fun x : EReal ↦ x - (a : EReal)) :=
      fun _ _ h ↦ EReal.sub_le_sub h le_rfl
    rw [coe_truncatedLogarithmicEnergyKernel, hmono.map_min, EReal.coe_sub]
  have hnonneg (z : ℝ × ℝ) : 0 ≤ g z - a := by
    rw [← EReal.coe_nonneg, EReal.coe_sub, hpoint]
    exact le_min ((EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))).mpr
      (ha z)) (EReal.coe_nonneg.mpr (sub_nonneg.mpr hM))
  have hint : Integrable (fun z ↦ g z - a) ν := hi.sub (integrable_const a)
  have hι : (∫ z, g z - a ∂ν) = truncatedLogarithmicEnergy V M μ - a := by
    rw [integral_sub hi (integrable_const a), integral_const, probReal_univ, one_smul,
      truncatedLogarithmicEnergy_def]
  rw [← EReal.coe_sub, ← hι, ← EReal.coe_toENNReal
    (EReal.coe_nonneg.mpr (integral_nonneg hnonneg)), EReal.real_coe_toENNReal,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnonneg)]
  congr 1
  apply lintegral_congr
  intro z
  have hmono : Monotone EReal.toENNReal := fun _ _ h ↦ EReal.toENNReal_le_toENNReal h
  rw [← EReal.real_coe_toENNReal, EReal.coe_sub, hpoint, hmono.map_min, EReal.real_coe_toENNReal]

/-- For a lower semicontinuous potential with a lower-bounded kernel, the truncated energy is
weakly lower semicontinuous at every real cutoff height. -/
theorem lowerSemicontinuous_truncatedLogarithmicEnergy {V : ℝ → ℝ}
    (hV : LowerSemicontinuous V) {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (M : ℝ) : LowerSemicontinuous (truncatedLogarithmicEnergy V M) := by
  let b := min a M
  have hb (z : ℝ × ℝ) : (b : EReal) ≤ logarithmicEnergyKernel V z :=
    (EReal.coe_le_coe_iff.mpr (min_le_left a M)).trans (ha z)
  have heq (μ : ProbabilityMeasure ℝ) :
      (truncatedLogarithmicEnergy V M μ : EReal) =
        ((∫⁻ z, min ((logarithmicEnergyKernel V z - (b : EReal)).toENNReal)
          (ENNReal.ofReal (M - b))
          ∂(μ.prod μ).toMeasure : ℝ≥0∞) : EReal) + (b : EReal) := by
    rw [← truncatedLogarithmicEnergy_sub_eq_lintegral hV.measurable hb μ (min_le_right a M),
      EReal.sub_add_cancel]
  have hlin := (lowerSemicontinuous_lintegral_probabilityMeasure
    ((lowerSemicontinuous_logarithmicEnergyKernel_sub_toENNReal hV b).inf
      (lowerSemicontinuous_const (z := ENNReal.ofReal (M - b))))).comp
        (ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id))
  have hcoe : LowerSemicontinuous (fun μ ↦ (truncatedLogarithmicEnergy V M μ : EReal)) := by
    rw [funext heq]
    exact (continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hlin
      EReal.coe_ennreal_strictMono.monotone).ereal_add lowerSemicontinuous_const
  intro μ r hr
  simpa only [EReal.coe_lt_coe_iff] using hcoe μ (r : EReal) (EReal.coe_lt_coe_iff.mpr hr)

/-- The energy is the increasing supremum of the upper truncations,
with cutoffs tending to infinity in unit steps from any real lower bound for the kernel. -/
theorem logarithmicEnergy_eq_iSup_truncated {V : ℝ → ℝ} (hV : Measurable V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (μ : ProbabilityMeasure ℝ) :
    logarithmicEnergy V μ =
      ⨆ n : ℕ, (truncatedLogarithmicEnergy V (a + n) μ : EReal) := by
  let ν := (μ.prod μ).toMeasure
  let f (z : ℝ × ℝ) := (logarithmicEnergyKernel V z - (a : EReal)).toENNReal
  have hf : Measurable f :=
    ((measurable_logarithmicEnergyKernel hV).add_const (-(a : EReal))).ereal_toENNReal
  let J (n : ℕ) := ∫⁻ z, min (f z) (n : ℝ≥0∞) ∂ν
  have hJ : (∫⁻ z, f z ∂ν) = ⨆ n, J n := by
    have hmono : Monotone (fun n : ℕ ↦ fun z ↦ min (f z) (n : ℝ≥0∞)) :=
      fun _ _ hmn z ↦ min_le_min_left _ (Nat.cast_le.mpr hmn)
    rw [← lintegral_iSup (fun n ↦ hf.min measurable_const) hmono]
    exact lintegral_congr fun z ↦ by
      rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hfin (n : ℕ) : (J n : EReal) =
      (truncatedLogarithmicEnergy V (a + n) μ : EReal) - (a : EReal) := by
    have hn : a ≤ a + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    simpa only [J, f, ν, add_sub_cancel_left, ENNReal.ofReal_natCast] using
      (truncatedLogarithmicEnergy_sub_eq_lintegral hV ha μ hn).symm
  have hsup : ((⨆ n, J n : ℝ≥0∞) : EReal) = ⨆ n, (J n : EReal) :=
    Monotone.map_ciSup_of_continuousAt continuous_coe_ennreal_ereal.continuousAt
      EReal.coe_ennreal_strictMono.monotone
  rw [logarithmicEnergy_eq_lintegral_sub_add μ ha, hJ, hsup, AddQuantale.iSup_add_distrib]
  simp_rw [hfin, EReal.sub_add_cancel]

/-- For a measurable potential with a lower-bounded kernel, the truncated energy at every real
cutoff is at most the full logarithmic energy. -/
theorem coe_truncatedLogarithmicEnergy_le_logarithmicEnergy {V : ℝ → ℝ} (hV : Measurable V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    (M : ℝ) (μ : ProbabilityMeasure ℝ) :
    (truncatedLogarithmicEnergy V M μ : EReal) ≤ logarithmicEnergy V μ := by
  obtain ⟨n, hn⟩ := exists_nat_ge (M - a)
  have hM : M ≤ a + (n : ℝ) := sub_le_iff_le_add'.mp hn
  rw [logarithmicEnergy_eq_iSup_truncated hV ha]
  exact le_iSup_of_le n (EReal.coe_le_coe_iff.mpr (monotone_truncatedLogarithmicEnergy hV ha μ hM))

/-- For an empirical measure the truncated energy is the average over ordered pairs. -/
theorem truncatedLogarithmicEnergy_empiricalMeasureOfFintype (V : ℝ → ℝ)
    (M : ℝ) {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    truncatedLogarithmicEnergy V M (empiricalMeasureOfFintype x) =
      (∑ i, ∑ j, truncatedLogarithmicEnergyKernel V M (x i, x j)) /
        (Fintype.card ι : ℝ) ^ 2 := by
  classical
  set c := ((Fintype.card ι : ℕ) : ℝ≥0∞)⁻¹ with hc_def
  have hc : c ≠ ∞ := ENNReal.inv_ne_top.mpr (by exact_mod_cast Fintype.card_ne_zero)
  rw [truncatedLogarithmicEnergy_def, ProbabilityMeasure.toMeasure_prod]
  simp only [empiricalMeasureOfFintype_toMeasure, ← Measure.sum_fintype]
  rw [Measure.prod_sum]
  simp_rw [← hc_def, Measure.prod_smul_left, Measure.prod_smul_right, Measure.dirac_prod_dirac,
    smul_smul]
  rw [integral_sum_dirac (fun _ ↦ ENNReal.mul_ne_top hc hc), tsum_fintype, Fintype.sum_prod_type]
  simp only [hc_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul,
    ← Finset.mul_sum]
  ring

/-- The ordered off-diagonal sum of the weighted logarithmic kernel divided by the square of
the number of particles. Distinct indices at the same location give infinite energy. -/
def offDiagLogarithmicEnergy {ι : Type*} [Fintype ι] (V : ℝ → ℝ) (x : ι → ℝ) : EReal := by
  classical
  exact if Function.Injective x then
    (((∑ i, ∑ j ∈ Finset.univ.erase i, (logarithmicEnergyKernel V (x i, x j)).toReal) /
      (Fintype.card ι : ℝ) ^ 2 : ℝ) : EReal)
  else ⊤

/-- The off-diagonal energy of a collision-free configuration is its normalized pair sum. -/
theorem offDiagLogarithmicEnergy_of_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ℝ → ℝ) {x : ι → ℝ} (hx : Function.Injective x) :
    offDiagLogarithmicEnergy V x =
      (((∑ i, ∑ j ∈ Finset.univ.erase i, (logarithmicEnergyKernel V (x i, x j)).toReal) /
        (Fintype.card ι : ℝ) ^ 2 : ℝ) : EReal) := by
  classical
  simp [offDiagLogarithmicEnergy, hx]

/-- A repeated location makes the off-diagonal energy infinite. -/
@[simp]
theorem offDiagLogarithmicEnergy_eq_top_iff {ι : Type*} [Fintype ι]
    (V : ℝ → ℝ) (x : ι → ℝ) :
    offDiagLogarithmicEnergy V x = ⊤ ↔ ¬ Function.Injective x := by
  classical
  by_cases hx : Function.Injective x
  · simp [offDiagLogarithmicEnergy, hx]
  · simp [offDiagLogarithmicEnergy, hx]

/-- The off-diagonal energy recovers the beta gas exponent after adding back one copy of the
sum of the external potential. The logarithm sum is over ordered pairs. -/
theorem card_sq_mul_offDiagLogarithmicEnergy_add_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ℝ → ℝ) {x : ι → ℝ} (hx : Function.Injective x) :
    (Fintype.card ι : ℝ) ^ 2 * (offDiagLogarithmicEnergy V x).toReal + (∑ i, V (x i)) =
      (Fintype.card ι : ℝ) * (∑ i, V (x i)) -
        ∑ i, ∑ j ∈ Finset.univ.erase i, Real.log |x i - x j| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [offDiagLogarithmicEnergy_of_injective V hx, EReal.toReal_coe,
    mul_div_cancel₀ _ (pow_ne_zero _ hc)]
  have hterms :
      (∑ i, ∑ j ∈ Finset.univ.erase i, (logarithmicEnergyKernel V (x i, x j)).toReal) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, ((V (x i) + V (x j)) / 2 - Real.log |x i - x j|) := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun _ hj ↦ ?_
    rw [logarithmicEnergyKernel_of_ne V
      (fun h ↦ (Finset.ne_of_mem_erase hj) (hx h).symm), EReal.toReal_coe]
  have hcard (i : ι) : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_one]
  have hleft : (∑ i, ∑ _j ∈ Finset.univ.erase i, V (x i)) =
      ((Fintype.card ι : ℝ) - 1) * ∑ i, V (x i) := by
    simp_rw [Finset.sum_const, nsmul_eq_mul, hcard, Finset.mul_sum]
  have hright : (∑ i, ∑ j ∈ Finset.univ.erase i, V (x j)) =
      ((Fintype.card ι : ℝ) - 1) * ∑ i, V (x i) := by
    have hinner (i : ι) : (∑ j ∈ Finset.univ.erase i, V (x j)) = (∑ j, V (x j)) - V (x i) :=
      eq_sub_of_add_eq (Finset.sum_erase_add _ (fun j ↦ V (x j)) (Finset.mem_univ i))
    simp_rw [hinner, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp_rw [hterms, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hleft, hright]
  ring

/-- Capping the kernel bounds the off-diagonal energy from below after subtracting the diagonal
contribution `M / card ι` of the empirical measure. -/
theorem coe_truncatedLogarithmicEnergy_sub_le_offDiag (V : ℝ → ℝ) (M : ℝ)
    {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ((truncatedLogarithmicEnergy V M (empiricalMeasureOfFintype x) -
      M / (Fintype.card ι : ℝ) : ℝ) : EReal) ≤ offDiagLogarithmicEnergy V x := by
  classical
  by_cases hx : Function.Injective x
  swap
  · rw [(offDiagLogarithmicEnergy_eq_top_iff V x).mpr hx]
    exact le_top
  rw [offDiagLogarithmicEnergy_of_injective V hx, EReal.coe_le_coe_iff,
    truncatedLogarithmicEnergy_empiricalMeasureOfFintype]
  have hsum (i : ι) : (∑ j, truncatedLogarithmicEnergyKernel V M (x i, x j)) =
      (∑ j ∈ Finset.univ.erase i, truncatedLogarithmicEnergyKernel V M (x i, x j)) + M := by
    simpa only [truncatedLogarithmicEnergyKernel_diag] using
      (Finset.sum_erase_add _ (fun j ↦ truncatedLogarithmicEnergyKernel V M (x i, x j))
        (Finset.mem_univ i)).symm
  simp_rw [hsum]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcancel (s : ℝ) :
      (s + (Fintype.card ι : ℝ) * M) / (Fintype.card ι : ℝ) ^ 2 -
        M / (Fintype.card ι : ℝ) = s / (Fintype.card ι : ℝ) ^ 2 := by
    field_simp
    ring
  rw [hcancel]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j hj ↦ ?_
  have hne : x i ≠ x j := fun h ↦ (Finset.ne_of_mem_erase hj) (hx h).symm
  have htop : logarithmicEnergyKernel V (x i, x j) ≠ ⊤ := by
    rw [logarithmicEnergyKernel_of_ne V hne]
    exact EReal.coe_ne_top _
  rw [← EReal.coe_le_coe_iff, coe_truncatedLogarithmicEnergyKernel,
    EReal.coe_toReal htop (logarithmicEnergyKernel_ne_bot V _)]
  exact min_le_left ..

/-- Along empirical configurations with growing cardinality, the limiting measure's energy
bounds the limit inferior of the off-diagonal energies. -/
theorem logarithmicEnergy_le_liminf_offDiag {V : ℝ → ℝ} (hV : LowerSemicontinuous V)
    {a : ℝ} (ha : ∀ z, (a : EReal) ≤ logarithmicEnergyKernel V z)
    {ι : Type*} {l : Filter ι} {κ : ι → Type*} [∀ i, Fintype (κ i)]
    [∀ i, Nonempty (κ i)] (x : ∀ i, κ i → ℝ)
    (hcard : Tendsto (fun i ↦ (Fintype.card (κ i) : ℝ)) l atTop)
    {μ : ProbabilityMeasure ℝ}
    (hμ : Tendsto (fun i ↦ empiricalMeasureOfFintype (x i)) l (𝓝 μ)) :
    logarithmicEnergy V μ ≤ liminf (fun i ↦ offDiagLogarithmicEnergy V (x i)) l := by
  rw [logarithmicEnergy_eq_iSup_truncated hV.measurable ha]
  refine iSup_le fun n ↦ ?_
  let M := a + (n : ℝ)
  let f (p : ProbabilityMeasure ℝ × ℝ) : EReal :=
    (truncatedLogarithmicEnergy V M p.1 : EReal) + ((-p.2 : ℝ) : EReal)
  have hf : LowerSemicontinuous f :=
    (continuous_coe_real_ereal.comp_lowerSemicontinuous
      ((lowerSemicontinuous_truncatedLogarithmicEnergy hV ha M).comp continuous_fst)
      EReal.coe_strictMono.monotone).ereal_add
      (continuous_coe_real_ereal.comp continuous_snd.neg).lowerSemicontinuous
  have hlim := (hf.le_liminf (μ, 0)).trans
    ((hμ.prodMk_nhds (hcard.const_div_atTop M)).liminf_le_liminf_comp (u := f))
  simp only [f, ← EReal.coe_add, ← sub_eq_add_neg, sub_zero] at hlim
  exact hlim.trans (liminf_le_liminf (Eventually.of_forall fun i ↦
    coe_truncatedLogarithmicEnergy_sub_le_offDiag V M (x i)))

end TauCeti.Probability

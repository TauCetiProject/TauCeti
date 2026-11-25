/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Measure.Regular
public import TauCeti.Geometry.Euclidean.Volume.UnitBall
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Order.LiminfLimsup
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.Topology.Algebra.Order.Field
import TauCeti.Topology.Instances.ENNReal

/-!
# `k`-dimensional densities of a measure

Let `μ` be a measure on an extended metric space `X`, `k : ℕ` and `x : X`. The `k`-dimensional
**density ratio** of `μ` at `x` and radius `ρ > 0` is `μ (B_ρ(x)) / (ω_k ρ ^ k)`, where `B_ρ(x)`
is the open ball and `ω_k` is the volume of the unit ball of `ℝ ^ k`
(`TauCeti.unitBallVolume`, with `ω_1 = 2` and `ω_2 = π`). Its upper and lower limits as `ρ → 0⁺`
are the **upper and lower densities** `Θ^{*k}(μ, x)` and `Θ^k_*(μ, x)` in `[0, ∞]`, and the
**density** `Θ^k(μ, x)` exists and equals `θ` when the density ratio tends to `θ`
(`MeasureTheory.Measure.HasDensity`). These are the densities of geometric measure theory: the
`k`-dimensional Lebesgue measure has density `1` at every point
(`MeasureTheory.Measure.hasDensity_volume`), an atom has density `∞` for `k ≥ 1`
(`MeasureTheory.Measure.hasDensity_dirac_self`), and densities of the weight of a varifold
appear in the monotonicity formula and the rectifiability and compactness theorems.

This file proves:

* open and closed balls give the same upper density, the same lower density and the same density
  (`MeasureTheory.Measure.upperDensity_eq_limsup_closedEBall`,
  `MeasureTheory.Measure.lowerDensity_eq_liminf_closedEBall`,
  `MeasureTheory.Measure.hasDensity_iff_tendsto_closedEBall`);
* the density exists exactly when the lower and upper densities agree, densities are additive
  and positively homogeneous in the measure, and they only depend on the measure near the point;
* `x ↦ Θ^{*k}(μ, x)` is Borel measurable for every measure `μ`
  (`MeasureTheory.Measure.measurable_upperDensity`), since `x ↦ μ (B_r(x))` is lower
  semicontinuous (`MeasureTheory.Measure.lowerSemicontinuous_measure_eball`);
* in a metric space, the comparison of densities with the Euclidean Hausdorff measure `μHE[k]`:
  if `Θ^{*k}(μ, x) ≥ c` on `A`, then `c μHE[k] A ≤ μ U` for every open `U ⊇ A`
  (`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure_of_isOpen_of_le_upperDensity`);
  if `Θ^{*k}(μ, x) < c` on `A`, then `μ A ≤ 2 ^ k c μHE[k] A`
  (`MeasureTheory.Measure.measure_le_mul_euclideanHausdorffMeasure_of_upperDensity_lt`); and an
  outer regular measure has upper density `0` at `μHE[k]`-almost every point of a `μ`-null set
  (`MeasureTheory.Measure.ae_upperDensity_eq_zero_of_measure_eq_zero`). Applied to
  `μ = θ μHE[k]⌞Γ` and the complement of `Γ`, the last statement says that such a measure, when it
  is outer regular (for instance, when it is locally finite on a Euclidean space), has upper
  density zero at `μHE[k]`-almost every point off its carrier.

## References

* H. Federer, *Geometric Measure Theory*, 2.10.19.
* L. Simon, *Lectures on Geometric Measure Theory*, §3.
-/

public section

noncomputable section

open Filter Metric MeasureTheory Set Topology Module
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

open TauCeti

section PseudoEMetricSpace

variable {X : Type*} [PseudoEMetricSpace X] [MeasurableSpace X]

/-- The `k`-dimensional **density ratio** `μ (B_ρ(x)) / (ω_k ρ ^ k)` of `μ` at `x` and radius `ρ`,
in `[0, ∞]`, where `B_ρ(x)` is the open ball of radius `ρ` about `x` and `ω_k` is
`TauCeti.unitBallVolume k`. -/
def densityRatio (μ : Measure X) (k : ℕ) (x : X) (ρ : ℝ) : ℝ≥0∞ :=
  μ (eball x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k)

/-- The `k`-dimensional **density** `Θ^k(μ, x)` of `μ` at `x` exists and equals `θ ∈ [0, ∞]`: the
density ratio `μ (B_ρ(x)) / (ω_k ρ ^ k)` tends to `θ` as `ρ → 0⁺`. -/
def HasDensity (μ : Measure X) (k : ℕ) (x : X) (θ : ℝ≥0∞) : Prop :=
  Tendsto (μ.densityRatio k x) (𝓝[>] 0) (𝓝 θ)

/-- The `k`-dimensional **upper density** `Θ^{*k}(μ, x)`: the upper limit of the density ratio
`μ (B_ρ(x)) / (ω_k ρ ^ k)` as `ρ → 0⁺`. -/
def upperDensity (μ : Measure X) (k : ℕ) (x : X) : ℝ≥0∞ :=
  limsup (μ.densityRatio k x) (𝓝[>] 0)

/-- The `k`-dimensional **lower density** `Θ^k_*(μ, x)`: the lower limit of the density ratio
`μ (B_ρ(x)) / (ω_k ρ ^ k)` as `ρ → 0⁺`. -/
def lowerDensity (μ : Measure X) (k : ℕ) (x : X) : ℝ≥0∞ :=
  liminf (μ.densityRatio k x) (𝓝[>] 0)

variable {μ ν : Measure X} {k : ℕ} {x : X} {θ θ' : ℝ≥0∞}

theorem densityRatio_def (μ : Measure X) (k : ℕ) (x : X) (ρ : ℝ) :
    μ.densityRatio k x ρ =
      μ (eball x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k) :=
  (rfl)

theorem hasDensity_iff :
    μ.HasDensity k x θ ↔ Tendsto (μ.densityRatio k x) (𝓝[>] 0) (𝓝 θ) :=
  Iff.rfl

theorem upperDensity_def (μ : Measure X) (k : ℕ) (x : X) :
    μ.upperDensity k x = limsup (μ.densityRatio k x) (𝓝[>] 0) :=
  (rfl)

theorem lowerDensity_def (μ : Measure X) (k : ℕ) (x : X) :
    μ.lowerDensity k x = liminf (μ.densityRatio k x) (𝓝[>] 0) :=
  (rfl)

/-- The density ratio vanishes at nonpositive radii, where the ball is empty. -/
theorem densityRatio_of_nonpos (μ : Measure X) (k : ℕ) (x : X) {ρ : ℝ} (hρ : ρ ≤ 0) :
    μ.densityRatio k x ρ = 0 := by
  rw [densityRatio_def, ENNReal.ofReal_of_nonpos hρ, eball_zero, measure_empty, ENNReal.zero_div]

@[simp]
theorem densityRatio_zero (k : ℕ) (x : X) (ρ : ℝ) : (0 : Measure X).densityRatio k x ρ = 0 := by
  simp [densityRatio_def]

@[simp]
theorem densityRatio_add_measure (μ ν : Measure X) (k : ℕ) (x : X) (ρ : ℝ) :
    (μ + ν).densityRatio k x ρ = μ.densityRatio k x ρ + ν.densityRatio k x ρ := by
  simp only [densityRatio_def, add_apply, ENNReal.add_div]

@[simp]
theorem densityRatio_smul_measure (c : ℝ≥0∞) (μ : Measure X) (k : ℕ) (x : X) (ρ : ℝ) :
    (c • μ).densityRatio k x ρ = c * μ.densityRatio k x ρ := by
  simp only [densityRatio_def, smul_apply, smul_eq_mul, mul_div_assoc]

@[gcongr]
theorem densityRatio_mono (h : μ ≤ ν) (k : ℕ) (x : X) (ρ : ℝ) :
    μ.densityRatio k x ρ ≤ ν.densityRatio k x ρ :=
  ENNReal.div_le_div_right (h _) _

/-- The density is unique when it exists. -/
theorem HasDensity.unique (h : μ.HasDensity k x θ) (h' : μ.HasDensity k x θ') : θ = θ' :=
  tendsto_nhds_unique h h'

/-- Where the density exists, it is the upper density. -/
theorem HasDensity.upperDensity_eq (h : μ.HasDensity k x θ) : μ.upperDensity k x = θ :=
  h.limsup_eq

/-- Where the density exists, it is the lower density. -/
theorem HasDensity.lowerDensity_eq (h : μ.HasDensity k x θ) : μ.lowerDensity k x = θ :=
  h.liminf_eq

theorem lowerDensity_le_upperDensity (μ : Measure X) (k : ℕ) (x : X) :
    μ.lowerDensity k x ≤ μ.upperDensity k x :=
  liminf_le_limsup

/-- The density exists and equals `θ` exactly when the lower and upper densities both equal
`θ`. -/
theorem hasDensity_iff_lowerDensity_eq_and_upperDensity_eq :
    μ.HasDensity k x θ ↔ μ.lowerDensity k x = θ ∧ μ.upperDensity k x = θ :=
  ⟨fun h ↦ ⟨h.lowerDensity_eq, h.upperDensity_eq⟩,
    fun h ↦ tendsto_of_liminf_eq_limsup h.1 h.2⟩

/-- The density exists exactly when the upper density is at most the lower density, and then it
is the upper density. -/
theorem hasDensity_upperDensity_iff :
    μ.HasDensity k x (μ.upperDensity k x) ↔ μ.upperDensity k x ≤ μ.lowerDensity k x := by
  rw [hasDensity_iff_lowerDensity_eq_and_upperDensity_eq, and_iff_left rfl]
  exact ⟨fun h ↦ h.ge, fun h ↦ (lowerDensity_le_upperDensity μ k x).antisymm h⟩

/-- Densities add: for instance, two lines crossing at `x` give density `2` at `x`. -/
theorem HasDensity.add_measure (hμ : μ.HasDensity k x θ) (hν : ν.HasDensity k x θ') :
    (μ + ν).HasDensity k x (θ + θ') := by
  rw [hasDensity_iff, funext (densityRatio_add_measure μ ν k x)]
  exact Tendsto.add hμ hν

/-- Densities scale with the measure. The case `c = ∞`, `θ = 0` is excluded: `∞` times a positive
density ratio is `∞`. -/
theorem HasDensity.smul_measure (h : μ.HasDensity k x θ) {c : ℝ≥0∞} (hc : θ ≠ 0 ∨ c ≠ ∞) :
    (c • μ).HasDensity k x (c * θ) := by
  rw [hasDensity_iff, funext (densityRatio_smul_measure c μ k x)]
  exact ENNReal.Tendsto.const_mul h hc

theorem upperDensity_smul_measure {c : ℝ≥0∞} (hc : c ≠ ∞) (μ : Measure X) (k : ℕ) (x : X) :
    (c • μ).upperDensity k x = c * μ.upperDensity k x := by
  rw [upperDensity_def, funext (densityRatio_smul_measure c μ k x)]
  exact ENNReal.limsup_const_mul_of_ne_top hc

theorem lowerDensity_smul_measure {c : ℝ≥0∞} (hc : c ≠ ∞) (μ : Measure X) (k : ℕ) (x : X) :
    (c • μ).lowerDensity k x = c * μ.lowerDensity k x := by
  rw [lowerDensity_def, funext (densityRatio_smul_measure c μ k x)]
  exact ENNReal.liminf_const_mul_of_ne_top hc

@[gcongr]
theorem upperDensity_mono (h : μ ≤ ν) (k : ℕ) (x : X) :
    μ.upperDensity k x ≤ ν.upperDensity k x :=
  limsup_le_limsup (Eventually.of_forall (densityRatio_mono h k x))

@[gcongr]
theorem lowerDensity_mono (h : μ ≤ ν) (k : ℕ) (x : X) :
    μ.lowerDensity k x ≤ ν.lowerDensity k x :=
  liminf_le_liminf (Eventually.of_forall (densityRatio_mono h k x))

theorem hasDensity_zero (k : ℕ) (x : X) : (0 : Measure X).HasDensity k x 0 := by
  rw [hasDensity_iff, funext (densityRatio_zero k x)]
  exact tendsto_const_nhds

@[simp]
theorem upperDensity_zero (k : ℕ) (x : X) : (0 : Measure X).upperDensity k x = 0 := by
  rw [upperDensity_def, funext (densityRatio_zero k x)]
  exact limsup_const 0

@[simp]
theorem lowerDensity_zero (k : ℕ) (x : X) : (0 : Measure X).lowerDensity k x = 0 := by
  rw [lowerDensity_def, funext (densityRatio_zero k x)]
  exact liminf_const 0

/-! ### Locality -/

section Restrict

variable {U : Set X}

/-- Near `0`, the density ratios at `x` of `μ` restricted to a neighbourhood of `x` are those of
`μ`. -/
theorem densityRatio_restrict_eventuallyEq (hU : U ∈ 𝓝 x) (k : ℕ) :
    (μ.restrict U).densityRatio k x =ᶠ[𝓝[>] 0] μ.densityRatio k x := by
  obtain ⟨ε, hε, hεU⟩ := EMetric.mem_nhds_iff.1 hU
  have hlim : Tendsto ENNReal.ofReal (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
      nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with ρ hρ
  rw [densityRatio_def, densityRatio_def,
    restrict_eq_self _ ((eball_subset_eball hρ.le).trans hεU)]

/-- The density at `x` only depends on the measure near `x`. -/
theorem hasDensity_restrict_iff (hU : U ∈ 𝓝 x) :
    (μ.restrict U).HasDensity k x θ ↔ μ.HasDensity k x θ :=
  tendsto_congr' (densityRatio_restrict_eventuallyEq hU k)

/-- The upper density at `x` only depends on the measure near `x`. -/
theorem upperDensity_restrict (hU : U ∈ 𝓝 x) (k : ℕ) :
    (μ.restrict U).upperDensity k x = μ.upperDensity k x :=
  limsup_congr (densityRatio_restrict_eventuallyEq hU k)

/-- The lower density at `x` only depends on the measure near `x`. -/
theorem lowerDensity_restrict (hU : U ∈ 𝓝 x) (k : ℕ) :
    (μ.restrict U).lowerDensity k x = μ.lowerDensity k x :=
  liminf_congr (densityRatio_restrict_eventuallyEq hU k)

end Restrict

/-! ### Open and closed balls -/

section ClosedBall

/-- Enlarging the radius by a factor `c > 1`: the closed ball of radius `ρ` lies in the open ball
of radius `c ρ`, so its ratio is at most `c ^ k` times the density ratio at `c ρ`. -/
private lemma measure_closedEBall_div_le (μ : Measure X) (k : ℕ) (x : X) {c ρ : ℝ} (hc : 1 < c)
    (hρ : 0 < ρ) :
    μ (closedEBall x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k) ≤
      ENNReal.ofReal c ^ k * μ.densityRatio k x (c * ρ) := by
  have hc0 : 0 < c := zero_lt_one.trans hc
  have hC0 : ENNReal.ofReal c ^ k ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 hc0).ne'
  have hCtop : ENNReal.ofReal c ^ k ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsub : closedEBall x (ENNReal.ofReal ρ) ⊆ eball x (ENNReal.ofReal (c * ρ)) := fun y hy ↦
    (mem_closedEBall.1 hy).trans_lt <| (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc0 hρ)).2 <|
      lt_mul_of_one_lt_left hρ hc
  calc _ ≤ μ (eball x (ENNReal.ofReal (c * ρ))) / (unitBallVolume k * ENNReal.ofReal ρ ^ k) :=
        ENNReal.div_le_div_right (measure_mono hsub) _
    _ = _ := by
        rw [densityRatio_def, ENNReal.ofReal_mul hc0.le, mul_pow, mul_left_comm (unitBallVolume k),
          ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ hC0 hCtop]

/-- The upper density may be computed with closed balls. -/
theorem upperDensity_eq_limsup_closedEBall (μ : Measure X) (k : ℕ) (x : X) :
    μ.upperDensity k x = limsup (fun ρ : ℝ ↦
      μ (closedEBall x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k))
        (𝓝[>] 0) := by
  refine le_antisymm (limsup_le_limsup (Eventually.of_forall fun ρ ↦
    ENNReal.div_le_div_right (measure_mono eball_subset_closedEBall) _)) ?_
  refine ENNReal.le_of_forall_one_lt_le_ofReal_pow_mul k fun c hc ↦ ?_
  calc _ ≤ limsup (fun ρ ↦ ENNReal.ofReal c ^ k * μ.densityRatio k x (c * ρ)) (𝓝[>] 0) :=
        limsup_le_limsup (eventually_nhdsWithin_of_forall fun ρ hρ ↦
          measure_closedEBall_div_le μ k x hc hρ)
    _ = ENNReal.ofReal c ^ k * limsup (μ.densityRatio k x ∘ (c * ·)) (𝓝[>] 0) :=
        ENNReal.limsup_const_mul_of_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal c ^ k * μ.upperDensity k x := by
        rw [limsup_comp]
        gcongr
        exact limsup_le_limsup_of_le (tendsto_const_mul_nhdsGT_zero (zero_lt_one.trans hc))

/-- The lower density may be computed with closed balls. -/
theorem lowerDensity_eq_liminf_closedEBall (μ : Measure X) (k : ℕ) (x : X) :
    μ.lowerDensity k x = liminf (fun ρ : ℝ ↦
      μ (closedEBall x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k))
        (𝓝[>] 0) := by
  set g : ℝ → ℝ≥0∞ := fun ρ ↦
    μ (closedEBall x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k)
  refine le_antisymm (liminf_le_liminf (Eventually.of_forall fun ρ ↦
    ENNReal.div_le_div_right (measure_mono eball_subset_closedEBall) _)) ?_
  refine ENNReal.le_of_forall_one_lt_le_ofReal_pow_mul k fun c hc ↦ ?_
  have hc0 : 0 < c := zero_lt_one.trans hc
  calc liminf g (𝓝[>] 0) ≤ liminf (g ∘ (c⁻¹ * ·)) (𝓝[>] 0) := by
        rw [liminf_comp]
        exact liminf_le_liminf_of_le (tendsto_const_mul_nhdsGT_zero (inv_pos.2 hc0))
    _ ≤ liminf (fun ρ ↦ ENNReal.ofReal c ^ k * μ.densityRatio k x ρ) (𝓝[>] 0) :=
        liminf_le_liminf (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) ↦ by
          simpa [mul_inv_cancel_left₀ hc0.ne'] using
            measure_closedEBall_div_le μ k x hc (mul_pos (inv_pos.2 hc0) hρ))
    _ = ENNReal.ofReal c ^ k * μ.lowerDensity k x :=
        ENNReal.liminf_const_mul_of_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)

/-- The density may be computed with closed balls. -/
theorem hasDensity_iff_tendsto_closedEBall :
    μ.HasDensity k x θ ↔ Tendsto (fun ρ : ℝ ↦
      μ (closedEBall x (ENNReal.ofReal ρ)) / (unitBallVolume k * ENNReal.ofReal ρ ^ k))
        (𝓝[>] 0) (𝓝 θ) := by
  rw [hasDensity_iff_lowerDensity_eq_and_upperDensity_eq, lowerDensity_eq_liminf_closedEBall,
    upperDensity_eq_limsup_closedEBall]
  exact ⟨fun h ↦ tendsto_of_liminf_eq_limsup h.1 h.2, fun h ↦ ⟨h.liminf_eq, h.limsup_eq⟩⟩

end ClosedBall

/-! ### Measurability of the upper density -/

section Measurability

/-- The density ratio at a radius `ρ` is at most the supremum of the density ratios at
rational radii in `(0, ρ)`, because the open ball is the union of the smaller ones. -/
private lemma densityRatio_le_iSup_rat (μ : Measure X) (k : ℕ) (x : X) (ρ : ℝ) :
    μ.densityRatio k x ρ ≤ ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 ρ), μ.densityRatio k x q := by
  rw [densityRatio_def, measure_eball_eq_iSup_lt]
  simp_rw [ENNReal.iSup_div]
  refine iSup₂_le fun r hr ↦ ?_
  obtain ⟨q, hrq, hqρ⟩ := exists_rat_btwn (ENNReal.toReal_lt_of_lt_ofReal hr)
  refine le_iSup₂_of_le q ⟨ENNReal.toReal_nonneg.trans_lt hrq, hqρ⟩ ?_
  rw [densityRatio_def, ← ENNReal.ofReal_toReal hr.ne_top]
  gcongr

/-- The upper density as a countable infimum of countable suprema of density ratios. -/
private lemma upperDensity_eq_iInf_iSup_rat (μ : Measure X) (k : ℕ) (x : X) :
    μ.upperDensity k x = ⨅ n : ℕ, ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 (n + 1 : ℝ)⁻¹),
      μ.densityRatio k x q := by
  set T : ℝ → ℝ≥0∞ := fun ε ↦ ⨆ (q : ℚ) (_ : (q : ℝ) ∈ Ioo 0 ε), μ.densityRatio k x q
  have hT : ∀ ε, (⨆ ρ ∈ Ioo 0 ε, μ.densityRatio k x ρ) = T ε := fun ε ↦
    le_antisymm (iSup₂_le fun ρ hρ ↦ (densityRatio_le_iSup_rat μ k x ρ).trans
        (iSup₂_mono' fun q hq ↦ ⟨q, ⟨hq.1, hq.2.trans hρ.2⟩, le_rfl⟩))
      (iSup₂_le fun q hq ↦ le_iSup₂ (f := fun ρ (_ : ρ ∈ Ioo 0 ε) ↦ μ.densityRatio k x ρ)
        (q : ℝ) hq)
  have hTmono : Monotone T := fun ε ε' h ↦
    iSup₂_mono' fun q hq ↦ ⟨q, ⟨hq.1, hq.2.trans_le h⟩, le_rfl⟩
  rw [upperDensity_def, (nhdsGT_basis (0 : ℝ)).limsup_eq_iInf_iSup]
  simp_rw [hT]
  refine le_antisymm (le_iInf fun n ↦ iInf₂_le _ (by positivity)) (le_iInf₂ fun ε hε ↦ ?_)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact (iInf_le _ n).trans (hTmono (by simpa using hn.le))

variable [OpensMeasurableSpace X]

/-- The density ratio at a fixed radius is a Borel measurable function of the centre. -/
theorem measurable_densityRatio (μ : Measure X) (k : ℕ) (ρ : ℝ) :
    Measurable fun x ↦ μ.densityRatio k x ρ :=
  (lowerSemicontinuous_measure_eball μ _).measurable.div_const _

/-- The upper density `x ↦ Θ^{*k}(μ, x)` is Borel measurable, for every measure `μ`. -/
@[fun_prop]
theorem measurable_upperDensity (μ : Measure X) (k : ℕ) :
    Measurable fun x ↦ μ.upperDensity k x := by
  simp_rw [upperDensity_eq_iInf_iSup_rat]
  exact .iInf fun n ↦ .iSup fun q ↦ .iSup fun _ ↦ measurable_densityRatio μ k q

end Measurability

/-- An atom has `k`-dimensional density `∞` for `k ≥ 1`: the density ratio of the Dirac mass at
`x` is `1 / (ω_k ρ ^ k)`. -/
theorem hasDensity_dirac_self (x : X) (hk : k ≠ 0) : (dirac x).HasDensity k x ∞ := by
  have hlim : Tendsto (fun ρ : ℝ ↦ unitBallVolume k * ENNReal.ofReal ρ ^ k) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := unitBallVolume k)
      (ENNReal.Tendsto.pow (n := k) (ENNReal.continuous_ofReal.tendsto 0))
      (Or.inr (unitBallVolume_ne_top k))
    simpa [zero_pow hk] using this.mono_left nhdsWithin_le_nhds
  have := tendsto_inv_iff.2 hlim
  rw [ENNReal.inv_zero] at this
  refine this.congr' (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) ↦ ?_)
  rw [densityRatio_def, dirac_apply_of_mem (mem_eball_self (ENNReal.ofReal_pos.2 hρ)),
    ENNReal.div_eq_inv_mul, mul_one]

/-- An atom has upper density `∞` for `k ≥ 1`. -/
theorem upperDensity_dirac_self (x : X) (hk : k ≠ 0) : (dirac x).upperDensity k x = ∞ :=
  (hasDensity_dirac_self x hk).upperDensity_eq

end PseudoEMetricSpace

/-- Lebesgue measure on a real inner product space of dimension `k` has `k`-dimensional density
`1` at every point. -/
theorem hasDensity_volume {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (x : E) :
    (volume : Measure E).HasDensity (finrank ℝ E) x 1 := by
  refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) ↦ ?_)
  rw [densityRatio_def, eball_ofReal, volume_ball_eq_unitBallVolume_mul x hρ,
    ENNReal.div_self (unitBallVolume_mul_ofReal_pow_ne_zero _ hρ)
      (unitBallVolume_mul_ofReal_pow_ne_top _ _)]

/-! ### Comparison with the Euclidean Hausdorff measure -/

section Hausdorff

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- For `ρ > 0`, a lower bound `a ≤ m / (ω_k ρ ^ k)` on a density ratio is a lower bound
`a * volume (closedBall 0 ρ) ≤ m` in terms of the volume of a closed ball of `ℝ ^ k`. -/
private lemma le_div_unitBallVolume_mul_iff (k : ℕ) {a m : ℝ≥0∞} {ρ : ℝ} (hρ : 0 < ρ) :
    a ≤ m / (unitBallVolume k * ENNReal.ofReal ρ ^ k) ↔
      a * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) ρ) ≤ m := by
  rw [volume_closedBall_eq_unitBallVolume_mul (0 : EuclideanSpace ℝ (Fin k)) hρ.le,
    finrank_euclideanSpace_fin, ENNReal.le_div_iff_mul_le
      (Or.inl (unitBallVolume_mul_ofReal_pow_ne_zero k hρ))
      (Or.inl (unitBallVolume_mul_ofReal_pow_ne_top k ρ))]

/-- For `ρ > 0`, an upper bound `m / (ω_k ρ ^ k) ≤ a` on a density ratio is an upper bound
`m ≤ a * volume (closedBall 0 ρ)` in terms of the volume of a closed ball of `ℝ ^ k`. -/
private lemma div_unitBallVolume_mul_le_iff (k : ℕ) {a m : ℝ≥0∞} {ρ : ℝ} (hρ : 0 < ρ) :
    m / (unitBallVolume k * ENNReal.ofReal ρ ^ k) ≤ a ↔
      m ≤ a * volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) ρ) := by
  rw [volume_closedBall_eq_unitBallVolume_mul (0 : EuclideanSpace ℝ (Fin k)) hρ.le,
    finrank_euclideanSpace_fin, ENNReal.div_le_iff_le_mul
      (Or.inl (unitBallVolume_mul_ofReal_pow_ne_zero k hρ))
      (Or.inl (unitBallVolume_mul_ofReal_pow_ne_top k ρ))]

/-- **Lower density bound, open-set form.** If the upper density of `μ` is at least `c` at every
point of `A`, then `c * μHE[k] A ≤ μ U` for every open set `U` containing `A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure_of_isOpen_of_le_upperDensity (μ : Measure X)
    (k : ℕ) {c : ℝ≥0∞} {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U)
    (h : ∀ x ∈ A, c ≤ μ.upperDensity k x) :
    c * μHE[k] A ≤ μ U := by
  refine ENNReal.mul_le_of_forall_lt fun c' hc' b hb ↦
    le_trans (by gcongr) (?_ : c' * μHE[k] A ≤ μ U)
  refine mul_euclideanHausdorffMeasure_le_measure_of_isOpen μ k hU hAU fun x hx ↦ ?_
  refine ((frequently_lt_of_lt_limsup (by isBoundedDefault) (hc'.trans_le (h x hx))).and_eventually
    self_mem_nhdsWithin).mono fun ρ ⟨hlt, (hρ : 0 < ρ)⟩ ↦ ?_
  rw [densityRatio_def, eball_ofReal] at hlt
  exact ((le_div_unitBallVolume_mul_iff k hρ).1 hlt.le).trans (measure_mono ball_subset_closedBall)

/-- **Lower density bound.** If `μ` is outer regular and its upper density is at least `c` at
every point of `A`, then `c * μHE[k] A ≤ μ A`. -/
theorem mul_euclideanHausdorffMeasure_le_measure_of_le_upperDensity (μ : Measure X)
    [μ.OuterRegular] (k : ℕ) {c : ℝ≥0∞} {A : Set X} (h : ∀ x ∈ A, c ≤ μ.upperDensity k x) :
    c * μHE[k] A ≤ μ A := by
  refine le_of_forall_gt fun b hb ↦ ?_
  obtain ⟨U, hAU, hU, hUb⟩ := A.exists_isOpen_lt_of_lt b hb
  exact (mul_euclideanHausdorffMeasure_le_measure_of_isOpen_of_le_upperDensity μ k hU hAU
    h).trans_lt hUb

/-- The upper density bound for a finite constant `c`. -/
private lemma measure_le_mul_euclideanHausdorffMeasure_of_upperDensity_lt_of_ne_top
    (μ : Measure X) (k : ℕ) {c : ℝ≥0∞} (hc : c ≠ ∞) {A : Set X}
    (h : ∀ x ∈ A, μ.upperDensity k x < c) :
    μ A ≤ 2 ^ k * c * μHE[k] A := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hc0 : c ≠ 0 := (pos_of_gt (h x₀ hx₀)).ne'
  refine measure_le_mul_euclideanHausdorffMeasure μ k hc0 hc fun x hx ↦ ?_
  have hlt := h x hx
  rw [upperDensity_eq_limsup_closedEBall] at hlt
  filter_upwards [eventually_lt_of_limsup_lt hlt (by isBoundedDefault), self_mem_nhdsWithin]
    with ρ hρc (hρ : 0 < ρ)
  rw [closedEBall_ofReal hρ.le] at hρc
  exact (div_unitBallVolume_mul_le_iff k hρ).1 hρc.le

/-- **Upper density bound.** If the upper density of `μ` is less than `c` at every point of `A`,
then `μ A ≤ 2 ^ k * c * μHE[k] A`. For `c = ∞` this says that a `μHE[k]`-null set on which
the upper density is finite is `μ`-null. -/
theorem measure_le_mul_euclideanHausdorffMeasure_of_upperDensity_lt (μ : Measure X) (k : ℕ)
    {c : ℝ≥0∞} {A : Set X} (h : ∀ x ∈ A, μ.upperDensity k x < c) :
    μ A ≤ 2 ^ k * c * μHE[k] A := by
  rcases ne_or_eq c ∞ with hc | rfl
  · exact measure_le_mul_euclideanHausdorffMeasure_of_upperDensity_lt_of_ne_top μ k hc h
  rcases ne_or_eq (μHE[k] A) 0 with hA | hA
  · rw [ENNReal.mul_top (pow_ne_zero _ two_ne_zero), ENNReal.top_mul hA]
    exact le_top
  -- Split `A` according to an integer bound `n` on the upper density.
  set B : ℕ → Set X := fun n ↦ {x | x ∈ A ∧ μ.upperDensity k x < n}
  have hcover : A ⊆ ⋃ n, B n := fun x hx ↦
    mem_iUnion.2 ((ENNReal.exists_nat_gt (h x hx).ne).imp fun _ hn ↦ ⟨hx, hn⟩)
  have hB (n : ℕ) : μ (B n) = 0 := by
    have hle := measure_le_mul_euclideanHausdorffMeasure_of_upperDensity_lt_of_ne_top μ k
      (ENNReal.natCast_ne_top n) (A := B n) fun x hx ↦ hx.2
    have hBA : μHE[k] (B n) = 0 := measure_mono_null (fun x hx ↦ hx.1) hA
    rwa [hBA, mul_zero, nonpos_iff_eq_zero] at hle
  rw [measure_mono_null hcover (measure_iUnion_null hB)]
  exact zero_le

/-- **Zero upper density on a null set.** If `μ` is outer regular, then at `μHE[k]`-almost every
point of a `μ`-null set `A`, the upper density of `μ` is `0`. When `μ = θ μHE[k]⌞Γ` is outer
regular (for instance, locally finite on a Euclidean space), taking `A` to be the complement of `Γ`
gives the vanishing of the upper density off the carrier `Γ`. Outer regularity can fail for such
measures: for `θ = 1`, `Γ = ℝ ^ n` and `k < n`, a point has measure `0` while every nonempty open
set has infinite measure. -/
theorem ae_upperDensity_eq_zero_of_measure_eq_zero (μ : Measure X) [μ.OuterRegular] (k : ℕ)
    {A : Set X} (hA : μ A = 0) :
    ∀ᵐ x ∂μHE[k], x ∈ A → μ.upperDensity k x = 0 := by
  set B : ℕ → Set X := fun n ↦ {x | x ∈ A ∧ (n : ℝ≥0∞)⁻¹ ≤ μ.upperDensity k x}
  have hn (n : ℕ) : μHE[k] (B n) = 0 := by
    have hle := mul_euclideanHausdorffMeasure_le_measure_of_le_upperDensity μ k (A := B n)
      fun x hx ↦ hx.2
    have h0 : μ (B n) = 0 := measure_mono_null (fun x hx ↦ hx.1) hA
    rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at hle
    exact hle.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
  rw [ae_iff]
  refine measure_mono_null (fun x hx ↦ ?_) (measure_iUnion_null hn)
  have hx' : x ∈ A ∧ μ.upperDensity k x ≠ 0 := by simpa only [not_imp, mem_ofPred_eq] using hx
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hx'.2
  exact mem_iUnion.2 ⟨n, hx'.1, hn.le⟩

end Hausdorff

end MeasureTheory.Measure

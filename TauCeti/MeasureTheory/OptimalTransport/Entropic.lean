/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.KullbackLeibler.Tilted
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Basic

/-!
# Entropic optimal transport and the static Schrödinger problem

Two entropy-based transport problems share the coupling constraint of Kantorovich's problem.

* The **static Schrödinger problem** with reference measure `R` on `X × Y` minimises the relative
  entropy `klDiv π R` over the couplings `π` of `μ` and `ν`. Its value is
  `TauCeti.schroedingerValue R μ ν`.
* **Entropically regularised transport** at temperature `ε` adds `ε` times the relative entropy
  against the product of the marginals to the transport cost of a plan, and minimises
  `∫⁻ c dπ + ε * klDiv π (μ.prod ν)` over the same couplings. Its value is
  `TauCeti.entropicTransportCost c ε μ ν`.

The two are the same problem. For probability measures `μ`, `ν`, a cost that is finite
`μ.prod ν`-almost everywhere, and a positive temperature `ε`, let
`Z = ∫ e^{-c/ε} d(μ ⊗ ν)` be the partition function and `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)` the Gibbs
measure, which is Mathlib's tilted measure
`(μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)`. Then for every probability measure `π` on
`X × Y`
`∫ c dπ + ε * klDiv π (μ ⊗ ν) = ε * klDiv π R - ε * log Z`,
so the regularised value is `ε` times the Schrödinger value with reference `R`, shifted by the
free energy `-ε log Z ≥ 0`, and the two problems have the same optimal couplings.

## Main definitions

* `TauCeti.schroedingerValue R μ ν`: the infimum of `klDiv π R` over the couplings `π` of `μ`
  and `ν`.
* `TauCeti.entropicTransportCost c ε μ ν`: the infimum of `∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)`
  over the couplings `π` of `μ` and `ν`.

## Main statements

* `TauCeti.schroedingerValue_prod`: with the product of the marginals as reference, the
  Schrödinger value is `0`, attained by the product coupling.
* `TauCeti.entropicTransportCost_zero` and `TauCeti.transportCost_le_entropicTransportCost`: at
  zero temperature the regularised value is the transport cost, which it always dominates.
* `TauCeti.entropicTransportCost_const`: for a constant cost the regularised value is the
  constant; when it is finite, with `Mathlib`'s `InformationTheory.klDiv_eq_zero_iff`, the product
  coupling is then the unique optimal plan at positive temperature.
* `TauCeti.lintegral_add_mul_klDiv_eq_mul_klDiv_tilted`: the Gibbs identity above, plan by plan.
* `TauCeti.entropicTransportCost_eq_mul_schroedingerValue_add`: the same identity for the
  optimal values.
* `TauCeti.lintegral_add_mul_klDiv_eq_entropicTransportCost_iff`: a coupling is optimal for the
  regularised problem exactly when it is optimal for the Schrödinger problem with the Gibbs
  reference.

## Implementation notes

As for `TauCeti.transportCost`, both values are defined for arbitrary measures, with an
extended-nonnegative cost, as an iterated infimum over plans and proofs of `TauCeti.IsCoupling`,
so that an empty feasible set gives `∞`. The temperature `ε` is a nonnegative real number; the
value at `ε = 0` is the unregularised transport cost.

The Gibbs identity needs the cost to be finite `μ.prod ν`-almost everywhere, since otherwise the
Gibbs measure is not equivalent to `μ.prod ν`; a cost that is infinite on a set of positive
product measure constrains the support of every plan of finite entropy and is a separate,
degenerate regime. The identity holds for every probability measure `π` on `X × Y`, not only for
couplings, and in `ℝ≥0∞` with no integrability hypothesis: when `π` is not absolutely continuous
with respect to `μ.prod ν`, or has infinite cost, both sides are `∞`.

## References

* M. Nutz, *Introduction to Entropic Optimal Transport*, lecture notes, Columbia University, 2021,
  for the regularised problem, its Gibbs reference measure, and the reduction to minimising
  relative entropy.
* C. Léonard, *A survey of the Schrödinger problem and some of its connections with optimal
  transport*, Discrete Contin. Dyn. Syst. 34 (2014), for the static Schrödinger problem.
-/

public section

noncomputable section

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c c' : X × Y → ℝ≥0∞} {ε ε' : ℝ≥0} {π R : Measure (X × Y)} {μ : Measure X} {ν : Measure Y}
  {a : ℝ≥0∞}

/-! ### The static Schrödinger problem -/

/-- The value of the static Schrödinger problem with reference measure `R`: the infimum of the
relative entropy `klDiv π R` over the couplings `π` of `μ` and `ν`. It is `∞` when `μ` and `ν`
have no coupling, or no coupling of finite relative entropy. -/
def schroedingerValue (R : Measure (X × Y)) (μ : Measure X) (ν : Measure Y) : ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), klDiv π R

/-- The Schrödinger value as the infimum of the relative entropies of all feasible plans. -/
theorem schroedingerValue_def :
    schroedingerValue R μ ν = ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), klDiv π R :=
  (rfl)

/-- Every coupling bounds the Schrödinger value from above. -/
theorem schroedingerValue_le_klDiv (hπ : IsCoupling π μ ν) (R : Measure (X × Y)) :
    schroedingerValue R μ ν ≤ klDiv π R :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the Schrödinger value from below. -/
theorem le_schroedingerValue (h : ∀ π, IsCoupling π μ ν → a ≤ klDiv π R) :
    a ≤ schroedingerValue R μ ν :=
  le_iInf₂ h

/-- The Schrödinger value is below a threshold exactly when some coupling is. -/
theorem schroedingerValue_lt_iff :
    schroedingerValue R μ ν < a ↔ ∃ π, IsCoupling π μ ν ∧ klDiv π R < a := by
  simp only [schroedingerValue, iInf_lt_iff, exists_prop]

/-- With the product of the marginals as reference, the Schrödinger value is `0`: the product
coupling has zero relative entropy. By `InformationTheory.klDiv_eq_zero_iff` it is the only
coupling attaining this value. -/
@[simp]
theorem schroedingerValue_prod [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    schroedingerValue (μ.prod ν) μ ν = 0 :=
  nonpos_iff_eq_zero.1 <| (schroedingerValue_le_klDiv (isCoupling_prod μ ν) _).trans_eq
    (klDiv_self _)

/-! ### Entropically regularised transport -/

/-- The entropically regularised transport cost of `μ` and `ν` for the cost `c` at temperature
`ε`: the infimum of `∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)` over the couplings `π` of `μ` and
`ν`. It is `∞` when `μ` and `ν` have no coupling. -/
def entropicTransportCost (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) (μ : Measure X) (ν : Measure Y) :
    ℝ≥0∞ :=
  ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν))

/-- The regularised transport cost as the infimum of the regularised costs of all feasible
plans. -/
theorem entropicTransportCost_def :
    entropicTransportCost c ε μ ν =
      ⨅ (π : Measure (X × Y)) (_ : IsCoupling π μ ν), (∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)) :=
  (rfl)

/-- Every coupling bounds the regularised transport cost from above. -/
theorem entropicTransportCost_le (hπ : IsCoupling π μ ν) (c : X × Y → ℝ≥0∞) (ε : ℝ≥0) :
    entropicTransportCost c ε μ ν ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) :=
  iInf₂_le π hπ

/-- A bound valid on every coupling bounds the regularised transport cost from below. -/
theorem le_entropicTransportCost
    (h : ∀ π, IsCoupling π μ ν → a ≤ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν)) :
    a ≤ entropicTransportCost c ε μ ν :=
  le_iInf₂ h

/-- The regularised transport cost is below a threshold exactly when some coupling is. -/
theorem entropicTransportCost_lt_iff :
    entropicTransportCost c ε μ ν < a ↔
      ∃ π, IsCoupling π μ ν ∧ ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) < a := by
  simp only [entropicTransportCost, iInf_lt_iff, exists_prop]

/-- The regularised transport cost is monotone in the cost and in the temperature. -/
theorem entropicTransportCost_mono (hc : c ≤ c') (hε : ε ≤ ε') :
    entropicTransportCost c ε μ ν ≤ entropicTransportCost c' ε' μ ν :=
  iInf₂_mono fun _ _ ↦ add_le_add (lintegral_mono hc) (by gcongr)

/-- At zero temperature the regularised transport cost is the transport cost. -/
@[simp]
theorem entropicTransportCost_zero : entropicTransportCost c 0 μ ν = transportCost c μ ν := by
  simp [entropicTransportCost, transportCost_def]

/-- The regularised transport cost dominates the transport cost. -/
theorem transportCost_le_entropicTransportCost :
    transportCost c μ ν ≤ entropicTransportCost c ε μ ν := by
  rw [transportCost_def]
  exact iInf₂_mono fun _ _ ↦ le_self_add

/-- For a constant cost `a`, the regularised transport cost of two probability measures is `a`,
attained by the product coupling. Since a coupling `π` pays `a + ε * klDiv π (μ.prod ν)`, at
positive temperature and for finite `a` the product coupling is the only optimal plan, by
`InformationTheory.klDiv_eq_zero_iff`. -/
@[simp]
theorem entropicTransportCost_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a : ℝ≥0∞) (ε : ℝ≥0) : entropicTransportCost (fun _ ↦ a) ε μ ν = a := by
  refine le_antisymm ?_ (le_entropicTransportCost fun π hπ ↦ ?_)
  · refine (entropicTransportCost_le (isCoupling_prod μ ν) _ ε).trans_eq ?_
    simp [klDiv_self]
  · have := hπ.isProbabilityMeasure
    simp

/-! ### The Gibbs reformulation -/

/-- **The Gibbs identity.** For probability measures `μ` and `ν`, a cost `c` finite
`μ.prod ν`-almost everywhere, and a positive temperature `ε`, every probability measure `π` on
`X × Y` satisfies `∫ c dπ + ε * klDiv π (μ ⊗ ν) = ε * klDiv π R - ε * log Z`, where
`Z = ∫ e^{-c/ε} d(μ ⊗ ν)` and `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)` is the Gibbs measure, written as the
tilted measure `(μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)`. Both sides may be `∞`. -/
theorem lintegral_add_mul_klDiv_eq_mul_klDiv_tilted [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsProbabilityMeasure π] (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) =
      ε * klDiv π ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) +
        ε * ENNReal.ofReal (-Real.log (∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν)) := by
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε
  by_cases hπ : π ≪ μ.prod ν
  swap
  · have hπR : ¬ π ≪ (μ.prod ν).tilted fun z ↦ -((c z).toReal / ε) :=
      fun h ↦ hπ (h.trans (tilted_absolutelyContinuous _ _))
    simp [klDiv_of_not_ac hπ, klDiv_of_not_ac hπR, ENNReal.mul_top hε']
  have hεpos : (0 : ℝ) < ε := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hε)
  have hcost : (ε : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ((c z).toReal / ε) ∂π = ∫⁻ z, c z ∂π := by
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hπ.ae_le hc_top] with z hz
    rw [ENNReal.ofReal_div_of_pos hεpos, ENNReal.ofReal_toReal hz, ENNReal.ofReal_coe_nnreal,
      ENNReal.mul_div_cancel hε' ENNReal.coe_ne_top]
  rw [← hcost, ← mul_add, ← klDiv_tilted_neg_add_ofReal_neg_log
    (hc.ennreal_toReal.div_const _) (ae_of_all _ fun z ↦ by positivity), mul_add]

/-- **The Gibbs reformulation of entropic transport.** For probability measures `μ` and `ν`, a
cost `c` finite `μ.prod ν`-almost everywhere, and a positive temperature `ε`, the regularised
transport cost is `ε` times the value of the Schrödinger problem with the Gibbs reference
measure `R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)`, plus the free energy `-ε log Z`. -/
theorem entropicTransportCost_eq_mul_schroedingerValue_add [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    entropicTransportCost c ε μ ν =
      ε * schroedingerValue ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) μ ν +
        ε * ENNReal.ofReal (-Real.log (∫ z, Real.exp (-((c z).toReal / ε)) ∂μ.prod ν)) := by
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε
  simp only [entropicTransportCost, schroedingerValue,
    ENNReal.mul_iInf_of_ne hε' ENNReal.coe_ne_top, ENNReal.iInf_add]
  refine iInf_congr fun π ↦ iInf_congr fun hπ ↦ ?_
  have := hπ.isProbabilityMeasure
  exact lintegral_add_mul_klDiv_eq_mul_klDiv_tilted hc hc_top hε

/-- A coupling is optimal for the regularised transport problem at positive temperature exactly
when it is optimal for the Schrödinger problem with the Gibbs reference measure
`R = Z⁻¹ e^{-c/ε} (μ ⊗ ν)`, for a cost finite `μ.prod ν`-almost everywhere. -/
theorem lintegral_add_mul_klDiv_eq_entropicTransportCost_iff [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hπ : IsCoupling π μ ν) (hc : AEMeasurable c (μ.prod ν))
    (hc_top : ∀ᵐ z ∂μ.prod ν, c z ≠ ∞) (hε : ε ≠ 0) :
    ∫⁻ z, c z ∂π + ε * klDiv π (μ.prod ν) = entropicTransportCost c ε μ ν ↔
      klDiv π ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) =
        schroedingerValue ((μ.prod ν).tilted fun z ↦ -((c z).toReal / ε)) μ ν := by
  have := hπ.isProbabilityMeasure
  rw [lintegral_add_mul_klDiv_eq_mul_klDiv_tilted hc hc_top hε,
    entropicTransportCost_eq_mul_schroedingerValue_add hc hc_top hε,
    ENNReal.add_left_inj (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top),
    ENNReal.mul_right_inj (ENNReal.coe_ne_zero.2 hε) ENNReal.coe_ne_top]

end TauCeti

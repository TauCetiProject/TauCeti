/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Countable
public import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The total of the root-count integrals

For a nonarchimedean local field `K`, the root counts over the totally ramified degree-`n`
subextensions of a separable closure sum to `n` almost everywhere on the Eisenstein region.
Integrating this identity gives
`∑' L, ∫⁻ a in eisensteinSet K n, L.rootCount a ∂μ = n * μ (eisensteinSet K n)`.
Countability of the family and almost-everywhere measurability of each root count justify
interchanging the sum and integral, also in equal characteristic.

This identity is the global counting step in the mass formula: evaluating the individual
integrals in terms of discriminant exponents then determines the weighted count of extensions.
The total is finite, and its real-valued counterpart is a convergent sum of ordinary integrals.
No normalization of Haar measure is needed until the explicit volume formula is substituted.

Dividing by the volume of the Eisenstein region, which is positive and finite, turns the identity
into Serre's first mass formula `∑' L, q ^ (-c(L)) = n` as soon as each integral is known: the
weighted count equals `n` exactly when the root-count integrals add up to
`∑' L, q ^ (-c(L)) * μ (eisensteinSet K n)`. For Haar measure normalized on the integer box,
`q ^ (-c(L))` times the volume `q ^ (-n) (1 - q⁻¹)` of the region is `q ^ (-(d(L) + 1)) (1 - q⁻¹)`,
because `c(L) + n = d(L) + 1`. So Serre's local integral `q ^ (-(d(L) + 1)) (1 - q⁻¹)` for every
`L` implies the mass formula.

## Main results

* `TauCeti.tsum_lintegral_rootCount_eq`: the root-count integrals over `σ_K(n)` add up to
  `n * μ (eisensteinSet K n)`.
* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent_eq_iff_tsum_lintegral_rootCount_eq`:
  the first mass formula is equivalent to the root-count integrals adding up to
  `∑' L, q ^ (-c(L)) * μ (eisensteinSet K n)`.
* `TauCeti.tsum_one_div_natCard_residueField_pow_wildExponent_eq_of_lintegral_rootCount_eq`: the
  first mass formula follows from Serre's value of each root-count integral.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open MeasureTheory ValuativeRel
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {n : ℕ}
  [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]

/-- The root-count integrals over all totally ramified degree-`n` subextensions add up to
`n` times the volume of the Eisenstein region. This holds for any additive Haar measure,
including in equal characteristic. -/
theorem tsum_lintegral_rootCount_eq (hn : 0 < n)
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    ∑' L : totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinSet K n, (L.1.rootCount a : ℝ≥0∞) ∂μ =
        n * μ (eisensteinSet K n) := by
  have := (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
  rw [← lintegral_tsum fun L ↦ aemeasurable_rootCount_restrict_eisensteinSet μ L.2,
    lintegral_congr_ae (ae_tsum_rootCount_eq hn μ)]
  simp

/-- For Haar measure normalized on the integer box, the sum of root-count integrals is
`n * q⁻ⁿ * (1 - q⁻¹)`, where `q` is the residue cardinality. -/
theorem tsum_lintegral_rootCount_eq_of_normalized (hn : 0 < n)
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure]
    (hμ : μ (integerBox K (Fin n)) = 1) :
    ∑' L : totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinSet K n, (L.1.rootCount a : ℝ≥0∞) ∂μ =
        n * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ n *
          (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
  rw [tsum_lintegral_rootCount_eq hn μ, measure_eisensteinSet hn μ hμ]

/-- The ordinary real root-count integrals form a convergent series whose sum is `n` times
the real volume of the Eisenstein region, including when the family of extensions is infinite. -/
theorem hasSum_integral_rootCount (hn : 0 < n)
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    HasSum (fun L : totallyRamifiedOfDegree K n ↦
      ∫ a in eisensteinSet K n, (L.1.rootCount a : ℝ) ∂μ)
      ((n : ℝ) * (μ (eisensteinSet K n)).toReal) := by
  have htotal : ∑' L : totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinSet K n, (L.1.rootCount a : ℝ≥0∞) ∂μ ≠ ∞ := by
    rw [tsum_lintegral_rootCount_eq hn μ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (measure_eisensteinSet_lt_top μ).ne
  have hreal (L : totallyRamifiedOfDegree K n) :
      ∫ a in eisensteinSet K n, (L.1.rootCount a : ℝ) ∂μ =
        (∫⁻ a in eisensteinSet K n, (L.1.rootCount a : ℝ≥0∞) ∂μ).toReal := by
    simpa only [ENNReal.toReal_natCast] using integral_toReal
      (aemeasurable_rootCount_restrict_eisensteinSet μ L.2)
      (Filter.Eventually.of_forall fun a ↦ ENNReal.natCast_lt_top (L.1.rootCount a))
  have hs := ENNReal.hasSum_toReal htotal
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top htotal),
    tsum_lintegral_rootCount_eq hn μ, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hs
  simpa only [← hreal] using hs

/-- **Theorem 1 in integral form**: for any additive Haar measure `μ`, the weighted count
`∑ q ^ (-c(L))` of the totally ramified degree-`n` subextensions equals `n` exactly when the
root-count integrals add up to `∑ q ^ (-c(L)) * μ(E_n)`, where `E_n` is the Eisenstein region.
The total of the integrals is `n * μ(E_n)`, and `μ(E_n)` is positive and finite. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent_eq_iff_tsum_lintegral_rootCount_eq
    (hn : 0 < n) (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = n ↔
      ∑' L : totallyRamifiedOfDegree K n,
        ∫⁻ a in eisensteinSet K n, (L.1.rootCount a : ℝ≥0∞) ∂μ =
        ∑' L : totallyRamifiedOfDegree K n,
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent * μ (eisensteinSet K n) := by
  rw [tsum_lintegral_rootCount_eq hn μ, ENNReal.tsum_mul_right, eq_comm,
    ENNReal.mul_left_inj (measure_eisensteinSet_pos μ).ne' (measure_eisensteinSet_lt_top μ).ne]

/-- For `L ∈ σ_K(n)` and Haar measure normalized on the integer box, `q ^ (-c(L))` times the
volume `q ^ (-n) (1 - q⁻¹)` of the Eisenstein region is `q ^ (-(d(L) + 1)) (1 - q⁻¹)`, where
`d(L)` is the discriminant exponent; this uses `c(L) + n = d(L) + 1`. -/
theorem _root_.IntermediateField.one_div_pow_wildExponent_mul_measure_eisensteinSet
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.wildExponent * μ (eisensteinSet K n) =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.discriminantExponent + 1) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ by
    simp [h, totallyRamifiedOfDegree_zero] at hL
  have hc : L.wildExponent + n = L.discriminantExponent + 1 := by
    have := IntermediateField.natCast_wildExponent hL
    omega
  rw [measure_eisensteinSet hn μ hμ, ← mul_assoc, ← hc]
  simp only [one_div]
  rw [ENNReal.inv_pow, ENNReal.inv_pow, ENNReal.inv_pow, pow_add]

/-- **Theorem 1 from the root-count integrals**: if, for Haar measure normalized on the integer
box, the root count of each `L ∈ σ_K(n)` integrates over the Eisenstein region to Serre's value
`q ^ (-(d(L) + 1)) (1 - q⁻¹)`, then `∑ q ^ (-c(L)) = n`. -/
theorem tsum_one_div_natCard_residueField_pow_wildExponent_eq_of_lintegral_rootCount_eq
    (hn : 0 < n) (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure]
    (hμ : μ (integerBox K (Fin n)) = 1)
    (h : ∀ L ∈ totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (L.discriminantExponent + 1) *
          (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) :
    ∑' L : totallyRamifiedOfDegree K n, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent = n :=
  (tsum_one_div_natCard_residueField_pow_wildExponent_eq_iff_tsum_lintegral_rootCount_eq hn
    μ).2 <| tsum_congr fun L ↦ by
    rw [h L L.2, L.1.one_div_pow_wildExponent_mul_measure_eisensteinSet L.2 μ hμ]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Strata
import TauCeti.NumberTheory.LocalField.MassFormula.Total
import TauCeti.RingTheory.Valuation.ValuativeRel.ResidueCard
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Krasner's discriminant-refined count of totally ramified extensions

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `σ_K(n)`
(`TauCeti.totallyRamifiedOfDegree K n`) be the family of totally ramified degree-`n` subextensions
of `SeparableClosure K`. Integrating the root-count identity `∑_{L ∈ σ_K(n)} L.rootCount a = n`
(`TauCeti.tsum_rootCount_eq_of_separable`) over Krasner's discriminant box
`TauCeti.eisensteinBox K n j` localizes the sum to those `L ∈ σ_K(n)` with `L.wildExponent = j`,
where each root-count integral equals `q ^ (-(n + j)) (1 - q⁻¹)`.

Comparing this localized integral with the Haar volume of `eisensteinBox K n j` proves uniformly in
mixed and equal characteristic that
`({E ∈ σ_K(n) | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j` (generalizing the `p`-adic
count of Krasner and Pauli–Roblot, Theorem 6.1, to equal characteristic). Combining this with the
box-independent stratum finiteness and mass-formula identities from
`TauCeti.NumberTheory.LocalField.MassFormula.Strata` yields consistency with Serre's first mass
formula and expresses `#σ_K(n)` as the finite sum of `krasnerCount K n j` whenever `(n : K) ≠ 0`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's box expression for the cardinality of
  `{E ∈ σ_K(n) | E.wildExponent = j}`.

## Main results

* `TauCeti.krasnerCount_eq_zero_iff`, `TauCeti.krasnerCount_zero_left`,
  `TauCeti.krasnerCount_one_left`, `TauCeti.krasnerCount_of_not_dvd`: vanishing and tame
  evaluation of `krasnerCount`.
* `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_mul_measure`,
  `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow`: measure and
  cleared-denominator stratum count identities.
* `TauCeti.natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCount`: Krasner's
  refined count `({E ∈ σ_K(n) | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j`.
* `TauCeti.hasSum_krasnerCount_div_natCard_residueField_pow`: consistency of `krasnerCount` with
  Serre's first mass formula.
* `TauCeti.natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount`: finite total count away from
  `(n : K) = 0`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, C. R. Acad. Sci. Paris
  **254** (1962), 3470–3472; Colloques Internationaux du CNRS **143**, Paris, 1966, 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1 (stated over `p`-adic fields; this
  module extends the refined count uniformly to equal characteristic).
-/

public section
noncomputable section

open ValuativeRel MeasureTheory
open scoped IntermediateField ENNReal NNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

open Classical in
variable (K) in
/-- **Krasner's discriminant-refined count**: `0` unless `IsOreAdmissible 𝒪[K] n j`, and otherwise
`n * q ^ ((n + j - 1) - ∑_{1 ≤ h < n} ν_h) * (if j % n = 0 then 1 else 1 - q⁻¹)`, where
`q = Nat.card 𝓀[K]` and `ν_h = oreCoefficientDepth 𝒪[K] n j h`. -/
def krasnerCount (n j : ℕ) : ℚ :=
  if IsOreAdmissible 𝒪[K] n j then
    (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹)
  else 0

open Classical in
variable (K) in
/-- Unfolding `TauCeti.krasnerCount`. -/
theorem krasnerCount_def (n j : ℕ) :
    krasnerCount K n j =
      if IsOreAdmissible 𝒪[K] n j then
        (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
          ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h : ℕ) : ℤ)) *
            (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹)
      else 0 := by
  rw [krasnerCount]

/-- For an Ore-admissible wild exponent, `krasnerCount` evaluates to Krasner's box formula. -/
theorem krasnerCount_of_isOreAdmissible {n j : ℕ} (h : IsOreAdmissible 𝒪[K] n j) :
    krasnerCount K n j =
      (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
        ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h : ℕ) : ℤ)) *
          (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹) := by
  rw [krasnerCount, ite_eq_left h]

/-- Outside Ore's admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible 𝒪[K] n j) :
    krasnerCount K n j = 0 := by
  rw [krasnerCount, ite_eq_right h]

/-- `krasnerCount K n j` vanishes if and only if `(n, j)` is not Ore-admissible over `𝒪[K]`. -/
@[simp]
theorem krasnerCount_eq_zero_iff {n j : ℕ} :
    krasnerCount K n j = 0 ↔ ¬ IsOreAdmissible 𝒪[K] n j := by
  by_cases hadm : IsOreAdmissible 𝒪[K] n j
  · rw [iff_false_right (not_not.mpr hadm), krasnerCount_of_isOreAdmissible hadm]
    have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hadm.pos.ne'
    have hq0 : (Nat.card 𝓀[K] : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hsub : (if j % n = 0 then (1 : ℚ) else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹) ≠ 0 := by
      split_ifs
      · exact one_ne_zero
      · exact sub_ne_zero.mpr
          (ne_of_gt (inv_lt_one_of_one_lt₀ (by exact_mod_cast Finite.one_lt_card)))
    exact mul_ne_zero (mul_ne_zero hn (zpow_ne_zero _ hq0)) hsub
  · exact iff_of_true (krasnerCount_of_not_isOreAdmissible hadm) hadm

variable (K) in
/-- `krasnerCount K 0 j = 0`. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

variable (K) in
/-- In degree `1`, `krasnerCount K 1 j` is `1` at `j = 0` and `0` otherwise. -/
@[simp]
theorem krasnerCount_one_left (j : ℕ) : krasnerCount K 1 j = if j = 0 then 1 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [krasnerCount_of_isOreAdmissible (isOreAdmissible_one_iff.mpr rfl)]
  · simp [hj, krasnerCount_of_not_isOreAdmissible (mt isOreAdmissible_one_iff.mp hj)]

/-- In the tame case (`¬ ringChar 𝓀[K] ∣ n`), `krasnerCount K n j` is `n` at `j = 0` and `0`
otherwise. -/
theorem krasnerCount_of_not_dvd {n j : ℕ} (hp : ¬ ringChar 𝓀[K] ∣ n) :
    krasnerCount K n j = if j = 0 then n else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [ite_eq_left rfl, krasnerCount_of_isOreAdmissible
      ((isOreAdmissible_iff_eq_zero_of_not_dvd (R := 𝒪[K]) hp).mpr rfl)]
    simp [Nat.card_Ico]
  · simp [hj, krasnerCount_of_not_isOreAdmissible
      (mt (isOreAdmissible_iff_eq_zero_of_not_dvd (R := 𝒪[K]) hp).mp hj)]

/-- Core integral identity on `eisensteinBox K n j`: the `encard` of the stratum
`{E ∈ σ_K(n) | E.wildExponent = j}` times `q ^ (-(n + j)) (1 - q⁻¹)` equals
`n * μ (eisensteinBox K n j)`. -/
private theorem encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      n * μ (eisensteinBox K n j) := by
  classical
  set w : ℝ≥0∞ := 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
  calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) * w
      = ∑' L : totallyRamifiedOfDegree K n, if L.val.wildExponent = j then w else 0 :=
          ((ENNReal.tsum_subtype_ite (totallyRamifiedOfDegree K n) (fun E ↦ E.wildExponent = j)
              fun _ ↦ w).trans
            (ENNReal.tsum_set_const _ w)).symm
    _ = ∑' L : totallyRamifiedOfDegree K n,
          ∫⁻ a in eisensteinBox K n j, (L.val.rootCount a : ℝ≥0∞) ∂μ :=
          tsum_congr fun L ↦ (L.val.lintegral_rootCount_eisensteinBox L.property μ hμ).symm
    _ = n * μ (eisensteinBox K n j) := by
          refine tsum_lintegral_rootCount_eq_of_subset μ
            (eisensteinBox_subset_eisensteinSet K n j)
            (ae_restrict_of_forall_mem measurableSet_eisensteinBox fun a ha ↦ ?_)
          obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
            (eisensteinBox_subset_eisensteinSet K n j ha)
          exact tsum_rootCount_eq_of_separable he hf
            (separable_monicOfCoeff_of_mem_eisensteinBox ha)

/-- **Krasner's count in measure form**: for a left-invariant measure `μ` normalized on the integer
box,
`#{E ∈ σ_K(n) | E.wildExponent = j} = n * q ^ (n + j) * μ (eisensteinBox K n j) / (1 - q⁻¹)`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_mul_measure {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      n * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) /
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hid := encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox (j := j) μ hμ
  rw [← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe] at hid
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  have hpow : q ^ (n + j) * (1 / q ^ (n + j)) = 1 := by
    rw [one_div, ENNReal.mul_inv_cancel
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]
  refine (ENNReal.eq_div_iff (one_sub_one_div_natCard_residueField_ne_zero (K := K))
    (ENNReal.sub_ne_top ENNReal.one_ne_top)).mpr ?_
  calc (1 - 1 / q) * ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞)
      = q ^ (n + j) * (1 / q ^ (n + j)) *
          ((1 - 1 / q) *
            ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞)) := by
          rw [hpow, one_mul]
    _ = q ^ (n + j) *
          (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
            (1 / q ^ (n + j) * (1 - 1 / q))) := by ring
    _ = n * q ^ (n + j) * μ (eisensteinBox K n j) := by rw [hid]; ring

/-- Auxiliary weighted equality after cancelling `1 - q⁻¹` on an Ore-admissible stratum. -/
private theorem ncard_wildExponent_eq_mul_one_div_pow {n j : ℕ} (hadm : IsOreAdmissible 𝒪[K] n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) =
      (n : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
          (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  obtain ⟨μ, _, hμ⟩ := exists_addHaarMeasure_integerBox_eq_one K (Fin n)
  have hid := ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_mul_measure (j := j) μ hμ
  rw [measure_eisensteinBox hadm μ hμ] at hid
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  have hpow : q ^ (n + j) / q ^ (n + j) = 1 :=
    ENNReal.div_self (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  have hsub : (1 - 1 / q) / (1 - 1 / q) = 1 :=
    ENNReal.div_self (one_sub_one_div_natCard_residueField_ne_zero (K := K))
      (ENNReal.sub_ne_top ENNReal.one_ne_top)
  rw [hid]
  calc
    n * q ^ (n + j) * (1 / q ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) *
        (1 - 1 / q) * (if j % n = 0 then 1 else 1 - 1 / q)) / (1 - 1 / q) * (1 / q ^ (n + j))
      = n * (1 / q ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h)) *
          (if j % n = 0 then 1 else 1 - 1 / q) * (q ^ (n + j) / q ^ (n + j)) *
          ((1 - 1 / q) / (1 - 1 / q)) := by
          simp only [div_eq_mul_inv]; ring
    _ = _ := by rw [hpow, hsub, mul_one, mul_one]

private theorem natCast_ncard_wildExponent_eq_div_pow_real {n j : ℕ}
    (hadm : IsOreAdmissible 𝒪[K] n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) /
        (Nat.card 𝓀[K] : ℝ) ^ (n + j) =
      (n : ℝ) /
        (Nat.card 𝓀[K] : ℝ) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ)) := by
  have h := congrArg ENNReal.toReal (ncard_wildExponent_eq_mul_one_div_pow hadm)
  have hite :
      (if j % n = 0 then (1 : ℝ≥0∞) else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)).toReal =
        if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ) := by
    split_ifs
    · exact ENNReal.toReal_one
    · rw [ENNReal.toReal_sub_of_le
        (by rw [one_div]; exact ENNReal.inv_le_one.mpr (by exact_mod_cast Nat.card_pos))
        ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_one,
        ENNReal.toReal_natCast]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_div, hite] at h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    div_eq_mul_inv, one_mul] using h

/-- Exact `ℕ` clearing-denominators identity for `{E ∈ σ_K(n) | E.wildExponent = j}.ncard` when
`IsOreAdmissible 𝒪[K] n j`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow {n j : ℕ}
    (hadm : IsOreAdmissible 𝒪[K] n j) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
      Nat.card 𝓀[K] ^ (2 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) =
      n * Nat.card 𝓀[K] ^ (n + j) *
        (if j % n = 0 then Nat.card 𝓀[K] else Nat.card 𝓀[K] - 1) := by
  have hR := natCast_ncard_wildExponent_eq_div_pow_real hadm
  have hq0 : (Nat.card 𝓀[K] : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  apply Nat.cast_injective (R := ℝ)
  push_cast
  have hexp : 2 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h =
      (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) + 1 := by omega
  rw [hexp, pow_succ]
  split_ifs at hR ⊢
  · field_simp at hR ⊢
    exact hR
  · rw [Nat.cast_sub Finite.one_lt_card.le, Nat.cast_one]
    field_simp at hR ⊢
    linear_combination hR

/-- **Krasner's discriminant-refined count**: for all `n` and `j`, the number of totally ramified
degree-`n` subextensions of `SeparableClosure K` with wild exponent `j` equals
`krasnerCount K n j`. -/
theorem natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCount (n j : ℕ) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
      krasnerCount K n j := by
  by_cases hadm : IsOreAdmissible 𝒪[K] n j
  · have hQ := congrArg (Nat.cast (R := ℚ))
      (ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow (K := K) hadm)
    have hn := hadm.pos
    have hq0 : (Nat.card 𝓀[K] : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hpow0 :
        (Nat.card 𝓀[K] : ℚ) ^ (2 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) ≠ 0 :=
      pow_ne_zero _ hq0
    push_cast at hQ
    rw [Nat.cast_sub Finite.one_lt_card.le, Nat.cast_one] at hQ
    have hnum : (Nat.card 𝓀[K] : ℚ) ^ (n + j) =
        (Nat.card 𝓀[K] : ℚ) ^ (n + j - 1) * (Nat.card 𝓀[K] : ℚ) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have hden : (Nat.card 𝓀[K] : ℚ) ^ (2 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) =
        (Nat.card 𝓀[K] : ℚ) ^ (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth 𝒪[K] n j h) *
          (Nat.card 𝓀[K] : ℚ) ^ 2 := by
      rw [add_comm, pow_add]
    rw [eq_div_of_mul_eq hpow0 hQ, krasnerCount_of_isOreAdmissible hadm, zpow_sub₀ hq0,
      zpow_natCast, zpow_natCast, hnum, hden]
    split_ifs <;> field_simp
  · rw [krasnerCount_of_not_isOreAdmissible hadm,
      setOf_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_empty_iff.mpr hadm,
      Set.ncard_empty, Nat.cast_zero]

/-- Real `HasSum` consistency of `krasnerCount` with Serre's first mass formula. -/
theorem hasSum_krasnerCount_div_natCard_residueField_pow (n : ℕ) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  let f : ℕ → ℝ≥0∞ := fun j ↦
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ j
  have htsum : ∑' j : ℕ, f j = n := tsum_ncard_wildExponent_div_natCard_residueField_pow n
  have hsum_ne_top : ∑' j : ℕ, f j ≠ ⊤ := htsum ▸ ENNReal.natCast_ne_top n
  have hf_ne_top : ∀ j, f j ≠ ⊤ := fun j ↦
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
  have hreal := ENNReal.hasSum_toReal hsum_ne_top
  rw [← ENNReal.tsum_toReal_eq hf_ne_top, htsum, ENNReal.toReal_natCast] at hreal
  refine hreal.congr_fun fun j ↦ ?_
  have hkr : (krasnerCount K n j : ℝ) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) := by
    exact_mod_cast
      (natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCount (K := K) n j).symm
  simp [f, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, hkr]

/-- Away from `(n : K) = 0`, `((totallyRamifiedOfDegree K n).ncard : ℚ)` is the finite sum of
`krasnerCount K n j` for `0 ≤ j ≤ n * v_K(n)`. -/
theorem natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦
    natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_krasnerCount (K := K) n j

end TauCeti

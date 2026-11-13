/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Countable

/-!
# Krasner's discriminant-refined count of totally ramified extensions

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `σ_K(n)`
(`TauCeti.totallyRamifiedOfDegree K n`) be the family of totally ramified degree-`n` subextensions
of `SeparableClosure K`. Integrating the root-count identity `∑_{L ∈ σ_K(n)} L.rootCount a = n`
over Krasner's discriminant box `TauCeti.eisensteinBox K n j` localizes the sum to those
`L ∈ σ_K(n)` with `L.wildExponent = j`, where each root-count integral equals
`q ^ (-(n + j)) (1 - q⁻¹)`.

Comparing this localized integral with the Haar volume of `eisensteinBox K n j` proves uniformly in
mixed and equal characteristic that every wild-exponent stratum `{E ∈ σ_K(n) | E.wildExponent = j}`
and every bounded-discriminant stratum `{E ∈ σ_K(n) | E.discriminantExponent ≤ D}` is finite, and
that `({E ∈ σ_K(n) | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j`. Summing over `j`
recovers Serre's first mass formula, gives the isomorphism-class stratum mass `#{c = j} / n`, and
yields the finite total count `#σ_K(n)` whenever `(n : K) ≠ 0`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's box expression for the cardinality of
  `{E ∈ σ_K(n) | E.wildExponent = j}`.

## Main results

* `TauCeti.finite_mem_totallyRamifiedOfDegree_wildExponent_eq`,
  `TauCeti.finite_mem_totallyRamifiedOfDegree_discriminantExponent_le`: finiteness of each fixed
  wild-exponent and bounded-discriminant stratum in any characteristic.
* `TauCeti.natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq`: Krasner's refined count
  `({E ∈ σ_K(n) | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j`.
* `TauCeti.tsum_ncard_wildExponent_div_natCard_residueField_pow`,
  `TauCeti.hasSum_krasnerCount_div_natCard_residueField_pow`: consistency with Serre's first mass
  formula.
* `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: isomorphism-class
  stratum mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #{c = j} / n`.
* `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`,
  `TauCeti.natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount`: finite total count away from
  `(n : K) = 0`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps p-adique*, C. R. Acad. Sci. Paris
  **254** (1962), 3470–3472; Colloques Internationaux du CNRS **143**, Paris, 1966, 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
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
/-- **Krasner's discriminant-refined count**: `0` unless `IsOreAdmissible K n j`, and otherwise
`n * q ^ ((n + j - 1) - ∑_{1 ≤ h < n} ν_h) * (if j % n = 0 then 1 else 1 - q⁻¹)`, where
`q = Nat.card 𝓀[K]` and `ν_h = oreCoefficientDepth K n j h`. -/
def krasnerCount (n j : ℕ) : ℚ :=
  if IsOreAdmissible K n j then
    (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹)
  else 0

/-- Outside Ore's admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  rw [krasnerCount, ite_eq_right h]

variable (K) in
/-- `krasnerCount K 0 j = 0`. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

variable (K) in
/-- In degree `1`, `krasnerCount K 1 j` is `1` at `j = 0` and `0` otherwise. -/
@[simp]
theorem krasnerCount_one_left (j : ℕ) : krasnerCount K 1 j = if j = 0 then 1 else 0 := by
  rw [krasnerCount, isOreAdmissible_one_iff]
  by_cases hj : j = 0 <;> simp [hj]

/-- In the tame case (`¬ ringChar 𝓀[K] ∣ n` and `0 < n`), `krasnerCount K n j` is `n` at `j = 0`
and `0` otherwise. -/
theorem krasnerCount_of_not_dvd {n j : ℕ} (hn : 0 < n) (hp : ¬ ringChar 𝓀[K] ∣ n) :
    krasnerCount K n j = if j = 0 then n else 0 := by
  rw [krasnerCount, isOreAdmissible_iff_eq_zero_of_not_dvd hn hp]
  by_cases hj : j = 0
  · subst hj
    have hdepth (h : ℕ) : oreCoefficientDepth K n 0 h = 1 :=
      (oreCoefficientDepth_def K n 0 h).trans (max_eq_left (ENat.toNat_le_of_le_natCast (by simp)))
    have hsum : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n 0 h = n - 1 := by
      rw [Finset.sum_congr rfl fun h _ ↦ hdepth h,
        Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]
    simp [hsum]
  · simp [hj]

open Classical in
/-- Restricting a `tsum` over `A` to the wild-exponent fiber `L.wildExponent = j`. -/
private theorem tsum_ite_wildExponent_eq (A : Set (IntermediateField K (SeparableClosure K)))
    (j : ℕ) (g : IntermediateField K (SeparableClosure K) → ℝ≥0∞) :
    (∑' L : A, if L.1.wildExponent = j then g L.1 else 0) =
      ∑' E : {E ∈ A | E.wildExponent = j}, g E.1 := by
  let e : {L : A | L.1.wildExponent = j} ≃ ({E ∈ A | E.wildExponent = j} : Set _) :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun E ↦ ⟨⟨E.1, E.2.1⟩, E.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine Eq.trans ?_ ((_root_.tsum_subtype {L : A | L.1.wildExponent = j}
    (fun L : A ↦ g L.1)).symm.trans (e.tsum_eq fun E ↦ g E.1))
  refine tsum_congr fun L ↦ ?_
  by_cases h : L.1.wildExponent = j <;> simp [Set.indicator, h]

private theorem exists_addHaarMeasure_integerBox_eq_one (n : ℕ)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)] :
    ∃ μ : Measure (Fin n → K), μ.IsAddHaarMeasure ∧ μ (integerBox K (Fin n)) = 1 := by
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]
      exact ⟨0, by simp⟩⟩
  exact ⟨Measure.addHaarMeasure B, inferInstance, Measure.addHaarMeasure_self⟩

/-- Core integral identity on `eisensteinBox K n j`: the `encard` of the stratum
`{E ∈ σ_K(n) | E.wildExponent = j}` times `q ^ (-(n + j)) (1 - q⁻¹)` equals
`n * μ (eisensteinBox K n j)`. -/
private theorem encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      n * μ (eisensteinBox K n j) := by
  classical
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [totallyRamifiedOfDegree_zero]
  set w : ℝ≥0∞ := 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
  have := (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
  calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) * w
      = ∑' L : totallyRamifiedOfDegree K n, if L.1.wildExponent = j then w else 0 :=
          ((tsum_ite_wildExponent_eq (totallyRamifiedOfDegree K n) j fun _ ↦ w).trans
            (ENNReal.tsum_set_const _ w)).symm
    _ = ∑' L : totallyRamifiedOfDegree K n,
          ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ :=
          tsum_congr fun L ↦ (L.1.lintegral_rootCount_eisensteinBox L.2 μ hμ).symm
    _ = ∫⁻ a in eisensteinBox K n j,
          (∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞)) ∂μ :=
          (lintegral_tsum fun L ↦ aemeasurable_rootCount_restrict_eisensteinBox μ L.2).symm
    _ = ∫⁻ _ in eisensteinBox K n j, (n : ℝ≥0∞) ∂μ := by
          refine setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦ ?_
          obtain ⟨f, hf, he⟩ := mem_eisensteinSet_iff_exists_isEisensteinAt.mp
            (eisensteinBox_subset_eisensteinSet K n j ha)
          exact tsum_rootCount_eq_of_separable he hf
            (separable_monicOfCoeff_of_mem_eisensteinBox ha)
    _ = n * μ (eisensteinBox K n j) := by simp

/-- **Finiteness of each wild-exponent stratum**: for every `n` and `j`, the set of
`E ∈ σ_K(n)` with `E.wildExponent = j` is finite, including in equal characteristic `p` with
`p ∣ n`. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite := by
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  obtain ⟨μ, _, hμ⟩ := exists_addHaarMeasure_integerBox_eq_one (K := K) n
  have hid := encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox (j := j) μ hμ
  have hq1 : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hw0 : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) ≠ 0 :=
    mul_ne_zero (ENNReal.div_pos one_ne_zero
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne'
      (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hrhs_lt : (n : ℝ≥0∞) * μ (eisensteinBox K n j) < ∞ :=
    ENNReal.mul_lt_top (ENNReal.natCast_lt_top n)
      ((measure_mono (eisensteinBox_subset_eisensteinSet K n j)).trans_lt
        (measure_eisensteinSet_lt_top μ))
  have hencard_ne_top :
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) ≠ ∞ := fun htop ↦ by
    rw [htop, ENNReal.top_mul hw0] at hid
    exact hrhs_lt.ne hid.symm
  exact Set.encard_ne_top_iff.mp (by simpa [ENat.toENNReal_eq_top] using hencard_ne_top)

/-- **Krasner's count in measure form**: for Haar measure `μ` normalized on the integer box,
`#{E ∈ σ_K(n) | E.wildExponent = j} = n * q ^ (n + j) * μ (eisensteinBox K n j) / (1 - q⁻¹)`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_eq_mul_measure {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddHaarMeasure] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      n * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) /
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have hid := encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox (j := j) μ hμ
  rw [← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe] at hid
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hq1 : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hsub0 : 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hsubt : 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  refine (ENNReal.eq_div_iff hsub0 hsubt).mpr ?_
  have hmul := congrArg ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * ·) hid
  rw [← mul_assoc, mul_comm ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)), mul_assoc, ← mul_assoc _ (1 / _),
    one_div, ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul] at hmul
  rw [mul_comm, hmul]
  ring

/-- Auxiliary weighted equality after cancelling `1 - q⁻¹` on an Ore-admissible stratum. -/
private theorem ncard_wildExponent_eq_mul_one_div_pow {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) =
      (n : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
          (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  obtain ⟨μ, _, hμ⟩ := exists_addHaarMeasure_integerBox_eq_one (K := K) n
  set q := Nat.card 𝓀[K]
  have hq1 : (1 : ℝ≥0∞) < q := by exact_mod_cast Finite.one_lt_card
  have hsub0 : 1 - 1 / (q : ℝ≥0∞) ≠ 0 := (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hsubt : 1 - 1 / (q : ℝ≥0∞) ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hid := encard_wildExponent_eq_mul_eq_mul_measure_eisensteinBox (j := j) μ hμ
  rw [← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe, measure_eisensteinBox hadm μ hμ] at hid
  exact (ENNReal.mul_left_inj hsub0 hsubt).mp ((mul_assoc _ _ _).trans (hid.trans (by ring)))

/-- Exact `ℕ` clearing-denominators identity for `{E ∈ σ_K(n) | E.wildExponent = j}.ncard` when
`IsOreAdmissible K n j`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow {n j : ℕ}
    (hadm : IsOreAdmissible K n j) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
      Nat.card 𝓀[K] ^ (2 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) =
      n * Nat.card 𝓀[K] ^ (n + j) *
        (if j % n = 0 then Nat.card 𝓀[K] else Nat.card 𝓀[K] - 1) := by
  set q := Nat.card 𝓀[K]
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  set M := {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard
  have hq_gt : 1 < q := Finite.one_lt_card
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqt : (q : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top q
  have hmul := congrArg (· * ((q : ℝ≥0∞) ^ (n + j) * (q : ℝ≥0∞) ^ (2 + S)))
    (ncard_wildExponent_eq_mul_one_div_pow hadm)
  have hlhs :
      (M : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (n + j)) *
        ((q : ℝ≥0∞) ^ (n + j) * (q : ℝ≥0∞) ^ (2 + S)) =
        ((M * q ^ (2 + S) : ℕ) : ℝ≥0∞) := by
    rw [mul_assoc (M : ℝ≥0∞), ← mul_assoc (1 / _), one_div,
      ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul]
    push_cast; rfl
  have hq_ite :
      (q : ℝ≥0∞) * (if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) =
        ((if j % n = 0 then q else q - 1 : ℕ) : ℝ≥0∞) := by
    split_ifs
    · simp
    · rw [ENNReal.mul_sub fun _ _ ↦ hqt, mul_one, one_div, ENNReal.mul_inv_cancel hq0 hqt]
      have hq_eq : q = (q - 1) + 1 := by omega
      conv_lhs => rw [hq_eq, Nat.cast_add, Nat.cast_one]
      exact ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  have hpow : (q : ℝ≥0∞) ^ (2 + S) = (q : ℝ≥0∞) ^ (1 + S) * (q : ℝ≥0∞) := by
    rw [(by omega : 2 + S = (1 + S) + 1)]; exact pow_succ _ _
  have hrhs :
      (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + S)) *
        (if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) *
        ((q : ℝ≥0∞) ^ (n + j) * (q : ℝ≥0∞) ^ (2 + S)) =
        ((n * q ^ (n + j) * (if j % n = 0 then q else q - 1) : ℕ) : ℝ≥0∞) := by
    calc (n : ℝ≥0∞) * (1 / (q : ℝ≥0∞) ^ (1 + S)) *
          (if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)) *
          ((q : ℝ≥0∞) ^ (n + j) * (q : ℝ≥0∞) ^ (2 + S))
        = (n : ℝ≥0∞) * (q : ℝ≥0∞) ^ (n + j) *
            ((1 / (q : ℝ≥0∞) ^ (1 + S) * (q : ℝ≥0∞) ^ (1 + S)) *
              ((q : ℝ≥0∞) * (if j % n = 0 then 1 else 1 - 1 / (q : ℝ≥0∞)))) := by rw [hpow]; ring
      _ = ((n * q ^ (n + j) * (if j % n = 0 then q else q - 1) : ℕ) : ℝ≥0∞) := by
            rw [one_div, ENNReal.inv_mul_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt),
              one_mul, hq_ite]
            push_cast; rfl
  exact_mod_cast hlhs.symm.trans (hmul.trans hrhs)

/-- **Krasner's discriminant-refined count**: for all `n` and `j`, the number of totally ramified
degree-`n` subextensions of `SeparableClosure K` with wild exponent `j` equals
`krasnerCount K n j`. -/
theorem natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
      krasnerCount K n j := by
  by_cases hadm : IsOreAdmissible K n j
  · have hn := hadm.pos
    have hrat := congrArg (fun k : ℕ ↦ (k : ℚ))
      (ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul_pow hadm)
    simp only [Nat.cast_mul, Nat.cast_pow] at hrat
    rw [krasnerCount, ite_eq_left hadm]
    set q : ℚ := (Nat.card 𝓀[K] : ℚ) with hq_def
    set S : ℕ := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    have hq_gt : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    apply mul_right_cancel₀ (pow_ne_zero (2 + S) hq0)
    have hite_q :
        ((if j % n = 0 then Nat.card 𝓀[K] else Nat.card 𝓀[K] - 1 : ℕ) : ℚ) =
          q * (if j % n = 0 then 1 else 1 - q⁻¹) := by
      split_ifs
      · simp [hq_def]
      · rw [Nat.cast_sub (by omega : 1 ≤ Nat.card 𝓀[K]), Nat.cast_one, ← hq_def,
          mul_sub, mul_one, mul_inv_cancel₀ hq0]
    rw [hite_q] at hrat
    have hcancel : (q ^ S)⁻¹ * q ^ S = 1 := inv_mul_cancel₀ (pow_ne_zero S hq0)
    rw [hrat, (by omega : n + j = (n + j - 1) + 1), pow_succ, (by omega : 2 + S = S + 2),
      pow_add, div_eq_mul_inv]
    calc (n : ℚ) * (q ^ (n + j - 1) * q) * (q * (if j % n = 0 then 1 else 1 - q⁻¹))
        = (n : ℚ) * q ^ (n + j - 1) * ((q ^ S)⁻¹ * q ^ S) *
            (if j % n = 0 then 1 else 1 - q⁻¹) * q ^ 2 := by rw [hcancel]; ring
      _ = (n : ℚ) * (q ^ (n + j - 1) * (q ^ S)⁻¹) *
            (if j % n = 0 then 1 else 1 - q⁻¹) * (q ^ S * q ^ 2) := by ring
  · rw [krasnerCount_of_not_isOreAdmissible hadm]
    have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun hE hEj ↦ hadm (ore_realizability.mp ⟨E, hE, hEj⟩)
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-- **Bounded wild-exponent finiteness**: in any characteristic, only finitely many members of
`σ_K(n)` have wild exponent at most `D`. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ D}.Finite :=
  ((Finset.range (D + 1)).finite_toSet.biUnion fun j _ ↦
    finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset
    fun _ ⟨hE, hle⟩ ↦ Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hle)) ⟨hE, rfl⟩

/-- **Bounded discriminant finiteness**: in any characteristic, only finitely many members of
`σ_K(n)` have discriminant exponent at most `D`. -/
theorem finite_mem_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset fun _ ⟨hE, _⟩ ↦ by
    have := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
    exact ⟨hE, by omega⟩

/-- Fiberwise summation of `w (L.wildExponent)` over `L ∈ σ_K(n)` weighted by stratum counts. -/
private theorem tsum_ncard_wildExponent_mul (n : ℕ) (w : ℕ → ℝ≥0∞) :
    (∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) * w j) =
      ∑' L : totallyRamifiedOfDegree K n, w L.1.wildExponent := by
  let g : totallyRamifiedOfDegree K n → ℕ := fun L ↦ L.1.wildExponent
  rw [← tsum_fiberwise (fun L : totallyRamifiedOfDegree K n ↦ w (g L)) g]
  refine tsum_congr fun j ↦ ?_
  let e : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} : Set _) ≃ (g ⁻¹' {j}) :=
    { toFun := fun E ↦ ⟨⟨E.1, E.2.1⟩, E.2.2⟩
      invFun := fun L ↦ ⟨L.1.1, L.1.2, L.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hconst : ∀ L : g ⁻¹' {j}, w (g L.1) = w j := fun L ↦ congrArg w L.2
  rw [tsum_congr hconst, ← e.tsum_eq (fun _ ↦ w j), ENNReal.tsum_set_const,
    ← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe]

/-- **Consistency with Serre's first mass formula**: summing the stratum counts weighted by
`q ^ (-j)` recovers `n`. -/
theorem tsum_ncard_wildExponent_div_natCard_residueField_pow (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  rw [tsum_congr fun j ↦ div_eq_mul_one_div _ _,
    tsum_ncard_wildExponent_mul, tsum_one_div_natCard_residueField_pow_wildExponent]

/-- Real `HasSum` consistency of `krasnerCount` with Serre's first mass formula. -/
theorem hasSum_krasnerCount_div_natCard_residueField_pow (n : ℕ) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  let term : ℕ → ℝ≥0 := fun j ↦
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0) /
      (Nat.card 𝓀[K] : ℝ≥0) ^ j
  have hcoe (j : ℕ) :
      (term j : ℝ≥0∞) =
        ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ j := by
    rw [ENNReal.coe_div (pow_ne_zero _ (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))]
    push_cast; rfl
  have htsum : ∑' j : ℕ, (term j : ℝ≥0∞) = ((n : ℝ≥0) : ℝ≥0∞) := by
    rw [tsum_congr hcoe, tsum_ncard_wildExponent_div_natCard_residueField_pow,
      ENNReal.coe_natCast]
  have hnn : HasSum term (n : ℝ≥0) := by
    rwa [← ENNReal.hasSum_coe, CompleteLattice.summable.hasSum_iff]
  have hreal := NNReal.hasSum_coe.mpr hnn
  rw [NNReal.coe_natCast] at hreal
  refine hreal.congr_fun fun j ↦ ?_
  have hkr : (krasnerCount K n j : ℝ) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ) := by
    exact_mod_cast (natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).symm
  dsimp only [term]
  push_cast
  rw [hkr]

/-- For a set of representatives `R` of `σ_K(n)`, each wild-exponent stratum `{M ∈ R | c(M) = j}`
is finite. -/
theorem IsRepresentativeSet.finite_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R) (j : ℕ) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset
    fun _ ⟨hM, hj⟩ ↦ ⟨hR.subset hM, hj⟩

/-- **Isomorphism-class stratum mass**: for `0 < n` and any set of representatives `R` of the
`K`-isomorphism classes in `σ_K(n)`, the Serre mass `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M)` equals
`#{E ∈ σ_K(n) | c(E) = j} / n`. -/
theorem IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq {n : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R)
    (hn : 0 < n) (j : ℕ) :
    ∑' M : {M ∈ R | M.wildExponent = j}, (1 / (Nat.card (M.1 ≃ₐ[K] M.1) : ℝ≥0∞)) =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) / n := by
  classical
  let f : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.wildExponent = j then 1 else 0
  have hf := hR.tsum_eq_tsum_div_natCard_algEquiv_mul f fun e ↦ by
    simp only [f, IntermediateField.wildExponent_eq_of_algEquiv e]
  have hlhs : ∑' L : totallyRamifiedOfDegree K n, f L =
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) := by
    rw [tsum_ite_wildExponent_eq (totallyRamifiedOfDegree K n) j fun _ ↦ 1,
      ENNReal.tsum_set_one,
      ← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
      ENat.toENNReal_coe]
  let gR : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun M ↦ 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)
  have hrhs : ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * f M =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, gR M.1 := by
    rw [← tsum_ite_wildExponent_eq R j gR, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun M ↦ ?_
    by_cases h : M.1.wildExponent = j <;> simp [f, gR, h, div_eq_mul_inv]
  rw [hlhs, hrhs] at hf
  exact (ENNReal.eq_div_iff (by exact_mod_cast hn.ne') (ENNReal.natCast_ne_top n)).mpr hf.symm

/-- **Krasner's total count (cardinal form)**: in any characteristic, the extended cardinality of
`σ_K(n)` is the sum over all wild exponents `j` of the stratum counts. -/
theorem tsum_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (n : ℕ) :
    ∑' j : ℕ, ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) =
      (totallyRamifiedOfDegree K n).encard := by
  simpa using (tsum_ncard_wildExponent_mul (K := K) n fun _ ↦ 1).trans (ENNReal.tsum_set_one _)

/-- **Krasner's total count away from equal characteristic `p ∣ n`**: when `(n : K) ≠ 0`,
`(totallyRamifiedOfDegree K n).ncard` is the finite sum of the stratum counts for
`0 ≤ j ≤ n * v_K(n)`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1),
        {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard := by
  have hfin : (totallyRamifiedOfDegree K n).Finite :=
    (tsum_one_div_natCard_residueField_pow_wildExponent_ne_top_iff_finite hnK).mp <| by
      rw [tsum_one_div_natCard_residueField_pow_wildExponent]
      exact ENNReal.natCast_ne_top n
  have htot := tsum_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe,
    tsum_eq_sum (s := Finset.range (n * natCastValuation K n hnK + 1))] at htot
  · rw [← Nat.cast_sum] at htot
    exact_mod_cast htot.symm
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ := by
      ext E
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hE hEj
      have := IntermediateField.wildExponent_le_mul_natCastValuation hE hnK
      omega
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

/-- Away from `(n : K) = 0`, `((totallyRamifiedOfDegree K n).ncard : ℚ)` is the finite sum of
`krasnerCount K n j` for `0 ≤ j ≤ n * v_K(n)`. -/
theorem natCast_ncard_totallyRamifiedOfDegree_eq_sum_krasnerCount {n : ℕ} (hnK : (n : K) ≠ 0) :
    ((totallyRamifiedOfDegree K n).ncard : ℚ) =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  rw [ncard_totallyRamifiedOfDegree_eq_sum hnK, Nat.cast_sum]
  exact Finset.sum_congr rfl fun j _ ↦
    natCast_ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j

end TauCeti

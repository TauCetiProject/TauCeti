/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Main
public import TauCeti.NumberTheory.LocalField.Padic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Countable
import TauCeti.NumberTheory.LocalField.MassFormula.Integral

/-!
# Krasner's count by degree and discriminant

Let `K` be a nonarchimedean local field with residue cardinality `q = Nat.card 𝓀[K]`, and let
`σ_K(n) = totallyRamifiedOfDegree K n` be the set of totally ramified degree-`n` subextensions of
`SeparableClosure K`. For each `j : ℕ`, Krasner's formula counts the stratum
`{L ∈ σ_K(n) | L.wildExponent = j}` of subextensions with discriminant exponent `n - 1 + j`.

Integrating the root-count identity `∑_{L : c(L) = j} L.rootCount a = n` over the discriminant box
`eisensteinBox K n j` against a normalized left-invariant measure `μ`, every member of the stratum
has constant root-count integral `q ^ (-(n + j)) * (1 - q⁻¹)` (by
`IntermediateField.lintegral_rootCount` and the vanishing of `L.rootCount` off
`eisensteinBox K n j`). Comparing with `n * μ (eisensteinBox K n j)` shows that every discriminant
stratum is finite—even in equal characteristic—and yields both exact natural-number counts and the
rational box formula `TauCeti.krasnerCount K n j`.

From the stratum count we deduce:

* **Bounded-discriminant finiteness**: for every local field `K` (including equal characteristic)
  and every `n, D : ℕ`, only finitely many `L ∈ σ_K(n)` have `L.wildExponent ≤ D` or
  `L.discriminantExponent ≤ D`.
* **Absolutely unramified closed form**: when `v_K(p) = 1` (in particular for `K = ℚ_[p]` and its
  unramified extensions), evaluating `∑_{h=1}^{n-1} ν_h` via the divisor-counting identity
  `Nat.Ioc_filter_dvd_card_eq_div` yields Krasner's explicit exponents
  `∑_{i=1}^{a} ⌊n / p^i⌋` (when `b = 0`) and `∑_{i=1}^{a} ⌊n / p^i⌋ + ⌊b / p^{a+1}⌋` (when `b > 0`).
* **Consistency with Serre's first mass formula**: summing `#{c = j} / q ^ j` over `j : ℕ`
  recovers `n` (both in `ℝ≥0∞` and as a convergent real series).
* **Isomorphism-class form**: for any set `R` of representatives of the `K`-isomorphism classes in
  `σ_K(n)`, `{M ∈ R | M.wildExponent = j}` is finite and
  `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #{c = j} / n`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's rational count formula for
  `{L ∈ σ_K(n) | L.wildExponent = j}`.

## Main results

* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_eq`: every discriminant stratum of `σ_K(n)`
  is finite, in both mixed and equal characteristic.
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_dvd` and
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_mod_pos`: exact natural-number counts
  for admissible strata.
* `TauCeti.krasner_refined_count`: finiteness and equality
  `(#{L ∈ σ_K(n) | L.wildExponent = j} : ℚ) = krasnerCount K n j`.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le` and
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-discriminant finiteness.
* `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_dvd`,
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_mod_pos`,
  and their `ℚ_[p]` specializations: Krasner's closed form for `v_K(p) = 1`.
* `TauCeti.tsum_ncard_wildExponent_div_pow_eq` and `TauCeti.hasSum_krasnerCount_div_pow`:
  consistency with Serre's first mass formula.
* `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: the
  isomorphism-class mass in each discriminant stratum.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les tendances
  géométriques en algèbre et théorie des nombres*, CNRS, Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a p-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section
noncomputable section

open ValuativeRel IsDiscreteValuationRing MeasureTheory
open scoped IntermediateField ENNReal NNReal

namespace TauCeti

/-! ### Krasner's rational count formula -/

section DiscreteValuationRing

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
open Classical in
/-- Krasner's refined count formula for the number of totally ramified degree-`n` extensions of
`K` with wild exponent `j`, written in terms of `oreCoefficientDepth`. It vanishes unless
`IsOreAdmissible K n j`. -/
def krasnerCount (n j : ℕ) : ℚ :=
  let q : ℚ := Nat.card 𝓀[K]
  if IsOreAdmissible K n j then
    n * q ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - q⁻¹)
  else 0

/-- Unfolding lemma for `krasnerCount`. -/
theorem krasnerCount_def (n j : ℕ) :
    krasnerCount K n j =
      letI := Classical.dec (IsOreAdmissible K n j)
      let q : ℚ := Nat.card 𝓀[K]
      if IsOreAdmissible K n j then
        n * q ^ (((n + j - 1 : ℕ) : ℤ) -
          ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
            (if j % n = 0 then 1 else 1 - q⁻¹)
      else 0 := by
  rw [krasnerCount]

/-- Outside Ore-admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  classical
  rw [krasnerCount_def, ite_eq_right (fun hadm ↦ absurd hadm h)]

/-- In degree `0`, `krasnerCount` is always `0`. -/
@[simp]
theorem krasnerCount_zero (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (not_isOreAdmissible_zero j)

/-- In degree `1`, `krasnerCount` is `1` at `j = 0` and `0` otherwise. -/
theorem krasnerCount_one (j : ℕ) : krasnerCount K 1 j = if j = 0 then 1 else 0 := by
  classical
  rw [krasnerCount_def]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hadm : IsOreAdmissible K 1 0 := isOreAdmissible_one_iff.2 rfl
    simp [hadm]
  · have hnot : ¬ IsOreAdmissible K 1 j := by rw [isOreAdmissible_one_iff]; exact hj.ne'
    simp [hnot, hj.ne']

/-- When `IsOreAdmissible K n j` and `j % n = 0`, `krasnerCount K n j` is a natural number. -/
theorem krasnerCount_of_dvd {n j : ℕ} (hadm : IsOreAdmissible K n j) (hb : j % n = 0) :
    krasnerCount K n j =
      ((n * (Nat.card 𝓀[K]) ^
        (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) : ℕ) : ℚ) := by
  classical
  have hle : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 1 := by
    simpa [hb] using sum_oreCoefficientDepth_le hadm
  rw [krasnerCount_def, ite_eq_left hadm, ite_eq_left hb, mul_one, ← Nat.cast_sub hle, zpow_natCast]
  push_cast
  rfl

/-- When `IsOreAdmissible K n j`, `0 < j % n`, and the residue field is finite, `krasnerCount K n j`
is the cast of `n * (q - 1) * q ^ (n + j - 2 - ∑ ν_h)`. -/
theorem krasnerCount_of_mod_pos [Finite 𝓀[K]] {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    krasnerCount K n j =
      ((n * (Nat.card 𝓀[K] - 1) * (Nat.card 𝓀[K]) ^
        (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) : ℕ) : ℚ) := by
  classical
  have hle : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 2 := by
    simpa [hb.ne'] using sum_oreCoefficientDepth_le hadm
  have hlt : j % n < n := Nat.mod_lt j hadm.pos
  have hjpos : 0 < j := Nat.lt_of_lt_of_le hb (Nat.mod_le j n)
  have hsub : n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h =
      (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) + 1 := by
    omega
  have hq0 : (Nat.card 𝓀[K] : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hq1 : 1 ≤ Nat.card 𝓀[K] := Nat.card_pos
  rw [krasnerCount_def, ite_eq_left hadm, ite_eq_right hb.ne',
    ← Nat.cast_sub (by omega : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤ n + j - 1),
    zpow_natCast, hsub, pow_succ]
  push_cast [Nat.cast_sub hq1]
  field_simp [hq0]

end DiscreteValuationRing

/-! ### Integration over discriminant boxes and Krasner's count -/

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `L ∈ σ_K(n)` with wild exponent `j`, the root count `L.rootCount` integrates over
`eisensteinBox K n j` to `q ^ (-(n + j)) * (1 - q⁻¹)`. -/
theorem _root_.IntermediateField.lintegral_rootCount_eisensteinBox {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    (hj : L.wildExponent = j) [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  have heq : ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ := by
    rw [← lintegral_indicator measurableSet_eisensteinBox,
      ← lintegral_indicator measurableSet_eisensteinSet]
    refine lintegral_congr fun a ↦ ?_
    by_cases ha : a ∈ eisensteinBox K n j
    · simp [ha, eisensteinBox_subset_eisensteinSet n j ha]
    · by_cases haE : a ∈ eisensteinSet K n
      · have h0 := rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL haE
          (hj.symm ▸ ha)
        simp [ha, haE, h0]
      · simp [ha, haE]
  rw [heq, L.lintegral_rootCount hL μ hμ]
  have hwc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL
  rw [show L.discriminantExponent + 1 = n + j by omega]

/-- Relating the stratum cardinality to the normalized volume of the discriminant box:
`#{L ∈ σ_K(n) | L.wildExponent = j} * (q ^ (-(n + j)) * (1 - q⁻¹)) = n * μ (eisensteinBox K n j)`.
-/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq_mul_weight {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      n * μ (eisensteinBox K n j) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [totallyRamifiedOfDegree_zero]
  set S : Set (IntermediateField K (SeparableClosure K)) :=
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}
  have hcount : S.Countable := (countable_totallyRamifiedOfDegree hn).mono fun _ h ↦ h.1
  have := hcount.to_subtype
  have hmeas (L : S) : AEMeasurable (fun a ↦ (L.1.rootCount a : ℝ≥0∞))
      (μ.restrict (eisensteinBox K n j)) :=
    (aemeasurable_rootCount_restrict_eisensteinSet μ L.2.1).mono_measure
      (Measure.restrict_mono (eisensteinBox_subset_eisensteinSet n j) le_rfl)
  have htsum : ∑' L : S, ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
      n * μ (eisensteinBox K n j) := by
    rw [← lintegral_tsum hmeas,
      setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦
        tsum_rootCount_wildExponent_eq_of_mem_eisensteinBox ha,
      setLIntegral_const]
  rw [← htsum, tsum_congr fun L : S ↦ L.1.lintegral_rootCount_eisensteinBox L.2.1 L.2.2 μ hμ,
    ENNReal.tsum_set_const]

/-- **Krasner's count in terms of box volume**: for a normalized left-invariant measure `μ`,
`#{L ∈ σ_K(n) | L.wildExponent = j} * (1 - q⁻¹) = n * q ^ (n + j) * μ (eisensteinBox K n j)`. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq_mul_one_sub {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
      n * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) := by
  have h := encard_totallyRamifiedOfDegree_wildExponent_eq_mul_weight (K := K) (n := n) (j := j)
    μ hμ
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hpow0 : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) ≠ 0 := pow_ne_zero _ hq0
  have hpowt : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) ≠ ∞ := ENNReal.pow_ne_top hqt
  have hmul := congrArg ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * ·) h
  rw [show (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (↑n * μ (eisensteinBox K n j)) =
      ↑n * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * μ (eisensteinBox K n j) by ring] at hmul
  rw [← hmul]
  calc ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
        (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
      = ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
          (((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j))) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
        rw [one_div ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)), ENNReal.mul_inv_cancel hpow0 hpowt, one_mul]
    _ = (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) *
          (({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)))) := by
        ring

/-- Helper: there exists a normalized left-invariant Borel measure on `Fin n → K`. -/
private theorem exists_normalized_measure (n : ℕ) :
    letI : MeasurableSpace (Fin n → K) := borel _
    ∃ (_ : BorelSpace (Fin n → K)) (μ : Measure (Fin n → K)),
      μ.IsAddLeftInvariant ∧ μ (integerBox K (Fin n)) = 1 := by
  let _ : MeasurableSpace (Fin n → K) := borel _
  have hB : BorelSpace (Fin n → K) := ⟨rfl⟩
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]
      exact ⟨0, by simp⟩⟩
  exact ⟨hB, Measure.addHaarMeasure B, inferInstance, Measure.addHaarMeasure_self⟩

/-- **Every discriminant stratum of `σ_K(n)` is finite**, in both mixed and equal
characteristic. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.Finite := by
  let _ : MeasurableSpace (Fin n → K) := borel _
  obtain ⟨hB, μ, hinv, hμ⟩ := exists_normalized_measure (K := K) n
  have h := encard_totallyRamifiedOfDegree_wildExponent_eq_mul_one_sub (K := K) (n := n) (j := j)
    μ hμ
  have hq : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hfac0 : (1 : ℝ≥0∞) - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hbox_lt : μ (eisensteinBox K n j) < ∞ :=
    (measure_mono ((eisensteinBox_subset_eisensteinSet n j).trans
      (eisensteinSet_subset_integerBox n))).trans_lt (by rw [hμ]; exact ENNReal.one_lt_top)
  have hprod_lt : ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) *
      (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) < ∞ := by
    rw [h]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top n)
      (ENNReal.pow_lt_top (ENNReal.natCast_lt_top _))) hbox_lt
  have hne : ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.encard : ℝ≥0∞) ≠ ∞ := by
    intro htop
    rw [htop, ENNReal.top_mul hfac0] at hprod_lt
    exact lt_irrefl ∞ hprod_lt
  rw [← Set.encard_lt_top_iff]
  exact ENat.toENNReal_lt.mp (lt_top_iff_ne_top.mpr hne)

/-- An inadmissible discriminant stratum has cardinality `0`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible {n j : ℕ}
    (h : ¬ IsOreAdmissible K n j) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard = 0 := by
  have hempty : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} = ∅ :=
    Set.eq_empty_of_forall_notMem fun E ⟨hE, hj⟩ ↦ h ((ore_realizability n j).1 ⟨E, hE, hj⟩)
  rw [hempty, Set.ncard_empty]

/-- Helper: cancel the common factor `1 - 1 / q` from the discriminant-box volume formula for an
admissible wild exponent. -/
private theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_ennreal {n j : ℕ}
    (hadm : IsOreAdmissible K n j) :
    ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) =
      n * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)) *
        (if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
  let _ : MeasurableSpace (Fin n → K) := borel _
  obtain ⟨hB, μ, hinv, hμ⟩ := exists_normalized_measure (K := K) n
  have h := encard_totallyRamifiedOfDegree_wildExponent_eq_mul_one_sub (K := K) (n := n) (j := j)
    μ hμ
  rw [measure_eisensteinBox hadm μ hμ] at h
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe] at h
  have hq : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
  have hfac0 : (1 : ℝ≥0∞) - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 :=
    (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hfact : (1 : ℝ≥0∞) - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · rw [ite_eq_left hb0, pow_one, ← mul_assoc] at h
    rw [ite_eq_left hb0, mul_one]
    exact (ENNReal.mul_left_inj hfac0 hfact).1 h
  · rw [ite_eq_right hbpos.ne', pow_two, ← mul_assoc, ← mul_assoc] at h
    rw [ite_eq_right hbpos.ne']
    exact (ENNReal.mul_left_inj hfac0 hfact).1 h

/-- Exact natural-number count of `{L ∈ σ_K(n) | L.wildExponent = j}` when `IsOreAdmissible K n j`
and `j % n = 0`: it equals `n * q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_dvd {n j : ℕ}
    (hadm : IsOreAdmissible K n j) (hb : j % n = 0) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard =
      n * (Nat.card 𝓀[K]) ^ (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  have hcancel := ncard_totallyRamifiedOfDegree_wildExponent_eq_ennreal hadm
  rw [ite_eq_left hb, mul_one] at hcancel
  set s := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hle : s ≤ n + j - 1 := by simpa [hb] using sum_oreCoefficientDepth_le hadm
  have hadd : (1 + s) + (n + j - 1 - s) = n + j := by
    have := hadm.pos
    omega
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hpow0 : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) ≠ 0 := pow_ne_zero _ hq0
  have hpowt : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) ≠ ∞ := ENNReal.pow_ne_top hqt
  rw [← hadd, pow_add] at hcancel
  have hrhs : (n : ℝ≥0∞) *
        ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 1 - s)) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s)) =
      ((n * (Nat.card 𝓀[K]) ^ (n + j - 1 - s) : ℕ) : ℝ≥0∞) := by
    calc _ = (n : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 1 - s) *
            ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s))) := by ring
      _ = _ := by rw [one_div, ENNReal.mul_inv_cancel hpow0 hpowt, mul_one]; push_cast; rfl
  rw [hrhs] at hcancel
  exact_mod_cast hcancel

/-- Exact natural-number count of `{L ∈ σ_K(n) | L.wildExponent = j}` when `IsOreAdmissible K n j`
and `0 < j % n`: it equals `n * (q - 1) * q ^ (n + j - 2 - ∑_{h=1}^{n-1} ν_h)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_mod_pos {n j : ℕ}
    (hadm : IsOreAdmissible K n j) (hb : 0 < j % n) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard =
      n * (Nat.card 𝓀[K] - 1) *
        (Nat.card 𝓀[K]) ^ (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  have hcancel := ncard_totallyRamifiedOfDegree_wildExponent_eq_ennreal hadm
  rw [ite_eq_right hb.ne'] at hcancel
  set s := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hle : s ≤ n + j - 2 := by simpa [hb.ne'] using sum_oreCoefficientDepth_le hadm
  have hlt : j % n < n := Nat.mod_lt j hadm.pos
  have hjpos : 0 < j := Nat.lt_of_lt_of_le hb (Nat.mod_le j n)
  have hadd : (1 + s) + ((n + j - 2 - s) + 1) = n + j := by omega
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hpow0 : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) ≠ 0 := pow_ne_zero _ hq0
  have hpowt : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) ≠ ∞ := ENNReal.pow_ne_top hqt
  have hqsub : (Nat.card 𝓀[K] : ℝ≥0∞) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
      ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) := by
    have hq1 : (Nat.card 𝓀[K] - 1) + 1 = Nat.card 𝓀[K] := Nat.sub_add_cancel Nat.card_pos
    calc (Nat.card 𝓀[K] : ℝ≥0∞) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
        = (Nat.card 𝓀[K] : ℝ≥0∞) - 1 := by
          rw [ENNReal.mul_sub (fun _ _ ↦ hqt), mul_one, one_div, ENNReal.mul_inv_cancel hq0 hqt]
      _ = ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) + 1 - 1 := by rw [← Nat.cast_one, ← Nat.cast_add, hq1]
      _ = ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) := ENNReal.add_sub_cancel_right ENNReal.one_ne_top
  rw [← hadd, pow_add, pow_succ] at hcancel
  have hrhs : (n : ℝ≥0∞) *
        ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) *
          ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - s) * (Nat.card 𝓀[K] : ℝ≥0∞))) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s)) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
      ((n * (Nat.card 𝓀[K] - 1) * (Nat.card 𝓀[K]) ^ (n + j - 2 - s) : ℕ) : ℝ≥0∞) := by
    calc _ = (n : ℝ≥0∞) *
            ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + s))) *
            ((Nat.card 𝓀[K] : ℝ≥0∞) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - s) := by ring
      _ = (n : ℝ≥0∞) * ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - s) := by
          rw [one_div, ENNReal.mul_inv_cancel hpow0 hpowt, mul_one, hqsub]
      _ = _ := by push_cast; rfl
  rw [hrhs] at hcancel
  exact_mod_cast hcancel

/-- **Krasner's discriminant-refined count**: for every `n, j : ℕ` (in both mixed and equal
characteristic), the members of `σ_K(n)` with wild exponent `j` form a finite set whose
cardinality equals `krasnerCount K n j`. -/
theorem krasner_refined_count (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite ∧
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
        krasnerCount K n j := by
  refine ⟨finite_totallyRamifiedOfDegree_wildExponent_eq n j, ?_⟩
  by_cases hadm : IsOreAdmissible K n j
  · rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
    · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_dvd hadm hb0,
        krasnerCount_of_dvd hadm hb0]
    · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_mod_pos hadm hbpos,
        krasnerCount_of_mod_pos hadm hbpos]
  · rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_not_isOreAdmissible hadm,
      krasnerCount_of_not_isOreAdmissible hadm, Nat.cast_zero]

/-! ### Bounded-discriminant finiteness -/

/-- **Bounded-wild-exponent finiteness**: for every local field `K` (including equal
characteristic) and every `n, D : ℕ`, only finitely many members of `σ_K(n)` have wild exponent
at most `D`. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n D : ℕ) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent ≤ D}.Finite := by
  have hsub : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent ≤ D} ⊆
      ⋃ j ∈ Finset.range (D + 1), {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} := by
    intro L ⟨hL, hle⟩
    exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hle)) ⟨hL, rfl⟩
  exact ((Finset.finite_toSet _).biUnion fun j _ ↦
    finite_totallyRamifiedOfDegree_wildExponent_eq n j).subset hsub

/-- **Bounded-discriminant finiteness**: for every local field `K` (including equal
characteristic) and every `n, D : ℕ`, only finitely many members of `σ_K(n)` have discriminant
exponent at most `D`. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {L ∈ totallyRamifiedOfDegree K n | L.discriminantExponent ≤ D}.Finite := by
  refine (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset ?_
  intro L ⟨hL, hle⟩
  refine ⟨hL, ?_⟩
  rw [IntermediateField.wildExponent_def]
  omega

/-! ### Closed form for absolutely unramified bases (`v_K(p) = 1`) and `ℚ_p` -/

/-- Elementary identity: `max 1 (M - v) + min (M - 1) v = M` whenever `1 ≤ M`. -/
private theorem max_one_sub_add_min_sub_one {M v : ℕ} (hM : 1 ≤ M) :
    max 1 (M - v) + min (M - 1) v = M := by
  omega

/-- Counting the `p`-adic valuation truncated at `a` as a sum of divisibility indicators. -/
private theorem min_padicValNat_eq_sum_ite {p : ℕ} (hp : p.Prime) {h : ℕ} (hh : h ≠ 0) (a : ℕ) :
    min a (padicValNat p h) = ∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hfilt : (Finset.Icc 1 a).filter (fun i ↦ p ^ i ∣ h) =
      Finset.Icc 1 (min a (padicValNat p h)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.padicValNat_def,
      Nat.pow_dvd_iff_le_multiplicity hp.ne_one hh]
    omega
  rw [hfilt, Nat.card_Icc]
  omega

/-- Summing `min a (padicValNat p h)` over `1 ≤ h ≤ n` equals `∑_{i=1}^{a} ⌊n / p^i⌋`. -/
private theorem sum_Ioc_min_padicValNat {p : ℕ} (hp : p.Prime) (n a : ℕ) :
    ∑ h ∈ Finset.Ioc 0 n, min a (padicValNat p h) = ∑ i ∈ Finset.Icc 1 a, n / p ^ i := by
  have hrew : ∀ h ∈ Finset.Ioc 0 n,
      min a (padicValNat p h) = ∑ i ∈ Finset.Icc 1 a, if p ^ i ∣ h then 1 else 0 :=
    fun h hh ↦ min_padicValNat_eq_sum_ite hp (Finset.mem_Ioc.1 hh).1.ne' a
  rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_boole, Nat.cast_id, Nat.Ioc_filter_dvd_card_eq_div]

/-- If `(ringChar 𝓀[K] : K) ≠ 0`, then every positive natural number is nonzero in `K`. -/
private theorem natCast_ne_zero_of_ringChar_residueField_ne_zero
    (hp : (ringChar 𝓀[K] : K) ≠ 0) {m : ℕ} (hm : m ≠ 0) : (m : K) ≠ 0 := fun h0 ↦ by
  have ⟨heq, _⟩ := (natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd
    (Nat.pos_of_ne_zero hm)).1 h0
  exact hp (heq ▸ ringChar.Nat.cast_ringChar (R := K))

/-- When `v_K(p) = 1` and `0 < n`, relating `∑_{h=1}^{n-1} ν_h` to the truncated `p`-adic
valuation sum and the number of multiples of `p ^ (j / n + 1)` strictly below `j % n`. -/
private theorem sum_oreCoefficientDepth_add_min_padicValNat
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hvp : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n : ℕ} (hn : 0 < n) (j : ℕ) :
    let p := ringChar 𝓀[K]
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) +
      (∑ h ∈ Finset.Ico 1 n, min (j / n) (padicValNat p h)) +
      ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card =
      (n - 1) * (j / n + 1) + (j % n - 1) := by
  intro p
  have hp' : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hv_eq (m : ℕ) (hm : m ≠ 0) :
      natCastValuation K m (natCast_ne_zero_of_ringChar_residueField_ne_zero hp hm) =
        padicValNat p m := by
    rw [natCastValuation_eq_padicValNat_mul K _ hp, hvp, mul_one]
  have hbn : j % n < n := Nat.mod_lt j hn
  have hterm (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      oreCoefficientDepth K n j h + min (j / n + if h < j % n then 1 else 0) (padicValNat p h) =
        j / n + 1 + if h < j % n then 1 else 0 := by
    have hh0 : h ≠ 0 := Nat.ne_of_gt (Finset.mem_Ico.1 hh).1
    have hhK := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hh0
    rw [oreCoefficientDepth_of_natCast_ne_zero hhK, hv_eq h hh0]
    have hM := max_one_sub_add_min_sub_one
      (M := j / n + 1 + if h < j % n then 1 else 0) (v := padicValNat p h)
      (by generalize j / n = q; split_ifs <;> omega)
    have hM1 : j / n + 1 + (if h < j % n then 1 else 0) - 1 =
        j / n + if h < j % n then 1 else 0 := by
      generalize j / n = q; split_ifs <;> omega
    rwa [hM1] at hM
  have hsum_all := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
    smul_eq_mul, Finset.sum_boole, Nat.cast_id] at hsum_all
  have hfilt_b : (Finset.Ico 1 n).filter (fun h ↦ h < j % n) = Finset.Ico 1 (j % n) := by
    ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rw [hfilt_b, Nat.card_Ico] at hsum_all
  have hsplit (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      min (j / n + if h < j % n then 1 else 0) (padicValNat p h) =
        min (j / n) (padicValNat p h) + if h < j % n ∧ p ^ (j / n + 1) ∣ h then 1 else 0 := by
    have hh0 : h ≠ 0 := Nat.ne_of_gt (Finset.mem_Ico.1 hh).1
    have hiff : p ^ (j / n + 1) ∣ h ↔ j / n + 1 ≤ padicValNat p h := by
      rw [Nat.padicValNat_def, Nat.pow_dvd_iff_le_multiplicity hp'.ne_one hh0]
    by_cases hlt : h < j % n <;> by_cases hd : p ^ (j / n + 1) ∣ h
    · have := hiff.1 hd; simp [hlt, hd]; omega
    · have : ¬ j / n + 1 ≤ padicValNat p h := fun hle ↦ hd (hiff.2 hle)
      simp [hlt, hd]; omega
    · simp [hlt, hd]
    · simp [hlt, hd]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← add_assoc] at hsum_all
  have hsum_b : ∑ h ∈ Finset.Ico 1 n, (if h < j % n ∧ p ^ (j / n + 1) ∣ h then 1 else 0) =
      ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card := by
    rw [Finset.sum_boole, Nat.cast_id]
    congr 1; ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; omega
  rwa [hsum_b] at hsum_all

/-- Evaluation of the Krasner exponent sum when `v_K(p) = 1`:
* for `j % n = 0`, `n + j - 1 - ∑_{h=1}^{n-1} ν_h = ∑_{i=1}^{j/n} ⌊n / p^i⌋`;
* for `0 < j % n`,
  `n + j - 2 - ∑_{h=1}^{n-1} ν_h = ∑_{i=1}^{j/n} ⌊n / p^i⌋ + ⌊(j % n) / p^{j/n + 1}⌋`. -/
private theorem krasner_exponent_of_natCastValuation_eq_one
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hvp : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    let p := ringChar 𝓀[K]
    let s := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    (j % n = 0 → n + j - 1 - s = ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) ∧
      (0 < j % n →
        n + j - 2 - s = (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  intro p s
  have hp' : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hn := hadm.pos
  have hv_eq (m : ℕ) (hm : m ≠ 0) :
      natCastValuation K m (natCast_ne_zero_of_ringChar_residueField_ne_zero hp hm) =
        padicValNat p m := by
    rw [natCastValuation_eq_padicValNat_mul K _ hp, hvp, mul_one]
  have hsum_all := sum_oreCoefficientDepth_add_min_padicValNat hp hvp hn j
  dsimp only at hsum_all
  have hvn : j / n ≤ padicValNat p n := by
    have hnK := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hn.ne'
    rcases (isOreAdmissible_iff.1 hadm).2 with ⟨_, ha⟩ | ⟨_, _, ha⟩
    · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, hv_eq n hn.ne',
        Nat.cast_inj] at ha
      exact ha.le
    · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, hv_eq n hn.ne',
        ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le] at ha
      omega
  have hIoc : Finset.Ioc 0 n = insert n (Finset.Ico 1 n) := by
    ext h; simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ico]; omega
  have hsum_n : ∑ h ∈ Finset.Ico 1 n, min (j / n) (padicValNat p h) + j / n =
      ∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i := by
    rw [← sum_Ioc_min_padicValNat hp' n (j / n), hIoc,
      Finset.sum_insert (by simp : n ∉ Finset.Ico 1 n), min_eq_left hvn, add_comm]
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hprod : (n - 1) * (j / n + 1) + j / n = n * (j / n) + (n - 1) := by
    have h1 : (n - 1) * (j / n + 1) = (n - 1) * (j / n) + (n - 1) := by ring
    have h2 : n * (j / n) = (n - 1) * (j / n) + j / n := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
    omega
  have hsum' : s + (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) +
      ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card =
      n * (j / n) + (n - 1) + (j % n - 1) := by
    calc _ = (s + ∑ h ∈ Finset.Ico 1 n, min (j / n) (padicValNat p h) +
            ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card) + j / n := by
          rw [← hsum_n]; ring
      _ = ((n - 1) * (j / n + 1) + (j % n - 1)) + j / n := by rw [hsum_all]
      _ = ((n - 1) * (j / n + 1) + j / n) + (j % n - 1) := by ring
      _ = n * (j / n) + (n - 1) + (j % n - 1) := by rw [hprod]
  refine ⟨fun hb0 ↦ ?_, fun hbpos ↦ ?_⟩
  · have hcard0 : ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card = 0 := by
      simp [hb0]
    have hrhs0 : n * (j / n) + (n - 1) + (j % n - 1) = n + j - 1 := by omega
    rw [hcard0, add_zero, hrhs0] at hsum'
    omega
  · have hndvd : ¬ p ^ (j / n + 1) ∣ j % n := by
      have hbK := natCast_ne_zero_of_ringChar_residueField_ne_zero hp hbpos.ne'
      rcases (isOreAdmissible_iff.1 hadm).2 with ⟨hb0, _⟩ | ⟨_, hvb, _⟩
      · exact absurd hb0 hbpos.ne'
      · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K (j % n) hbK, hv_eq (j % n) hbpos.ne',
          Nat.cast_le] at hvb
        rw [Nat.pow_dvd_iff_le_multiplicity hp'.ne_one hbpos.ne', ← Nat.padicValNat_def]
        omega
    have hcard_b : ((Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ (j / n + 1) ∣ h)).card =
        (j % n) / p ^ (j / n + 1) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div (j % n) (p ^ (j / n + 1))]
      congr 1; ext h; simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
      exact ⟨fun ⟨⟨h1, h2⟩, hd⟩ ↦ ⟨⟨h1, h2.le⟩, hd⟩,
        fun ⟨⟨h1, h2⟩, hd⟩ ↦ ⟨⟨h1, lt_of_le_of_ne h2 fun heq ↦ hndvd (heq ▸ hd)⟩, hd⟩⟩
    have hrhs1 : n * (j / n) + (n - 1) + (j % n - 1) = n + j - 2 := by omega
    rw [hcard_b, hrhs1] at hsum'
    omega

/-- **Krasner's closed form when `v_K(p) = 1`, divisible case (`n ∣ j`)**: for an admissible wild
exponent `j = a * n` (so `a = v_p(n)`),
`#{L ∈ σ_K(n) | L.wildExponent = j} = n * q ^ (∑_{i=1}^{a} ⌊n / p^i⌋)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_dvd
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hvp : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hb : j % n = 0) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard =
      n * (Nat.card 𝓀[K]) ^ (∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i) := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_dvd hadm hb,
    (krasner_exponent_of_natCastValuation_eq_one hp hvp hadm).1 hb]

/-- **Krasner's closed form when `v_K(p) = 1`, non-divisible case (`0 < j % n`)**: for an
admissible wild exponent `j = a * n + b` with `0 < b < n`,
`#{L ∈ σ_K(n) | L.wildExponent = j} = n * (q - 1) * q ^ (∑_{i=1}^{a} ⌊n / p^i⌋ + ⌊b / p^{a+1}⌋)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_mod_pos
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hvp : natCastValuation K (ringChar 𝓀[K]) hp = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hb : 0 < j % n) :
    {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard =
      n * (Nat.card 𝓀[K] - 1) * (Nat.card 𝓀[K]) ^
        ((∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i) +
          (j % n) / (ringChar 𝓀[K]) ^ (j / n + 1)) := by
  rw [ncard_totallyRamifiedOfDegree_wildExponent_eq_of_mod_pos hadm hb,
    (krasner_exponent_of_natCastValuation_eq_one hp hvp hadm).2 hb]

/-- The residue characteristic of `ℚ_[p]` is `p`. -/
private theorem ringChar_residueField_padic (p : ℕ) [Fact p.Prime] :
    ringChar 𝓀[ℚ_[p]] = p := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  exact (natCastValuation_ne_zero_iff_ringChar_eq ℚ_[p] Fact.out hp).1
    (by rw [Padic.natCastValuation_self]; exact one_ne_zero)

/-- Ore's admissibility condition over `ℚ_[p]`: `0 < n` and either `j % n = 0 ∧ j / n = v_p(n)`
or `0 < j % n ∧ v_p(j % n) ≤ j / n ∧ j / n + 1 ≤ v_p(n)`. -/
theorem isOreAdmissible_padic_iff (p : ℕ) [Fact p.Prime] (n j : ℕ) :
    IsOreAdmissible ℚ_[p] n j ↔
      0 < n ∧
        ((j % n = 0 ∧ j / n = padicValNat p n) ∨
          (0 < j % n ∧ padicValNat p (j % n) ≤ j / n ∧ j / n + 1 ≤ padicValNat p n)) := by
  rw [isOreAdmissible_iff]
  refine and_congr_right fun hn ↦ ?_
  have hnK : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] n hnK,
    Padic.natCastValuation_eq_padicValNat]
  refine or_congr (and_congr_right fun _ ↦ Nat.cast_inj) (and_congr_right fun hbpos ↦ ?_)
  have hbK : ((j % n : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hbpos.ne'
  rw [TauCeti.IsDiscreteValuationRing.addVal_natCast ℚ_[p] (j % n) hbK,
    Padic.natCastValuation_eq_padicValNat, Nat.cast_le, ← Nat.cast_one, ← Nat.cast_add,
    Nat.cast_le]

/-- **Krasner's closed form over `ℚ_[p]`, divisible case (`n ∣ j`)**:
`#{L ∈ σ_{ℚ_p}(n) | L.wildExponent = j} = n * p ^ (∑_{i=1}^{j/n} ⌊n / p^i⌋)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_dvd (p : ℕ) [Fact p.Prime]
    {n j : ℕ} (hadm : IsOreAdmissible ℚ_[p] n j) (hb : j % n = 0) :
    {L ∈ totallyRamifiedOfDegree ℚ_[p] n | L.wildExponent = j}.ncard =
      n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) := by
  have hchar := ringChar_residueField_padic p
  have hp : (ringChar 𝓀[ℚ_[p]] : ℚ_[p]) ≠ 0 := by
    rw [hchar]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hvp : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]]) hp = 1 := by
    simpa [hchar] using Padic.natCastValuation_self p
  simpa [hchar, Padic.natCard_residueField] using
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_dvd hp hvp hadm hb

/-- **Krasner's closed form over `ℚ_[p]`, non-divisible case (`0 < j % n`)**:
`#{L ∈ σ_{ℚ_p}(n) | L.wildExponent = j}` equals
`n * (p - 1) * p ^ (∑_{i=1}^{j/n} ⌊n / p^i⌋ + ⌊(j % n) / p^{j/n + 1}⌋)`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq_padic_of_mod_pos (p : ℕ) [Fact p.Prime]
    {n j : ℕ} (hadm : IsOreAdmissible ℚ_[p] n j) (hb : 0 < j % n) :
    {L ∈ totallyRamifiedOfDegree ℚ_[p] n | L.wildExponent = j}.ncard =
      n * (p - 1) *
        p ^ ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  have hchar := ringChar_residueField_padic p
  have hp : (ringChar 𝓀[ℚ_[p]] : ℚ_[p]) ≠ 0 := by
    rw [hchar]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hvp : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]]) hp = 1 := by
    simpa [hchar] using Padic.natCastValuation_self p
  simpa [hchar, Padic.natCard_residueField] using
    ncard_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_eq_one_of_mod_pos
      hp hvp hadm hb

/-! ### Consistency with Serre's first mass formula -/

/-- **Consistency with Serre's Theorem 1 (in `ℝ≥0∞`)**: regrouping Serre's first mass formula by
wild exponent yields `∑_{j : ℕ} #{L ∈ σ_K(n) | L.wildExponent = j} / q ^ j = n`. -/
theorem tsum_ncard_wildExponent_div_pow_eq (n : ℕ) :
    ∑' j : ℕ, ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  have hserre := tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)
  let e : totallyRamifiedOfDegree K n ≃
      Σ j : ℕ, {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} :=
    { toFun L := ⟨L.1.wildExponent, L.1, L.2, rfl⟩
      invFun x := ⟨x.2.1, x.2.2.1⟩
      left_inv _ := rfl
      right_inv := fun ⟨j, L, hL, hj⟩ ↦ by subst hj; rfl }
  have hsigma : ∑' L : totallyRamifiedOfDegree K n,
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ L.1.wildExponent =
      ∑' x : Σ j : ℕ, {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ x.1 :=
    e.tsum_eq fun x ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ x.1
  rw [← hserre, hsigma, tsum_sigma']
  refine tsum_congr fun j ↦ ?_
  dsimp only
  have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  rw [ENNReal.tsum_set_const, ← hfin.cast_ncard_eq, ENat.toENNReal_coe, mul_one_div]

/-- **Consistency with Serre's Theorem 1 (as a real series)**: the real series
`∑_{j : ℕ} krasnerCount K n j / q ^ j` converges to `n`, including in equal characteristic. -/
theorem hasSum_krasnerCount_div_pow (n : ℕ) :
    HasSum (fun j : ℕ ↦ (krasnerCount K n j : ℝ) / (Nat.card 𝓀[K] : ℝ) ^ j) n := by
  have hcoe (j : ℕ) :
      ((({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0) /
          (Nat.card 𝓀[K] : ℝ≥0) ^ j : ℝ≥0) : ℝ≥0∞) =
        ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ j := by
    rw [ENNReal.coe_div (pow_ne_zero _ (Nat.cast_ne_zero.2 Nat.card_pos.ne'))]
    push_cast
    rfl
  have hsum : HasSum (fun j : ℕ ↦
      ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ) /
        (Nat.card 𝓀[K] : ℝ) ^ j) n := by
    have h := tsum_ncard_wildExponent_div_pow_eq (K := K) n
    have hnn : HasSum (fun j : ℕ ↦
        ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0) /
          (Nat.card 𝓀[K] : ℝ≥0) ^ j) (n : ℝ≥0) := by
      rw [← ENNReal.hasSum_coe, CompleteLattice.summable.hasSum_iff, ENNReal.coe_natCast]
      exact (tsum_congr hcoe).trans h
    simpa only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast] using NNReal.hasSum_coe.2 hnn
  refine hsum.congr_fun fun j ↦ ?_
  rw [← (krasner_refined_count (K := K) n j).2, Rat.cast_natCast]

/-! ### Isomorphism-class form of Krasner's count -/

namespace IsRepresentativeSet

variable {n : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

/-- For any set of representatives `R` of `σ_K(n)`, the representatives of wild exponent `j` form
a finite set. -/
theorem finite_wildExponent_eq (hR : IsRepresentativeSet n R) (j : ℕ) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset
    fun _ ⟨hM, hj⟩ ↦ ⟨hR.subset hM, hj⟩

/-- **Isomorphism-class form in `ℝ≥0∞`**:
`n * ∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = #{L ∈ σ_K(n) | c(L) = j}`. -/
theorem mul_tsum_one_div_natCard_algEquiv_wildExponent_eq (hR : IsRepresentativeSet n R) (j : ℕ) :
    (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) =
      ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) := by
  classical
  have h := hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ if L.wildExponent = j then (1 : ℝ≥0∞) else 0)
    fun e ↦ by rw [IntermediateField.wildExponent_eq_of_algEquiv e]
  -- Evaluate the LHS as the cardinality of the stratum.
  have hlhs : ∑' L : totallyRamifiedOfDegree K n,
      (if L.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
      ({L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard : ℝ≥0∞) := by
    let S : Set (totallyRamifiedOfDegree K n) := {L | L.1.wildExponent = j}
    have hsupp : Function.support
        (fun L : totallyRamifiedOfDegree K n ↦ if L.1.wildExponent = j then (1 : ℝ≥0∞) else 0) ⊆
        S := fun L hL ↦ by
      by_contra hne
      have hne' : L.1.wildExponent ≠ j := hne
      exact hL (by simp [hne'])
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    let e : {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j} ≃ S :=
      { toFun L := ⟨⟨L.1, L.2.1⟩, L.2.2⟩
        invFun L := ⟨L.1.1, L.1.2, L.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← e.tsum_eq fun L : S ↦ if L.1.1.wildExponent = j then (1 : ℝ≥0∞) else 0]
    have hfin := finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
    rw [tsum_congr fun L ↦ ite_eq_left L.2.2, ENNReal.tsum_set_one, ← hfin.cast_ncard_eq,
      ENat.toENNReal_coe]
  -- Evaluate the RHS as `n` times the sum of `1 / #Aut_K(M)` over the stratum of `R`.
  have hrhs : ∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
        (if M.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
      (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, 1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) := by
    let T : Set R := {M | M.1.wildExponent = j}
    have hsupp : Function.support (fun M : R ↦ (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
        if M.1.wildExponent = j then (1 : ℝ≥0∞) else 0) ⊆ T := fun M hM ↦ by
      by_contra hne
      have hne' : M.1.wildExponent ≠ j := hne
      exact hM (by simp [hne'])
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    let e : {M ∈ R | M.wildExponent = j} ≃ T :=
      { toFun M := ⟨⟨M.1, M.2.1⟩, M.2.2⟩
        invFun M := ⟨M.1.1, M.1.2, M.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← e.tsum_eq, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun M ↦ ?_
    simp only [e, Equiv.coe_fn_mk, M.2.2, ↓reduceIte, mul_one, mul_one_div]
  rw [hlhs, hrhs] at h
  exact h.symm

/-- **Isomorphism-class form in `ℚ`**: for `0 < n` and any set of representatives `R` of `σ_K(n)`,
`∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`. -/
theorem tsum_one_div_natCard_algEquiv_wildExponent_eq (hR : IsRepresentativeSet n R)
    (hn : 0 < n) (j : ℕ) :
    ∑' M : {M ∈ R | M.wildExponent = j}, (1 : ℚ) / Nat.card (M ≃ₐ[K] M) =
      krasnerCount K n j / n := by
  have hfin := hR.finite_wildExponent_eq j
  have : Fintype {M ∈ R | M.wildExponent = j} := hfin.fintype
  have he := hR.mul_tsum_one_div_natCard_algEquiv_wildExponent_eq j
  rw [tsum_fintype] at he ⊢
  rw [← (krasner_refined_count (K := K) n j).2, eq_div_iff (Nat.cast_ne_zero.2 hn.ne'), mul_comm]
  -- Convert the finite sum identity in `ℝ≥0∞` to `ℚ` by clearing denominators.
  have haut (M : {M ∈ R | M.wildExponent = j}) : Nat.card (M ≃ₐ[K] M) ≠ 0 := by
    have := (mem_totallyRamifiedOfDegree_iff.1 (hR.subset M.2.1)).2.finite
    exact Nat.card_ne_zero.2 ⟨⟨.refl⟩, inferInstance⟩
  set D : ℕ := ∏ M : {M ∈ R | M.wildExponent = j}, Nat.card (M ≃ₐ[K] M)
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun M _ ↦ haut M
  have hterm_nat (M : {M ∈ R | M.wildExponent = j}) :
      (D : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞)) =
        ((D / Nat.card (M ≃ₐ[K] M) : ℕ) : ℝ≥0∞) := by
    have hdvd : Nat.card (M ≃ₐ[K] M) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ M)
    calc (D : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞))
        = ((D / Nat.card (M ≃ₐ[K] M) : ℕ) : ℝ≥0∞) *
            ((Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) * (1 / (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞))) := by
          rw [← mul_assoc, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
      _ = ((D / Nat.card (M ≃ₐ[K] M) : ℕ) : ℝ≥0∞) := by
          rw [one_div, ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (haut M))
            (ENNReal.natCast_ne_top _), mul_one]
  have hD_mul := congrArg ((D : ℝ≥0∞) * ·) he
  rw [mul_left_comm, Finset.mul_sum, Finset.sum_congr rfl fun M _ ↦ hterm_nat M] at hD_mul
  have hnat : n * ∑ M : {M ∈ R | M.wildExponent = j}, D / Nat.card (M ≃ₐ[K] M) =
      D * {L ∈ totallyRamifiedOfDegree K n | L.wildExponent = j}.ncard := by
    exact_mod_cast hD_mul
  have hD_rat : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hD
  apply mul_left_cancel₀ hD_rat
  have hq : (D : ℚ) * ((n : ℚ) * ∑ M : {M ∈ R | M.wildExponent = j},
      (1 : ℚ) / Nat.card (M ≃ₐ[K] M)) =
      (n : ℚ) * ∑ M : {M ∈ R | M.wildExponent = j}, ((D / Nat.card (M ≃ₐ[K] M) : ℕ) : ℚ) := by
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun M _ ↦ ?_
    have hdvd : Nat.card (M ≃ₐ[K] M) ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ M)
    rw [mul_one_div, Nat.cast_div hdvd (Nat.cast_ne_zero.2 (haut M))]
  rw [hq]
  exact_mod_cast hnat

end IsRepresentativeSet

end LocalField

end TauCeti

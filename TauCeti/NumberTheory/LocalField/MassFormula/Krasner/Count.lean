/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Representative
public import TauCeti.NumberTheory.LocalField.Padic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex
import TauCeti.NumberTheory.LocalField.MassFormula.Countable
import TauCeti.NumberTheory.LocalField.MassFormula.Main
import TauCeti.NumberTheory.LocalField.MassFormula.RootCount
import TauCeti.NumberTheory.Padics.PadicValNat

/-!
# Krasner's discriminant-refined count of totally ramified extensions

Let `K` be a nonarchimedean local field whose residue field `𝓀[K]` has `q` elements, and let
`σ_K(n) = totallyRamifiedOfDegree K n` be the set of totally ramified subextensions of degree `n`
of a fixed separable closure of `K`. For each wild exponent `j`, the discriminant box
`eisensteinBox K n j` isolates those Eisenstein polynomials of degree `n` whose roots generate
extensions in `σ_K(n)` of wild exponent `j` (equivalently, discriminant exponent `n - 1 + j`).

Integrating the root-count identity `∑_{L ∈ σ_K(n)} L.rootCount a = n` over `eisensteinBox K n j`
against additive Haar measure normalized on `integerBox K (Fin n)` yields
`#{E ∈ σ_K(n) | c(E) = j} · q ^ (-(n + j)) (1 - q⁻¹) = n · μ (eisensteinBox K n j)`.
Substituting `TauCeti.measure_eisensteinBox` proves both finiteness of the fiber (including in
equal characteristic `p` when `p ∣ n`, where `σ_K(n)` itself is infinite) and Krasner's closed
formula `TauCeti.krasnerCount K n j`: for Ore-admissible `(n, j)`,
`#{E ∈ σ_K(n) | c(E) = j} = n · q ^ ((n + j - 1) - ∑_{h=1}^{n-1} ν_h) · (1 or 1 - q⁻¹)`,
where `ν_h = oreCoefficientDepth K n j h`, and `0` otherwise.

From Krasner's refined count we deduce:
* finiteness of the set of totally ramified degree-`n` extensions of bounded wild or discriminant
  exponent, in any characteristic;
* consistency with Serre's first mass formula via fiberwise summation over `j`;
* the isomorphism-class mass formula `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`
  for any representative set `R`;
* Pauli and Roblot's closed form when `K` is absolutely unramified (`v_K(p) = 1`), and its
  specialization to `ℚ_[p]`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's rational formula for the number of totally ramified
  extensions of degree `n` and wild exponent `j`.

## Main results

* `TauCeti.encard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul`: the root-count integral
  identity relating the fiber cardinality to `μ (eisensteinBox K n j)`.
* `TauCeti.krasner_refined_count`: finiteness and exact cardinality of
  `{E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}`.
* `TauCeti.finite_mem_totallyRamifiedOfDegree_wildExponent_le` and
  `TauCeti.finite_mem_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-discriminant
  finiteness in all characteristics.
* `TauCeti.tsum_ncard_wildExponent_eq_div_pow`: fiberwise recovery of Serre's mass formula.
* `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: the mass of
  isomorphism classes of prescribed wild exponent.
* `TauCeti.krasnerCount_eq_of_natCastValuation_ringChar_eq_one`,
  `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_ringChar_eq_one`,
  `TauCeti.krasnerCount_padic`, and
  `TauCeti.ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_padic`: Pauli and Roblot's closed
  formula when `v_K(p) = 1` and over `ℚ_[p]`.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `p`-adique*, Colloq. Internat.
  CNRS **143** (1966), 143–169.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659.
-/

public section
noncomputable section

open MeasureTheory ValuativeRel IsDiscreteValuationRing
open scoped ENNReal

namespace TauCeti

section DiscreteValuation

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **Krasner's discriminant-refined count**: for an Ore-admissible pair `(n, j)` over `K` with
residue cardinality `q = Nat.card 𝓀[K]`, the rational expression
`n * q ^ ((n + j - 1) - ∑_{h=1}^{n-1} oreCoefficientDepth K n j h) * (1 or 1 - q⁻¹)`, and `0`
otherwise. Over a local field `K` this equals the cardinality of the wild-exponent-`j` fiber of
`totallyRamifiedOfDegree K n` (`TauCeti.krasner_refined_count`). -/
def krasnerCount (n j : ℕ) : ℚ := by
  classical
  let q : ℚ := Nat.card 𝓀[K]
  exact if IsOreAdmissible K n j then
    n * q ^ (((n + j - 1 : ℕ) : ℤ) -
      ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ)) *
        (if j % n = 0 then 1 else 1 - q⁻¹)
  else 0

/-- On an Ore-admissible pair `(n, j)`, `krasnerCount` unfolds to Krasner's power formula. -/
theorem krasnerCount_of_isOreAdmissible {n j : ℕ} (h : IsOreAdmissible K n j) :
    krasnerCount K n j =
      let q : ℚ := Nat.card 𝓀[K]
      n * q ^ (((n + j - 1 : ℕ) : ℤ) -
        ((∑ m ∈ Finset.Ico 1 n, oreCoefficientDepth K n j m : ℕ) : ℤ)) *
          (if j % n = 0 then 1 else 1 - q⁻¹) := by
  simp [krasnerCount, h]

/-- Outside Ore's admissible wild exponents, `krasnerCount` vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by simp [krasnerCount, h]

/-- In degree zero, `krasnerCount` vanishes for every `j`. -/
@[simp]
theorem krasnerCount_zero (j : ℕ) : krasnerCount K 0 j = 0 := by simp [krasnerCount]

/-- In degree one, `krasnerCount` is `1` at `j = 0` and `0` otherwise. -/
@[simp]
theorem krasnerCount_one (j : ℕ) : krasnerCount K 1 j = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0 <;> simp [krasnerCount, hj]

end DiscreteValuation

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On `eisensteinBox K n j`, the root-count integrals over `σ_K(n)` sum to `n` times the measure
of the box. -/
private theorem tsum_lintegral_rootCount_eisensteinBox {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [OpensMeasurableSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) :
    ∑' L : totallyRamifiedOfDegree K n,
      ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
        n * μ (eisensteinBox K n j) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [totallyRamifiedOfDegree_zero]
  have := (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
  have hmeas (L : totallyRamifiedOfDegree K n) :
      AEMeasurable (fun a ↦ (L.1.rootCount a : ℝ≥0∞)) (μ.restrict (eisensteinBox K n j)) :=
    (aemeasurable_rootCount_restrict_eisensteinSet μ L.2).mono_set
      eisensteinBox_subset_eisensteinSet
  have hsum : ∫⁻ a in eisensteinBox K n j,
      (∑' L : totallyRamifiedOfDegree K n, (L.1.rootCount a : ℝ≥0∞)) ∂μ =
        ∫⁻ _ in eisensteinBox K n j, (n : ℝ≥0∞) ∂μ :=
    setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦ by
      obtain ⟨f, hf, he⟩ :=
        mem_eisensteinSet_iff_exists_isEisensteinAt.mp (eisensteinBox_subset_eisensteinSet ha)
      exact tsum_rootCount_eq_of_separable he hf (separable_monicOfCoeff_of_mem_eisensteinBox ha)
  rw [← lintegral_tsum hmeas, hsum, setLIntegral_const]

/-- Summing a constant supported on a single wild-exponent fiber of `σ_K(n)` gives `encard` times
that constant. -/
private theorem tsum_ite_wildExponent_eq {n j : ℕ} (c : ℝ≥0∞) :
    (∑' L : totallyRamifiedOfDegree K n, if L.1.wildExponent = j then c else 0) =
      {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard * c := by
  let S := {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  let g : S → totallyRamifiedOfDegree K n := fun E ↦ ⟨E.1, E.2.1⟩
  have hg : Function.Injective g := by rintro ⟨_, _⟩ ⟨_, _⟩ h; cases h; rfl
  have hsupp : Function.support (fun L : totallyRamifiedOfDegree K n ↦
      if L.1.wildExponent = j then c else 0) ⊆ Set.range g := by
    intro L hL
    rw [Function.mem_support] at hL
    by_cases hw : L.1.wildExponent = j
    · exact ⟨⟨L.1, L.2, hw⟩, rfl⟩
    · exact absurd (ite_eq_right hw) hL
  rw [← hg.tsum_eq hsupp]
  have hc : (∑' E : S, if (g E).1.wildExponent = j then c else 0) = ∑' _ : S, c :=
    tsum_congr fun E ↦ ite_eq_left E.2.2
  rw [hc, ENNReal.tsum_set_const]

/-- **Box-volume form of Krasner's count**: for any left-invariant measure `μ` on `Fin n → K`
normalized on `integerBox K (Fin n)`, the extended cardinality of the wild-exponent-`j` fiber of
`σ_K(n)` times `q ^ (-(n + j)) (1 - q⁻¹)` equals `n · μ (eisensteinBox K n j)`. -/
theorem encard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul {n j : ℕ}
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard *
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
        n * μ (eisensteinBox K n j) := by
  rw [← tsum_lintegral_rootCount_eisensteinBox μ, ← tsum_ite_wildExponent_eq]
  exact tsum_congr fun L ↦ (L.1.lintegral_rootCount_eisensteinBox L.2 μ hμ).symm

open scoped Classical in
/-- Existence of an additive Haar measure on `Fin n → K` normalized on `integerBox K (Fin n)` gives
the box-volume identity without ambient measure-space hypotheses. -/
private theorem exists_normalized_encard_mul (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite ∧
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) =
      if IsOreAdmissible K n j then
        (n : ℝ≥0∞) *
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
            (1 + ∑ m ∈ Finset.Ico 1 n, oreCoefficientDepth K n j m) *
            if j % n = 0 then 1 else 1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
      else 0 := by
  let : MeasurableSpace (Fin n → K) := borel _
  have : BorelSpace (Fin n → K) := ⟨rfl⟩
  let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
    ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
      rw [isOpen_integerBox.interior_eq]; exact ⟨0, by simp⟩⟩
  let μ := Measure.addHaarMeasure B
  have hμ : μ (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
  have hbox := encard_mem_totallyRamifiedOfDegree_wildExponent_eq_mul (j := j) μ hμ
  let q : ℝ≥0∞ := Nat.card 𝓀[K]
  have hq1 : (1 : ℝ≥0∞) < q := Nat.one_lt_cast.mpr Finite.one_lt_card
  have hqtop : q ≠ ∞ := ENNReal.natCast_ne_top _
  have hsub0 : 1 - 1 / q ≠ 0 := (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
  have hsubtop : 1 - 1 / q ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hpow0 : 1 / q ^ (n + j) ≠ 0 := (ENNReal.div_pos one_ne_zero (ENNReal.pow_ne_top hqtop)).ne'
  by_cases hadm : IsOreAdmissible K n j
  · rw [measure_eisensteinBox hadm μ hμ] at hbox
    have hrhs : (n : ℝ≥0∞) * (1 / q ^ (1 + ∑ m ∈ Finset.Ico 1 n, oreCoefficientDepth K n j m) *
        (1 - 1 / q) * if j % n = 0 then 1 else 1 - 1 / q) ≠ ∞ := by
      refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top
          (pow_ne_zero _ (zero_lt_one.trans hq1).ne')) hsubtop) ?_)
      split_ifs <;> [exact ENNReal.one_ne_top; exact hsubtop]
    have henc : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) ≠ ∞ := by
      intro htop
      rw [htop, ENNReal.top_mul (mul_ne_zero hpow0 hsub0)] at hbox
      exact hrhs hbox.symm
    have hfin : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
      Set.encard_ne_top_iff.mp (ENat.toENNReal_ne_top.mp henc)
    refine ⟨hfin, ?_⟩
    rw [ite_eq_left hadm]
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe] at hbox
    refine (ENNReal.mul_left_inj hsub0 hsubtop).mp ?_
    calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
          (1 / q ^ (n + j)) * (1 - 1 / q)
        = (n : ℝ≥0∞) * (1 / q ^ (1 + ∑ m ∈ Finset.Ico 1 n, oreCoefficientDepth K n j m) *
            (1 - 1 / q) * if j % n = 0 then 1 else 1 - 1 / q) := by
          simpa only [mul_assoc] using hbox
      _ = (n : ℝ≥0∞) * (1 / q ^ (1 + ∑ m ∈ Finset.Ico 1 n, oreCoefficientDepth K n j m) *
            if j % n = 0 then 1 else 1 - 1 / q) * (1 - 1 / q) := by ring
  · rw [eisensteinBox_eq_empty_of_not_isOreAdmissible hadm, measure_empty, mul_zero,
      mul_eq_zero] at hbox
    have henc0 := hbox.resolve_right (mul_ne_zero hpow0 hsub0)
    have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.encard_eq_zero.mp (ENat.toENNReal_eq_zero.mp henc0)
    refine ⟨hempty ▸ Set.finite_empty, ?_⟩
    rw [hempty, Set.ncard_empty, Nat.cast_zero, zero_mul, ite_eq_right hadm]

/-- Cross-multiplied natural-number form of Krasner's count for an Ore-admissible pair `(n, j)`. -/
private theorem ncard_mul_pow_oreCoefficientDepth_eq {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
      Nat.card 𝓀[K] ^ (1 + ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) * Nat.card 𝓀[K] =
    n * Nat.card 𝓀[K] ^ (n + j) *
      if j % n = 0 then Nat.card 𝓀[K] else Nat.card 𝓀[K] - 1 := by
  classical
  obtain ⟨_, hEq⟩ := exists_normalized_encard_mul (K := K) n j
  rw [ite_eq_left hadm] at hEq
  let qn := Nat.card 𝓀[K]
  let q : ℝ≥0∞ := qn
  let s := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr (Finite.one_lt_card : 1 < qn).ne_bot
  have hqtop : q ≠ ∞ := ENNReal.natCast_ne_top _
  have hmul := congrArg (· * (q ^ (n + j) * q ^ (1 + s) * q)) hEq
  have hcancel (k : ℕ) : 1 / q ^ k * q ^ k = 1 :=
    ENNReal.div_mul_cancel (pow_ne_zero k hq0) (ENNReal.pow_ne_top hqtop)
  have hlhs : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
      (1 / q ^ (n + j)) * (q ^ (n + j) * q ^ (1 + s) * q) =
      (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
        qn ^ (1 + s) * qn : ℕ) : ℝ≥0∞) := by
    calc ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
          (1 / q ^ (n + j)) * (q ^ (n + j) * q ^ (1 + s) * q)
        = ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) *
            (1 / q ^ (n + j) * q ^ (n + j)) * q ^ (1 + s) * q := by ring
      _ = (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard *
            qn ^ (1 + s) * qn : ℕ) : ℝ≥0∞) := by
          rw [hcancel, mul_one]; push_cast; rfl
  have hite : (if j % n = 0 then (1 : ℝ≥0∞) else 1 - 1 / q) * q =
      ((if j % n = 0 then qn else qn - 1 : ℕ) : ℝ≥0∞) := by
    split_ifs
    · exact one_mul q
    · rw [ENNReal.sub_mul (fun _ _ ↦ hqtop), one_mul, ENNReal.div_mul_cancel hq0 hqtop,
        ENNReal.natCast_sub, Nat.cast_one]
  have hrhs : (n : ℝ≥0∞) * (1 / q ^ (1 + s) * if j % n = 0 then 1 else 1 - 1 / q) *
      (q ^ (n + j) * q ^ (1 + s) * q) =
      ((n * qn ^ (n + j) * if j % n = 0 then qn else qn - 1 : ℕ) : ℝ≥0∞) := by
    calc (n : ℝ≥0∞) * (1 / q ^ (1 + s) * if j % n = 0 then 1 else 1 - 1 / q) *
          (q ^ (n + j) * q ^ (1 + s) * q)
        = (n : ℝ≥0∞) * (1 / q ^ (1 + s) * q ^ (1 + s)) * q ^ (n + j) *
            ((if j % n = 0 then 1 else 1 - 1 / q) * q) := by ring
      _ = ((n * qn ^ (n + j) * if j % n = 0 then qn else qn - 1 : ℕ) : ℝ≥0∞) := by
          rw [hcancel, mul_one, hite]; push_cast; rfl
  rw [hlhs, hrhs] at hmul
  exact Nat.cast_inj.mp hmul

/-- **Krasner's discriminant-refined count**: for every degree `n` and wild exponent `j`, the set
`{E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}` is finite, including in equal
characteristic, and its cardinality equals `krasnerCount K n j`. -/
theorem krasner_refined_count (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite ∧
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
        krasnerCount K n j := by
  classical
  obtain ⟨hfin, hEq⟩ := exists_normalized_encard_mul (K := K) n j
  refine ⟨hfin, ?_⟩
  by_cases hadm : IsOreAdmissible K n j
  · have hnat := congrArg (Nat.cast (R := ℚ)) (ncard_mul_pow_oreCoefficientDepth_eq (K := K) hadm)
    let qn := Nat.card 𝓀[K]
    let q : ℚ := qn
    let s := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    have hq1 : 1 < qn := Finite.one_lt_card
    have hq : q ≠ 0 := Nat.cast_ne_zero.mpr (zero_lt_one.trans hq1).ne'
    have hden : q ^ (1 + s) * q ≠ 0 := mul_ne_zero (pow_ne_zero _ hq) hq
    refine mul_right_cancel₀ hden ?_
    have hn : 0 < n := hadm.pos
    have hnj : n + j - 1 + 1 = n + j := by omega
    have hite : ((if j % n = 0 then qn else qn - 1 : ℕ) : ℚ) =
        (if j % n = 0 then 1 else 1 - q⁻¹) * q := by
      split_ifs
      · exact (one_mul q).symm
      · rw [Nat.cast_sub hq1.le, Nat.cast_one, sub_mul, one_mul, inv_mul_cancel₀ hq]
    have hkras : krasnerCount K n j * (q ^ (1 + s) * q) =
        (n : ℚ) * q ^ (n + j) * ((if j % n = 0 then qn else qn - 1 : ℕ) : ℚ) := by
      rw [krasnerCount, ite_eq_left hadm, zpow_sub₀ hq, zpow_natCast, zpow_natCast, hite,
        pow_add q 1 s, pow_one]
      calc (n : ℚ) * (q ^ (n + j - 1) / q ^ s) * (if j % n = 0 then 1 else 1 - q⁻¹) *
            (q * q ^ s * q)
          = (n : ℚ) * (q ^ (n + j - 1) / q ^ s * q ^ s) * q *
              ((if j % n = 0 then 1 else 1 - q⁻¹) * q) := by ring
        _ = (n : ℚ) * (q ^ (n + j - 1) * q) * ((if j % n = 0 then 1 else 1 - q⁻¹) * q) := by
            rw [div_mul_cancel₀ _ (pow_ne_zero _ hq), mul_assoc (n : ℚ) (q ^ (n + j - 1)) q]
        _ = (n : ℚ) * q ^ (n + j) * ((if j % n = 0 then 1 else 1 - q⁻¹) * q) := by
            rw [← pow_succ, hnj]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow] at hnat
    rw [hkras, ← mul_assoc]
    exact hnat
  · rw [ite_eq_right hadm, mul_eq_zero] at hEq
    have hpow0 : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) ≠ 0 :=
      (ENNReal.div_pos one_ne_zero (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne'
    have hncard : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard = 0 :=
      Nat.cast_eq_zero.mp (hEq.resolve_right hpow0)
    rw [hncard, Nat.cast_zero, krasnerCount_of_not_isOreAdmissible hadm]

/-- Every wild-exponent fiber of `totallyRamifiedOfDegree K n` is finite, including in equal
characteristic. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite :=
  (krasner_refined_count (K := K) n j).1

/-- Rational cardinality formula for the wild-exponent-`j` fiber of `totallyRamifiedOfDegree K n`.
-/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) = krasnerCount K n j :=
  (krasner_refined_count (K := K) n j).2

/-- **Bounded-wild-exponent finiteness**: for every degree `n` and bound `B`, there are only
finitely many `E ∈ totallyRamifiedOfDegree K n` with `E.wildExponent ≤ B`, even in equal
characteristic `p` with `p ∣ n`. -/
theorem finite_mem_totallyRamifiedOfDegree_wildExponent_le (n B : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ B}.Finite := by
  refine ((Finset.range (B + 1)).finite_toSet.biUnion fun j _ ↦
    finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset ?_
  rintro E ⟨hE, hle⟩
  exact Set.mem_iUnion₂.mpr ⟨E.wildExponent, Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hle),
    hE, rfl⟩

/-- **Bounded-discriminant finiteness**: for every degree `n` and bound `D`, there are only
finitely many `E ∈ totallyRamifiedOfDegree K n` with `E.discriminantExponent ≤ D`, in any
characteristic. -/
theorem finite_mem_totallyRamifiedOfDegree_discriminantExponent_le (n D : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ D}.Finite := by
  refine (finite_mem_totallyRamifiedOfDegree_wildExponent_le (K := K) n (D + 1)).subset ?_
  rintro E ⟨hE, hle⟩
  have hw := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hE
  exact ⟨hE, by omega⟩

/-- **Consistency of Krasner's count with Serre's first mass formula**: summing the fiber counts
weighted by `q ^ (-j)` over all `j : ℕ` recovers `n`. -/
theorem tsum_ncard_wildExponent_eq_div_pow (n : ℕ) :
    ∑' j : ℕ,
      ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  let T (j : ℕ) : Set (IntermediateField K (SeparableClosure K)) :=
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  have hU : totallyRamifiedOfDegree K n = ⋃ j : ℕ, T j := by
    ext E; simp [T]
  have hdisj : Set.univ.PairwiseDisjoint T := by
    rintro i - j - hij
    exact Set.disjoint_left.mpr fun E h1 h2 ↦ hij (h1.2.symm.trans h2.2)
  have hserre := tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)
  rw [hU, tsum_iUnion (f := fun E ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.wildExponent) hdisj] at hserre
  rw [← hserre]
  refine tsum_congr fun j ↦ ?_
  have hfin := finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j
  calc (({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℝ≥0∞) /
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ j)
      = (T j).encard * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j) := by
        rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, div_eq_mul_one_div]
    _ = ∑' E : T j, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.1.wildExponent := by
        rw [← ENNReal.tsum_set_const]
        exact tsum_congr fun E ↦ by rw [E.2.2]

namespace IsRepresentativeSet

variable {n : ℕ} {R : Set (IntermediateField K (SeparableClosure K))}

/-- For any set of representatives `R` of `σ_K(n)` and any wild exponent `j`, the subset of
representatives of wild exponent `j` is finite. -/
theorem finite_wildExponent_eq (hR : IsRepresentativeSet n R) (j : ℕ) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset
    fun _ hM ↦ ⟨hR.subset hM.1, hM.2⟩

/-- **Isomorphism-class form of Krasner's count**: for any representative set `R` of `σ_K(n)`, the
automorphism-weighted count of representatives of wild exponent `j` equals `krasnerCount K n j / n`.
-/
theorem tsum_one_div_natCard_algEquiv_wildExponent_eq (hR : IsRepresentativeSet n R) (j : ℕ) :
    (∑' M : {M ∈ R | M.wildExponent = j}, (1 : ℚ) / Nat.card (M ≃ₐ[K] M)) =
      krasnerCount K n j / n := by
  classical
  rcases n.eq_zero_or_pos with rfl | hn
  · have hempty : {M ∈ R | M.wildExponent = j} = ∅ := by
      ext M; simp [Set.subset_empty_iff.mp (totallyRamifiedOfDegree_zero (K := K) ▸ hR.subset)]
    simp [hempty]
  let SR := {M ∈ R | M.wildExponent = j}
  let _ : Fintype SR := (hR.finite_wildExponent_eq j).fintype
  have hrep := hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ if L.wildExponent = j then (1 : ℝ≥0∞) else 0)
    (fun e ↦ by simp [IntermediateField.wildExponent_eq_of_algEquiv e])
  rw [tsum_ite_wildExponent_eq, mul_one,
    ← (finite_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).cast_ncard_eq,
    ENat.toENNReal_coe] at hrep
  let g : SR → R := fun M ↦ ⟨M.1, M.2.1⟩
  have hg : Function.Injective g := by rintro ⟨_, _⟩ ⟨_, _⟩ h; cases h; rfl
  have hsupp : Function.support (fun M : R ↦
      (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) * if M.1.wildExponent = j then 1 else 0) ⊆
      Set.range g := by
    intro M hM
    rw [Function.mem_support] at hM
    by_cases hw : M.1.wildExponent = j
    · exact ⟨⟨M.1, M.2, hw⟩, rfl⟩
    · exact absurd (by simp [hw]) hM
  rw [← hg.tsum_eq hsupp, tsum_fintype] at hrep
  have hsum_eq : (∑ M : SR, (n : ℝ≥0∞) / Nat.card (g M ≃ₐ[K] g M) *
      if (g M).1.wildExponent = j then 1 else 0) =
      ∑ M : SR, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) :=
    Finset.sum_congr rfl fun M _ ↦ by
      simpa only [g, M.2.2, ↓reduceIte] using mul_one ((n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M))
  rw [hsum_eq] at hrep
  have hne (M : SR) : (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) ≠ ∞ := by
    have := (mem_totallyRamifiedOfDegree_iff.1 (hR.subset M.2.1)).2.finite
    have hAut : (Nat.card (M ≃ₐ[K] M) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.card_ne_zero.2 ⟨⟨.refl⟩, inferInstance⟩)
    exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hAut
  have hreal := congrArg ENNReal.toReal hrep
  rw [ENNReal.toReal_natCast, ENNReal.toReal_sum fun M _ ↦ hne M] at hreal
  have hterm (M : SR) : ((n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M)).toReal =
      (n : ℝ) * (1 / Nat.card (M ≃ₐ[K] M)) := by
    rw [div_eq_mul_inv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, one_div]
  simp_rw [hterm, ← Finset.mul_sum] at hreal
  have hrat : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard : ℚ) =
      (n : ℚ) * ∑ M : SR, (1 : ℚ) / Nat.card (M ≃ₐ[K] M) :=
    Rat.cast_injective (α := ℝ) (by push_cast; exact hreal)
  rw [tsum_fintype, eq_div_iff (Nat.cast_ne_zero.mpr hn.ne'), mul_comm, ← hrat,
    ncard_mem_totallyRamifiedOfDegree_wildExponent_eq]

end IsRepresentativeSet

/-! ### Pauli and Roblot's closed formula when `v_K(p) = 1` -/

/-- Pointwise identity `oreCoefficientDepth + min = k + 1` when `v_K(p) = 1`. -/
private theorem oreCoefficientDepth_add_min_of_natCastValuation_eq_one [CharZero K]
    (hvp : natCastValuation K (ringChar 𝓀[K]) (natCast_ringChar_residueField_ne_zero K) = 1)
    {n j h : ℕ} (hh : h ≠ 0) :
    oreCoefficientDepth K n j h +
      min (j / n + if h < j % n then 1 else 0) (padicValNat (ringChar 𝓀[K]) h) =
        (j / n + if h < j % n then 1 else 0) + 1 := by
  have hhK : (h : K) ≠ 0 := Nat.cast_ne_zero.mpr hh
  rw [oreCoefficientDepth_of_natCast_ne_zero hhK,
    natCastValuation_eq_padicValNat_mul K hhK (natCast_ringChar_residueField_ne_zero K),
    hvp, mul_one]
  omega

/-- Evaluation of `∑_{h=1}^{n-1} oreCoefficientDepth K n j h` when `v_K(p) = 1` and `j % n = 0`. -/
private theorem sum_oreCoefficientDepth_add_of_mod_eq_zero [CharZero K]
    (hvp : natCastValuation K (ringChar 𝓀[K]) (natCast_ringChar_residueField_ne_zero K) = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hb : j % n = 0) :
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) +
      ∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i = n + j - 1 := by
  have hj : n * (j / n) = j := by have := Nat.div_add_mod j n; omega
  set p := ringChar 𝓀[K]
  set a := j / n
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hn : 0 < n := hadm.pos
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have ha : a = padicValNat p n := by
    rcases (isOreAdmissible_iff_natCastValuation hnK).mp hadm with ⟨_, h⟩ | ⟨_, hb', -⟩
    · rwa [natCastValuation_eq_padicValNat_mul K hnK (natCast_ringChar_residueField_ne_zero K),
        hvp, mul_one] at h
    · exact absurd hb hb'.ne'
  have hpt : ∀ h ∈ Finset.Ico 1 n,
      oreCoefficientDepth K n j h + min a (padicValNat p h) = a + 1 := fun h hh ↦ by
    have h0 := oreCoefficientDepth_add_min_of_natCastValuation_eq_one hvp (n := n) (j := j)
      (by have := (Finset.mem_Ico.mp hh).1; omega : h ≠ 0)
    rwa [hb, ite_eq_right (Nat.not_lt_zero h), add_zero] at h0
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, sum_Ico_min_padicValNat hp.ne_one n a, Finset.sum_const,
    Nat.card_Ico, smul_eq_mul] at hsum
  have hdiv := sum_Icc_sub_one_div_pow_add ha.le
  have hmul : (n - 1) * (a + 1) + a = n + j - 1 := by
    have hj' : (j : ℤ) = (n : ℤ) * a := by exact_mod_cast hj.symm
    zify [hn, Nat.le_add_right_of_le hn]
    rw [hj']; ring
  omega

/-- Evaluation of `∑_{h=1}^{n-1} oreCoefficientDepth K n j h` when `v_K(p) = 1` and `0 < j % n`. -/
private theorem sum_oreCoefficientDepth_add_of_mod_pos [CharZero K]
    (hvp : natCastValuation K (ringChar 𝓀[K]) (natCast_ringChar_residueField_ne_zero K) = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) (hb : 0 < j % n) :
    (∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) +
      ((∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i) +
        (j % n) / (ringChar 𝓀[K]) ^ (j / n + 1)) + 1 = n + j - 1 := by
  have hj : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hn : 0 < n := hadm.pos
  set p := ringChar 𝓀[K]
  set a := j / n
  set b := j % n
  have hbn : b < n := Nat.mod_lt j hn
  have hp : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hadm' : padicValNat p b ≤ a ∧ a + 1 ≤ padicValNat p n := by
    rcases (isOreAdmissible_iff_natCastValuation hnK).mp hadm with ⟨hb0, _⟩ | ⟨hbK, _, hbv, hnv⟩
    · exact absurd hb0 hb.ne'
    · rw [natCastValuation_eq_padicValNat_mul K hbK (natCast_ringChar_residueField_ne_zero K),
        hvp, mul_one] at hbv
      rw [natCastValuation_eq_padicValNat_mul K hnK (natCast_ringChar_residueField_ne_zero K),
        hvp, mul_one] at hnv
      exact ⟨hbv, hnv⟩
  have hb1 : 1 ≤ b := hb
  have hs1 : (∑ h ∈ Finset.Ico 1 b, oreCoefficientDepth K n j h) +
      ((∑ i ∈ Finset.Icc 1 a, (b - 1) / p ^ i) + (b - 1) / p ^ (a + 1)) = (b - 1) * (a + 2) := by
    have hc : ∑ h ∈ Finset.Ico 1 b, (oreCoefficientDepth K n j h + min (a + 1) (padicValNat p h)) =
        ∑ _ ∈ Finset.Ico 1 b, (a + 2) := Finset.sum_congr rfl fun h hh ↦ by
      have h0 := oreCoefficientDepth_add_min_of_natCastValuation_eq_one hvp (n := n) (j := j)
        (Nat.ne_of_gt (Finset.mem_Ico.mp hh).1)
      rwa [ite_eq_left (Finset.mem_Ico.mp hh).2, add_assoc] at h0
    rwa [Finset.sum_add_distrib, sum_Ico_min_padicValNat hp.ne_one b (a + 1),
      Finset.sum_Icc_succ_top (Nat.succ_pos a), Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hc
  have hs2 : (∑ h ∈ Finset.Ico b n, oreCoefficientDepth K n j h) +
      ∑ h ∈ Finset.Ico b n, min a (padicValNat p h) = (n - b) * (a + 1) := by
    have hc : ∑ h ∈ Finset.Ico b n, (oreCoefficientDepth K n j h + min a (padicValNat p h)) =
        ∑ _ ∈ Finset.Ico b n, (a + 1) := Finset.sum_congr rfl fun h hh ↦ by
      have h0 := oreCoefficientDepth_add_min_of_natCastValuation_eq_one hvp (n := n) (j := j)
        (Nat.ne_of_gt (hb.trans_le (Finset.mem_Ico.mp hh).1))
      rwa [ite_eq_right (Nat.not_lt.mpr (Finset.mem_Ico.mp hh).1), add_zero] at h0
    rwa [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul] at hc
  have hm := Finset.sum_Ico_consecutive (fun h ↦ min a (padicValNat p h)) hb1 hbn.le
  rw [sum_Ico_min_padicValNat hp.ne_one b a, sum_Ico_min_padicValNat hp.ne_one n a] at hm
  have hso := Finset.sum_Ico_consecutive (oreCoefficientDepth K n j) hb1 hbn.le
  have hdivn := sum_Icc_sub_one_div_pow_add ((Nat.le_succ a).trans hadm'.2)
  have hdivb : (b - 1) / p ^ (a + 1) = b / p ^ (a + 1) := by
    have hndvd : ¬ p ^ (a + 1) ∣ b := by
      rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one hb.ne', ← Nat.padicValNat_def]
      exact not_le.mpr (Nat.lt_succ_of_le hadm'.1)
    have hs := Nat.succ_div_of_not_dvd ((Nat.sub_add_cancel hb).symm ▸ hndvd)
    rwa [Nat.sub_add_cancel hb, eq_comm] at hs
  have halg : (b - 1) * (a + 2) + (n - b) * (a + 1) + a + 1 = n + j - 1 := by
    have hj' : (j : ℤ) = (n : ℤ) * a + b := by exact_mod_cast hj.symm
    zify [hb, hbn.le, Nat.le_add_right_of_le hn]
    rw [hj']; ring
  omega

/-- **Pauli and Roblot's closed form for `krasnerCount` when `v_K(p) = 1`**: over an absolutely
unramified mixed-characteristic local field `K` with residue cardinality `q` and residue
characteristic `p`, for every Ore-admissible pair `(n, j)`, `krasnerCount K n j` equals
`n · q ^ (∑_{i=1}^{j/n} ⌊n / p^i⌋)` when `j % n = 0` and
`n · (q - 1) · q ^ (∑_{i=1}^{j/n} ⌊n / p^i⌋ + ⌊(j % n) / p^(j/n + 1)⌋)` when `j % n > 0`. -/
theorem krasnerCount_eq_of_natCastValuation_ringChar_eq_one [CharZero K]
    (hvp : natCastValuation K (ringChar 𝓀[K]) (natCast_ringChar_residueField_ne_zero K) = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    krasnerCount K n j =
      let p := ringChar 𝓀[K]
      let q : ℚ := Nat.card 𝓀[K]
      if j % n = 0 then
        n * q ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else
        n * (q - 1) * q ^
          ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  dsimp only
  let q : ℚ := Nat.card 𝓀[K]
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [krasnerCount_of_isOreAdmissible hadm]
  dsimp only
  rcases (j % n).eq_zero_or_pos with hb | hb
  · have hexp : ((n + j - 1 : ℕ) : ℤ) -
        ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ) =
        ((∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i : ℕ) : ℤ) := by
      have := sum_oreCoefficientDepth_add_of_mod_eq_zero hvp hadm hb
      omega
    rw [ite_eq_left hb, ite_eq_left hb, mul_one, hexp, zpow_natCast]
  · have hexp : ((n + j - 1 : ℕ) : ℤ) -
        ((∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h : ℕ) : ℤ) =
        (((∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i) +
          (j % n) / (ringChar 𝓀[K]) ^ (j / n + 1) : ℕ) : ℤ) + 1 := by
      have := sum_oreCoefficientDepth_add_of_mod_pos hvp hadm hb
      omega
    set e := (∑ i ∈ Finset.Icc 1 (j / n), n / (ringChar 𝓀[K]) ^ i) +
      (j % n) / (ringChar 𝓀[K]) ^ (j / n + 1)
    rw [ite_eq_right hb.ne', ite_eq_right hb.ne', hexp, zpow_add₀ hq, zpow_one, zpow_natCast]
    calc (n : ℚ) * (q ^ e * q) * (1 - q⁻¹)
        = (n : ℚ) * (q - q * q⁻¹) * q ^ e := by ring
      _ = (n : ℚ) * (q - 1) * q ^ e := by rw [mul_inv_cancel₀ hq]

/-- **Natural-number form of Pauli and Roblot's count when `v_K(p) = 1`.** -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_of_natCastValuation_ringChar_eq_one
    [CharZero K]
    (hvp : natCastValuation K (ringChar 𝓀[K]) (natCast_ringChar_residueField_ne_zero K) = 1)
    {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard =
      let p := ringChar 𝓀[K]
      let q := Nat.card 𝓀[K]
      if j % n = 0 then
        n * q ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else
        n * (q - 1) * q ^
          ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  have hrat := (ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).trans
    (krasnerCount_eq_of_natCastValuation_ringChar_eq_one hvp hadm)
  have hq1 : 1 ≤ Nat.card 𝓀[K] := Nat.card_pos
  apply Nat.cast_injective (R := ℚ)
  rw [hrat]
  dsimp only
  split_ifs
  · push_cast; rfl
  · push_cast [Nat.cast_sub hq1]; rfl

end LocalField

section Padic

/-- **Pauli and Roblot's closed form for `krasnerCount` over `ℚ_[p]`.** -/
theorem krasnerCount_padic (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    krasnerCount ℚ_[p] n j =
      if j % n = 0 then
        n * (p : ℚ) ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else
        n * ((p : ℚ) - 1) * (p : ℚ) ^
          ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  have hchar : ringChar 𝓀[ℚ_[p]] = p :=
    @ringChar.eq 𝓀[ℚ_[p]] _ p (charP_residueField ℚ_[p] p)
  have hvp : natCastValuation ℚ_[p] (ringChar 𝓀[ℚ_[p]])
      (natCast_ringChar_residueField_ne_zero ℚ_[p]) = 1 := by
    rw [Padic.natCastValuation_eq_padicValNat, hchar]
    simpa only [Padic.natCastValuation_eq_padicValNat] using Padic.natCastValuation_self p
  rw [krasnerCount_eq_of_natCastValuation_ringChar_eq_one hvp hadm]
  simp [hchar]

/-- **Natural-number count of totally ramified degree-`n` extensions of `ℚ_[p]` with wild exponent
`j`** for an Ore-admissible pair `(n, j)`. -/
theorem ncard_mem_totallyRamifiedOfDegree_wildExponent_eq_padic (p : ℕ) [Fact p.Prime] {n j : ℕ}
    (hadm : IsOreAdmissible ℚ_[p] n j) :
    {E ∈ totallyRamifiedOfDegree ℚ_[p] n | E.wildExponent = j}.ncard =
      if j % n = 0 then
        n * p ^ (∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i)
      else
        n * (p - 1) * p ^
          ((∑ i ∈ Finset.Icc 1 (j / n), n / p ^ i) + (j % n) / p ^ (j / n + 1)) := by
  have hrat := (ncard_mem_totallyRamifiedOfDegree_wildExponent_eq (K := ℚ_[p]) n j).trans
    (krasnerCount_padic p hadm)
  apply Nat.cast_injective (R := ℚ)
  rw [hrat]
  split_ifs
  · push_cast; rfl
  · push_cast [Nat.cast_sub (Fact.out : p.Prime).pos]; rfl

end Padic

end TauCeti

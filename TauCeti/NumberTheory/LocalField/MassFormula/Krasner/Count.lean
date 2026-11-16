/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Krasner.Box
public import TauCeti.NumberTheory.LocalField.MassFormula.Representative
import Mathlib.MeasureTheory.Measure.Haar.Basic
import TauCeti.NumberTheory.LocalField.MassFormula.Countable
import TauCeti.NumberTheory.LocalField.MassFormula.Integral
import TauCeti.NumberTheory.LocalField.MassFormula.Main

/-!
# Krasner's count by degree and discriminant

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, and let `σ_K(n)` be
the set of totally ramified degree-`n` subextensions of a fixed separable closure of `K`.
Integrating the root counts of members of `σ_K(n)` over `TauCeti.eisensteinBox K n j` yields
Krasner's exact count `#{E ∈ σ_K(n) | E.wildExponent = j} = TauCeti.krasnerCount K n j` in both
mixed and equal characteristic, together with bounded-discriminant finiteness, consistency with
Serre's first mass formula, the isomorphism-class weighted count, the total count `#σ_K(n)` when
`(n : K) ≠ 0`, and Pauli–Roblot's closed forms in mixed and equal characteristic.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's count of members of `σ_K(n)` with wild exponent `j`.

## Main results

* `IntermediateField.lintegral_rootCount_eisensteinBox`: root-count integral over a discriminant
  box.
* `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq`,
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq`: Krasner's discriminant-refined count.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le`,
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-discriminant finiteness.
* `TauCeti.tsum_krasnerCount_div_natCard_residueField_pow`: Serre's first mass formula recovered.
* `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: isomorphism-class
  weighted count for fixed wild exponent.
* `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`: total cardinality of `σ_K(n)` when `(n : K) ≠ 0`.
* `TauCeti.krasnerCount_of_mod_eq_zero_of_natCast_ne_zero`,
  `TauCeti.krasnerCount_of_mod_pos_of_natCast_ne_zero`,
  `TauCeti.krasnerCount_of_natCast_ringChar_eq_zero`: closed forms in mixed and equal
  characteristic.

## References

* M. Krasner, *Nombre des extensions d'un degré donné d'un corps `𝔭`-adique*, in *Les Tendances
  Géom. en Algèbre et Théorie des Nombres*, Éditions du C.N.R.S., Paris, 1966, 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Theorem 6.1.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section
noncomputable section

open ValuativeRel IsDiscreteValuationRing MeasureTheory Function
open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Definition and basic API of `krasnerCount` -/

open Classical in
variable (K) in
/-- **Krasner's count** of totally ramified degree-`n` extensions of `K` with wild exponent `j`
inside a fixed separable closure. When `IsOreAdmissible K n j`, this equals
`n * q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h)` if `j % n = 0`, and
`n * (q - 1) * q ^ (n + j - 2 - ∑_{h=1}^{n-1} ν_h)` if `0 < j % n`, where `q = Nat.card 𝓀[K]` and
`ν_h = oreCoefficientDepth K n j h`; otherwise it is `0`. -/
def krasnerCount (n j : ℕ) : ℕ :=
  if IsOreAdmissible K n j then
    if j % n = 0 then
      n * Nat.card 𝓀[K] ^ (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
    else
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^ (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
  else 0

open Classical in
/-- Definitional unfolding of `krasnerCount`. -/
theorem krasnerCount_def (n j : ℕ) :
    krasnerCount K n j =
      if IsOreAdmissible K n j then
        if j % n = 0 then
          n * Nat.card 𝓀[K] ^ (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
        else
          n * (Nat.card 𝓀[K] - 1) *
            Nat.card 𝓀[K] ^ (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h)
      else 0 :=
  (rfl)

/-- For an inadmissible wild exponent, Krasner's count vanishes. -/
theorem krasnerCount_of_not_isOreAdmissible {n j : ℕ} (h : ¬ IsOreAdmissible K n j) :
    krasnerCount K n j = 0 := by
  rw [krasnerCount_def, ite_eq_right h]

/-- In degree zero, Krasner's count is zero. -/
@[simp]
theorem krasnerCount_zero_left (j : ℕ) : krasnerCount K 0 j = 0 :=
  krasnerCount_of_not_isOreAdmissible (not_isOreAdmissible_zero_left j)

/-- In degree one, Krasner's count is `1` at wild exponent `0` and `0` otherwise. -/
@[simp]
theorem krasnerCount_one_left (j : ℕ) : krasnerCount K 1 j = if j = 0 then 1 else 0 := by
  rcases eq_or_ne j 0 with rfl | hj <;> simp [krasnerCount_def, *]

/-- Evaluation of `krasnerCount` when `IsOreAdmissible K n j` and `j % n = 0`. -/
theorem krasnerCount_of_mod_eq_zero {n j : ℕ} (hO : IsOreAdmissible K n j) (hb : j % n = 0) :
    krasnerCount K n j =
      n * Nat.card 𝓀[K] ^ (n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  rw [krasnerCount_def, ite_eq_left hO, ite_eq_left hb]

/-- Evaluation of `krasnerCount` when `IsOreAdmissible K n j` and `0 < j % n`. -/
theorem krasnerCount_of_mod_pos {n j : ℕ} (hO : IsOreAdmissible K n j) (hb : 0 < j % n) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^ (n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) := by
  rw [krasnerCount_def, ite_eq_left hO, ite_eq_right hb.ne']

/-- Krasner's count is positive if and only if `(n, j)` is Ore-admissible. -/
theorem krasnerCount_pos_iff {n j : ℕ} : 0 < krasnerCount K n j ↔ IsOreAdmissible K n j := by
  have hq : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  by_cases hO : IsOreAdmissible K n j
  · refine iff_of_true ?_ hO
    rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · rw [krasnerCount_of_mod_eq_zero hO hb]; exact Nat.mul_pos hO.pos (pow_pos (by omega) _)
    · rw [krasnerCount_of_mod_pos hO hb]
      exact Nat.mul_pos (Nat.mul_pos hO.pos (by omega)) (pow_pos (by omega) _)
  · simp [krasnerCount_of_not_isOreAdmissible hO, hO]

/-- Krasner's count vanishes if and only if `(n, j)` is not Ore-admissible. -/
theorem krasnerCount_eq_zero_iff {n j : ℕ} :
    krasnerCount K n j = 0 ↔ ¬ IsOreAdmissible K n j := by
  rw [← not_iff_not, not_not, ← ne_eq, ← Nat.pos_iff_ne_zero, krasnerCount_pos_iff]

open Classical in
/-- Rational form of Krasner's formula:
`krasnerCount K n j = n * q ^ ((n + j - 1) - ∑ ν_h) * (if j % n = 0 then 1 else 1 - q⁻¹)` when
`IsOreAdmissible K n j`, and `0` otherwise. -/
theorem natCast_krasnerCount (n j : ℕ) :
    (krasnerCount K n j : ℚ) =
      if IsOreAdmissible K n j then
        (n : ℚ) * (Nat.card 𝓀[K] : ℚ) ^
          ((n + j - 1 : ℤ) - ∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) *
          (if j % n = 0 then 1 else 1 - (Nat.card 𝓀[K] : ℚ)⁻¹)
      else 0 := by
  by_cases hO : IsOreAdmissible K n j
  · rw [ite_eq_left hO]
    have hn := hO.pos; have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    rw [show (∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) = (S : ℤ) by
      exact_mod_cast (Nat.cast_sum (Finset.Ico 1 n) (oreCoefficientDepth K n j)).symm]
    rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · have := sum_oreCoefficientDepth_le (K := K) (j := j) hn
      rw [krasnerCount_of_mod_eq_zero hO hb, ite_eq_left hb, mul_one,
        show (n + j - 1 : ℤ) - (S : ℤ) = ((n + j - 1 - S : ℕ) : ℤ) by omega, zpow_natCast]
      push_cast; rfl
    · have : 0 < j := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hb
      have := sum_oreCoefficientDepth_add_one_le (K := K) (j := j) hn hb
      rw [krasnerCount_of_mod_pos hO hb, ite_eq_right hb.ne',
        show (n + j - 1 : ℤ) - (S : ℤ) = ((n + j - 2 - S : ℕ) : ℤ) + 1 by omega,
        zpow_add_one₀ (Nat.cast_ne_zero.2 (by omega)), zpow_natCast, Nat.cast_mul, Nat.cast_mul,
        Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ Nat.card 𝓀[K]), Nat.cast_one]
      field_simp; rfl
  · rw [krasnerCount_of_not_isOreAdmissible hO, ite_eq_right hO, Nat.cast_zero]

/-! ### Root-count integral over the discriminant box and Krasner's count -/

/-- **Root-count integral on a discriminant box**: for `L ∈ σ_K(n)` and a left-invariant measure
normalized on the integer box, `L.rootCount` integrates over `eisensteinBox K n j` to
`q ^ (-(n + j)) * (1 - q⁻¹)` if `L.wildExponent = j`, and `0` otherwise. -/
theorem _root_.IntermediateField.lintegral_rootCount_eisensteinBox {n j : ℕ}
    {L : IntermediateField K (SeparableClosure K)} (hL : L ∈ totallyRamifiedOfDegree K n)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
      if L.wildExponent = j then
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
      else 0 := by
  by_cases heq : L.wildExponent = j
  · rw [ite_eq_left heq]
    have hint : ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ := by
      rw [show μ.restrict (eisensteinBox K n j) =
          (μ.restrict (eisensteinSet K n)).restrict (eisensteinBox K n j) by
        rw [Measure.restrict_restrict measurableSet_eisensteinBox,
          Set.inter_eq_left.2 (eisensteinBox_subset_eisensteinSet n j)],
        ← lintegral_indicator measurableSet_eisensteinBox]
      refine setLIntegral_congr_fun measurableSet_eisensteinSet fun a ha ↦ ?_
      by_cases hmem : a ∈ eisensteinBox K n j
      · exact Set.indicator_of_mem hmem _
      · rw [Set.indicator_of_notMem hmem,
          rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL ha (heq ▸ hmem),
          Nat.cast_zero]
    rw [hint, L.lintegral_rootCount hL μ hμ,
      ← IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL, heq, add_comm]
  · rw [ite_eq_right heq, setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦ by
      rw [rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne hL ha heq, Nat.cast_zero],
      lintegral_zero]

/-- Algebraic identity in `ℝ≥0∞` relating `krasnerCount K n j` to the volume of
`eisensteinBox K n j`. -/
private theorem krasnerCount_mul_weight_eq {n j : ℕ} (hO : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    (krasnerCount K n j : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      n * μ (eisensteinBox K n j) := by
  have hn := hO.pos; set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  have hq0 : q ≠ 0 := by simp [q, Nat.card_pos.ne']
  have hqt : q ≠ ∞ := ENNReal.natCast_ne_top _
  have hcancel (a b : ℕ) : q ^ a * (1 / q ^ (b + a)) = 1 / q ^ b := by
    rw [pow_add, one_div,
      ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt)),
      mul_comm (q ^ b)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul, one_div]
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  rw [measure_eisensteinBox hO μ hμ]
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · have := sum_oreCoefficientDepth_le (K := K) (j := j) hn
    have hpow : q ^ (n + j - 1 - S) * (1 / q ^ (n + j)) = 1 / q ^ (1 + S) := by
      nth_rw 2 [show n + j = (1 + S) + (n + j - 1 - S) by omega]; exact hcancel ..
    rw [krasnerCount_of_mod_eq_zero hO hb, ite_eq_left hb, mul_one, Nat.cast_mul, Nat.cast_pow,
      mul_assoc, ← mul_assoc (q ^ _), hpow]
  · have : 0 < j := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hb
    have := sum_oreCoefficientDepth_add_one_le (K := K) (j := j) hn hb
    have hpow : q ^ (n + j - 2 - S) * (1 / q ^ (n + j)) = 1 / q ^ (1 + S) * (1 / q) := by
      rw [show 1 / q ^ (1 + S) * (1 / q) = 1 / q ^ (1 + S + 1) by
        simp only [one_div]; rw [pow_succ,
          ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt))]]
      nth_rw 2 [show n + j = (1 + S + 1) + (n + j - 2 - S) by omega]; exact hcancel ..
    have hsub : ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) * (1 / q) = 1 - 1 / q := by
      rw [ENNReal.natCast_sub, Nat.cast_one, one_div,
        ENNReal.sub_mul fun _ _ ↦ ENNReal.inv_ne_top.2 hq0, ENNReal.mul_inv_cancel hq0 hqt,
        one_mul]
    rw [krasnerCount_of_mod_pos hO hb, ite_eq_right hb.ne', Nat.cast_mul, Nat.cast_mul,
      Nat.cast_pow, mul_assoc, mul_assoc, ← mul_assoc (q ^ _), hpow, ← hsub]
    ring

/-- Restricting a `tsum` over a set `s` by an `if` guard equals the `tsum` over `{x ∈ s | p x}`. -/
private theorem tsum_ite_subtype {α : Type*} (s : Set α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ≥0∞) :
    (∑' x : s, if p x.1 then f x.1 else 0) = ∑' x : {x ∈ s | p x}, f x.1 := by
  rw [tsum_subtype s (fun x ↦ if p x then f x else 0), tsum_subtype {x ∈ s | p x} f]
  refine tsum_congr fun x ↦ ?_
  by_cases hs : x ∈ s <;> by_cases hp : p x <;> simp [Set.indicator, hs, hp]

/-- **Krasner's discriminant-refined count (`encard` form)**: in a fixed separable closure of `K`,
the number of totally ramified degree-`n` subextensions with wild exponent `j` equals
`krasnerCount K n j`. This holds in both mixed and equal characteristic, and for all `n, j`. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard = krasnerCount K n j := by
  by_cases hO : IsOreAdmissible K n j
  · let : MeasurableSpace (Fin n → K) := borel _; have : BorelSpace (Fin n → K) := ⟨rfl⟩
    let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
      ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩,
        by rw [isOpen_integerBox.interior_eq]; exact ⟨0, by simp⟩⟩
    set μ := Measure.addHaarMeasure B
    have hμ : μ (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
    have := (countable_totallyRamifiedOfDegree hO.pos (K := K)).to_subtype
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞); set W : ℝ≥0∞ := 1 / q ^ (n + j) * (1 - 1 / q)
    have hq1 : (1 : ℝ≥0∞) < q := by dsimp [q]; exact_mod_cast Finite.one_lt_card
    have hW0 : W ≠ 0 := mul_ne_zero (ENNReal.div_pos one_ne_zero
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne'
      (tsub_pos_of_lt (by rwa [one_div, ENNReal.inv_lt_one])).ne'
    have hWtop : W ≠ ∞ := ENNReal.mul_ne_top
      (ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ (by simp [q, Nat.card_pos.ne'])))
      (ENNReal.sub_ne_top ENNReal.one_ne_top)
    have hcard : ({E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard : ℝ≥0∞) =
        (krasnerCount K n j : ℝ≥0∞) := (ENNReal.mul_left_inj hW0 hWtop).1 <| by
      rw [← ENNReal.tsum_set_const,
        ← tsum_ite_subtype (totallyRamifiedOfDegree K n) (·.wildExponent = j) (fun _ ↦ W),
        ← tsum_congr fun L : totallyRamifiedOfDegree K n ↦
          L.1.lintegral_rootCount_eisensteinBox L.2 μ hμ,
        ← lintegral_tsum fun L ↦ aemeasurable_rootCount_restrict_eisensteinBox μ L.2,
        setLIntegral_congr_fun measurableSet_eisensteinBox
          fun _ ha ↦ tsum_rootCount_eq_of_mem_eisensteinBox ha,
        setLIntegral_const, krasnerCount_mul_weight_eq hO μ hμ]
    exact_mod_cast hcard
  · have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨hE, hEj⟩ ↦ hO (hEj ▸ isOreAdmissible_wildExponent hE)
    rw [hempty, Set.encard_empty, krasnerCount_of_not_isOreAdmissible hO, Nat.cast_zero]

/-- For every degree `n` and wild exponent `j`, there are only finitely many members of `σ_K(n)`
with wild exponent `j`, including in equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.Finite := by
  rw [← Set.encard_ne_top_iff, encard_totallyRamifiedOfDegree_wildExponent_eq]
  exact ENat.natCast_ne_top _

/-- **Krasner's discriminant-refined count (`ncard` form)**: the cardinality of
`{E ∈ σ_K(n) | E.wildExponent = j}` equals `krasnerCount K n j`. -/
theorem ncard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.ncard = krasnerCount K n j := by
  rw [Set.ncard_def, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toNat_natCast]

/-! ### Bounded-discriminant finiteness, Serre consistency, and total count -/

/-- For every degree `n` and bound `B`, there are only finitely many members of `σ_K(n)` with wild
exponent at most `B`, including in equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_wildExponent_le (n B : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ B}.Finite :=
  ((Finset.range (B + 1)).finite_toSet.biUnion fun j _ ↦
    finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset fun _ ⟨hE, hle⟩ ↦
      Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hle)) ⟨hE, rfl⟩

/-- For every degree `n` and bound `B`, there are only finitely many members of `σ_K(n)` with
discriminant exponent at most `B`, including in equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n B : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ B}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n B).subset fun E ⟨hE, hle⟩ ↦ by
    have := (mem_totallyRamifiedOfDegree_iff.1 hE).2.finite
    have : 0 < Module.finrank K E := Module.finrank_pos
    exact ⟨hE, by rw [IntermediateField.wildExponent_def]; omega⟩

/-- Partitioning a `tsum` over `σ_K(n)` by wild exponent. -/
private theorem tsum_totallyRamifiedOfDegree_eq_tsum_wildExponent (n : ℕ)
    (f : IntermediateField K (SeparableClosure K) → ℝ≥0∞) :
    (∑' E : totallyRamifiedOfDegree K n, f E.1) =
      ∑' j : ℕ, ∑' E : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}, f E.1 := by
  let S (j : ℕ) := {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  have hU : totallyRamifiedOfDegree K n = ⋃ j : ℕ, S j := by
    ext E; simp only [Set.mem_iUnion, S, Set.mem_ofPred_eq]
    exact ⟨fun hE ↦ ⟨E.wildExponent, hE, rfl⟩, fun ⟨_, hE, _⟩ ↦ hE⟩
  have hdisj : Set.univ.PairwiseDisjoint S := fun _ _ _ _ hne ↦
    Set.disjoint_left.2 fun _ ⟨_, h1⟩ ⟨_, h2⟩ ↦ hne (h1.symm.trans h2)
  exact (Equiv.tsum_eq (Set.equivOfEq hU) fun E ↦ f E.1).trans (tsum_iUnion (f := f) hdisj)

/-- **Consistency with Serre's first mass formula**: summing `krasnerCount K n j / q ^ j` over all
wild exponents `j` yields `n`, in both mixed and equal characteristic. -/
theorem tsum_krasnerCount_div_natCard_residueField_pow (n : ℕ) :
    ∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ j = n := by
  have hmain := tsum_one_div_natCard_residueField_pow_wildExponent (K := K) (n := n)
  rw [tsum_totallyRamifiedOfDegree_eq_tsum_wildExponent n
    (fun E ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ E.wildExponent)] at hmain
  rw [← hmain]
  refine tsum_congr fun j ↦ ?_
  rw [tsum_congr fun E : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} ↦ by rw [E.2.2],
    ENNReal.tsum_set_const, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe,
    mul_one_div]

namespace IsRepresentativeSet

/-- For any set `R` of representatives of the `K`-isomorphism classes in `σ_K(n)`, there are only
finitely many representatives with a given wild exponent `j`. -/
theorem finite_wildExponent_eq {n j : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R) :
    {M ∈ R | M.wildExponent = j}.Finite :=
  (finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset fun _ ⟨hM, hj⟩ ↦
    ⟨hR.subset hM, hj⟩

/-- **Isomorphism-class form of Krasner's count (multiplicative form)**: for any set `R` of
representatives of the `K`-isomorphism classes in `σ_K(n)`,
`n * ∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j`. -/
theorem mul_tsum_one_div_natCard_algEquiv_wildExponent_eq {n j : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R) :
    (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, (1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) =
      krasnerCount K n j := by
  have hreg := hR.tsum_eq_tsum_div_natCard_algEquiv_mul
    (fun L ↦ if L.wildExponent = j then (1 : ℝ≥0∞) else 0) fun e ↦ by
      rw [IntermediateField.wildExponent_eq_of_algEquiv e]
  rw [tsum_ite_subtype (totallyRamifiedOfDegree K n) (·.wildExponent = j) (fun _ ↦ 1),
    ENNReal.tsum_set_one, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe,
    tsum_congr fun M : R ↦ show (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
        (if M.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
      if M.1.wildExponent = j then (n : ℝ≥0∞) * ((1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M)) else 0 by
        split_ifs <;> simp [div_eq_mul_inv],
    tsum_ite_subtype R (·.wildExponent = j)
      (fun M ↦ (n : ℝ≥0∞) * ((1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M))), ENNReal.tsum_mul_left] at hreg
  exact hreg.symm

/-- **Isomorphism-class form of Krasner's count**: for `0 < n` and any set `R` of representatives
of the `K`-isomorphism classes in `σ_K(n)`,
`∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`. -/
theorem tsum_one_div_natCard_algEquiv_wildExponent_eq {n j : ℕ}
    {R : Set (IntermediateField K (SeparableClosure K))} (hR : IsRepresentativeSet n R)
    (hn : 0 < n) :
    ∑' M : {M ∈ R | M.wildExponent = j}, (1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) =
      (krasnerCount K n j : ℝ≥0∞) / n :=
  (ENNReal.eq_div_iff (Nat.cast_ne_zero.2 hn.ne') (ENNReal.natCast_ne_top _)).2
    (hR.mul_tsum_one_div_natCard_algEquiv_wildExponent_eq (j := j))

end IsRepresentativeSet

/-- Total cardinality of `σ_K(n)` as the series of Krasner counts over all wild exponents. -/
theorem encard_totallyRamifiedOfDegree_eq_tsum (n : ℕ) :
    ((totallyRamifiedOfDegree K n).encard : ℝ≥0∞) = ∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) := by
  rw [← ENNReal.tsum_set_one, tsum_totallyRamifiedOfDegree_eq_tsum_wildExponent n (fun _ ↦ 1)]
  refine tsum_congr fun j ↦ ?_
  rw [ENNReal.tsum_set_one, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe]

/-- **Total count of `σ_K(n)` away from equal characteristic `p ∣ n`**: when `(n : K) ≠ 0`,
`#σ_K(n) = ∑_{j = 0}^{n * v_K(n)} krasnerCount K n j`. -/
theorem ncard_totallyRamifiedOfDegree_eq_sum {n : ℕ} (hnK : (n : K) ≠ 0) :
    (totallyRamifiedOfDegree K n).ncard =
      ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), krasnerCount K n j := by
  have htsum := encard_totallyRamifiedOfDegree_eq_tsum (K := K) n
  have hsum :
      ∑' j : ℕ, (krasnerCount K n j : ℝ≥0∞) =
        ∑ j ∈ Finset.range (n * natCastValuation K n hnK + 1), (krasnerCount K n j : ℝ≥0∞) := by
    refine tsum_eq_sum fun j hj ↦ ?_
    rw [Finset.mem_range, not_lt] at hj
    rw [krasnerCount_of_not_isOreAdmissible fun hO ↦ by
      have := hO.le_mul_natCastValuation hnK; omega, Nat.cast_zero]
  rw [hsum, ← Nat.cast_sum, ← ENat.toENNReal_coe, ENat.toENNReal_inj] at htsum
  rw [Set.ncard_def, htsum, ENat.toNat_natCast]

/-! ### Explicit closed forms in mixed and equal characteristic -/

/-- `min` commutes with coercion `ℕ → ℕ∞`. -/
private theorem min_natCast_enat (a b : ℕ) : min (a : ℕ∞) (b : ℕ∞) = ((min a b : ℕ) : ℕ∞) := by
  rcases le_total a b with h | h <;> simp [h]

/-- Pointwise saving identity: `ν_h + min (m_h - 1, v_K(h)) = m_h`. -/
private theorem oreCoefficientDepth_add_saving (n j h : ℕ) :
    oreCoefficientDepth K n j h +
        (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
          (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
      j / n + 1 + if h < j % n then 1 else 0 := by
  rw [oreCoefficientDepth_def]
  cases addVal 𝒪[K] (h : 𝒪[K]) with
  | top => simp only [ENat.sub_top, ENat.toNat_zero, min_top_right, ENat.toNat_natCast]; omega
  | coe v =>
    rw [ENat.toNat_sub (ENat.natCast_ne_top _), ENat.toNat_natCast, ENat.toNat_natCast,
      min_natCast_enat, ENat.toNat_natCast]
    omega

/-- Unified expression for the exponent of `q` in `krasnerCount K n j` in terms of valuation
savings `min (j / n + [h < j % n], v_K(h))`. -/
private theorem exponent_eq_add_sum_saving {n j : ℕ} (hn : 0 < n) :
    (if j % n = 0 then
        n + j - 1 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
      else
        n + j - 2 - ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h) =
      j / n + ∑ h ∈ Finset.Ico 1 n,
        (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
          (addVal 𝒪[K] (h : 𝒪[K]))).toNat := by
  have hsum_add : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
      ∑ h ∈ Finset.Ico 1 n, (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
        (addVal 𝒪[K] (h : 𝒪[K]))).toNat = (n - 1) * (j / n + 1) + (j % n - 1) := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl fun h _ ↦ oreCoefficientDepth_add_saving n j h,
      Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Finset.sum_boole,
      Nat.cast_id, show (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) by
        ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; have := Nat.mod_lt j hn; omega,
      Nat.card_Ico]
  have hdiv := Nat.div_add_mod j n
  have hmul : (n - 1) * (j / n + 1) + j / n = n * (j / n) + (n - 1) := by
    cases n with | zero => omega | succ m => simp only [Nat.add_sub_cancel]; ring
  have htot : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
      (j / n + ∑ h ∈ Finset.Ico 1 n, (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
        (addVal 𝒪[K] (h : 𝒪[K]))).toNat) = n * (j / n) + (n - 1) + (j % n - 1) := by linarith
  split_ifs <;> [rw [show n + j - 1 = n * (j / n) + (n - 1) + (j % n - 1) by omega];
    rw [show n + j - 2 = n * (j / n) + (n - 1) + (j % n - 1) by omega]] <;>
    rw [← htot, Nat.add_sub_cancel_left]

/-- Number of multiples of `d` in `[1, m)`: `m / d - 1` if `d ∣ m`, and `m / d` otherwise. -/
private theorem card_Ico_one_filter_dvd {m d : ℕ} (hm : 0 < m) (hd : 0 < d) :
    ((Finset.Ico 1 m).filter (d ∣ ·)).card = m / d - if d ∣ m then 1 else 0 := by
  rw [show Finset.Ico 1 m = Finset.Ioc 0 (m - 1) by
    ext h; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega, Nat.Ioc_filter_dvd_card_eq_div]
  split_ifs with h
  · obtain ⟨_ | k, rfl⟩ := h
    · simp at hm
    rw [Nat.mul_div_cancel_left _ hd, show d * (k + 1) - 1 = (d - 1) + d * k by
        rw [Nat.mul_succ]; omega,
      Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (by omega : d - 1 < d), zero_add,
      Nat.add_sub_cancel]
  · have := Nat.div_add_mod m d; have := Nat.mod_lt m hd
    have : 0 < m % d := Nat.pos_of_ne_zero fun h0 ↦ h (Nat.dvd_of_mod_eq_zero h0)
    rw [show m - 1 = (m % d - 1) + d * (m / d) by omega, Nat.add_mul_div_left _ _ hd,
      Nat.div_eq_of_lt (by omega : m % d - 1 < d), zero_add, Nat.sub_zero]

/-- Divisibility characterization of `i ≤ padicValNat p h * e`. -/
private theorem le_padicValNat_mul_iff {p h e i : ℕ} (hp : p.Prime) (hh : 0 < h) (he : 0 < e) :
    i ≤ padicValNat p h * e ↔ p ^ ((i + e - 1) / e) ∣ h := by
  have hceil : i ≤ padicValNat p h * e ↔ (i + e - 1) / e ≤ padicValNat p h := by
    have : i + e - 1 + 1 = i + e := by omega
    refine ⟨fun hle ↦ ?_, fun hle ↦ ?_⟩
    · have := (Nat.div_lt_iff_lt_mul he).2 (show i + e - 1 < (padicValNat p h + 1) * e by
        nlinarith); omega
    · have := Nat.div_add_mod (i + e - 1) e; have := Nat.mod_lt (i + e - 1) he; nlinarith
  rw [hceil, Nat.padicValNat_def, Nat.pow_dvd_iff_le_multiplicity hp.ne_one hh.ne']

/-- Combined divisor-sum evaluation for the mixed-characteristic exponent. -/
private theorem add_sum_min_padicValNat_mul {n p e a : ℕ} (hn : 0 < n) (hp : p.Prime) (he : 0 < e)
    (ha : a ≤ padicValNat p n * e) :
    a + ∑ h ∈ Finset.Ico 1 n, min a (padicValNat p h * e) =
      ∑ i ∈ Finset.Icc 1 a, n / p ^ ((i + e - 1) / e) := by
  have hmin (v : ℕ) : min a v = ∑ i ∈ Finset.Icc 1 a, if i ≤ v then 1 else 0 := by
    rw [← Finset.card_filter, show (Finset.Icc 1 a).filter (· ≤ v) = Finset.Icc 1 (min a v) by
      ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega, Nat.card_Icc]; omega
  have h1 : ∑ h ∈ Finset.Ico 1 n, min a (padicValNat p h * e) =
      ∑ i ∈ Finset.Icc 1 a, (n / p ^ ((i + e - 1) / e) - 1) := by
    rw [Finset.sum_congr rfl fun h _ ↦ hmin _, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hdvd := (le_padicValNat_mul_iff hp hn he).1 (le_trans (Finset.mem_Icc.1 hi).2 ha)
    rw [show (∑ h ∈ Finset.Ico 1 n, if i ≤ padicValNat p h * e then 1 else 0) =
        ((Finset.Ico 1 n).filter (p ^ ((i + e - 1) / e) ∣ ·)).card by
      rw [Finset.card_filter]; exact Finset.sum_congr rfl fun h hh ↦ by
        simp only [le_padicValNat_mul_iff hp (Finset.mem_Ico.1 hh).1 he],
      card_Ico_one_filter_dvd hn (pow_pos hp.pos _), ite_eq_left hdvd]
  rw [h1]
  nth_rw 1 [show a = ∑ _i ∈ Finset.Icc 1 a, 1 by
    rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]; omega]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hdvd := (le_padicValNat_mul_iff hp hn he).1 (le_trans (Finset.mem_Icc.1 hi).2 ha)
  have := Nat.div_pos (Nat.le_of_dvd hn hdvd) (pow_pos hp.pos ((i + e - 1) / e)); omega

/-- In mixed characteristic (`(ringChar 𝓀[K] : K) ≠ 0`), every positive natural number has additive
valuation `padicValNat p m * e`. -/
private theorem addVal_natCast_of_natCast_ringChar_ne_zero (hp : (ringChar 𝓀[K] : K) ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    addVal 𝒪[K] (m : 𝒪[K]) =
      ((padicValNat (ringChar 𝓀[K]) m * natCastValuation K (ringChar 𝓀[K]) hp : ℕ) : ℕ∞) := by
  have hmK : (m : K) ≠ 0 := fun h0 ↦
    hp (((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hm).1 h0).1 ▸
      ringChar.Nat.cast_ringChar (R := K))
  rw [IsDiscreteValuationRing.addVal_natCast K m hmK,
    natCastValuation_eq_padicValNat_mul K hmK hp]

/-- **Mixed-characteristic closed form of Krasner's count (`n ∣ j`, Pauli–Roblot Theorem 6.1)**:
for a mixed-characteristic local field `K` with residue characteristic `p` and absolute ramification
index `e = v_K(p)`, and an Ore-admissible `(n, j)` with `j % n = 0`,
`krasnerCount K n j = n * q ^ (∑_{i=1}^{j/n} n / p ^ ⌈i / e⌉)`. -/
theorem krasnerCount_of_mod_eq_zero_of_natCast_ne_zero {n j : ℕ}
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hO : IsOreAdmissible K n j) (hb : j % n = 0) :
    krasnerCount K n j =
      n * Nat.card 𝓀[K] ^
        ∑ i ∈ Finset.Icc 1 (j / n),
          n / ringChar 𝓀[K] ^
            ((i + natCastValuation K (ringChar 𝓀[K]) hp - 1) /
              natCastValuation K (ringChar 𝓀[K]) hp) := by
  set p := ringChar 𝓀[K]; set e := natCastValuation K p hp
  have hn := hO.pos; have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have he : 0 < e :=
    Nat.pos_of_ne_zero ((natCastValuation_ne_zero_iff_ringChar_eq K hp_prime hp).2 rfl)
  have ha_eq : j / n = padicValNat p n * e := by
    have hvn := (isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO
    rwa [addVal_natCast_of_natCast_ringChar_ne_zero hp hn, Nat.cast_inj] at hvn
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_left hb] at hexp
  rw [krasnerCount_of_mod_eq_zero hO hb, hexp,
    ← add_sum_min_padicValNat_mul hn hp_prime he ha_eq.le]
  congr 3
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  rw [hb, ite_eq_right (Nat.not_lt_zero h), add_zero,
    addVal_natCast_of_natCast_ringChar_ne_zero hp (Finset.mem_Ico.1 hh).1, min_natCast_enat,
    ENat.toNat_natCast]

/-- **Mixed-characteristic closed form of Krasner's count (`¬ n ∣ j`, Pauli–Roblot Theorem 6.1)**:
for a mixed-characteristic local field `K` with residue characteristic `p` and absolute ramification
index `e = v_K(p)`, and an Ore-admissible `(n, j)` with `0 < j % n`,
`krasnerCount K n j = n * (q - 1) * q ^ (∑_{i=1}^{j/n} n / p ^ ⌈i / e⌉ + (j % n) / p ^ ⌈(a+1)/e⌉)`
where `a = j / n`. -/
theorem krasnerCount_of_mod_pos_of_natCast_ne_zero {n j : ℕ}
    (hp : (ringChar 𝓀[K] : K) ≠ 0) (hO : IsOreAdmissible K n j) (hb : 0 < j % n) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^
        (∑ i ∈ Finset.Icc 1 (j / n),
          n / ringChar 𝓀[K] ^
            ((i + natCastValuation K (ringChar 𝓀[K]) hp - 1) /
              natCastValuation K (ringChar 𝓀[K]) hp) +
        (j % n) / ringChar 𝓀[K] ^
          ((j / n + natCastValuation K (ringChar 𝓀[K]) hp) /
            natCastValuation K (ringChar 𝓀[K]) hp)) := by
  set p := ringChar 𝓀[K]; set e := natCastValuation K p hp
  have hn := hO.pos; have hmod := Nat.mod_lt j hn
  have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have he : 0 < e :=
    Nat.pos_of_ne_zero ((natCastValuation_ne_zero_iff_ringChar_eq K hp_prime hp).2 rfl)
  have hvb : padicValNat p (j % n) * e ≤ j / n := by
    have h := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).1
    rwa [addVal_natCast_of_natCast_ringChar_ne_zero hp hb, Nat.cast_le] at h
  have hvn : j / n + 1 ≤ padicValNat p n * e := by
    have h := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).2
    rwa [addVal_natCast_of_natCast_ringChar_ne_zero hp hn, ← Nat.cast_add_one, Nat.cast_le] at h
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_right hb.ne'] at hexp
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞) (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
        min (j / n) (padicValNat p h * e) +
          if h < j % n ∧ j / n + 1 ≤ padicValNat p h * e then 1 else 0 := by
    rw [addVal_natCast_of_natCast_ringChar_ne_zero hp (Finset.mem_Ico.1 hh).1, min_natCast_enat,
      ENat.toNat_natCast]
    dsimp only [p, e]; split_ifs <;> omega
  have he_eq : j / n + 1 + e - 1 = j / n + e := by omega
  have hndvd : ¬ p ^ ((j / n + e) / e) ∣ j % n := fun hdvd ↦ by
    have := (le_padicValNat_mul_iff hp_prime hb he).2 (by rwa [he_eq]); omega
  have hsecond :
      (∑ h ∈ Finset.Ico 1 n, if h < j % n ∧ j / n + 1 ≤ padicValNat p h * e then 1 else 0) =
        (j % n) / p ^ ((j / n + e) / e) := by
    rw [← Finset.card_filter,
      show (Finset.Ico 1 n).filter (fun h ↦ h < j % n ∧ j / n + 1 ≤ padicValNat p h * e) =
          (Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ ((j / n + e) / e) ∣ h) by
        ext h; simp only [Finset.mem_filter, Finset.mem_Ico]
        exact ⟨fun ⟨⟨h1, _⟩, hlt, hle⟩ ↦ ⟨⟨h1, hlt⟩, by
            simpa [he_eq] using (le_padicValNat_mul_iff hp_prime h1 he).1 hle⟩,
          fun ⟨⟨h1, hlt⟩, hdvd⟩ ↦ ⟨⟨h1, lt_trans hlt hmod⟩, hlt,
            (le_padicValNat_mul_iff hp_prime h1 he).2 (by rwa [he_eq])⟩⟩,
      card_Ico_one_filter_dvd hb (pow_pos hp_prime.pos _), ite_eq_right hndvd, Nat.sub_zero]
  rw [krasnerCount_of_mod_pos hO hb, hexp, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib,
    ← add_assoc, add_sum_min_padicValNat_mul hn hp_prime he (Nat.le_of_succ_le hvn), hsecond]

/-- **Equal-characteristic closed form of Krasner's count**: when `K` has equal characteristic
`p = ringChar 𝓀[K]`, `0 < n`, `p ∣ n`, and `¬ p ∣ j`,
`krasnerCount K n j = n * (q - 1) * q ^ ((j / n) * (n / p) + (j % n) / p)`. -/
theorem krasnerCount_of_natCast_ringChar_eq_zero {n j : ℕ}
    (hp : (ringChar 𝓀[K] : K) = 0) (hn : 0 < n) (hpn : ringChar 𝓀[K] ∣ n)
    (hpj : ¬ ringChar 𝓀[K] ∣ j) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^ ((j / n) * (n / ringChar 𝓀[K]) + (j % n) / ringChar 𝓀[K]) := by
  set p := ringChar 𝓀[K]; have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hchar : ringChar K = p :=
    ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hp_prime.pos).1 hp).1
  have hcast_zero (m : ℕ) : (m : K) = 0 ↔ p ∣ m := by rw [← hchar, ringChar.spec K m]
  have hO := (isOreAdmissible_iff_of_natCast_eq_zero hn ((hcast_zero n).2 hpn)).2 hpj
  have hpb : ¬ p ∣ j % n := fun h ↦ hpj <| by
    rw [← Nat.div_add_mod j n]; exact dvd_add (dvd_mul_of_dvd_left hpn _) h
  have hb : 0 < j % n := Nat.pos_of_ne_zero fun h0 ↦ hpb (h0 ▸ dvd_zero p)
  have hmod := Nat.mod_lt j hn
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_right hb.ne'] at hexp
  have hpoint (h : ℕ) :
      (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞) (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
        (if p ∣ h then j / n else 0) + (if h < j % n ∧ p ∣ h then 1 else 0) := by
    by_cases hph : p ∣ h
    · have hh𝒪 : (h : 𝒪[K]) = 0 := Subtype.ext (by simpa using (hcast_zero h).2 hph)
      rw [hh𝒪, addVal_zero, min_top_right, ENat.toNat_natCast]; split_ifs <;> omega
    · have hhK : (h : K) ≠ 0 := mt (hcast_zero h).1 hph
      rw [IsDiscreteValuationRing.addVal_natCast K h hhK,
        (natCastValuation_eq_zero_iff_not_dvd K h hhK).2 hph,
        min_natCast_enat, Nat.min_zero, ENat.toNat_natCast]; split_ifs <;> omega
  have hsum1 : (∑ h ∈ Finset.Ico 1 n, if p ∣ h then j / n else 0) = (j / n) * (n / p - 1) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm,
      card_Ico_one_filter_dvd hn hp_prime.pos, ite_eq_left hpn]
  have hsum2 : (∑ h ∈ Finset.Ico 1 n, if h < j % n ∧ p ∣ h then 1 else 0) = (j % n) / p := by
    rw [← Finset.card_filter,
      show (Finset.Ico 1 n).filter (fun h ↦ h < j % n ∧ p ∣ h) =
          (Finset.Ico 1 (j % n)).filter (fun h ↦ p ∣ h) by
        ext h; simp only [Finset.mem_filter, Finset.mem_Ico]; omega,
      card_Ico_one_filter_dvd hb hp_prime.pos, ite_eq_right hpb, Nat.sub_zero]
  rw [krasnerCount_of_mod_pos hO hb, hexp, Finset.sum_congr rfl fun h _ ↦ hpoint h,
    Finset.sum_add_distrib, hsum1, hsum2]
  congr 2
  have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp_prime.pos
  have : j / n ≤ (j / n) * (n / p) := Nat.le_mul_of_pos_right _ hnp
  rw [Nat.mul_sub_left_distrib, mul_one]; omega

end TauCeti

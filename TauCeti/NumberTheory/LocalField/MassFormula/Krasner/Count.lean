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
the set of totally ramified degree-`n` subextensions of a fixed separable closure of `K`. For any
degree `n` and wild exponent `j`, integrating the root counts of members of `σ_K(n)` over the
discriminant box `TauCeti.eisensteinBox K n j` yields Krasner's exact count of the extensions
`E ∈ σ_K(n)` with wild exponent `j`:

`#{E ∈ σ_K(n) | E.wildExponent = j} = krasnerCount K n j`.

When `IsOreAdmissible K n j`, the count is
`n * q ^ (n + j - 1 - ∑_{h=1}^{n-1} ν_h)` if `n ∣ j`, and
`n * (q - 1) * q ^ (n + j - 2 - ∑_{h=1}^{n-1} ν_h)` if `¬ n ∣ j`,
where `ν_h = oreCoefficientDepth K n j h`; when `¬ IsOreAdmissible K n j`, the count is `0`.
In rational form, `TauCeti.natCast_krasnerCount` expresses this uniformly as
`n * q ^ ((n + j - 1) - ∑ ν_h) * (if j % n = 0 then 1 else 1 - q⁻¹)`.

Immediate consequences proved here include:

* finiteness of every fixed-discriminant and bounded-discriminant slice of `σ_K(n)`, in both mixed
  and equal characteristic (even when `σ_K(n)` itself is infinite);
* consistency with Serre's first mass formula: `∑' j, krasnerCount K n j / q ^ j = n`;
* the isomorphism-class form over any representative set `R`:
  `∑_{M ∈ R, c(M) = j} 1 / #Aut_K(M) = krasnerCount K n j / n`;
* the finite-sum total count `#σ_K(n) = ∑_{j ≤ n v_K(n)} krasnerCount K n j` whenever `(n : K) ≠ 0`;
* Pauli–Roblot's closed form in mixed characteristic in terms of `p`-power floors with ceiling
  steps by the absolute ramification index `e = v_K(p)`, and the corresponding closed form in equal
  characteristic `p ∣ n`.

## Main definitions

* `TauCeti.krasnerCount K n j`: Krasner's count of members of `σ_K(n)` with wild exponent `j`.

## Main results

* `IntermediateField.lintegral_rootCount_eisensteinBox`: the root count of `L ∈ σ_K(n)` integrates
  over `eisensteinBox K n j` to `q ^ (-(n + j)) * (1 - q⁻¹)` if `L.wildExponent = j`, and `0`
  otherwise.
* `TauCeti.encard_totallyRamifiedOfDegree_wildExponent_eq` and
  `TauCeti.ncard_totallyRamifiedOfDegree_wildExponent_eq`: Krasner's discriminant-refined count.
* `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_eq`,
  `TauCeti.finite_totallyRamifiedOfDegree_wildExponent_le`, and
  `TauCeti.finite_totallyRamifiedOfDegree_discriminantExponent_le`: bounded-discriminant finiteness
  in both mixed and equal characteristic.
* `TauCeti.tsum_krasnerCount_div_natCard_residueField_pow`: Serre's first mass formula recovered as
  the weighted sum of Krasner counts.
* `TauCeti.IsRepresentativeSet.tsum_one_div_natCard_algEquiv_wildExponent_eq`: the
  isomorphism-class weighted count for fixed wild exponent.
* `TauCeti.ncard_totallyRamifiedOfDegree_eq_sum`: total cardinality of `σ_K(n)` when `(n : K) ≠ 0`.
* `TauCeti.krasnerCount_of_mod_eq_zero_of_natCast_ne_zero` and
  `TauCeti.krasnerCount_of_mod_pos_of_natCast_ne_zero`: closed forms in mixed characteristic.
* `TauCeti.krasnerCount_of_natCast_ringChar_eq_zero`: closed form in equal characteristic.

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
  rcases eq_or_ne j 0 with rfl | hj
  · simp [krasnerCount_def]
  · simp [krasnerCount_def, hj]

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
    have hn := hO.pos
    rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · rw [krasnerCount_of_mod_eq_zero hO hb]
      exact Nat.mul_pos hn (pow_pos (by omega) _)
    · rw [krasnerCount_of_mod_pos hO hb]
      exact Nat.mul_pos (Nat.mul_pos hn (by omega)) (pow_pos (by omega) _)
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
    have hn := hO.pos
    have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
    have hq0 : (Nat.card 𝓀[K] : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
    have hS_cast : (∑ h ∈ Finset.Ico 1 n, (oreCoefficientDepth K n j h : ℤ)) = (S : ℤ) := by
      exact_mod_cast (Nat.cast_sum (Finset.Ico 1 n) (fun h ↦ oreCoefficientDepth K n j h)).symm
    rw [hS_cast]
    rcases Nat.eq_zero_or_pos (j % n) with hb | hb
    · have hSle : S ≤ n + j - 1 := sum_oreCoefficientDepth_le hn
      have hexp : (n + j - 1 : ℤ) - (S : ℤ) = ((n + j - 1 - S : ℕ) : ℤ) := by omega
      rw [krasnerCount_of_mod_eq_zero hO hb, ite_eq_left hb, mul_one, hexp, zpow_natCast]
      push_cast
      rfl
    · have hj : 0 < j := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hb
      have hSle : S + 1 ≤ n + j - 1 := sum_oreCoefficientDepth_add_one_le hn hb
      have hexp : (n + j - 1 : ℤ) - (S : ℤ) = ((n + j - 2 - S : ℕ) : ℤ) + 1 := by omega
      rw [krasnerCount_of_mod_pos hO hb, ite_eq_right hb.ne', hexp, zpow_add_one₀ hq0, zpow_natCast,
        Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ Nat.card 𝓀[K]),
        Nat.cast_one]
      field_simp
      rfl
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
    have hres : μ.restrict (eisensteinBox K n j) =
        (μ.restrict (eisensteinSet K n)).restrict (eisensteinBox K n j) := by
      rw [Measure.restrict_restrict measurableSet_eisensteinBox,
        Set.inter_eq_left.2 (eisensteinBox_subset_eisensteinSet n j)]
    have hint : ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ a in eisensteinSet K n, (L.rootCount a : ℝ≥0∞) ∂μ := by
      rw [hres, ← lintegral_indicator measurableSet_eisensteinBox]
      refine setLIntegral_congr_fun measurableSet_eisensteinSet fun a ha ↦ ?_
      by_cases hmem : a ∈ eisensteinBox K n j
      · exact Set.indicator_of_mem hmem _
      · rw [Set.indicator_of_notMem hmem,
          rootCount_eq_zero_of_mem_eisensteinSet_of_notMem_eisensteinBox hL ha (heq ▸ hmem),
          Nat.cast_zero]
    rw [hint, L.lintegral_rootCount hL μ hμ,
      ← IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hL, heq, add_comm]
  · rw [ite_eq_right heq]
    have hzero : ∫⁻ a in eisensteinBox K n j, (L.rootCount a : ℝ≥0∞) ∂μ =
        ∫⁻ _ in eisensteinBox K n j, (0 : ℝ≥0∞) ∂μ :=
      setLIntegral_congr_fun measurableSet_eisensteinBox fun a ha ↦ by
        rw [rootCount_eq_zero_of_mem_eisensteinBox_of_wildExponent_ne hL ha heq, Nat.cast_zero]
    rw [hzero, lintegral_zero]

/-- Algebraic identity in `ℝ≥0∞` relating `krasnerCount K n j` to the volume of
`eisensteinBox K n j`. -/
private theorem krasnerCount_mul_weight_eq {n j : ℕ} (hO : IsOreAdmissible K n j)
    [MeasurableSpace (Fin n → K)] [BorelSpace (Fin n → K)]
    (μ : Measure (Fin n → K)) [μ.IsAddLeftInvariant] (hμ : μ (integerBox K (Fin n)) = 1) :
    (krasnerCount K n j : ℝ≥0∞) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) =
      n * μ (eisensteinBox K n j) := by
  have hn := hO.pos
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := by simp [Nat.card_pos.ne']
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hcancel (a b : ℕ) :
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ a * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (b + a)) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ b := by
    rw [pow_add, one_div,
      ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt)),
      mul_comm ((Nat.card 𝓀[K] : ℝ≥0∞) ^ b)⁻¹, ← mul_assoc,
      ENNReal.mul_inv_cancel (pow_ne_zero _ hq0) (ENNReal.pow_ne_top hqt), one_mul, one_div]
  set S := ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h
  rw [measure_eisensteinBox hO μ hμ]
  rcases Nat.eq_zero_or_pos (j % n) with hb | hb
  · have hSle : S ≤ n + j - 1 := sum_oreCoefficientDepth_le hn
    have hadd : (1 + S) + (n + j - 1 - S) = n + j := by omega
    have hpow : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 1 - S) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) = 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) := by
      nth_rw 2 [← hadd]
      exact hcancel _ _
    rw [krasnerCount_of_mod_eq_zero hO hb, ite_eq_left hb, mul_one, Nat.cast_mul, Nat.cast_pow]
    calc ((n : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 1 - S)) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)))
        = (n : ℝ≥0∞) * (((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 1 - S) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j))) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by ring
      _ = (n : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by rw [hpow]
  · have : 0 < j := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hb
    have hSle : S + 1 ≤ n + j - 1 := sum_oreCoefficientDepth_add_one_le hn hb
    have hadd : (1 + S + 1) + (n + j - 2 - S) = n + j := by omega
    have hpow : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - S) *
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j)) =
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S + 1) := by
      nth_rw 2 [← hadd]
      exact hcancel _ _
    have hsub : ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞)) =
        1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
      rw [ENNReal.natCast_sub, Nat.cast_one, one_div,
        ENNReal.sub_mul fun _ _ ↦ ENNReal.inv_ne_top.2 hq0,
        ENNReal.mul_inv_cancel hq0 hqt, one_mul]
    have hpow1 : 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S + 1) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞)) := by
      simp only [one_div]
      rw [pow_succ, ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inl (ENNReal.pow_ne_top hqt))]
    rw [krasnerCount_of_mod_pos hO hb, ite_eq_right hb.ne', Nat.cast_mul, Nat.cast_mul,
      Nat.cast_pow]
    calc ((n : ℝ≥0∞) * ((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) *
            (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - S)) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)))
        = (n : ℝ≥0∞) * (((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) *
            ((Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j - 2 - S) *
              (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j))) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by ring
      _ = (n : ℝ≥0∞) * (((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞))) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by rw [hpow, hpow1]
      _ = (n : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) *
            (((Nat.card 𝓀[K] - 1 : ℕ) : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞))) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by ring
      _ = (n : ℝ≥0∞) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (1 + S) *
            (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞)) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))) := by
          rw [hsub]

/-- Restricting a `tsum` over a set `s` by an `if` guard equals the `tsum` over `{x ∈ s | p x}`. -/
private theorem tsum_ite_subtype {α : Type*} (s : Set α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ≥0∞) :
    (∑' x : s, if p x.1 then f x.1 else 0) = ∑' x : {x ∈ s | p x}, f x.1 := by
  rw [tsum_subtype s (fun x ↦ if p x then f x else 0), tsum_subtype {x ∈ s | p x} f]
  refine tsum_congr fun x ↦ ?_
  by_cases hs : x ∈ s
  · by_cases hp : p x
    · have hmem : x ∈ {x ∈ s | p x} := ⟨hs, hp⟩
      rw [Set.indicator_of_mem hs, Set.indicator_of_mem hmem, ite_eq_left hp]
    · have hnot : x ∉ {x ∈ s | p x} := fun h ↦ hp h.2
      rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hnot, ite_eq_right hp]
  · have hnot : x ∉ {x ∈ s | p x} := fun h ↦ hs h.1
    rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hnot]

/-- **Krasner's discriminant-refined count (`encard` form)**: in a fixed separable closure of `K`,
the number of totally ramified degree-`n` subextensions with wild exponent `j` equals
`krasnerCount K n j`. This holds in both mixed and equal characteristic, and for all `n, j`. -/
theorem encard_totallyRamifiedOfDegree_wildExponent_eq (n j : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}.encard = krasnerCount K n j := by
  by_cases hO : IsOreAdmissible K n j
  · have hn := hO.pos
    let : MeasurableSpace (Fin n → K) := borel _
    have : BorelSpace (Fin n → K) := ⟨rfl⟩
    let B : TopologicalSpace.PositiveCompacts (Fin n → K) :=
      ⟨⟨integerBox K (Fin n), isCompact_integerBox⟩, by
        rw [isOpen_integerBox.interior_eq]
        exact ⟨0, by simp⟩⟩
    set μ : Measure (Fin n → K) := Measure.addHaarMeasure B
    have hμ : μ (integerBox K (Fin n)) = 1 := Measure.addHaarMeasure_self
    have := (countable_totallyRamifiedOfDegree hn (K := K)).to_subtype
    set W : ℝ≥0∞ := 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (n + j) * (1 - 1 / (Nat.card 𝓀[K] : ℝ≥0∞))
    set S : Set (IntermediateField K (SeparableClosure K)) :=
      {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
    have hW0 : W ≠ 0 := by
      have hq : (1 : ℝ≥0∞) < Nat.card 𝓀[K] := by exact_mod_cast Finite.one_lt_card
      refine mul_ne_zero (ENNReal.div_pos one_ne_zero
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))).ne' (tsub_pos_of_lt ?_).ne'
      rwa [one_div, ENNReal.inv_lt_one]
    have hWtop : W ≠ ∞ := by
      have hq : (1 : ℝ≥0∞) ≤ Nat.card 𝓀[K] := by exact_mod_cast Nat.card_pos
      refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      rw [one_div]
      exact ENNReal.inv_le_one.2 (one_le_pow₀ hq)
    have hsum_int :
        ∑' L : totallyRamifiedOfDegree K n,
          ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
          n * μ (eisensteinBox K n j) := by
      rw [← lintegral_tsum fun L ↦ aemeasurable_rootCount_restrict_eisensteinBox μ L.2,
        setLIntegral_congr_fun measurableSet_eisensteinBox
          fun a ha ↦ tsum_rootCount_eq_of_mem_eisensteinBox ha,
        setLIntegral_const]
    have hlhs :
        ∑' L : totallyRamifiedOfDegree K n,
          ∫⁻ a in eisensteinBox K n j, (L.1.rootCount a : ℝ≥0∞) ∂μ =
          S.encard * W := by
      rw [tsum_congr fun L ↦ L.1.lintegral_rootCount_eisensteinBox L.2 μ hμ,
        tsum_ite_subtype (totallyRamifiedOfDegree K n) (·.wildExponent = j) (fun _ ↦ W),
        ENNReal.tsum_set_const]
    have heq : (S.encard : ℝ≥0∞) * W = (krasnerCount K n j : ℝ≥0∞) * W := by
      rw [← hlhs, hsum_int, ← krasnerCount_mul_weight_eq hO μ hμ]
    have hcard : (S.encard : ℝ≥0∞) = (krasnerCount K n j : ℝ≥0∞) :=
      (ENNReal.mul_left_inj hW0 hWtop).1 heq
    exact_mod_cast hcard
  · have hempty : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j} = ∅ :=
      Set.eq_empty_of_forall_notMem fun E ⟨hE, hEj⟩ ↦ hO (hEj ▸ isOreAdmissible_wildExponent hE)
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
    {E ∈ totallyRamifiedOfDegree K n | E.wildExponent ≤ B}.Finite := by
  refine ((Finset.range (B + 1)).finite_toSet.biUnion fun j _ ↦
    finite_totallyRamifiedOfDegree_wildExponent_eq (K := K) n j).subset ?_
  intro E ⟨hE, hle⟩
  exact Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le hle)) ⟨hE, rfl⟩

/-- For every degree `n` and bound `B`, there are only finitely many members of `σ_K(n)` with
discriminant exponent at most `B`, including in equal characteristic. -/
theorem finite_totallyRamifiedOfDegree_discriminantExponent_le (n B : ℕ) :
    {E ∈ totallyRamifiedOfDegree K n | E.discriminantExponent ≤ B}.Finite := by
  refine (finite_totallyRamifiedOfDegree_wildExponent_le (K := K) n B).subset ?_
  intro E ⟨hE, hle⟩
  have := (mem_totallyRamifiedOfDegree_iff.1 hE).2.finite
  have hpos : 0 < Module.finrank K E := Module.finrank_pos
  refine ⟨hE, le_trans ?_ hle⟩
  rw [IntermediateField.wildExponent_def]
  omega

/-- Partitioning a `tsum` over `σ_K(n)` by wild exponent. -/
private theorem tsum_totallyRamifiedOfDegree_eq_tsum_wildExponent (n : ℕ)
    (f : IntermediateField K (SeparableClosure K) → ℝ≥0∞) :
    (∑' E : totallyRamifiedOfDegree K n, f E.1) =
      ∑' j : ℕ, ∑' E : {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}, f E.1 := by
  let S : ℕ → Set (IntermediateField K (SeparableClosure K)) :=
    fun j ↦ {E ∈ totallyRamifiedOfDegree K n | E.wildExponent = j}
  have hU : totallyRamifiedOfDegree K n = ⋃ j : ℕ, S j := by
    ext E
    simp only [Set.mem_iUnion, S, Set.mem_ofPred_eq]
    exact ⟨fun hE ↦ ⟨E.wildExponent, hE, rfl⟩, fun ⟨_, hE, _⟩ ↦ hE⟩
  have hdisj : Set.univ.PairwiseDisjoint S := fun j₁ _ j₂ _ hne ↦
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
  have hlhs :
      (∑' L : totallyRamifiedOfDegree K n, if L.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
        krasnerCount K n j := by
    rw [tsum_ite_subtype (totallyRamifiedOfDegree K n) (·.wildExponent = j) (fun _ ↦ 1),
      ENNReal.tsum_set_one, encard_totallyRamifiedOfDegree_wildExponent_eq, ENat.toENNReal_coe]
  have hrhs :
      (∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
          if M.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
        (n : ℝ≥0∞) * ∑' M : {M ∈ R | M.wildExponent = j}, (1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) := by
    have hcongr :
        (∑' M : R, (n : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M) *
            if M.1.wildExponent = j then (1 : ℝ≥0∞) else 0) =
          ∑' M : R, if M.1.wildExponent = j then
            (n : ℝ≥0∞) * ((1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M)) else 0 :=
      tsum_congr fun M ↦ by split_ifs <;> simp [div_eq_mul_inv]
    rw [hcongr,
      tsum_ite_subtype R (·.wildExponent = j)
        (fun M ↦ (n : ℝ≥0∞) * ((1 : ℝ≥0∞) / Nat.card (M ≃ₐ[K] M))),
      ENNReal.tsum_mul_left]
  rw [← hrhs, ← hreg, hlhs]

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
    have hnot : ¬ IsOreAdmissible K n j := fun hO ↦ by
      have hle := hO.le_mul_natCastValuation hnK
      omega
    rw [krasnerCount_of_not_isOreAdmissible hnot, Nat.cast_zero]
  rw [hsum, ← Nat.cast_sum, ← ENat.toENNReal_coe, ENat.toENNReal_inj] at htsum
  rw [Set.ncard_def, htsum, ENat.toNat_natCast]

/-! ### Explicit closed forms in mixed and equal characteristic -/

/-- `min` commutes with coercion `ℕ → ℕ∞`. -/
private theorem min_natCast_enat (a b : ℕ) :
    min (a : ℕ∞) (b : ℕ∞) = ((min a b : ℕ) : ℕ∞) := by
  rcases le_total a b with h | h <;> simp [h]

/-- Pointwise saving identity: `ν_h + min (m_h - 1, v_K(h)) = m_h`. -/
private theorem oreCoefficientDepth_add_saving (n j h : ℕ) :
    oreCoefficientDepth K n j h +
        (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
          (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
      j / n + 1 + if h < j % n then 1 else 0 := by
  rw [oreCoefficientDepth_def]
  cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
  | top =>
    simp only [ENat.sub_top, ENat.toNat_zero, min_top_right, ENat.toNat_natCast]
    omega
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
  have hsum_add :
      ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
          ∑ h ∈ Finset.Ico 1 n,
            (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
              (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
        ∑ h ∈ Finset.Ico 1 n, (j / n + 1 + if h < j % n then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun h _ ↦ oreCoefficientDepth_add_saving n j h
  have hcard_lt : (Finset.Ico 1 n).filter (· < j % n) = Finset.Ico 1 (j % n) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have := Nat.mod_lt j hn
    omega
  have hsum_m :
      ∑ h ∈ Finset.Ico 1 n, (j / n + 1 + if h < j % n then 1 else 0) =
        (n - 1) * (j / n + 1) + (j % n - 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Finset.sum_boole,
      Nat.cast_id, hcard_lt, Nat.card_Ico]
  have hdiv : n * (j / n) + j % n = j := Nat.div_add_mod j n
  have hmul : (n - 1) * (j / n + 1) + j / n = n * (j / n) + (n - 1) := by
    cases n with
    | zero => omega
    | succ m => simp only [Nat.add_sub_cancel]; ring
  rw [hsum_m] at hsum_add
  have htot :
      ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h +
          (j / n + ∑ h ∈ Finset.Ico 1 n,
            (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞)
              (addVal 𝒪[K] (h : 𝒪[K]))).toNat) =
        n * (j / n) + (n - 1) + (j % n - 1) := by
    linarith
  split_ifs with hb
  · have h1 : n * (j / n) + (n - 1) + (j % n - 1) = n + j - 1 := by omega
    rw [h1] at htot
    rw [← htot, Nat.add_sub_cancel_left]
  · have h1 : n * (j / n) + (n - 1) + (j % n - 1) = n + j - 2 := by omega
    rw [h1] at htot
    rw [← htot, Nat.add_sub_cancel_left]

/-- Number of multiples of `d` in `[1, m)`. -/
private theorem card_Ico_one_filter_dvd (m d : ℕ) (hm : 0 < m) :
    ((Finset.Ico 1 m).filter (d ∣ ·)).card = (m - 1) / d := by
  have hIco : Finset.Ico 1 m = Finset.Ioc 0 (m - 1) := by
    ext h
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hIco, Nat.Ioc_filter_dvd_card_eq_div]

/-- When `d ∣ m` with `0 < m` and `0 < d`, `(m - 1) / d = m / d - 1`. -/
private theorem sub_one_div_of_dvd {m d : ℕ} (hm : 0 < m) (hd : 0 < d) (h : d ∣ m) :
    (m - 1) / d = m / d - 1 := by
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hm
  rw [Nat.mul_div_cancel_left k hd]
  have h1 : d * k - 1 = (d - 1) + d * (k - 1) := by
    cases k with
    | zero => omega
    | succ k' => simp only [Nat.mul_succ, Nat.add_sub_cancel]; omega
  rw [h1, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (by omega : d - 1 < d), zero_add]

/-- When `¬ d ∣ m`, `(m - 1) / d = m / d`. -/
private theorem sub_one_div_of_not_dvd {m d : ℕ} (h : ¬ d ∣ m) : (m - 1) / d = m / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hm : 0 < m := Nat.pos_of_ne_zero fun h0 ↦ h (h0 ▸ dvd_zero d)
  have hmod_lt : m % d < d := Nat.mod_lt m hd
  have hdiv : m - 1 = (m % d - 1) + d * (m / d) := by
    have := Nat.div_add_mod m d
    have : 0 < m % d := Nat.pos_of_ne_zero fun h0 ↦ h (Nat.dvd_of_mod_eq_zero h0)
    omega
  rw [hdiv, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt (by omega : m % d - 1 < d), zero_add]

/-- Ceiling inequality for positive `e`: `i ≤ m * e ↔ (i + e - 1) / e ≤ m`. -/
private theorem le_mul_iff_ceil_div_le {i m e : ℕ} (he : 0 < e) :
    i ≤ m * e ↔ (i + e - 1) / e ≤ m := by
  have he1 : i + e - 1 + 1 = i + e := by omega
  constructor
  · intro h
    have hlt : i + e - 1 < (m + 1) * e := by nlinarith
    have := (Nat.div_lt_iff_lt_mul he).2 hlt
    omega
  · intro h
    have hdiv := Nat.div_add_mod (i + e - 1) e
    have hmod := Nat.mod_lt (i + e - 1) he
    nlinarith

/-- Divisibility characterization of `i ≤ padicValNat p h * e`. -/
private theorem le_padicValNat_mul_iff {p h e i : ℕ} (hp : p.Prime) (hh : 0 < h) (he : 0 < e) :
    i ≤ padicValNat p h * e ↔ p ^ ((i + e - 1) / e) ∣ h := by
  rw [le_mul_iff_ceil_div_le he, Nat.padicValNat_def,
    Nat.pow_dvd_iff_le_multiplicity hp.ne_one hh.ne']

/-- Layer-cake identity for `min`: `min M v = #{i ∈ [1, M] | i ≤ v}`. -/
private theorem min_eq_sum_ite_Icc (M v : ℕ) :
    min M v = ∑ i ∈ Finset.Icc 1 M, if i ≤ v then 1 else 0 := by
  have hfilt : (Finset.Icc 1 M).filter (· ≤ v) = Finset.Icc 1 (min M v) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.card_filter, hfilt, Nat.card_Icc]
  omega

/-- Combined divisor-sum evaluation for the mixed-characteristic exponent. -/
private theorem add_sum_min_padicValNat_mul {n p e a : ℕ} (hn : 0 < n) (hp : p.Prime) (he : 0 < e)
    (ha : a ≤ padicValNat p n * e) :
    a + ∑ h ∈ Finset.Ico 1 n, min a (padicValNat p h * e) =
      ∑ i ∈ Finset.Icc 1 a, n / p ^ ((i + e - 1) / e) := by
  have h1 : ∑ h ∈ Finset.Ico 1 n, min a (padicValNat p h * e) =
      ∑ i ∈ Finset.Icc 1 a, (n / p ^ ((i + e - 1) / e) - 1) := by
    calc ∑ h ∈ Finset.Ico 1 n, min a (padicValNat p h * e)
        = ∑ h ∈ Finset.Ico 1 n, ∑ i ∈ Finset.Icc 1 a,
            if i ≤ padicValNat p h * e then 1 else 0 :=
          Finset.sum_congr rfl fun h _ ↦ min_eq_sum_ite_Icc a _
      _ = ∑ i ∈ Finset.Icc 1 a, ∑ h ∈ Finset.Ico 1 n,
            if i ≤ padicValNat p h * e then 1 else 0 := Finset.sum_comm
      _ = ∑ i ∈ Finset.Icc 1 a, (n / p ^ ((i + e - 1) / e) - 1) := by
          refine Finset.sum_congr rfl fun i hi ↦ ?_
          have hhi := Finset.mem_Icc.1 hi
          have hcongr : (∑ h ∈ Finset.Ico 1 n, if i ≤ padicValNat p h * e then 1 else 0) =
              ((Finset.Ico 1 n).filter (p ^ ((i + e - 1) / e) ∣ ·)).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun h hh ↦ ?_
            simp only [le_padicValNat_mul_iff hp (Finset.mem_Ico.1 hh).1 he]
          rw [hcongr, card_Ico_one_filter_dvd n _ hn]
          have hdvd : p ^ ((i + e - 1) / e) ∣ n :=
            (le_padicValNat_mul_iff hp hn he).1 (le_trans hhi.2 ha)
          exact sub_one_div_of_dvd hn (pow_pos hp.pos _) hdvd
  have ha_eq : a = ∑ _i ∈ Finset.Icc 1 a, 1 := by
    rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, mul_one]
    omega
  rw [h1]
  nth_rw 1 [ha_eq]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hdvd : p ^ ((i + e - 1) / e) ∣ n :=
    (le_padicValNat_mul_iff hp hn he).1 (le_trans (Finset.mem_Icc.1 hi).2 ha)
  have hpos : 0 < n / p ^ ((i + e - 1) / e) :=
    Nat.div_pos (Nat.le_of_dvd hn hdvd) (pow_pos hp.pos _)
  omega

/-- In mixed characteristic (`(ringChar 𝓀[K] : K) ≠ 0`), every positive natural number is nonzero
in `K`. -/
private theorem natCast_ne_zero_of_natCast_ringChar_ne_zero (hp : (ringChar 𝓀[K] : K) ≠ 0)
    {m : ℕ} (hm : 0 < m) : (m : K) ≠ 0 := fun h0 ↦ by
  have hchar := ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hm).1 h0).1
  exact hp (hchar ▸ ringChar.Nat.cast_ringChar (R := K))

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
  set p := ringChar 𝓀[K]
  set e := natCastValuation K p hp
  have hn := hO.pos
  have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have he : 0 < e :=
    Nat.pos_of_ne_zero ((natCastValuation_ne_zero_iff_ringChar_eq K hp_prime hp).2 rfl)
  have hnK : (n : K) ≠ 0 := natCast_ne_zero_of_natCast_ringChar_ne_zero hp hn
  have ha_eq : j / n = padicValNat p n * e := by
    have hvn := (isOreAdmissible_iff_of_mod_eq_zero hn hb).1 hO
    rw [IsDiscreteValuationRing.addVal_natCast K n hnK, Nat.cast_inj,
      natCastValuation_eq_padicValNat_mul K hnK hp] at hvn
    exact hvn
  rw [krasnerCount_of_mod_eq_zero hO hb]
  congr 2
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_left hb] at hexp
  rw [hexp, ← add_sum_min_padicValNat_mul hn hp_prime he ha_eq.le]
  congr 1
  refine Finset.sum_congr rfl fun h hh ↦ ?_
  have hh0 : 0 < h := (Finset.mem_Ico.1 hh).1
  have hhK : (h : K) ≠ 0 := natCast_ne_zero_of_natCast_ringChar_ne_zero hp hh0
  rw [hb, ite_eq_right (Nat.not_lt_zero h), add_zero,
    IsDiscreteValuationRing.addVal_natCast K h hhK, natCastValuation_eq_padicValNat_mul K hhK hp,
    min_natCast_enat, ENat.toNat_natCast]

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
  set p := ringChar 𝓀[K]
  set e := natCastValuation K p hp
  have hn := hO.pos
  have hmod : j % n < n := Nat.mod_lt j hn
  have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have he : 0 < e :=
    Nat.pos_of_ne_zero ((natCastValuation_ne_zero_iff_ringChar_eq K hp_prime hp).2 rfl)
  have hnK : (n : K) ≠ 0 := natCast_ne_zero_of_natCast_ringChar_ne_zero hp hn
  have hbK : ((j % n : ℕ) : K) ≠ 0 := natCast_ne_zero_of_natCast_ringChar_ne_zero hp hb
  have hvb : padicValNat p (j % n) * e ≤ j / n := by
    have h := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).1
    rw [IsDiscreteValuationRing.addVal_natCast K (j % n) hbK, Nat.cast_le,
      natCastValuation_eq_padicValNat_mul K hbK hp] at h
    exact h
  have hvn : j / n + 1 ≤ padicValNat p n * e := by
    have h := ((isOreAdmissible_iff_of_mod_pos hn hb).1 hO).2
    rw [IsDiscreteValuationRing.addVal_natCast K n hnK, ← Nat.cast_add_one, Nat.cast_le,
      natCastValuation_eq_padicValNat_mul K hnK hp] at h
    exact h
  rw [krasnerCount_of_mod_pos hO hb]
  congr 2
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_right hb.ne'] at hexp
  have hpoint (h : ℕ) (hh : h ∈ Finset.Ico 1 n) :
      (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞) (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
        min (j / n) (padicValNat p h * e) +
          if h < j % n ∧ j / n + 1 ≤ padicValNat p h * e then 1 else 0 := by
    have hhK : (h : K) ≠ 0 :=
      natCast_ne_zero_of_natCast_ringChar_ne_zero hp (Finset.mem_Ico.1 hh).1
    have hvh : addVal 𝒪[K] (h : 𝒪[K]) = ((padicValNat p h * e : ℕ) : ℕ∞) := by
      rw [IsDiscreteValuationRing.addVal_natCast K h hhK,
        natCastValuation_eq_padicValNat_mul K hhK hp]
    rw [hvh, min_natCast_enat, ENat.toNat_natCast]
    split_ifs <;> omega
  have hsecond :
      (∑ h ∈ Finset.Ico 1 n, if h < j % n ∧ j / n + 1 ≤ padicValNat p h * e then 1 else 0) =
        (j % n) / p ^ ((j / n + e) / e) := by
    have hfilt :
        (Finset.Ico 1 n).filter (fun h ↦ h < j % n ∧ j / n + 1 ≤ padicValNat p h * e) =
          (Finset.Ico 1 (j % n)).filter (fun h ↦ p ^ ((j / n + e) / e) ∣ h) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, _⟩, hlt, hle⟩
        refine ⟨⟨h1, hlt⟩, ?_⟩
        have := (le_padicValNat_mul_iff hp_prime h1 he).1 hle
        rwa [show j / n + 1 + e - 1 = j / n + e by omega] at this
      · rintro ⟨⟨h1, hlt⟩, hdvd⟩
        refine ⟨⟨h1, lt_trans hlt hmod⟩, hlt, ?_⟩
        rw [le_padicValNat_mul_iff hp_prime h1 he, show j / n + 1 + e - 1 = j / n + e by omega]
        exact hdvd
    rw [← Finset.card_filter, hfilt, card_Ico_one_filter_dvd (j % n) _ hb]
    refine sub_one_div_of_not_dvd fun hdvd ↦ ?_
    have hdvd' : p ^ ((j / n + 1 + e - 1) / e) ∣ j % n := by
      rwa [show j / n + 1 + e - 1 = j / n + e by omega]
    have hle := (le_padicValNat_mul_iff hp_prime hb he).2 hdvd'
    omega
  rw [hexp, Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, ← add_assoc,
    add_sum_min_padicValNat_mul hn hp_prime he (Nat.le_of_succ_le hvn), hsecond]

/-- **Equal-characteristic closed form of Krasner's count**: when `K` has equal characteristic
`p = ringChar 𝓀[K]`, `0 < n`, `p ∣ n`, and `¬ p ∣ j`,
`krasnerCount K n j = n * (q - 1) * q ^ ((j / n) * (n / p) + (j % n) / p)`. -/
theorem krasnerCount_of_natCast_ringChar_eq_zero {n j : ℕ}
    (hp : (ringChar 𝓀[K] : K) = 0) (hn : 0 < n) (hpn : ringChar 𝓀[K] ∣ n)
    (hpj : ¬ ringChar 𝓀[K] ∣ j) :
    krasnerCount K n j =
      n * (Nat.card 𝓀[K] - 1) *
        Nat.card 𝓀[K] ^ ((j / n) * (n / ringChar 𝓀[K]) + (j % n) / ringChar 𝓀[K]) := by
  set p := ringChar 𝓀[K]
  have hp_prime : p.Prime := CharP.char_is_prime 𝓀[K] _
  have hchar : ringChar K = p :=
    ((natCast_eq_zero_iff_ringChar_eq_ringChar_residueField_and_dvd hp_prime.pos).1 hp).1
  have hcast_zero (m : ℕ) : (m : K) = 0 ↔ p ∣ m := by
    rw [← hchar, ringChar.spec K m]
  have hnK : (n : K) = 0 := (hcast_zero n).2 hpn
  have hO : IsOreAdmissible K n j := (isOreAdmissible_iff_of_natCast_eq_zero hn hnK).2 hpj
  have hpb : ¬ p ∣ j % n := fun h ↦ hpj <| by
    have hdiv := Nat.div_add_mod j n
    rw [← hdiv]
    exact dvd_add (dvd_mul_of_dvd_left hpn _) h
  have hb : 0 < j % n := Nat.pos_of_ne_zero fun h0 ↦ hpb (h0 ▸ dvd_zero p)
  have hmod : j % n < n := Nat.mod_lt j hn
  rw [krasnerCount_of_mod_pos hO hb]
  congr 2
  have hexp := exponent_eq_add_sum_saving (K := K) (j := j) hn
  rw [ite_eq_right hb.ne'] at hexp
  have hpoint (h : ℕ) :
      (min ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞) (addVal 𝒪[K] (h : 𝒪[K]))).toNat =
        (if p ∣ h then j / n else 0) + (if h < j % n ∧ p ∣ h then 1 else 0) := by
    by_cases hph : p ∣ h
    · have hhK : (h : K) = 0 := (hcast_zero h).2 hph
      have hh𝒪 : (h : 𝒪[K]) = 0 := Subtype.ext (by simpa using hhK)
      rw [hh𝒪, addVal_zero, min_top_right, ENat.toNat_natCast]
      split_ifs <;> omega
    · have hhK : (h : K) ≠ 0 := mt (hcast_zero h).1 hph
      have hv0 : natCastValuation K h hhK = 0 :=
        (natCastValuation_eq_zero_iff_not_dvd K h hhK).2 hph
      rw [IsDiscreteValuationRing.addVal_natCast K h hhK, hv0, min_natCast_enat, Nat.min_zero,
        ENat.toNat_natCast]
      split_ifs <;> omega
  have hsum1 :
      (∑ h ∈ Finset.Ico 1 n, if p ∣ h then j / n else 0) = (j / n) * (n / p - 1) := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm,
      card_Ico_one_filter_dvd n p hn, sub_one_div_of_dvd hn hp_prime.pos hpn]
  have hsum2 :
      (∑ h ∈ Finset.Ico 1 n, if h < j % n ∧ p ∣ h then 1 else 0) = (j % n) / p := by
    have hfilt : (Finset.Ico 1 n).filter (fun h ↦ h < j % n ∧ p ∣ h) =
        (Finset.Ico 1 (j % n)).filter (fun h ↦ p ∣ h) := by
      ext h
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [← Finset.card_filter, hfilt, card_Ico_one_filter_dvd (j % n) p hb,
      sub_one_div_of_not_dvd hpb]
  have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp_prime.pos
  rw [hexp, Finset.sum_congr rfl fun h _ ↦ hpoint h, Finset.sum_add_distrib, hsum1, hsum2]
  have hmul_sub : j / n + (j / n) * (n / p - 1) = (j / n) * (n / p) := by
    cases hq : n / p with
    | zero => omega
    | succ k => simp only [Nat.add_sub_cancel, Nat.mul_succ]; omega
  omega

end TauCeti

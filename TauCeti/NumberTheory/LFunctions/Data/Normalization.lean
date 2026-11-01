/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Data.Basic
import TauCeti.NumberTheory.LSeries.Twist

/-!
# Arithmetic and analytic normalizations of completed L-functions

An L-function attached to arithmetic data of weight `w` (a modular form of weight `k` has
`w = k - 1`) is usually written in its *arithmetic normalization*: the coefficients are
algebraic, the Dirichlet series converges on `Re s > 1 + w/2`, and the completed function
`Λ_ar(s) = N^(s/2) γ_ar(s) L_ar(s)` satisfies a functional equation reflecting `s ↦ w + 1 - s`.
The *analytic normalization* of `TauCeti.LFunctions.AnalyticLFunctionData` instead centres the
functional equation at `1/2`. The two are related by the substitution `s ↦ s + w/2`:
```
a_an(n) = a_ar(n) / n^(w/2),   μ_an = μ_ar + w/2,   ν_an = ν_ar + w/2,
Λ_an(s) = N^(-w/4) Λ_ar(s + w/2),   ord_p Λ_an = ord_(p + w/2) Λ_ar,
```
with the same conductor and root number. The constant `N^(-w/4)` is forced: it is what makes
`Λ_an(s) = N^(s/2) γ_an(s) L_an(s)` when `Λ_ar(s) = N^(s/2) γ_ar(s) L_ar(s)`.

This file defines `TauCeti.LFunctions.ArithmeticLFunctionData`, the completed-function record
with its unused zeroth coefficient fixed to `0`, and `TauCeti.LFunctions.NormalizationTranslation`,
a pair of an arithmetic card and an analytic card of a given weight related by the formulas
above. Every field of the analytic card is pinned by the arithmetic card and the weight, so a
translation exists and is unique (`NormalizationTranslation.existsUnique`); the weight-zero
translation is the identity (`NormalizationTranslation.analytic_eq_of_weight_zero`). The
translation preserves the degree, shifts the gamma factor, commutes with duality, and
translates each of the three basic properties of a card: agreement with the Dirichlet series
on `Re s > 1 + w/2`, meromorphic continuation with exact poles, and the functional equation
`Λ_ar(s) = ε conj Λ_ar(w + 1 - conj s)` together with the symmetry of the polar divisor under
`s ↦ w + 1 - conj s` (`NormalizationTranslation.hasFunctionalEquation_iff`).

The symmetry of the polar divisor is not implied by the other two clauses of the functional
equation: the weight-zero card with completed function `0` and a single pole at `0` has a unit
root number and satisfies the value equation off the polar loci, but has no functional
equation. This is checked at the end of the file.

## Main definitions

* `TauCeti.LFunctions.ArithmeticLFunctionData`: a card with zeroth coefficient `0`.
* `ArithmeticLFunctionData.dual`: its dual card.
* `TauCeti.LFunctions.NormalizationTranslation`: the translation of weight `w`.
* `NormalizationTranslation.of`: the translation of a given arithmetic card and weight.
* `NormalizationTranslation.dual`: the dual translation.

## Main results

* `NormalizationTranslation.ext`, `NormalizationTranslation.existsUnique`: a translation is
  determined by its arithmetic card and its weight, and one exists for each.
* `NormalizationTranslation.analytic_degree`, `analytic_gammaFactor`, `LSeries_analytic_coeff`.
* `NormalizationTranslation.hasDirichletAgreement_iff`, `hasMeromorphicContinuation_iff`,
  `hasFunctionalEquation_iff`: the three properties in the two normalizations.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1, where the analytic normalization `Λ(s) = ε conj Λ(1 - conj s)` is fixed and the
  arithmetic normalization of the L-function of a weight-`k` form is shifted by `(k - 1)/2`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.LFunctions

/-- **Completed L-function data in an arithmetic normalization.** An `AnalyticLFunctionData`
record whose zeroth coefficient, which `LSeries` never reads, is fixed to be `0`. The record
does not store a weight: the weight `w` enters through `NormalizationTranslation`, which
relates the card to its analytic normalization, whose functional equation reflects
`s ↦ 1 - s` where the arithmetic one reflects `s ↦ w + 1 - s`. -/
structure ArithmeticLFunctionData extends AnalyticLFunctionData where
  /-- The coefficient at `0` is `0`. -/
  coeff_zero : toAnalyticLFunctionData.coeff 0 = 0

namespace ArithmeticLFunctionData

attribute [simp] coeff_zero

theorem toAnalyticLFunctionData_injective :
    Function.Injective toAnalyticLFunctionData := by
  rintro ⟨d, _⟩ ⟨d', _⟩ (rfl : d = d')
  rfl

@[ext]
theorem ext {a b : ArithmeticLFunctionData}
    (h : a.toAnalyticLFunctionData = b.toAnalyticLFunctionData) : a = b :=
  toAnalyticLFunctionData_injective h

/-- The **dual** of an arithmetic card: the dual of the underlying card, whose zeroth
coefficient `conj 0 = 0` is again `0`. -/
noncomputable def dual (a : ArithmeticLFunctionData) : ArithmeticLFunctionData where
  toAnalyticLFunctionData := a.toAnalyticLFunctionData.dual
  coeff_zero := by simp

@[simp]
theorem toAnalyticLFunctionData_dual (a : ArithmeticLFunctionData) :
    a.dual.toAnalyticLFunctionData = a.toAnalyticLFunctionData.dual := (rfl)

/-- Taking the dual of an arithmetic card is involutive. -/
@[simp]
theorem dual_dual (a : ArithmeticLFunctionData) : a.dual.dual = a := by
  ext1
  simp

end ArithmeticLFunctionData

/-- **The translation from the arithmetic normalization of weight `w` to the analytic
normalization.** An arithmetic card `arithmetic`, an analytic card `analytic` and an integer
weight `w`, related by
```
a_an(n) = a_ar(n) / n^(w/2) (n ≠ 0),   a_an(0) = 0,   N_an = N_ar,   ε_an = ε_ar,
μ_an = μ_ar + w/2,   ν_an = ν_ar + w/2,
Λ_an(s) = N^(-w/4) Λ_ar(s + w/2),   ord_an(p) = ord_ar(p + w/2).
```
These laws determine the analytic card (`NormalizationTranslation.ext`), and
`NormalizationTranslation.of` constructs it. -/
structure NormalizationTranslation where
  /-- The card in the arithmetic normalization. -/
  arithmetic : ArithmeticLFunctionData
  /-- The card in the analytic normalization. -/
  analytic : AnalyticLFunctionData
  /-- The arithmetic weight `w`: the arithmetic functional equation reflects `s ↦ w + 1 - s`. -/
  weight : ℤ
  coeff_eq : ∀ n : ℕ, n ≠ 0 →
    analytic.coeff n = arithmetic.coeff n / (n : ℂ) ^ ((weight : ℂ) / 2)
  analytic_coeff_zero : analytic.coeff 0 = 0
  conductor_eq : analytic.conductor = arithmetic.conductor
  gammaR_eq : analytic.gammaR = arithmetic.gammaR.map (· + (weight : ℂ) / 2)
  gammaC_eq : analytic.gammaC = arithmetic.gammaC.map (· + (weight : ℂ) / 2)
  rootNumber_eq : analytic.rootNumber = arithmetic.rootNumber
  completed_eq : ∀ s : ℂ, analytic.completed s =
    ((arithmetic.conductor : ℕ) : ℂ) ^ (-(weight : ℂ) / 4) *
      arithmetic.completed (s + (weight : ℂ) / 2)
  polarOrder_eq : ∀ p : ℂ, analytic.polarOrder p = arithmetic.polarOrder (p + (weight : ℂ) / 2)

namespace NormalizationTranslation

attribute [simp] conductor_eq gammaR_eq gammaC_eq rootNumber_eq polarOrder_eq

variable (T : NormalizationTranslation)

private theorem conj_weight_div_two (w : ℤ) : conj ((w : ℂ) / 2) = (w : ℂ) / 2 := by
  rw [map_div₀, map_intCast, map_ofNat]

private theorem conductor_cpow_ne_zero (N : ℕ+) (z : ℂ) : ((N : ℕ) : ℂ) ^ z ≠ 0 :=
  cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast N.ne_zero))

/-- The coefficient translation holds at every index, `0` included, since both zeroth
coefficients vanish. -/
@[simp]
theorem analytic_coeff (n : ℕ) :
    T.analytic.coeff n = T.arithmetic.coeff n / (n : ℂ) ^ ((T.weight : ℂ) / 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [T.analytic_coeff_zero]
  · exact T.coeff_eq n hn

theorem analytic_coeff_one : T.analytic.coeff 1 = T.arithmetic.coeff 1 := by
  simp

/-- The analytic Dirichlet series is the arithmetic one shifted by `w/2`. -/
theorem LSeries_analytic_coeff (s : ℂ) :
    LSeries T.analytic.coeff s = LSeries T.arithmetic.coeff (s + (T.weight : ℂ) / 2) := by
  have hc : T.analytic.coeff = fun n ↦ T.arithmetic.coeff n * (n : ℂ) ^ (-((T.weight : ℂ) / 2)) :=
    funext fun n ↦ by rw [T.analytic_coeff, cpow_neg, div_eq_mul_inv]
  rw [hc, TauCeti.LSeries.LSeries_mul_natCast_cpow_neg]

/-- The analytic completed function is `N^(-w/4)` times the arithmetic one shifted by `w/2`. -/
theorem analytic_completed :
    T.analytic.completed = ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4) •
      (T.arithmetic.completed ∘ (· + (T.weight : ℂ) / 2)) :=
  funext T.completed_eq

@[simp]
theorem analytic_degree : T.analytic.degree = T.arithmetic.degree := by
  simp [AnalyticLFunctionData.degree_def]

/-- The analytic gamma factor is the arithmetic one shifted by `w/2`. -/
@[simp]
theorem analytic_gammaFactor (s : ℂ) :
    T.analytic.gammaFactor s = T.arithmetic.gammaFactor (s + (T.weight : ℂ) / 2) := by
  simp [AnalyticLFunctionData.gammaFactor_def, Multiset.map_map,
    ← add_assoc, add_right_comm _ ((T.weight : ℂ) / 2)]

/-- **A translation is determined by its arithmetic card and its weight.** -/
@[ext]
theorem ext {T T' : NormalizationTranslation} (h : T.arithmetic = T'.arithmetic)
    (hw : T.weight = T'.weight) : T = T' := by
  have hd : T.analytic = T'.analytic := by
    ext n
    · rw [T.analytic_coeff, T'.analytic_coeff, h, hw]
    · rw [T.conductor_eq, T'.conductor_eq, h]
    · rw [T.gammaR_eq, T'.gammaR_eq, h, hw]
    · rw [T.gammaC_eq, T'.gammaC_eq, h, hw]
    · rw [T.rootNumber_eq, T'.rootNumber_eq, h]
    · rw [T.completed_eq, T'.completed_eq, h, hw]
    · rw [T.polarOrder_eq, T'.polarOrder_eq, h, hw]
  cases T
  cases T'
  simp only at h hw hd
  subst h hw hd
  rfl

/-- **The translation of an arithmetic card of weight `w`.** Its analytic card has
coefficients `a(n) / n^(w/2)`, the same conductor and root number, gamma shifts moved by
`+w/2`, completed function `N^(-w/4) Λ(s + w/2)` and polar divisor moved by `-w/2`. -/
noncomputable def of (a : ArithmeticLFunctionData) (w : ℤ) : NormalizationTranslation where
  arithmetic := a
  analytic :=
    { coeff n := a.coeff n / (n : ℂ) ^ ((w : ℂ) / 2)
      conductor := a.conductor
      gammaR := a.gammaR.map (· + (w : ℂ) / 2)
      gammaC := a.gammaC.map (· + (w : ℂ) / 2)
      rootNumber := a.rootNumber
      completed s := ((a.conductor : ℕ) : ℂ) ^ (-(w : ℂ) / 4) * a.completed (s + (w : ℂ) / 2)
      polarOrder := a.polarOrder.equivMapDomain (Equiv.subRight ((w : ℂ) / 2)) }
  weight := w
  coeff_eq _ _ := (rfl)
  analytic_coeff_zero := by simp
  conductor_eq := (rfl)
  gammaR_eq := (rfl)
  gammaC_eq := (rfl)
  rootNumber_eq := (rfl)
  completed_eq _ := (rfl)
  polarOrder_eq _ := by simp [Finsupp.equivMapDomain_apply]

@[simp]
theorem of_arithmetic (a : ArithmeticLFunctionData) (w : ℤ) : (of a w).arithmetic = a := (rfl)

@[simp]
theorem of_weight (a : ArithmeticLFunctionData) (w : ℤ) : (of a w).weight = w := (rfl)

/-- Every translation is the one constructed by `NormalizationTranslation.of`. -/
theorem of_arithmetic_weight : of T.arithmetic T.weight = T :=
  ext (of_arithmetic _ _) (of_weight _ _)

/-- **Existence and uniqueness of the translation** of an arithmetic card at a given weight. -/
theorem existsUnique (a : ArithmeticLFunctionData) (w : ℤ) :
    ∃! T : NormalizationTranslation, T.arithmetic = a ∧ T.weight = w :=
  ⟨of a w, ⟨of_arithmetic a w, of_weight a w⟩, fun _ h ↦ ext (h.1.trans (of_arithmetic a w).symm)
    (h.2.trans (of_weight a w).symm)⟩

/-- **The weight-zero translation is the identity**, as an equality of cards: both zeroth
coefficients are `0`. -/
theorem analytic_eq_of_weight_zero (h : T.weight = 0) :
    T.analytic = T.arithmetic.toAnalyticLFunctionData := by
  ext n
  · simp [h]
  · exact T.conductor_eq
  · simp [h]
  · simp [h]
  · exact T.rootNumber_eq
  · simp [T.completed_eq, h]
  · simp [T.polarOrder_eq, h]

/-- **The dual translation**, from the dual arithmetic card to the dual analytic card, at the
same weight. The shift `w/2` and the conductor power `N^(-w/4)` are real, so they commute with
conjugation. -/
noncomputable def dual : NormalizationTranslation where
  arithmetic := T.arithmetic.dual
  analytic := T.analytic.dual
  weight := T.weight
  coeff_eq n hn := by
    have hpow := TauCeti.ofReal_cpow_conj (n.cast_nonneg : (0 : ℝ) ≤ n) ((T.weight : ℂ) / 2)
    rw [ofReal_natCast, conj_weight_div_two] at hpow
    simp [map_div₀, ← hpow]
  analytic_coeff_zero := by simp
  conductor_eq := by simp
  gammaR_eq := by
    simp [Multiset.map_map, map_ofNat]
  gammaC_eq := by
    simp [Multiset.map_map, map_ofNat]
  rootNumber_eq := by simp
  completed_eq s := by
    have hpow := TauCeti.ofReal_cpow_conj ((T.arithmetic.conductor : ℕ).cast_nonneg : (0 : ℝ) ≤ _)
      (-(T.weight : ℂ) / 4)
    rw [ofReal_natCast] at hpow
    have hw : conj (-(T.weight : ℂ) / 4) = -(T.weight : ℂ) / 4 := by
      rw [map_div₀, map_neg, map_intCast, map_ofNat]
    rw [hw] at hpow
    simp [AnalyticLFunctionData.dual_completed_apply, T.completed_eq, ← hpow, map_ofNat]
  polarOrder_eq p := by simp [T.polarOrder_eq, map_ofNat]

@[simp]
theorem dual_arithmetic : T.dual.arithmetic = T.arithmetic.dual := (rfl)

@[simp]
theorem dual_analytic : T.dual.analytic = T.analytic.dual := (rfl)

@[simp]
theorem dual_weight : T.dual.weight = T.weight := (rfl)

/-- Taking the dual translation is involutive. -/
@[simp]
theorem dual_dual : T.dual.dual = T :=
  ext (by simp) (by simp)

/-- **Dirichlet agreement in the two normalizations.** The analytic card agrees with its
Dirichlet series on `Re s > 1` exactly when the arithmetic card has first coefficient `1`,
positive degree, and agrees with its Dirichlet series on `Re s > 1 + w/2`. -/
theorem hasDirichletAgreement_iff :
    T.analytic.HasDirichletAgreement ↔
      T.arithmetic.coeff 1 = 1 ∧ 0 < T.arithmetic.degree ∧
        ∀ s : ℂ, 1 + (T.weight : ℝ) / 2 < s.re →
          T.arithmetic.completed s = ((T.arithmetic.conductor : ℕ) : ℂ) ^ (s / 2) *
            T.arithmetic.gammaFactor s * LSeries T.arithmetic.coeff s := by
  set d : ℂ := (T.weight : ℂ) / 2
  set N : ℂ := ((T.arithmetic.conductor : ℕ) : ℂ)
  have hc : N ^ (-(T.weight : ℂ) / 4) ≠ 0 := conductor_cpow_ne_zero _ _
  have hN : N ≠ 0 := by simp [N]
  have hre (s : ℂ) : (s + d).re = s.re + (T.weight : ℝ) / 2 := by simp [d]
  -- the completed equations at `s` and at `s + w/2` differ by the factor `N^(-w/4)`
  have hval (s : ℂ) :
      T.analytic.completed s = ((T.analytic.conductor : ℕ) : ℂ) ^ (s / 2) *
          T.analytic.gammaFactor s * LSeries T.analytic.coeff s ↔
        T.arithmetic.completed (s + d) = N ^ ((s + d) / 2) *
          T.arithmetic.gammaFactor (s + d) * LSeries T.arithmetic.coeff (s + d) := by
    have hpow : N ^ ((s + d) / 2) * N ^ (-(T.weight : ℂ) / 4) = N ^ (s / 2) := by
      rw [← cpow_add _ _ hN]
      congr 1
      simp only [d]
      ring
    rw [T.completed_eq, T.conductor_eq, T.analytic_gammaFactor, T.LSeries_analytic_coeff, ← hpow]
    constructor
    · intro h
      refine mul_left_cancel₀ hc ?_
      rw [h]
      ring
    · intro h
      rw [h]
      ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, by simpa using h2, fun t ht ↦ ?_⟩
    have hlt : 1 < (t - d).re := by
      have := hre (t - d)
      rw [sub_add_cancel] at this
      linarith
    have := (hval (t - d)).1 (h3 _ hlt)
    rwa [sub_add_cancel] at this
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using h1, by simpa using h2, fun s hs ↦ (hval s).2 (h3 _ (by
      rw [hre]; linarith))⟩

/-- **Meromorphic continuation in the two normalizations.** The analytic card is
meromorphically continued with exact poles exactly when the arithmetic card is: the two
completed functions differ by a nonzero constant and the translation by `w/2`, which also
moves the polar divisor. -/
theorem hasMeromorphicContinuation_iff :
    T.analytic.HasMeromorphicContinuation ↔
      T.arithmetic.HasMeromorphicContinuation := by
  set d : ℂ := (T.weight : ℂ) / 2
  set c : ℂ := ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4)
  have hc : c ≠ 0 := conductor_cpow_ne_zero _ _
  have hmer : Meromorphic T.analytic.completed ↔ Meromorphic T.arithmetic.completed := by
    rw [T.analytic_completed, meromorphic_const_smul_iff_meromorphic hc,
      Meromorphic.meromorphic_comp_add_const_iff_meromorphic]
  have hord (p : ℂ) : meromorphicOrderAt T.analytic.completed p =
      meromorphicOrderAt T.arithmetic.completed (p + d) := by
    rw [T.analytic_completed, meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hc,
      meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  have han (p : ℂ) : AnalyticAt ℂ T.analytic.completed p ↔
      AnalyticAt ℂ T.arithmetic.completed (p + d) := by
    rw [funext T.completed_eq]
    refine ⟨fun h ↦ ?_, fun h ↦ analyticAt_const.mul (h.comp_of_eq (by fun_prop) rfl)⟩
    have h' := (analyticAt_const (v := c⁻¹)).mul
      (h.comp_of_eq (f := fun z ↦ z - d) (by fun_prop) (add_sub_cancel_right p d))
    exact h'.congr (Filter.Eventually.of_forall fun z ↦ by simp [c, hc, d])
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hmer.1 h1, fun q hq ↦ ?_, fun q hq ↦ ?_⟩
    · have := h2 (q - d) (by rwa [T.polarOrder_eq, sub_add_cancel])
      rwa [hord, T.polarOrder_eq, sub_add_cancel] at this
    · simpa using (han (q - d)).1 (h3 _ (by rwa [T.polarOrder_eq, sub_add_cancel]))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hmer.2 h1, fun p hp ↦ ?_, fun p hp ↦ ?_⟩
    · rw [T.polarOrder_eq] at hp ⊢
      rw [hord]
      exact h2 _ hp
    · rw [T.polarOrder_eq] at hp
      exact (han p).2 (h3 _ hp)

/-- **The functional equation in the two normalizations.** The analytic card has its
functional equation `Λ_an(s) = ε conj Λ_an(1 - conj s)` exactly when the arithmetic card has a
unit root number, a polar divisor symmetric under `s ↦ w + 1 - conj s`, and the functional
equation `Λ_ar(s) = ε conj Λ_ar(w + 1 - conj s)` at every `s` at which neither `s` nor
`w + 1 - conj s` is a pole. The symmetry of the polar divisor is a separate clause: it is not
implied by the other two. -/
theorem hasFunctionalEquation_iff :
    T.analytic.HasFunctionalEquation ↔
      ‖T.arithmetic.rootNumber‖ = 1 ∧
        (∀ s : ℂ, T.arithmetic.polarOrder ((T.weight : ℂ) + 1 - conj s) =
          T.arithmetic.polarOrder s) ∧
        ∀ s : ℂ, T.arithmetic.polarOrder s = 0 →
          T.arithmetic.polarOrder ((T.weight : ℂ) + 1 - conj s) = 0 →
            T.arithmetic.completed s =
              T.arithmetic.rootNumber * T.arithmetic.dual.completed ((T.weight : ℂ) + 1 - s) := by
  set d : ℂ := (T.weight : ℂ) / 2
  set c : ℂ := ((T.arithmetic.conductor : ℕ) : ℂ) ^ (-(T.weight : ℂ) / 4)
  have hc : c ≠ 0 := conductor_cpow_ne_zero _ _
  -- the analytic reflection `s ↦ 1 - conj s` is the arithmetic one read at `s + w/2`
  have hrefl (s : ℂ) : 1 - conj s + d = (T.weight : ℂ) + 1 - conj (s + d) := by
    rw [map_add, conj_weight_div_two]
    simp only [d]
    ring
  have hdual (s : ℂ) : T.analytic.dual.completed (1 - s) =
      c * T.arithmetic.dual.completed ((T.weight : ℂ) + 1 - (s + d)) := by
    rw [← dual_analytic, T.dual.completed_eq, dual_arithmetic,
      ArithmeticLFunctionData.toAnalyticLFunctionData_dual, AnalyticLFunctionData.dual_conductor,
      dual_weight]
    congr 2
    simp only [d]
    ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by rwa [T.rootNumber_eq] at h1, fun t ↦ ?_, fun t ht ht' ↦ ?_⟩
    · have := h2 (t - d)
      rwa [T.polarOrder_eq, T.polarOrder_eq, hrefl, sub_add_cancel] at this
    · have := h3 (t - d) (by rwa [T.polarOrder_eq, sub_add_cancel])
        (by rwa [T.polarOrder_eq, hrefl, sub_add_cancel])
      rw [T.completed_eq, hdual, sub_add_cancel, T.rootNumber_eq, mul_left_comm] at this
      exact mul_left_cancel₀ hc this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by rwa [T.rootNumber_eq], fun s ↦ ?_, fun s hs hs' ↦ ?_⟩
    · rw [T.polarOrder_eq, T.polarOrder_eq, hrefl]
      exact h2 _
    · rw [T.polarOrder_eq] at hs
      rw [T.polarOrder_eq, hrefl] at hs'
      rw [T.completed_eq, h3 _ hs hs', hdual, T.rootNumber_eq, mul_left_comm]

end NormalizationTranslation

/-! ### Checks -/

/-- The discriminant form `Δ` of weight `12` has arithmetic weight `11` and the single complex
gamma shift `0` in its arithmetic normalization; its analytic normalization has the complex
gamma shift `11/2`, not `-11/2`. -/
example (T : NormalizationTranslation) (hw : T.weight = 11) (hR : T.arithmetic.gammaR = 0)
    (hC : T.arithmetic.gammaC = {0}) :
    T.analytic.gammaR = 0 ∧ T.analytic.gammaC = {11 / 2} ∧ T.analytic.degree = 2 := by
  simp [AnalyticLFunctionData.degree_def, hw, hR, hC]

/-- A malformed weight-zero card, with completed function `0` and a single pole at `0`, has a
unit root number and satisfies the value equation off the polar loci, but its polar divisor is
not symmetric, so it has no functional equation. -/
example : ∃ T : NormalizationTranslation, T.weight = 0 ∧ ‖T.arithmetic.rootNumber‖ = 1 ∧
    (∀ s : ℂ, T.arithmetic.polarOrder s = 0 → T.arithmetic.polarOrder (1 - conj s) = 0 →
      T.arithmetic.completed s = T.arithmetic.rootNumber * T.arithmetic.dual.completed (1 - s)) ∧
    ¬ T.analytic.HasFunctionalEquation := by
  let a : ArithmeticLFunctionData :=
    { coeff := 0
      conductor := 1
      gammaR := 0
      gammaC := 0
      rootNumber := 1
      completed := 0
      polarOrder := Finsupp.single 0 1
      coeff_zero := rfl }
  refine ⟨NormalizationTranslation.of a 0, rfl, by simp [a], fun s _ _ ↦ by simp [a], ?_⟩
  rw [NormalizationTranslation.hasFunctionalEquation_iff]
  rintro ⟨-, h, -⟩
  simpa [a] using h 0

end TauCeti.LFunctions

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClass

import TauCeti.GroupTheory.Index.Map
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# Direct calculation of the quadratic norm index across all defect cases

Let `K` be a nonarchimedean local field with `2 ≠ 0`. For `a : Kˣ`, applying
`Subgroup.index_map_mul_relIndex_ker` to `normalizedValuation K : Kˣ →* Multiplicative ℤ`
(whose kernel is `U(K, 0)`) factors the index of `quadraticNormSubgroup (a : K)` as

`[(Multiplicative ℤ) : v_K(N)] · [U(K, 0) : N ∩ U(K, 0)] = [Kˣ : N]`

(`TauCeti.index_map_normalizedValuation_mul_relIndex_quadraticNormSubgroup_unitFiltration_zero`).
All three regimes of the quadratic defect are evaluated directly in the base field `K`, without
forming a local-field norm or square-class count on the quadratic extension `K(√a)`:

1. **Split radicands (`IsSquare a`)**: `N = ⊤`, `v_K(N) = ⊤`, and `U(K, 0) ≤ N`, giving
   `1 · 1 = 1`.
2. **Even finite defect (`defectExponent a = d`, `Even d`)**: `N` consists of the units of `K` of
   even normalized valuation (`TauCeti.mem_quadraticNormSubgroup_iff_even_of_even_defectExponent`),
   so `[Kˣ : N] = 2` (`TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`) while
   `U(K, 0) ≤ N` gives unit index `1`, hence valuation index `2` (`2 · 1 = 2`).
3. **Odd finite defect (`defectExponent a = d`, `Odd d`)**: this covers both odd-valuation
   radicands (where square rescaling makes `a` a uniformizer, whose unit norms are counted by
   `TauCeti.uniformizerNormSquareClass`) and even-valuation radicands of odd unit defect (where
   square rescaling makes `a` a unit of odd defect, whose unit norms have the Eisenstein form
   `u² (1 - t v + c v²)`). In both subcases `v_K(N) = ⊤` has index `1`, while
   `unitQuadraticNormSquareClasses (a : K)` has `#𝓀[K] ^ v_K(2)` elements inside the
   `2 · #𝓀[K] ^ v_K(2)` classes of `unitSquareClasses K`, giving unit index `2` and total index
   `1 · 2 = 2` (`TauCeti.quadraticNormSubgroup_index_eq_two_of_odd_defectExponent`).

Consequently `(quadraticNormSubgroup (a : K)).index = 2 ↔ ¬IsSquare a`
(`TauCeti.quadraticNormSubgroup_index_eq_two_iff`), and the valuation-index and unit-index factors
each equal `2` exclusively in the unramified (even-defect) and ramified (odd-defect) cases
(`TauCeti.index_map_normalizedValuation_quadraticNormSubgroup_eq_two_iff`,
`TauCeti.relIndex_quadraticNormSubgroup_unitFiltration_zero_eq_two_iff`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, especially 63:11–63:13.
* J.-P. Serre, *Local Fields*, Chapter V, §3.
-/

public noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Valuation-and-unit index factorization -/

/-- Under `normalizedValuation K : Kˣ →* Multiplicative ℤ`, the index of `quadraticNormSubgroup a`
factors into the index of its valuation image and its relative index inside `U(K, 0)`. -/
theorem index_map_normalizedValuation_mul_relIndex_quadraticNormSubgroup_unitFiltration_zero
    (a : K) :
    ((quadraticNormSubgroup a).map (normalizedValuation K)).index *
        (quadraticNormSubgroup a).relIndex (unitFiltration K 0) =
      (quadraticNormSubgroup a).index := by
  have h := (quadraticNormSubgroup a).index_map_mul_relIndex_ker (normalizedValuation K)
    (normalizedValuation_surjective (K := K))
  rwa [ker_normalizedValuation] at h

/-! ### Valuation image of the quadratic norm subgroup -/

/-- When `2 ≠ 0` and `a : Kˣ` is a square, `quadraticNormSubgroup (a : K)` maps onto
`Multiplicative ℤ` under `normalizedValuation K`. -/
theorem map_normalizedValuation_quadraticNormSubgroup_eq_top_of_isSquare (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : IsSquare a) :
    (quadraticNormSubgroup (a : K)).map (normalizedValuation K) = ⊤ := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rw [quadraticNormSubgroup_eq_top_of_isSquare ha]
  exact Subgroup.map_top_of_surjective _ (normalizedValuation_surjective (K := K))

/-- If `a : Kˣ` has odd quadratic defect exponent `d`, every integer valuation is attained by a
norm from `K(√a)`, so `quadraticNormSubgroup (a : K)` maps onto `Multiplicative ℤ`. -/
theorem map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).map (normalizedValuation K) = ⊤ := by
  rw [eq_top_iff]
  intro n _
  obtain ⟨b, hb, hbv⟩ :=
    exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_of_odd_defectExponent
      hd hodd n.toAdd
  exact ⟨b, hb, Multiplicative.toAdd.injective hbv⟩

/-- If `a : Kˣ` has odd quadratic defect exponent, the valuation image of
`quadraticNormSubgroup (a : K)` has index `1`. -/
theorem index_map_normalizedValuation_quadraticNormSubgroup_of_odd_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    ((quadraticNormSubgroup (a : K)).map (normalizedValuation K)).index = 1 := by
  rw [map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent hd hodd,
    Subgroup.index_top]

/-- For `a : Kˣ` of even finite defect exponent `d`, `quadraticNormSubgroup (a : K)` consists
precisely of the elements of `Kˣ` of even normalized valuation. -/
theorem mem_quadraticNormSubgroup_iff_even_of_even_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) (b : Kˣ) :
    b ∈ quadraticNormSubgroup (a : K) ↔ Even (normalizedValuation K b).toAdd :=
  mem_quadraticNormSubgroup_iff_even_of_unramified_class
    ((unramified_class_iff_even_defectExponent h2 hd).mpr hev) b

/-! ### Unit-norm square classes and unit-norm relative index -/

/-- For `a : Kˣ` of even finite defect exponent, every unit in `U(K, 0)` is a quadratic norm. -/
theorem unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) := by
  intro b hb
  have hbv : (normalizedValuation K b).toAdd = 0 :=
    toAdd_eq_zero.mpr ((normalizedValuation_eq_one_iff b).mpr ((mem_unitFiltration_zero b).mp hb))
  exact (mem_quadraticNormSubgroup_iff_even_of_even_defectExponent h2 hd hev b).mpr
    (hbv ▸ Even.zero)

/-- For `a : Kˣ` of even finite defect exponent, `unitQuadraticNormSquareClasses (a : K)` equals
`unitSquareClasses K`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K :=
  (unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_unitFiltration_le (a : K)).mpr
    (unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent h2 hd hev)

/-- For `a : Kˣ` of even finite defect exponent, `quadraticNormSubgroup (a : K)` has relative
index `1` inside `U(K, 0)`. -/
theorem relIndex_quadraticNormSubgroup_unitFiltration_zero_of_even_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 1 :=
  Subgroup.relIndex_eq_one.mpr
    (unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent h2 hd hev)

/-- **Unit-norm square-class count for any radicand of odd quadratic defect.** Over a
nonarchimedean local field with `2 ≠ 0`, any `a : Kˣ` (of arbitrary integer valuation) whose
defect exponent `d` is odd has `#𝓀[K] ^ v_K(2)` unit-norm square classes. -/
theorem natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases Int.even_or_odd (normalizedValuation K a).toAdd with hv | hv
  · obtain ⟨c, hc_val, hc_def⟩ := exists_defectExponent_mul_sq_eq_sub_of_even_valuation hd hv
    obtain ⟨t, w, ht, hw, -, -, heq⟩ :=
      exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd hc_val hc_def
        (hodd.sub_even hv)
    have hcard := natCard_eisensteinNormSquareSubgroup h2 ht hw
    rwa [← heq, Units.val_mul, Units.val_pow_eq_pow_val,
      unitQuadraticNormSquareClasses_mul_sq] at hcard
  · obtain ⟨k, hk⟩ := hv
    obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
    have hunif : IsUniformizer K (a * c ^ 2) := by
      apply (isUniformizer_def _).mpr
      apply Multiplicative.toAdd.injective
      simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd]
      omega
    have hcard := natCard_unitQuadraticNormSquareClasses_of_isUniformizer h2 hunif
    rwa [Units.val_mul, Units.val_pow_eq_pow_val, unitQuadraticNormSquareClasses_mul_sq] at hcard

/-- **Index of unit-norm square classes for any radicand of odd quadratic defect.** Over a
nonarchimedean local field with `2 ≠ 0`, for any `a : Kˣ` of odd defect exponent,
`unitQuadraticNormSquareClasses (a : K)` has index `2` inside `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 := by
  have hmul := (unitQuadraticNormSquareClasses (a : K)).relIndex_mul_card (unitSquareClasses K)
  rw [inf_of_le_left (unitQuadraticNormSquareClasses_le_unitSquareClasses _),
    natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd,
    card_unitSquareClasses K h2] at hmul
  exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) hmul

/-- For any `a : Kˣ` of odd quadratic defect exponent, `quadraticNormSubgroup (a : K)` has
relative index `2` inside `U(K, 0)`. -/
theorem relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 := by
  rw [Subgroup.relIndex, ← relIndex_unitQuadraticNormSquareClasses,
    relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd]

/-! ### The direct norm-index theorems and ramification dichotomies -/

/-- **Direct norm-index theorem for odd quadratic defect.** Over a nonarchimedean local field with
`2 ≠ 0`, if `a : Kˣ` has odd defect exponent, `quadraticNormSubgroup (a : K)` has index `2` in
`Kˣ` (with valuation index `1` and unit index `2`). -/
theorem quadraticNormSubgroup_index_eq_two_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rw [← index_map_normalizedValuation_mul_relIndex_quadraticNormSubgroup_unitFiltration_zero,
    index_map_normalizedValuation_quadraticNormSubgroup_of_odd_defectExponent hd hodd,
    relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent h2 hd hodd, one_mul]

/-- **Direct norm-index theorem for even quadratic defect.** Over a nonarchimedean local field with
`2 ≠ 0`, if `a : Kˣ` has even finite defect exponent, `quadraticNormSubgroup (a : K)` has index `2`
in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_even_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_unramified_class
    ((unramified_class_iff_even_defectExponent h2 hd).mpr hev)

/-- For `a : Kˣ` of even finite defect exponent, the valuation image of
`quadraticNormSubgroup (a : K)` has index `2` in `Multiplicative ℤ`. -/
theorem index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    ((quadraticNormSubgroup (a : K)).map (normalizedValuation K)).index = 2 := by
  have h :=
    index_map_normalizedValuation_mul_relIndex_quadraticNormSubgroup_unitFiltration_zero
      (K := K) (a : K)
  rw [relIndex_quadraticNormSubgroup_unitFiltration_zero_of_even_defectExponent h2 hd hev,
    mul_one, quadraticNormSubgroup_index_eq_two_of_even_defectExponent h2 hd hev] at h
  exact h

/-- Every `a : Kˣ` of finite quadratic defect exponent `d` has norm subgroup of index `2`. -/
theorem quadraticNormSubgroup_index_eq_two_of_defectExponent_eq (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rcases Int.even_or_odd d with hev | hodd
  · exact quadraticNormSubgroup_index_eq_two_of_even_defectExponent h2 hd hev
  · exact quadraticNormSubgroup_index_eq_two_of_odd_defectExponent h2 hd hodd

/-- **Exact criterion for norm index two.** Over a nonarchimedean local field with `2 ≠ 0`,
`quadraticNormSubgroup (a : K)` has index `2` in `Kˣ` if and only if `a` is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_iff (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).index = 2 ↔ ¬IsSquare a := by
  constructor
  · intro hidx ha
    have : Invertible (2 : K) := invertibleOfNonzero h2
    have h1 := quadraticNormSubgroup_index_eq_one_of_isSquare ha
    omega
  · intro ha
    obtain ⟨d, hd⟩ := exists_defectExponent_eq_of_not_isSquare ha
    exact quadraticNormSubgroup_index_eq_two_of_defectExponent_eq h2 hd

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K) = ⊤` if and
only if `a` is a square. -/
theorem quadraticNormSubgroup_eq_top_iff (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    quadraticNormSubgroup (a : K) = ⊤ ↔ IsSquare a := by
  constructor
  · intro htop
    by_contra ha
    have h2_idx := (quadraticNormSubgroup_index_eq_two_iff h2).mpr ha
    rw [htop, Subgroup.index_top] at h2_idx
    omega
  · intro ha
    have : Invertible (2 : K) := invertibleOfNonzero h2
    exact quadraticNormSubgroup_eq_top_of_isSquare ha

/-- Every local unit in `U(K, 0)` is a norm from `K[√a]` if and only if `a` is a square or has
even finite defect exponent (that is, `K[√a]/K` is split or unramified). -/
theorem unitFiltration_zero_le_quadraticNormSubgroup_iff (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) ↔
      IsSquare a ∨ ∃ d : ℤ, defectExponent a = d ∧ Even d := by
  constructor
  · intro hle
    by_cases ha : IsSquare a
    · exact Or.inl ha
    obtain ⟨d, hd⟩ := exists_defectExponent_eq_of_not_isSquare ha
    rcases Int.even_or_odd d with hev | hodd
    · exact Or.inr ⟨d, hd, hev⟩
    · have h1 : (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 1 :=
        Subgroup.relIndex_eq_one.mpr hle
      have h2_idx :=
        relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent h2 hd hodd
      omega
  · rintro (ha | ⟨d, hd, hev⟩)
    · have : Invertible (2 : K) := invertibleOfNonzero h2
      rw [quadraticNormSubgroup_eq_top_of_isSquare ha]
      exact le_top
    · exact unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent h2 hd hev

/-- The unit norms `quadraticNormSubgroup (a : K) ⊓ U(K, 0)` have index `2` in `U(K, 0)` if and
only if `a` has odd finite defect exponent (that is, `K(√a)/K` is ramified). -/
theorem relIndex_quadraticNormSubgroup_unitFiltration_zero_eq_two_iff (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 ↔
      ∃ d : ℤ, defectExponent a = d ∧ Odd d := by
  refine ⟨fun hidx ↦ ?_, fun ⟨d, hd, hodd⟩ ↦
    relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent h2 hd hodd⟩
  by_cases ha : IsSquare a
  · have : Invertible (2 : K) := invertibleOfNonzero h2
    have h1 : (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 1 :=
      Subgroup.relIndex_eq_one.mpr (quadraticNormSubgroup_eq_top_of_isSquare ha ▸ le_top)
    omega
  obtain ⟨d, hd⟩ := exists_defectExponent_eq_of_not_isSquare ha
  rcases Int.even_or_odd d with hev | hodd
  · have h1 :=
      relIndex_quadraticNormSubgroup_unitFiltration_zero_of_even_defectExponent h2 hd hev
    omega
  · exact ⟨d, hd, hodd⟩

/-- The valuation image `(quadraticNormSubgroup (a : K)).map (normalizedValuation K)` has index `2`
in `Multiplicative ℤ` if and only if `a` has even finite defect exponent (that is, `K(√a)/K` is an
unramified field extension). -/
theorem index_map_normalizedValuation_quadraticNormSubgroup_eq_two_iff
    (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    ((quadraticNormSubgroup (a : K)).map (normalizedValuation K)).index = 2 ↔
      ∃ d : ℤ, defectExponent a = d ∧ Even d := by
  refine ⟨fun hidx ↦ ?_, fun ⟨d, hd, hev⟩ ↦
    index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent h2 hd hev⟩
  by_cases ha : IsSquare a
  · rw [map_normalizedValuation_quadraticNormSubgroup_eq_top_of_isSquare h2 ha,
      Subgroup.index_top] at hidx
    omega
  obtain ⟨d, hd⟩ := exists_defectExponent_eq_of_not_isSquare ha
  rcases Int.even_or_odd d with hev | hodd
  · exact ⟨d, hd, hev⟩
  · have h1 := index_map_normalizedValuation_quadraticNormSubgroup_of_odd_defectExponent hd hodd
    omega

end TauCeti

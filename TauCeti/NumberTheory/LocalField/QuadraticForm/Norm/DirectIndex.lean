/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClasses

import Mathlib.GroupTheory.IndexNormal
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.UnitQuotient
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# The direct norm-index theorem and norm square-class classification

Over a nonarchimedean local field `K` with `2 ≠ 0` and `q = #𝓀[K]`, this file establishes the
index `(Kˣ : N(K(√a)ˣ)) = 2` of `TauCeti.quadraticNormSubgroup (a : K)` and classifies both the full
norm square-class subgroup `(quadraticNormSubgroup (a : K)).map squareClassHom` and the unit-norm
square-class subgroup `TauCeti.unitQuadraticNormSquareClasses (a : K)` across all cases of the
quadratic defect `δ(a) = TauCeti.defectExponent a`, using only arithmetic in the base field `K`:

* **Even finite defect (`δ(a) = d` even, unramified nonsquare)**: the norms from `K(√a)` are
  precisely the elements of even normalized valuation, so `(quadraticNormSubgroup (a : K)).map
  squareClassHom` and `unitQuadraticNormSquareClasses (a : K)` both equal `unitSquareClasses K` of
  cardinality `2 * q ^ v_K(2)`, `U(K, 0) ≤ quadraticNormSubgroup (a : K)`, and
  `(quadraticNormSubgroup (a : K)).index = 2`.
* **Odd finite defect (`δ(a) = d` odd, ramified nonsquare — uniformizers and odd-defect units
  alike)**: `unitQuadraticNormSquareClasses (a : K)` has cardinality `q ^ v_K(2)` and index `2` in
  `unitSquareClasses K`, while `quadraticNormSubgroup (a : K)` contains elements of odd normalized
  valuation so `(quadraticNormSubgroup (a : K)).map squareClassHom ⊔ unitSquareClasses K = ⊤` and
  `U(K, 0)` meets every norm coset, again giving `(quadraticNormSubgroup (a : K)).index = 2`.
* **Square radicands (`δ(a) = ⊤`)**: `quadraticNormSubgroup (a : K) = ⊤` of index `1`, and
  `unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K`.

Consequently, among all `a : Kˣ` (`2 ≠ 0`), `(quadraticNormSubgroup (a : K)).index = 2` if and only
if `a` is not a square (`TauCeti.quadraticNormSubgroup_index_eq_two_iff_not_isSquare`),
`U(K, 0) ≤ quadraticNormSubgroup (a : K)` if and only if `a` is a square or has even defect
exponent (`TauCeti.unitFiltration_zero_le_quadraticNormSubgroup_iff`), and
`(quadraticNormSubgroup (a : K)).map squareClassHom = unitSquareClasses K` if and only if `a` has
even finite defect exponent
(`TauCeti.map_squareClassHom_quadraticNormSubgroup_eq_unitSquareClasses_iff`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Even quadratic defect -/

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), the image of
`quadraticNormSubgroup (a : K)` in `Kˣ ⧸ (Kˣ)²` is `unitSquareClasses K`. -/
theorem map_squareClassHom_quadraticNormSubgroup_eq_unitSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).map squareClassHom = unitSquareClasses K := by
  have hunr := (unramified_class_iff_even_defectExponent h2 hd).mpr hev
  ext q
  obtain ⟨b, rfl⟩ := squareClassHom_surjective q
  rw [squareClassHom_mem_map_quadraticNormSubgroup_iff,
    mem_quadraticNormSubgroup_iff_even_of_unramified_class hunr, squareClassHom_apply,
    mk_mem_unitSquareClasses_iff]

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), the unit-norm square classes fill
`unitSquareClasses K`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K := by
  rw [unitQuadraticNormSquareClasses_eq_inf,
    map_squareClassHom_quadraticNormSubgroup_eq_unitSquareClasses_of_even_defectExponent h2 hd hev,
    inf_idem]

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), every depth-zero unit of `K` is a norm
from `K(√a)`. -/
theorem unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) :=
  (unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff (a : K)).mp
    (unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent h2 hd hev)

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), there are
`2 * #𝓀[K] ^ natCastValuation K 2 h2` unit-norm square classes. -/
theorem natCard_unitQuadraticNormSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      2 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent h2 hd hev,
    card_unitSquareClasses K h2]

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), `unitQuadraticNormSquareClasses (a : K)`
has relative index `1` in `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 1 := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent h2 hd hev,
    Subgroup.relIndex_self]

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), the valuation-one quadratic norms have
index `1` in `U(K, 0)`. -/
theorem index_subgroupOf_unitFiltration_zero_eq_one_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    ((quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0)).index = 1 := by
  rw [← relIndex_unitQuadraticNormSquareClasses,
    relIndex_unitQuadraticNormSquareClasses_of_even_defectExponent h2 hd hev]

/-- For `a : Kˣ` of even finite defect exponent (`2 ≠ 0`), `quadraticNormSubgroup (a : K)` has
index `2` in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_unramified_class
    ((unramified_class_iff_even_defectExponent h2 hd).mpr hev)

/-! ### Odd quadratic defect -/

/-- For `a : Kˣ` of odd quadratic defect exponent (`2 ≠ 0`), the valuation-one quadratic norms have
index `2` inside `U(K, 0)`. -/
theorem index_subgroupOf_unitFiltration_zero_eq_two_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    ((quadraticNormSubgroup (a : K)).subgroupOf (unitFiltration K 0)).index = 2 := by
  rw [← relIndex_unitQuadraticNormSquareClasses,
    relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd]

/-- For `a : Kˣ` of odd quadratic defect exponent (`2 ≠ 0`), `quadraticNormSubgroup (a : K)` has
index `2` in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rw [← index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent hd
      hodd,
    index_subgroupOf_unitFiltration_zero_eq_two_of_odd_defectExponent h2 hd hodd]

/-- For a radicand of odd normalized valuation (`2 ≠ 0`), the quadratic norm subgroup has index
two. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_odd_defectExponent h2 (defectExponent_of_odd ha) ha

/-- For `a : Kˣ` of odd quadratic defect exponent, `(quadraticNormSubgroup (a : K)).map
squareClassHom` and `unitSquareClasses K` generate the entire square-class group `Kˣ ⧸ (Kˣ)²`. -/
theorem map_squareClassHom_quadraticNormSubgroup_sup_unitSquareClasses_of_odd_defectExponent
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).map squareClassHom ⊔ unitSquareClasses K = ⊤ := by
  obtain ⟨b, hb, hbval⟩ :=
    exists_mem_quadraticNormSubgroup_toAdd_normalizedValuation_eq_of_odd_defectExponent hd hodd 1
  have hb_notMem : squareClassHom b ∉ unitSquareClasses K := by
    rw [squareClassHom_apply, mk_mem_unitSquareClasses_iff, hbval]
    exact Int.not_even_one
  have hcoatom : IsCoatom (unitSquareClasses K) :=
    Subgroup.isCoatom_of_index_prime ((unitSquareClasses_index K).symm ▸ Nat.prime_two)
  exact (SetLike.isCoatom_iff.mp hcoatom).2 _ (squareClassHom b) le_sup_right hb_notMem
    (Subgroup.mem_sup_left ⟨b, hb, rfl⟩)

/-! ### Synthesis across all quadratic-defect cases -/

/-- Over a nonarchimedean local field with `2 ≠ 0`, every radicand `a : Kˣ` of finite quadratic
defect exponent has `(quadraticNormSubgroup (a : K)).index = 2`. -/
theorem quadraticNormSubgroup_index_eq_two_of_defectExponent_eq (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rcases Int.even_or_odd d with hev | hodd
  · exact quadraticNormSubgroup_index_eq_two_of_even_defectExponent h2 hd hev
  · exact quadraticNormSubgroup_index_eq_two_of_odd_defectExponent h2 hd hodd

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K)` has index `2`
in `Kˣ` if and only if `a` is not a square. -/
theorem quadraticNormSubgroup_index_eq_two_iff_not_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).index = 2 ↔ ¬IsSquare a := by
  refine ⟨fun h ha ↦ ?_, fun ha ↦ ?_⟩
  · rw [quadraticNormSubgroup_eq_top_of_isSquare h2.isUnit a.isUnit
        (Units.isSquare_coe_iff.mpr ha), Subgroup.index_top] at h
    exact absurd h (by decide)
  · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
    exact quadraticNormSubgroup_index_eq_two_of_defectExponent_eq h2 hd.symm

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K) = ⊤` if and only
if `a` is a square. -/
theorem quadraticNormSubgroup_eq_top_iff_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    quadraticNormSubgroup (a : K) = ⊤ ↔ IsSquare a := by
  refine ⟨fun h ↦ not_not.mp fun ha ↦ ?_, fun ha ↦
    quadraticNormSubgroup_eq_top_of_isSquare h2.isUnit a.isUnit (Units.isSquare_coe_iff.mpr ha)⟩
  have h2idx := (quadraticNormSubgroup_index_eq_two_iff_not_isSquare h2).mpr ha
  rw [h, Subgroup.index_top] at h2idx
  exact absurd h2idx (by decide)

/-- Over a nonarchimedean local field with `2 ≠ 0`, `(quadraticNormSubgroup (a : K)).map
squareClassHom = ⊤` if and only if `a` is a square. -/
theorem map_squareClassHom_quadraticNormSubgroup_eq_top_iff_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).map squareClassHom = ⊤ ↔ IsSquare a := by
  rw [← quadraticNormSubgroup_eq_top_iff_isSquare h2]
  exact ⟨fun h ↦ by
      rw [← comap_squareClassHom_map_quadraticNormSubgroup (a : K), h, Subgroup.comap_top],
    fun h ↦ by rw [h, Subgroup.map_top_of_surjective _ squareClassHom_surjective]⟩

/-- Over a nonarchimedean local field with `2 ≠ 0`, `quadraticNormSubgroup (a : K)` has index `1`
if and only if `a` is a square. -/
theorem quadraticNormSubgroup_index_eq_one_iff_isSquare (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).index = 1 ↔ IsSquare a := by
  rw [Subgroup.index_eq_one, quadraticNormSubgroup_eq_top_iff_isSquare h2]

/-- Over a nonarchimedean local field with `2 ≠ 0`, for every nonsquare `a : Kˣ`, the norm
square-class subgroup `(quadraticNormSubgroup (a : K)).map squareClassHom` has cardinality
`2 * #𝓀[K] ^ natCastValuation K 2 h2`. -/
theorem natCard_map_squareClassHom_quadraticNormSubgroup_of_not_isSquare (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : ¬IsSquare a) :
    Nat.card ((quadraticNormSubgroup (a : K)).map squareClassHom) =
      2 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  have hmul := ((quadraticNormSubgroup (a : K)).map squareClassHom).card_mul_index
  rw [index_map_squareClassHom_quadraticNormSubgroup,
    (quadraticNormSubgroup_index_eq_two_iff_not_isSquare h2).mpr ha, card_squareClass h2] at hmul
  omega

/-- Over a nonarchimedean local field with `2 ≠ 0`, every depth-zero unit is a norm from `K[√a]` if
and only if `a` is a square or has an even finite quadratic defect exponent. -/
theorem unitFiltration_zero_le_quadraticNormSubgroup_iff (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) ↔
      IsSquare a ∨ ∃ d : ℤ, defectExponent a = d ∧ Even d := by
  constructor
  · intro hle
    by_cases ha : IsSquare a
    · exact Or.inl ha
    · obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
      rcases Int.even_or_odd d with hev | hodd
      · exact Or.inr ⟨d, hd.symm, hev⟩
      · have hidx := index_subgroupOf_unitFiltration_zero_eq_two_of_odd_defectExponent h2 hd.symm
          hodd
        rw [Subgroup.subgroupOf_eq_top.mpr hle, Subgroup.index_top] at hidx
        exact absurd hidx (by decide)
  · rintro (ha | ⟨d, hd, hev⟩)
    · rw [quadraticNormSubgroup_eq_top_of_isSquare h2.isUnit a.isUnit
        (Units.isSquare_coe_iff.mpr ha)]
      exact le_top
    · exact unitFiltration_zero_le_quadraticNormSubgroup_of_even_defectExponent h2 hd hev

/-- Over a nonarchimedean local field with `2 ≠ 0`, `unitQuadraticNormSquareClasses (a : K)` equals
`unitSquareClasses K` if and only if `a` is a square or has an even finite quadratic defect
exponent. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_isSquare_or_even
    (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K ↔
      IsSquare a ∨ ∃ d : ℤ, defectExponent a = d ∧ Even d := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff,
    unitFiltration_zero_le_quadraticNormSubgroup_iff h2]

/-- Over a nonarchimedean local field with `2 ≠ 0`, the full norm square-class subgroup
`(quadraticNormSubgroup (a : K)).map squareClassHom` equals `unitSquareClasses K` if and only if
`a` has an even finite quadratic defect exponent. -/
theorem map_squareClassHom_quadraticNormSubgroup_eq_unitSquareClasses_iff
    (h2 : (2 : K) ≠ 0) {a : Kˣ} :
    (quadraticNormSubgroup (a : K)).map squareClassHom = unitSquareClasses K ↔
      ∃ d : ℤ, defectExponent a = d ∧ Even d := by
  refine ⟨fun heq ↦ ?_, fun ⟨d, hd, hev⟩ ↦
    map_squareClassHom_quadraticNormSubgroup_eq_unitSquareClasses_of_even_defectExponent h2 hd hev⟩
  have ha : ¬IsSquare a := fun hsq ↦ unitSquareClasses_ne_top K <| by
    rwa [← heq, map_squareClassHom_quadraticNormSubgroup_eq_top_iff_isSquare h2]
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp (mt defectExponent_eq_top_iff.mp ha)
  refine ⟨d, hd.symm, (Int.even_or_odd d).resolve_right fun hodd ↦ unitSquareClasses_ne_top K ?_⟩
  have hsup := map_squareClassHom_quadraticNormSubgroup_sup_unitSquareClasses_of_odd_defectExponent
    hd.symm hodd
  rwa [heq, sup_idem] at hsup

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClasses

import TauCeti.GroupTheory.QuotientGroup.KerEquiv
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Eisenstein.OddDefect
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Index
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.SquareClass
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.UnitQuotient
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# The direct quadratic norm-index calculation across all defect regimes

Let `K` be a nonarchimedean local field with `2 ≠ 0`, residue cardinality `q = #𝓀[K]`, and dyadic
valuation `e = v_K(2)`. Under the exact sequence `1 → U(K, 0) → Kˣ → Multiplicative ℤ → 1`, the
index of the quadratic norm subgroup `N = quadraticNormSubgroup (a : K)` factors into the index of
its valuation image and its relative index in `U(K, 0)`. For every nonsquare `a : Kˣ`, its
quadratic defect exponent `δ(a) = d ∈ ℤ` is finite and determines how the index `2` splits between
valuation cosets and unit square classes, using only base-field arithmetic:

* **Odd defect exponent (`Odd d`)**: up to a square factor, `a` is either a uniformizer or a unit
  of odd defect exponent `2k + 1 < 2e`. Combining the uniformizer norm-family count with the
  Eisenstein unit-norm count shows `#unitQuadraticNormSquareClasses (a : K) = q ^ e`
  (`TauCeti.natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent`), giving index `2` inside
  `unitSquareClasses K` (`TauCeti.relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent`)
  and inside `U(K, 0)`
  (`TauCeti.relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent`). Since `N`
  attains every normalized valuation, `(Kˣ : N) = 2`
  (`TauCeti.quadraticNormSubgroup_index_eq_two_of_odd_defectExponent`).
* **Even defect exponent (`Even d`)**: by the ramification dictionary, `a` lies in the unramified
  square class, so `N` consists of the elements of even normalized valuation. Every unit in
  `U(K, 0)` is a norm, `unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K` has
  cardinality `2 * q ^ e`
  (`TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent`,
  `TauCeti.natCard_unitQuadraticNormSquareClasses_of_even_defectExponent`), the valuation image is
  `Subgroup.square (Multiplicative ℤ)` of index `2`
  (`TauCeti.map_normalizedValuation_quadraticNormSubgroup_eq_square_of_even_defectExponent`,
  `TauCeti.index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent`),
  normalized valuation modulo two gives `Kˣ ⧸ N ≃* Multiplicative (ZMod 2)`
  (`TauCeti.normQuotientEquivOfEvenDefectExponent`), and `(Kˣ : N) = 2`
  (`TauCeti.quadraticNormSubgroup_index_eq_two_of_even_defectExponent`).

Putting both regimes together also yields two-sided characterizations of unit-norm surjectivity,
unit relative index `2`, and the valuation image by the parity of `d`
(`TauCeti.unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent`,
`TauCeti.relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent`,
`TauCeti.relIndex_quadraticNormSubgroup_unitFiltration_zero_eq_two_iff_odd_defectExponent`,
`TauCeti.map_normalizedValuation_quadraticNormSubgroup_eq_top_iff_odd_defectExponent`,
`TauCeti.map_normalizedValuation_quadraticNormSubgroup_eq_square_iff_even_defectExponent`,
`TauCeti.index_map_normalizedValuation_quadraticNormSubgroup_eq_two_iff_even_defectExponent`).

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public noncomputable section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Odd quadratic defect -/

private theorem natCard_unitQuadraticNormSquareClasses_of_odd (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : Odd (normalizedValuation K a).toAdd) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨c, hc⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (-k))
  have hb : IsUniformizer K (a * c ^ 2) := by
    apply (isUniformizer_def _).mpr
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, nsmul_eq_mul, hc, toAdd_ofAdd]
    omega
  obtain ⟨π, hπ, hπb⟩ := (isUniformizer_iff_exists_irreducible K (a * c ^ 2)).mp hb
  have hset : (unitQuadraticNormSquareClasses (π : K) : Set (Kˣ ⧸ Subgroup.square Kˣ)) =
      Set.range (uniformizerNormSquareClass K hπ) := by
    ext q
    rw [SetLike.mem_coe, mem_unitQuadraticNormSquareClasses_iff,
      mem_range_uniformizerNormSquareClass_iff]
    exact ⟨fun ⟨u, hu, huv, huq⟩ ↦ ⟨u, huv, hu, huq⟩,
      fun ⟨u, huv, hu, huq⟩ ↦ ⟨u, hu, huv, huq⟩⟩
  calc Nat.card (unitQuadraticNormSquareClasses (a : K))
      = Nat.card (unitQuadraticNormSquareClasses ((a * c ^ 2 : Kˣ) : K)) := by
          rw [Units.val_mul, Units.val_pow_eq_pow_val, unitQuadraticNormSquareClasses_mul_sq]
    _ = (unitQuadraticNormSquareClasses (π : K) : Set (Kˣ ⧸ Subgroup.square Kˣ)).ncard := by
          rw [← hπb]; exact Nat.card_coe_set_eq _
    _ = Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
          rw [hset, ncard_range_uniformizerNormSquareClass h2 hπ]

/-- **Unit-norm square-class count for odd quadratic defect.** Over a nonarchimedean local field
with `2 ≠ 0`, if `a` has odd quadratic defect exponent, `unitQuadraticNormSquareClasses (a : K)`
has cardinality `#𝓀[K] ^ v_K(2)`. -/
theorem natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rcases Int.even_or_odd (normalizedValuation K a).toAdd with hev | hval
  · obtain ⟨c, hcval, hcd⟩ := exists_defectExponent_mul_sq_eq_sub_of_even_valuation hd hev
    obtain ⟨t, π', ht, hπ', -, -, hsq⟩ :=
      exists_eisenstein_mem_quadraticNormSubgroup_iff_of_defectExponent_eq_odd hcval hcd
        (hodd.sub_even hev)
    rw [← unitQuadraticNormSquareClasses_mul_sq (a : K) c, ← Units.val_pow_eq_pow_val,
      ← Units.val_mul, hsq, natCard_eisensteinNormSquareSubgroup h2 ht hπ']
  · exact natCard_unitQuadraticNormSquareClasses_of_odd h2 hval

/-- **Unit-norm square-class index for odd quadratic defect.** Over a nonarchimedean local field
with `2 ≠ 0`, if `a` has odd quadratic defect exponent, `unitQuadraticNormSquareClasses (a : K)`
has index two in `unitSquareClasses K`. -/
theorem relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 := by
  have hmul := (unitQuadraticNormSquareClasses (a : K)).relIndex_mul_card (unitSquareClasses K)
  rw [inf_of_le_left (unitQuadraticNormSquareClasses_le_unitSquareClasses (a : K)),
    natCard_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd,
    card_unitSquareClasses K h2] at hmul
  have hq : 0 < Nat.card 𝓀[K] := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul

/-- For odd quadratic defect over a nonarchimedean local field with `2 ≠ 0`, the unit norms from
`K(√a)` have index two in `U(K, 0)`. -/
theorem relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 := by
  rw [Subgroup.relIndex, ← relIndex_unitQuadraticNormSquareClasses (a : K)]
  exact relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd

/-- **Direct norm-index theorem for odd quadratic defect.** Over a nonarchimedean local field with
`2 ≠ 0`, if `a` has odd quadratic defect exponent, `quadraticNormSubgroup (a : K)` has index two
in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hodd : Odd d) :
    (quadraticNormSubgroup (a : K)).index = 2 := by
  rw [← index_map_normalizedValuation_quadraticNormSubgroup_mul_relIndex (a : K),
    map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent hd hodd,
    Subgroup.index_top, one_mul]
  exact relIndex_quadraticNormSubgroup_unitFiltration_zero_of_odd_defectExponent h2 hd hodd

/-- For a radicand of odd normalized valuation, the quadratic norm subgroup has index two. -/
theorem quadraticNormSubgroup_index_eq_two_of_odd (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : Odd (normalizedValuation K a).toAdd) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_odd_defectExponent h2 (defectExponent_of_odd ha) ha

/-! ### Even quadratic defect -/

-- Proved directly from the unramified-class dictionary so this module stays upstream of
-- `Bimultiplicativity` (which `Norm.Conductor` imports through `Norm.Sharpness`).
private theorem unitFiltration_zero_le_of_even_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) := by
  have hunr := (unramified_class_iff_even_defectExponent h2 hd).mpr hev
  intro u hu
  rw [mem_quadraticNormSubgroup_iff_even_of_unramified_class hunr,
    (normalizedValuation_eq_one_iff u).mpr ((mem_unitFiltration_zero u).mp hu), toAdd_one]
  exact Even.zero

/-- For even quadratic defect over a nonarchimedean local field with `2 ≠ 0`, every unit square
class of `K` is represented by a valuation-one norm from `K(√a)`. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K :=
  (unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff (a : K)).mpr
    (unitFiltration_zero_le_of_even_defectExponent h2 hd hev)

/-- **Unit-norm square-class count for even quadratic defect.** Over a nonarchimedean local field
with `2 ≠ 0`, if `a` has even quadratic defect exponent, `unitQuadraticNormSquareClasses (a : K)`
has cardinality `2 * #𝓀[K] ^ v_K(2)`. -/
theorem natCard_unitQuadraticNormSquareClasses_of_even_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    Nat.card (unitQuadraticNormSquareClasses (a : K)) =
      2 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent h2 hd hev,
    card_unitSquareClasses K h2]

/-- For even quadratic defect over a nonarchimedean local field with `2 ≠ 0`, `normalizedValuation`
maps `quadraticNormSubgroup (a : K)` onto the subgroup of squares in `Multiplicative ℤ` (the even
valuations). -/
theorem map_normalizedValuation_quadraticNormSubgroup_eq_square_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).map (normalizedValuation K) =
      Subgroup.square (Multiplicative ℤ) := by
  have hunr := (unramified_class_iff_even_defectExponent h2 hd).mpr hev
  ext v
  simp only [Subgroup.mem_map, mem_quadraticNormSubgroup_iff_even_of_unramified_class hunr,
    Subgroup.mem_square, IsSquare]
  constructor
  · rintro ⟨b, ⟨k, hk⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd k,
      Multiplicative.toAdd.injective (by simpa only [toAdd_mul, toAdd_ofAdd] using hk)⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨b, hb⟩ := normalizedValuation_surjective (K := K) (w * w)
    exact ⟨b, hb ▸ ⟨w.toAdd, toAdd_mul w w⟩, hb⟩

private def valuationParityHom : Kˣ →* Multiplicative (ZMod 2) :=
  (squareClassValuation K).comp (QuotientGroup.mk' (Subgroup.square Kˣ))

private theorem valuationParityHom_surjective :
    Function.Surjective (valuationParityHom (K := K)) :=
  (squareClassValuation_surjective K).comp (QuotientGroup.mk'_surjective _)

private theorem quadraticNormSubgroup_eq_ker_valuationParityHom (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    quadraticNormSubgroup (a : K) = (valuationParityHom (K := K)).ker := by
  have hunr := (unramified_class_iff_even_defectExponent h2 hd).mpr hev
  ext b
  rw [mem_quadraticNormSubgroup_iff_even_of_unramified_class hunr, MonoidHom.mem_ker,
    valuationParityHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply, squareClassValuation_mk,
    ofAdd_eq_one, ZMod.intCast_eq_zero_iff_even]

/-- For even quadratic defect over a nonarchimedean local field with `2 ≠ 0`, normalized valuation
modulo two identifies the quadratic norm quotient `Kˣ ⧸ quadraticNormSubgroup (a : K)` with
`Multiplicative (ZMod 2)`, dual to `TauCeti.unitNormQuotientEquivOfOddDefectExponent`. -/
def normQuotientEquivOfEvenDefectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hev : Even d) :
    Kˣ ⧸ quadraticNormSubgroup (a : K) ≃* Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq
      (quadraticNormSubgroup_eq_ker_valuationParityHom h2 hd hev)).trans
    (QuotientGroup.quotientKerEquivOfSurjective valuationParityHom valuationParityHom_surjective)

/-- `normQuotientEquivOfEvenDefectExponent` sends the class of `b : Kˣ` to its normalized valuation
modulo two. -/
@[simp]
theorem normQuotientEquivOfEvenDefectExponent_mk (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ}
    (hd : defectExponent a = d) (hev : Even d) (b : Kˣ) :
    normQuotientEquivOfEvenDefectExponent h2 hd hev (b : Kˣ ⧸ quadraticNormSubgroup (a : K)) =
      Multiplicative.ofAdd ((normalizedValuation K b).toAdd : ZMod 2) := by
  unfold normQuotientEquivOfEvenDefectExponent
  rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    TauCeti.QuotientGroup.quotientKerEquivOfSurjective_apply_mk]
  exact squareClassValuation_mk K b

/-- **Direct norm-index theorem for even quadratic defect.** Over a nonarchimedean local field with
`2 ≠ 0`, if `a` has even quadratic defect exponent, `quadraticNormSubgroup (a : K)` has index two
in `Kˣ`. -/
theorem quadraticNormSubgroup_index_eq_two_of_even_defectExponent (h2 : (2 : K) ≠ 0) {a : Kˣ}
    {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    (quadraticNormSubgroup (a : K)).index = 2 :=
  quadraticNormSubgroup_index_eq_two_of_unramified_class
    ((unramified_class_iff_even_defectExponent h2 hd).mpr hev)

/-- For even quadratic defect over a nonarchimedean local field with `2 ≠ 0`, the image of
`quadraticNormSubgroup (a : K)` under `normalizedValuation K` has index two in
`Multiplicative ℤ`. -/
theorem index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) (hev : Even d) :
    ((quadraticNormSubgroup (a : K)).map (normalizedValuation K)).index = 2 := by
  have hmul := index_map_normalizedValuation_quadraticNormSubgroup_mul_relIndex (a : K)
  rwa [Subgroup.relIndex_eq_one.mpr (unitFiltration_zero_le_of_even_defectExponent h2 hd hev),
    mul_one, quadraticNormSubgroup_index_eq_two_of_even_defectExponent h2 hd hev] at hmul

/-! ### Parity characterizations across finite defect -/

/-- For a nonsquare `a` of defect exponent `d`, `unitQuadraticNormSquareClasses (a : K)` equals
`unitSquareClasses K` if and only if `d` is even. -/
theorem unitQuadraticNormSquareClasses_eq_unitSquareClasses_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    unitQuadraticNormSquareClasses (a : K) = unitSquareClasses K ↔ Even d := by
  refine ⟨fun h ↦ ?_, unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent
    h2 hd⟩
  by_contra hnot
  have hodd := Int.not_even_iff_odd.mp hnot
  have hrel := relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd hodd
  rw [h, Subgroup.relIndex_self] at hrel
  omega

/-- For a nonsquare `a` of defect exponent `d`, `unitQuadraticNormSquareClasses (a : K)` has index
two in `unitSquareClasses K` if and only if `d` is odd. -/
theorem relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (unitQuadraticNormSquareClasses (a : K)).relIndex (unitSquareClasses K) = 2 ↔ Odd d := by
  refine ⟨fun h ↦ ?_, relIndex_unitQuadraticNormSquareClasses_of_odd_defectExponent h2 hd⟩
  rw [← Int.not_even_iff_odd]
  intro hev
  rw [unitQuadraticNormSquareClasses_eq_unitSquareClasses_of_even_defectExponent h2 hd hev,
    Subgroup.relIndex_self] at h
  omega

/-- For a nonsquare `a` of defect exponent `d`, the unit norms from `K(√a)` have index two in
`U(K, 0)` if and only if `d` is odd. -/
theorem relIndex_quadraticNormSubgroup_unitFiltration_zero_eq_two_iff_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 ↔ Odd d := by
  rw [Subgroup.relIndex, ← relIndex_unitQuadraticNormSquareClasses (a : K),
    relIndex_unitQuadraticNormSquareClasses_eq_two_iff_odd_defectExponent h2 hd]

/-- For a nonsquare `a` of defect exponent `d`, `normalizedValuation K` maps
`quadraticNormSubgroup (a : K)` onto `Multiplicative ℤ` if and only if `d` is odd. -/
theorem map_normalizedValuation_quadraticNormSubgroup_eq_top_iff_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).map (normalizedValuation K) = ⊤ ↔ Odd d := by
  refine ⟨fun h ↦ ?_, map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent hd⟩
  rw [← Int.not_even_iff_odd]
  intro hev
  have hidx := index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent h2 hd hev
  rw [h, Subgroup.index_top] at hidx
  omega

/-- For a nonsquare `a` of defect exponent `d`, `normalizedValuation K` maps
`quadraticNormSubgroup (a : K)` onto `Subgroup.square (Multiplicative ℤ)` if and only if `d` is
even. -/
theorem map_normalizedValuation_quadraticNormSubgroup_eq_square_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    (quadraticNormSubgroup (a : K)).map (normalizedValuation K) =
        Subgroup.square (Multiplicative ℤ) ↔
      Even d := by
  refine ⟨fun h ↦ ?_,
    map_normalizedValuation_quadraticNormSubgroup_eq_square_of_even_defectExponent h2 hd⟩
  by_contra hnot
  have htop := map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent hd
    (Int.not_even_iff_odd.mp hnot)
  have hmem : Multiplicative.ofAdd (1 : ℤ) ∈ (⊤ : Subgroup (Multiplicative ℤ)) :=
    Subgroup.mem_top _
  rw [← htop, h, Subgroup.mem_square] at hmem
  obtain ⟨w, hw⟩ := hmem
  have h1 := congrArg Multiplicative.toAdd hw
  simp only [toAdd_mul, toAdd_ofAdd] at h1
  omega

/-- For a nonsquare `a` of defect exponent `d`, the image of `quadraticNormSubgroup (a : K)` under
`normalizedValuation K` has index two in `Multiplicative ℤ` if and only if `d` is even. -/
theorem index_map_normalizedValuation_quadraticNormSubgroup_eq_two_iff_even_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} {d : ℤ} (hd : defectExponent a = d) :
    ((quadraticNormSubgroup (a : K)).map (normalizedValuation K)).index = 2 ↔ Even d := by
  refine ⟨fun h ↦ ?_, index_map_normalizedValuation_quadraticNormSubgroup_of_even_defectExponent
    h2 hd⟩
  by_contra hnot
  have hodd := Int.not_even_iff_odd.mp hnot
  rw [map_normalizedValuation_quadraticNormSubgroup_eq_top_of_odd_defectExponent hd hodd,
    Subgroup.index_top] at h
  omega

end TauCeti

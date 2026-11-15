/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Filtration
public import TauCeti.NumberTheory.LocalField.UnitSquareClasses

import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.DirectIndex
import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Square

/-!
# The unit norms of an odd-defect radicand and the deep units modulo squares

Let `K` be a nonarchimedean local field with `2 ≠ 0`, put `e = v_K(2)`, and let `q` be the
cardinality of the residue field. For `m ≤ e`, the subgroup `U(K, 2m) · (𝒪[K]ˣ)²` has index
`q ^ m` in `𝒪[K]ˣ` (`TauCeti.relIndex_unitFiltration_two_mul_sup_square`). Here `𝒪[K]ˣ` is
`U(K, 0)`, and `U(K, 2m) · (𝒪[K]ˣ)²` is `(U(K, 2m) · (Kˣ)²) ∩ U(K, 0)`, because a unit that is a
square in `K` is the square of a unit.

For a unit radicand `a` of odd defect exponent `d = 2k + 1` (`k = d / 2 < e`), the deep units
`U(K, 2e - d + 1) = U(K, 2(e - k))` are norms from `K(√a)`, and so is every square. Because the
unit norms `N(K(√a)ˣ) ∩ 𝒪[K]ˣ` have index `2` in `𝒪[K]ˣ`
(`TauCeti.relIndex_unitFiltration_quadraticNormSubgroup_of_odd_defectExponent`), twice the index of
`U(K, 2e - d + 1) · (𝒪[K]ˣ)²` inside the unit norms equals `q ^ (e - d / 2)`
(`TauCeti.two_mul_relIndex_quadraticNormSubgroup_inf_of_odd_defectExponent`).

Consequently, the containment `U(K, 2e - d + 1) · (𝒪[K]ˣ)² ⊆ N(K(√a)ˣ) ∩ 𝒪[K]ˣ` is an equality
if and only if `q ^ (e - d / 2) = 2` — equivalently, `q = 2` and `d = 2e - 1` is the maximal odd
defect — and is strict whenever `q ^ (e - d / 2) > 2`. Specializing to `d = 1` recovers the
defect-one comparison (`q ^ e = 2` vs `q ^ e > 2`), which for `K = ℚ₂(√2)` (`q = 2`, `e = 2`)
shows that `U(K, 4) · (𝒪[K]ˣ)²` has index `4` in `𝒪[K]ˣ` and index `2` inside the unit norms
(`TauCeti.DyadicSqrtTwo.relIndex_unitFiltration_four_sup_square`).

## Main results

* `TauCeti.unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq`: for a unit
  radicand of finite defect exponent `d`, `U(K, 2e - d + 1) · (Kˣ)²` consists of norms.
* `TauCeti.two_mul_relIndex_quadraticNormSubgroup_inf_of_odd_defectExponent`:
  for a unit of odd defect `d`, twice the index of `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` inside the unit
  norms is `q ^ (e - d / 2)`.
* `TauCeti.unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_of_odd_defectExponent`
  and `TauCeti.unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_natCard_eq_two`:
  equality holds iff `q ^ (e - d / 2) = 2`, equivalently `q = 2 ∧ d = 2e - 1`.
* `TauCeti.unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff_of_odd_defectExponent`:
  strict containment holds iff `2 < q ^ (e - d / 2)`.
* `TauCeti.unitFiltration_sup_square_le_quadraticNormSubgroup`,
  `TauCeti.unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff`, and
  `TauCeti.unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff`: the `d = 1`
  specializations.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **`U(K, 2e - d + 1) · (Kˣ)²` consists of norms from `K(√a)`** for a unit `a` of finite defect
exponent `d`, where `e = v_K(2)`: every element of `U(K, 2e - d + 1)` is a norm, and so is every
square. -/
theorem unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ} (hd : defectExponent a = (d : ℤ)) :
    unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ ≤
      quadraticNormSubgroup (a : K) :=
  sup_le (unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd)
    (square_le_quadraticNormSubgroup (a : K))

/-- **Index of `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` inside the unit norms of an odd-defect radicand.**
For a unit `a` of odd defect exponent `d`, twice the index of `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` inside
`quadraticNormSubgroup (a : K) ⊓ U(K, 0)` equals `#𝓀[K] ^ (e - d / 2)`. -/
theorem two_mul_relIndex_quadraticNormSubgroup_inf_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    2 * (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ).relIndex
        (quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0) =
      Nat.card 𝓀[K] ^ (dyadicLevel K h2 - d / 2) := by
  have hdle : d ≤ 2 * dyadicLevel K h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha
      (not_isSquare_of_defectExponent_eq hd)
    rw [hd, ← dyadicLevel_def, WithTop.coe_le_coe] at h
    exact_mod_cast h
  obtain ⟨k, hk⟩ := hodd
  have hstep : 2 * dyadicLevel K h2 - d + 1 = 2 * (dyadicLevel K h2 - d / 2) := by omega
  have hm : dyadicLevel K h2 - d / 2 ≤ natCastValuation K 2 h2 := by
    rw [← dyadicLevel_def]; omega
  let H := unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ
  let U := unitFiltration K 0
  have hsub : H ⊓ U ≤ quadraticNormSubgroup (a : K) ⊓ U :=
    inf_le_inf_right U
      (unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd)
  have hmul := Subgroup.relIndex_mul_relIndex (H ⊓ U) (quadraticNormSubgroup (a : K) ⊓ U) U
    hsub inf_le_right
  have hleft : (H ⊓ U).relIndex (quadraticNormSubgroup (a : K) ⊓ U) =
      H.relIndex (quadraticNormSubgroup (a : K) ⊓ U) := by
    rw [Subgroup.relIndex, Subgroup.relIndex]
    congr 1
    ext x
    exact ⟨fun hx ↦ hx.1, fun hx ↦ ⟨hx, x.2.2⟩⟩
  have hoddZ : Odd (d : ℤ) := ⟨k, by push_cast [hk]; ring⟩
  have hN : (quadraticNormSubgroup (a : K) ⊓ U).relIndex U = 2 := by
    rw [Subgroup.inf_relIndex_right]
    exact relIndex_unitFiltration_quadraticNormSubgroup_of_odd_defectExponent h2 hd hoddZ
  have hT : (H ⊓ U).relIndex U = Nat.card 𝓀[K] ^ (dyadicLevel K h2 - d / 2) := by
    rw [Subgroup.inf_relIndex_right]
    dsimp only [H, U]
    rw [hstep, relIndex_unitFiltration_two_mul_sup_square h2 hm]
  rw [hleft, hN, hT, mul_comm] at hmul
  exact hmul

/-- **The unit norms of an odd-defect radicand equal `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` iff
`#𝓀[K] ^ (e - d / 2) = 2`.** -/
theorem unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 =
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      Nat.card 𝓀[K] ^ (dyadicLevel K h2 - d / 2) = 2 := by
  have hmul :=
    two_mul_relIndex_quadraticNormSubgroup_inf_of_odd_defectExponent
      h2 ha hd hodd
  have hsub := inf_le_inf_right (unitFiltration K 0)
    (unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd)
  constructor
  · intro heq
    have h1 : (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ).relIndex
        (quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0) = 1 := by
      rw [← heq]
      exact Subgroup.relIndex_eq_one.mpr inf_le_left
    omega
  · intro hq2
    have h1 : (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ).relIndex
        (quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0) = 1 := by omega
    exact le_antisymm hsub (le_inf (Subgroup.relIndex_eq_one.mp h1) inf_le_right)

/-- **Residue-cardinality and maximal-odd-defect form of equality.** For a unit `a` of odd defect
exponent `d`, the unit norms equal `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` if and only if `#𝓀[K] = 2` and
`d = 2 v_K(2) - 1` is the maximal odd defect exponent. -/
theorem unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_natCard_eq_two
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 =
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      Nat.card 𝓀[K] = 2 ∧ d = 2 * dyadicLevel K h2 - 1 := by
  rw [unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
    h2 ha hd hodd]
  have hdle : d ≤ 2 * dyadicLevel K h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha
      (not_isSquare_of_defectExponent_eq hd)
    rw [hd, ← dyadicLevel_def, WithTop.coe_le_coe] at h
    exact_mod_cast h
  obtain ⟨k, hk⟩ := hodd
  have h1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hm_pos : 0 < dyadicLevel K h2 - d / 2 := by omega
  constructor
  · intro hpow
    have hq_le : Nat.card 𝓀[K] ≤ 2 :=
      hpow ▸ Nat.le_self_pow hm_pos.ne' (Nat.card 𝓀[K])
    have hq2 : Nat.card 𝓀[K] = 2 := by omega
    rw [hq2] at hpow
    have hm1 : dyadicLevel K h2 - d / 2 = 1 :=
      Nat.pow_right_injective le_rfl (hpow.trans (pow_one 2).symm)
    exact ⟨hq2, by omega⟩
  · rintro ⟨hq2, hd_eq⟩
    rw [hq2, show dyadicLevel K h2 - d / 2 = 1 by omega, pow_one]

/-- **Strict containment of `U(K, 2e - d + 1) · (𝒪[K]ˣ)²` inside the unit norms of an odd-defect
radicand.** Containment is strict if and only if `2 < #𝓀[K] ^ (e - d / 2)`. -/
theorem unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
    (h2 : (2 : K) ≠ 0) {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) (hodd : Odd d) :
    (unitFiltration K (2 * dyadicLevel K h2 - d + 1) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 <
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      2 < Nat.card 𝓀[K] ^ (dyadicLevel K h2 - d / 2) := by
  have hdle : d ≤ 2 * dyadicLevel K h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha
      (not_isSquare_of_defectExponent_eq hd)
    rw [hd, ← dyadicLevel_def, WithTop.coe_le_coe] at h
    exact_mod_cast h
  have ⟨k, hk⟩ := hodd
  have h1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hq : Nat.card 𝓀[K] ≤ Nat.card 𝓀[K] ^ (dyadicLevel K h2 - d / 2) :=
    Nat.le_self_pow (by omega) _
  rw [lt_iff_le_and_ne, and_iff_right (inf_le_inf_right (unitFiltration K 0)
    (unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha hd)), Ne,
    unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
      h2 ha hd hodd]
  omega

/-! ### Defect-one specializations -/

/-- **`U(K, 2e) · (Kˣ)²` consists of norms from `K(√a)`** for a unit `a` of defect exponent `1`,
where `e = v_K(2)`: every element of `U(K, 2e) = U(K, 2e - 1 + 1)` is a norm, and so is every
square. -/
theorem unitFiltration_sup_square_le_quadraticNormSubgroup (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ ≤
      quadraticNormSubgroup (a : K) := by
  have he := dyadicLevel_ne_zero_of_defectExponent_eq h2 ha hd one_pos
  have hle := unitFiltration_sup_square_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha
    (d := 1) (by exact_mod_cast hd)
  rwa [Nat.sub_add_cancel (by omega)] at hle

/-- **The unit norms of a defect-one radicand equal `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
`q ^ e = 2`.** Here `a` is a unit of defect exponent `1`, `e = v_K(2)` and `q` is the cardinality
of the residue field. -/
theorem unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 =
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      Nat.card 𝓀[K] ^ dyadicLevel K h2 = 2 := by
  have he := dyadicLevel_ne_zero_of_defectExponent_eq h2 ha hd one_pos
  simpa only [Nat.sub_add_cancel (show 1 ≤ 2 * dyadicLevel K h2 by omega),
    Nat.div_eq_of_lt (by decide : 1 < 2), Nat.sub_zero] using
    unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
      h2 ha (d := 1) (by exact_mod_cast hd) odd_one

/-- **The unit norms of a defect-one radicand strictly contain `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
`q ^ e > 2`.** -/
theorem unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 <
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      2 < Nat.card 𝓀[K] ^ dyadicLevel K h2 := by
  have he := dyadicLevel_ne_zero_of_defectExponent_eq h2 ha hd one_pos
  simpa only [Nat.sub_add_cancel (show 1 ≤ 2 * dyadicLevel K h2 by omega),
    Nat.div_eq_of_lt (by decide : 1 < 2), Nat.sub_zero] using
    unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff_of_odd_defectExponent
      h2 ha (d := 1) (by exact_mod_cast hd) odd_one

end TauCeti

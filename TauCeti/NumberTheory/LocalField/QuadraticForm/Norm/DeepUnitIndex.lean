/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.Filtration
public import TauCeti.NumberTheory.LocalField.UnitSquareClasses

import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.NumberTheory.LocalField.QuadraticForm.Norm.UnitQuotient
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# The unit norms of a defect-one radicand and the deep units modulo squares

Let `K` be a nonarchimedean local field with `2 ≠ 0`, put `e = v_K(2)`, and let `q` be the
cardinality of the residue field. The subgroup `U(K, 2e) · (𝒪[K]ˣ)²` has index `q^e` in `𝒪[K]ˣ`
(`TauCeti.relIndex_unitFiltration_two_mul_dyadicLevel_sup_square`). Here `𝒪[K]ˣ` is `U(K, 0)`, and
`U(K, 2e) · (𝒪[K]ˣ)²` is `(U(K, 2e) · (Kˣ)²) ∩ U(K, 0)`, because a unit that is a square in `K` is
the square of a unit.

For a unit radicand `a` of defect exponent `d = 1`, the deep units `U(K, 2e - d + 1) = U(K, 2e)`
are norms from `K(√a)`, and so is every square. The unit norms have index two in `𝒪[K]ˣ`. So the
containment `U(K, 2e) · (𝒪[K]ˣ)² ⊆ N(K(√a)ˣ) ∩ 𝒪[K]ˣ` is an equality exactly when `q^e = 2`, as
over `ℚ₂`, and is strict as soon as `q^e > 2`. In the strict case the containment half of the
norm-filtration calculation does not by itself determine the unit norms, and the defect
computation has to close the difference. For `K = ℚ₂(√2)` the index of
`U(K, 4) · (𝒪[K]ˣ)²` is `4` (`TauCeti.DyadicSqrtTwo.relIndex_unitFiltration_four_sup_square`).

## Main results

* `TauCeti.unitFiltration_sup_square_le_quadraticNormSubgroup`: for a unit radicand of defect
  exponent one, `U(K, 2e) · (Kˣ)²` consists of norms.
* `TauCeti.unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff`: the unit norms equal
  `U(K, 2e) · (𝒪[K]ˣ)²` exactly when `q^e = 2`.
* `TauCeti.unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff`: the unit norms
  strictly contain `U(K, 2e) · (𝒪[K]ˣ)²` exactly when `q^e > 2`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **`U(K, 2e) · (Kˣ)²` consists of norms from `K(√a)`** for a unit `a` of defect exponent `1`,
where `e = v_K(2)`: every element of `U(K, 2e) = U(K, 2e - 1 + 1)` is a norm, and so is every
square. -/
theorem unitFiltration_sup_square_le_quadraticNormSubgroup (h2 : (2 : K) ≠ 0) {a : Kˣ}
    (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ ≤
      quadraticNormSubgroup (a : K) := by
  have he := dyadicLevel_ne_zero_of_defectExponent_eq h2 ha (d := 1) (by exact_mod_cast hd) one_pos
  have hle := unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha (d := 1)
    (by exact_mod_cast hd)
  rw [Nat.sub_add_cancel (show 1 ≤ 2 * dyadicLevel K h2 by omega)] at hle
  exact sup_le hle (square_le_quadraticNormSubgroup (a : K))

/-- **The unit norms of a defect-one radicand equal `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
`q ^ e = 2`.** Here `a` is a unit of defect exponent `1`, `e = v_K(2)` and `q` is the cardinality
of the residue field. The unit norms have index two in `𝒪[K]ˣ`, while `U(K, 2e) · (𝒪[K]ˣ)²` has
index `q ^ e` and is contained in them. -/
theorem unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 =
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      Nat.card 𝓀[K] ^ dyadicLevel K h2 = 2 := by
  have hsub := inf_le_inf_right (unitFiltration K 0)
    (unitFiltration_sup_square_le_quadraticNormSubgroup h2 ha hd)
  have hN : (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 := by
    rw [Subgroup.relIndex,
      index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent hd
        odd_one, quadraticNormSubgroup_index_eq_two_of_not_isSquare h2
        (not_isSquare_of_defectExponent_eq hd)]
  have hT := relIndex_unitFiltration_two_mul_dyadicLevel_sup_square h2
  constructor
  · intro h
    have hidx := congrArg (fun H : Subgroup Kˣ ↦ H.relIndex (unitFiltration K 0)) h
    simpa only [Subgroup.inf_relIndex_right, hT, hN] using hidx
  · intro hq2
    -- With `q ^ e = 2` the two subgroups have the same index in `U(K, 0)`, so they are equal.
    have h := Subgroup.relIndex_mul_relIndex _ _ (unitFiltration K 0) hsub inf_le_right
    rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right, hN, hT, hq2] at h
    exact le_antisymm hsub (Subgroup.relIndex_eq_one.mp (by omega))

/-- **The unit norms of a defect-one radicand strictly contain `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
`q ^ e > 2`.** Here `a` is a unit of defect exponent `1`, `e = v_K(2)` and `q` is the cardinality
of the residue field. Since `e ≥ 1` and `q ≥ 2`, this is the failure of the equality case
`q ^ e = 2`. -/
theorem unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 <
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      2 < Nat.card 𝓀[K] ^ dyadicLevel K h2 := by
  have he := dyadicLevel_ne_zero_of_defectExponent_eq h2 ha (d := 1) (by exact_mod_cast hd) one_pos
  have h1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hq : Nat.card 𝓀[K] ≤ Nat.card 𝓀[K] ^ dyadicLevel K h2 := Nat.le_self_pow (by omega) _
  rw [lt_iff_le_and_ne, and_iff_right (inf_le_inf_right (unitFiltration K 0)
    (unitFiltration_sup_square_le_quadraticNormSubgroup h2 ha hd)), Ne,
    unitFiltration_sup_square_inf_eq_quadraticNormSubgroup_inf_iff h2 ha hd]
  omega

end TauCeti

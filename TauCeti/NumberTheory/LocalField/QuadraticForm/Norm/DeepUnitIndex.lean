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
# Deep units modulo squares, and the unit norms of a defect-one radicand

Let `K` be a nonarchimedean local field with `2 ≠ 0`, put `e = v_K(2)`, and let `q` be the
cardinality of the residue field. The local square theorem says that `U(K, 2e + 1)` consists of
squares while `U(K, 2e)` does not. This file shows that `U(K, 2e)` meets exactly two square
classes: two nonsquares of `U(K, 2e)` both have the maximal defect exponent `2e`, so they differ by
a square. Since `U(K, 0)` meets `2 q^e` square classes, the subgroup `U(K, 2e) · (𝒪[K]ˣ)²` has
index `q^e` in `𝒪[K]ˣ`. Here `𝒪[K]ˣ` is `U(K, 0)`, and `U(K, 2e) · (𝒪[K]ˣ)²` is
`(U(K, 2e) · (Kˣ)²) ∩ U(K, 0)`, because a unit that is a square in `K` is the square of a unit.

For a unit radicand `a` of defect exponent `d = 1`, the deep units `U(K, 2e - d + 1) = U(K, 2e)`
are norms from `K(√a)`, and so is every square. The unit norms have index two in `𝒪[K]ˣ`. So the
containment `U(K, 2e) · (𝒪[K]ˣ)² ⊆ N(K(√a)ˣ) ∩ 𝒪[K]ˣ` is an equality exactly when `q^e = 2`, as
over `ℚ₂`, and is strict as soon as `q^e > 2`. In the strict case the containment half of the
norm-filtration calculation does not by itself determine the unit norms, and the defect
computation has to close the difference. For `K = ℚ₂(√2)` the index of
`U(K, 4) · (𝒪[K]ˣ)²` is `4` (`TauCeti.DyadicSqrtTwo.relIndex_unitFiltration_four_sup_square`).

## Main results

* `TauCeti.isSquare_mul_of_mem_unitFiltration`: two nonsquares of `U(K, 2e)` differ by a square.
* `TauCeti.relIndex_square_unitFiltration_two_mul_dyadicLevel`: `U(K, 2e)` meets exactly two
  square classes.
* `TauCeti.relIndex_unitFiltration_sup_square`: `U(K, 2e) · (𝒪[K]ˣ)²` has index `q^e` in
  `𝒪[K]ˣ`.
* `TauCeti.unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff`: for a unit radicand
  of defect exponent one, the unit norms strictly contain `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
  `q^e > 2`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The nonsquares of `U(K, 2 v_K(2))` form one square class.** Both have the maximal defect
exponent `2 v_K(2)`, so they differ by a square. -/
theorem isSquare_mul_of_mem_unitFiltration (h2 : (2 : K) ≠ 0) {u w : Kˣ}
    (hu : u ∈ unitFiltration K (2 * dyadicLevel K h2))
    (hw : w ∈ unitFiltration K (2 * dyadicLevel K h2)) (hu' : ¬IsSquare u) (hw' : ¬IsSquare w) :
    IsSquare (u * w) := by
  rw [dyadicLevel_def] at hu hw
  have hval {x : Kˣ} (hx : x ∈ unitFiltration K (2 * natCastValuation K 2 h2)) :
      valuation K (x : K) = 1 :=
    (mem_unitFiltration_zero x).mp (unitFiltration_antitone (Nat.zero_le _) hx)
  exact isSquare_mul_of_defectExponent_eq_two_mul h2 (hval hu) (hval hw)
    (defectExponent_eq_two_mul_natCastValuation_of_mem_unitFiltration h2 hu hu')
    (defectExponent_eq_two_mul_natCastValuation_of_mem_unitFiltration h2 hw hw')

/-- **`U(K, 2 v_K(2))` meets exactly two square classes**: the squares have index two in
`U(K, 2 v_K(2))`. -/
theorem relIndex_square_unitFiltration_two_mul_dyadicLevel (h2 : (2 : K) ≠ 0) :
    (Subgroup.square Kˣ).relIndex (unitFiltration K (2 * dyadicLevel K h2)) = 2 := by
  obtain ⟨u, hu, hnsq⟩ := exists_mem_unitFiltration_not_isSquare h2
  rw [← dyadicLevel_def] at hu
  refine Subgroup.relIndex_eq_two_iff.2 ⟨u, hu, fun b hb ↦ ?_⟩
  rw [xor_iff_not_iff, Subgroup.mem_square, Subgroup.mem_square]
  intro h
  by_cases hb' : IsSquare b
  · exact hnsq (by simpa using (h.2 hb').mul hb'.inv)
  · exact hb' (h.1 (isSquare_mul_of_mem_unitFiltration h2 hb hu hb' hnsq))

/-- **`U(K, 2 v_K(2)) · (𝒪[K]ˣ)²` has index `q ^ v_K(2)` in `𝒪[K]ˣ`**, where `q` is the
cardinality of the residue field. The subgroup is written as `U(K, 2 v_K(2)) · (Kˣ)²` intersected
with `U(K, 0) = 𝒪[K]ˣ`, as `Subgroup.relIndex` does. -/
theorem relIndex_unitFiltration_sup_square (h2 : (2 : K) ≠ 0) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ).relIndex
        (unitFiltration K 0) = Nat.card 𝓀[K] ^ dyadicLevel K h2 := by
  set U := unitFiltration K (2 * dyadicLevel K h2)
  set S := Subgroup.square Kˣ
  have hU : U ≤ unitFiltration K 0 := unitFiltration_antitone (Nat.zero_le _)
  have hUS : S.relIndex U = 2 := relIndex_square_unitFiltration_two_mul_dyadicLevel h2
  have hsup : S.relIndex (U ⊔ S) = 2 := by rw [Subgroup.relIndex_sup_right, hUS]
  -- The squares also have index two in the intermediate `(U ⊔ S) ⊓ U(K, 0)`.
  have hmid : S.relIndex ((U ⊔ S) ⊓ unitFiltration K 0) = 2 := by
    have hne : S.relIndex ((U ⊔ S) ⊓ unitFiltration K 0) ≠ 0 :=
      mt (Subgroup.relIndex_eq_zero_of_le_right inf_le_left) (by rw [hsup]; norm_num)
    refine le_antisymm
      (hsup ▸ Subgroup.relIndex_le_of_le_right inf_le_left (by rw [hsup]; norm_num))
      (hUS ▸ Subgroup.relIndex_le_of_le_right (le_inf le_sup_left hU) hne)
  have h := Subgroup.relIndex_inf_mul_relIndex S (U ⊔ S) (unitFiltration K 0)
  rw [hmid, inf_eq_left.mpr le_sup_right, relIndex_square_unitFiltration_zero K h2,
    ← dyadicLevel_def] at h
  exact Nat.eq_of_mul_eq_mul_left two_pos h

/-- **The unit norms of a defect-one radicand strictly contain `U(K, 2e) · (𝒪[K]ˣ)²` exactly when
`q ^ e > 2`.** Here `a` is a unit of defect exponent `1`, `e = v_K(2)` and `q` is the cardinality
of the residue field. Every element of `U(K, 2e)` and every square is a norm from `K(√a)`. The
unit norms have index two in `𝒪[K]ˣ`, while `U(K, 2e) · (𝒪[K]ˣ)²` has index `q ^ e`. -/
theorem unitFiltration_sup_square_inf_lt_quadraticNormSubgroup_inf_iff (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) (hd : defectExponent a = 1) :
    (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓ unitFiltration K 0 <
        quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 ↔
      2 < Nat.card 𝓀[K] ^ dyadicLevel K h2 := by
  have hnsq : ¬IsSquare a := not_isSquare_of_defectExponent_eq hd
  -- A unit of odd defect exponent `1` forces `v_K(2) ≥ 1`.
  have he : 1 ≤ 2 * dyadicLevel K h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha hnsq
    rw [hd, ← dyadicLevel_def] at h
    exact_mod_cast h
  have hle := unitFiltration_le_quadraticNormSubgroup_of_defectExponent_eq h2 ha (d := 1)
    (by exact_mod_cast hd)
  rw [Nat.sub_add_cancel he] at hle
  have hsub : (unitFiltration K (2 * dyadicLevel K h2) ⊔ Subgroup.square Kˣ) ⊓
      unitFiltration K 0 ≤ quadraticNormSubgroup (a : K) ⊓ unitFiltration K 0 :=
    inf_le_inf_right _ (sup_le hle (square_le_quadraticNormSubgroup (a : K)))
  have hN : (quadraticNormSubgroup (a : K)).relIndex (unitFiltration K 0) = 2 := by
    rw [Subgroup.relIndex,
      index_subgroupOf_unitFiltration_eq_quadraticNormSubgroup_index_of_odd_defectExponent hd
        odd_one, quadraticNormSubgroup_index_eq_two_of_not_isSquare h2 hnsq]
  have hT := relIndex_unitFiltration_sup_square h2
  constructor
  · intro hlt
    by_contra hq
    -- With `q ^ e = 2` the two subgroups have the same index in `U(K, 0)`, so they are equal.
    have hq2 : Nat.card 𝓀[K] ^ dyadicLevel K h2 = 2 := by
      have h1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
      have h2' : Nat.card 𝓀[K] ≤ Nat.card 𝓀[K] ^ dyadicLevel K h2 :=
        Nat.le_self_pow (by omega) _
      omega
    have h := Subgroup.relIndex_mul_relIndex _ _ (unitFiltration K 0) hsub inf_le_right
    rw [Subgroup.inf_relIndex_right, Subgroup.inf_relIndex_right, hN, hT, hq2] at h
    exact hlt.not_ge (Subgroup.relIndex_eq_one.mp (by omega))
  · intro hq
    refine lt_of_le_of_ne hsub fun h ↦ ?_
    have hidx := congrArg (fun H : Subgroup Kˣ ↦ H.relIndex (unitFiltration K 0)) h
    simp only [Subgroup.inf_relIndex_right, hT, hN] at hidx
    omega

end TauCeti

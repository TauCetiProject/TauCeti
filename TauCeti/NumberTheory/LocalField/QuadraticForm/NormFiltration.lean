/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.NormSubgroup
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect
public import TauCeti.NumberTheory.LocalField.Squares

/-!
# Deep units are quadratic norms

Let `a` be a nonsquare unit of a nonarchimedean local field, with quadratic defect exponent
`d`, and put `e = v_K(2)`. Every element of `U(K, 2e - d + 1)` is a norm from `K(√a)`.
This includes units of odd defect in residue characteristic two, where the depth is smaller
than the depth `2e + 1` at which every principal unit is a square.

The result is stated using the norm subgroup of the quadratic algebra and the canonical unit
filtration. It supplies the containment half of the norm-filtration calculation; sharpness and
the norm index are separate questions.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- If a local unit has finite quadratic defect exponent `d`, then every principal unit of
depth `2 v_K(2) - d + 1` is a norm from its quadratic extension. -/
theorem unitFiltration_le_quadraticNormSubgroup_of_defectExponent (h2 : (2 : K) ≠ 0)
    {a : Kˣ} (ha : valuation K (a : K) = 1) {d : ℕ}
    (hd : defectExponent a = (d : ℤ)) :
    unitFiltration K (2 * natCastValuation K 2 h2 - d + 1) ≤ quadraticNormSubgroup (a : K) := by
  have hnsq : ¬IsSquare a := by
    rw [← defectExponent_eq_top_iff, hd]
    exact WithTop.coe_ne_top
  have hdle : d ≤ 2 * natCastValuation K 2 h2 := by
    have h := defectExponent_le_two_mul_natCastValuation h2 ha hnsq
    rw [hd, WithTop.coe_le_coe] at h
    exact_mod_cast h
  have hsquares : unitFiltration K (2 * natCastValuation K 2 h2 + 1) ≤
      Subgroup.square Kˣ := by simpa using unitFiltration_le_square h2
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · simpa using hsquares.trans (square_le_quadraticNormSubgroup (a : K))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ1 : valuation K (π : K) < 1 :=
    Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ
  obtain ⟨ξ, x, hx, hxd⟩ := exists_defectExponent_eq hnsq
  rw [hd, WithTop.coe_inj] at hxd
  have hxv : valuation K (x : K) = valuation K (π : K) ^ d := by
    have h := (toAdd_normalizedValuation_eq_iff_valuation_eq_zpow
      (normalizedValuation_irreducible hπ) (d : ℤ) x).mp hxd
    simpa only [zpow_natCast, Units.val_mk0] using h
  -- An optimal square approximation of a unit at positive depth is itself a unit.
  have hξv : valuation K (ξ ^ 2) = 1 := by
    have heq : ξ ^ 2 = (a : K) - (x : K) := by rw [hx]; ring
    rw [heq, Valuation.map_sub_eq_of_lt_left _ (ha ▸
      (hxv ▸ pow_lt_one₀ zero_le hπ1 hdpos.ne')), ha]
  have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξv
  intro b hb
  have hbv := ((mem_unitFiltration_iff_valuation_le hπ).mp hb).2
  -- The discriminant of the norm equation is a square by the local square theorem.
  let c : K := -(x : K) * ((b : K) - 1) / ξ ^ 2
  have hcv : valuation K c ≤ valuation K (π : K) ^ (2 * natCastValuation K 2 h2 + 1) := by
    dsimp [c]
    rw [map_div₀, map_mul, Valuation.map_neg, hξv, div_one, hxv]
    calc
      _ ≤ valuation K (π : K) ^ d *
          valuation K (π : K) ^ (2 * natCastValuation K 2 h2 - d + 1) :=
        mul_le_mul' le_rfl hbv
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hc1 : valuation K c < 1 :=
    hcv.trans_lt (pow_lt_one₀ zero_le hπ1 (by omega))
  have hu0 : 1 + c ≠ 0 := by
    intro h
    have hval := (valuation K).map_one_add_of_lt hc1
    simp [h] at hval
  let u : Kˣ := Units.mk0 (1 + c) hu0
  have humem : u ∈ unitFiltration K (2 * natCastValuation K 2 h2 + 1) := by
    rw [mem_unitFiltration_succ_valuation _ _ π hπ]
    simpa [u] using hcv
  obtain ⟨z, hz⟩ := Subgroup.mem_square.mp (hsquares humem)
  have hz' : (z : K) ^ 2 = 1 + c := by
    simpa [u, sq] using (congrArg (fun w : Kˣ => (w : K)) hz).symm
  -- Solve `N(1 + t(ξ + √a)) = b` using this square root.
  let t : K := ξ * ((z : K) - 1) / (ξ ^ 2 - a)
  have hden : ξ ^ 2 - (a : K) ≠ 0 := by
    intro h
    apply x.ne_zero
    rw [hx, ← sub_eq_zero.mp h, sub_self]
  have hnorm : (1 + ξ * t) ^ 2 - (a : K) * t ^ 2 = b := by
    dsimp [c] at hz'
    dsimp [t]
    rw [hx] at hz'
    field_simp at hz' ⊢
    linear_combination (ξ ^ 2 - (a : K)) * hz'
  apply (mem_quadraticNormSubgroup_iff_exists_norm_eq _ _).mpr
  exact ⟨⟨1 + ξ * t, t⟩, by simpa [QuadraticAlgebra.norm_def, sq, mul_assoc] using hnorm⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.Squares

/-!
# The sharp square depth in `ℚ₂`

The principal units `1 + 8ℤ₂` are squares, while `5 ∈ 1 + 4ℤ₂` is not a square.
These examples specialize the sharp local square theorem at its boundary depth.
-/

public section

open ValuativeRel

namespace Padic

open TauCeti

/-- Every dyadic unit of depth three, that is every element of `1 + 8ℤ₂`, is a square. -/
theorem unitFiltration_three_le_square :
    unitFiltration ℚ_[2] 3 ≤ Subgroup.square ℚ_[2]ˣ := by
  have h := unitFiltration_le_square (K := ℚ_[2]) (by norm_num : (2 : ℚ_[2]) ≠ 0)
  rw [dyadicLevel_def, _root_.Padic.natCastValuation_self] at h
  exact h

/-- The unit `5` belongs to `1 + 4ℤ₂`. -/
theorem five_mem_unitFiltration_two :
    Units.mk0 (5 : ℚ_[2]) (by norm_num) ∈ unitFiltration ℚ_[2] 2 := by
  rw [mem_unitFiltration_iff_valuation_sub_one_le (by decide : 2 ≠ 0)
    (TauCeti.Padic.irreducible_natCast_self 2)]
  norm_num only [Units.val_mk0]
  have htwo : ((2 : 𝒪[ℚ_[2]]) : ℚ_[2]) = 2 := map_ofNat (Subring.subtype 𝒪[ℚ_[2]]) 2
  rw [htwo, show (4 : ℚ_[2]) = 2 ^ 2 by norm_num, map_pow]

/-- The square-depth theorem cannot be lowered to depth two: `5` is an explicit witness. -/
theorem not_unitFiltration_two_le_square :
    ¬ unitFiltration ℚ_[2] 2 ≤ Subgroup.square ℚ_[2]ˣ := by
  intro h
  have hs := Subgroup.mem_square.1 (h five_mem_unitFiltration_two)
  exact not_isSquare_five (by
    obtain ⟨u, hu⟩ := hs
    exact ⟨(u : ℚ_[2]), congrArg Units.val hu⟩)

end Padic

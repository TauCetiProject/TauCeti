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
Together with `Padic.not_isSquare_five`, the explicit membership witnesses sharpness of the
generic square-depth theorem at depth two. At depth three, the generic
`TauCeti.unitFiltration_le_square` applies directly to `ℚ₂`.
-/

public section

open ValuativeRel

namespace Padic

open TauCeti

/-- The unit `5` belongs to `1 + 4ℤ₂`. -/
theorem mk0_five_mem_unitFiltration_two :
    Units.mk0 (5 : ℚ_[2]) (by norm_num) ∈ unitFiltration ℚ_[2] 2 := by
  rw [mem_unitFiltration_iff_valuation_sub_one_le (by decide : 2 ≠ 0)
    (TauCeti.Padic.irreducible_natCast_self 2)]
  norm_num only [Units.val_mk0]
  have htwo : ((2 : 𝒪[ℚ_[2]]) : ℚ_[2]) = 2 := map_ofNat (Subring.subtype 𝒪[ℚ_[2]]) 2
  have hfour : (4 : ℚ_[2]) = 2 ^ 2 := by norm_num
  rw [htwo, hfour, map_pow]

end Padic

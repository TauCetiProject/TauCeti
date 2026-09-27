/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.WidthRatio

/-!
# Cusp ramification indices in a tower of Fuchsian groups

The ratio of compatible normalized cusp widths is a canonical positive natural number. For
three nested groups this index multiplies, giving the exponent of the composite cusp map.

The normalization of cusp widths follows Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.Subgroup.CuspDatum

variable {Δ Γ Θ : Subgroup PSL(2, ℝ)}

/-- The integral ratio between two positive normalized cusp widths is unique. -/
theorem width_factor_unique (D : Δ.CuspDatum) (E : Γ.CuspDatum) {m n : ℕ}
    (hm : D.width = m * E.width) (hn : D.width = n * E.width) : m = n := by
  have h : (m : ℝ) * E.width = (n : ℝ) * E.width := hm.symm.trans hn
  exact_mod_cast (mul_right_cancel₀ E.width_pos.ne' h)

/-- The exponent of the cusp width ratio multiplies in a subgroup tower. -/
theorem width_factor_tower (D : Δ.CuspDatum) (E : Γ.CuspDatum) (F : Θ.CuspDatum)
    {m n : ℕ} (hm : D.width = m * E.width) (hn : E.width = n * F.width) :
    D.width = ((m * n : ℕ) : ℝ) * F.width := by
  rw [hm, hn]
  simp only [Nat.cast_mul, mul_assoc]

/-- The positive integer by which the cusp width grows under a subgroup inclusion, for
normalized cusp data with the same representative and scaling. -/
def widthIndex (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling) : ℕ :=
  (exists_width_eq_nat_mul h D E hc hσ).choose

/-- The cusp width ratio is positive. -/
theorem widthIndex_pos (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling) :
    0 < widthIndex h D E hc hσ :=
  (exists_width_eq_nat_mul h D E hc hσ).choose_spec.1

/-- The smaller group's width is the cusp index times the larger group's width. -/
theorem width_eq_widthIndex_mul (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling) :
    D.width = widthIndex h D E hc hσ * E.width :=
  (exists_width_eq_nat_mul h D E hc hσ).choose_spec.2

/-- The cusp index of the identity inclusion is one. -/
@[simp]
theorem widthIndex_self (D : Δ.CuspDatum) :
    widthIndex (le_refl Δ) D D rfl rfl = 1 := by
  apply width_factor_unique D D (width_eq_widthIndex_mul (le_refl Δ) D D rfl rfl)
  simp

/-- The cusp ramification index multiplies in a tower of subgroup inclusions. -/
theorem widthIndex_tower (h : Δ ≤ Γ) (k : Γ ≤ Θ)
    (D : Δ.CuspDatum) (E : Γ.CuspDatum) (F : Θ.CuspDatum)
    (hcDE : D.cusp = E.cusp) (hcEF : E.cusp = F.cusp)
    (hσDE : D.scaling = E.scaling) (hσEF : E.scaling = F.scaling) :
    widthIndex (h.trans k) D F (hcDE.trans hcEF) (hσDE.trans hσEF) =
      widthIndex h D E hcDE hσDE * widthIndex k E F hcEF hσEF := by
  apply width_factor_unique D F
    (width_eq_widthIndex_mul (h.trans k) D F (hcDE.trans hcEF) (hσDE.trans hσEF))
  exact width_factor_tower D E F
    (width_eq_widthIndex_mul h D E hcDE hσDE)
    (width_eq_widthIndex_mul k E F hcEF hσEF)

end TauCeti.Subgroup.CuspDatum

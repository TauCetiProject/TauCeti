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
three nested groups this index multiplies, giving the exponent of the composite cusp map. The
index is also the relative index of the two cusp stabilizers, so it does not depend on the
chosen scaling.

The normalization of cusp widths follows Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open MulAction UpperHalfPlane
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

/-- **The cusp width index is the index of the cusp stabilizers.** For compatible normalized
cusp data, the factor by which the width grows under `Δ ≤ Γ` is the relative index of `Δ` in the
stabilizer of the cusp in `Γ`, that is, `[stabilizer Γ c : stabilizer Δ c]`. The generator for
`Δ` is the `n`-th power of the generator for `Γ`, and the infinite cyclic stabilizer for `Γ`
contains its subgroup of `n`-th powers with index `n`. -/
theorem widthIndex_eq_relIndex (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling) :
    widthIndex h D E hc hσ = (Δ.subgroupOf Γ).relIndex (stabilizer Γ E.cusp) := by
  set n := widthIndex h D E hc hσ
  have hgen : (⟨D.generator, h D.generator.2⟩ : Γ) = E.generator ^ (n : ℤ) := by
    refine Subtype.ext ((MulAut.conj E.scaling).injective ?_)
    rw [MulAut.conj_apply, MulAut.conj_apply, Subgroup.coe_zpow,
      E.scaling_mul_generator_zpow_mul_inv, ← hσ, Subgroup.coe_mk,
      D.scaling_mul_generator_mul_inv, width_eq_widthIndex_mul h D E hc hσ, Int.cast_natCast]
  -- the elements of `Δ` fixing the cusp are the powers of the generator for `Δ`
  have hinf : Δ.subgroupOf Γ ⊓ stabilizer Γ E.cusp =
      Subgroup.zpowers (E.generator ^ (n : ℤ)) := by
    apply le_antisymm
    · rintro g ⟨hgΔ, hgs⟩
      have : (⟨g, hgΔ⟩ : Δ) ∈ stabilizer Δ D.cusp := by
        simpa [mem_stabilizer_iff, Subgroup.smul_def, hc] using hgs
      obtain ⟨k, hk⟩ := D.mem_stabilizer_iff.mp this
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [← hgen]
      exact Subtype.ext (by simpa using congrArg Subtype.val hk)
    · rw [Subgroup.zpowers_le, ← hgen]
      refine ⟨D.generator.2, ?_⟩
      simpa [mem_stabilizer_iff, Subgroup.smul_def, hc] using D.generator_mem_stabilizer
  rw [← Subgroup.inf_relIndex_right, hinf, ← E.zpowers_generator, Subgroup.relIndex_zpowers_zpow,
    E.orderOf_generator_eq_zero]
  simp

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

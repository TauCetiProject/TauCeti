/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Coordinate
public import TauCeti.Analysis.Complex.Periodic

/-!
# Cusp widths under subgroup inclusion

For normalized cusp data of `Δ ≤ Γ` with the same boundary point and scaling, the width for
`Δ` is a positive integer multiple of the width for `Γ`. In the corresponding coordinates,
the map of cusp quotients is therefore the power map `q ↦ q ^ n`. This is the local input for
computing ramification at cusps of maps between compactified Fuchsian quotients.

The integer is forced by the full stabilizers: the primitive generator for `Δ` lies in the
cyclic stabilizer for `Γ`. The argument does not require finite index of `Δ` in `Γ`.

This follows the cusp-width convention of Diamond and Shurman, *A First Course in Modular
Forms*, §2.4.
-/

public noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MulAction UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.Subgroup.CuspDatum

variable {Δ Γ : Subgroup PSL(2, ℝ)}

/-- With a common scaling, the width for a subgroup is a positive integral multiple of the
width for the larger group. The integer is the exponent of the smaller cusp generator in the
larger cusp stabilizer. -/
theorem exists_width_eq_nat_mul (h : Δ ≤ Γ) (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    (hc : D.cusp = E.cusp) (hσ : D.scaling = E.scaling) :
    ∃ n : ℕ, 0 < n ∧ D.width = n * E.width := by
  let g : Γ := ⟨D.generator, h D.generator.property⟩
  have hg : g ∈ stabilizer Γ E.cusp := by
    apply MulAction.mem_stabilizer_iff.mpr
    simpa only [Subgroup.smul_def, ← hc] using
      (MulAction.mem_stabilizer_iff.mp D.generator_mem_stabilizer)
  obtain ⟨k, hk⟩ := E.mem_stabilizer_iff_conj.mp hg
  have hwidth : D.width = (k : ℝ) * E.width := by
    apply upperRightHom_injective
    rw [← D.scaling_mul_generator_mul_inv, hσ]
    exact hk
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) :=
      (mul_pos_iff_of_pos_right E.width_pos).mp (hwidth ▸ D.width_pos)
    exact_mod_cast this
  refine ⟨k.toNat, by omega, ?_⟩
  have hcast : (k.toNat : ℝ) = k := by
    exact_mod_cast Int.toNat_of_nonneg hkpos.le
  rw [hcast]
  exact hwidth

/-- A positive integral multiple of a cusp width bounds that width from above. -/
theorem width_le_of_width_eq_nat_mul (D : Δ.CuspDatum) (E : Γ.CuspDatum)
    {n : ℕ} (hw : D.width = n * E.width) {A : ℝ} (hD : D.width ≤ A) :
    E.width ≤ A := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn
    simp only [hn, Nat.cast_zero, zero_mul] at hw
    exact D.width_pos.ne' hw)
  calc
    E.width = 1 * E.width := (one_mul _).symm
    _ ≤ (n : ℝ) * E.width := mul_le_mul_of_nonneg_right (by exact_mod_cast hn)
      E.width_pos.le
    _ = D.width := hw.symm
    _ ≤ A := hD

/-- The larger group's q-coordinate is the `n`-th power of the smaller group's coordinate
when their normalized widths differ by the factor `n`. -/
theorem coordinate_pow_eq (D : Δ.CuspDatum) (E : Γ.CuspDatum) {n : ℕ}
    (hσ : D.scaling = E.scaling)
    (hw : D.width = n * E.width) (z : ℍ) :
    coordinate D z ^ n = coordinate E z := by
  have hn : n ≠ 0 := by
    intro hn
    simp only [hn, Nat.cast_zero, zero_mul] at hw
    exact D.width_pos.ne' hw
  rw [coordinate_apply, coordinate_apply, hσ, hw]
  exact TauCeti.Periodic.qParam_nat_mul_pow hn _

end TauCeti.Subgroup.CuspDatum

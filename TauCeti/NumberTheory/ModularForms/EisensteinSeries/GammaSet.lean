/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs

/-!
# The residues of coprime integer pairs

Mathlib's `EisensteinSeries.gammaSet N 1 a` is the set of coprime integer pairs reducing to
`a : Fin 2 → ZMod N`. This file characterizes the residues `a` for which it is nonempty: they are
exactly the bottom rows modulo `N` of the inverses of matrices in `SL(2, ℤ)`, the form in which
residues index the cusps of `Γ(N)`. The set of such residues is closed under negation.

## Main results

* `TauCeti.EisensteinSeries.nonempty_gammaSet_iff`: `gammaSet N 1 a` is nonempty exactly when `a`
  is the bottom row modulo `N` of `γ⁻¹` for some `γ ∈ SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.nonempty_gammaSet_neg_iff`: `gammaSet N 1 (-a)` is nonempty exactly
  when `gammaSet N 1 a` is.
-/

public section

open Matrix Matrix.SpecialLinearGroup
open _root_.EisensteinSeries
open scoped MatrixGroups

namespace TauCeti.EisensteinSeries

variable {N : ℕ}

/-- A residue pair lifts to a coprime integer pair exactly when it is the bottom row modulo `N`
of the inverse of a matrix in `SL(2, ℤ)`. -/
theorem nonempty_gammaSet_iff (a : Fin 2 → ZMod N) :
    Nonempty (gammaSet N 1 a) ↔
      ∃ γ : SL(2, ℤ), ((![0, 1] : Fin 2 → ZMod N) ᵥ* (γ⁻¹ : SL(2, ℤ)) : Fin 2 → ZMod N) = a := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨σ, hσ0, hσ1⟩ := (Int.isCoprime_iff_gcd_eq_one.mpr hx.2).exists_SL2_row 1
    refine ⟨σ⁻¹, ?_⟩
    rw [inv_inv]
    ext i
    fin_cases i <;> simpa [vecMul, dotProduct, hσ0, hσ1] using congrFun hx.1 _
  · rintro ⟨γ, rfl⟩
    refine ⟨⟨fun i ↦ (γ⁻¹ : SL(2, ℤ)) 1 i, ?_, ?_⟩⟩
    · ext i
      fin_cases i <;> simp [vecMul, dotProduct, adjugate_fin_two]
    · refine Int.isCoprime_iff_gcd_eq_one.mp ⟨-(γ⁻¹ : SL(2, ℤ)) 0 1, (γ⁻¹ : SL(2, ℤ)) 0 0, ?_⟩
      have := (γ⁻¹ : SL(2, ℤ)).det_coe
      rw [det_fin_two] at this
      linear_combination this

/-- The residues of coprime integer pairs are closed under negation. -/
theorem nonempty_gammaSet_neg_iff (a : Fin 2 → ZMod N) :
    Nonempty (gammaSet N 1 (-a)) ↔ Nonempty (gammaSet N 1 a) := by
  suffices h : ∀ a : Fin 2 → ZMod N, Nonempty (gammaSet N 1 a) → Nonempty (gammaSet N 1 (-a)) by
    exact ⟨fun ha ↦ neg_neg a ▸ h _ ha, h a⟩
  rintro a ⟨x, hx⟩
  refine ⟨⟨-x, ?_, ?_⟩⟩
  · ext i
    simpa using congrArg Neg.neg (congrFun hx.1 i)
  · simpa using hx.2

end TauCeti.EisensteinSeries

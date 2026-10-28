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
residues index the cusps of `Γ(N)`, and exactly the residues of the integer pairs whose gcd is
prime to `N`. The set of such residues is closed under negation.

## Main results

* `TauCeti.EisensteinSeries.nonempty_gammaSet_iff`: `gammaSet N 1 a` is nonempty exactly when `a`
  is the bottom row modulo `N` of `γ⁻¹` for some `γ ∈ SL(2, ℤ)`.
* `TauCeti.EisensteinSeries.nonempty_gammaSet_intCast_iff`: the residue of an integer pair `x`
  lifts to a coprime pair exactly when `gcd(x₀, x₁)` is prime to `N`.
* `TauCeti.EisensteinSeries.nonempty_gammaSet_iff_coprime_val`: the same, read on the least
  nonnegative representatives of a residue pair.
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

/-- An integer pair is congruent modulo `N` to a coprime pair exactly when the gcd of its entries
is prime to `N`. -/
theorem nonempty_gammaSet_intCast_iff (x : Fin 2 → ℤ) :
    Nonempty (gammaSet N 1 ((↑) ∘ x)) ↔ Nat.Coprime ((x 0).gcd (x 1)) N := by
  constructor
  · rintro ⟨y, hy, hy1⟩
    refine Nat.coprime_of_dvd fun q hq hqx hqN ↦ hq.one_lt.ne' ?_
    have hdvd (i : Fin 2) : (q : ℤ) ∣ y i := by
      have hx : (q : ℤ) ∣ x i := by
        refine (Int.natCast_dvd_natCast.mpr hqx).trans ?_
        fin_cases i
        exacts [Int.gcd_dvd_left .., Int.gcd_dvd_right ..]
      have hN : (N : ℤ) ∣ x i - y i :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (congrFun hy i)
      simpa using dvd_sub hx ((Int.natCast_dvd_natCast.mpr hqN).trans hN)
    rw [← Nat.dvd_one, ← hy1]
    exact Int.dvd_gcd (hdvd 0) (hdvd 1)
  · intro hcop
    set g := (x 0).gcd (x 1)
    -- write `x = g • x'` with `x'` coprime, and move `(g, N)` along an `SL(2, ℤ)` matrix
    obtain ⟨x', hx', hxx'⟩ : ∃ x' : Fin 2 → ℤ, IsCoprime (x' 0) (x' 1) ∧ x = (g : ℤ) • x' := by
      by_cases hg0 : g = 0
      · refine ⟨![1, 0], isCoprime_one_left, ?_⟩
        have := Int.gcd_eq_zero_iff.mp hg0
        ext i
        fin_cases i <;> simp [hg0, this.1, this.2]
      · have : NeZero g := ⟨hg0⟩
        refine ⟨x / (g : ℤ), finGcdMap_div x rfl, ?_⟩
        ext i
        refine (Int.mul_ediv_cancel' ?_).symm
        fin_cases i
        exacts [Int.gcd_dvd_left .., Int.gcd_dvd_right ..]
    obtain ⟨γ, hγ0, hγ1⟩ := hx'.exists_SL2_row 0
    have hw : IsCoprime ((![(g : ℤ), N] : Fin 2 → ℤ) 0) ((![(g : ℤ), N] : Fin 2 → ℤ) 1) := by
      simpa using Nat.isCoprime_iff_coprime.mpr hcop
    refine ⟨⟨![(g : ℤ), N] ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ), ?_,
      Int.isCoprime_iff_gcd_eq_one.mp (hw.vecMulSL γ)⟩⟩
    ext i
    fin_cases i <;> simp [vecMul, dotProduct, hγ0, hγ1, hxx']

/-- A residue pair lifts to a coprime integer pair exactly when the gcd of its least nonnegative
representatives is prime to `N`. -/
theorem nonempty_gammaSet_iff_coprime_val [NeZero N] (a : Fin 2 → ZMod N) :
    Nonempty (gammaSet N 1 a) ↔ Nat.Coprime ((a 0).val.gcd (a 1).val) N := by
  have h := nonempty_gammaSet_intCast_iff (N := N) fun i ↦ ((a i).val : ℤ)
  have ha : ((↑) : ℤ → ZMod N) ∘ (fun i ↦ ((a i).val : ℤ)) = a := by
    ext i
    simp
  rwa [ha, Int.gcd_natCast_natCast] at h

/-- The multiple `k a` of a residue pair lifts to a coprime integer pair exactly when `k` times
the gcd of the least nonnegative representatives of `a` is prime to `N`. -/
theorem nonempty_gammaSet_natCast_smul_iff [NeZero N] (k : ℕ) (a : Fin 2 → ZMod N) :
    Nonempty (gammaSet N 1 ((k : ZMod N) • a)) ↔ Nat.Coprime (k * (a 0).val.gcd (a 1).val) N := by
  have h : ((↑) : ℤ → ZMod N) ∘ (fun i ↦ (k : ℤ) * (a i).val) = (k : ZMod N) • a := by
    ext i
    simp
  rw [← h, nonempty_gammaSet_intCast_iff, Int.gcd_mul_left, Int.natAbs_natCast,
    Int.gcd_natCast_natCast]

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

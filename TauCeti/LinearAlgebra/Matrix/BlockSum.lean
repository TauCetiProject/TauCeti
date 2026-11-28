/-
Copyright (c) 2026 The Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Sums over block matrices and determinant-character averages

This file provides Fubini-style decompositions for finite sums over row-block, column-block, and
four-block matrices over a finite type `R`, together with the averaging identity
`∑ u : Matrix a a R, χ⁻¹ u.det * f u = Fintype.card (GL a R) * v` for functions transforming by
`χ ∘ Matrix.det` on `GL a R`.

## Main results

* `TauCeti.sum_eq_sum_fromRows`: decomposes a sum over `Matrix (N ⊕ n) a R` as a double sum over
  `Matrix.fromRows`.
* `TauCeti.sum_eq_sum_fromCols`: decomposes a sum over `Matrix a (N ⊕ n) R` as a double sum over
  `Matrix.fromCols`.
* `TauCeti.sum_eq_sum_fromBlocks`: decomposes a sum over `Matrix (N ⊕ n) (a ⊕ b) R` as a fourfold
  sum over `Matrix.fromBlocks`.
* `TauCeti.sum_inv_det_mul_eq_card_mul`: evaluates `∑ u : Matrix a a R, χ⁻¹ u.det * f u` when
  `f g.val = χ g.val.det * v` for all `g : GL a R`.

## Provenance

Adapted from `src/New/Determinant/Chain/SquareLaw.lean` (`New.Exchange.sum_eq_sum_fromRows`,
`New.Exchange.sum_eq_sum_fromCols`, `New.Exchange.sum_eq_sum_fromBlocks`,
`New.Exchange.sum_inv_det_mul_eq_card_mul`) in <https://github.com/lsernau/grh-lean> at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

@[expose] public section

namespace TauCeti

open Finset Function Matrix MulChar

/-- A finite sum over `(N ⊕ n) × a` matrices decomposes as a double sum over `Matrix.fromRows`. -/
theorem sum_eq_sum_fromRows {R N n a M : Type*} [Fintype R] [Fintype N] [DecidableEq N]
    [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [AddCommMonoid M]
    (f : Matrix (N ⊕ n) a R → M) :
    ∑ w : Matrix (N ⊕ n) a R, f w =
      ∑ y : Matrix N a R, ∑ z : Matrix n a R, f (fromRows y z) := by
  have h_bij : Bijective fun w : Matrix N a R × Matrix n a R ↦ fromRows w.fst w.snd :=
    ⟨fromRows_inj.uncurry, fun w ↦ ⟨(w.toRows₁, w.toRows₂), w.fromRows_toRows⟩⟩
  exact (h_bij.sum_comp f).symm.trans (Fintype.sum_prod_type _)

/-- A finite sum over `a × (N ⊕ n)` matrices decomposes as a double sum over `Matrix.fromCols`. -/
theorem sum_eq_sum_fromCols {R N n a M : Type*} [Fintype R] [Fintype N] [DecidableEq N]
    [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [AddCommMonoid M]
    (f : Matrix a (N ⊕ n) R → M) :
    ∑ w : Matrix a (N ⊕ n) R, f w =
      ∑ z : Matrix a n R, ∑ y : Matrix a N R, f (fromCols y z) := by
  have h_bij : Bijective fun w : Matrix a N R × Matrix a n R ↦ fromCols w.fst w.snd :=
    ⟨fromCols_inj.uncurry, fun w ↦ ⟨(w.toCols₁, w.toCols₂), w.fromCols_toCols⟩⟩
  exact (h_bij.sum_comp f).symm.trans (Fintype.sum_prod_type_right _)

/-- A finite sum over `(N ⊕ n) × (a ⊕ b)` matrices decomposes as a fourfold sum over
`Matrix.fromBlocks`. -/
theorem sum_eq_sum_fromBlocks {R N n a b M : Type*} [Fintype R] [Fintype N] [DecidableEq N]
    [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [AddCommMonoid M] (f : Matrix (N ⊕ n) (a ⊕ b) R → M) :
    ∑ w : Matrix (N ⊕ n) (a ⊕ b) R, f w =
      ∑ B : Matrix N b R, ∑ A : Matrix N a R, ∑ D : Matrix n b R, ∑ C : Matrix n a R,
        f (fromBlocks A B C D) := by
  simp only [sum_eq_sum_fromRows f, sum_eq_sum_fromCols, fromRows_fromCols_eq_fromBlocks]

/-- If `f g.val = χ g.val.det * v` for all `g : GL a R`, then the sum of `χ⁻¹ u.det * f u` over
all `a × a` matrices `u` over `R` equals `Fintype.card (GL a R) * v`. -/
theorem sum_inv_det_mul_eq_card_mul {R S a : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    [Field S] [Fintype a] [DecidableEq a] (χ : MulChar R S) {f : Matrix a a R → S} {v : S}
    (hf : ∀ g : GL a R, f g.val = χ g.val.det * v) :
    ∑ u : Matrix a a R, χ⁻¹ u.det * f u = Fintype.card (GL a R) * v := by
  have h_ne (g : GL a R) : χ g.val.det ≠ 0 := ((Matrix.isUnits_det_units g).map χ).ne_zero
  calc ∑ u : Matrix a a R, χ⁻¹ u.det * f u
      = ∑ g : GL a R, χ⁻¹ g.val.det * f g.val := by
        refine (Fintype.sum_of_injective _ Units.val_injective _ _ (fun u hu ↦ ?_)
          fun _ ↦ rfl).symm
        rw [χ⁻¹.map_nonunit (mt u.isUnit_iff_isUnit_det.mpr hu), zero_mul]
    _ = ∑ _g : GL a R, v := by
        simp only [hf, MulChar.inv_apply_eq_inv', inv_mul_cancel_left₀ (h_ne _)]
    _ = Fintype.card (GL a R) * v := by simp

end TauCeti

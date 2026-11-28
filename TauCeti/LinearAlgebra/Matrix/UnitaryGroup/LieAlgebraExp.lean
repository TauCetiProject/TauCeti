/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Form
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# Lie algebra and exponential map for the unitary group of a sesquilinear form

For a square complex matrix `J : Matrix n n ℂ`, the real subspace `TauCeti.unitaryLie J` consists
of all matrices `X : Matrix n n ℂ` satisfying `Xᴴ * J + J * X = 0`, the Lie algebra of
`Matrix.unitaryGroupOf J`. Exponentiating `X ∈ unitaryLie J` produces an element
`TauCeti.expUnitaryOf J X` of `Matrix.unitaryGroupOf J` via
`SemiconjBy.exp_neg_mul_mul_exp_eq_self`, giving one-parameter subgroups `t ↦ exp (t • X)` in
`Matrix.unitaryGroupOf J` and preserving commutation with `J`.

## Main definitions and results

* `TauCeti.unitaryLie`: the real submodule `{X : Matrix n n ℂ | Xᴴ * J + J * X = 0}`.
* `TauCeti.mem_unitaryLie_iff`: membership characterization `X ∈ unitaryLie J ↔ Xᴴ * J + J * X = 0`.
* `TauCeti.exp_mem_unitaryGroupOf`: for `X ∈ unitaryLie J`,
  `(Matrix.isUnit_exp X).unit ∈ Matrix.unitaryGroupOf J`.
* `TauCeti.exp_smul_mem_unitaryGroupOf`: for `X ∈ unitaryLie J` and `t : ℝ`,
  `(Matrix.isUnit_exp (t • X)).unit ∈ Matrix.unitaryGroupOf J`.
* `TauCeti.commute_exp_of_commute`: if `Commute J X`, then `Commute J (NormedSpace.exp X)`.

## Provenance

Adapted from `New.unitaryLie` and `New.expU` in `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
file `src/Lib/DiscreteSeries/FlenstedJensen/Defs.lean`).
-/

public section

namespace TauCeti

open Matrix NormedSpace
open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Lie algebra of `Matrix.unitaryGroupOf J`: the real vector space of complex matrices `X`
satisfying `Xᴴ * J + J * X = 0`. -/
def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X : Matrix n n ℂ | Xᴴ * J + J * X = 0}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, conjTranspose_add, add_mul, mul_add] at hX hY ⊢
    calc Xᴴ * J + Yᴴ * J + (J * X + J * Y)
        = (Xᴴ * J + J * X) + (Yᴴ * J + J * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' c {X} hX := by
    simp only [Set.mem_ofPred_eq, conjTranspose_smul, star_trivial, smul_mul_assoc,
      mul_smul_comm, ← smul_add] at hX ⊢
    rw [hX, smul_zero]

/-- Membership in `unitaryLie J` is the equation `Xᴴ * J + J * X = 0`. -/
@[simp]
theorem mem_unitaryLie_iff {J X : Matrix n n ℂ} :
    X ∈ unitaryLie J ↔ Xᴴ * J + J * X = 0 :=
  Iff.rfl

/-- The matrix exponential of any `X ∈ unitaryLie J` lies in `Matrix.unitaryGroupOf J`. -/
theorem exp_mem_unitaryGroupOf {J X : Matrix n n ℂ} (hX : X ∈ unitaryLie J) :
    (Matrix.isUnit_exp X).unit ∈ Matrix.unitaryGroupOf J := by
  have hsemi : SemiconjBy J X (-Xᴴ) :=
    (eq_neg_of_add_eq_zero_right hX).trans (neg_mul Xᴴ J).symm
  simpa [Matrix.mem_unitaryGroupOf_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose] using!
    hsemi.exp_neg_mul_mul_exp_eq_self

/-- One-parameter subgroups: for `X ∈ unitaryLie J` and `t : ℝ`, `exp (t • X)` lies in
`Matrix.unitaryGroupOf J`. -/
theorem exp_smul_mem_unitaryGroupOf {J X : Matrix n n ℂ} (hX : X ∈ unitaryLie J) (t : ℝ) :
    (Matrix.isUnit_exp (t • X)).unit ∈ Matrix.unitaryGroupOf J :=
  exp_mem_unitaryGroupOf ((unitaryLie J).smul_mem t hX)

/-- If `X` commutes with `J`, then `exp (t • X)` commutes with `J` for every `t : ℝ`. -/
theorem commute_exp_smul_of_commute {J X : Matrix n n ℂ} (hcomm : Commute J X) (t : ℝ) :
    Commute J (exp (t • X)) :=
  (hcomm.smul_right t).exp_right

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# The modular-group generators in special linear groups

This module records the matrix of the standard modular-group generator `S` after scalar extension
from `SL₂(ℤ)` to `SL₂(R)`, writes it as a word in three transvections, and shows that `S` and
`U = T S` generate `SL₂(ℤ)`. It also makes explicit the right action `r ↦ r γ` of `S` and `T` on
row vectors over any ring, through the integer cast of the entries; the general composition laws
of that action are in `TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic`.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S`: the scalar extension of
  `ModularGroup.S` has matrix `!![0, -1; 1, 0]`.
* `TauCeti.Matrix.SpecialLinearGroup.modularGroup_S_decompose`: over any commutative ring,
  `S = x₀₁(-1) x₁₀(1) x₀₁(-1)` is a word in three transvections, the word that defines the Weyl
  representative `n_r(-1)` of a rank-one Chevalley group.
* `TauCeti.Matrix.SpecialLinearGroup.mem_op_modularGroup_S_smul_diagonalTorus_iff`: the
  antidiagonal elements of `SL₂(R)` form the right coset `T S` of the diagonal torus.
* `TauCeti.Matrix.SpecialLinearGroup.closure_S_T_mul_S`: `S` and `T S` generate `SL₂(ℤ)`; this
  follows from Mathlib's `Matrix.SpecialLinearGroup.SL2Z_generators` for `S` and `T`, since
  `T = (T S) S⁻¹`.
* `TauCeti.Matrix.SpecialLinearGroup.apply_smul_eq_of_S_smul_of_T_smul`: a function on an
  `SL₂(ℤ)`-set that is invariant under `S` and `T` is invariant under all of `SL₂(ℤ)`.
* `TauCeti.Matrix.SpecialLinearGroup.eq_of_le_of_perm_S_T`: a subgroup `H ≤ K ≤ SL₂(ℤ)` equals `K`
  when a family `R i` (with `R 0 = 1` and meeting `K` only at `0`) has its left cosets `R i · H`
  permuted under left multiplication by `S` and `T`.

* `TauCeti.Matrix.SpecialLinearGroup.vecMul_map_modularGroup_S`,
  `TauCeti.Matrix.SpecialLinearGroup.vecMul_map_modularGroup_T`: `r S = (r₂, -r₁)` and
  `r T = (r₁, r₁ + r₂)`.
* `TauCeti.ModularGroup.mul_T_zpow_apply_apply_zero`,
  `TauCeti.ModularGroup.mul_T_zpow_apply_apply_one`, `TauCeti.ModularGroup.mul_S_apply_apply_zero`,
  `TauCeti.ModularGroup.mul_S_apply_apply_one`, `TauCeti.ModularGroup.neg_mul_S_apply_apply_zero`,
  `TauCeti.ModularGroup.neg_mul_S_apply_apply_one`: the columns of `γ Tⁿ`, `γ S` and `-(γ S)` in
  terms of those of `γ`.
* `Matrix.SpecialLinearGroup.coe_mul_T_zpow`, `Matrix.SpecialLinearGroup.coe_mul_S`: explicit
  `2 × 2` matrices of `γ * T ^ n` and `γ * S` for `γ ∈ SL₂(ℤ)`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- Multiplying `γ ∈ SL₂(ℤ)` on the right by `Tⁿ` adds `n` times the first column to the second. -/
theorem coe_mul_T_zpow (γ : SL(2, ℤ)) (n : ℤ) :
    (↑(γ * ModularGroup.T ^ n) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0, γ 0 0 * n + γ 0 1; γ 1 0, γ 1 0 * n + γ 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
      Fin.sum_univ_two]

/-- Multiplying `γ ∈ SL₂(ℤ)` on the right by `S` swaps the columns and negates the new second
column. -/
theorem coe_mul_S (γ : SL(2, ℤ)) :
    (↑(γ * ModularGroup.S) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 1, -γ 0 0; γ 1 1, -γ 1 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S, Matrix.mul_apply,
      Fin.sum_univ_two]

end Matrix.SpecialLinearGroup

namespace TauCeti.Matrix.SpecialLinearGroup

universe u

/-- The scalar extension of `ModularGroup.S` to a commutative ring has its standard matrix. -/
theorem coe_modularGroup_S {R : Type u} [CommRing R] :
    (((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_matrix_coe, ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The scalar extension of `ModularGroup.S` is the word `x₀₁(-1) x₁₀(1) x₀₁(-1)` in the upper
and lower transvections. -/
theorem modularGroup_S_decompose {R : Type u} [CommRing R] :
    ((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) =
      Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-1) *
        Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) 1 *
        Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-1) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    coe_modularGroup_S]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]

open scoped Pointwise in
/-- The antidiagonal elements of `SL₂(R)` form the right coset `T S` of the diagonal torus `T`,
where `S = !![0, -1; 1, 0]`. -/
theorem mem_op_modularGroup_S_smul_diagonalTorus_iff {R : Type u} [CommRing R] {g : SL(2, R)} :
    g ∈ MulOpposite.op ((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) •
        (Matrix.SpecialLinearGroup.diagonalTorus R 2 : Set SL(2, R)) ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 0 := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_diagonalTorus_iff] at ht
    have h01 : (t : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 := ht (by decide)
    have h10 : (t : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 := ht (by decide)
    simp [MulOpposite.smul_eq_mul_unop, Matrix.mul_apply, Fin.sum_univ_two, h01, h10]
  · rintro ⟨h0, h1⟩
    refine ⟨g * ((ModularGroup.S : SL(2, ℤ)) : SL(2, R))⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Matrix.SpecialLinearGroup.mem_diagonalTorus_iff,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, coe_modularGroup_S,
      Matrix.adjugate_fin_two]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.mul_apply, Fin.sum_univ_two]

open ModularGroup in
/-- `S` and `U = T S` generate `SL₂(ℤ)`. -/
theorem closure_S_T_mul_S : Subgroup.closure {S, T * S} = (⊤ : Subgroup SL(2, ℤ)) := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  have hU : T * S ∈ Subgroup.closure {S, T * S} := Subgroup.subset_closure (by simp)
  -- `T = (T S) S⁻¹`
  exact Set.pair_subset hS (by simpa using mul_mem hU (inv_mem hS))

open ModularGroup in
/-- A function on an `SL₂(ℤ)`-set that is invariant under the generators `S` and `T` is invariant
under all of `SL₂(ℤ)`. -/
theorem apply_smul_eq_of_S_smul_of_T_smul {X α : Type*} [MulAction SL(2, ℤ) X] {f : X → α}
    (hS : ∀ x, f (S • x) = f x) (hT : ∀ x, f (T • x) = f x) (γ : SL(2, ℤ)) (x : X) :
    f (γ • x) = f x := by
  have hγ : γ ∈ Subgroup.closure {S, T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hγ using Subgroup.closure_induction generalizing x with
  | one => rw [one_smul]
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact hS x
    · exact hT x
  | mul g h _ _ hg hh => rw [mul_smul, hg, hh]
  | inv g _ hg => rw [← hg, smul_inv_smul]

open ModularGroup in
/-- If `H ≤ K ≤ SL(2, ℤ)` and `R : Fin n → SL(2, ℤ)` with `R 0 = 1` meets `K` only at `0` while
left multiplication by `S` and `T` permutes the left cosets `R i · H`, then `H = K`. -/
theorem eq_of_le_of_perm_S_T {n : ℕ} [NeZero n] {H K : Subgroup SL(2, ℤ)} (hle : H ≤ K)
    (R : Fin n → SL(2, ℤ)) (hR0 : R 0 = 1) (hRK : ∀ i, R i ∈ K → i = 0)
    (hS : ∃ σ : Equiv.Perm (Fin n), ∀ i, (R (σ i))⁻¹ * S * R i ∈ H)
    (hT : ∃ σ : Equiv.Perm (Fin n), ∀ i, (R (σ i))⁻¹ * T * R i ∈ H) :
    H = K := by
  let M : Subgroup SL(2, ℤ) :=
    { carrier := {g | ∃ σ : Equiv.Perm (Fin n), ∀ i, (R (σ i))⁻¹ * g * R i ∈ H}
      one_mem' := ⟨1, fun i ↦ by simp [one_mem]⟩
      mul_mem' := fun ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ ↦
        ⟨σ₁ * σ₂, fun i ↦ by simpa [mul_assoc] using mul_mem (h₁ (σ₂ i)) (h₂ i)⟩
      inv_mem' := fun ⟨σ, h⟩ ↦
        ⟨σ⁻¹, fun i ↦ by simpa [mul_assoc] using inv_mem (h (σ⁻¹ i))⟩ }
  have hMtop : M = ⊤ := by
    rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
    exact Set.pair_subset hS hT
  refine le_antisymm hle fun k hk ↦ ?_
  obtain ⟨σ, hσ⟩ : k ∈ M := hMtop.symm ▸ Subgroup.mem_top k
  have hi : (R (σ 0))⁻¹ * k ∈ H := by simpa [hR0] using hσ 0
  have hRσ : R (σ 0) ∈ K := by simpa using inv_mem (mul_mem (hle hi) (inv_mem hk))
  simpa [hRK (σ 0) hRσ, hR0] using hi

/-- The row vector `r` multiplied on the right by `S = [[0, -1], [1, 0]]` is `(r₂, -r₁)`. -/
theorem vecMul_map_modularGroup_S {R : Type u} [Ring R] (r : Fin 2 → R) :
    r ᵥ* (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R) = ![r 1, -r 0] := by
  ext i
  fin_cases i <;> simp [ModularGroup.coe_S, vecMul, dotProduct, Fin.sum_univ_two]

/-- The row vector `r` multiplied on the right by `T = [[1, 1], [0, 1]]` is `(r₁, r₁ + r₂)`. -/
theorem vecMul_map_modularGroup_T {R : Type u} [Ring R] (r : Fin 2 → R) :
    r ᵥ* (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R) =
      ![r 0, r 0 + r 1] := by
  ext i
  fin_cases i <;> simp [ModularGroup.coe_T, vecMul, dotProduct, Fin.sum_univ_two]

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-- `S² = -I` in the integral modular group. -/
@[simp]
theorem S_sq : S ^ 2 = (-1 : SL(2, ℤ)) :=
  by rw [pow_two, S_mul_S_eq]

/-- `S⁴ = I` in the integral modular group. -/
theorem S_pow_four : S ^ 4 = (1 : SL(2, ℤ)) := by
  calc
    S ^ 4 = (S ^ 2) ^ 2 := pow_mul S 2 2
    _ = 1 := by rw [S_sq]; decide

/-- The first column of `γ Tⁿ` is that of `γ`. -/
theorem mul_T_zpow_apply_apply_zero (γ : SL(2, ℤ)) (n : ℤ) (i : Fin 2) :
    (γ * T ^ n) i 0 = γ i 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second column of `γ Tⁿ` is `n` times the first column of `γ` plus its second column. -/
theorem mul_T_zpow_apply_apply_one (γ : SL(2, ℤ)) (n : ℤ) (i : Fin 2) :
    (γ * T ^ n) i 1 = γ i 0 * n + γ i 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- The first column of `γ S` is the second column of `γ`. -/
theorem mul_S_apply_apply_zero (γ : SL(2, ℤ)) (i : Fin 2) : (γ * S) i 0 = γ i 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- The second column of `γ S` is minus the first column of `γ`. -/
theorem mul_S_apply_apply_one (γ : SL(2, ℤ)) (i : Fin 2) : (γ * S) i 1 = -γ i 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, coe_S, Matrix.mul_apply, Fin.sum_univ_two]

/-- The first column of `-(γ S)` is minus the second column of `γ`. -/
theorem neg_mul_S_apply_apply_zero (γ : SL(2, ℤ)) (i : Fin 2) : (-(γ * S)) i 0 = -γ i 1 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, mul_S_apply_apply_zero]

/-- The second column of `-(γ S)` is the first column of `γ`. -/
theorem neg_mul_S_apply_apply_one (γ : SL(2, ℤ)) (i : Fin 2) : (-(γ * S)) i 1 = γ i 0 := by
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, mul_S_apply_apply_one, neg_neg]

end TauCeti.ModularGroup

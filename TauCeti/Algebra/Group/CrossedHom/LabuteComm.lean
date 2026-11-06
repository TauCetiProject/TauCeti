/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.CrossedHom
public import TauCeti.Algebra.Group.LabuteComm
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

/-!
# Crossed homomorphisms on Labute's commutator

For a crossed homomorphism `F` for a character `χ : H → Rˣ` (`TauCeti.IsCrossedHom`), the value on
Labute's commutator `(x, y) = x⁻¹y⁻¹xy` is determined by the values on `x` and `y`:
`χ x * χ y * F (x, y) = (1 - χ y) F x + (χ x - 1) F y`. This file records this identity, its
consequences for vanishing and for triviality of `χ`, and the value on a product of commutators.

## Main declarations

* `TauCeti.IsCrossedHom.mul_mul_map_labuteComm`: the value on Labute's commutator.
* `TauCeti.IsCrossedHom.map_labuteComm_eq_zero_of_eq_zero`: vanishing at `x` and `y` implies
  vanishing at `(x, y)`.
* `TauCeti.IsCrossedHom.map_list_range_prod_labuteComm`: the value on a product of commutators is
  the sum of the values on the factors.
-/

public section

namespace TauCeti

open Finset

variable {H : Type*} [Group H] {R : Type*} [CommRing R] {F' : Type*} [FunLike F' H Rˣ]
  [MonoidHomClass F' H Rˣ] {χ : F'} {F : H → R} (hF : IsCrossedHom χ F)
include hF

/-- The value of a crossed homomorphism on Labute's commutator `(x, y) = x⁻¹y⁻¹xy`, multiplied
through by `χ x * χ y`: it is read off `F (x * y) = F (y * x * (x, y))`. -/
theorem IsCrossedHom.mul_mul_map_labuteComm (x y : H) :
    (χ x : R) * χ y * F (labuteComm x y) = (1 - χ y) * F x + (χ x - 1) * F y := by
  have h : y * x * labuteComm x y = x * y := by
    rw [labuteComm_def]
    group
  have h1 := hF.map_mul (y * x) (labuteComm x y)
  rw [h, hF.map_mul x y, hF.map_mul y x, _root_.map_mul, Units.val_mul] at h1
  linear_combination -h1

/-- A crossed homomorphism vanishing at `x` and `y` vanishes at `(x, y)`. -/
theorem IsCrossedHom.map_labuteComm_eq_zero_of_eq_zero {x y : H} (hx : F x = 0) (hy : F y = 0) :
    F (labuteComm x y) = 0 := by
  have h := hF.mul_mul_map_labuteComm x y
  rw [hx, hy, mul_zero, mul_zero, add_zero, ← Units.val_mul] at h
  exact (Units.mul_right_eq_zero _).1 h

/-- A crossed homomorphism vanishes at `(x, y)` when the character is trivial at `x` and `y`. -/
theorem IsCrossedHom.map_labuteComm_eq_zero_of_eq_one {x y : H} (hx : χ x = 1) (hy : χ y = 1) :
    F (labuteComm x y) = 0 := by
  have h := hF.mul_mul_map_labuteComm x y
  rwa [hx, hy, Units.val_one, one_mul, one_mul, sub_self, zero_mul, zero_mul, add_zero] at h

/-- If a crossed homomorphism takes the value `1` at `x`, the value `0` at `y` and vanishes at
`(x, y)`, then the character is trivial at `y`. -/
theorem IsCrossedHom.eq_one_of_map_labuteComm_eq_zero_left {x y : H} (hx : F x = 1) (hy : F y = 0)
    (h : F (labuteComm x y) = 0) : χ y = 1 := by
  have h' := hF.mul_mul_map_labuteComm x y
  rw [h, hx, hy, mul_zero, mul_zero, mul_one, add_zero, eq_comm, sub_eq_zero, eq_comm] at h'
  exact Units.val_eq_one.1 h'

/-- If a crossed homomorphism takes the value `0` at `x`, the value `1` at `y` and vanishes at
`(x, y)`, then the character is trivial at `x`. -/
theorem IsCrossedHom.eq_one_of_map_labuteComm_eq_zero_right {x y : H} (hx : F x = 0) (hy : F y = 1)
    (h : F (labuteComm x y) = 0) : χ x = 1 := by
  have h' := hF.mul_mul_map_labuteComm x y
  rw [h, hx, hy, mul_zero, mul_zero, mul_one, zero_add, eq_comm, sub_eq_zero] at h'
  exact Units.val_eq_one.1 h'

/-- The value of a crossed homomorphism on a product of Labute commutators indexed by
`List.range m` is the sum of the values on the factors. -/
theorem IsCrossedHom.map_list_range_prod_labuteComm (m : ℕ) (x y : ℕ → H) :
    F ((List.range m).map fun i ↦ labuteComm (x i) (y i)).prod =
      ∑ i ∈ range m, F (labuteComm (x i) (y i)) := by
  rw [hF.map_list_prod_of_forall_eq_one, List.map_map, Finset.sum_eq_multiset_sum,
    Finset.range_val, ← Multiset.coe_range, Multiset.map_coe, Multiset.sum_coe]
  · rfl
  · simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro i _
    rw [map_labuteComm, labuteComm_eq_one]

end TauCeti

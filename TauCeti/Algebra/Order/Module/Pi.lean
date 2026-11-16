/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Fintype.EquivFin

/-!
# Positivity and monotonicity of linear maps on finite products

A linear map `L` from a finite product `ι → R` of a preordered semiring with `0 ≤ 1` into an
ordered `R`-module is nonnegative on the subcone of nonnegative vectors vanishing on a coordinate
set `J` if and only if `0 ≤ L (Pi.single j 1)` for every `j ∉ J`. Similarly, `L` is monotone if
and only if it is nonnegative on every standard basis vector `Pi.single j 1`.

## Main results

* `TauCeti.forall_map_nonneg_of_eq_zero_iff`: cone-positivity on nonnegative vectors vanishing on
  `J` is equivalent to nonnegativity on `Pi.single j 1` for all `j ∉ J`.
* `TauCeti.monotone_iff_forall_map_single_nonneg`: a linear map on `ι → R` is monotone if and only
  if it is nonnegative on every standard basis vector `Pi.single j 1`.
-/

public section

open Finset

namespace TauCeti

/-- A linear map on a finite product `ι → R` is nonnegative on every nonnegative vector vanishing
on `J` if and only if its value on every standard basis vector `Pi.single j 1` with `j ∉ J` is
nonnegative. -/
theorem forall_map_nonneg_of_eq_zero_iff {ι R M F : Type*} [Finite ι] [DecidableEq ι]
    [Semiring R] [Preorder R] [ZeroLEOneClass R]
    [AddCommMonoid M] [Preorder M] [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M]
    [FunLike F (ι → R) M] [LinearMapClass F R (ι → R) M]
    (L : F) (J : Set ι) :
    (∀ v : ι → R, 0 ≤ v → (∀ j ∈ J, v j = 0) → 0 ≤ L v) ↔
      ∀ j ∉ J, 0 ≤ L (Pi.single j 1) := by
  have := Fintype.ofFinite ι
  refine ⟨fun h j hj => h (Pi.single j 1) (fun k => by
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]) fun k hk => ?_,
    fun h v hv hvJ => ?_⟩
  · have hkj : k ≠ j := fun h' => hj (h' ▸ hk)
    exact Pi.single_eq_of_ne hkj 1
  · conv_rhs => rw [pi_eq_sum_univ' v]
    rw [map_sum]
    refine sum_nonneg fun j _ => ?_
    rw [map_smul]
    by_cases hj : j ∈ J
    · simp [hvJ j hj]
    · exact smul_nonneg (hv j) (h j hj)

/-- A linear map on a finite product `ι → R` is monotone if and only if it is nonnegative on every
standard basis vector `Pi.single j 1`. -/
theorem monotone_iff_forall_map_single_nonneg {ι R M F : Type*} [Finite ι] [DecidableEq ι]
    [Semiring R] [Preorder R] [ZeroLEOneClass R]
    [AddCommMonoid M] [Preorder M] [IsOrderedAddMonoid M] [Module R M] [SMulPosMono R M]
    [FunLike F (ι → R) M] [LinearMapClass F R (ι → R) M]
    (L : F) :
    Monotone L ↔ ∀ j : ι, 0 ≤ L (Pi.single j 1) := by
  have := Fintype.ofFinite ι
  refine ⟨fun h j => ?_, fun h v w hvw => ?_⟩
  · have hle : (0 : ι → R) ≤ Pi.single j 1 := fun k => by
      by_cases hkj : k = j
      · subst hkj; simp
      · simp [hkj]
    simpa only [map_zero] using h hle
  · rw [pi_eq_sum_univ' v, pi_eq_sum_univ' w, map_sum, map_sum]
    refine sum_le_sum fun j _ => ?_
    rw [map_smul, map_smul]
    exact smul_le_smul_of_nonneg_right (hvw j) (h j)

end TauCeti

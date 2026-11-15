/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.SurfaceGroup.Free
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.GroupTheory.FreeGroup.Centralizer
import TauCeti.GroupTheory.SurfaceGroup.LowGenus

/-!
# Boundary elements of surface groups have infinite order

Let `S±(g, m)` be one of the surface groups of `TauCeti.GroupTheory.SurfaceGroup.Basic`, with
peripheral elements `p₁, …, p_m`. Each `pⱼ` is represented by a loop around a boundary circle of
the compact surface, and the boundary subgroup it generates is infinite cyclic, except on the disc
`S⁺(0, 1)`, where the defining relation reads `p₁ = 1`. Equivalently, unless the surface is a
disc, every boundary map `ℤ → S±(g, m)`, `n ↦ pⱼ ^ n`, is injective. This holds for every surface
with boundary other than the disc, including those of Euler characteristic zero (the annulus and
the Möbius band), and it is what makes the boundary subgroups usable as the infinite cyclic edge
groups along which surface groups are cut and glued into amalgams and HNN extensions.

A surface group with nonempty boundary is free
(`TauCeti.SurfaceGroup.Orientable.instIsFreeGroupSucc`), and free groups are torsion-free, so
every nontrivial element has infinite order; a boundary element `pⱼ` is nontrivial unless the
surface is the disc.

## Main results

* `TauCeti.SurfaceGroup.Orientable.not_isOfFinOrder_peripheral` and
  `TauCeti.SurfaceGroup.Nonorientable.not_isOfFinOrder_peripheral`: the peripheral elements of
  `S⁺(g, m)` and `S⁻(g, m)` have infinite order unless `g = 0` and `m = 1`.
* `TauCeti.SurfaceGroup.Orientable.isOfFinOrder_peripheral_iff` and
  `TauCeti.SurfaceGroup.Nonorientable.isOfFinOrder_peripheral_iff`: a peripheral element has
  finite order exactly on the disc.
* `TauCeti.SurfaceGroup.Orientable.zpowersHom_peripheral_injective` and
  `TauCeti.SurfaceGroup.Nonorientable.zpowersHom_peripheral_injective`: the boundary maps
  `ℤ → S±(g, m)` are injective unless the surface is the disc.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §5.1.1
  (for a compact hyperbolic surface, the boundary subgroups are the fundamental groups of the
  boundary circles, infinite cyclic) and §5.1.2 (cyclic splittings dual to simple closed curves).
-/

public section

namespace TauCeti

namespace SurfaceGroup

open Equiv

namespace Orientable

variable {g m : ℕ}

/-- **Boundary elements have infinite order.** Unless the surface is the disc `S⁺(0, 1)`, every
peripheral element `pⱼ` of the orientable surface group `S⁺(g, m)` has infinite order. -/
theorem not_isOfFinOrder_peripheral (h : g ≠ 0 ∨ m ≠ 1) (j : Fin m) :
    ¬IsOfFinOrder (peripheral g m j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero j.pos.ne'
  -- `S⁺(g, m + 1)` is free, hence torsion-free, so it suffices that `pⱼ ≠ 1`.
  refine not_isOfFinOrder_of_isMulTorsionFree fun hj ↦ ?_
  rcases m with _ | m
  · -- One boundary circle, so `g ≠ 0`: `a₁ ↦ (0 1)`, `b₁ ↦ (1 2)`, `p₁ ↦ [(0 1), (1 2)]⁻¹`.
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (h.resolve_right (by simp))
    have hw : orientableWord (g := g + 1) (Fin.cons (swap 0 1) 1) (Fin.cons (swap 1 2) 1)
        (fun _ : Fin 1 ↦ (swap 0 1 * swap 1 2 * swap 0 1 * swap 1 2 : Perm (Fin 3))⁻¹) = 1 := by
      simp [orientableWord_def, List.ofFn_succ, Pi.one_def, mul_assoc]
    have := congrArg (lift _ _ _ hw) hj
    rw [lift_peripheral, map_one] at this
    exact absurd this (by decide)
  · -- At least two boundary circles: `pⱼ ↦ 1` and `pₖ ↦ -1` in `ℤ` for some `k ≠ j`.
    obtain ⟨k, hk⟩ := exists_ne j
    have hw : orientableWord (G := Multiplicative ℤ) (g := g) 1 1
        (Pi.mulSingle j (.ofAdd 1) * Pi.mulSingle k (.ofAdd (-1))) = 1 := by
      rw [orientableWord_def, List.prod_ofFn, List.prod_ofFn]
      simp [Finset.prod_mul_distrib]
    simpa [hk.symm] using congrArg (lift _ _ _ hw) hj

/-- A peripheral element of the orientable surface group `S⁺(g, m)` has finite order exactly
when the surface is the disc `S⁺(0, 1)`, where `p₁ = 1`. -/
@[simp]
theorem isOfFinOrder_peripheral_iff (j : Fin m) :
    IsOfFinOrder (peripheral g m j) ↔ g = 0 ∧ m = 1 := by
  refine ⟨fun hj ↦ of_not_not fun h ↦ not_isOfFinOrder_peripheral (not_and_or.mp h) j hj, ?_⟩
  rintro ⟨rfl, rfl⟩
  -- The disc group `S⁺(0, 1)` is trivial.
  exact isOfFinOrder_of_finite _

/-- Unless the surface is the disc, the boundary map `ℤ → S⁺(g, m)`, `n ↦ pⱼ ^ n`, is
injective. -/
theorem zpowersHom_peripheral_injective (h : g ≠ 0 ∨ m ≠ 1) (j : Fin m) :
    Function.Injective (zpowersHom (Orientable g m) (peripheral g m j)) := fun x y hxy ↦
  Multiplicative.toAdd.injective <|
    injective_zpow_iff_not_isOfFinOrder.2 (not_isOfFinOrder_peripheral h j) <| by
      simpa using hxy

end Orientable

namespace Nonorientable

variable {g m : ℕ}

/-- **Boundary elements have infinite order.** Unless `g = 0` and `m = 1` (the presentation of
the disc), every peripheral element `pⱼ` of the nonorientable surface group `S⁻(g, m)` has
infinite order. -/
theorem not_isOfFinOrder_peripheral (h : g ≠ 0 ∨ m ≠ 1) (j : Fin m) :
    ¬IsOfFinOrder (peripheral g m j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero j.pos.ne'
  -- `S⁻(g, m + 1)` is free, hence torsion-free, so it suffices that `pⱼ ≠ 1`.
  refine not_isOfFinOrder_of_isMulTorsionFree fun hj ↦ ?_
  rcases m with _ | m
  · -- One boundary circle, so `g ≠ 0`: `c₁ ↦ 1`, `p₁ ↦ -2` in `ℤ`.
    obtain ⟨g, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (h.resolve_right (by simp))
    have hw : nonorientableWord (M := Multiplicative ℤ) (g := g + 1) (Pi.mulSingle 0 (.ofAdd 1))
        (fun _ : Fin 1 ↦ .ofAdd (-2)) = 1 := by
      simp [nonorientableWord_def, ← ofAdd_nsmul]
    simpa using congrArg (lift _ _ hw) hj
  · -- At least two boundary circles: `pⱼ ↦ 1` and `pₖ ↦ -1` in `ℤ` for some `k ≠ j`.
    obtain ⟨k, hk⟩ := exists_ne j
    have hw : nonorientableWord (M := Multiplicative ℤ) (g := g) 1
        (Pi.mulSingle j (.ofAdd 1) * Pi.mulSingle k (.ofAdd (-1))) = 1 := by
      rw [nonorientableWord_def, List.prod_ofFn, List.prod_ofFn]
      simp [Finset.prod_mul_distrib]
    simpa [hk.symm] using congrArg (lift _ _ hw) hj

/-- A peripheral element of `S⁻(g, m)` has finite order exactly when `g = 0` and `m = 1`, where
the presentation is that of the disc and `p₁ = 1`. -/
@[simp]
theorem isOfFinOrder_peripheral_iff (j : Fin m) :
    IsOfFinOrder (peripheral g m j) ↔ g = 0 ∧ m = 1 := by
  refine ⟨fun hj ↦ of_not_not fun h ↦ not_isOfFinOrder_peripheral (not_and_or.mp h) j hj, ?_⟩
  rintro ⟨rfl, rfl⟩
  -- The relation of the disc reads `p₁ = 1`.
  have : peripheral 0 1 j = 1 := by
    simpa [nonorientableWord_def, Fin.fin_one_eq_zero j] using nonorientableWord_c_peripheral 0 1
  exact this ▸ IsOfFinOrder.one

/-- Unless `g = 0` and `m = 1`, the boundary map `ℤ → S⁻(g, m)`, `n ↦ pⱼ ^ n`, is injective. -/
theorem zpowersHom_peripheral_injective (h : g ≠ 0 ∨ m ≠ 1) (j : Fin m) :
    Function.Injective (zpowersHom (Nonorientable g m) (peripheral g m j)) := fun x y hxy ↦
  Multiplicative.toAdd.injective <|
    injective_zpow_iff_not_isOfFinOrder.2 (not_isOfFinOrder_peripheral h j) <| by
      simpa using hxy

end Nonorientable

end SurfaceGroup

end TauCeti

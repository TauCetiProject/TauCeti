/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Tactic.Module

/-!
# Linear combinations of the first two arguments of an alternating map

Replacing the first two arguments `p, v` of an alternating map `f` by the linear combinations
`a p + s v` and `α p + β v` multiplies its value by the determinant `a β - s α` of the
coefficient matrix (`AlternatingMap.map_cons_cons_add_smul`). This is the two-dimensional case of
the multiplicativity of the determinant, with the remaining arguments held fixed, as in the
orientation sign of a rotation in the plane spanned by `p` and `v`. When the second combination
is instead the last argument, moving it to the second place contributes the sign `(-1)ⁿ` of a
cycle (`AlternatingMap.map_cons_snoc_add_smul`), and scaling the remaining `n` arguments by `t`
contributes `tⁿ` (`AlternatingMap.map_cons_snoc_smul_add_smul`).
-/

public section

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- Applying an alternating map to `Fin.cons x (Fin.cons y w)` is applying its double left
curry at `x` and `y` to `w`. -/
private theorem map_cons_cons_eq_curryLeft_curryLeft (f : M [⋀^Fin (n + 1 + 1)]→ₗ[R] N)
    (x y : M) (w : Fin n → M) :
    f (Fin.cons x (Fin.cons y w)) = (f.curryLeft x).curryLeft y w := by
  rw [curryLeft_apply_apply, curryLeft_apply_apply]
  -- `Matrix.vecCons` is `Fin.cons`.
  rfl

/-- Replacing the first two arguments `p, v` of an alternating map by `a p + s v, α p + β v`
multiplies its value by the determinant `a β - s α`. -/
theorem map_cons_cons_add_smul (f : M [⋀^Fin (n + 1 + 1)]→ₗ[R] N) (p v : M) (w : Fin n → M)
    (a s α β : R) :
    f (Fin.cons (a • p + s • v) (Fin.cons (α • p + β • v) w)) =
      (a * β - s * α) • f (Fin.cons p (Fin.cons v w)) := by
  have hswap : (f.curryLeft v).curryLeft p w = -(f.curryLeft p).curryLeft v w := by
    have h := congrArg (fun f ↦ f w) (f.curryLeft_same (p + v))
    simp only [map_add, curryLeft_add, LinearMap.add_apply, add_apply, curryLeft_same,
      zero_apply, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [map_cons_cons_eq_curryLeft_curryLeft, map_cons_cons_eq_curryLeft_curryLeft]
  simp only [map_add, map_smul, curryLeft_add, curryLeft_smul, LinearMap.add_apply,
    LinearMap.smul_apply, add_apply, smul_apply, curryLeft_same, zero_apply, smul_zero, hswap]
  module

/-- Replacing the first argument `p` of an alternating map by `a p + s v` and appending
`α p + β v` after the remaining `n` arguments `w`, in place of `v` in second position, multiplies
its value by `(-1)ⁿ (a β - s α)`. -/
theorem map_cons_snoc_add_smul (f : M [⋀^Fin (n + 1 + 1)]→ₗ[R] N) (p v : M) (w : Fin n → M)
    (a s α β : R) :
    f (Fin.cons (a • p + s • v) (Fin.snoc w (α • p + β • v))) =
      ((-1) ^ n * (a * β - s * α)) • f (Fin.cons p (Fin.cons v w)) := by
  -- Moving the last argument to the second place costs the sign `(-1)ⁿ` of a cycle.
  have hins := (f.curryLeft (a • p + s • v)).map_insertNth (Fin.last n) (α • p + β • v) w
  simp only [Fin.insertNth_last', Fin.val_last, curryLeft_apply_apply, Matrix.vecCons] at hins
  rw [hins, map_cons_cons_add_smul]
  module

/-- The version of `AlternatingMap.map_cons_snoc_add_smul` in which the remaining `n` arguments
`w` are also scaled by `t`: the value is multiplied by `(-1)ⁿ tⁿ (a β - s α)`. -/
theorem map_cons_snoc_smul_add_smul (f : M [⋀^Fin (n + 1 + 1)]→ₗ[R] N) (p v : M) (w : Fin n → M)
    (a s α β t : R) :
    f (Fin.cons (a • p + s • v) (Fin.snoc (t • w) (α • p + β • v))) =
      ((-1) ^ n * t ^ n * (a * β - s * α)) • f (Fin.cons p (Fin.cons v w)) := by
  have hs := ((f.curryLeft p).curryLeft v).map_smul_univ (fun _ ↦ t) w
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hs
  rw [map_cons_snoc_add_smul, map_cons_cons_eq_curryLeft_curryLeft,
    map_cons_cons_eq_curryLeft_curryLeft]
  -- `t • w` is `fun i ↦ t • w i` by definition of the scalar action on functions.
  rw [show t • w = fun i ↦ t • w i from rfl, hs, smul_smul]
  congr 1
  ring

end AlternatingMap

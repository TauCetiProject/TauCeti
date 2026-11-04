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
cycle (`AlternatingMap.map_cons_snoc_add_smul`).
-/

public section

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- Replacing the first two arguments `p, v` of an alternating map by `a p + s v, α p + β v`
multiplies its value by the determinant `a β - s α`. -/
theorem map_cons_cons_add_smul (f : M [⋀^Fin (n + 1 + 1)]→ₗ[R] N) (p v : M) (w : Fin n → M)
    (a s α β : R) :
    f (Fin.cons (a • p + s • v) (Fin.cons (α • p + β • v) w)) =
      (a * β - s * α) • f (Fin.cons p (Fin.cons v w)) := by
  have e (x y : M) : f (Fin.cons x (Fin.cons y w)) = (f.curryLeft x).curryLeft y w := by
    rw [curryLeft_apply_apply, curryLeft_apply_apply]
    -- `Matrix.vecCons` is `Fin.cons`.
    rfl
  have hswap : (f.curryLeft v).curryLeft p w = -(f.curryLeft p).curryLeft v w := by
    have h := congrArg (fun f ↦ f w) (f.curryLeft_same (p + v))
    simp only [map_add, curryLeft_add, LinearMap.add_apply, add_apply, curryLeft_same,
      zero_apply, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  rw [e, e]
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

end AlternatingMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic

/-!
# Exchanging the first argument of an alternating map with a later one

Writing the arguments of an alternating map `f` on `Fin (n + 1)` as `Fin.cons x w`, exchanging
`x` with the argument `y` in slot `i + 1` changes the sign of the value
(`AlternatingMap.map_cons_update_add`).
-/

public section

namespace AlternatingMap

open Function

variable {R M N : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] {n : ℕ}

/-- Exchanging the first argument of an alternating map with the argument in slot `i + 1` changes
the sign: `f (x, w with y at i) + f (y, w with x at i) = 0`. -/
theorem map_cons_update_add (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (w : Fin n → M) (i : Fin n)
    (x y : M) : f (Fin.cons x (update w i y)) + f (Fin.cons y (update w i x)) = 0 := by
  have hv : (Fin.cons y (update w i x) : Fin (n + 1) → M) ∘ Equiv.swap 0 i.succ =
      Fin.cons x (update w i y) := by
    ext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [-Fin.cons_update]
    · rcases eq_or_ne j i with rfl | hj
      · simp [-Fin.cons_update]
      · rw [comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero j)
          ((Fin.succ_injective _).ne hj)]
        simp [update_of_ne hj]
  simpa only [hv] using f.map_swap_add (v := Fin.cons y (update w i x)) (Fin.succ_ne_zero i).symm

end AlternatingMap

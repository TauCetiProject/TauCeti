/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Translating every argument of an alternating map

Adding the same vector `u` to each of the `n` arguments of an alternating map `f` changes its
value by the sum of the values in which a single argument is replaced by `u`:
`f (v + u) = f v + ∑ k, f (update v k u)` (`AlternatingMap.map_add_const`). Terms in which two
arguments are replaced vanish, because `f` is alternating.

Read with `-u` in place of `u`, this is the expansion of an alternating map along the edges of a
simplex with apex `u` (`AlternatingMap.map_sub_const`):
`f (v₁ - u, …, vₙ - u) = ∑ j, (-1) ^ j • f (w₀, …, ŵⱼ, …, wₙ)`, where `w = (u, v₁, …, vₙ)`.
This is how the derivative of the face of the standard simplex opposite the origin, whose edges
are `eₖ₊₁ - e₀`, is compared with the coordinate faces in Stokes' theorem for a simplex.
-/

public section

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- Adding a vector `u` to every argument of an alternating map adds the values obtained by
replacing a single argument by `u`. -/
theorem map_add_const : ∀ {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (u : M),
    f (fun k ↦ v k + u) = f v + ∑ k, f (Function.update v k u)
  | 0, f, v, u => by
    simp [Subsingleton.elim (fun k ↦ v k + u) v]
  | n + 1, f, v, u => by
    have hv : (fun k ↦ v k + u) = Matrix.vecCons (v 0 + u) fun k ↦ Fin.tail v k + u := by
      ext k
      cases k using Fin.cases <;> simp [Fin.tail]
    -- A second copy of `u` in the arguments kills each term of the expansion of `f (u, v + u)`.
    have hu : ∀ k, f.curryLeft u (Function.update (Fin.tail v) k u) = 0 := fun k ↦ by
      rw [curryLeft_apply_apply]
      exact f.map_eq_zero_of_eq _ (i := 0) (j := k.succ) (by simp [Matrix.vecCons])
        (Fin.succ_ne_zero k).symm
    have hcons : v = Matrix.vecCons (v 0) (Fin.tail v) := (Fin.cons_self_tail v).symm
    rw [hv, map_vecCons_add, ← curryLeft_apply_apply, ← curryLeft_apply_apply, map_add_const,
      map_add_const, Finset.sum_eq_zero fun k _ ↦ hu k, add_zero, Fin.sum_univ_succ]
    conv_rhs => rw [hcons]
    simp only [curryLeft_apply_apply, Matrix.vecCons, Fin.update_cons_zero, ← Fin.cons_update]
    abel

/-- **Expansion along the edges of a simplex.** Evaluating an alternating map on the differences
`vₖ - u` gives the alternating sum of its values on the tuples obtained from `(u, v₁, …, vₙ)` by
omitting one vector. -/
theorem map_sub_const {n : ℕ} (f : M [⋀^Fin n]→ₗ[R] N) (v : Fin n → M) (u : M) :
    f (fun k ↦ v k - u) =
      ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) • f (j.removeNth (Fin.cons u v : Fin (n + 1) → M)) := by
  rcases n with _ | n
  · simp [Subsingleton.elim (fun k ↦ v k - u) v]
  have hrem : ∀ k : Fin (n + 1), k.succ.removeNth (Fin.cons u v : Fin (n + 2) → M) =
      Fin.cons u (k.removeNth v) := fun k ↦ by
    ext i
    cases i using Fin.cases <;> simp [Fin.removeNth_apply, Fin.succ_succAbove_succ]
  simp_rw [sub_eq_add_neg]
  rw [map_add_const, Fin.sum_univ_succ (f := fun j : Fin (n + 2) ↦ (-1) ^ (j : ℕ) • _),
    Fin.removeNth_zero, Fin.tail_cons, Fin.val_zero, pow_zero, one_smul]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_update_neg, ← Fin.insertNth_removeNth, map_insertNth, hrem, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Matrix.vecCons]

end AlternatingMap

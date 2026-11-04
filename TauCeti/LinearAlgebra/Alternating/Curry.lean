/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Uncurrying alternating maps in the first argument

Mathlib's `AlternatingMap.curryLeft` turns an alternating map `f` in `n + 2` arguments into a
linear family `x ↦ f.curryLeft x` of alternating maps in `n + 1` arguments, and every member of
that family vanishes once its first argument is `x` again (`AlternatingMap.curryLeft_same`). This
file constructs the inverse: a linear family `g` of alternating maps with `(g x).curryLeft x = 0`
for every `x` assembles into the alternating map `AlternatingMap.uncurryLeft g hg` with
`uncurryLeft g hg v = g (v 0) (Fin.tail v)`.

So an alternating map may be defined by giving its value with the first argument fixed, and
checking only that it vanishes when the first two arguments agree. This is how the
Chevalley–Eilenberg differential, defined degree by degree through its interior products, is
shown to be alternating. The file also records that alternating maps are determined by their
interior products (`AlternatingMap.curryLeft_injective`) and that interior products anticommute
(`AlternatingMap.curryLeft_curryLeft_eq_neg`).
-/

public section

open Fin

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- An alternating map in at least one argument is determined by its interior products. -/
theorem curryLeft_injective :
    Function.Injective (curryLeft : M [⋀^Fin (n + 1)]→ₗ[R] N → M →ₗ[R] M [⋀^Fin n]→ₗ[R] N) := by
  intro f g h
  ext v
  have hv := congr(($h (v 0)) (tail v))
  rwa [curryLeft_apply_apply, curryLeft_apply_apply, Matrix.vecCons, cons_self_tail] at hv

/-- Interior products anticommute: exchanging the first two arguments changes the sign. -/
theorem curryLeft_curryLeft_eq_neg (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (x y : M) :
    (f.curryLeft x).curryLeft y = -(f.curryLeft y).curryLeft x := by
  ext r
  simp only [curryLeft_apply_apply, neg_apply]
  rw [← f.map_swap (Matrix.vecCons y (Matrix.vecCons x r)) (zero_ne_one' (Fin (n + 2)))]
  congr 1
  ext i
  refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j) i
  · simp
  · simp
  · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (succ_ne_zero _) (succ_succ_ne_one k)]
    simp

/-- A linear family `g` of alternating maps in `n + 1` arguments, each vanishing when its first
argument equals the parameter, assembles into an alternating map in `n + 2` arguments whose first
argument is the parameter. This inverts `AlternatingMap.curryLeft`. -/
def uncurryLeft (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N) (hg : ∀ x, (g x).curryLeft x = 0) :
    M [⋀^Fin (n + 2)]→ₗ[R] N where
  toMultilinearMap := (toMultilinearMapLM ∘ₗ g).uncurryLeft
  map_eq_zero_of_eq' v i j hv hij := by
    rw [MultilinearMap.toFun_eq_coe, LinearMap.uncurryLeft_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, toMultilinearMapLM_apply,
      coe_multilinearMap]
    -- Two equal arguments after the first make `g (v 0)` vanish; otherwise one of them is the
    -- first argument, and moving the other one next to it uses `hg`.
    wlog hle : i < j generalizing i j
    · exact this j i hv.symm hij.symm (lt_of_le_of_ne (not_lt.1 hle) hij.symm)
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hij.symm
      have hj : tail v j = v 0 := hv.symm
      rw [← insertNth_self_removeNth j (tail v), hj, map_insertNth, ← curryLeft_apply_apply, hg,
        zero_apply, smul_zero]
    · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 (Fin.ne_zero_of_lt hle)
      exact (g (v 0)).map_eq_zero_of_eq (tail v) hv (ne_of_apply_ne succ hij)

/-- The first argument of `uncurryLeft g hg` selects the member of the family `g`. -/
@[simp]
theorem uncurryLeft_apply (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hg : ∀ x, (g x).curryLeft x = 0) (v : Fin (n + 2) → M) :
    uncurryLeft g hg v = g (v 0) (tail v) := (rfl)

/-- Currying `uncurryLeft g hg` recovers the family `g`. -/
@[simp]
theorem curryLeft_uncurryLeft (g : M →ₗ[R] M [⋀^Fin (n + 1)]→ₗ[R] N)
    (hg : ∀ x, (g x).curryLeft x = 0) : (uncurryLeft g hg).curryLeft = g := by
  ext x v
  simp

/-- Uncurrying the interior products of `f` recovers `f`. -/
@[simp]
theorem uncurryLeft_curryLeft (f : M [⋀^Fin (n + 2)]→ₗ[R] N) :
    uncurryLeft f.curryLeft f.curryLeft_same = f := by
  ext v
  rw [uncurryLeft_apply, curryLeft_apply_apply]
  exact congrArg f (cons_self_tail v)

end AlternatingMap

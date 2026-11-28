/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Basic

/-!
# The telescope difference map on a countable direct sum of abelian groups

Given a sequence of additive group homomorphisms `t : ∀ n, A n →+ A (n + 1)`, the *telescope
difference map* `TauCeti.telescopeDiff t` is the endomorphism of `⨁ n, A n` sending `a : A n` to
`of A n a - of A (n + 1) (t n a)`. Its coordinates are `x 0` at `0` and `x (n + 1) - t n (x n)` at
`n + 1`, so `telescopeDiff t` is injective and its cokernel presents the sequential colimit of
`(A, t)`. This underlies both module telescopes (`ModuleCat.telescopeDiff`) and hom-set telescopes
out of countably compact objects in preadditive categories.

## Main declarations

* `TauCeti.telescopeDiff`: the telescope difference endomorphism `(⨁ n, A n) →+ ⨁ n, A n`.
* `TauCeti.telescopeDiff_apply_zero`, `TauCeti.telescopeDiff_apply_succ`: coordinate formulas.
* `TauCeti.telescopeDiff_injective`: `telescopeDiff t` is injective.
* `TauCeti.comp_telescopeDiff_eq_zero_iff`: universal property on maps killing `telescopeDiff t`.
* `TauCeti.apply_eq_zero_of_telescopeDiff_eq_of_lt`, `TauCeti.apply_eq_of_telescopeDiff_eq_of`,
  `TauCeti.apply_succ_eq_of_telescopeDiff_eq_of_ne`: preimage coordinates of single summands.

## References

* J. Milnor, *On axiomatic homology theory*, Pacific J. Math. 12 (1962), 337–341.
-/

public section

open scoped DirectSum

namespace TauCeti

variable {A : ℕ → Type*} [∀ n, AddCommGroup (A n)]

section Basic

variable (t : ∀ n, A n →+ A (n + 1))

/-- The telescope difference endomorphism on a countable direct sum `⨁ n, A n`, sending `a : A n`
in degree `n` to `of A n a - of A (n + 1) (t n a)`. -/
def telescopeDiff : (⨁ n, A n) →+ ⨁ n, A n :=
  DirectSum.toAddMonoid fun n ↦ DirectSum.of A n - (DirectSum.of A (n + 1)).comp (t n)

theorem telescopeDiff_def :
    telescopeDiff t =
      DirectSum.toAddMonoid fun n ↦ DirectSum.of A n - (DirectSum.of A (n + 1)).comp (t n) := (rfl)

@[simp]
theorem telescopeDiff_of (n : ℕ) (a : A n) :
    telescopeDiff t (DirectSum.of A n a) =
      DirectSum.of A n a - DirectSum.of A (n + 1) (t n a) := by simp [telescopeDiff]

@[simp]
theorem telescopeDiff_apply_zero (x : ⨁ n, A n) : telescopeDiff t x 0 = x 0 :=
  DirectSum.induction_on x (by simp)
    (fun k _ ↦ by rw [telescopeDiff_of, DirectSum.sub_apply,
      DirectSum.of_eq_of_ne (β := A) (k + 1) 0 _ (Nat.succ_ne_zero k).symm, sub_zero])
    fun _ _ hu hv ↦ by simp [map_add, hu, hv]

@[simp]
theorem telescopeDiff_apply_succ (x : ⨁ n, A n) (n : ℕ) :
    telescopeDiff t x (n + 1) = x (n + 1) - t n (x n) := by
  refine DirectSum.induction_on x (by simp) (fun k _ ↦ ?_) fun _ _ hu hv ↦ by
    simp [map_add, hu, hv, sub_add_sub_comm]
  rw [telescopeDiff_of, DirectSum.sub_apply]
  by_cases hkn : k = n
  · subst hkn; simp [DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne (β := A) (k + 1) (n + 1) _ fun h ↦ hkn (Nat.succ.inj h).symm,
      DirectSum.of_eq_of_ne (β := A) k n _ (Ne.symm hkn), map_zero]

/-- The telescope difference endomorphism `telescopeDiff t` is injective: each coordinate `x n` is
recursively determined by the coordinates of `telescopeDiff t x` in degrees `≤ n`. -/
theorem telescopeDiff_injective : Function.Injective (telescopeDiff t) :=
  (injective_iff_map_eq_zero _).2 fun x hx ↦ DFinsupp.ext fun n ↦ by
    induction n with
    | zero => simpa using congr($hx 0)
    | succ n ih => simpa [ih] using congr($hx (n + 1))

end Basic

/-- A homomorphism out of `⨁ n, A n` vanishes on `telescopeDiff t` if and only if its restrictions
to the summands commute with the transitions `t n`. -/
theorem comp_telescopeDiff_eq_zero_iff {B : Type*} [AddCommGroup B]
    {t : ∀ n, A n →+ A (n + 1)} {f : (⨁ n, A n) →+ B} :
    f.comp (telescopeDiff t) = 0 ↔
      ∀ n a, f (DirectSum.of A n a) = f (DirectSum.of A (n + 1) (t n a)) :=
  ⟨fun h n a ↦ sub_eq_zero.1 (by simpa [telescopeDiff_of, map_sub] using congr($h (.of A n a))),
    fun h ↦ DirectSum.addHom_ext fun n a ↦ by simp [telescopeDiff_of, map_sub, h n a]⟩

/-- If `telescopeDiff t x` is supported in a single degree `n`, then `x` vanishes below `n`. -/
theorem apply_eq_zero_of_telescopeDiff_eq_of_lt {t : ∀ n, A n →+ A (n + 1)}
    {x : ⨁ n, A n} {n : ℕ} {a : A n} (hx : telescopeDiff t x = DirectSum.of A n a)
    {k : ℕ} (hk : k < n) : x k = 0 := by
  induction k with
  | zero => simpa [DirectSum.of_eq_of_ne (β := A) n 0 a hk.ne] using congr($hx 0)
  | succ k ih =>
    simpa [ih (Nat.lt_of_succ_lt hk), DirectSum.of_eq_of_ne (β := A) n (k + 1) a hk.ne] using
      congr($hx (k + 1))

/-- If `telescopeDiff t x = DirectSum.of A n a`, then `x n = a`. -/
theorem apply_eq_of_telescopeDiff_eq_of {t : ∀ n, A n →+ A (n + 1)}
    {x : ⨁ n, A n} {n : ℕ} {a : A n} (hx : telescopeDiff t x = DirectSum.of A n a) : x n = a := by
  cases n with
  | zero => simpa using congr($hx 0)
  | succ k =>
    simpa [apply_eq_zero_of_telescopeDiff_eq_of_lt hx (Nat.lt_succ_self k)] using
      congr($hx (k + 1))

/-- If `telescopeDiff t x = DirectSum.of A n a`, then `x (k + 1) = t k (x k)` whenever
`k + 1 ≠ n`. -/
theorem apply_succ_eq_of_telescopeDiff_eq_of_ne {t : ∀ n, A n →+ A (n + 1)}
    {x : ⨁ n, A n} {n : ℕ} {a : A n} (hx : telescopeDiff t x = DirectSum.of A n a)
    {k : ℕ} (hk : k + 1 ≠ n) : x (k + 1) = t k (x k) := by
  have h := congr($hx (k + 1))
  rw [telescopeDiff_apply_succ, DirectSum.of_eq_of_ne (β := A) n (k + 1) a hk] at h
  exact sub_eq_zero.1 h

end TauCeti

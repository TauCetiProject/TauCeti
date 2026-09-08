/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# The total sign homomorphism of a number field

A real place `w` of a number field `K` carries an embedding
`NumberField.InfinitePlace.embedding_of_isReal : K →+* ℝ`, so every nonzero element of `K` has a
sign at `w`.  Collecting those signs over all the real places gives the **total sign
homomorphism**

```text
signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ).
```

This is the archimedean half of a multiplicative congruence in group-theoretic form: `x` is
totally positive exactly when `signHom x = 1`.

Surjectivity of `signHom` is not formal — it is a consequence of weak approximation, and is proved
as `TauCeti.GlobalNumberFields.signHom_surjective` in
`TauCeti.NumberTheory.NumberField.Global.Approximation.Weak`.  The composite
`(𝓞 K)ˣ → Kˣ → ({w // w.IsReal} → ℤˣ)` need *not* be surjective, and its failure to be so is
exactly the obstruction that separates the narrow class group from the wide one; nothing here
asserts otherwise.

## Main definitions

* `TauCeti.GlobalNumberFields.signHom`: the total sign homomorphism.

## Main results

* `TauCeti.GlobalNumberFields.signHom_apply_eq_one_iff` and
  `TauCeti.GlobalNumberFields.signHom_apply_eq_neg_one_iff`: the two possible signs, read off as
  positivity and negativity of the real embedding.
* `TauCeti.GlobalNumberFields.signHom_eq_one_iff`: an element lies in the kernel exactly when it
  is totally positive.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K]

/-- A real embedding of a number field does not vanish on a unit. -/
theorem embedding_of_isReal_ne_zero (w : {w : InfinitePlace K // w.IsReal}) (x : Kˣ) :
    InfinitePlace.embedding_of_isReal w.2 (x : K) ≠ 0 :=
  (map_ne_zero_iff _ (InfinitePlace.embedding_of_isReal w.2).injective).mpr x.ne_zero

/-- **The total sign homomorphism of a number field**: the signs of a unit of `K` at all of the
real places at once, valued in the product of copies of `ℤˣ` indexed by those places.

The domain is `Kˣ` rather than `K`, so that every value really is a sign: a formulation on `K`
would have to invent a sign for `0`. -/
noncomputable def signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ) where
  toFun x w := if 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) then 1 else -1
  map_one' := by
    funext w
    simp
  map_mul' x y := by
    funext w
    have hx := lt_or_gt_of_ne (embedding_of_isReal_ne_zero w x)
    have hy := lt_or_gt_of_ne (embedding_of_isReal_ne_zero w y)
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [ite_eq_left (mul_pos_of_neg_of_neg hx hy), ite_eq_right (not_lt.mpr hx.le),
        ite_eq_right (not_lt.mpr hy.le)]
      simp
    · rw [ite_eq_right (not_lt.mpr (mul_neg_of_neg_of_pos hx hy).le),
        ite_eq_right (not_lt.mpr hx.le), ite_eq_left hy]
      simp
    · rw [ite_eq_right (not_lt.mpr (mul_neg_of_pos_of_neg hx hy).le), ite_eq_left hx,
        ite_eq_right (not_lt.mpr hy.le)]
      simp
    · rw [ite_eq_left (mul_pos hx hy), ite_eq_left hx, ite_eq_left hy]
      simp

private theorem signHom_apply (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = if 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) then 1 else -1 := rfl

/-- **A sign is `1` exactly at a positive element.** -/
@[simp] theorem signHom_apply_eq_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = 1 ↔ 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := by
  rw [signHom_apply]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- **A sign is `-1` exactly at a negative element.** -/
@[simp] theorem signHom_apply_eq_neg_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = -1 ↔ InfinitePlace.embedding_of_isReal w.2 (x : K) < 0 := by
  rw [signHom_apply]
  rcases lt_or_gt_of_ne (embedding_of_isReal_ne_zero w x) with h | h
  · rw [ite_eq_right (not_lt.mpr h.le)]
    simp [h]
  · rw [ite_eq_left h]
    simp [asymm h]

/-- **The kernel of the total sign homomorphism is the totally positive elements.** -/
theorem signHom_eq_one_iff (x : Kˣ) :
    signHom x = 1 ↔ ∀ w : {w : InfinitePlace K // w.IsReal},
      0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := by
  rw [funext_iff]
  exact forall_congr' fun w ↦ by rw [Pi.one_apply, signHom_apply_eq_one_iff]

end TauCeti.GlobalNumberFields

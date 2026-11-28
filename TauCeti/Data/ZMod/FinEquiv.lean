/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Applying `ZMod.finEquiv`

Mathlib defines `ZMod.finEquiv : Fin n ≃+* ZMod n` for `[NeZero n]` and states nothing about
applying it. This file states the two evaluation rules as `@[simp]` lemmas, so that an argument
indexed by `Fin n` rewrites into `ZMod n` arithmetic instead of being unfolded at each use.
Through `ZMod.finEquiv`, for `n > 0`, a sum or product over the residues modulo `n` of a
function of the least nonnegative representative is a sum or product over `range n`.

## Main results

* `ZMod.finEquiv_apply`: `ZMod.finEquiv n j` is the natural cast of `j.val`.
* `ZMod.finEquiv_symm_apply_val`: the canonical `Fin n` representative
  `(ZMod.finEquiv n).symm z` of `z : ZMod n` has natural value `z.val`.
* `ZMod.prod_val_eq_prod_range`, `ZMod.sum_val_eq_sum_range`: multiplying or summing a function
  of the representatives over `range n`.
* `ZMod.prod_val_erase_zero_eq_prod_Ico_one`, `ZMod.sum_val_erase_zero_eq_sum_Ico_one`:
  multiplying or summing a function of the representatives over the nonzero residues as `Ico 1 n`.
* `ZMod.prod_val_eq_prod_Ico_one`, `ZMod.sum_val_eq_sum_Ico_one`: the same over all residues when
  the value at `0` is `1` or `0`.
* `ZMod.prod_val_sub_eq_prod_range`, `ZMod.sum_val_sub_eq_sum_range`: the same for the
  representatives of a shift `x - c`.
* `TauCeti.mulModEquiv`: multiplication by `d` modulo `p` as a permutation of `Fin p`, for `d`
  coprime to `p`, with its evaluation rule `TauCeti.mulModEquiv_apply_val`. These take a modulus
  rather than a `ZMod` value, so they are not dot notation on `ZMod` and live in `TauCeti`.
-/

public section

namespace ZMod

open Fin.CommRing in
/-- **Applying `ZMod.finEquiv` is the natural cast.** `ZMod.finEquiv n j` is the image of `j.val`
under `Nat.cast`.

Mathlib defines `finEquiv` and states no evaluation rule for it in either direction, so this is
the lemma a `Fin n`-indexed statement rewrites through to reach `ZMod n`. -/
@[simp]
lemma finEquiv_apply {n : ℕ} [NeZero n] (j : Fin n) :
    (ZMod.finEquiv n) j = ((j : ℕ) : ZMod n) := by
  -- Through stated lemmas rather than defeq: `map_natCast` moves the cast of `j.val` back across
  -- the ring hom, and `Fin.cast_val_eq_self` recognises it as `j`. So the proof does not depend
  -- on `finEquiv` being defined by cases on `n`. `Fin.instCommRing` is scoped
  -- (`Mathlib/Data/ZMod/Defs.lean`), hence the `open Fin.CommRing in` above.
  rw [← map_natCast (ZMod.finEquiv n), Fin.cast_val_eq_self]

/-- **The canonical `Fin n` representative of `z : ZMod n` has natural value `z.val`.** The
representative is `(ZMod.finEquiv n).symm z`. This is the companion of `finEquiv_apply`, and the
form needed to index by `Fin n` an element obtained by solving in `ZMod n`. -/
@[simp]
lemma finEquiv_symm_apply_val {n : ℕ} [NeZero n] (z : ZMod n) :
    (((ZMod.finEquiv n).symm z : Fin n) : ℕ) = z.val := by
  -- Through the stated rules rather than the `ZMod (k+1) = Fin (k+1)` reduction: the
  -- representative is below `n`, so it is the `val` of its own cast, which `finEquiv_apply`
  -- identifies with `finEquiv` applied to it, that is with `z`.
  rw [← ZMod.val_natCast_of_lt ((ZMod.finEquiv n).symm z).isLt, ← finEquiv_apply,
    RingEquiv.apply_symm_apply]

/-- **Multiplying over the representatives.** For `n > 0`, a function of the least nonnegative
representative multiplied over the residues modulo `n` is its product over `range n`. -/
@[to_additive /-- **Summing over the representatives.** For `n > 0`, a function of the least
nonnegative representative summed over the residues modulo `n` is its sum over `range n`. -/]
theorem prod_val_eq_prod_range {n : ℕ} {M : Type*} [CommMonoid M] [NeZero n] (f : ℕ → M) :
    ∏ x : ZMod n, f x.val = ∏ i ∈ Finset.range n, f i := by
  rw [Finset.prod_range, ← (finEquiv n).symm.toEquiv.prod_comp]
  simp

/-- **Multiplying over the nonzero representatives.** For `n > 0`, a function of the least
nonnegative representative multiplied over the nonzero residues modulo `n` is its product over
`Finset.Ico 1 n`. -/
@[to_additive sum_val_erase_zero_eq_sum_Ico_one
/-- **Summing over the nonzero representatives.** For `n > 0`, a function of the least
nonnegative representative summed over the nonzero residues modulo `n` is its sum over
`Finset.Ico 1 n`. -/]
theorem prod_val_erase_zero_eq_prod_Ico_one {n : ℕ} {M : Type*} [CommMonoid M] [NeZero n]
    (f : ℕ → M) :
    ∏ x ∈ Finset.univ.erase (0 : ZMod n), f x.val = ∏ i ∈ Finset.Ico 1 n, f i := by
  refine Finset.prod_nbij' (fun x ↦ x.val) (fun i ↦ (i : ZMod n)) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro x hx
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hx
    refine Finset.mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun h ↦ hx ?_, x.val_lt⟩
    rw [← ZMod.natCast_zmod_val x, h, Nat.cast_zero]
  · intro i hi
    rw [Finset.mem_Ico] at hi
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
    intro h0
    have hval := congrArg ZMod.val h0
    rw [ZMod.val_natCast_of_lt hi.2, ZMod.val_zero] at hval
    omega
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro i hi
    exact ZMod.val_natCast_of_lt (Finset.mem_Ico.mp hi).2

/-- **Multiplying over representatives when the zero term is one.** If `f 0 = 1`, multiplying
`f x.val` over `x : ZMod n` equals the product of `f i` over `i ∈ Finset.Ico 1 n`. -/
@[to_additive sum_val_eq_sum_Ico_one
/-- **Summing over representatives when the zero term vanishes.** If `f 0 = 0`,
summing `f x.val` over `x : ZMod n` equals the sum of `f i` over `i ∈ Finset.Ico 1 n`. -/]
theorem prod_val_eq_prod_Ico_one {n : ℕ} {M : Type*} [CommMonoid M] [NeZero n] (f : ℕ → M)
    (hf0 : f 0 = 1) : ∏ x : ZMod n, f x.val = ∏ i ∈ Finset.Ico 1 n, f i := by
  rw [← Finset.mul_prod_erase Finset.univ (fun x : ZMod n ↦ f x.val) (Finset.mem_univ 0),
    ZMod.val_zero, hf0, one_mul, prod_val_erase_zero_eq_prod_Ico_one]

/-- **Multiplying over shifted representatives.** For `n > 0`, a function of the representative
of `x - c` multiplied over the residues modulo `n` is its product over `range n`. -/
@[to_additive /-- **Summing over shifted representatives.** For `n > 0`, a function of the
representative of `x - c` summed over the residues modulo `n` is its sum over `range n`. -/]
theorem prod_val_sub_eq_prod_range {n : ℕ} {M : Type*} [CommMonoid M] [NeZero n] (f : ℕ → M)
    (c : ZMod n) : ∏ x : ZMod n, f (x - c).val = ∏ i ∈ Finset.range n, f i := by
  simpa only [Equiv.subRight_apply] using
    ((Equiv.subRight c).prod_comp fun x ↦ f x.val).trans (prod_val_eq_prod_range f)

end ZMod

namespace TauCeti

/-- **Multiplication by a unit permutes the residues**: for `d` coprime to `p`, the map
`b ↦ d b mod p` is a permutation of `Fin p`. It is multiplication by the unit
`ZMod.unitOfCoprime d hdp` of `ZMod p`, read through `ZMod.finEquiv`. -/
noncomputable def mulModEquiv (p : ℕ) {d : ℕ} [NeZero p] (hdp : Nat.Coprime d p) :
    Fin p ≃ Fin p :=
  (ZMod.finEquiv p).toEquiv.trans <|
    (Units.mulLeft (ZMod.unitOfCoprime d hdp)).trans (ZMod.finEquiv p).toEquiv.symm

/-- **The value of `TauCeti.mulModEquiv`**: it sends `b` to the residue `d b mod p`. -/
@[simp]
lemma mulModEquiv_apply_val (p : ℕ) {d : ℕ} [NeZero p] (hdp : Nat.Coprime d p) (b : Fin p) :
    (mulModEquiv p hdp b : ℕ) = d * (b : ℕ) % p := by
  simp [mulModEquiv, ZMod.coe_unitOfCoprime, ← Nat.cast_mul, ZMod.val_natCast]

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Applying `ZMod.finEquiv`

Mathlib defines `ZMod.finEquiv : Fin n ≃+* ZMod n` for `[NeZero n]` and states nothing about
applying it. This file states the two evaluation rules as `@[simp]` lemmas, so that an argument
indexed by `Fin n` rewrites into `ZMod n` arithmetic instead of being unfolded at each use.

## Main results

* `ZMod.finEquiv_apply`: `ZMod.finEquiv n j` is the natural cast of `j.val`.
* `ZMod.finEquiv_symm_apply_val`: the canonical `Fin n` representative
  `(ZMod.finEquiv n).symm z` of `z : ZMod n` has natural value `z.val`.
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

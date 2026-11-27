/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Algebra.Star.SelfAdjoint

import Mathlib.Tactic.Abel

/-!
# The idempotents cut out by a square root of one

Let `A` be an algebra over a commutative ring `R` in which `2` is invertible, and let `ω : A`. The
element

`TauCeti.halfOneAdd R ω = ½ (1 + ω)`

and its companion `TauCeti.halfOneAdd R (-ω) = ½ (1 - ω)` always add up to `1`
(`TauCeti.halfOneAdd_add_halfOneAdd_neg`) and always differ by `ω`
(`TauCeti.halfOneAdd_sub_halfOneAdd_neg`). As soon as `ω * ω = 1` they are moreover orthogonal
(`TauCeti.halfOneAdd_mul_halfOneAdd_neg`) and therefore idempotent
(`TauCeti.isIdempotentElem_halfOneAdd`): a square root of one always cuts out a **complementary
orthogonal pair** of idempotents. The right ideals `e₊ A` and `e₋ A` are two-sided, and the
resulting decomposition is one of rings, only when the idempotents are central, which is more than
this file assumes. If `ω` commutes with a given element then so do both idempotents
(`TauCeti.commute_halfOneAdd`), and elements written in the form `e₊ a + e₋ b` then multiply
componentwise (`TauCeti.halfOneAdd_mul_add_mul`).

Nothing here is specific to any one algebra:
`TauCeti/LinearAlgebra/CliffordAlgebra/OddSplitting.lean` runs it on a central odd square root of
one in a Clifford algebra, where the two blocks turn out to be copies of the even subalgebra.

Mathlib has `IsIdempotentElem` and its complement API
(`IsIdempotentElem.of_mul_add`, `IsIdempotentElem.one_sub_mul_self`), which is what the proofs below
consume, but not the passage from a square root of one to the idempotent pair.

## Main definitions

* `TauCeti.halfOneAdd`: the element `½ (1 + ω)`. No property of `ω` is built into it, so that the
  complementary idempotent is literally the same construction applied to `-ω`.

## Main results

* `TauCeti.halfOneAdd_add_halfOneAdd_neg`, `TauCeti.halfOneAdd_sub_halfOneAdd_neg`: the pair is
  complementary, and its difference recovers `ω`.
* `TauCeti.halfOneAdd_smul_add_halfOneAdd_neg_smul`: in every module, each vector is the sum of
  its images under the pair.
* `TauCeti.isUnit_two_of_invertible_two`: `2` is a unit of every algebra over a ring in which `2`
  is invertible.
* `TauCeti.halfOneAdd_smul_eq_self_iff`, `TauCeti.halfOneAdd_smul_eq_zero_iff`: for any `ω`, the
  fixed vectors of `½ (1 + ω)` are the `1`-eigenvectors of `ω` and its kernel is the
  `-1`-eigenspace.
* `TauCeti.isSelfAdjoint_halfOneAdd`: `½ (1 + ω)` is self-adjoint along with `ω`.
* `TauCeti.halfOneAdd_mul_halfOneAdd_neg`, `TauCeti.isIdempotentElem_halfOneAdd`: for a square root
  of one the pair is orthogonal and idempotent.
* `TauCeti.mul_halfOneAdd`, `TauCeti.mul_halfOneAdd_neg`: `ω` acts on the two idempotents by
  `1` and `-1`, so in every module they project onto the `±1`-eigenvectors of `ω`.
* `TauCeti.mul_halfOneAdd_eq_halfOneAdd_neg_mul`: an element anticommuting with `ω` exchanges the
  two idempotents.
* `TauCeti.map_halfOneAdd`: algebra homomorphisms carry the pair of `ω` to the pair of its image.
* `TauCeti.halfOneAdd_mul_add_mul`: **the multiplication rule** `(e₊ a + e₋ b) (e₊ c + e₋ d)
  = e₊ (a c) + e₋ (b d)`, for `a` and `b` commuting with `ω`.
-/

public section

namespace TauCeti

variable (R : Type*) {A : Type*} [CommRing R] [Ring A] [Algebra R A] [Invertible (2 : R)]

/-- The element `½ (1 + ω)` of an `R`-algebra, for `2` invertible in `R`.

It is idempotent when `ω * ω = 1` (`TauCeti.isIdempotentElem_halfOneAdd`), and then
`halfOneAdd R (-ω) = ½ (1 - ω)` is the complementary idempotent. No property of `ω` is built into
the definition, so that the two idempotents are literally the same construction applied to `ω` and
to `-ω`. -/
noncomputable def halfOneAdd (ω : A) : A := (⅟2 : R) • (1 + ω)

/-- The defining formula for `TauCeti.halfOneAdd`. -/
theorem halfOneAdd_def (ω : A) : halfOneAdd R ω = (⅟2 : R) • (1 + ω) := (rfl)

/-- An algebra homomorphism carries `½ (1 + ω)` to `½ (1 + f ω)`. -/
theorem map_halfOneAdd {B F : Type*} [Ring B] [Algebra R B] [FunLike F A B] [AlgHomClass F R A B]
    (f : F) (ω : A) : f (halfOneAdd R ω) = halfOneAdd R (f ω) := by
  rw [halfOneAdd_def, halfOneAdd_def, map_smul, map_add, map_one]

/-- **The pair is complementary**: `½ (1 + ω) + ½ (1 - ω) = 1`. -/
@[simp]
theorem halfOneAdd_add_halfOneAdd_neg (ω : A) : halfOneAdd R ω + halfOneAdd R (-ω) = 1 := by
  rw [halfOneAdd_def, halfOneAdd_def, ← smul_add]
  have h : (1 + ω) + (1 + -ω) = (2 : R) • (1 : A) := by rw [two_smul]; abel
  rw [h, invOf_smul_smul]

/-- **The difference of the pair is `ω`**: `½ (1 + ω) - ½ (1 - ω) = ω`. This is what makes `ω`
recoverable from the splitting it induces. -/
@[simp]
theorem halfOneAdd_sub_halfOneAdd_neg (ω : A) : halfOneAdd R ω - halfOneAdd R (-ω) = ω := by
  rw [halfOneAdd_def, halfOneAdd_def, ← smul_sub]
  have h : (1 + ω) - (1 + -ω) = (2 : R) • ω := by rw [two_smul]; abel
  rw [h, invOf_smul_smul]

/-- The companion element is the complement `1 - ½ (1 + ω)`, the form in which Mathlib's
`IsIdempotentElem` API talks about it. -/
theorem halfOneAdd_neg_eq_one_sub (ω : A) : halfOneAdd R (-ω) = 1 - halfOneAdd R ω :=
  eq_sub_of_add_eq' (halfOneAdd_add_halfOneAdd_neg R ω)

/-- **Every vector splits along the pair**: in any `A`-module, `½ (1 + ω) m + ½ (1 - ω) m = m`. -/
theorem halfOneAdd_smul_add_halfOneAdd_neg_smul {M : Type*} [AddCommGroup M] [Module A M] (ω : A)
    (m : M) : halfOneAdd R ω • m + halfOneAdd R (-ω) • m = m := by
  rw [← add_smul, halfOneAdd_add_halfOneAdd_neg, one_smul]

/-- Doubling `½ (1 + ω)` gives back `1 + ω`. -/
theorem two_mul_halfOneAdd (ω : A) : (2 : A) * halfOneAdd R ω = 1 + ω := by
  rw [halfOneAdd_def, mul_smul_comm, two_mul, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

variable {ω : A}

include R in
/-- `2` is a unit of every algebra over a ring in which `2` is invertible. -/
theorem isUnit_two_of_invertible_two : IsUnit (2 : A) := by
  simpa only [map_ofNat] using (isUnit_of_invertible (2 : R)).map (algebraMap R A)

/-- **The fixed vectors of `½ (1 + ω)` are the `1`-eigenvectors of `ω`**: in any `A`-module,
`½ (1 + ω) m = m` exactly when `ω m = m`. No property of `ω` is needed. -/
theorem halfOneAdd_smul_eq_self_iff {M : Type*} [AddCommGroup M] [Module A M] {m : M} :
    halfOneAdd R ω • m = m ↔ ω • m = m := by
  rw [← (isUnit_two_of_invertible_two R (A := A)).smul_left_cancel, ← mul_smul,
    two_mul_halfOneAdd, add_smul, one_smul, two_smul, add_right_inj]

/-- **The kernel of `½ (1 + ω)` is the `-1`-eigenspace of `ω`**: in any `A`-module,
`½ (1 + ω) m = 0` exactly when `ω m = -m`. No property of `ω` is needed. -/
theorem halfOneAdd_smul_eq_zero_iff {M : Type*} [AddCommGroup M] [Module A M] {m : M} :
    halfOneAdd R ω • m = 0 ↔ ω • m = -m := by
  rw [← (isUnit_two_of_invertible_two R (A := A)).smul_left_cancel, smul_zero, ← mul_smul,
    two_mul_halfOneAdd, add_smul, one_smul, add_eq_zero_iff_eq_neg']

/-- **`½ (1 + ω)` is self-adjoint along with `ω`**, in a star algebra over a star ring. -/
theorem isSelfAdjoint_halfOneAdd [StarRing R] [StarRing A] [StarModule R A]
    (h : IsSelfAdjoint ω) : IsSelfAdjoint (halfOneAdd R ω) := by
  have h2 : IsSelfAdjoint (⅟2 : R) := by
    rw [isSelfAdjoint_iff, star_invOf]
    exact invOf_eq_right_inv (by rw [star_ofNat, mul_invOf_self])
  rw [halfOneAdd_def]
  exact h2.smul ((IsSelfAdjoint.one A).add h)

/-- **The pair is orthogonal** when `ω` squares to `1`: `½ (1 + ω) · ½ (1 - ω) = 0`. -/
theorem halfOneAdd_mul_halfOneAdd_neg (hsq : ω * ω = 1) :
    halfOneAdd R ω * halfOneAdd R (-ω) = 0 := by
  have h : (1 + ω) * (1 + -ω) = 0 := by
    rw [add_mul, one_mul, mul_add, mul_one, mul_neg, hsq]
    abel
  rw [halfOneAdd_def, halfOneAdd_def, smul_mul_assoc, mul_smul_comm, h, smul_zero, smul_zero]

/-- **`½ (1 + ω)` is idempotent** when `ω` squares to `1`. -/
theorem isIdempotentElem_halfOneAdd (hsq : ω * ω = 1) : IsIdempotentElem (halfOneAdd R ω) :=
  (IsIdempotentElem.of_mul_add (halfOneAdd_mul_halfOneAdd_neg R hsq)
    (halfOneAdd_add_halfOneAdd_neg R ω)).1

/-- **`½ (1 - ω)` is idempotent** when `ω` squares to `1`; it is the complementary idempotent. -/
theorem isIdempotentElem_halfOneAdd_neg (hsq : ω * ω = 1) :
    IsIdempotentElem (halfOneAdd R (-ω)) :=
  (IsIdempotentElem.of_mul_add (halfOneAdd_mul_halfOneAdd_neg R hsq)
    (halfOneAdd_add_halfOneAdd_neg R ω)).2

/-- The reverse orthogonality `½ (1 - ω) · ½ (1 + ω) = 0`, read off the complement. -/
theorem halfOneAdd_neg_mul_halfOneAdd (hsq : ω * ω = 1) :
    halfOneAdd R (-ω) * halfOneAdd R ω = 0 := by
  rw [halfOneAdd_neg_eq_one_sub]
  exact (isIdempotentElem_halfOneAdd R hsq).one_sub_mul_self

/-- **`½ (1 + ω)` cuts out the `1`-eigenvectors of `ω`**: `ω · ½ (1 + ω) = ½ (1 + ω)` when `ω`
squares to `1`. -/
theorem mul_halfOneAdd (hsq : ω * ω = 1) : ω * halfOneAdd R ω = halfOneAdd R ω := by
  rw [halfOneAdd_def, mul_smul_comm, mul_add, mul_one, hsq, add_comm]

/-- **`½ (1 - ω)` cuts out the `-1`-eigenvectors of `ω`**: `ω · ½ (1 - ω) = -½ (1 - ω)` when `ω`
squares to `1`. -/
theorem mul_halfOneAdd_neg (hsq : ω * ω = 1) : ω * halfOneAdd R (-ω) = -halfOneAdd R (-ω) := by
  rw [halfOneAdd_def, mul_smul_comm, ← smul_neg, mul_add, mul_one, mul_neg, hsq, neg_add, neg_neg,
    add_comm]

/-- **The pair inherits commutation from `ω`.** Only commutation with the element at hand is
needed, so a central `ω` gives a central pair. -/
theorem commute_halfOneAdd {x : A} (h : Commute ω x) : Commute (halfOneAdd R ω) x := by
  rw [halfOneAdd_def]
  exact Commute.smul_left ((Commute.one_left x).add_left h) _

/-- **An element anticommuting with `ω` exchanges the pair**: if `ω x = -(x ω)`, then
`x · ½ (1 + ω) = ½ (1 - ω) · x`, so in every module `x` carries the `1`-eigenvectors of `ω` to its
`-1`-eigenvectors. -/
theorem mul_halfOneAdd_eq_halfOneAdd_neg_mul {x : A} (h : ω * x = -(x * ω)) :
    x * halfOneAdd R ω = halfOneAdd R (-ω) * x := by
  rw [halfOneAdd_def, halfOneAdd_def, mul_smul_comm, smul_mul_assoc, mul_add, mul_one, add_mul,
    one_mul, neg_mul, h, neg_neg]

/-- **The multiplication rule a splitting rests on**: the pair being orthogonal, idempotent and
commuting with `a` and `b`, elements of the form `e₊ a + e₋ b` multiply componentwise. -/
theorem halfOneAdd_mul_add_mul (hsq : ω * ω = 1) {a b : A} (ha : Commute ω a) (hb : Commute ω b)
    (c d : A) :
    (halfOneAdd R ω * a + halfOneAdd R (-ω) * b) *
        (halfOneAdd R ω * c + halfOneAdd R (-ω) * d)
      = halfOneAdd R ω * (a * c) + halfOneAdd R (-ω) * (b * d) := by
  have hee := (isIdempotentElem_halfOneAdd R hsq).eq
  have hff := (isIdempotentElem_halfOneAdd_neg R hsq).eq
  have hef := halfOneAdd_mul_halfOneAdd_neg R hsq
  have hfe := halfOneAdd_neg_mul_halfOneAdd R hsq
  have hae : Commute a (halfOneAdd R ω) := (commute_halfOneAdd R ha).symm
  have haf : Commute a (halfOneAdd R (-ω)) := (commute_halfOneAdd R ha.neg_left).symm
  have hbe : Commute b (halfOneAdd R ω) := (commute_halfOneAdd R hb).symm
  have hbf : Commute b (halfOneAdd R (-ω)) := (commute_halfOneAdd R hb.neg_left).symm
  calc (halfOneAdd R ω * a + halfOneAdd R (-ω) * b) *
        (halfOneAdd R ω * c + halfOneAdd R (-ω) * d)
      = halfOneAdd R ω * a * (halfOneAdd R ω * c)
          + halfOneAdd R ω * a * (halfOneAdd R (-ω) * d)
          + (halfOneAdd R (-ω) * b * (halfOneAdd R ω * c)
            + halfOneAdd R (-ω) * b * (halfOneAdd R (-ω) * d)) := by
        rw [add_mul, mul_add, mul_add]
    _ = halfOneAdd R ω * halfOneAdd R ω * (a * c)
          + halfOneAdd R ω * halfOneAdd R (-ω) * (a * d)
          + (halfOneAdd R (-ω) * halfOneAdd R ω * (b * c)
            + halfOneAdd R (-ω) * halfOneAdd R (-ω) * (b * d)) := by
        rw [hae.mul_mul_mul_comm _ c, haf.mul_mul_mul_comm _ d, hbe.mul_mul_mul_comm _ c,
          hbf.mul_mul_mul_comm _ d]
    _ = halfOneAdd R ω * (a * c) + halfOneAdd R (-ω) * (b * d) := by
        rw [hee, hff, hef, hfe, zero_mul, zero_mul, add_zero, zero_add]

end TauCeti

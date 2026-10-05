/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm

/-!
# Arrow action on type-`A` preprojective normal forms

In the signless preprojective algebra of `0 — ⋯ — (n - 1)`, left multiplication by an
arrow extends the end of a valley word. An upward arrow extends its climb. A downward
arrow pushes the bottom down by one, with sign `(-1)` to the number of climbs; if the
bottom is already zero, the product vanishes. An arrow with the wrong source also
annihilates the word.

These formulas describe the left-module action on the spanning valley families of
the vertex projectives. They provide the multiplication computations for their socles
and for the Frobenius pairing, without assuming independence of the spanning words.
They hold over any commutative ring, including characteristic two, and use
later-factor-first path multiplication.

## References

* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin
  Frobenius property and projective socles.
* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the
  Deligne--Simpson problem*, Section 1, for the preprojective relations.

The computations use `TauCeti.ladderValley` and its ladder relations, and the
projected classes `TauCeti.signlessPreprojectiveAValley`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver

variable (k : Type*) [CommRing k] {n : ℕ}

attribute [local instance] finiteNeighborSetFintype

local notation "AG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.A n))
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver AG)
local notation "e" => fun a : Fin (DynkinType.A n).rank => π (vertexIdempotent k (vertex AG a))
local notation "u" => fun w => signlessArrow k AG w (w + 1)
local notation "d" => fun w => signlessArrow k AG (w + 1) w

/-- The two turns cancel at every positive vertex, with missing arrows read as zero. -/
private theorem ladder_turn (w : ℕ) : d (w + 1) * u (w + 1) + u w * d w = 0 := by
  simpa only [Nat.add_sub_cancel, add_comm] using signlessArrow_A_relation k (n := n) (w + 1)

/-- The sole turn at the bottom endpoint vanishes. -/
private theorem ladder_bottom : d 0 * u 0 = 0 := by
  have hzero : signlessArrow k AG 0 0 = 0 :=
    signlessArrow_eq_zero k fun _ _ => SimpleGraph.irrefl _
  simpa only [Nat.zero_add, Nat.sub_self, hzero, zero_mul, add_zero] using
    signlessArrow_A_relation k (n := n) 0

/-- An upward arrow extends the climb of a valley normal form. -/
@[simp]
theorem signlessArrow_mul_signlessPreprojectiveAValley_of_succ (a b b' : Fin (DynkinType.A n).rank)
    (m : ℕ) (hb : b.val + 1 = b'.val) (hm : m ≤ b.val) :
    signlessArrow k AG b.val b'.val * signlessPreprojectiveAValley k a b m =
      signlessPreprojectiveAValley k a b' m := by
  have hheight : m + (b.val - m) = b.val := by omega
  have hclimb : b'.val - m = (b.val - m) + 1 := by omega
  rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def,
    ← mul_assoc, ← mul_assoc, signlessArrow_mul_vertexIdempotent, ite_eq_left rfl]
  rw [hclimb, ← u_mul_ladderValley, hheight, hb]
  simp only [← mul_assoc, vertexIdempotent_mul_signlessArrow, ite_true]

/-- A downward arrow moves a positive valley bottom down one rung. Each climb crossed
contributes one minus sign. -/
@[simp]
theorem signlessArrow_mul_signlessPreprojectiveAValley_of_pred (a b b' : Fin (DynkinType.A n).rank)
    (m : ℕ) (hb : b'.val + 1 = b.val) (hm : m + 1 ≤ min a.val b.val) :
    signlessArrow k AG b.val b'.val * signlessPreprojectiveAValley k a b (m + 1) =
      ((-1 : ℤ) ^ (b.val - (m + 1))) • signlessPreprojectiveAValley k a b' m := by
  have hheight : m + (b.val - (m + 1)) = b'.val := by omega
  have hdesc : a.val - m = (a.val - (m + 1)) + 1 := by omega
  have hclimb : b'.val - m = b.val - (m + 1) := by omega
  have hstep : signlessArrow k AG b.val b'.val *
      ladderValley u d (m + 1) (a.val - (m + 1)) (b.val - (m + 1)) =
      ((-1 : ℤ) ^ (b.val - (m + 1))) •
        ladderValley u d m (a.val - m) (b'.val - m) := by
    simpa only [hheight, hb, hdesc, hclimb, zsmul_eq_mul,
      Int.cast_pow, Int.cast_neg, Int.cast_one] using
        d_mul_ladderValley (ladder_turn k (n := n)) m
          (a.val - (m + 1)) (b.val - (m + 1))
  rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def,
    ← mul_assoc, ← mul_assoc, signlessArrow_mul_vertexIdempotent, ite_eq_left rfl]
  calc
    _ = e b' * (signlessArrow k AG b.val b'.val *
        ladderValley u d (m + 1) (a.val - (m + 1)) (b.val - (m + 1))) * e a := by
      simp only [← mul_assoc, vertexIdempotent_mul_signlessArrow, ite_true]
    _ = _ := by rw [hstep, mul_smul_comm, smul_mul_assoc]

/-- A downward arrow annihilates a valley whose bottom is zero. -/
@[simp]
theorem signlessArrow_mul_signlessPreprojectiveAValley_zero (a b b' : Fin (DynkinType.A n).rank)
    (hb : b'.val + 1 = b.val) :
    signlessArrow k AG b.val b'.val * signlessPreprojectiveAValley k a b 0 = 0 := by
  rw [signlessPreprojectiveAValley_def, ← mul_assoc, ← mul_assoc,
    signlessArrow_mul_vertexIdempotent, ite_eq_left rfl]
  simp only [Nat.sub_zero]
  rw [← hb, d_mul_ladderValley_zero_eq_zero (ladder_bottom k) (ladder_turn k), zero_mul]

/-- An arrow whose source differs from the terminal vertex of a valley annihilates it. -/
@[simp]
theorem signlessArrow_mul_signlessPreprojectiveAValley_of_ne (a b : Fin (DynkinType.A n).rank)
    (m i j : ℕ) (hi : i ≠ b.val) :
    signlessArrow k AG i j * signlessPreprojectiveAValley k a b m = 0 := by
  rw [signlessPreprojectiveAValley_def, ← mul_assoc, ← mul_assoc,
    signlessArrow_mul_vertexIdempotent, ite_eq_right hi, zero_mul, zero_mul]

end TauCeti

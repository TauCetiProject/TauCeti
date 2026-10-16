/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm

/-!
# Multiplication of type-`A` preprojective normal forms

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

The valley from `a` to `b` with bottom `m`, followed by the valley from `b` to `c` with
bottom `l`, has formal bottom `m + l - b`. If this is negative, the product vanishes.
Otherwise the product is the resulting valley times the sign
`(-1)^((b-l)*(b-m))`. Products are in later-factor-first order.

These formulas determine multiplication on the corner spanning families over any commutative
ring, including characteristic two. They supply the products whose top-degree coefficients
enter a Frobenius functional; no linear independence or nonvanishing is asserted here.

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

/-- Removing the target projection from a composable ladder word with its source projection. -/
private theorem target_ladderValley (a b : Fin (DynkinType.A n).rank) {m s r : ℕ}
    (ha : m + s = a.val) (hb : m + r = b.val) :
    e b * (ladderValley u d m s r * e a) = ladderValley u d m s r * e a := by
  classical
  dsimp only
  rw [← mul_assoc]
  cases r with
  | zero =>
    cases s with
    | zero =>
      have hab : a = b := Fin.ext (by omega)
      subst b
      rw [ladderValley_zero_zero, mul_one, one_mul, ← map_mul, vertexIdempotent_mul_self]
    | succ s =>
      have hm : m < (DynkinType.A n).rank := by omega
      have hm' : m + 1 < (DynkinType.A n).rank := by omega
      have hadj : (AG).Adj ⟨m + 1, hm'⟩ ⟨m, hm⟩ :=
        (diagramGraph_A_adj n _ _).mpr (.inr rfl)
      have he : e b * d m = d m := by
        dsimp only
        rw [signlessArrow_of_adj k hadj, ← map_mul, ofArrow_eq_ofPath]
        have hb' : (⟨m, hm⟩ : Fin (DynkinType.A n).rank) = b := Fin.ext (by omega)
        rw [← hb', vertexIdempotent_mul_ofPath]
      rw [← d_mul_ladderValley_succ_zero, ← mul_assoc, he]
  | succ r =>
    have hm : m + r < (DynkinType.A n).rank := by omega
    have hm' : m + r + 1 < (DynkinType.A n).rank := by omega
    have hadj : (AG).Adj ⟨m + r, hm⟩ ⟨m + r + 1, hm'⟩ :=
      (diagramGraph_A_adj n _ _).mpr (.inl rfl)
    have he : e b * u (m + r) = u (m + r) := by
      dsimp only
      rw [signlessArrow_of_adj k hadj, ← map_mul, ofArrow_eq_ofPath]
      have hb' : (⟨m + r + 1, hm'⟩ : Fin (DynkinType.A n).rank) = b := Fin.ext (by omega)
      rw [← hb', vertexIdempotent_mul_ofPath]
    rw [← u_mul_ladderValley, ← mul_assoc, he]

/-- The product of two composable valleys with nonnegative formal bottom.
The sign counts the crossings of the later descents with the earlier climbs. -/
@[simp]
theorem signlessPreprojectiveAValley_mul (a b c : Fin (DynkinType.A n).rank) {m l : ℕ}
    (hm : m ≤ min a.val b.val) (hl : l ≤ min b.val c.val) (hbottom : b.val ≤ m + l) :
    signlessPreprojectiveAValley k b c l * signlessPreprojectiveAValley k a b m =
      (-1) ^ ((b.val - l) * (b.val - m)) *
        signlessPreprojectiveAValley k a c (m + l - b.val) := by
  rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def,
    signlessPreprojectiveAValley_def]
  simp only [mul_assoc]
  rw [target_ladderValley k a b (by omega) (by omega),
    target_ladderValley k a b (by omega) (by omega)]
  rw [← mul_assoc (ladderValley u d l (b.val - l) (c.val - l)),
    ladderValley_mul_ladderValley (ladder_turn k (n := n))
      (by omega) (by omega)]
  have h1 : m - (b.val - l) = m + l - b.val := by omega
  have h2 : (a.val - m) + (b.val - l) = a.val - (m + l - b.val) := by omega
  have h3 : (b.val - m) + (c.val - l) = c.val - (m + l - b.val) := by omega
  rw [h1, h2, h3]
  simp only [← mul_assoc]
  rw [((Commute.neg_one_right (e c)).pow_right ((b.val - l) * (b.val - m))).eq]

/-- The product is zero when commuting the descents past the climbs would cross rung zero.
This includes valleys whose bottom lies above their source. -/
@[simp]
theorem signlessPreprojectiveAValley_mul_eq_zero (a b c : Fin (DynkinType.A n).rank) {m l : ℕ}
    (hbottom : m + l < b.val) :
    signlessPreprojectiveAValley k b c l * signlessPreprojectiveAValley k a b m = 0 := by
  by_cases hm : m ≤ a.val
  · rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def]
    simp only [mul_assoc]
    rw [target_ladderValley k a b (by omega) (by omega),
      target_ladderValley k a b (by omega) (by omega),
      ← mul_assoc (ladderValley u d l (b.val - l) (c.val - l)),
      ladderValley_mul_ladderValley_eq_zero (ladder_bottom k (n := n))
        (ladder_turn k (n := n)) (by omega) (by omega), zero_mul, mul_zero]
  · have ha : a.val - m = 0 := by omega
    obtain ⟨r, hr⟩ : ∃ r, b.val - m = r + 1 := ⟨b.val - m - 1, by omega⟩
    have hzero : signlessPreprojectiveAValley k a b m = 0 := by
      rw [signlessPreprojectiveAValley_def, ha, hr, ← ladderValley_succ_zero_mul_u,
        mul_assoc, mul_assoc, signlessArrow_mul_vertexIdempotent, ite_eq_right (by omega),
        mul_zero, mul_zero]
    rw [hzero, mul_zero]

/-- Valleys in noncomposable corners have zero product, with no bounds on their bottoms. -/
@[simp]
theorem signlessPreprojectiveAValley_mul_eq_zero_of_ne
    (a b c f : Fin (DynkinType.A n).rank) (m l : ℕ) (h : b ≠ f) :
    signlessPreprojectiveAValley k f c l * signlessPreprojectiveAValley k a b m = 0 := by
  classical
  have he : e f * e b = 0 := by
    rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne
      (fun hfb => h (vertex_injective AG hfb).symm), map_zero]
  have hid (i : Fin (DynkinType.A n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex AG i)) π
  have hsource := mul_eq_self_of_mem_cornerSubmodule_right (hid f)
    (signlessPreprojectiveAValley_mem_cornerSubmodule k f c l)
  have htarget := mul_eq_self_of_mem_cornerSubmodule (hid b)
    (signlessPreprojectiveAValley_mem_cornerSubmodule k a b m)
  calc
    _ = (signlessPreprojectiveAValley k f c l * e f) *
        (e b * signlessPreprojectiveAValley k a b m) := by rw [hsource, htarget]
    _ = signlessPreprojectiveAValley k f c l * (e f * e b) *
        signlessPreprojectiveAValley k a b m := by simp only [mul_assoc]
    _ = 0 := by rw [he, mul_zero, zero_mul]

end TauCeti

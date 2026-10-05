/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeA.NormalForm

/-!
# Products of type-`A` preprojective valleys

The valley from `a` to `b` with bottom `m`, followed by the valley from `b` to `c` with
bottom `l`, has formal bottom `m + l - b`. If this is negative, the product vanishes.
Otherwise the product is the resulting valley times the sign
`(-1)^((b-l)*(b-m))`. Products are in later-factor-first order.

These formulas determine multiplication on the corner spanning families over any commutative
ring, including characteristic two. They supply the products whose top-degree coefficients
enter a Frobenius functional; no linear independence or nonvanishing is asserted here.

The proof uses `TauCeti.ladderValley_mul_ladderValley` and the existing projected valley
normal forms. The local relations are those of W. Crawley-Boevey, *Quiver algebras, weighted
projective lines, and the Deligne--Simpson problem*, Section 1. For the finite-Dynkin
Frobenius property, see C. M. Ringel, *The preprojective algebra of a quiver*.
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

private theorem ladder_relation (w : ℕ) : d (w + 1) * u (w + 1) + u w * d w = 0 := by
  simpa only [Nat.add_sub_cancel] using
    signlessArrow_relation_of_consecutive k (G := AG)
      (fun i j hij => (diagramGraph_A_adj n i j).mp hij) (w + 1)

private theorem ladder_bottom_relation : d 0 * u 0 = 0 := by
  simpa only [Nat.zero_sub, signlessArrow_eq_zero k (i := 0) (j := 0)
    (fun _ _ => SimpleGraph.irrefl _), zero_mul, add_zero] using
    signlessArrow_relation_of_consecutive k (G := AG)
      (fun i j hij => (diagramGraph_A_adj n i j).mp hij) 0

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
    ladderValley_mul_ladderValley (ladder_relation k (n := n))
      (by omega) (by omega)]
  have h1 : m - (b.val - l) = m + l - b.val := by omega
  have h2 : (a.val - m) + (b.val - l) = a.val - (m + l - b.val) := by omega
  have h3 : (b.val - m) + (c.val - l) = c.val - (m + l - b.val) := by omega
  rw [h1, h2, h3]
  simp only [← mul_assoc]
  rw [((Commute.neg_one_right (e c)).pow_right ((b.val - l) * (b.val - m))).eq]

/-- The product is zero when commuting the descents past the climbs would cross rung zero. -/
@[simp]
theorem signlessPreprojectiveAValley_mul_eq_zero (a b c : Fin (DynkinType.A n).rank) {m l : ℕ}
    (hm : m ≤ a.val) (hbottom : m + l < b.val) :
    signlessPreprojectiveAValley k b c l * signlessPreprojectiveAValley k a b m = 0 := by
  rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def]
  simp only [mul_assoc]
  rw [target_ladderValley k a b (by omega) (by omega),
    target_ladderValley k a b (by omega) (by omega),
    ← mul_assoc (ladderValley u d l (b.val - l) (c.val - l)),
    ladderValley_mul_ladderValley_eq_zero (ladder_bottom_relation k (n := n))
      (ladder_relation k (n := n)) (by omega) (by omega), zero_mul, mul_zero]

/-- Valleys in noncomposable corners have zero product, with no bounds on their bottoms. -/
@[simp]
theorem signlessPreprojectiveAValley_mul_eq_zero_of_ne
    (a b c f : Fin (DynkinType.A n).rank) (m l : ℕ) (h : b ≠ f) :
    signlessPreprojectiveAValley k f c l * signlessPreprojectiveAValley k a b m = 0 := by
  classical
  have he : e f * e b = 0 := by
    rw [← map_mul, vertexIdempotent_mul_vertexIdempotent_of_ne
      (fun hfb => h (vertex_injective AG hfb).symm), map_zero]
  rw [signlessPreprojectiveAValley_def, signlessPreprojectiveAValley_def]
  simp only [mul_assoc]
  rw [← mul_assoc (e f), he, zero_mul, mul_zero, mul_zero]

end TauCeti

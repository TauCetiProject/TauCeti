/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basis
import all TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic

/-!
# The terminal power of the type-`D` fork backtracks

At the fork of the doubled `Dₙ` diagram, the two backtracks `x` and `y` square to zero.
Their sum has vanishing `(n - 2)`-nd power. Over every commutative ring, the
`(n - 2)`-nd power of their linear span is precisely the cyclic span of the alternating
word `x (x + y)^(n - 3)`, and the next power vanishes. Over fields, this word is
nonzero, so the terminal power is one-dimensional. This identifies the terminal power
of the two backtracks, needed for the Frobenius pairing of the type-`D` preprojective
algebra.

The local relations follow Crawley-Boevey, *Quiver algebras, weighted projective lines,
and the Deligne--Simpson problem*, Section 1. The alternating-word calculation uses
`TauCeti.span_pair_pow_succ_le`; the expected Frobenius pairing is described by Ringel,
*The preprojective algebra of a quiver*.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

section CommRing

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver DG)
local notation "c" => n - 3

/-- The backtrack from the fork of `Dₙ` into one of its two leaves: `true` selects
the leaf `n - 2` and `false` the leaf `n - 1`. -/
noncomputable def signlessPreprojectiveDForkBacktrack (l : Bool) : Π :=
  let j := if l then c + 1 else c + 2
  signlessArrow k DG j c * signlessArrow k DG c j

/-- The backtrack through the first fork leaf. -/
theorem signlessPreprojectiveDForkBacktrack_true :
    signlessPreprojectiveDForkBacktrack (n := n) k true =
      signlessArrow k DG (c + 1) c * signlessArrow k DG c (c + 1) := (rfl)

/-- The backtrack through the second fork leaf. -/
theorem signlessPreprojectiveDForkBacktrack_false :
    signlessPreprojectiveDForkBacktrack (n := n) k false =
      signlessArrow k DG (c + 2) c * signlessArrow k DG c (c + 2) := (rfl)

private theorem forkBacktrack_true :
    signlessPreprojectiveDForkBacktrack (n := n) k true = forkTurn k DG c (c + 1) := (rfl)

private theorem forkBacktrack_false :
    signlessPreprojectiveDForkBacktrack (n := n) k false = forkTurn k DG c (c + 2) := (rfl)

/-- Both leaf backtracks at the fork square to zero. -/
@[simp] theorem signlessPreprojectiveDForkBacktrack_mul_self (hn : 3 ≤ n) (l : Bool) :
    signlessPreprojectiveDForkBacktrack (n := n) k l *
      signlessPreprojectiveDForkBacktrack (n := n) k l = 0 := by
  cases l
  · rw [forkBacktrack_false]
    exact forkTurn_mul_self k (G := DG)
      (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn) (by omega)
      (by rw [DynkinType.rank_D]; omega)
  · rw [forkBacktrack_true]
    exact forkTurn_mul_self k (G := DG)
      (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn) (by omega)
      (by rw [DynkinType.rank_D]; omega)

/-- The sum of the leaf backtracks has zero `(n - 2)`-nd power. -/
@[simp] theorem signlessPreprojectiveDForkBacktrack_add_pow_eq_zero (hn : 3 ≤ n) :
    (signlessPreprojectiveDForkBacktrack (n := n) k true +
      signlessPreprojectiveDForkBacktrack (n := n) k false) ^ (c + 1) = 0 := by
  rw [forkBacktrack_true, forkBacktrack_false]
  exact forkTurn_add_pow_eq_zero k (G := DG) (by rw [DynkinType.rank_D]; omega)
    (by simpa only [DynkinType.rank_D] using diagramGraph_D_adj hn)

/-- The longest fork word is `x (x + y)^(n - 3)`, in later-factor-first order. -/
theorem signlessPreprojectiveDForkTopWord_eq (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inr ()) =
      signlessPreprojectiveDForkBacktrack (n := n) k true *
        (signlessPreprojectiveDForkBacktrack (n := n) k true +
          signlessPreprojectiveDForkBacktrack (n := n) k false) ^ c := by
  rw [signlessPreprojectiveDForkWords_inr, signlessPreprojectiveDBranchWord_def]
  simp only [preprojectiveDForkVertex_val, le_refl, ite_true, Nat.sub_self,
    ladderValley_zero_zero, mul_one, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    Nat.add_sub_cancel]
  simp only [signlessPreprojectiveDForkBacktrack, ite_true, ite_false]
  let e : Π := signlessPreprojectiveMk k _
    (vertexIdempotent k (vertex DG (preprojectiveDForkVertex n hn)))
  let x : Π := signlessArrow k DG (c + 1) c * signlessArrow k DG c (c + 1)
  let y : Π := signlessArrow k DG (c + 2) c * signlessArrow k DG c (c + 2)
  have hex : e * x = x := by
    simp only [e, x, ← mul_assoc, vertexIdempotent_mul_signlessArrow,
      preprojectiveDForkVertex_val, ↓reduceIte]
  have hxe : x * e = x := by
    simp only [e, x, mul_assoc, signlessArrow_mul_vertexIdempotent,
      preprojectiveDForkVertex_val, ↓reduceIte]
  have hye : y * e = y := by
    simp only [e, y, mul_assoc, signlessArrow_mul_vertexIdempotent,
      preprojectiveDForkVertex_val, ↓reduceIte]
  have hse : (x + y) * e = x + y := by rw [add_mul, hxe, hye]
  have hxe_pow (t : ℕ) : x * (x + y) ^ t * e = x * (x + y) ^ t := by
    induction t with
    | zero => simpa only [pow_zero, mul_one] using hxe
    | succ t ih =>
      simp only [pow_succ, mul_assoc, hse]
  -- The two corner idempotents in the unfolded fork word act as the identity on its factors.
  change e * (x * (x + y) ^ c) * e = x * (x + y) ^ c
  rw [← mul_assoc, hex, hxe_pow]

/-- The terminal power of the span of the two leaf backtracks is the line of the longest
alternating fork word. -/
theorem signlessPreprojectiveDForkBacktrack_span_pow_eq (hn : 3 ≤ n) :
    (Submodule.span k {signlessPreprojectiveDForkBacktrack (n := n) k true,
      signlessPreprojectiveDForkBacktrack (n := n) k false}) ^ (c + 1) =
        Submodule.span k {signlessPreprojectiveDForkWords k hn (.inr ())} := by
  let x := signlessPreprojectiveDForkBacktrack (n := n) k true
  let y := signlessPreprojectiveDForkBacktrack (n := n) k false
  let P := Submodule.span k {x, y}
  have hx : x ∈ P := Submodule.subset_span (Or.inl rfl)
  have hy : y ∈ P := Submodule.subset_span (Or.inr rfl)
  have hsum : x + y ∈ P := P.add_mem hx hy
  have htop : signlessPreprojectiveDForkWords k hn (.inr ()) = x * (x + y) ^ c :=
    signlessPreprojectiveDForkTopWord_eq k hn
  have hpow : (x + y) ^ (c + 1) = 0 :=
    signlessPreprojectiveDForkBacktrack_add_pow_eq_zero k hn
  apply le_antisymm
  · refine (span_pair_pow_succ_le (signlessPreprojectiveDForkBacktrack_mul_self k hn true)
      (signlessPreprojectiveDForkBacktrack_mul_self k hn false) c).trans ?_
    apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [← htop]
      exact Submodule.subset_span rfl
    · have hrel : y * (x + y) ^ c = -(x * (x + y) ^ c) := by
        have hs : x * (x + y) ^ c + y * (x + y) ^ c = 0 := by
          simpa only [add_mul, pow_succ'] using hpow
        exact eq_neg_of_add_eq_zero_right hs
      rw [hrel, ← htop]
      exact Submodule.neg_mem _ (Submodule.subset_span rfl)
  · apply Submodule.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    rw [htop, pow_succ']
    exact Submodule.mul_mem_mul hx (Submodule.pow_mem_pow P hsum c)

/-- One further product of leaf backtracks vanishes. -/
@[simp] theorem signlessPreprojectiveDForkBacktrack_span_pow_succ_eq_bot (hn : 3 ≤ n) :
    (Submodule.span k {signlessPreprojectiveDForkBacktrack (n := n) k true,
      signlessPreprojectiveDForkBacktrack (n := n) k false}) ^ (c + 2) = ⊥ := by
  exact span_pair_pow_succ_eq_bot
    (signlessPreprojectiveDForkBacktrack_mul_self k hn true)
    (signlessPreprojectiveDForkBacktrack_mul_self k hn false)
    (signlessPreprojectiveDForkBacktrack_add_pow_eq_zero k hn)

/-- The terminal fork word is annihilated on the left by every linear combination of the
two leaf backtracks. -/
theorem signlessPreprojectiveDForkBacktrack_mul_topWord_eq_zero (hn : 3 ≤ n)
    {z : Π} (hz : z ∈ Submodule.span k
      {signlessPreprojectiveDForkBacktrack (n := n) k true,
        signlessPreprojectiveDForkBacktrack (n := n) k false}) :
    z * signlessPreprojectiveDForkWords k hn (.inr ()) = 0 := by
  let P := Submodule.span k
    {signlessPreprojectiveDForkBacktrack (n := n) k true,
      signlessPreprojectiveDForkBacktrack (n := n) k false}
  have htop : signlessPreprojectiveDForkWords k hn (.inr ()) ∈ P ^ (c + 1) := by
    rw [signlessPreprojectiveDForkBacktrack_span_pow_eq k hn]
    exact Submodule.subset_span rfl
  have hmem : z * signlessPreprojectiveDForkWords k hn (.inr ()) ∈ P ^ (c + 2) := by
    rw [show c + 2 = (c + 1) + 1 by omega, pow_succ']
    exact Submodule.mul_mem_mul hz htop
  dsimp only [P] at hmem
  rw [signlessPreprojectiveDForkBacktrack_span_pow_succ_eq_bot k hn] at hmem
  simpa only [Submodule.mem_bot] using hmem

/-- The terminal fork word is annihilated on the right by every linear combination of the
two leaf backtracks. -/
theorem signlessPreprojectiveDForkTopWord_mul_backtrack_eq_zero (hn : 3 ≤ n)
    {z : Π} (hz : z ∈ Submodule.span k
      {signlessPreprojectiveDForkBacktrack (n := n) k true,
        signlessPreprojectiveDForkBacktrack (n := n) k false}) :
    signlessPreprojectiveDForkWords k hn (.inr ()) * z = 0 := by
  let P := Submodule.span k
    {signlessPreprojectiveDForkBacktrack (n := n) k true,
      signlessPreprojectiveDForkBacktrack (n := n) k false}
  have htop : signlessPreprojectiveDForkWords k hn (.inr ()) ∈ P ^ (c + 1) := by
    rw [signlessPreprojectiveDForkBacktrack_span_pow_eq k hn]
    exact Submodule.subset_span rfl
  have hmem : signlessPreprojectiveDForkWords k hn (.inr ()) * z ∈ P ^ (c + 2) := by
    rw [show c + 2 = (c + 1) + 1 by omega, pow_succ]
    exact Submodule.mul_mem_mul htop hz
  dsimp only [P] at hmem
  rw [signlessPreprojectiveDForkBacktrack_span_pow_succ_eq_bot k hn] at hmem
  simpa only [Submodule.mem_bot] using hmem

end CommRing

section Field

variable (k : Type*) [Field k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "c" => n - 3

/-- The longest alternating fork word survives over every field, including characteristic two. -/
theorem signlessPreprojectiveDForkTopWord_ne_zero (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inr ()) ≠ 0 :=
  LinearIndependent.ne_zero (.inr ()) (linearIndependent_signlessPreprojectiveDForkWords k hn)

/-- The terminal backtrack-span power at the type-`D` fork has dimension one. -/
@[simp] theorem finrank_signlessPreprojectiveDForkBacktrack_span_pow (hn : 3 ≤ n) :
    Module.finrank k (↥((Submodule.span k
      {signlessPreprojectiveDForkBacktrack (n := n) k true,
        signlessPreprojectiveDForkBacktrack (n := n) k false}) ^ (c + 1))) = 1 := by
  rw [signlessPreprojectiveDForkBacktrack_span_pow_eq k hn]
  exact finrank_span_singleton (signlessPreprojectiveDForkTopWord_ne_zero k hn)

end Field

end TauCeti

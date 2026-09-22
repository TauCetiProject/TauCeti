/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ginzburg.Basic

/-!
# The loop-count grading of the two-dimensional Ginzburg path algebra

The Ginzburg quiver of a quiver `Q` consists of the doubled arrows and one additional loop `t_i`
at every vertex.  Its cohomological grading gives doubled arrows degree `0` and the loops degree
`-1`.  This file introduces the companion natural-number weight
`TauCeti.ginzburgLoopCount`, which gives the same arrows weights `0` and `1` respectively.

The two path weights contain exactly the same information: the cohomological degree of a path is
the negative of its loop count.  Consequently the cohomological degree `-n` piece is literally the
loop-count degree `n` piece, not merely isomorphic to it, and every positive cohomological piece
vanishes.  In particular, degree zero is spanned precisely by paths containing no adjoined loop.
This is the path decomposition needed to identify the zeroth cohomology of the two-dimensional
Ginzburg DG algebra with the additive preprojective algebra.

## Main results

* `Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount`: the two weights
  of a Ginzburg path differ by sign.
* `TauCeti.gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount`: the degree `-n`
  cohomological piece is the piece containing exactly `n` adjoined loops.
* `TauCeti.gradeBy_ginzburgTwoDegree_eq_bot_of_pos`: positive cohomological pieces vanish.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 6.5.
* T. Etgü and Y. Lekili, *Koszul duality patterns in Floer theory*, Section 4.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

/-- The number of adjoined Ginzburg loops contributed by an arrow.  A doubled arrow contributes
zero and a loop `t_i` contributes one. -/
def ginzburgLoopCount : ∀ {i j : GinzburgQuiver Q}, (i ⟶ j) → ℕ
  | _, _, .double _ => 0
  | _, _, .loop _ => 1

@[simp]
theorem ginzburgLoopCount_double {i j : Q} (a : (i ⟶ j) ⊕ (j ⟶ i)) :
    ginzburgLoopCount (GinzburgHom.double a) = 0 := by
  simp [ginzburgLoopCount]

@[simp]
theorem ginzburgLoopCount_loop (i : Q) : ginzburgLoopCount (GinzburgHom.loop i) = 1 := by
  simp [ginzburgLoopCount]

/-- On every Ginzburg arrow, cohomological degree is the negative of loop count. -/
theorem ginzburgTwoDegree_eq_neg_ginzburgLoopCount :
    ∀ {i j : GinzburgQuiver Q} (e : i ⟶ j),
      ginzburgTwoDegree e = -((ginzburgLoopCount e : ℕ) : ℤ)
  | _, _, .double a => by
      rw [ginzburgTwoDegree_double (Q := Q), ginzburgLoopCount_double (Q := Q)]
      simp
  | _, _, .loop i => by
      rw [ginzburgTwoDegree_loop (Q := Q), ginzburgLoopCount_loop (Q := Q)]
      simp

/-- The cohomological degree of a Ginzburg path is the negative of its number of adjoined loops. -/
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount
    {i j : GinzburgQuiver Q} (p : Path i j) :
    p.addWeight ginzburgTwoDegree = -((p.addWeight ginzburgLoopCount : ℕ) : ℤ) := by
  induction p with
  | nil => rw [Path.addWeight_nil, Path.addWeight_nil]; rfl
  | cons p e ih =>
      rw [Path.addWeight_cons, Path.addWeight_cons, ih,
        ginzburgTwoDegree_eq_neg_ginzburgLoopCount e]
      push_cast
      omega

/-- A Ginzburg path has cohomological degree `-n` exactly when it contains `n` adjoined loops. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_neg_iff {i j : GinzburgQuiver Q}
    (p : Path i j) (n : ℕ) :
    p.addWeight ginzburgTwoDegree = -(n : ℤ) ↔ p.addWeight ginzburgLoopCount = n := by
  rw [p.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount]
  exact neg_inj.trans Int.ofNat_inj

/-- A Ginzburg path has cohomological degree zero exactly when it contains no adjoined loop. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_eq_zero_iff {i j : GinzburgQuiver Q}
    (p : Path i j) :
    p.addWeight ginzburgTwoDegree = 0 ↔ p.addWeight ginzburgLoopCount = 0 := by
  simpa using p.addWeight_ginzburgTwoDegree_eq_neg_iff 0

/-- Every Ginzburg path has nonpositive cohomological degree. -/
theorem _root_.Quiver.Path.addWeight_ginzburgTwoDegree_nonpos {i j : GinzburgQuiver Q}
    (p : Path i j) :
    p.addWeight ginzburgTwoDegree ≤ 0 := by
  rw [p.addWeight_ginzburgTwoDegree_eq_neg_addWeight_ginzburgLoopCount]
  exact neg_nonpos.mpr (Int.natCast_nonneg _)

/-- The loop count pulled back along `TauCeti.ginzburgOf` is the constant weight `0`.  This is
`TauCeti.ginzburgLoopCount_double` for an arrow of `Quiver.Symmetrify Q`, whose type is
definitionally the sum type but does not match it syntactically. -/
private theorem ginzburgLoopCount_ginzburgOf_map {a b : Symmetrify Q} (e : a ⟶ b) :
    ginzburgLoopCount (ginzburgOf.map e) = 0 :=
  ginzburgLoopCount_double e

/-- The inclusion of the doubled quiver contributes no adjoined loops to a path. -/
@[simp]
theorem _root_.Quiver.Path.addWeight_ginzburgLoopCount_mapPath {i j : Symmetrify Q}
    (p : Path i j) :
    (ginzburgOf.mapPath p).addWeight ginzburgLoopCount = 0 := by
  simp only [ginzburgOf.addWeight_mapPath, ginzburgLoopCount_ginzburgOf_map,
    Quiver.Path.addWeight_const, smul_zero]

section Pieces

variable (k : Type w) [Semiring k]

/-- The cohomological degree `-n` part of the Ginzburg path algebra is exactly its loop-count
degree `n` part. -/
theorem gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount (n : ℕ) :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree (-(n : ℤ)) =
      gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount n := by
  ext x
  simp only [mem_gradeBy_iff]
  constructor
  · intro hx p hp
    exact (p.2.2.addWeight_ginzburgTwoDegree_eq_neg_iff n).mp (hx p hp)
  · intro hx p hp
    exact (p.2.2.addWeight_ginzburgTwoDegree_eq_neg_iff n).mpr (hx p hp)

/-- The degree-zero cohomological piece consists exactly of linear combinations of paths with no
adjoined loop. -/
theorem gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree 0 =
      gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount 0 := by
  simpa using gradeBy_ginzburgTwoDegree_neg_eq_gradeBy_ginzburgLoopCount k 0

/-- Every positive cohomological piece of the two-dimensional Ginzburg path algebra vanishes. -/
theorem gradeBy_ginzburgTwoDegree_eq_bot_of_pos {m : ℤ} (hm : 0 < m) :
    gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree m = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_gradeBy_iff] at hx
  apply (pathAlgebraBasis k (GinzburgQuiver Q)).repr.injective
  ext p
  by_cases hp : p ∈ ((pathAlgebraBasis k (GinzburgQuiver Q)).repr x).support
  · have hdegree := hx p hp
    have hnonpos := p.2.2.addWeight_ginzburgTwoDegree_nonpos
    omega
  · rw [Finsupp.notMem_support_iff.mp hp]
    simp

end Pieces

section Differential

variable (k : Type w)

/-- The doubled path algebra lands in loop-count degree zero inside the Ginzburg path algebra. -/
theorem ginzburgMap_mem_gradeBy_ginzburgLoopCount_zero [CommSemiring k] [Finite Q]
    (x : pathAlgebra k (Symmetrify Q)) :
    ginzburgMap k x ∈ gradeBy (Q := GinzburgQuiver Q) k ginzburgLoopCount 0 := by
  rw [← gradeBy_ginzburgTwoDegree_zero_eq_gradeBy_ginzburgLoopCount_zero]
  exact ginzburgMap_mem_gradeBy_ginzburgTwoDegree k x

/-- Every cohomological degree-zero element is a cycle in the two-dimensional Ginzburg DG
algebra. -/
theorem ginzburgTwoDifferential_eq_zero_of_mem_gradeBy_zero [CommRing k] [Fintype Q]
    [∀ i j : Q, Fintype (i ⟶ j)] {x : pathAlgebra k (GinzburgQuiver Q)}
    (hx : x ∈ gradeBy (Q := GinzburgQuiver Q) k ginzburgTwoDegree 0) :
    ginzburgTwoDifferential k x = 0 := by
  have hmem := (isDGAlgebra_ginzburgTwoDifferential k).map_mem hx
  rw [gradeBy_ginzburgTwoDegree_eq_bot_of_pos k (by omega)] at hmem
  exact (Submodule.mem_bot k).mp hmem

end Differential

end TauCeti

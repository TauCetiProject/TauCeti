/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basic
public import TauCeti.RingTheory.Idempotents.Corner

/-!
# Corner words for the type-`D` preprojective algebra

For `n ≥ 3`, in Bourbaki's labelling of `Dₙ`, put `c = n - 3`. The long arm is `0 — ⋯ — c`, and the
fork leaves are `c + 1, c + 2`. The words below either stay on the long arm, or pass through
`c` with an alternating word in the two leaf backtracks between their entry and exit paths.
They give finite spanning families for the source/target corners of the signless preprojective
algebra. Independence is not asserted: the families deliberately retain redundant words.

Products are later-factor-first. The entry path is on the right and the exit path on the left.
The signless presentation agrees with the preprojective presentation of each orientation of this
bipartite diagram via sign rescaling.

## References

* W. Crawley-Boevey, *Quiver algebras, weighted projective lines, and the Deligne--Simpson
  problem*, Section 1, for the local relations.
* C. M. Ringel, *The preprojective algebra of a quiver*, for the finite-Dynkin Frobenius property.

The arm words use `TauCeti.ladderValley`; the alternating backtracks use the construction of
`TauCeti.Algebra.Algebra.SquareZeroPair`.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

attribute [local instance] forkNeighborSetFintype

variable (k : Type*) [CommRing k] {n : ℕ}

local notation "DG" => diagramGraph (DynkinType.cartanMatrix (DynkinType.D n))
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver DG)
local notation "π" => signlessPreprojectiveMk k (DoubledQuiver DG)
local notation "c" => n - 3
local notation "e" => fun a : Fin (DynkinType.D n).rank => π (vertexIdempotent k (vertex DG a))

/-- The corner word which stays on the long arm, with valley bottom `m` counted from the fork.
Its path interpretation requires `a, b ≤ n - 3` and `m ≤ min (n - 3 - a) (n - 3 - b)`. -/
noncomputable def signlessPreprojectiveDValley (a b : Fin (DynkinType.D n).rank) (m : ℕ) : Π :=
  e b * ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
    (fun r => signlessArrow k DG (c - r - 1) (c - r)) m
    (c - a.val - m) (c - b.val - m) * e a

/-- The projected arm-valley word. -/
theorem signlessPreprojectiveDValley_def (a b : Fin (DynkinType.D n).rank) (m : ℕ) :
    signlessPreprojectiveDValley k a b m =
      e b * ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
        (fun r => signlessArrow k DG (c - r - 1) (c - r)) m
        (c - a.val - m) (c - b.val - m) * e a := by
  rw [signlessPreprojectiveDValley]

/-- The zero-length arm word at `a` is its vertex idempotent. -/
@[simp]
theorem signlessPreprojectiveDValley_self (a : Fin (DynkinType.D n).rank) :
    signlessPreprojectiveDValley k a a (c - a.val) = e a := by
  rw [signlessPreprojectiveDValley_def]
  simp only [Nat.sub_self, ladderValley_zero_zero, mul_one, ← map_mul,
    vertexIdempotent_mul_self]

/-- Every arm-valley word lies in its source/target corner. -/
@[simp]
theorem signlessPreprojectiveDValley_mem_cornerSubmodule
    (a b : Fin (DynkinType.D n).rank) (m : ℕ) :
    signlessPreprojectiveDValley k a b m ∈ cornerSubmodule k (e b) (e a) := by
  have hid (i : Fin (DynkinType.D n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex DG i)) π
  rw [mem_cornerSubmodule_iff k (hid b) (hid a), signlessPreprojectiveDValley_def]
  simp only [← mul_assoc, (hid b).eq]
  simp only [mul_assoc, (hid a).eq]

/-- A corner word passing through the fork. With zero backtracks the middle word is `1`;
with `t > 0` backtracks it is `x * (x + y)^(t - 1)` or `y * (x + y)^(t - 1)`, selected by `l`.
Here `x, y` are the backtracks into the two fork leaves, each of path length two. -/
noncomputable def signlessPreprojectiveDBranchWord
    (a b : Fin (DynkinType.D n).rank) (l : Bool) (t : ℕ) : Π :=
  let turn := fun j => signlessArrow k DG j c * signlessArrow k DG c j
  let entry := if a.val ≤ c then
    ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
      (fun r => signlessArrow k DG (c - r - 1) (c - r)) 0 (c - a.val) 0
    else signlessArrow k DG a.val c
  let exit := if b.val ≤ c then
    ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
      (fun r => signlessArrow k DG (c - r - 1) (c - r)) 0 0 (c - b.val)
    else signlessArrow k DG c b.val
  e b * exit * (if t = 0 then 1 else
    (if l then turn (c + 1) else turn (c + 2)) * (turn (c + 1) + turn (c + 2)) ^ (t - 1)) *
      entry * e a

/-- The projected fork word, with its entry, middle, and exit factors. -/
theorem signlessPreprojectiveDBranchWord_def (a b : Fin (DynkinType.D n).rank) (l : Bool) (t : ℕ) :
    signlessPreprojectiveDBranchWord k a b l t =
      let turn := fun j => signlessArrow k DG j c * signlessArrow k DG c j
      let entry := if a.val ≤ c then
        ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
          (fun r => signlessArrow k DG (c - r - 1) (c - r)) 0 (c - a.val) 0
        else signlessArrow k DG a.val c
      let exit := if b.val ≤ c then
        ladderValley (fun r => signlessArrow k DG (c - r) (c - r - 1))
          (fun r => signlessArrow k DG (c - r - 1) (c - r)) 0 0 (c - b.val)
        else signlessArrow k DG c b.val
      e b * exit * (if t = 0 then 1 else
        (if l then turn (c + 1) else turn (c + 2)) * (turn (c + 1) + turn (c + 2)) ^ (t - 1)) *
          entry * e a := by
  rw [signlessPreprojectiveDBranchWord]

/-- Every fork word lies in its source/target corner. -/
@[simp]
theorem signlessPreprojectiveDBranchWord_mem_cornerSubmodule
    (a b : Fin (DynkinType.D n).rank) (l : Bool) (t : ℕ) :
    signlessPreprojectiveDBranchWord k a b l t ∈ cornerSubmodule k (e b) (e a) := by
  have hid (i : Fin (DynkinType.D n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex DG i)) π
  rw [mem_cornerSubmodule_iff k (hid b) (hid a), signlessPreprojectiveDBranchWord_def]
  dsimp only
  simp only [← mul_assoc, (hid b).eq]
  simp only [mul_assoc, (hid a).eq]

/-- The explicit finite family of normal words in the corner from `a` to `b`: arm valleys
away from the fork, fork words with at most `n - 3 + 1` backtracks (`n - 2` when `n ≥ 3`),
and the empty path at a leaf when `a = b`. The families need not be independent. -/
noncomputable def signlessPreprojectiveDNormalForms (a b : Fin (DynkinType.D n).rank) : Set Π :=
  (if a.val ≤ c ∧ b.val ≤ c then
    signlessPreprojectiveDValley k a b ''
      (Finset.Icc 1 (min (c - a.val) (c - b.val)) : Set ℕ) else ∅) ∪
  (fun p : Bool × Fin (c + 2) => signlessPreprojectiveDBranchWord k a b p.1 p.2) '' Set.univ ∪
  (if a = b ∧ c < a.val then {e a} else ∅)

/-- The normal-word family is the union of its three constituent families. -/
theorem signlessPreprojectiveDNormalForms_def (a b : Fin (DynkinType.D n).rank) :
    signlessPreprojectiveDNormalForms k a b =
      (if a.val ≤ c ∧ b.val ≤ c then
        signlessPreprojectiveDValley k a b ''
          (Finset.Icc 1 (min (c - a.val) (c - b.val)) : Set ℕ) else ∅) ∪
      (fun p : Bool × Fin (c + 2) => signlessPreprojectiveDBranchWord k a b p.1 p.2) '' Set.univ ∪
      (if a = b ∧ c < a.val then {e a} else ∅) := by
  rw [signlessPreprojectiveDNormalForms]

/-- The normal-word family is finite over any commutative coefficient ring. -/
theorem finite_signlessPreprojectiveDNormalForms (a b : Fin (DynkinType.D n).rank) :
    (signlessPreprojectiveDNormalForms k a b).Finite := by
  classical
  unfold signlessPreprojectiveDNormalForms
  apply Set.Finite.union
  · apply Set.Finite.union
    · split_ifs
      · exact (Finset.finite_toSet _).image _
      · exact Set.finite_empty
    · exact Set.finite_univ.image _
  · split_ifs
    · exact Set.finite_singleton _
    · exact Set.finite_empty

/-- Every normal word has the prescribed source and target corner. -/
theorem signlessPreprojectiveDNormalForms_subset_cornerSubmodule
    (a b : Fin (DynkinType.D n).rank) :
    signlessPreprojectiveDNormalForms k a b ⊆ cornerSubmodule k (e b) (e a) := by
  have hid (i : Fin (DynkinType.D n).rank) : IsIdempotentElem (e i) :=
    IsIdempotentElem.map (vertexIdempotent_mul_self (k := k) (vertex DG i)) π
  intro z hz
  unfold signlessPreprojectiveDNormalForms at hz
  rcases hz with (hz | ⟨p, -, rfl⟩) | hz
  · split_ifs at hz with h
    · obtain ⟨m, -, rfl⟩ := hz
      exact signlessPreprojectiveDValley_mem_cornerSubmodule k a b m
    · exact False.elim hz
  · exact signlessPreprojectiveDBranchWord_mem_cornerSubmodule k a b p.1 p.2
  · split_ifs at hz with h
    · obtain rfl := Set.mem_singleton_iff.mp hz
      obtain ⟨rfl, -⟩ := h
      exact (mem_cornerSubmodule_iff k (hid a) (hid a)).mpr (by simp only [(hid a).eq])
    · exact False.elim hz

end TauCeti

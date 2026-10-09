/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.NormalForm

/-!
# Reduced spanning words at the type-`D` fork

For the signless preprojective algebra of the Bourbaki-labelled `Dₙ` diagram, let `c = n - 3`
be the fork vertex and let `x, y` be its two leaf backtracks. The corner `e_c Π e_c` is spanned
by its unit, the two alternating words of each length `1, …, c`, and just one alternating word
of length `c + 1`. Here length counts backtracks, not arrows. The two longest words sum to
zero, because `(x + y)^(c + 1) = 0`. Thus there are `2 n - 4` spanning indices.

These are the fork-corner coordinates for the Frobenius pairing. This file proves spanning and
the resulting dimension upper bound. Linear independence over a field is proved in
`TauCeti.RepresentationTheory.Quiver.Preprojective.ADE.TypeD.Basis`. The longest
word relation holds in every source/target corner and over every commutative ring, including
characteristic two. As in the existing type-`D` word API, quotient carriers use
`forkNeighborSetFintype`; imported callers can select it as a local instance when writing
path-algebra representatives explicitly.

The path reduction is reused from the type-`D` normal forms. See Crawley-Boevey,
*Quiver algebras, weighted projective lines, and the Deligne--Simpson problem*, Section 1,
for the local relations, and Ringel, *The preprojective algebra of a quiver*, for the
finite-Dynkin Frobenius property.
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

/-- The fork vertex of the Bourbaki-labelled `Dₙ` diagram. -/
def preprojectiveDForkVertex (n : ℕ) (hn : 3 ≤ n) : Fin (DynkinType.D n).rank :=
  ⟨n - 3, by rw [DynkinType.rank_D]; omega⟩

@[simp]
theorem preprojectiveDForkVertex_val (hn : 3 ≤ n) :
    (preprojectiveDForkVertex n hn).val = n - 3 := (rfl)

/-- The reduced family of fork-corner words: the empty word, two alternating words for each
backtrack length `1, …, n - 3`, and one word of length `n - 2`. Over a field they are linearly
independent, by `TauCeti.linearIndependent_signlessPreprojectiveDForkWords`. -/
noncomputable def signlessPreprojectiveDForkWords (hn : 3 ≤ n) :
    Option (Bool × Fin c) ⊕ Unit → Π
  | .inl none => e (preprojectiveDForkVertex n hn)
  | .inl (some (l, t)) => signlessPreprojectiveDBranchWord k
      (preprojectiveDForkVertex n hn) (preprojectiveDForkVertex n hn) l (t.val + 1)
  | .inr _ => signlessPreprojectiveDBranchWord k
      (preprojectiveDForkVertex n hn) (preprojectiveDForkVertex n hn) true (c + 1)

@[simp]
theorem signlessPreprojectiveDForkWords_inl_none (hn : 3 ≤ n) :
    signlessPreprojectiveDForkWords k hn (.inl none) = e (preprojectiveDForkVertex n hn) := (rfl)

@[simp]
theorem signlessPreprojectiveDForkWords_inl_some (hn : 3 ≤ n) (l : Bool) (t : Fin c) :
    signlessPreprojectiveDForkWords k hn (.inl (some (l, t))) =
      signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
        (preprojectiveDForkVertex n hn) l (t.val + 1) := (rfl)

@[simp]
theorem signlessPreprojectiveDForkWords_inr (hn : 3 ≤ n) (u : Unit) :
    signlessPreprojectiveDForkWords k hn (.inr u) =
      signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
        (preprojectiveDForkVertex n hn) true (c + 1) := (rfl)

/-- At the fork, a word with no backtracks is the corner unit. -/
@[simp]
theorem signlessPreprojectiveDBranchWord_fork_zero (hn : 3 ≤ n) (l : Bool) :
    signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
      (preprojectiveDForkVertex n hn) l 0 = e (preprojectiveDForkVertex n hn) := by
  rw [signlessPreprojectiveDBranchWord_def]
  simp only [preprojectiveDForkVertex_val, le_refl, ite_true, Nat.sub_self,
    ladderValley_zero_zero, mul_one, ← map_mul, vertexIdempotent_mul_self]

private theorem fork_branchWord_mem_span (hn : 3 ≤ n) (l : Bool) (t : ℕ) (ht : t < c + 2) :
    signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
      (preprojectiveDForkVertex n hn) l t ∈
        Submodule.span k (Set.range (signlessPreprojectiveDForkWords k hn)) := by
  let M := Submodule.span k (Set.range (signlessPreprojectiveDForkWords k hn))
  cases t with
  | zero =>
    rw [signlessPreprojectiveDBranchWord_fork_zero]
    exact Submodule.subset_span ⟨.inl none, rfl⟩
  | succ t =>
    by_cases htc : t < c
    · exact Submodule.subset_span ⟨.inl (some (l, ⟨t, htc⟩)), rfl⟩
    · have htc' : t = c := by omega
      subst t
      have htrue : signlessPreprojectiveDBranchWord k (preprojectiveDForkVertex n hn)
          (preprojectiveDForkVertex n hn) true (c + 1) ∈ M :=
        Submodule.subset_span ⟨.inr (), rfl⟩
      cases l
      · rw [eq_neg_of_add_eq_zero_right (signlessPreprojectiveDBranchWord_add_eq_zero k hn _ _)]
        exact M.neg_mem htrue
      · exact htrue

/-- Every reduced fork word lies in the fork corner. -/
@[simp]
theorem signlessPreprojectiveDForkWords_mem_cornerSubmodule (hn : 3 ≤ n)
    (i : Option (Bool × Fin c) ⊕ Unit) :
    signlessPreprojectiveDForkWords k hn i ∈
      cornerSubmodule k (e (preprojectiveDForkVertex n hn))
        (e (preprojectiveDForkVertex n hn)) := by
  rcases i with (_ | ⟨l, t⟩) | u
  · rw [signlessPreprojectiveDForkWords_inl_none]
    simpa only [signlessPreprojectiveDBranchWord_fork_zero] using
      signlessPreprojectiveDBranchWord_mem_cornerSubmodule k
        (preprojectiveDForkVertex n hn) (preprojectiveDForkVertex n hn) false 0
  · exact signlessPreprojectiveDBranchWord_mem_cornerSubmodule k _ _ l (t.val + 1)
  · exact signlessPreprojectiveDBranchWord_mem_cornerSubmodule k _ _ true (c + 1)

/-- The reduced family spans the entire fork corner of the signless preprojective algebra of
`Dₙ`. It has `2 n - 4` indices; the two longest words are represented by just one index. -/
theorem cornerSubmodule_signlessPreprojective_D_fork_eq_span (hn : 3 ≤ n) :
    cornerSubmodule k (e (preprojectiveDForkVertex n hn)) (e (preprojectiveDForkVertex n hn)) =
      Submodule.span k (Set.range (signlessPreprojectiveDForkWords k hn)) := by
  apply le_antisymm
  · rw [cornerSubmodule_signlessPreprojective_D_eq_span_normalForms k hn]
    apply Submodule.span_le.mpr
    intro z hz
    rw [signlessPreprojectiveDNormalForms_def] at hz
    simp only [preprojectiveDForkVertex_val, le_refl, and_self, ite_true,
      Nat.sub_self, min_self, Finset.Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1),
      Finset.coe_empty, Set.image_empty, Set.empty_union, lt_self_iff_false, and_false,
      ite_false, Set.union_empty] at hz
    obtain ⟨⟨l, t⟩, -, rfl⟩ := hz
    exact fork_branchWord_mem_span k hn l t t.isLt
  · apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    exact signlessPreprojectiveDForkWords_mem_cornerSubmodule k hn i

/-- The natural-number rank of the fork corner is at most `2 n - 4`, over every nontrivial
commutative ring. Over a field it is equal to `2 n - 4`, by
`TauCeti.finrank_cornerSubmodule_signlessPreprojective_D_fork`. -/
theorem finrank_cornerSubmodule_signlessPreprojective_D_fork_le [Nontrivial k] (hn : 3 ≤ n) :
    Module.finrank k
      (cornerSubmodule k (e (preprojectiveDForkVertex n hn)) (e (preprojectiveDForkVertex n hn))) ≤
        2 * n - 4 := by
  rw [cornerSubmodule_signlessPreprojective_D_fork_eq_span k hn]
  have h := finrank_range_le_card (R := k) (signlessPreprojectiveDForkWords k hn)
  simp only [Fintype.card_sum, Fintype.card_option, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unit] at h
  exact h.trans_eq (by omega)

end TauCeti

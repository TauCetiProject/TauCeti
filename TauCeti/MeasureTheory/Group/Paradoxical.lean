/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.Equipartition
public import TauCeti.Algebra.Group.Action.Paradoxical
public import TauCeti.MeasureTheory.Measure.AddContent

/-!
# Invariant contents and paradoxical sets

Let a group `G` act on `X`, and let `m` be a finitely additive set function on all subsets of `X`,
`m : MeasureTheory.AddContent M (Set.univ : Set (Set X))`, which is invariant under the action:
`m (g • s) = m s`. Cutting a set into finitely many pieces and moving each piece by an element of
`G` preserves the total content, so equidecomposable sets have the same content
(`TauCeti.Equidecomposable.addContent_eq`).

Consequently a paradoxical set `S`, which splits into two disjoint sets each equidecomposable with
`S`, satisfies `m S + m S = m S`. For an `ℝ≥0∞`-valued content this forces `m S` to be zero or
infinite. In particular a group action admitting an invariant finitely additive probability on all
subsets of `X` is not paradoxical on all of `X`. This is the easy half of Tarski's
characterization of amenability by the absence of paradoxical decompositions.

## Main results

* `TauCeti.Equidecomposable.addContent_eq`: an invariant content takes equal values on
  equidecomposable sets.
* `TauCeti.Paradoxical.addContent_add_self`: an invariant content of a paradoxical set `S`
  satisfies `m S + m S = m S`.
* `TauCeti.Paradoxical.addContent_eq_zero`: a finite invariant `ℝ≥0∞`-valued content vanishes on
  paradoxical sets.
* `TauCeti.not_paradoxical_univ_of_addContent`: if `X` carries an invariant finitely additive
  probability on all subsets, then `X` is not paradoxical.

## References

* A. Garrido, *An introduction to amenable groups*, §1.
-/

public section

open Set MeasureTheory

open scoped ENNReal Pointwise

variable {X G M : Type*} [Group G] [MulAction G X]

namespace TauCeti

section AddCommMonoid

variable [AddCommMonoid M] {m : AddContent M (univ : Set (Set X))} {A B S : Set X}

/-- A content on all subsets which is invariant under the action of `G` takes equal values on sets
which are equidecomposable using `G`. -/
theorem Equidecomposable.addContent_eq (hm : ∀ (g : G) (s : Set X), m (g • s) = m s)
    (h : Equidecomposable G A B) : m A = m B := by
  obtain ⟨P, γ, hγ, rfl⟩ :=
    Equidecomp.exists_iff_exists_finpartition.1 (equidecomposable_iff.1 h)
  -- `A` and `B` are finite disjoint unions of the parts `s` and of their translates `γ s • s`.
  have hA : A = ⋃ s ∈ P.parts, id s := by rw [← Finset.sup_set_eq_biUnion, P.sup_parts]
  have hdisj : (P.parts : Set (Set X)).PairwiseDisjoint id :=
    Finset.supIndep_iff_pairwiseDisjoint.1 P.supIndep
  conv_lhs => rw [hA]
  rw [addContent_biUnion_eq isSetRing_univ (fun _ _ => mem_univ _) hdisj,
    addContent_biUnion_eq isSetRing_univ (fun _ _ => mem_univ _) hγ]
  exact Finset.sum_congr rfl fun s _ => (hm (γ s) s).symm

/-- An invariant content of a paradoxical set `S` satisfies `m S + m S = m S`: the set splits into
two disjoint sets, each with the same content as `S`. -/
theorem Paradoxical.addContent_add_self (hm : ∀ (g : G) (s : Set X), m (g • s) = m s)
    (hS : Paradoxical G S) : m S + m S = m S := by
  obtain ⟨-, A, B, hAB, rfl, hA, hB⟩ := paradoxical_iff.1 hS
  calc m (A ∪ B) + m (A ∪ B) = m A + m B := by rw [hA.addContent_eq hm, hB.addContent_eq hm]
    _ = m (A ∪ B) := (addContent_union isSetRing_univ (mem_univ A) (mem_univ B) hAB).symm

end AddCommMonoid

variable {m : AddContent ℝ≥0∞ (univ : Set (Set X))} {S : Set X}

/-- A finite invariant `ℝ≥0∞`-valued content on all subsets vanishes on every paradoxical set. -/
theorem Paradoxical.addContent_eq_zero (hm : ∀ (g : G) (s : Set X), m (g • s) = m s)
    (hS : Paradoxical G S) (hfin : m S ≠ ∞) : m S = 0 :=
  (ENNReal.add_right_inj hfin).1 ((hS.addContent_add_self hm).trans (add_zero _).symm)

/-- If `X` carries a finitely additive probability on all subsets which is invariant under the
action of `G`, then `X` is not paradoxical for this action. -/
theorem not_paradoxical_univ_of_addContent (hm : ∀ (g : G) (s : Set X), m (g • s) = m s)
    (h1 : m univ = 1) : ¬Paradoxical G (univ : Set X) := fun hS => by
  simpa [h1] using hS.addContent_eq_zero hm (by simp [h1])

end TauCeti

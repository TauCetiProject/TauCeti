/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.BraidEquivalence
public import TauCeti.GroupTheory.Coxeter.Dihedral
public import TauCeti.GroupTheory.Coxeter.Geometric

/-!
# Matsumoto's theorem

Any two reduced words representing the same element of a Coxeter group are connected by braid
moves. Consequently, generators in an arbitrary monoid satisfying the braid relations have a
well-defined value along reduced words. The generators need not be involutions, so this value
need not be a monoid homomorphism.

The relational statement is `TauCeti.braidEquivalent_of_isReduced_wordProd_eq`; the evaluation
statement is `TauCeti.matsumoto`. Both apply to arbitrary Coxeter systems, including infinite
groups and infinite Coxeter-matrix entries. `TauCeti.existsUnique_reducedWordLift` expresses the
result as a universal property: there is a unique function on the group agreeing with evaluation
of every reduced word.

## Implementation notes

Induction on length cancels a common first letter. For different first letters, Tits' rank-two
parabolic lemma supplies two reduced expressions with a common suffix and braid-related
prefixes. The geometric representation identifies the length of those prefixes with the
Coxeter-matrix entry. Induction then joins the original words to these expressions.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.9.
* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 3.3.
-/

public section

namespace TauCeti

open CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

-- This bridge is specific to the different-first-letters step of Matsumoto's induction.
private theorem exists_braidEquivalent_cons_of_isLeftDescent_pair {i j : B} (hne : i ≠ j)
    {w : W} (hi : cs.IsLeftDescent w i) (hj : cs.IsLeftDescent w j) :
    ∃ u v : List B, cs.IsReduced (i :: u) ∧ cs.IsReduced (j :: v) ∧
      cs.wordProd (i :: u) = w ∧ cs.wordProd (j :: v) = w ∧
      BraidEquivalent M (i :: u) (j :: v) := by
  obtain ⟨x, hm, hx, hx', hlen⟩ :=
    cs.exists_wordProd_alternatingWord_mul_of_isLeftDescent_pair hne hi hj
  rw [cs.orderOf_simple_mul_simple] at hm hx hx' hlen
  obtain ⟨σ, hσ, hprod⟩ := cs.exists_isReduced x
  have hA : cs.wordProd (braidWord M i j ++ σ) = w := by
    rw [cs.wordProd_append, ← hprod]; exact hx.symm
  have hB : cs.wordProd (braidWord M j i ++ σ) = w := by
    rw [cs.wordProd_append, ← hprod]
    simpa only [braidWord, M.symmetric j i] using hx'.symm
  have hredA : cs.IsReduced (braidWord M i j ++ σ) := by
    rw [CoxeterSystem.IsReduced, hA, hlen, hprod, hσ.eq]; simp
  have hbraid := (BraidEquivalent.braidWord (M := M) i j).append_right σ
  have hredB := (hbraid.isReduced_iff cs).mp hredA
  obtain ⟨m, heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have heq' : M j i = m + 1 := (M.symmetric j i).trans heq
  simp only [braidWord, heq, heq', alternatingWord_succ',
    List.cons_append] at hA hB hredA hredB hbraid
  by_cases hpar : Even m
  · simp only [hpar, ↓reduceIte] at hA hB hredA hredB hbraid
    exact ⟨_, _, hredB, hredA, hB, hA, hbraid.symm⟩
  · simp only [hpar, ↓reduceIte] at hA hB hredA hredB hbraid
    exact ⟨_, _, hredA, hredB, hA, hB, hbraid⟩

/-- **Matsumoto's theorem, relational form.** Two reduced words representing the same element
of a Coxeter group are connected by braid moves. -/
theorem braidEquivalent_of_isReduced_wordProd_eq {ω ω' : List B}
    (hω : cs.IsReduced ω) (hω' : cs.IsReduced ω')
    (hprod : cs.wordProd ω = cs.wordProd ω') : BraidEquivalent M ω ω' := by
  suffices H : ∀ n : ℕ, ∀ ω ω' : List B, ω.length = n → cs.IsReduced ω →
      cs.IsReduced ω' → cs.wordProd ω = cs.wordProd ω' → BraidEquivalent M ω ω' from
    H ω.length ω ω' rfl hω hω' hprod
  intro n
  induction n with
  | zero =>
      intro ω ω' hlen hred hred' hp
      have hlen' : ω'.length = 0 := by rw [← hred'.eq, ← hp, hred.eq, hlen]
      obtain rfl := List.length_eq_zero_iff.mp hlen
      obtain rfl := List.length_eq_zero_iff.mp hlen'
      exact .refl _
  | succ n ih =>
      -- Any two expressions with the same first letter reduce to words of length `n`.
      have sameHead : ∀ a : B, ∀ u v : List B, (a :: u).length = n + 1 →
          cs.IsReduced (a :: u) → cs.IsReduced (a :: v) →
          cs.wordProd (a :: u) = cs.wordProd (a :: v) →
          BraidEquivalent M (a :: u) (a :: v) := by
        intro a u v hlen hred hred' hp
        have hu : cs.IsReduced u := by simpa using hred.drop 1
        have hv : cs.IsReduced v := by simpa using hred'.drop 1
        have hp' : cs.wordProd u = cs.wordProd v := by
          simpa only [cs.wordProd_cons, mul_left_cancel_iff] using hp
        have huLen : u.length = n := by simpa only [List.length_cons, Nat.add_right_cancel_iff]
          using hlen
        exact (ih u v huLen hu hv hp').append_left [a]
      intro ω ω' hlen hred hred' hp
      obtain ⟨i, u, rfl⟩ := List.exists_cons_of_ne_nil (l := ω) (by
        intro h; simp [h] at hlen)
      have hlen' : ω'.length = n + 1 := by rw [← hred'.eq, ← hp, hred.eq, hlen]
      obtain ⟨j, v, rfl⟩ := List.exists_cons_of_ne_nil (l := ω') (by
        intro h; simp [h] at hlen')
      by_cases hij : i = j
      · subst j; exact sameHead i u v hlen hred hred' hp
      have descent : ∀ a : B, ∀ σ : List B, cs.IsReduced (a :: σ) →
          cs.IsLeftDescent (cs.wordProd (a :: σ)) a := by
        intro a σ hσ
        have ht : cs.IsReduced σ := by simpa using hσ.drop 1
        rw [cs.isLeftDescent_iff, cs.wordProd_cons, cs.simple_mul_simple_cancel_left,
          ← cs.wordProd_cons, hσ.eq, ht.eq, List.length_cons]
      obtain ⟨u', v', hu', hv', hpu', hpv', hbraid⟩ :=
        exists_braidEquivalent_cons_of_isLeftDescent_pair cs hij (descent i u hred)
          (hp.symm ▸ descent j v hred')
      have h₁ := sameHead i u u' hlen hred hu' hpu'.symm
      have h₂ := sameHead j v v' hlen' hred' hv' (hp.symm.trans hpv'.symm)
      exact h₁.trans (hbraid.trans h₂.symm)

/-- For reduced words, braid equivalence is exactly equality of the represented Coxeter-group
elements. -/
theorem braidEquivalent_iff_wordProd_eq {ω ω' : List B}
    (hω : cs.IsReduced ω) (hω' : cs.IsReduced ω') :
    BraidEquivalent M ω ω' ↔ cs.wordProd ω = cs.wordProd ω' :=
  ⟨fun h => h.wordProd_eq cs, braidEquivalent_of_isReduced_wordProd_eq cs hω hω'⟩

/-- **Matsumoto's theorem, monoid-valued form.** If the chosen generators satisfy all braid
relations, evaluating a reduced word depends only on the element it represents. No square
relations are required of the generators. -/
theorem matsumoto {G : Type*} [Monoid G] (f : B → G)
    (hbraid : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod)
    {ω ω' : List B} (hω : cs.IsReduced ω) (hω' : cs.IsReduced ω')
    (hprod : cs.wordProd ω = cs.wordProd ω') : (ω.map f).prod = (ω'.map f).prod :=
  (braidEquivalent_of_isReduced_wordProd_eq cs hω hω' hprod).prod_map_eq f hbraid

/-- Generators satisfying the braid relations extend uniquely to a function on the Coxeter
group whose value on every reduced expression is the product of those generators. -/
theorem existsUnique_reducedWordLift {G : Type*} [Monoid G] (f : B → G)
    (hbraid : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod) :
    ∃! F : W → G, ∀ ω : List B, cs.IsReduced ω → F (cs.wordProd ω) = (ω.map f).prod := by
  classical
  let F : W → G := fun w => ((cs.exists_isReduced w).choose.map f).prod
  have hF : ∀ ω : List B, cs.IsReduced ω → F (cs.wordProd ω) = (ω.map f).prod := by
    intro ω hω
    exact matsumoto cs f hbraid (cs.exists_isReduced (cs.wordProd ω)).choose_spec.1 hω
      (cs.exists_isReduced (cs.wordProd ω)).choose_spec.2.symm
  refine ⟨F, hF, ?_⟩
  intro F' hF'
  funext w
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  exact (hF' ω hω).trans (hF ω hω).symm

end TauCeti

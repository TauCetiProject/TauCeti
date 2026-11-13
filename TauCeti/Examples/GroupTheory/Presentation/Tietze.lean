/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Tietze
public import Mathlib.Data.ZMod.Basic

/-!
# Examples of changing generators in presentations

The presentation `⟨a, b | b = a², b²a = 1⟩` reduces to `⟨a | a⁵ = 1⟩`.
The latter has a nontrivial image in the cyclic group of order five. These checks also
exercise the public word and inverse-word equations without unfolding the equivalence.
A second change of generators squares the generator of `⟨a | a⁵ = 1⟩` and recovers it by
cubing. These substitutions are inverse only modulo the relation, not in the free group.

Adjoining the generator `b = a²` to `⟨a | a⁵⟩` and eliminating it again returns `a`. Splitting
the projective-plane relator `a²` along a fresh generator `d` gives `⟨a, d | a d, d⁻¹ a⟩`, which
is isomorphic to `⟨a | a²⟩` but not to `⟨a | a, a²⟩`, the group obtained by imposing the half `a`
as an additional relator: cutting along a fresh side is not the same as adding a relation.
-/

public section

open PresentedGroup

namespace TauCeti.Examples

private abbrev a : FreeGroup Unit := FreeGroup.of ()
private abbrev b : FreeGroup (Unit ⊕ Unit) := FreeGroup.of (Sum.inr ())
private abbrev a' : FreeGroup (Unit ⊕ Unit) := FreeGroup.of (Sum.inl ())

private abbrev definitions : Unit → FreeGroup Unit := fun _ ↦ a ^ 2
private abbrev relations : Set (FreeGroup (Unit ⊕ Unit)) := {b ^ 2 * a'}

example : FreeGroup.lift (Sum.elim FreeGroup.of definitions) '' relations = {a ^ 5} := by
  simp [relations, definitions, b, a', a, ← pow_mul, ← pow_succ]

-- The inverse includes `a`; the auxiliary generator is the square of that same element.
example : (eliminateGenerators definitions relations).symm (of ()) = of (Sum.inl ()) := by
  simp

example : eliminateGenerators definitions relations (of (Sum.inr ())) =
    (of () : PresentedGroup
      (FreeGroup.lift (Sum.elim FreeGroup.of definitions) '' relations)) ^ 2 := by
  rw [eliminateGenerators_of_inr]
  simp [definitions, a, of]

-- The two arbitrary-word equations are available to importing modules.
example (r : FreeGroup (Unit ⊕ Unit)) :
    eliminateGenerators definitions relations (mk _ r) =
      mk _ (FreeGroup.lift (Sum.elim FreeGroup.of definitions) r) := by
  simp

example (r : FreeGroup Unit) :
    (eliminateGenerators definitions relations).symm (mk _ r) =
      mk _ (FreeGroup.map Sum.inl r) := by
  simp

/-- The reduced presentation has a homomorphism to the cyclic group of order five
that is nontrivial on its generator. -/
theorem exists_nontrivial_hom_tietzeCyclicFive :
    ∃ f : PresentedGroup ({FreeGroup.of () ^ 5} : Set (FreeGroup Unit)) →*
      Multiplicative (ZMod 5), f (of ()) ≠ 1 := by
  let f : PresentedGroup ({a ^ 5} : Set (FreeGroup Unit)) →* Multiplicative (ZMod 5) :=
    toGroup (f := fun _ ↦ Multiplicative.ofAdd (1 : ZMod 5)) (by
      rintro r (rfl : r = a ^ 5)
      simp only [map_pow, a, FreeGroup.lift_apply_of]
      decide)
  refine ⟨f, ?_⟩
  simpa [f] using (by decide : (1 : ZMod 5) ≠ 0)

/-- Squaring and cubing give inverse generator dictionaries for the cyclic presentation of
order five. In particular the dictionaries need only be inverse modulo the relators. -/
theorem exists_equiv_tietzeCyclicFive_square :
    ∃ e : PresentedGroup ({FreeGroup.of () ^ 5} : Set (FreeGroup Unit)) ≃*
        PresentedGroup ({FreeGroup.of () ^ 5} : Set (FreeGroup Unit)),
      e (of ()) = of () ^ 2 ∧ e.symm (of ()) = of () ^ 3 := by
  let R : Set (FreeGroup Unit) := {a ^ 5}
  have h5 : (of () : PresentedGroup R) ^ 5 = 1 := by
    have h := one_of_mem (Set.mem_singleton (a ^ 5))
    rw [map_pow] at h
    exact h
  have hpow (k : ℕ) : ∀ r ∈ R, mk R (FreeGroup.lift (fun _ : Unit ↦ a ^ k) r) = 1 := by
    rintro r (rfl : r = a ^ 5)
    simpa only [a, map_pow, FreeGroup.lift_apply_of, ← pow_mul, Nat.mul_comm k 5, of,
      one_pow] using congrArg (· ^ k) h5
  have h6 : (of () : PresentedGroup R) ^ 6 = of () := by
    rw [pow_succ, h5, one_mul]
  let e := equivOfGeneratorWords (R := R) (S := R)
    (fun _ : Unit ↦ a ^ 2) (fun _ : Unit ↦ a ^ 3) (hpow 2) (hpow 3)
    (fun () ↦ by simpa [a, of, ← pow_mul] using h6)
    (fun () ↦ by simpa [a, of, ← pow_mul] using h6)
  refine ⟨e, ?_, ?_⟩
  · rw [equivOfGeneratorWords_of, map_pow]
    simp only [a, of, R]
  · rw [equivOfGeneratorWords_symm_of, map_pow]
    simp only [a, of, R]

-- No finiteness or nonemptiness assumption on the generator families is needed.
example (w : Empty → FreeGroup Empty) (R : Set (FreeGroup (Empty ⊕ Empty))) :
    (eliminateGenerators w R).symm.toMonoidHom.comp
      (eliminateGenerators w R).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp

-- Adjoining `b = a²` to `⟨a | a⁵⟩` and then eliminating it returns the generator `a`.
example : (eliminateGenerators definitions (FreeGroup.map Sum.inl '' {a ^ 5}))
    (adjoinGenerators definitions {a ^ 5} (of ())) = of () := by
  simp

example : (adjoinGenerators definitions {a ^ 5}).symm (of (Sum.inr ())) =
    (of () : PresentedGroup ({a ^ 5} : Set (FreeGroup Unit))) ^ 2 := by
  rw [adjoinGenerators_symm_of_inr]
  simp [definitions, a, of]

-- The two word dictionaries of adjoining generators compose to the identity under `simp`.
example {α β : Type*} (w : β → FreeGroup α) (R : Set (FreeGroup α)) (r : FreeGroup α) :
    (adjoinGenerators w R).symm (adjoinGenerators w R (mk R r)) = mk R r := by
  simp

-- Splitting the projective-plane relator `a²` along a fresh side `d` sends `d` back to `a`.
example : (splitRelator ∅ a a).symm (of (Sum.inr ())) = of () := by
  rw [splitRelator_symm_of_inr]
  simp [a, of]

-- The two word dictionaries of splitting a relator compose to the identity under `simp`.
example {α : Type*} (R : Set (FreeGroup α)) (u v r : FreeGroup α) :
    (splitRelator R u v).symm (splitRelator R u v (mk _ r)) = mk _ r := by
  simp

/-- Splitting the relator `a²` of `⟨a | a²⟩` along a fresh generator `d` gives
`⟨a, d | a d, d⁻¹ a⟩`, the target of `PresentedGroup.splitRelator ∅ a a`. This group is not
isomorphic to `⟨a | a, a²⟩`, the group obtained by imposing the half `a` of the split relator as
an additional relation instead of introducing a fresh side. -/
theorem not_nonempty_tietzeCyclicTwo_split_mulEquiv_pair : ¬Nonempty (PresentedGroup
    ({FreeGroup.map Sum.inl (FreeGroup.of ()) * FreeGroup.of (Sum.inr ()),
        (FreeGroup.of (Sum.inr ()))⁻¹ * FreeGroup.map Sum.inl (FreeGroup.of ())} ∪
      FreeGroup.map Sum.inl '' ∅ : Set (FreeGroup (Unit ⊕ Unit))) ≃*
    PresentedGroup ({FreeGroup.of (), FreeGroup.of () * FreeGroup.of ()} :
      Set (FreeGroup Unit))) := by
  rintro ⟨e⟩
  -- The additional relator `a` kills the only generator.
  have hmk : mk ({a, a * a} : Set (FreeGroup Unit)) = 1 :=
    FreeGroup.ext_hom _ _ fun _ ↦ one_of_mem (Set.mem_insert _ _)
  have he (y) : e y = 1 := by
    obtain ⟨w, hw⟩ := mk_surjective _ (e y)
    rw [← hw, hmk, MonoidHom.one_apply]
  -- Transported back through the split, `a = 1` in `⟨a | a²⟩`, which maps onto `ℤ/2`.
  have h1 : (of () : PresentedGroup (insert (a * a) (∅ : Set (FreeGroup Unit)))) = 1 :=
    (splitRelator ∅ a a).map_eq_one_iff.mp (e.map_eq_one_iff.mp (he _))
  let f : PresentedGroup (insert (a * a) (∅ : Set (FreeGroup Unit))) →* Multiplicative (ZMod 2) :=
    toGroup (f := fun _ ↦ Multiplicative.ofAdd 1) (by
      simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false, forall_eq, map_mul, a,
        FreeGroup.lift_apply_of]
      decide)
  simpa [f] using congrArg f h1

end TauCeti.Examples

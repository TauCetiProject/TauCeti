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

end TauCeti.Examples

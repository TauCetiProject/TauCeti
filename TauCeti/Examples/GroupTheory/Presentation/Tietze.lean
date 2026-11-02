/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Tietze
public import Mathlib.Data.ZMod.Basic

/-!
# Examples of Tietze generator elimination

The presentation `⟨a, b | b = a², b²a = 1⟩` reduces to `⟨a | a⁵ = 1⟩`.
The latter has a nontrivial image in the cyclic group of order five. These checks also
exercise the public word and inverse-word equations without unfolding the equivalence.
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

-- No finiteness or nonemptiness assumption on the generator families is needed.
example (w : Empty → FreeGroup Empty) (R : Set (FreeGroup (Empty ⊕ Empty))) :
    (eliminateGenerators w R).symm.toMonoidHom.comp
      (eliminateGenerators w R).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp

end TauCeti.Examples

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Counting.Vaught
public import TauCeti.ModelTheory.Satisfiability

/-!
# Vaught's conjecture for first-order theories

Vaught's original question concerns a complete first-order theory `T` in a countable language:
are its countably infinite models countably many up to isomorphism whenever they are not
perfectly many? `FirstOrderVaughtConjecture` states this for countable relational languages in
universe zero, with the models on `ℕ` read through the model class
`TauCeti.RelationalConfiguration.modelsOfTheory T`.

A first-order theory in a countable relational language is a countable set of sentences, so the
countable conjunction of its image in `L_{ω₁ω}` is one sentence with the same models. Applying the
perfect-set conjecture `TauCeti.VaughtConjecture` to that sentence conjoined with infinitude gives
`TauCeti.VaughtConjecture.firstOrder`. Completeness of `T` is not used in that implication, and the
converse implication is not claimed: the two conjectures are distinct statements.

Translating a theory along a language equivalence preserves completeness and Vaught's dichotomy
for its models on `ℕ`. With the universe lift and the small presentation of a countable language,
`TauCeti.firstOrderVaughtConjecture_iff_forall_universe` shows that the first-order conjecture
does not depend on the universes of the language.

## Main definitions

* `TauCeti.FirstOrderVaughtConjecture`: Vaught's conjecture for complete first-order theories in
  countable relational languages.

## Main results

* `FirstOrder.Language.LEquiv.countable_or_hasPerfectAntichainOn_modelsOfTheory_onTheory_iff`:
  the dichotomy for the models of a theory transfers along a language equivalence.
* `TauCeti.VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory`: the perfect-set
  conjecture gives the dichotomy for the models on `ℕ` of every first-order theory in a countable
  relational language, in any universes.
* `TauCeti.VaughtConjecture.firstOrder`: the perfect-set conjecture implies the first-order
  conjecture.
* `TauCeti.firstOrderVaughtConjecture_iff_forall_universe`: the first-order conjecture in
  universe zero is equivalent to its statement in any fixed pair of universes.

## References

* R. L. Vaught, *Denumerable models of complete theories*, in Infinitistic Methods (1961),
  303–321.
* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016), for the
  passage from first-order theories to `L_{ω₁ω}` sentences.
-/

public section

universe u v u' v'

open FirstOrder FirstOrder.Language

namespace FirstOrder.Language.LEquiv

open TauCeti TauCeti.RelationalConfiguration

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (e : L ≃ᴸ L') {V : Type*}

/-- **Vaught's dichotomy for a first-order theory along a language equivalence.** The models on
`V` of a first-order theory meet countably many isomorphism classes, or contain a nonempty perfect
set of pairwise non-isomorphic ones, exactly when the same holds for the models of its translation
along `e`. -/
theorem countable_or_hasPerfectAntichainOn_modelsOfTheory_onTheory_iff (T : L.Theory) :
    (Countable (Quotient ((isoSetoid L' V).comap
        (Subtype.val : modelsOfTheory (V := V) (e.toLHom.onTheory T) → _))) ∨
      (isoSetoid L' V).HasPerfectAntichainOn (modelsOfTheory (V := V) (e.toLHom.onTheory T))) ↔
    (Countable (Quotient ((isoSetoid L V).comap (Subtype.val : modelsOfTheory (V := V) T → _))) ∨
      (isoSetoid L V).HasPerfectAntichainOn (modelsOfTheory (V := V) T)) := by
  rw [← image_onConfiguration_modelsOfTheory, e.countable_quotient_comap_isoSetoid_image_iff,
    Setoid.hasPerfectAntichainOn_image_homeomorph_iff _
      (fun _ _ => e.isoSetoid_onConfiguration_iff)]

end FirstOrder.Language.LEquiv

namespace TauCeti

open RelationalConfiguration

/-- Vaught's conjecture for complete first-order theories, in Vaught's original setting of
countably infinite models: for every countable relational language in universe zero, the models on
`ℕ` of a complete first-order theory meet countably many isomorphism classes, or contain a nonempty
perfect set of pairwise non-isomorphic models. This is an open conjecture, not an assertion made by
the library. -/
def FirstOrderVaughtConjecture : Prop :=
  ∀ (L : Language.{0, 0}) [L.IsRelational] [Countable (Σ n, L.Relations n)] (T : L.Theory),
    T.IsComplete →
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory (V := ℕ) T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory (V := ℕ) T)

/-- The quantifiers in the first-order conjecture. -/
theorem firstOrderVaughtConjecture_iff :
    FirstOrderVaughtConjecture ↔ ∀ (L : Language.{0, 0}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (T : L.Theory), T.IsComplete →
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory (V := ℕ) T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory (V := ℕ) T) :=
  Iff.rfl

/-- The perfect-set Vaught conjecture gives Vaught's dichotomy for the models on `ℕ` of every
first-order theory in a countable relational language, in any universes, complete or not: these
models are those of the countable conjunction of the theory. -/
theorem VaughtConjecture.countable_or_hasPerfectAntichainOn_modelsOfTheory
    (h : VaughtConjecture) {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ n, L.Relations n)] (T : L.Theory) :
    Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory (V := ℕ) T → _))) ∨
      (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory (V := ℕ) T) := by
  have hT : (BoundedFormula.toOmega '' T).Countable := (Set.to_countable T).image _
  rw [← modelsOf_conjunction_image_toOmega hT]
  exact (hasVaughtDichotomy_inf_infiniteSentence_iff _).1
    (vaughtConjecture_iff_forall_universe.1 h L _)

/-- The perfect-set Vaught conjecture implies Vaught's conjecture for complete first-order
theories. -/
theorem VaughtConjecture.firstOrder (h : VaughtConjecture) : FirstOrderVaughtConjecture :=
  fun _ _ _ T _ => h.countable_or_hasPerfectAntichainOn_modelsOfTheory T

/-- The first-order Vaught conjecture holds for complete theories in countable relational
languages in any fixed pair of universes exactly when it holds in universe zero. A language in
universe zero is presented in the larger universes by `FirstOrder.Language.uLift`, and conversely
a countable language is presented in universe zero by `FirstOrder.Language.smallPresentation`;
translation along either presentation preserves completeness. -/
theorem firstOrderVaughtConjecture_iff_forall_universe :
    FirstOrderVaughtConjecture ↔ ∀ (L : Language.{u, v}) [L.IsRelational]
      [Countable (Σ n, L.Relations n)] (T : L.Theory), T.IsComplete →
      Countable (Quotient ((isoSetoid L ℕ).comap (Subtype.val : modelsOfTheory (V := ℕ) T → _))) ∨
        (isoSetoid L ℕ).HasPerfectAntichainOn (modelsOfTheory (V := ℕ) T) := by
  refine ⟨fun h L _ _ T hT => ?_, fun h L _ _ T hT => ?_⟩
  · let e := L.smallPresentationEquiv
    rw [← e.countable_or_hasPerfectAntichainOn_modelsOfTheory_onTheory_iff]
    exact h _ _ (LEquiv.isComplete_onTheory_iff.2 hT)
  · let e := L.uLiftEquiv.{0, 0, u, v}
    rw [← e.countable_or_hasPerfectAntichainOn_modelsOfTheory_onTheory_iff]
    exact h _ _ (LEquiv.isComplete_onTheory_iff.2 hT)

end TauCeti

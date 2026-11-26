/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.Functional.Complexity
import TauCeti.ModelTheory.RelationalConfiguration.GraphClass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MonoidAlgebra.Cardinal
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.ModelTheory.Algebra.Field.CharP
import Mathlib.ModelTheory.Graph

/-!
# Models of first-order theories in the functional coding space

In the functional coding space of the language of graphs, every function table is the empty map,
and the models of Mathlib's `Theory.simpleGraph` are exactly the configurations whose relation
code lies in `graphClass`. In the language of rings, the models of `Theory.fieldOfChar 2` form an
isomorphism-invariant Borel class, which contains a code of the countable field `𝔽₂(t)` and no
code of `ℚ`.
-/

open FirstOrder FirstOrder.Language MeasureTheory TauCeti RelationalConfiguration
  FunctionalConfiguration

/-! ### Simple graphs -/

-- The language of graphs has no function symbols, so every function table is the empty map.
example (F : FunctionalConfiguration Language.graph ℕ) :
    IsEmpty (Arg Language.graph ℕ) ∧ ∀ T : Arg Language.graph ℕ → ℕ, F = mk T F.rel := by
  have : IsEmpty (Arg Language.graph ℕ) := ⟨fun p => by obtain ⟨⟨_, f⟩, _⟩ := p; exact f.elim⟩
  exact ⟨this, fun T => ext (funext isEmptyElim) (rel_mk T F.rel).symm⟩

-- The models of `Theory.simpleGraph` are the configurations whose relation code is a code of a
-- simple graph.
example (F : FunctionalConfiguration Language.graph ℕ) :
    @Theory.Model _ ℕ F.toStructure Theory.simpleGraph ↔ F.rel ∈ graphClass := by
  let := F.toStructure
  rw [Theory.simpleGraph_model_iff, mem_graphClass, isSimpleGraph_iff]
  simp only [toStructure_relMap, ← adjAtom_def]
  refine ⟨fun ⟨h₁, h₂⟩ => ⟨fun u v => ?_, fun v => ?_⟩, fun ⟨h₁, h₂⟩ =>
    ⟨⟨fun v h => by simp [h₂ v] at h⟩, ⟨fun u v h => by rwa [← h₁]⟩⟩⟩
  · exact Bool.eq_iff_iff.2 ⟨fun h => h₂.symm _ _ h, fun h => h₂.symm _ _ h⟩
  · simpa using h₁.irrefl v

/-! ### Fields of characteristic two -/

-- The models of the theory of fields of characteristic two form an isomorphism-invariant Borel
-- class of the functional coding space on `ℕ`.
example : MeasurableSet[borel (FunctionalConfiguration Language.ring ℕ)]
    {F : FunctionalConfiguration Language.ring ℕ |
      @Theory.Model _ ℕ F.toStructure (Theory.fieldOfChar 2)} :=
  measurableSet_setOf_model (Set.to_countable _)

example : IsomorphismInvariant {F : FunctionalConfiguration Language.ring ℕ |
    @Theory.Model _ ℕ F.toStructure (Theory.fieldOfChar 2)} :=
  isomorphismInvariant_iff.2 fun F G h hF =>
    (@Theory.model_iff _ ℕ G.toStructure _).2 fun φ hφ =>
      (realize_sentence_iff_of_isoSetoid h φ).1 ((@Theory.model_iff _ ℕ F.toStructure _).1 hF φ hφ)

-- The class contains a code of the countable field `𝔽₂(t)`: transport its ring structure to `ℕ`
-- along a bijection.
example : ∃ F : FunctionalConfiguration Language.ring ℕ,
    @Theory.Model _ ℕ F.toStructure (Theory.fieldOfChar 2) ∧
      Nonempty (@Language.Equiv _ ℕ (RatFunc (ZMod 2)) F.toStructure
        (FirstOrder.Ring.compatibleRingOfRing (RatFunc (ZMod 2))).toStructure) := by
  let _ := FirstOrder.Ring.compatibleRingOfRing (RatFunc (ZMod 2))
  have : Countable (RatFunc (ZMod 2)) :=
    (IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial (ZMod 2)))).countable
  have : Infinite (RatFunc (ZMod 2)) :=
    .of_injective _ (IsFractionRing.injective (Polynomial (ZMod 2)) (RatFunc (ZMod 2)))
  let e : RatFunc (ZMod 2) ≃ ℕ := nonempty_equiv_of_countable.some
  refine ⟨@FunctionalConfiguration.ofStructure _ ℕ e.inducedStructure, ?_, ?_⟩
  · rw [FunctionalConfiguration.toStructure_ofStructure]
    exact @StrongHomClass.theory_model _ _ ℕ _ e.inducedStructure _ _ _ _
      e.inducedStructureEquiv _
  · rw [FunctionalConfiguration.toStructure_ofStructure]
    let := e.inducedStructure (L := Language.ring)
    exact ⟨e.inducedStructureEquiv.symm⟩

-- The class contains no code of `ℚ`: a structure on `ℕ` isomorphic to `ℚ` has characteristic
-- zero.
example (F : FunctionalConfiguration Language.ring ℕ)
    (hF : @Theory.Model _ ℕ F.toStructure (Theory.fieldOfChar 2)) :
    IsEmpty (@Language.Equiv _ ℕ ℚ F.toStructure
      (FirstOrder.Ring.compatibleRingOfRing ℚ).toStructure) := by
  let _ := FirstOrder.Ring.compatibleRingOfRing ℚ
  let := F.toStructure
  refine ⟨fun e => ?_⟩
  have : (Theory.fieldOfChar 2).Model ℚ :=
    @StrongHomClass.theory_model _ ℕ ℚ F.toStructure _ _ _ _ _ e hF
  have := Field.charP_of_model_fieldOfChar 2 ℚ
  exact two_ne_zero (CharP.cast_eq_zero ℚ 2)

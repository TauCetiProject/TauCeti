/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.ModelTheory.Graph
import TauCeti.ModelTheory.RelationalConfiguration.Complexity

/-!
# Examples: clopen, closed and Gδ model classes

For a binary relation symbol `R`, the configurations on `ℕ` satisfying the `∀∃` sentence
`∀ x, ∃ y, R(x, y)` form a Gδ set, hence a Polish space in the subspace topology. Irreflexivity of
`R` is a universal sentence, so its model class is closed, and the simple-graph theory, whose
axioms are universal, has a closed model class on every carrier.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration BoundedFormula

-- The false sentence has no models.
example {L : Language} [L.IsRelational] : modelsOf (V := ℕ) (⊥ : L.Sentenceω) = ∅ :=
  modelsOf_bot

-- The universal closure `alls` of the existential formula `∃ y, R(x, y)` in one free variable is
-- the sentence `∀ x, ∃ y, R(x, y)`.
example {L : Language} (R : L.Relations 2) :
    ((R.boundedFormula₂ (&0) (&1)).ex : L.BoundedFormula Empty 1).alls =
      (R.boundedFormula₂ (&0) (&1)).ex.all :=
  rfl

-- So the configurations on `ℕ` satisfying `∀ x, ∃ y, R(x, y)` form a Gδ set.
example {L : Language} [L.IsRelational] (R : L.Relations 2) :
    IsGδ (modelsOf (V := ℕ)
      ((R.boundedFormula₂ (&0) (&1)).ex : L.BoundedFormula Empty 1).alls.toOmega) :=
  (IsAtomic.rel R _).isExistential.ex.isGδ_modelsOf_toInf_alls

-- With countably many relation symbols the configuration space on `ℕ` is Polish, and so is this
-- Gδ model class in its subspace topology.
example {L : Language} [L.IsRelational] [∀ n, Countable (L.Relations n)] (R : L.Relations 2) :
    PolishSpace (modelsOf (V := ℕ)
      ((R.boundedFormula₂ (&0) (&1)).ex : L.BoundedFormula Empty 1).alls.toOmega) :=
  (IsAtomic.rel R _).isExistential.ex.isGδ_modelsOf_toInf_alls.polishSpace

-- Irreflexivity is a universal sentence, so its model class is closed on every carrier.
example {L : Language} [L.IsRelational] {V : Type*} (R : L.Relations 2) :
    IsClosed (modelsOf (V := V) R.irreflexive.toOmega) :=
  ((IsAtomic.rel R _).isQF.imp isQF_bot).isUniversal.all.isClosed_modelsOf_toInf

-- The simple-graph axioms, irreflexivity and symmetry of adjacency, are universal, so the
-- configurations of simple graphs form a closed set on every carrier.
example {V : Type*} : IsClosed (modelsOfTheory (V := V) Theory.simpleGraph) := by
  refine isClosed_modelsOfTheory ?_
  simp only [Theory.simpleGraph, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  exact ⟨((IsAtomic.rel _ _).isQF.imp isQF_bot).isUniversal.all,
    ((IsAtomic.rel _ _).isQF.imp (IsAtomic.rel _ _).isQF).isUniversal.all.all⟩

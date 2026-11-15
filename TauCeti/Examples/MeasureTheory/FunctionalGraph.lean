/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Constructions.Polish.Graph

/-!
# Evaluating functions from their Borel graphs

These examples recover an existing function from its graph on a subset, evaluate the inverse of
the graph-domain equivalence, and check that empty targets require no arbitrary default value.
-/

open Set

section Evaluation

variable {X Y : Type*} {s : Set X} {f : X → Y}

-- Recover the original function, even if the domain is a proper subset.
example (x : Prod.fst '' s.graphOn f) :
    (fst_injOn_graph : InjOn Prod.fst (s.graphOn f)).graphValue x = f x := by
  simp

end Evaluation

section StandardBorel

variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y] {G : Set (X × Y)}
  (hG : MeasurableSet G) (hinj : InjOn Prod.fst G)

-- The domain itself is Borel by the existing Lusin–Souslin API.
example : MeasurableSet (Prod.fst '' G) :=
  hG.image_of_measurable_injOn measurable_fst hinj

-- The inverse equivalence recovers the entire graph point, not just its first coordinate.
example (p : X × Y) (hp : p ∈ G) :
    (hG.graphDomainEquiv hinj).symm ⟨p.1, mem_image_of_mem Prod.fst hp⟩ = ⟨p, hp⟩ := by
  simp only [MeasurableSet.graphDomainEquiv_symm_apply, hinj.graphValue_eq_of_mem hp]

-- Evaluation is measurable independently of the choice of presentation of the graph.
example {f : (Prod.fst '' G) → Y} (hf : ∀ x : Prod.fst '' G, ((x : X), f x) ∈ G) :
    Measurable f := by
  rw [hinj.eq_graphValue hf]
  exact hinj.measurable_graphValue hG

end StandardBorel

-- In particular, the construction applies when even the target is empty.
example : Measurable
    (injOn_empty Prod.fst : InjOn Prod.fst (∅ : Set (ℕ × Empty))).graphValue :=
  (injOn_empty Prod.fst).measurable_graphValue MeasurableSet.empty

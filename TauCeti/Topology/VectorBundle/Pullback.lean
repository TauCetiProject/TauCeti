/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Topological module structures on pullback fibres

The fibres of a native bundle pullback inherit additive groups, continuous addition and
continuous scalar multiplication from the original fibres. These instances complement
Mathlib's inherited additive-monoid, module and fibre-topology instances, allowing bundle
constructions on pullbacks to use the same topological-module API as the original bundle.
-/

public section

namespace Bundle.Pullback

variable {B B' : Type*} (E : B → Type*) (f : B' → B)

/-- Pullback fibres inherit the additive groups of the original fibres. -/
instance addCommGroup [∀ x, AddCommGroup (E x)] (x : B') : AddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (AddCommGroup (E (f x)))

/-- Addition and negation on a pullback fibre are continuous. -/
instance isTopologicalAddGroup [∀ x, AddCommGroup (E x)] [∀ x, TopologicalSpace (E x)]
    [∀ x, IsTopologicalAddGroup (E x)] (x : B') : IsTopologicalAddGroup ((f *ᵖ E) x) :=
  inferInstanceAs (IsTopologicalAddGroup (E (f x)))

/-- Scalar multiplication on a pullback fibre is continuous. -/
instance continuousSMul (R : Type*) [Semiring R] [TopologicalSpace R] [∀ x, AddCommMonoid (E x)]
    [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)] [∀ x, ContinuousSMul R (E x)]
    (x : B') : ContinuousSMul R ((f *ᵖ E) x) :=
  inferInstanceAs (ContinuousSMul R (E (f x)))

end Bundle.Pullback

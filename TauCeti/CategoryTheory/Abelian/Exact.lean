/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Right exact functors preserving monomorphisms are exact

A functor between abelian categories which preserves finite colimits preserves cokernels and
binary biproducts, hence is additive. Such a functor preserves homology as soon as it preserves
monomorphisms (Mathlib's `Functor.preservesHomology_of_preservesMonos_and_cokernels`), hence
preserves finite limits.

For example, tensoring with a fixed object `M` in a closed abelian monoidal category is a left
adjoint, so `M` is flat, in the sense that `M ⊗ -` is exact, as soon as `M ⊗ -` preserves
monomorphisms. This applies to categories such as sheaves of modules, whose tensor product is
right exact but not exact in general.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- A functor between abelian categories which preserves finite colimits and monomorphisms
preserves finite limits: being right exact, preserving monomorphisms makes it exact. -/
lemma preservesFiniteLimits_of_preservesMonomorphisms {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [PreservesFiniteColimits F] [F.PreservesMonomorphisms] :
    PreservesFiniteLimits F := by
  -- Preserving binary coproducts, `F` preserves binary biproducts, so it is additive.
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have := F.additive_of_preservesBinaryBiproducts
  have := F.preservesHomology_of_preservesMonos_and_cokernels
  exact F.preservesFiniteLimits_of_preservesHomology

end CategoryTheory.Functor

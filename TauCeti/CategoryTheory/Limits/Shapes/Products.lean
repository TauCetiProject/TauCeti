/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Reindexing a coproduct along an injection is split

Let `X : I → C` be a family of objects of a category with zero morphisms and coproducts, and let
`f : J → I` be injective.  Reindexing along `f` gives a map `∐ (X ∘ f) ⟶ ∐ X`, and this file
shows that it is a split monomorphism: the retraction sends the summand indexed by `f j` back to
the one indexed by `j`, and kills the summands indexed outside the range of `f`.

Mathlib's `CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective` proves the same map is a
monomorphism in a category satisfying `MonoCoprod`; the splitting below needs zero morphisms
instead, and is the stronger statement in the situations where both apply.

Chain complexes built as coproducts over a set of simplices, singular or simplicial, get their
degreewise splittings this way: for a pair of spaces the singular simplices of the subspace form a
subset of those of the ambient space, so the short exact sequence of chains of the pair is split in
each degree, and therefore stays exact after applying a contravariant `Hom(-, M)`.
-/

public section

open CategoryTheory Limits

universe w

namespace TauCeti

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCoproducts.{w} C]

open scoped Classical in
/-- Reindexing a coproduct along an injective map of index types is a split monomorphism. -/
instance isSplitMono_sigmaMap' {I J : Type w} (X : I → C) (f : J ⟶ I) [Mono f] :
    IsSplitMono (Sigma.map' f fun j ↦ 𝟙 ((X ∘ f) j)) :=
  IsSplitMono.mk'
    { retraction := Sigma.desc fun i ↦
        if h : i ∈ Set.range f then
          eqToHom (congrArg X h.choose_spec).symm ≫ Sigma.ι (X ∘ f) h.choose
        else 0
      id := by
        refine Sigma.hom_ext _ _ fun j ↦ ?_
        have h : f j ∈ Set.range f := ⟨j, rfl⟩
        have hj : h.choose = j := (mono_iff_injective f).1 ‹_› h.choose_spec
        rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_comp_desc,
          dite_eq_left h, Category.comp_id]
        exact Sigma.eqToHom_comp_ι (X ∘ f) hj }

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Free objects on an injection are split

For an object `R` of a category with zero morphisms and coproducts, the functor
`sigmaConst.obj R : Type w ⥤ C` sends a type `α` to the coproduct `∐ (_ : α), R` of copies of `R`.
This file shows that it sends an injective map `f : α ⟶ β` to a split monomorphism: the retraction
sends the summand indexed by `f a` back to the summand indexed by `a`, and kills the summands
indexed by elements outside the range of `f`.

This is what makes the short exact sequence of chains of a pair of simplicial sets split in each
degree, so that it stays exact after applying the contravariant functor `Hom(-, M)`.
-/

public section

open CategoryTheory Limits

universe w

namespace TauCeti

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCoproducts.{w} C] (R : C)

open scoped Classical in
/-- The map of coproducts of copies of `R` induced by an injective map of index types is a split
monomorphism. -/
instance isSplitMono_sigmaConst_obj_map {α β : Type w} (f : α ⟶ β) [Mono f] :
    IsSplitMono ((sigmaConst.obj R).map f) :=
  IsSplitMono.mk'
    { retraction := Sigma.desc fun b ↦
        if h : b ∈ Set.range f then Sigma.ι (fun _ ↦ R) h.choose else 0
      id := by
        refine Sigma.hom_ext _ _ fun a ↦ ?_
        have h : f a ∈ Set.range f := ⟨a, rfl⟩
        have ha : h.choose = a := (mono_iff_injective f).1 ‹_› h.choose_spec
        simp [ha] }

end TauCeti

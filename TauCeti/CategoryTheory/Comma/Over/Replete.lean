/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Limits.Replete
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Repleteness of slice categories

Every slice of a replete category with binary products is replete. In particular, the
inverse-sequence epimorphism condition defining a replete topos holds on every slice,
as needed when applying inverse-limit results locally.

The forgetful functor from the slice preserves connected limits and reflects
epimorphisms. Binary products give it a right adjoint, so it also preserves
epimorphisms. No existence assumption on sequential limits is needed: repleteness
is tested on each limit cone that exists.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Lemma 3.1.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] [IsReplete C]

/-- Every slice of a replete category with binary products is replete. This applies,
in particular, to slices of replete topoi. -/
instance isReplete_over (X : C) : IsReplete (Over X) :=
  have : IsConnected ℕᵒᵖ := IsCofiltered.isConnected ℕᵒᵖ
  IsReplete.of_reflectsEpimorphisms (Over.forget X)

end TauCeti

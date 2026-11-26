/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Projective.Internal

/-!
# Exactness of internal Hom out of an internally projective object

In an abelian closed monoidal category, internal Hom out of an internally projective object
preserves epimorphisms by definition and, as a right adjoint, preserves kernels, so it is exact:
it preserves homology.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace CategoryTheory.InternallyProjective

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalClosed C]

/-- Internal Hom out of an internally projective object of an abelian closed monoidal category
is exact. -/
instance preservesHomology (P : C) [InternallyProjective P] : (ihom P).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end CategoryTheory.InternallyProjective

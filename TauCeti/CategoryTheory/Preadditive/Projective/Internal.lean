/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Internal

import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exactness of internal Hom out of an internally projective object

In an abelian closed monoidal category, internal Hom out of an internally projective object
preserves homology: it is a right adjoint, so it preserves kernels, and it preserves
epimorphisms by internal projectivity.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalClosed C]

/-- Internal Hom out of an internally projective object of an abelian closed monoidal category
preserves homology. -/
instance InternallyProjective.preservesHomology_ihom (P : C) [InternallyProjective P] :
    (ihom P).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

end CategoryTheory

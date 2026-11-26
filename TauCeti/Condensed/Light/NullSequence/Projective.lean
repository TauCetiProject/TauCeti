/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.Condensed.Light.NullSequence.Basic
public import TauCeti.Condensed.Light.Sequence

import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Internal projectivity of the null-sequence module

Over a commutative ring in any site universe, internal Hom out of the null-sequence module
preserves epimorphisms. The marked-point splitting exhibits the reduced module as a retract
of the internally projective free module on the convergent sequence. Being also a right adjoint,
internal Hom out of the null-sequence module is therefore exact.

See Rodríguez Camargo, *Notes on Solid Geometry*, Theorem 2.3.3(3) and Definition 3.2.1.
-/

public section

universe u

open CategoryTheory LightCondensed

namespace TauCeti

variable (R : Type u) [CommRing R]

/-- Internal Hom out of the null-sequence module preserves epimorphisms. -/
theorem internallyProjective_nullSeq : InternallyProjective (nullSeq R) := by
  have : InternallyProjective
      ((lightProfiniteToLightCondSet ⋙ free R).obj (Under.mk inftyPoint.{u}).right) :=
    internallyProjective_free_liftedSequence R
  exact InternallyProjective.ofRetract (reducedLightFreeRetract R (Under.mk inftyPoint))

/-- Internal Hom out of the null-sequence module preserves homology: it is a right adjoint, so it
preserves kernels, and it preserves epimorphisms by internal projectivity. -/
instance preservesHomology_ihom_nullSeq : (ihom (nullSeq R)).PreservesHomology := by
  have := internallyProjective_nullSeq R
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

end TauCeti

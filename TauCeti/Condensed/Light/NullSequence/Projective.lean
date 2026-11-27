/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.NullSequence.Basic
public import TauCeti.Condensed.Light.Sequence

/-!
# Internal projectivity of the null-sequence module

Over a commutative ring in any site universe, internal Hom out of the null-sequence module
preserves epimorphisms. The marked-point splitting exhibits the reduced module as a retract
of the internally projective free module on the convergent sequence.

See Rodríguez Camargo, *Notes on Solid Geometry*, Theorem 2.3.3(3) and Definition 3.2.1.
-/

public section

universe u

open CategoryTheory LightCondensed

namespace TauCeti

variable (R : Type u) [CommRing R]

/-- Internal Hom out of the null-sequence module preserves epimorphisms. -/
instance internallyProjective_nullSeq : InternallyProjective (nullSeq R) := by
  have : InternallyProjective
      ((lightProfiniteToLightCondSet ⋙ free R).obj (Under.mk inftyPoint.{u}).right) :=
    internallyProjective_free_liftedSequence R
  exact InternallyProjective.ofRetract (reducedLightFreeRetract R (Under.mk inftyPoint))

end TauCeti

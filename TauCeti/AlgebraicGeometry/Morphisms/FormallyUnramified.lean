/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Source locality of formally unramified morphisms

Expose Zariski locality on the source for formally unramified morphisms, using Mathlib's
ring-homomorphism property interface. This permits formal unramifiedness to be restricted
along open immersions and checked on open covers independently of nodal-curve theory.
-/

public section

open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Formal unramifiedness is Zariski local on the source. -/
instance FormallyUnramified.isZariskiLocalAtSource :
    IsZariskiLocalAtSource @_root_.AlgebraicGeometry.FormallyUnramified.{u} :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @_root_.AlgebraicGeometry.FormallyUnramified.{u}) (Q := RingHom.FormallyUnramified)

end TauCeti.AlgebraicGeometry

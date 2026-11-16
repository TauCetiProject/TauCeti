/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import Mathlib.RingTheory.Smooth.Basic

/-!
# Smoothness of the identity component

The identity component of a smooth affine group of finite type over an algebraically closed
field is smooth. Its coordinate algebra is the localization at the idempotent selecting the
identity component. This supplies smooth connected subgroups to which radical and
semisimplicity criteria apply.
-/

public section

namespace TauCeti.FiniteTypeCommHopfAlgCat

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The identity component of a smooth finite-type affine group is smooth. -/
instance smooth_identityComponent (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Algebra.Smooth k H] : Algebra.Smooth k (identityComponent H) := by
  have := isLocalization_away_identityComponent H
  let _ : Algebra.Smooth H (identityComponent H) := Algebra.Smooth.of_isLocalization_Away
    (PrimeSpectrum.connectedComponentIdempotent (R := H) (Bialgebra.augmentationPoint k H))
  exact Algebra.Smooth.comp k H (identityComponent H)

end TauCeti.FiniteTypeCommHopfAlgCat

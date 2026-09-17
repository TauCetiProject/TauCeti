/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
import Mathlib.RingTheory.Localization.Away.Lemmas
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
  let e : H := PrimeSpectrum.connectedComponentIdempotent (R := H)
    (Bialgebra.augmentationPoint k H)
  -- The ideal's definition is not exposed across modules, so use its public membership lemma.
  have hI : PrimeSpectrum.connectedComponentIdeal (R := H) (Bialgebra.augmentationPoint k H) =
      Ideal.span {1 - e} := by
    ext x
    exact (PrimeSpectrum.mem_connectedComponentIdeal_iff
      (x := Bialgebra.augmentationPoint k H) (r := x)).trans Ideal.mem_span_singleton'.symm
  let _ : IsLocalization.Away e (identityComponent H) := by
    -- Direct application through the bundled identity component exceeds the heartbeat limit.
    -- Expose the quotient carrier so the underlying Hopf ideal can be rewritten explicitly.
    change IsLocalization.Away e
      (H ⧸ (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := H)).toIdeal)
    rw [HopfAlgebra.identityComponentHopfIdeal_toIdeal, hI]
    exact IsLocalization.Away.quotient_of_isIdempotentElem
      (PrimeSpectrum.isIdempotentElem_connectedComponentIdempotent (R := H) _)
  let _ : Algebra.Smooth H (identityComponent H) :=
    Algebra.Smooth.of_isLocalization_Away e
  exact Algebra.Smooth.comp k H (identityComponent H)

end TauCeti.FiniteTypeCommHopfAlgCat

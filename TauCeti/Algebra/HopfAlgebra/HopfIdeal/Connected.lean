/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Augmentation
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Hopf ideals of Hopf algebras with connected spectrum

A finitely generated Hopf ideal of a Hopf algebra with connected spectrum is zero as soon as it
is idempotent.

* `TauCeti.HopfIdeal.eq_bot_of_isIdempotentElem`: a finitely generated idempotent Hopf ideal of a
  Hopf algebra with connected spectrum is zero. The generator of such an ideal is an idempotent
  element of the ring, hence `0` or `1`; the value `1` is excluded because every Hopf ideal lies in
  the augmentation ideal.
-/

public section

namespace TauCeti.HopfIdeal

variable {k H : Type*} [CommRing k] [Nontrivial k] [CommRing H] [HopfAlgebra k H]

/-- A finitely generated idempotent Hopf ideal of a Hopf algebra with connected spectrum is zero. -/
theorem eq_bot_of_isIdempotentElem [ConnectedSpace (PrimeSpectrum H)] (I : HopfIdeal k H)
    (hfg : I.toIdeal.FG) (hI : IsIdempotentElem I.toIdeal) :
    I = ⊥ := by
  have hI_aug : I.toIdeal ≤ RingHom.ker (Bialgebra.counitAlgHom k H) :=
    (toIdeal_le_toIdeal.mpr (HopfIdeal.le_augmentation k H I)).trans_eq
      (augmentation_toIdeal k H)
  have hne : I.toIdeal ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI_aug
  have h := Ideal.eq_bot_of_isIdempotentElem_of_ne_top hfg hI hne
  apply HopfIdeal.ext
  intro x
  rw [← mem_toIdeal, ← mem_toIdeal, bot_toIdeal, h]

end TauCeti.HopfIdeal

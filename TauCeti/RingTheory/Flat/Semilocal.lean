/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology

import Mathlib.RingTheory.LocalRing.Module
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Flat modules over commutative semilocal rings

Over a commutative semilocal ring (`Finite (MaximalSpectrum R)`) whose prime spectrum is
preconnected, every finitely presented flat module has constant stalk rank and is therefore free.

## Main results

* `TauCeti.free_of_finite_maximalSpectrum_of_preconnectedSpace`: a finitely presented flat module
  over a commutative semilocal ring with preconnected prime spectrum is free.
-/

public section

namespace TauCeti

/-- Over a commutative semilocal ring with preconnected prime spectrum (for instance a local ring
or a connected semilocal domain), every finitely presented flat module is free. -/
theorem free_of_finite_maximalSpectrum_of_preconnectedSpace
    {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [PreconnectedSpace (PrimeSpectrum R)]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Free R M := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    exact Module.Free.of_subsingleton R M
  · obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    refine Module.free_of_flat_of_finrank_eq R M (Module.rankAtStalk M p₀) fun P ↦ ?_
    rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk]
    exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).apply_eq_of_preconnectedSpace
      P.toPrimeSpectrum p₀

end TauCeti

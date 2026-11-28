/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import TauCeti.LinearAlgebra.QuadraticForm.ExtendScalars

/-!
# Nondegeneracy of quadratic forms on fibres

After scalar extension, a quadratic form on the fibre at a prime is nondegenerate
exactly when the original form on the fibre at its contraction is nondegenerate.
-/

public section

namespace QuadraticForm

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- After an arbitrary base change, the fibre at a prime is nondegenerate exactly
when the original fibre at the contracted prime is nondegenerate. -/
theorem nondegenerate_extendScalars_residueField_iff_comap (Q : QuadraticForm R (ι → R))
    (S : Type*) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) :
    ((Q.extendScalars S).extendScalars q.asIdeal.ResidueField).Nondegenerate ↔
      (Q.extendScalars (q.comap (algebraMap R S)).asIdeal.ResidueField).Nondegenerate := by
  let p := q.comap (algebraMap R S)
  let := Localization.AtPrime.algebraOfLiesOver p.asIdeal q.asIdeal
  simpa only [extendScalars_extendScalars] using
    (Q.extendScalars p.asIdeal.ResidueField).nondegenerate_extendScalars_iff q.asIdeal.ResidueField

end QuadraticForm

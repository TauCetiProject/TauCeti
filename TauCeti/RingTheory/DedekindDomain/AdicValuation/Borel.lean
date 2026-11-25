/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# The Borel structure on an adic completion

Let `R` be a Dedekind domain with fraction field `K` and `v` a height-one prime of `R`. This file
gives the completion `K_v` its Borel σ-algebra, on which its additive Haar measures live.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.instMeasurableSpaceAdicCompletion`,
  `IsDedekindDomain.HeightOneSpectrum.instBorelSpaceAdicCompletion`: the Borel structure on `K_v`.
-/

public section

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The Borel σ-algebra on the completion `K_v`. -/
instance instMeasurableSpaceAdicCompletion : MeasurableSpace (v.adicCompletion K) := borel _

instance instBorelSpaceAdicCompletion : BorelSpace (v.adicCompletion K) := ⟨rfl⟩

end IsDedekindDomain.HeightOneSpectrum

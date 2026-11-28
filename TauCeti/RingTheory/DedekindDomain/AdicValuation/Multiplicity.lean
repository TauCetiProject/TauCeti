/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
import TauCeti.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Multiplicities of ideals in a completed integer ring

Extending an ideal of a Dedekind domain to the integer ring of its completion preserves its
multiplicity at the selected prime. The prime generates the maximal ideal of the completion,
so its ramification index in this extension is one. This comparison lets coefficients of
global ideals be read in the completed ring.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The coefficient at `v` of a nonzero ideal equals the coefficient at the maximal ideal after
extension to the integer ring of the `v`-adic completion. -/
@[simp]
theorem multiplicity_map_adicCompletionIntegers (v : HeightOneSpectrum R)
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
        (I.map (algebraMap R (v.adicCompletionIntegers K))) =
      multiplicity v.asIdeal I :=
  Ideal.multiplicity_map_of_map_eq
    (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K))
    (v.map_asIdeal_adicCompletionIntegers (K := K)) hI

end IsDedekindDomain.HeightOneSpectrum

end

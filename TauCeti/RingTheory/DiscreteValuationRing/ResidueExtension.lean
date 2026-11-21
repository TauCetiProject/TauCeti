/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.LocalRing.ResidueField.Completion
public import TauCeti.RingTheory.RegularLocalRing.ResidueExtension
import TauCeti.RingTheory.DiscreteValuationRing.Etale

/-!
# Discrete valuation ring extensions with prescribed residue field extension

When `R` is a discrete valuation ring and `L` is any field extension of `ResidueField R`, the
completed residue-field extension `TauCeti.IsLocalRing.CompletedResidueExtension R L` (constructed
in `TauCeti/RingTheory/LocalRing/ResidueField/Completion.lean` and shown to be a regular local
domain in `TauCeti/RingTheory/RegularLocalRing/ResidueExtension.lean`) is a discrete valuation ring
in which every uniformizer of `R` remains a uniformizer, and is complete with respect to its maximal
ideal via `CompletedResidueExtension.instIsAdicComplete`. Taking
`L = AlgebraicClosure (ResidueField R)` enlarges the residue field of any discrete valuation ring to
an algebraically closed field without ramifying the base.

## Main results

* `TauCeti.IsLocalRing.CompletedResidueExtension.instIsDiscreteValuationRing`: over a discrete
  valuation ring `R`, `CompletedResidueExtension R L` is a discrete valuation ring (complete via
  `CompletedResidueExtension.instIsAdicComplete`).
* `TauCeti.IsLocalRing.CompletedResidueExtension.irreducible_algebraMap`: every uniformizer of `R`
  remains a uniformizer in `CompletedResidueExtension R L`.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique III*, Chapitre 0,
  Proposition 10.3.1.
* J.-P. Serre, *Local Fields*, Chapter III, §5 (the case of separable algebraic residue-field
  extensions of complete discrete valuation rings).
-/

public section

universe u v

open IsLocalRing

namespace TauCeti.IsLocalRing.CompletedResidueExtension

/-- When `R` is a discrete valuation ring, `CompletedResidueExtension R L` is a discrete valuation
ring (and adically complete with respect to its maximal ideal via `instIsAdicComplete`). -/
instance instIsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (L : Type v) [Field L] [Algebra (ResidueField R) L] :
    IsDiscreteValuationRing (CompletedResidueExtension R L) :=
  IsDiscreteValuationRing.of_flat_of_map_maximalIdeal_eq (maximalIdeal_eq_map R L).symm

/-- Every uniformizer of a discrete valuation ring `R` remains a uniformizer in
`CompletedResidueExtension R L`. -/
theorem irreducible_algebraMap {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] {π : R} (hπ : Irreducible π) :
    Irreducible (algebraMap R (CompletedResidueExtension R L) π) :=
  IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal_eq
    (maximalIdeal_eq_map R L).symm hπ

end TauCeti.IsLocalRing.CompletedResidueExtension

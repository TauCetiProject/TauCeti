/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Local compactness and second countability of finite adele rings

The finite adele ring of a Dedekind domain with finite residue fields is locally compact.  Each
adic completion is a nonarchimedean local field, and its integer ring is compact and open.  The
result then follows from the local-compactness theorem for restricted products.  If the Dedekind
domain moreover has countably many places, for example if it is countable
(`IsDedekindDomain.HeightOneSpectrum.countable`), the finite adele ring is second countable, since
each completion is a second-countable local field; Mathlib then makes it σ-compact.

The finite-residue-field hypothesis is stated directly, rather than specialized to rings of
integers, so this applies to every Dedekind domain for which the same local compactness argument is
valid.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.instLocallyCompactSpace`: the finite adele ring is locally
  compact when all residue fields are finite.
* `IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`: the finite adele ring is second
  countable when moreover the Dedekind domain has countably many places.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §14.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63, pp. 188–189.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adele ring of a Dedekind domain with finite residue fields is locally compact. -/
instance instLocallyCompactSpace [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    LocallyCompactSpace (FiniteAdeleRing R K) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs <| LocallyCompactSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

/-- The finite adele ring of a Dedekind domain with countably many places and finite residue
fields is second countable. -/
instance instSecondCountableTopology [Countable (HeightOneSpectrum R)]
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    SecondCountableTopology (FiniteAdeleRing R K) :=
  RestrictedProduct.secondCountableTopology_of_cofinite
    (.of_forall fun _ ↦ Valued.isOpen_valuationSubring _)

end IsDedekindDomain.FiniteAdeleRing

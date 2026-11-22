/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
public import TauCeti.RingTheory.Noetherian.Countable
public import TauCeti.Topology.MetricSpace.Polish.LocallyCompact
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Second countability and the Borel structure of finite adele rings

Let `R` be a Dedekind domain with countably many places and finite residue fields, and let `K` be
its fraction field; for example `R` may be any countable such domain
(`IsDedekindDomain.HeightOneSpectrum.countable`), such as the ring of integers of a number field.
Its finite adele ring `FiniteAdeleRing R K = Πʳ v, [K_v, 𝒪_v]` is second countable: each
completion `K_v` is a second-countable nonarchimedean local field and each `𝒪_v` is open, so the
second countability of restricted products over a countable index type applies. Being moreover
locally compact and Hausdorff, the finite adele ring is Polish.

The finite adele ring carries the Borel σ-algebra of its restricted-product topology. It is the
σ-algebra `RestrictedProduct.measurableSpace` of the underlying restricted product, so the
restricted products of local Haar measures (`TauCeti.restrictedAddHaar`) are measures on the
finite adele ring.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`: the finite adele ring is second
  countable.
* `IsDedekindDomain.FiniteAdeleRing.instPolishSpace`: the finite adele ring is Polish.
* `IsDedekindDomain.FiniteAdeleRing.instMeasurableSpace`,
  `IsDedekindDomain.FiniteAdeleRing.instBorelSpace`: its Borel σ-algebra.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63, pp. 188–189.
-/

public section
noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite adele ring carries the Borel σ-algebra of its restricted-product topology. -/
instance instMeasurableSpace : MeasurableSpace (FiniteAdeleRing R K) :=
  inferInstanceAs <| MeasurableSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

/-- The finite adele ring is a Borel space. -/
instance instBorelSpace : BorelSpace (FiniteAdeleRing R K) :=
  inferInstanceAs <| BorelSpace <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

variable [Countable (HeightOneSpectrum R)] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The finite adele ring of a Dedekind domain with countably many places and finite residue
fields is second countable. -/
instance instSecondCountableTopology : SecondCountableTopology (FiniteAdeleRing R K) := by
  let _ (v : HeightOneSpectrum R) : IsNonarchimedeanLocalField (v.adicCompletion K) :=
    inferInstance
  let _ : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact inferInstanceAs <| SecondCountableTopology <|
    RestrictedProduct (fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
      (fun v ↦ v.adicCompletionIntegers K) Filter.cofinite

/-- The finite adele ring of a Dedekind domain with countably many places and finite residue
fields is Polish, being a second-countable locally compact Hausdorff space. -/
instance instPolishSpace : PolishSpace (FiniteAdeleRing R K) :=
  TauCeti.polishSpace_of_weaklyLocallyCompactSpace _

end IsDedekindDomain.FiniteAdeleRing

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Borel
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocallyCompact
public import TauCeti.RingTheory.DedekindDomain.Ideal.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.SecondCountable

/-!
# Second countability and Borel structures on finite adele rings

Let `R` be a Dedekind domain with fraction field `K`. This file registers the Borel σ-algebra on
the finite adele ring `FiniteAdeleRing R K`, on which its Haar measures live, and defines the Borel
σ-algebras of the native units topologies on its unit group (the finite ideles) and on
`GL_n(FiniteAdeleRing R K) = (Matrix n n (FiniteAdeleRing R K))ˣ`, where the Haar measures of
finite ideles live. These two are definitions, not instances: Mathlib's `Units.instMeasurableSpace`
already gives a unit group the pullback σ-algebra along `Units.val`, which differs from the Borel
σ-algebra because the units topology is not the subspace topology. The completions `K_v` get their
Borel σ-algebras in `TauCeti.RingTheory.DedekindDomain.AdicValuation.Borel`.

If `R` is countable and all its residue fields are finite, the finite adele ring is second
countable: it is the restricted product over the countably many height-one primes of `R`
(`IsDedekindDomain.HeightOneSpectrum.instCountable`) of the completions `K_v`, which are
nonarchimedean local fields and hence second countable, with respect to the open integer rings
`𝒪_v`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`: second countability of the
  finite adele ring of a countable Dedekind domain with finite residue fields.
* `IsDedekindDomain.FiniteAdeleRing.instBorelSpace`: the Borel structure on the finite adeles.
* `IsDedekindDomain.FiniteAdeleRing.measurableSpaceUnits`,
  `IsDedekindDomain.FiniteAdeleRing.measurableSpaceMatrixUnits`: the Borel σ-algebras on the
  finite ideles and on `GL_n` of the finite adeles.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., Lemma 3.63, pp. 188–189 (the countable restricted-product topology).
-/

public section

noncomputable section

open IsDedekindDomain MeasureTheory TopologicalSpace

namespace IsDedekindDomain.FiniteAdeleRing

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The finite adele ring of a countable Dedekind domain with finite residue fields is second
countable. -/
instance instSecondCountableTopology [Countable R]
    [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)] :
    SecondCountableTopology (FiniteAdeleRing R K) :=
  RestrictedProduct.instSecondCountableTopology
    (R := fun v : HeightOneSpectrum R ↦ v.adicCompletion K)
    (A := fun v ↦ (v.adicCompletionIntegers K : Set (v.adicCompletion K)))

/-- The Borel σ-algebra on the finite adele ring. It is the Borel σ-algebra of the underlying
restricted product (`RestrictedProduct.measurableSpace`). -/
instance instMeasurableSpace : MeasurableSpace (FiniteAdeleRing R K) := borel _

instance instBorelSpace : BorelSpace (FiniteAdeleRing R K) := ⟨rfl⟩

/-- The Borel σ-algebra on the finite ideles, for their native units topology. It is not an
instance: Mathlib's `Units.instMeasurableSpace` already gives the units of a measurable monoid the
pullback σ-algebra along `Units.val`, and the units topology is not the subspace topology. -/
@[instance_reducible]
def measurableSpaceUnits : MeasurableSpace (FiniteAdeleRing R K)ˣ := borel _

/-- `measurableSpaceUnits R K` is the Borel σ-algebra of the finite ideles. -/
theorem borelSpaceUnits :
    @BorelSpace (FiniteAdeleRing R K)ˣ _ (measurableSpaceUnits R K) :=
  @BorelSpace.mk _ _ (measurableSpaceUnits R K) rfl

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Borel σ-algebra on `GL_n` of the finite adeles, for the native topology of the units of the
matrix ring. Like `measurableSpaceUnits`, it is not an instance. -/
@[instance_reducible]
def measurableSpaceMatrixUnits : MeasurableSpace (Matrix n n (FiniteAdeleRing R K))ˣ :=
  borel _

/-- `measurableSpaceMatrixUnits R K n` is the Borel σ-algebra of `GL_n` of the finite adeles. -/
theorem borelSpaceMatrixUnits :
    @BorelSpace (Matrix n n (FiniteAdeleRing R K))ˣ _ (measurableSpaceMatrixUnits R K n) :=
  @BorelSpace.mk _ _ (measurableSpaceMatrixUnits R K n) rfl

end IsDedekindDomain.FiniteAdeleRing

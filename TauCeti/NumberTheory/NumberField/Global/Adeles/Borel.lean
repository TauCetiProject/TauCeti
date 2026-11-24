/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Borel
public import TauCeti.Topology.Algebra.Group.Units
public import TauCeti.Topology.Instances.Matrix

/-!
# Second countability and Borel structures on adeles and ideles

For a number field `K`, the finite adele ring `𝔸_{K,f}`, the infinite adele ring `K_∞`, the adele
ring `𝔸_K = K_∞ × 𝔸_{K,f}`, their unit groups (the finite ideles and the ideles) and `GL_n` over
each of them are second countable. This file registers the instances specific to number fields
and the Borel structures on which the Haar measures of adeles and ideles live.

* The ring of integers `𝓞 K` is countable, so it has countably many height-one primes
  (`IsDedekindDomain.HeightOneSpectrum.instCountable`). Together with the finiteness of
  its residue fields this makes `𝔸_{K,f}` second countable
  (`IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`).
* `K_∞` is homeomorphic to the Minkowski space `ℝ^{r₁} × ℂ^{r₂}`
  (`NumberField.InfiniteAdeleRing.instSecondCountableTopology`), so `𝔸_K` is second countable.
* The unit groups, and the groups `GL_n = (Matrix n n _)ˣ` of the matrix rings (second countable
  as finite products of copies of the ring, `TauCeti.Topology.Instances.Matrix`), are second
  countable by `Units.instSecondCountableTopology`, which uses the embedding `u ↦ (u, u⁻¹)` and so
  covers the adelic rings, whose unit groups do not carry the subspace topology.

The infinite adeles, their units, the ideles and `GL_n` of the infinite adeles and of the adeles
carry their Borel σ-algebras, those of the unit groups for their native units topologies (the
local completions `K_v` get theirs in `TauCeti.RingTheory.DedekindDomain.AdicValuation.Borel`,
and the finite adeles, the finite ideles and `GL_n` of the finite adeles in
`TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Borel`); the adele ring carries the product
σ-algebra of `K_∞ × 𝔸_{K,f}`, which is its Borel σ-algebra by second countability
(`NumberField.AdeleRing.instBorelSpace`).

## Main results

* `NumberField.instCountableRingOfIntegers`: the ring of integers of a number field is
  countable, so it has countably many finite places.
* `NumberField.AdeleRing.instSecondCountableTopology`.
* `NumberField.InfiniteAdeleRing.instBorelSpace`, `NumberField.AdeleRing.instBorelSpace`,
  `NumberField.InfiniteAdeleRing.instBorelSpaceUnits`, `NumberField.IdeleGroup.instBorelSpace`.
* `NumberField.InfiniteAdeleRing.instBorelSpaceMatrixUnits`,
  `NumberField.AdeleRing.instBorelSpaceMatrixUnits`: the Borel structures on `GL_n`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. I,
  2nd ed., Lemma 3.63, pp. 188–189 (the countable restricted-product topology).
-/

public section

noncomputable section

open IsDedekindDomain MeasureTheory NumberField TopologicalSpace

/-! ### Second countability -/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The ring of integers of a number field is countable, being a finitely generated
`ℤ`-module. -/
instance instCountableRingOfIntegers : Countable (𝓞 K) :=
  Countable.of_moduleFinite (R := ℤ)

/-- The adele ring of a number field is second countable. -/
instance AdeleRing.instSecondCountableTopology :
    SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end NumberField

/-! ### Borel structures -/

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The Borel σ-algebra on the infinite adele ring. -/
instance InfiniteAdeleRing.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing K) := borel _

instance InfiniteAdeleRing.instBorelSpace : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩

/-- The adele ring `K_∞ × 𝔸_{K,f}` carries the product σ-algebra. -/
instance AdeleRing.instMeasurableSpace : MeasurableSpace (AdeleRing R K) :=
  inferInstanceAs <| MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

/-- The Borel σ-algebra on the idele group. -/
instance IdeleGroup.instMeasurableSpace : MeasurableSpace (IdeleGroup R K) := borel _

instance IdeleGroup.instBorelSpace : BorelSpace (IdeleGroup R K) := ⟨rfl⟩

/-- The product σ-algebra on the adele ring of a number field is its Borel σ-algebra. -/
instance AdeleRing.instBorelSpace [NumberField K] : BorelSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

/-- The Borel σ-algebra on the units of the infinite adele ring, for their native topology. -/
instance InfiniteAdeleRing.instMeasurableSpaceUnits : MeasurableSpace (InfiniteAdeleRing K)ˣ :=
  borel _

instance InfiniteAdeleRing.instBorelSpaceUnits : BorelSpace (InfiniteAdeleRing K)ˣ := ⟨rfl⟩

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The Borel σ-algebra on `GL_n` of the infinite adeles, for the native topology of the units of
the matrix ring. -/
instance InfiniteAdeleRing.instMeasurableSpaceMatrixUnits :
    MeasurableSpace (Matrix n n (InfiniteAdeleRing K))ˣ :=
  borel _

instance InfiniteAdeleRing.instBorelSpaceMatrixUnits :
    BorelSpace (Matrix n n (InfiniteAdeleRing K))ˣ :=
  ⟨rfl⟩

/-- The Borel σ-algebra on `GL_n` of the adeles, for the native topology of the units of the
matrix ring. -/
instance AdeleRing.instMeasurableSpaceMatrixUnits : MeasurableSpace (Matrix n n (AdeleRing R K))ˣ :=
  borel _

instance AdeleRing.instBorelSpaceMatrixUnits : BorelSpace (Matrix n n (AdeleRing R K))ˣ := ⟨rfl⟩

end NumberField

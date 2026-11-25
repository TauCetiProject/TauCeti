/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.MeasureTheory.Constructions.Polish.Units
public import TauCeti.NumberTheory.NumberField.Countable
public import TauCeti.NumberTheory.NumberField.Global.Adeles.LocallyCompact
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.BorelSpace
public import TauCeti.Topology.MetricSpace.Polish.Matrix

/-!
# Second countability and the Borel structure of adele rings

Let `K` be a number field. Its infinite adele ring `K_∞ = ∏_{w | ∞} K_w` is homeomorphic to the
finite-dimensional real mixed space, so it is second countable, and being locally compact and
Hausdorff it is Polish. It carries its Borel σ-algebra.

Let `R` be a Dedekind domain with fraction field `K`, countably many places and finite residue
fields, such as the ring of integers of `K` (`NumberField.RingOfIntegers.instCountable`). The
adele ring `AdeleRing R K = K_∞ × 𝔸_{K,f}` carries the product of the Borel σ-algebras of its two
factors, which by second countability is its own Borel σ-algebra, and it is second countable and
Polish.

For the unit groups the coordinate σ-algebra `Units.instMeasurableSpace` is the Borel σ-algebra of
the native topology of the units, induced by `u ↦ (u, u⁻¹)`, even though for the ideles this
topology is strictly finer than the subspace topology of the adeles (`Units.borelSpace`). With
`Units.instPolishSpace`, `Units.instSecondCountableTopology` and Mathlib's Borel structure on
matrices, every instance below therefore extends without further hypotheses to the ideles
`IdeleGroup R K = (AdeleRing R K)ˣ`, the finite and infinite ideles, and the general linear
groups `GL n` over each of the three adele rings for every finite `n`.

## Main results

* `NumberField.InfiniteAdeleRing.instPolishSpace`, `NumberField.InfiniteAdeleRing.instBorelSpace`:
  the infinite adele ring is a Polish Borel space. Its second countability is
  `NumberField.InfiniteAdeleRing.instSecondCountableTopology`.
* `NumberField.AdeleRing.instPolishSpace`, `NumberField.AdeleRing.instBorelSpace`: so is the
  adele ring, with the product σ-algebra. Its second countability is
  `NumberField.AdeleRing.instSecondCountableTopology`.

## References

* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), Lemma 3.63, pp. 188–189.
-/

public section
noncomputable section

open IsDedekindDomain

namespace NumberField

section Infinite

variable (K : Type*) [Field K]

/-- The infinite adele ring carries its Borel σ-algebra. -/
instance InfiniteAdeleRing.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing K) :=
  borel _

/-- The infinite adele ring is a Borel space. -/
instance InfiniteAdeleRing.instBorelSpace : BorelSpace (InfiniteAdeleRing K) :=
  ⟨rfl⟩

variable [NumberField K]

/-- The infinite adele ring of a number field is Polish. -/
instance InfiniteAdeleRing.instPolishSpace : PolishSpace (InfiniteAdeleRing K) :=
  TauCeti.polishSpace_of_weaklyLocallyCompactSpace _

end Infinite

variable (R : Type*) [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The adele ring carries the product of the Borel σ-algebras of its infinite and finite parts. -/
instance AdeleRing.instMeasurableSpace : MeasurableSpace (AdeleRing R K) :=
  inferInstanceAs <| MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

variable [Countable (HeightOneSpectrum R)] [∀ v : HeightOneSpectrum R, Finite (R ⧸ v.asIdeal)]

/-- The adele ring is a Borel space: since the finite adele ring is second countable, the product
σ-algebra is the Borel σ-algebra of the product topology. -/
instance AdeleRing.instBorelSpace : BorelSpace (AdeleRing R K) :=
  inferInstanceAs <| BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

variable [NumberField K]

/-- The adele ring of a number field is Polish. -/
instance AdeleRing.instPolishSpace : PolishSpace (AdeleRing R K) :=
  inferInstanceAs <| PolishSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

section Examples

variable (F : Type*) [Field F] [NumberField F]

/-- For the ring of integers of a number field all hypotheses are found by instance search: a
product of a Borel set of infinite adeles and a Borel set of finite adeles is a Borel set of
adeles. -/
example {s : Set (InfiniteAdeleRing F)} {t : Set (FiniteAdeleRing (𝓞 F) F)} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t : Set (AdeleRing (𝓞 F) F)) :=
  hs.prod ht

/-- The ideles of a number field form a Polish Borel space for their native topology. -/
example : PolishSpace (IdeleGroup (𝓞 F) F) ∧ BorelSpace (IdeleGroup (𝓞 F) F) :=
  ⟨inferInstance, inferInstance⟩

/-- So do the general linear groups over its adeles. -/
example (n : ℕ) : PolishSpace (GL (Fin n) (AdeleRing (𝓞 F) F)) ∧
    BorelSpace (GL (Fin n) (AdeleRing (𝓞 F) F)) :=
  ⟨inferInstance, inferInstance⟩

end Examples

end NumberField

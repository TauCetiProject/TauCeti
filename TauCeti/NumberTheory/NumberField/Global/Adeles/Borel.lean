/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.NumberTheory.NumberField.Global.Adeles.LocallyCompact
public import TauCeti.NumberTheory.NumberField.RingOfIntegers.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Borel

/-!
# Borel structures on adeles

For a number field `K`, this file registers the Borel structures on which the Haar measures of
adeles live.

The infinite adeles carry their Borel σ-algebra. The local completions `K_v` get their Borel
σ-algebras in `TauCeti.RingTheory.DedekindDomain.AdicValuation.Borel`, and the finite adeles in
`TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Borel`. The adele ring carries the product
σ-algebra of `K_∞ × 𝔸_{K,f}`, which is its Borel σ-algebra by second countability
(`NumberField.AdeleRing.instBorelSpace`): the ring of integers `𝓞 K` is countable
(`NumberField.instCountableRingOfIntegers`), so `𝔸_{K,f}` and `𝔸_K` are second countable
(`IsDedekindDomain.FiniteAdeleRing.instSecondCountableTopology`,
`NumberField.AdeleRing.instSecondCountableTopology`). The unit groups (the ideles and `K_∞ˣ`) and
`GL_n` of the adelic rings carry the Borel σ-algebras of their native units topologies through the
general definition `Units.borelMeasurableSpace`
(`TauCeti.MeasureTheory.Constructions.BorelSpace.Units`), not through instances, since Mathlib's
`Units.instMeasurableSpace` already gives unit groups the pullback σ-algebra along `Units.val`.

## Main results

* `NumberField.InfiniteAdeleRing.instBorelSpace`, `NumberField.AdeleRing.instBorelSpace`.
-/

public section

noncomputable section

open IsDedekindDomain MeasureTheory NumberField

namespace NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The Borel σ-algebra on the infinite adele ring. -/
instance InfiniteAdeleRing.instMeasurableSpace : MeasurableSpace (InfiniteAdeleRing K) := borel _

instance InfiniteAdeleRing.instBorelSpace : BorelSpace (InfiniteAdeleRing K) := ⟨rfl⟩

/-- The adele ring `K_∞ × 𝔸_{K,f}` carries the product σ-algebra. -/
instance AdeleRing.instMeasurableSpace : MeasurableSpace (AdeleRing R K) :=
  inferInstanceAs <| MeasurableSpace (InfiniteAdeleRing K × FiniteAdeleRing R K)

/-- The product σ-algebra on the adele ring of a number field is its Borel σ-algebra. -/
instance AdeleRing.instBorelSpace [NumberField K] : BorelSpace (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| BorelSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end NumberField

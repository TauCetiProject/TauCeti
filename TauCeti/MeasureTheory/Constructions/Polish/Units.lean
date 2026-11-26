/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import TauCeti.Topology.Algebra.Group.Units

/-!
# The Borel structure on the units of a Polish monoid

Mathlib gives the units `Mˣ` of a measurable monoid the σ-algebra `Units.instMeasurableSpace`
pulled back along the coercion `Units.val : Mˣ → M`. The units also carry their own topology,
induced by `u ↦ (u, u⁻¹)`, which is in general strictly finer than the subspace topology: over the
ideles, inversion is not continuous for the subspace topology of the adeles. This file shows that
for a Polish monoid `M` with continuous multiplication and its Borel σ-algebra, the two
measurable structures on `Mˣ` nevertheless agree, so `Mˣ` is a Borel space.

The proof is the Lusin–Souslin theorem. By `Units.instPolishSpace` the units form a Polish space,
and `Units.val` is continuous and injective, so it maps each open set of `Mˣ` onto a Borel subset
of `M`. Every open set of `Mˣ` is therefore the preimage of a Borel set of `M`.

## Main results

* `Units.measurableSet_range_val`: the units of a Polish monoid form a Borel subset.
* `Units.measurableEmbedding_val`: the coercion `Mˣ → M` is a measurable embedding.
* `Units.borelSpace`: the units of a Polish monoid form a Borel space.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156, Springer,
  1995, Theorem 15.1 (Lusin–Souslin).
-/

public section

open MeasureTheory Set

namespace Units

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] [PolishSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- **The units of a Polish monoid form a Borel subset.** This is the Lusin–Souslin theorem for
the continuous injection `Units.val` out of the Polish space `Mˣ`. -/
@[to_additive /-- The additive units of a Polish additive monoid form a Borel subset. -/]
theorem measurableSet_range_val : MeasurableSet (range (val : Mˣ → M)) :=
  measurableSet_range_of_continuous_injective continuous_val val_injective

/-- **The units of a Polish monoid form a Borel space.** The σ-algebra that Mathlib pulls back
along `Units.val` is the Borel σ-algebra of the topology of `Mˣ`. -/
@[to_additive /-- The additive units of a Polish additive monoid form a Borel space. -/]
instance borelSpace : BorelSpace Mˣ where
  measurable_eq := by
    -- Against the Borel σ-algebra of `Mˣ`, the continuous injection `Units.val` out of the Polish
    -- space `Mˣ` is a measurable embedding (Lusin–Souslin), so pulling back along it recovers the
    -- Borel σ-algebra.
    let _ : MeasurableSpace Mˣ := borel Mˣ
    have : BorelSpace Mˣ := ⟨rfl⟩
    exact (continuous_val.measurableEmbedding val_injective).comap_eq

/-- The coercion from the units of a Polish monoid is a measurable embedding. -/
@[to_additive /-- The coercion from the additive units of a Polish additive monoid is a measurable
embedding. -/]
theorem measurableEmbedding_val : MeasurableEmbedding (val : Mˣ → M) :=
  continuous_val.measurableEmbedding val_injective

end Units

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Cardinal.Partition.Basic
public import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# Pigeonhole principles as partition relations

The infinite pigeonhole principle says that a map from a set of infinite cardinality `κ` to a
set of cardinality less than the cofinality of `κ` has a fibre of cardinality `κ`. In the language
of the partition calculus this is the relation `κ → (κ)¹_μ` for `μ < cf κ`; for regular `κ` the
condition is `μ < κ`. Its successor-cardinal instance `κ⁺ → (κ⁺)¹_κ` is the exponent-one case of
the Erdős–Rado theorem `ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ` and the base of its induction.

A second form concerns unboundedness rather than size: a map from a linear order to a type of
cardinality less than the cofinality of the order takes some value on a cofinal set. For the
countable ordinals and a countable type, this is the form used to make countably many choices
coherently along `ω₁`.

## Main results

* `Cardinal.partitionRel_one_of_lt_cof`: `κ → (κ)¹_μ` for infinite `κ` and `μ < cf κ`.
* `Cardinal.partitionRel_one_of_isRegular`: `κ → (κ)¹_μ` for regular `κ` and `μ < κ`.
* `Cardinal.partitionRel_succ_one`: `κ⁺ → (κ⁺)¹_κ` for infinite `κ`.
* `TauCeti.exists_isCofinal_fiber`: a map from a linear order to a type of cardinality less than
  its cofinality has a cofinal fibre.
* `TauCeti.exists_isCofinal_fiber_Iio_omega_one`: a map from `Set.Iio ω₁` to a countable type has a
  cofinal fibre.

## References

* D. Marker, *Lectures on Infinitary Model Theory*, Lecture Notes in Logic 46 (2016): the proof of
  Theorem 5.5 (case `n = 0`) and the proof of Theorem 5.2.
-/

public section

universe u v

open Cardinal Ordinal Set

namespace Cardinal

/-- **The pigeonhole principle for an infinite cardinal.** If `κ` is infinite and `μ < cf κ`,
then `κ → (κ)¹_μ`: every map from a set of cardinality `κ` to a set of cardinality at most `μ` has
a fibre of cardinality `κ`. -/
theorem partitionRel_one_of_lt_cof {κ μ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hμ : μ < κ.ord.cof) :
    PartitionRel κ κ 1 μ := by
  rw [partitionRel_one_iff]
  intro X D hX hD f
  obtain ⟨d, hd⟩ := infinite_pigeonhole_card f κ hX.ge hκ (hD.trans_lt hμ)
  exact ⟨f ⁻¹' {d}, hd, fun x hx y hy ↦ hx.trans hy.symm⟩

/-- **The pigeonhole principle for a regular cardinal.** If `κ` is regular and `μ < κ`, then
`κ → (κ)¹_μ`: every map from a set of cardinality `κ` to a set of cardinality at most `μ` has a
fibre of cardinality `κ`. -/
theorem partitionRel_one_of_isRegular {κ μ : Cardinal.{u}} (hκ : κ.IsRegular) (hμ : μ < κ) :
    PartitionRel κ κ 1 μ :=
  partitionRel_one_of_lt_cof hκ.aleph0_le (by rwa [hκ.cof_ord])

/-- **The pigeonhole principle for a successor cardinal**, `κ⁺ → (κ⁺)¹_κ` for infinite `κ`: every
map from a set of cardinality `κ⁺` to a set of cardinality at most `κ` has a fibre of cardinality
`κ⁺`. -/
theorem partitionRel_succ_one {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    PartitionRel (Order.succ κ) (Order.succ κ) 1 κ :=
  partitionRel_one_of_isRegular (isRegular_succ hκ) (Order.lt_succ κ)

end Cardinal

namespace TauCeti

/-- **The pigeonhole principle for cofinal sets.** A map from a linear order to a type of
cardinality less than the cofinality of the order takes some value on a cofinal set. -/
theorem exists_isCofinal_fiber {α : Type u} [LinearOrder α] {D : Type v} (f : α → D)
    (h : lift.{u} #D < lift.{v} (Order.cof α)) : ∃ d, IsCofinal (f ⁻¹' {d}) := by
  have hunion : IsCofinal (⋃₀ range fun d ↦ f ⁻¹' {d}) := by
    simp [← preimage_iUnion, iUnion_of_singleton]
  obtain ⟨_, ⟨d, rfl⟩, hd⟩ := isCofinal_of_isCofinal_sUnion hunion
    (lift_lt.1 (mk_range_le_lift.trans_lt h))
  exact ⟨d, hd⟩

/-- **The `ω₁`-pigeonhole principle.** A map from the countable ordinals to a countable type takes
some value on a cofinal set of countable ordinals: there is `d` such that every `β < ω₁` lies below
some `α < ω₁` with `f α = d`. -/
theorem exists_isCofinal_fiber_Iio_omega_one {D : Type v} [Countable D]
    (f : Iio (ω₁ : Ordinal.{u}) → D) : ∃ d, IsCofinal (f ⁻¹' {d}) :=
  exists_isCofinal_fiber f <| by simp

end TauCeti

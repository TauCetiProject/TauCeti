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

The infinite pigeonhole principle says that a map from a set of regular cardinality `κ` to a set
of smaller cardinality has a fibre of cardinality `κ`. In the language of the partition calculus
this is the relation `κ → (κ)¹_μ` for `μ < κ`. It is the exponent-one case of the Erdős–Rado
theorem `ℶₙ(κ)⁺ → (κ⁺)ⁿ⁺¹_κ`, whose induction starts from the successor-cardinal instance
`κ⁺ → (κ⁺)¹_κ`.

A second form concerns unboundedness rather than size: a map from the countable ordinals to a
countable type takes some value at a cofinal set of countable ordinals. This is the form used to
make countably many choices coherently along `ω₁`.

## Main results

* `Cardinal.partitionRel_one_of_isRegular`: `κ → (κ)¹_μ` for regular `κ` and `μ < κ`.
* `Cardinal.partitionRel_succ_one`: `κ⁺ → (κ⁺)¹_κ` for infinite `κ`.
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

/-- **The pigeonhole principle for a regular cardinal.** If `κ` is regular and `μ < κ`, then
`κ → (κ)¹_μ`: every map from a set of cardinality `κ` to a set of cardinality at most `μ` has a
fibre of cardinality `κ`. -/
theorem partitionRel_one_of_isRegular {κ μ : Cardinal.{u}} (hκ : κ.IsRegular) (hμ : μ < κ) :
    PartitionRel κ κ 1 μ := by
  rw [partitionRel_one_iff]
  intro X D hX hD f
  obtain ⟨d, hd⟩ := infinite_pigeonhole_card f κ hX.ge hκ.aleph0_le
    (by rw [hκ.cof_ord]; exact hD.trans_lt hμ)
  exact ⟨f ⁻¹' {d}, hd, fun x hx y hy ↦ hx.trans hy.symm⟩

/-- **The pigeonhole principle for a successor cardinal**, `κ⁺ → (κ⁺)¹_κ` for infinite `κ`: every
map from a set of cardinality `κ⁺` to a set of cardinality at most `κ` has a fibre of cardinality
`κ⁺`. -/
theorem partitionRel_succ_one {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    PartitionRel (Order.succ κ) (Order.succ κ) 1 κ :=
  partitionRel_one_of_isRegular (isRegular_succ hκ) (Order.lt_succ κ)

end Cardinal

namespace TauCeti

/-- **The `ω₁`-pigeonhole principle.** A map from the countable ordinals to a countable type takes
some value on a cofinal set of countable ordinals: there is `d` such that every `β < ω₁` lies below
some `α < ω₁` with `f α = d`. -/
theorem exists_isCofinal_fiber_Iio_omega_one {D : Type v} [Countable D]
    (f : Iio (ω₁ : Ordinal.{u}) → D) : ∃ d, IsCofinal (f ⁻¹' {d}) := by
  have hcount : (range fun d ↦ f ⁻¹' {d}).Countable := countable_range _
  have hcof : #(range fun d ↦ f ⁻¹' {d}) < Order.cof (Iio (ω₁ : Ordinal.{u})) := by
    rw [cof_Iio, ← lift_cof, cof_omega_one, lift_aleph, Ordinal.lift_one]
    exact (mk_le_aleph0_iff.2 hcount.to_subtype).trans_lt aleph0_lt_aleph_one
  have hunion : IsCofinal (⋃₀ range fun d ↦ f ⁻¹' {d}) := by
    rw [sUnion_range, ← preimage_iUnion, iUnion_of_singleton, preimage_univ]
    exact IsCofinal.univ
  obtain ⟨_, ⟨d, rfl⟩, hd⟩ := isCofinal_of_isCofinal_sUnion hunion hcof
  exact ⟨d, hd⟩

end TauCeti

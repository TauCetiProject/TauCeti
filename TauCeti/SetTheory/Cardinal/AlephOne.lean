/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Regular

/-!
# Ranks into the countable ordinals

A map `r : X → Ordinal` whose values are all countable ordinals (below `ω₁`) controls the size
of `X` and the countability of its subsets as soon as its fibres are small:

* if every fibre has at most `c` elements, then `X` has at most `ℵ₁ * c` elements; with countable
  fibres, `X` has at most `ℵ₁` elements, and exactly `ℵ₁` when it is uncountable;
* with countable fibres, a subset of `X` is countable exactly when `r` is bounded below `ω₁`
  on it.

These are the cardinal estimates behind stratifying a class of countable structures by a
Scott-rank-like invariant: there are `ℵ₁` strata, each stratum is small, and a family of
structures is countable precisely when its ranks are bounded below `ω₁`. The ordinals may live in
any universe, independent of the universe of `X`.

## Main results

* `TauCeti.mk_le_aleph_one_mul_of_mk_preimage_le`: fibres of size at most `c` give `#X ≤ ℵ₁ * c`.
* `TauCeti.mk_le_aleph_one_of_countable_preimage`: countable fibres give `#X ≤ ℵ₁`.
* `TauCeti.mk_eq_aleph_one_of_countable_preimage`: if moreover `X` is uncountable, `#X = ℵ₁`.
* `Set.Countable.exists_lt_omega_one_forall_lt`: on a countable set, a rank below `ω₁` is bounded
  below `ω₁`.
* `TauCeti.countable_preimage_Iio_of_lt_omega_one`: below a countable ordinal, countably many
  countable fibres have a countable union.
* `TauCeti.countable_iff_exists_lt_omega_one_forall_lt`: with countable fibres, a set is countable
  iff the rank is bounded below `ω₁` on it.

## References

The countable-fibre statements, for ranks into `Ordinal.{0}`, are also proved in
`InfinitaryLogic/OrdinalCountability.lean` of Cameron Freer's Lean formalization
`cameronfreer/infinitary-logic` (checkpoint `518a366`, Apache-2.0).
-/

public section

universe u w

open Cardinal Ordinal Set

variable {X : Type u} {r : X → Ordinal.{w}}

/-- **A countable set of countable ordinals is bounded below `ω₁`.** If `r` takes values below
`ω₁` on a countable set `s`, some single countable ordinal strictly bounds `r` on `s`. -/
theorem Set.Countable.exists_lt_omega_one_forall_lt {s : Set X} (hs : s.Countable)
    (hr : ∀ x ∈ s, r x < ω₁) : ∃ β < ω₁, ∀ x ∈ s, r x < β := by
  have := hs.to_subtype
  refine ⟨⨆ x : s, Order.succ (r x),
    Ordinal.iSup_lt_omega_one fun x ↦ (isSuccLimit_omega 1).succ_lt (hr x x.2), fun x hx ↦ ?_⟩
  exact (Order.lt_succ (r x)).trans_le
    (Ordinal.le_iSup (fun x : s ↦ Order.succ (r x)) ⟨x, hx⟩)

namespace TauCeti

/-- **Bounding a set by a rank below `ω₁`.** If `r` takes values below `ω₁` and every fibre of
`r` over a countable ordinal has at most `c` elements, then `X` has at most `ℵ₁ * c` elements. -/
theorem mk_le_aleph_one_mul_of_mk_preimage_le {c : Cardinal.{u}} (hr : ∀ x, r x < ω₁)
    (hc : ∀ o < ω₁, #(r ⁻¹' {o}) ≤ c) : #X ≤ ℵ₁ * c := by
  -- Corestrict `r` to the countable ordinals, a set of size `ℵ₁`, and count fibre by fibre.
  let f : X → Iio (ω₁ : Ordinal.{w}) := fun x ↦ ⟨r x, hr x⟩
  have hf : ∀ o, lift.{w + 1} #(f ⁻¹' {o}) ≤ lift.{w + 1} c := fun o ↦ by
    have hpre : f ⁻¹' {o} = r ⁻¹' {o.1} := by
      ext x
      simp [f, Subtype.ext_iff]
    rw [hpre, Cardinal.lift_le]
    exact hc o.1 o.2
  have h := lift_mk_le_lift_mk_mul_of_lift_mk_preimage_le f hf
  rw [← Cardinal.lift_le.{w + 1}]
  simpa using h

/-- **Countable fibres over the countable ordinals bound a set by `ℵ₁`.** If `r` takes values
below `ω₁` and each of its fibres over a countable ordinal is countable, then `#X ≤ ℵ₁`. -/
theorem mk_le_aleph_one_of_countable_preimage (hr : ∀ x, r x < ω₁)
    (hfib : ∀ o < ω₁, (r ⁻¹' {o}).Countable) : #X ≤ ℵ₁ := by
  have h := mk_le_aleph_one_mul_of_mk_preimage_le hr fun o ho ↦
    le_aleph0_iff_set_countable.2 (hfib o ho)
  rwa [mul_aleph0_eq (aleph0_le_aleph 1)] at h

/-- **An uncountable set with a rank below `ω₁` and countable fibres has exactly `ℵ₁`
elements.** -/
theorem mk_eq_aleph_one_of_countable_preimage [Uncountable X] (hr : ∀ x, r x < ω₁)
    (hfib : ∀ o < ω₁, (r ⁻¹' {o}).Countable) : #X = ℵ₁ :=
  (mk_le_aleph_one_of_countable_preimage hr hfib).antisymm
    (aleph_one_le_iff.2 (aleph0_lt_mk_iff.2 ‹_›))

/-- **Countably many countable fibres.** If the fibres of `r` over the ordinals below a countable
ordinal `β` are countable, then so is the set of points of rank below `β`. -/
theorem countable_preimage_Iio_of_lt_omega_one {β : Ordinal.{w}} (hβ : β < ω₁)
    (hfib : ∀ o < β, (r ⁻¹' {o}).Countable) : (r ⁻¹' Iio β).Countable := by
  rw [← biUnion_of_singleton (Iio β), preimage_iUnion₂]
  exact (countable_Iio_of_lt_omega_one hβ).biUnion hfib

/-- **Countable means bounded below `ω₁`.** For a rank `r` below `ω₁` on `s` whose fibres over
the countable ordinals are countable, `s` is countable exactly when `r` is bounded on `s` by a
countable ordinal. -/
theorem countable_iff_exists_lt_omega_one_forall_lt {s : Set X} (hr : ∀ x ∈ s, r x < ω₁)
    (hfib : ∀ o < ω₁, (r ⁻¹' {o}).Countable) :
    s.Countable ↔ ∃ β < ω₁, ∀ x ∈ s, r x < β :=
  ⟨fun hs ↦ hs.exists_lt_omega_one_forall_lt hr, fun ⟨_, hβ, hs⟩ ↦
    (countable_preimage_Iio_of_lt_omega_one hβ fun o ho ↦ hfib o (ho.trans hβ)).mono
      fun x hx ↦ hs x hx⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# The Kuratowski–Ulam theorem

The Kuratowski–Ulam theorem is the analogue of Fubini's theorem for Baire category: a set `s` with
the Baire property in a product `X × Y` with `Y` second countable is comeagre if and only if,
for comeagrely many `x`, its section `{y | (x, y) ∈ s}` is comeagre. Equivalently, `s` is meagre
if and only if comeagrely many of its sections are meagre. No Baire hypothesis on the factors and
no countability hypothesis on `X` is needed; exchanging the order of the two quantifiers uses
second countability of both factors.

The sections of `s : Set (X × Y)` are written `(x, ·) ⁻¹' s` and `(·, y) ⁻¹' s`. The curried
filter `(residual X).curry (residual Y)` is the filter of sets with comeagrely many comeagre
sections, so the theorem says that this filter agrees with `residual (X × Y)` on sets with the
Baire property; one inclusion holds for all sets.

This is how meagreness of a relation is checked through its sections, for example to show that
an equivalence relation with the Baire property and meagre classes is meagre in the square.

## Main results

* `Dense.eventually_dense_curry_left`: comeagrely many sections of a dense open set are dense.
* `IsNowhereDense.eventually_isNowhereDense_curry_left`: comeagrely many sections of a nowhere
  dense set are nowhere dense.
* `TauCeti.curry_le_residual`: `(residual X).curry (residual Y) ≤ residual (X × Y)`, that is, a
  comeagre subset of `X × Y` has comeagre sections over a comeagre set of `x`.
* `IsMeagre.eventually_isMeagre_curry_left`: comeagrely many sections of a meagre set are meagre.
* `IsMeagre.prod_left`, `IsMeagre.prod_right`: a product with a meagre factor is meagre.
* `BaireMeasurableSet.baireMeasurableSet_curry_left`: comeagrely many sections of a set with the
  Baire property have the Baire property.
* `BaireMeasurableSet.mem_curry_iff_mem_residual`: **the Kuratowski–Ulam theorem**, with the
  right-hand form `eventually_eventually_right_iff_mem_residual` and the
  exchange of quantifiers `eventually_eventually_swap`.
* `BaireMeasurableSet.eventually_isMeagre_curry_left_iff_isMeagre` and
  `BaireMeasurableSet.isMeagre_of_forall_isMeagre_curry_left`: the meagre-sections forms.

## References

* K. Kuratowski and S. Ulam, *Quelques propriétés topologiques du produit combinatoire*,
  Fundamenta Mathematicae 19 (1932), 247–251.
* A. S. Kechris, *Classical Descriptive Set Theory*, Springer, 1995, Theorem 8.41.
* The statements and the proof of the converse direction follow Mathlib PR #17368 by
  Felix Weilacher (`curry_le_residual`, `IsMeagre.prod_left`, and the `BaireMeasurableSet`
  forms of the theorem).
-/

public section

open Set Filter Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Sections

variable [SecondCountableTopology Y] {s : Set (X × Y)}

/-- If `s` is a dense open subset of `X × Y` with `Y` second countable, then for comeagrely many
`x` the section `(x, ·) ⁻¹' s` is dense. -/
theorem Dense.eventually_dense_curry_left (hd : Dense s) (ho : IsOpen s) :
    ∀ᵇ x : X, Dense ((x, ·) ⁻¹' s) := by
  -- For a basic open set `t` of `Y`, the set of `x` whose section meets `t` is the projection
  -- of `s ∩ (X × t)`, which is open and dense.
  have hB := isBasis_countableBasis Y
  simp_rw [hB.dense_iff]
  refine (eventually_countable_ball (countable_countableBasis Y)).2 fun t ht ↦ ?_
  rcases t.eq_empty_or_nonempty with rfl | htne
  · exact Eventually.of_forall fun _ h ↦ absurd h not_nonempty_empty
  have htO := hB.isOpen ht
  have hA : Dense (Prod.fst '' (s ∩ Prod.snd ⁻¹' t)) := by
    refine dense_iff_inter_open.2 fun u hu hune ↦ ?_
    obtain ⟨⟨x, y⟩, ⟨hxu, hyt⟩, hxy⟩ := hd.inter_open_nonempty _ (hu.prod htO) (hune.prod htne)
    exact ⟨x, hxu, (x, y), ⟨hxy, hyt⟩, rfl⟩
  filter_upwards [residual_of_dense_open
    (isOpenMap_fst _ (ho.inter (htO.preimage continuous_snd))) hA]
    with x ⟨⟨x', y⟩, ⟨hxy, hyt⟩, hx⟩ _
  subst hx
  exact ⟨y, hyt, hxy⟩

/-- If `s` is a nowhere dense subset of `X × Y` with `Y` second countable, then for comeagrely many
`x` the section `(x, ·) ⁻¹' s` is nowhere dense. -/
theorem IsNowhereDense.eventually_isNowhereDense_curry_left (hs : IsNowhereDense s) :
    ∀ᵇ x : X, IsNowhereDense ((x, ·) ⁻¹' s) := by
  obtain ⟨ho, hd⟩ := isClosed_isNowhereDense_iff_compl.1 ⟨isClosed_closure, hs.closure⟩
  filter_upwards [hd.eventually_dense_curry_left ho] with x hx
  refine (isClosed_isNowhereDense_iff_compl.2 ⟨?_, hx⟩).2.mono (preimage_mono subset_closure)
  exact ho.preimage (by fun_prop)

namespace TauCeti

/-- **One half of the Kuratowski–Ulam theorem.** If `Y` is second countable, every comeagre subset
of `X × Y` has comeagre sections `(x, ·) ⁻¹' s` over a comeagre set of `x`. -/
theorem curry_le_residual : (residual X).curry (residual Y) ≤ residual (X × Y) := by
  refine le_countableGenerate_iff_of_countableInterFilter.2 ?_
  rintro s ⟨ho, hd⟩
  refine mem_curry_iff.2 ?_
  filter_upwards [hd.eventually_dense_curry_left ho] with x hx
  exact residual_of_dense_open (ho.preimage (by fun_prop)) hx

/-- **One half of the Kuratowski–Ulam theorem.** If `Y` is second countable and `s` is comeagre
in `X × Y`, then comeagrely many sections `(x, ·) ⁻¹' s` are comeagre. -/
theorem eventually_eventually_left_of_mem_residual (hs : s ∈ residual (X × Y)) :
    ∀ᵇ x : X, ∀ᵇ y : Y, (x, y) ∈ s :=
  curry_le_residual hs

end TauCeti

/-- If `Y` is second countable and `s` is meagre in `X × Y`, then comeagrely many sections
`(x, ·) ⁻¹' s` are meagre. -/
theorem IsMeagre.eventually_isMeagre_curry_left (hs : IsMeagre s) :
    ∀ᵇ x : X, IsMeagre ((x, ·) ⁻¹' s) :=
  TauCeti.eventually_eventually_left_of_mem_residual hs

/-- If `Y` is second countable and `s` has the Baire property in `X × Y`, then comeagrely many
sections `(x, ·) ⁻¹' s` have the Baire property. -/
theorem BaireMeasurableSet.baireMeasurableSet_curry_left (hs : BaireMeasurableSet s) :
    ∀ᵇ x : X, BaireMeasurableSet ((x, ·) ⁻¹' s) := by
  obtain ⟨u, hu, hsu⟩ := hs.residualEq_isOpen
  filter_upwards [TauCeti.eventually_eventually_left_of_mem_residual hsu.mem_iff] with x hx
  exact (hu.preimage (by fun_prop)).baireMeasurableSet.congr hx.set_eq.symm

end Sections

namespace TauCeti

/-- **One half of the Kuratowski–Ulam theorem.** If `X` is second countable and `s` is comeagre
in `X × Y`, then comeagrely many sections `(·, y) ⁻¹' s` are comeagre. -/
theorem eventually_eventually_right_of_mem_residual [SecondCountableTopology X]
    {s : Set (X × Y)} (hs : s ∈ residual (X × Y)) : ∀ᵇ y : Y, ∀ᵇ x : X, (x, y) ∈ s :=
  eventually_eventually_left_of_mem_residual
    (tendsto_residual_of_isOpenMap continuous_swap (Homeomorph.prodComm Y X).isOpenMap hs)

end TauCeti

/-- A product whose left factor is meagre is meagre. -/
theorem IsMeagre.prod_left {s : Set X} (hs : IsMeagre s) (t : Set Y) : IsMeagre (s ×ˢ t) :=
  (hs.preimage_of_isOpenMap continuous_fst isOpenMap_fst).mono (prod_subset_preimage_fst s t)

/-- A product whose right factor is meagre is meagre. -/
theorem IsMeagre.prod_right {t : Set Y} (ht : IsMeagre t) (s : Set X) : IsMeagre (s ×ˢ t) :=
  (ht.preimage_of_isOpenMap continuous_snd isOpenMap_snd).mono (prod_subset_preimage_snd s t)

namespace BaireMeasurableSet

/-- If `X` is second countable and `s` has the Baire property in `X × Y`, then comeagrely many
sections `(·, y) ⁻¹' s` have the Baire property. -/
theorem baireMeasurableSet_curry_right [SecondCountableTopology X] {s : Set (X × Y)}
    (hs : BaireMeasurableSet s) : ∀ᵇ y : Y, BaireMeasurableSet ((·, y) ⁻¹' s) :=
  (hs.preimage continuous_swap (Homeomorph.prodComm Y X).isOpenMap).baireMeasurableSet_curry_left

section Left

variable [SecondCountableTopology Y] {s : Set (X × Y)}

/-- If `Y` is second countable, a non-meagre set `s` with the Baire property in `X × Y` is
frequently met along the curried residual filter: the set of `x` whose section `(x, ·) ⁻¹' s` is
non-meagre is itself non-meagre. -/
theorem frequently_curry_of_not_isMeagre (hs : BaireMeasurableSet s) (hn : ¬ IsMeagre s) :
    ∃ᶠ p in (residual X).curry (residual Y), p ∈ s := by
  obtain ⟨u, hu, hsu⟩ := hs.residualEq_isOpen
  have hun : ¬ IsMeagre u := fun h ↦
    hn (Eventually.congr h (hsu.compl.mem_iff.mono fun _ h ↦ h.symm))
  -- `u` is covered by the countably many boxes `{x | {x} ×ˢ t ⊆ u} ×ˢ t` over basic open sets
  -- `t` of `Y`, one of which is non-meagre.
  have hU : u ⊆ ⋃ t ∈ countableBasis Y, {x | ∀ y ∈ t, (x, y) ∈ u} ×ˢ t := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨t, ht, hyt, htu⟩ :=
      (isBasis_countableBasis Y).isOpen_iff.1 (hu.preimage (by fun_prop)) y hxy
    exact mem_biUnion ht ⟨fun _ hy ↦ htu hy, hyt⟩
  obtain ⟨t, -, hb⟩ :=
    exists_of_not_isMeagre_biUnion (countable_countableBasis Y) fun h ↦ hun (h.mono hU)
  have hvw : ∃ᶠ p in (residual X).curry (residual Y), p ∈ {x | ∀ y ∈ t, (x, y) ∈ u} ×ˢ t :=
    frequently_curry_prod_iff.2
      ⟨fun h ↦ hb (IsMeagre.prod_left h t), fun h ↦ hb (IsMeagre.prod_right h _)⟩
  refine (hvw.and_eventually (TauCeti.curry_le_residual hsu.mem_iff)).mono ?_
  rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hpsu⟩
  exact hpsu.2 (hx y hy)

/-- **The Kuratowski–Ulam theorem.** If `Y` is second countable, a set `s` with the Baire property
in `X × Y` is comeagre if and only if it belongs to the curried residual filter, that is, if and
only if comeagrely many sections `(x, ·) ⁻¹' s` are comeagre. -/
theorem mem_curry_iff_mem_residual (hs : BaireMeasurableSet s) :
    s ∈ (residual X).curry (residual Y) ↔ s ∈ residual (X × Y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ TauCeti.curry_le_residual h⟩
  by_contra hns
  have hn : ¬ IsMeagre sᶜ := by rwa [IsMeagre, compl_compl]
  exact hs.compl.frequently_curry_of_not_isMeagre hn (mem_of_superset h fun _ hp hpc ↦ hpc hp)

/-- **The Kuratowski–Ulam theorem**, meagre form. If `Y` is second countable, a set `s` with the
Baire property in `X × Y` is meagre if and only if comeagrely many sections `(x, ·) ⁻¹' s` are
meagre. -/
theorem eventually_isMeagre_curry_left_iff_isMeagre (hs : BaireMeasurableSet s) :
    (∀ᵇ x : X, IsMeagre ((x, ·) ⁻¹' s)) ↔ IsMeagre s :=
  hs.compl.mem_curry_iff_mem_residual

/-- If `Y` is second countable, a set with the Baire property in `X × Y` all of whose sections
`(x, ·) ⁻¹' s` are meagre is meagre. -/
theorem isMeagre_of_forall_isMeagre_curry_left (hs : BaireMeasurableSet s)
    (h : ∀ x, IsMeagre ((x, ·) ⁻¹' s)) : IsMeagre s :=
  hs.eventually_isMeagre_curry_left_iff_isMeagre.1 (Eventually.of_forall h)

end Left

/-- **The Kuratowski–Ulam theorem**, right-hand form. If `X` is second countable, a set `s` with
the Baire property in `X × Y` is comeagre if and only if comeagrely many sections `(·, y) ⁻¹' s`
are comeagre. -/
theorem eventually_eventually_right_iff_mem_residual [SecondCountableTopology X]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    (∀ᵇ y : Y, ∀ᵇ x : X, (x, y) ∈ s) ↔ s ∈ residual (X × Y) := by
  rw [← (Homeomorph.prodComm Y X).residual_map_eq]
  exact (hs.preimage continuous_swap (Homeomorph.prodComm Y X).isOpenMap).mem_curry_iff_mem_residual

/-- For a set with the Baire property in a product of second countable spaces, the two orders of
the category quantifiers agree. -/
theorem eventually_eventually_swap [SecondCountableTopology X] [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    (∀ᵇ x : X, ∀ᵇ y : Y, (x, y) ∈ s) ↔ ∀ᵇ y : Y, ∀ᵇ x : X, (x, y) ∈ s :=
  hs.mem_curry_iff_mem_residual.trans
    hs.eventually_eventually_right_iff_mem_residual.symm

end BaireMeasurableSet

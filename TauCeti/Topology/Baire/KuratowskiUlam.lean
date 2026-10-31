/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Curry
public import Mathlib.Topology.Baire.BaireMeasurable

/-!
# The Kuratowski–Ulam theorem

The Kuratowski–Ulam theorem is the Baire-category analogue of Fubini's theorem: for a set
`s ⊆ X × Y` with the Baire property, `s` is comeagre if and only if for comeagrely many `x` the
section `{y | (x, y) ∈ s}` is comeagre, and `s` is meagre if and only if comeagrely many of its
sections are meagre.

The forward direction needs only that `Y` is second countable. If `U` is open and dense in `X × Y`
and `V` runs over a countable basis of `Y`, the projections of `U ∩ (X × V)` to `X` are countably
many dense open sets, and a point `x` in all of them has a section of `U` meeting every basic open
set. Hence comeagre sets have comeagre sections over a comeagre set of `x`, which is the filter
inequality `(residual X).curry (residual Y) ≤ residual (X × Y)`.

The converse needs the Baire property, and again only that `Y` is second countable. A
Baire-measurable set differs from an open set by a meagre set. An open set `u` with comeagrely many
meagre sections is covered by the countably many boxes `{x | {x} ×ˢ V ⊆ u} ×ˢ V` with `V` basic,
and each of them has a meagre side. The right-hand forms, quantifying over `y` first, follow by
swapping the factors and need `X` second countable instead. No Baire space hypothesis is needed
anywhere: in a space that is meagre in itself both sides of each equivalence hold trivially.

## Main results

* `IsMeagre.prod_left`, `IsMeagre.prod_right`: a product with a meagre factor is meagre.
* `TauCeti.curry_le_residual`: comeagre subsets of `X × Y` have comeagre sections over a comeagre
  set of `x`, stated as `(residual X).curry (residual Y) ≤ residual (X × Y)`.
* `TauCeti.eventually_eventually_left_of_mem_residual` and its right-hand form, obtained through
  `TauCeti.preimage_swap_mem_residual_iff`.
* `IsNowhereDense.eventually_isNowhereDense_sections`, `IsMeagre.eventually_isMeagre_sections`:
  nowhere dense and meagre subsets of `X × Y` have nowhere dense and meagre sections over a
  comeagre set of `x`.
* `BaireMeasurableSet.baireMeasurableSet_curry_left`: a Baire-measurable subset of `X × Y` has
  Baire-measurable sections over a comeagre set of `x`.
* `BaireMeasurableSet.isMeagre_iff_eventually_isMeagre_sections` and
  `TauCeti.isMeagre_of_forall_isMeagre_sections`: a Baire-measurable set is meagre iff comeagrely
  many of its sections are meagre.
* `BaireMeasurableSet.eventually_eventually_left_iff_mem_residual`, its right-hand form, and
  `BaireMeasurableSet.eventually_eventually_left_iff_eventually_eventually_right`: the
  Kuratowski–Ulam theorem for comeagre sets, and the exchange of the two iterated quantifiers.

## References

* K. Kuratowski and S. Ulam, *Quelques propriétés topologiques du produit combinatoire*,
  Fundamenta Mathematicae 19 (1932), 247–251.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 8.41.
* The declaration names follow Mathlib PR #17368 (the Kuratowski–Ulam theorem).
-/

public section

open Set Filter Topology TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A product whose first factor is meagre is meagre. -/
theorem IsMeagre.prod_left {s : Set X} (hs : IsMeagre s) (t : Set Y) : IsMeagre (s ×ˢ t) :=
  (hs.preimage_of_isOpenMap continuous_fst isOpenMap_fst).mono fun _ hp => hp.1

/-- A product whose second factor is meagre is meagre. -/
theorem IsMeagre.prod_right (s : Set X) {t : Set Y} (ht : IsMeagre t) : IsMeagre (s ×ˢ t) :=
  (ht.preimage_of_isOpenMap continuous_snd isOpenMap_snd).mono fun _ hp => hp.2

namespace TauCeti

/-- A dense open subset of `X × Y` has dense sections over a comeagre set of `x`, when `Y` is
second countable. -/
private theorem eventually_dense_preimage_prodMk [SecondCountableTopology Y] {u : Set (X × Y)}
    (hu : IsOpen u) (hd : Dense u) : ∀ᶠ x in residual X, Dense (Prod.mk x ⁻¹' u) := by
  have hV : ∀ V ∈ countableBasis Y, ∀ᶠ x in residual X, (V ∩ Prod.mk x ⁻¹' u).Nonempty := by
    intro V hV
    have hVo : IsOpen V := (isBasis_countableBasis Y).isOpen hV
    refine mem_of_superset (residual_of_dense_open
      (isOpenMap_fst _ (hu.inter (isOpen_univ.prod hVo))) ?_) ?_
    · refine dense_iff_inter_open.2 fun O hO hOne => ?_
      have hVne : V.Nonempty :=
        nonempty_iff_ne_empty.2 fun h => empty_notMem_countableBasis Y (h ▸ hV)
      obtain ⟨⟨x, y⟩, hxy, hxyu⟩ := hd.inter_open_nonempty _ (hO.prod hVo) (hOne.prod hVne)
      exact ⟨x, hxy.1, ⟨(x, y), ⟨hxyu, trivial, hxy.2⟩, rfl⟩⟩
    · rintro x ⟨⟨_, y⟩, ⟨hxyu, -, hy⟩, rfl⟩
      exact ⟨y, hy, hxyu⟩
  filter_upwards [(eventually_countable_ball (countable_countableBasis Y)).2 hV] with x hx
  exact (isBasis_countableBasis Y).dense_iff.2 fun V hV _ => hx V hV

/-- **Kuratowski–Ulam**, forward direction: a comeagre subset of `X × Y` has comeagre sections
over a comeagre set of `x`. Only the second factor needs to be second countable. -/
theorem curry_le_residual [SecondCountableTopology Y] :
    (residual X).curry (residual Y) ≤ residual (X × Y) := by
  refine le_countableGenerate_iff_of_countableInterFilter.2 ?_
  rintro u ⟨hu, hd⟩
  exact mem_curry_iff.2 <| (eventually_dense_preimage_prodMk hu hd).mono fun x hx =>
    residual_of_dense_open (hu.preimage (Continuous.prodMk_right x)) hx

/-- A comeagre subset of `X × Y` has comeagre sections over a comeagre set of `x`. -/
theorem eventually_eventually_left_of_mem_residual [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : s ∈ residual (X × Y)) :
    ∀ᶠ x in residual X, ∀ᶠ y in residual Y, (x, y) ∈ s :=
  curry_le_residual hs

/-- A subset of `X × Y` is comeagre if and only if its preimage under `Prod.swap` is
comeagre in `Y × X`. -/
theorem preimage_swap_mem_residual_iff {s : Set (X × Y)} :
    Prod.swap ⁻¹' s ∈ residual (Y × X) ↔ s ∈ residual (X × Y) := by
  rw [← (Homeomorph.prodComm X Y).residual_map_eq, mem_map, Homeomorph.coe_prodComm,
    preimage_preimage]
  simp

/-- A comeagre subset of `X × Y` has comeagre vertical sections over a comeagre set of `y`. -/
theorem eventually_eventually_right_of_mem_residual [SecondCountableTopology X]
    {s : Set (X × Y)} (hs : s ∈ residual (X × Y)) :
    ∀ᶠ y in residual Y, ∀ᶠ x in residual X, (x, y) ∈ s :=
  eventually_eventually_left_of_mem_residual (preimage_swap_mem_residual_iff.2 hs)

end TauCeti

open TauCeti

/-- A nowhere dense subset of `X × Y` has nowhere dense sections over a comeagre set of `x`, when
`Y` is second countable. -/
theorem IsNowhereDense.eventually_isNowhereDense_sections [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : IsNowhereDense s) :
    ∀ᶠ x in residual X, IsNowhereDense (Prod.mk x ⁻¹' s) := by
  have hc : IsOpen (closure s)ᶜ := isClosed_closure.isOpen_compl
  have hd : Dense (closure s)ᶜ :=
    interior_eq_empty_iff_dense_compl.1 (isClosed_closure.isNowhereDense_iff.1 hs.closure)
  filter_upwards [eventually_dense_preimage_prodMk hc hd] with x hx
  exact ((isClosed_closure.preimage (Continuous.prodMk_right x)).isNowhereDense_iff.2
    (interior_eq_empty_iff_dense_compl.2 hx)).mono (preimage_mono subset_closure)

/-- A meagre subset of `X × Y` has meagre sections over a comeagre set of `x`, when `Y` is second
countable. -/
theorem IsMeagre.eventually_isMeagre_sections [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : IsMeagre s) : ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' s) := by
  filter_upwards [eventually_eventually_left_of_mem_residual hs] with x hx
  rwa [IsMeagre, ← preimage_compl]

/-- A Baire-measurable subset of `X × Y` has Baire-measurable sections over a comeagre set of `x`,
when `Y` is second countable. -/
theorem BaireMeasurableSet.baireMeasurableSet_curry_left [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    ∀ᶠ x in residual X, BaireMeasurableSet (Prod.mk x ⁻¹' s) := by
  obtain ⟨u, hu, hsu⟩ := hs.residualEq_isOpen
  filter_upwards [eventually_eventually_left_of_mem_residual (eventuallyEqSet_iff.1 hsu)] with x hx
  exact (hu.preimage (Continuous.prodMk_right x)).baireMeasurableSet.congr
    (eventuallyEqSet_iff.2 (hx.mono fun _ h => h.symm))

namespace TauCeti

/-- An open subset of `X × Y` with meagre sections over a comeagre set of `x` is meagre, when `Y`
is second countable. It is covered by the countably many boxes `{x | {x} ×ˢ V ⊆ u} ×ˢ V` with `V`
basic, and in each box either `V` lies in a meagre section or the first side misses a comeagre
set. -/
private theorem isMeagre_of_isOpen_of_eventually_isMeagre_sections [SecondCountableTopology Y]
    {u : Set (X × Y)} (hu : IsOpen u) (h : ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' u)) :
    IsMeagre u := by
  have hcover : u ⊆ ⋃ V ∈ countableBasis Y, {x | ∀ y ∈ V, (x, y) ∈ u} ×ˢ V := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨U, V, -, hV, hxU, hyV, hUV⟩ := isOpen_prod_iff.1 hu x y hxy
    obtain ⟨B, hB, hyB, hBV⟩ := (isBasis_countableBasis Y).exists_subset_of_mem_open hyV hV
    exact mem_biUnion hB ⟨fun y' hy' => hUV ⟨hxU, hBV hy'⟩, hyB⟩
  refine (isMeagre_biUnion (countable_countableBasis Y) fun V _ => ?_).mono hcover
  by_cases hA : ∃ x, (∀ y ∈ V, (x, y) ∈ u) ∧ IsMeagre (Prod.mk x ⁻¹' u)
  · obtain ⟨x, hx, hxu⟩ := hA
    exact IsMeagre.prod_right _ (hxu.mono fun y hy => hx y hy)
  · simp only [not_exists, not_and] at hA
    have hA' : IsMeagre {x | ∀ y ∈ V, (x, y) ∈ u} := by
      rw [IsMeagre]
      exact mem_of_superset h fun x hx hxV => hA x hxV hx
    exact hA'.prod_left _

end TauCeti

/-- **Kuratowski–Ulam** for meagre sets: a Baire-measurable subset of `X × Y` is meagre if and only
if its sections are meagre over a comeagre set of `x`. -/
theorem BaireMeasurableSet.isMeagre_iff_eventually_isMeagre_sections [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) :
    IsMeagre s ↔ ∀ᶠ x in residual X, IsMeagre (Prod.mk x ⁻¹' s) := by
  refine ⟨IsMeagre.eventually_isMeagre_sections, fun h => ?_⟩
  obtain ⟨u, hu, hsu⟩ := hs.residualEq_isOpen
  have hsu' := eventuallyEqSet_iff.1 hsu
  have hu' : IsMeagre u := by
    refine isMeagre_of_isOpen_of_eventually_isMeagre_sections hu ?_
    filter_upwards [h, eventually_eventually_left_of_mem_residual hsu'] with x hx hxu
    rw [IsMeagre] at hx ⊢
    filter_upwards [hx, hxu] with y hy hyu
    exact fun hyu' => hy (hyu.2 hyu')
  rw [IsMeagre] at hu' ⊢
  filter_upwards [hu', hsu'] with p hp hpu
  exact fun hps => hp (hpu.1 hps)

/-- A Baire-measurable subset of `X × Y` all of whose sections are meagre is meagre. -/
theorem TauCeti.isMeagre_of_forall_isMeagre_sections [SecondCountableTopology Y]
    {s : Set (X × Y)} (hs : BaireMeasurableSet s) (h : ∀ x, IsMeagre (Prod.mk x ⁻¹' s)) :
    IsMeagre s :=
  hs.isMeagre_iff_eventually_isMeagre_sections.2 (Eventually.of_forall h)

/-- **Kuratowski–Ulam**: a Baire-measurable subset of `X × Y` is comeagre if and only if its
sections are comeagre over a comeagre set of `x`. -/
theorem BaireMeasurableSet.eventually_eventually_left_iff_mem_residual
    [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : BaireMeasurableSet s) :
    (∀ᶠ x in residual X, ∀ᶠ y in residual Y, (x, y) ∈ s) ↔ s ∈ residual (X × Y) := by
  have h := hs.compl.isMeagre_iff_eventually_isMeagre_sections
  simp_rw [IsMeagre, preimage_compl, compl_compl] at h
  exact h.symm

/-- **Kuratowski–Ulam**, right-hand form: a Baire-measurable subset of `X × Y` is comeagre if and
only if its vertical sections are comeagre over a comeagre set of `y`. -/
theorem BaireMeasurableSet.eventually_eventually_right_iff_mem_residual
    [SecondCountableTopology X] {s : Set (X × Y)}
    (hs : BaireMeasurableSet s) :
    (∀ᶠ y in residual Y, ∀ᶠ x in residual X, (x, y) ∈ s) ↔ s ∈ residual (X × Y) :=
  (BaireMeasurableSet.eventually_eventually_left_iff_mem_residual
    (hs.preimage continuous_swap (Homeomorph.prodComm Y X).isOpenMap)).trans
    (preimage_swap_mem_residual_iff (s := s))

/-- For a Baire-measurable subset of `X × Y`, the two iterated "comeagrely many" quantifiers
agree. -/
theorem BaireMeasurableSet.eventually_eventually_left_iff_eventually_eventually_right
    [SecondCountableTopology X] [SecondCountableTopology Y] {s : Set (X × Y)}
    (hs : BaireMeasurableSet s) :
    (∀ᶠ x in residual X, ∀ᶠ y in residual Y, (x, y) ∈ s) ↔
      ∀ᶠ y in residual Y, ∀ᶠ x in residual X, (x, y) ∈ s :=
  hs.eventually_eventually_left_iff_mem_residual.trans
    hs.eventually_eventually_right_iff_mem_residual.symm

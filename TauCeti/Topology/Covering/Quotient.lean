/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Covering.Quotient
import TauCeti.Topology.Covering.Proper

/-!
# Intermediate quotients of a quotient covering map

Let a group `G` act on a space `E` so that `q : E → X` presents `X` as the quotient `E / G` in
the strong sense of Mathlib's `IsQuotientCoveringMap`: the fibres of `q` are the orbits, and every
point of `E` has a neighbourhood whose `G`-translates are pairwise disjoint. Let `H` be a subgroup
of `G`, and let `qH : E → Y` present `Y` as `E / H` in the same sense. The projection `q` then
factors through `qH`, and the theorem of this file is that the factor

`r : E / H → E / G`

is a covering map. Neither space is assumed connected, and no local connectedness of `X` is
needed: the sheets of `r` over the base set `q '' U` are the images in `Y` of the translates
`g • U`, whose overlaps the disjointness hypothesis controls directly.

The intended reading is that a subgroup of the deck group of a regular covering cuts out an
intermediate covering. That is the shape of the subgroup-to-cover half of the classification of
covering spaces, where `E` is the universal cover of `X` and `G` is its fundamental group; that
application is `TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj`.

The file also records that a surjective covering map is an open quotient map: the companion,
for a covering map with no group acting, of Mathlib's `IsQuotientCoveringMap.isOpenQuotientMap`
that the rest of the file consumes. Finally, the quotient covering map of a finite group has
finite fibres (and hence a compact covering space whenever the base is compact), which is what
makes it a finite covering with a transfer on singular chains. The acting group may be replaced by
any isomorphic group acting compatibly, which is how an abstract group identified with a
fundamental group is made to act on a universal cover. Over a subset `s` of the base, the
restriction `q ⁻¹' s → s` is again a quotient covering map for the restricted action, which is how
a quotient covering of spaces becomes a quotient covering of the topological pairs `(E, q ⁻¹' s)`
and `(X, s)`.

For a discrete additive subgroup `L` of a topological additive group `E`, the orbit projection
`E → AddAction.orbitRel.Quotient L E` for translation by `L` is a quotient covering map. Unlike
Mathlib's `isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd`, this needs no local
compactness or separation axiom: discreteness of `L` alone provides neighbourhoods whose
translates are pairwise disjoint (Mathlib's
`Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup`). For a lattice `L` this is the
covering of the torus `E / L` by `E`.

For a discrete subgroup `N` of a topological group `G`, the native coset projection
`G → G ⧸ N` is a local homeomorphism, by Mathlib's `Subgroup.isQuotientCoveringMap`.
Neither normality nor a separation axiom is needed.

## Main results

* `Subgroup.isLocalHomeomorph_quotientMk`, `AddSubgroup.isLocalHomeomorph_quotientMk`: the coset
  projection by a discrete subgroup is a local homeomorphism.
* `IsCoveringMap.isOpenQuotientMap`: a surjective covering map is an open quotient map.
* `IsQuotientCoveringMap.isCoveringMap_of_comp`: the map from the quotient by a subgroup down to
  the quotient by the whole group is a covering map.
* `IsQuotientCoveringMap.finite_fiber`, `IsAddQuotientCoveringMap.finite_fiber`: the quotient
  covering map of a finite group has finite fibres.
* `IsQuotientCoveringMap.compactSpace`, `IsAddQuotientCoveringMap.compactSpace`: the covering
  space of a finite-group quotient covering over a compact base is compact.
* `IsQuotientCoveringMap.natCard_fiber`: every fibre of the quotient covering map has as many
  points as the acting group.
* `IsQuotientCoveringMap.image_smul_set`: the quotient covering map has the same image on a set
  and on its translates.
* `IsQuotientCoveringMap.injOn_of_disjoint`, `IsQuotientCoveringMap.injOn_smul`: the quotient
  covering map is injective on a set disjoint from its nontrivial translates, and injectivity on a
  set passes to its translates.
* `IsQuotientCoveringMap.mapsTo_smul_preimage`: the preimage of a set under the quotient covering
  map is invariant under the action.
* `IsQuotientCoveringMap.of_smul_eq`: a quotient covering map for `G` is one for any group
  isomorphic to `G` acting compatibly.
* `TauCeti.involutive_of_forall_eq_neg_one_smul`: for any action of `ℤˣ`, the action of `-1` is an
  involution.
* `IsQuotientCoveringMap.comp_eq_of_forall_eq_neg_one_smul`,
  `IsQuotientCoveringMap.ne_self_of_forall_eq_neg_one_smul`,
  `IsQuotientCoveringMap.eq_or_eq_of_forall_eq_neg_one_smul`: for a quotient cover by `ℤˣ`, the
  involution `e ↦ -1 • e` lies over the base, fixes no point, and exchanges the two points of each
  fibre.
* `IsQuotientCoveringMap.restrict`: the restriction of a quotient covering map to the full
  preimage of a subset of the base is a quotient covering map onto that subset.
* `AddSubgroup.isAddQuotientCoveringMap_quotientMk`: the orbit projection for translation by a
  discrete additive subgroup is a quotient covering map.

## Implementation notes

The sheets are produced by hand rather than by exhibiting `r` as a quotient covering map for some
group, because in general it is not one. The fibre of `r` over `q e` consists of the classes of
the points `g • e` for `g : G`, two of which agree exactly when `g` differs by an element of `H`;
the normalizer quotient `N_G(H) / H` acts on `E / H` over `X` by deck transformations of `r`, but
on that fibre it acts transitively only when `H` is normal in `G`. (Whether it exhausts the deck
transformations of `r` is a further question, needing connectedness hypotheses that are not
assumed here.)

So the construction goes through Mathlib's `IsOpen.trivializationDiscrete`, which turns a family
of pairwise disjoint sets on which the map is injective into a `Bundle.Trivialization`. The index
type of that family is the set of translate images itself, which makes the family injective and
its pairwise disjointness exactly the statement that two meeting translate images coincide.

## References

The `IsQuotientCoveringMap` interface this file is built on — the predicate itself, its
`disjoint` and `apply_eq_iff_mem_orbit` fields, and `IsQuotientCoveringMap.isOpenQuotientMap` —
is Junyan Xu's, in `Mathlib/Topology/Covering/Quotient.lean`.
-/

public section

/-- The native coset projection by a discrete subgroup of a topological group is a local
homeomorphism. Neither normality nor a separation axiom is needed. -/
@[to_additive /-- The native coset projection by a discrete additive subgroup of a topological
additive group is a local homeomorphism. Neither normality nor a separation axiom is needed. -/]
theorem Subgroup.isLocalHomeomorph_quotientMk {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [DiscreteTopology N] :
    IsLocalHomeomorph (QuotientGroup.mk (s := N)) :=
  (N.isQuotientCoveringMap (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance))
    |>.isLocalHomeomorph

namespace TauCeti

open Pointwise Topology

variable {E X Y : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace Y]
  {G : Type*} [Group G] [MulAction G E] {H : Subgroup G}
  {q : E → X} {qH : E → Y} {r : Y → X}

/-- A surjective covering map is an open quotient map. -/
theorem _root_.IsCoveringMap.isOpenQuotientMap {p : E → X} (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : IsOpenQuotientMap p :=
  .of_isOpenMap_isQuotientMap hp.isOpenMap (hp.isQuotientMap hsurj)

namespace IsQuotientCoveringMap

omit [TopologicalSpace E] [TopologicalSpace Y] in
/-- **When the `G`-translates of `U` are pairwise disjoint, two translates whose images in `Y` meet
have the same image.** So the sets `qH '' (g • U)` are pairwise equal or disjoint. This is a
statement about the fibres of `qH` alone: no topology enters. -/
private theorem image_smul_eq_image_smul_of_inter_nonempty
    (horbit : ∀ {e₁ e₂ : E}, qH e₁ = qH e₂ ↔ e₁ ∈ MulAction.orbit H e₂) {U : Set E}
    (hdisj : ∀ g : G, (g • U ∩ U).Nonempty → g = 1) {g g' : G}
    (hmeet : (qH '' (g • U) ∩ qH '' (g' • U)).Nonempty) :
    qH '' (g • U) = qH '' (g' • U) := by
  -- A point common to the two images is `qH (g • u) = qH (g' • u')` for some `u, u' ∈ U`.
  obtain ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, _, ⟨u', hu', rfl⟩, hww'⟩ := hmeet
  obtain ⟨⟨h, hh⟩, hhu'⟩ := horbit.mp hww'.symm
  -- `H` acts through the coercion to `G` — `MulAction.subgroup_smul_def` — so the orbit witness is
  -- an element of `G` fixing `qH`, and `hhu'` retypes to the ambient action.
  have hhu : h • (g' • u') = g • u := by simpa only [MulAction.subgroup_smul_def] using hhu'
  have hmap : ∀ e : E, qH (h • e) = qH e := fun e =>
    horbit.mpr ⟨⟨h, hh⟩, MulAction.subgroup_smul_def ⟨h, hh⟩ e⟩
  have hgg' : g = h * g' := eq_of_inv_mul_eq_one <| by
    refine hdisj _ ⟨u, Set.mem_smul_set.mpr ⟨u', hu', ?_⟩, hu⟩
    rw [mul_smul, mul_smul, hhu, inv_smul_smul]
  simp [hgg', mul_smul, ← Set.image_smul, Set.image_image, hmap]

/-- The quotient covering map has the same image on a set and on each of its translates. -/
theorem _root_.IsQuotientCoveringMap.image_smul_set (hq : IsQuotientCoveringMap q G) (g : G)
    (s : Set E) : q '' (g • s) = q '' s := by
  rw [← Set.image_smul, Set.image_image]
  simp_rw [hq.map_smul]

/-- A quotient covering map is injective on a set that is disjoint from its nontrivial
translates. -/
theorem _root_.IsQuotientCoveringMap.injOn_of_disjoint (hq : IsQuotientCoveringMap q G)
    {U : Set E} (hU : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) : Set.InjOn q U := by
  intro a ha b hb hab
  obtain ⟨k, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 hab
  obtain rfl := hU k ⟨_, ⟨b, hb, rfl⟩, ha⟩
  simp

/-- If a quotient covering map is injective on a set, then it is injective on every translate of
that set, since `q (g • x) = q x`. -/
theorem _root_.IsQuotientCoveringMap.injOn_smul (hq : IsQuotientCoveringMap q G) {S : Set E}
    (hS : Set.InjOn q S) (g : G) : Set.InjOn q (g • S) := by
  rw [← Set.image_smul]
  exact Set.InjOn.image_of_comp (by simpa [Function.comp_def, hq.map_smul] using hS)

/-- The preimage of a set under the quotient covering map is invariant under the action. -/
theorem _root_.IsQuotientCoveringMap.mapsTo_smul_preimage (hq : IsQuotientCoveringMap q G)
    (s : Set X) (g : G) : Set.MapsTo (g • ·) (q ⁻¹' s) (q ⁻¹' s) :=
  fun e he ↦ by rwa [Set.mem_preimage, hq.map_smul]

/-- **Openness in a quotient covering map is detected on a single translate.** A subset `W` of the
image of `U` is open as soon as the part of its preimage lying in `U` is open, because the whole
preimage is covered by the translates of that part. -/
theorem _root_.IsQuotientCoveringMap.isOpen_of_isOpen_preimage_inter
    (hq : IsQuotientCoveringMap q G) {U : Set E} {W : Set X} (hWU : W ⊆ q '' U)
    (h : IsOpen (q ⁻¹' W ∩ U)) : IsOpen W := by
  have : ContinuousConstSMul G E := hq.toContinuousConstSMul
  rw [← hq.toIsQuotientMap.isOpen_preimage]
  have hcover : q ⁻¹' W = ⋃ k : G, k • (q ⁻¹' W ∩ U) := by
    refine Set.Subset.antisymm (fun w hw => ?_) (Set.iUnion_subset fun k w hw => ?_)
    · obtain ⟨u, hu, hqu⟩ := hWU hw
      obtain ⟨m, hm⟩ := hq.apply_eq_iff_mem_orbit.mp hqu.symm
      refine Set.mem_iUnion.mpr ⟨m, Set.mem_smul_set.mpr ⟨u, ⟨?_, hu⟩, hm⟩⟩
      rw [Set.mem_preimage, hqu]
      exact hw
    · obtain ⟨w', ⟨hw', -⟩, rfl⟩ := Set.mem_smul_set.mp hw
      rw [Set.mem_preimage, hq.map_smul]
      exact hw'
  rw [hcover]
  exact isOpen_iUnion fun k => h.smul k

/-- Openness inside the base set `q '' U` is detected on any single sheet `qH '' (g • U)`: a subset
`W` of `q '' U` is open exactly when its preimage under `r`, cut down to that sheet, is open. -/
private theorem _root_.IsQuotientCoveringMap.isOpen_iff_isOpen_preimage_inter_image_smul
    (hq : IsQuotientCoveringMap q G)
    (hqH : IsQuotientCoveringMap qH H) (hr : r ∘ qH = q) (hrc : Continuous r) {U : Set E}
    (hUo : IsOpen U) (g : G) {W : Set X} (hWV : W ⊆ q '' U) :
    IsOpen W ↔ IsOpen (r ⁻¹' W ∩ qH '' (g • U)) := by
  have hrqH : ∀ y : E, r (qH y) = q y := congrFun hr
  have hcsG : ContinuousConstSMul G E := hq.toContinuousConstSMul
  have hsheet_open : IsOpen (qH '' (g • U)) := hqH.isOpenQuotientMap.isOpenMap _ (hUo.smul g)
  refine ⟨fun hW => (hW.preimage hrc).inter hsheet_open, fun hW => ?_⟩
  have hSopen : IsOpen (q ⁻¹' W ∩ g • U) := by
    have hpull : IsOpen (qH ⁻¹' (r ⁻¹' W ∩ qH '' (g • U))) := hW.preimage hqH.continuous
    have hinter : qH ⁻¹' (r ⁻¹' W ∩ qH '' (g • U)) ∩ g • U = q ⁻¹' W ∩ g • U := by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_preimage, hrqH]
      exact and_congr_left fun hw => and_iff_left ⟨w, hw, rfl⟩
    exact hinter ▸ hpull.inter (hUo.smul g)
  refine hq.isOpen_of_isOpen_preimage_inter (U := g • U) ?_ hSopen
  rwa [hq.image_smul_set]

/-- The evenly covered neighbourhood of `q e` cut out by a set `U` around `e` whose `G`-translates
are pairwise disjoint. Its sheets are the images in `Y` of the translates `g • U`. -/
private theorem isEvenlyCovered_of_smul_disjoint (hq : IsQuotientCoveringMap q G)
    (hqH : IsQuotientCoveringMap qH H) (hr : r ∘ qH = q) {U : Set E} (hUo : IsOpen U)
    (hdisj : ∀ g : G, (g • U ∩ U).Nonempty → g = 1) {e : E} (heU : e ∈ U) :
    IsEvenlyCovered r (q e) (r ⁻¹' {q e}) := by
  have hrqH : ∀ y : E, r (qH y) = q y := congrFun hr
  have hrc : Continuous r := by
    rw [hqH.toIsQuotientMap.continuous_iff, hr]
    exact hq.continuous
  have hVo : IsOpen (q '' U) := hq.isOpenQuotientMap.isOpenMap _ hUo
  let : TopologicalSpace {S : Set Y // ∃ g : G, S = qH '' (g • U)} := ⊥
  have : DiscreteTopology {S : Set Y // ∃ g : G, S = qH '' (g • U)} := ⟨rfl⟩
  have : Nonempty {S : Set Y // ∃ g : G, S = qH '' (g • U)} :=
    ⟨⟨qH '' ((1 : G) • U), 1, rfl⟩⟩
  have : Nonempty (X → Y) := ⟨fun _ => qH e⟩
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (IsEvenlyCovered.of_trivialization (f := r)
      (t := hVo.trivializationDiscrete
        (Subtype.val : {S : Set Y // ∃ g : G, S = qH '' (g • U)} → Set Y) (q '' U)
        ?_ ?_ ?_ ?_ ?_) ⟨e, heU, rfl⟩)
  · -- Openness inside the base set is detected on any single sheet.
    rintro ⟨S, g, rfl⟩ W hWV
    exact hq.isOpen_iff_isOpen_preimage_inter_image_smul hqH hr hrc hUo g hWV
  · -- The map is injective on each sheet.
    rintro ⟨S, g, rfl⟩ z hz z' hz' hzz'
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hz'
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hw
    obtain ⟨u', hu', rfl⟩ := Set.mem_smul_set.mp hw'
    rw [hrqH, hrqH, hq.map_smul, hq.map_smul] at hzz'
    obtain ⟨k, hk⟩ := hq.apply_eq_iff_mem_orbit.mp hzz'
    have hk1 : k • u' = u := hk
    rw [hdisj k ⟨u, Set.mem_smul_set.mpr ⟨u', hu', hk1⟩, hu⟩, one_smul] at hk1
    rw [hk1]
  · -- Each sheet surjects onto the base set.
    rintro ⟨S, g, rfl⟩ v ⟨u, hu, rfl⟩
    exact ⟨qH (g • u), ⟨g • u, Set.smul_mem_smul_set hu, rfl⟩, by rw [hrqH, hq.map_smul]⟩
  · -- Distinct sheets are disjoint.
    rintro ⟨S, g, rfl⟩ ⟨S', g', rfl⟩ hne
    by_contra hcon
    exact hne (Subtype.ext (image_smul_eq_image_smul_of_inter_nonempty
      hqH.apply_eq_iff_mem_orbit hdisj
      (Set.not_disjoint_iff_nonempty_inter.mp hcon)))
  · -- The sheets exhaust the preimage of the base set.
    intro z hz
    obtain ⟨w, rfl⟩ := hqH.surjective z
    rw [Set.mem_preimage, hrqH] at hz
    obtain ⟨u, hu, hqu⟩ := hz
    obtain ⟨k, hk⟩ := hq.apply_eq_iff_mem_orbit.mp hqu.symm
    exact Set.mem_iUnion.mpr
      ⟨⟨qH '' (k • U), k, rfl⟩, ⟨w, Set.mem_smul_set.mpr ⟨u, hu, hk⟩, rfl⟩⟩

/-- **An intermediate quotient of a quotient covering map is a covering map.**

If `q : E → X` presents `X` as the quotient of `E` by a group `G` in the sense of
`IsQuotientCoveringMap`, and `qH : E → Y` presents `Y` as the quotient of `E` by a subgroup `H`
of `G`, then the map `r : Y → X` through which `q` factors is a covering map. -/
theorem _root_.IsQuotientCoveringMap.isCoveringMap_of_comp (hq : IsQuotientCoveringMap q G)
    (hqH : IsQuotientCoveringMap qH H) (hr : r ∘ qH = q) : IsCoveringMap r := by
  intro x
  obtain ⟨e, rfl⟩ := hq.surjective x
  obtain ⟨U, hU, hdisj⟩ := hq.disjoint e
  refine isEvenlyCovered_of_smul_disjoint hq hqH hr isOpen_interior (fun g hg => hdisj g ?_)
    (mem_interior_iff_mem_nhds.mpr hU)
  rw [← Set.image_smul] at hg
  exact Set.Nonempty.mono
    (Set.inter_subset_inter (Set.image_mono interior_subset) interior_subset) hg

end IsQuotientCoveringMap

/-- The fibres of the quotient covering map of a finite group are finite, each being an orbit of
the free action. -/
@[to_additive
/-- The fibres of the additive quotient covering map of a finite additive group are finite, each
being an orbit of the free action. -/]
theorem _root_.IsQuotientCoveringMap.finite_fiber [Finite G] (hq : IsQuotientCoveringMap q G)
    (x : X) : Finite ↥(q ⁻¹' {x}) := by
  obtain ⟨e, rfl⟩ := hq.surjective x
  exact Finite.of_equiv G (hq.fiberEquivGroup ⟨e, rfl⟩).symm

/-- Every fibre of the quotient covering map has as many points as the acting group, each fibre
being an orbit of the free action. -/
theorem _root_.IsQuotientCoveringMap.natCard_fiber (hq : IsQuotientCoveringMap q G) (x : X) :
    Nat.card ↥(q ⁻¹' {x}) = Nat.card G := by
  obtain ⟨e, rfl⟩ := hq.surjective x
  exact Nat.card_congr (hq.fiberEquivGroup ⟨e, rfl⟩)

/-- The covering space of a finite-group quotient covering over a compact base is compact. -/
@[to_additive
/-- The covering space of a finite additive group quotient covering over a compact base is
compact. -/]
theorem _root_.IsQuotientCoveringMap.compactSpace [CompactSpace X] [Finite G]
    (hq : IsQuotientCoveringMap q G) : CompactSpace E :=
  hq.isCoveringMap.compactSpace hq.finite_fiber

/-- **A quotient covering map stays one when the acting group is replaced by an isomorphic one
acting compatibly.** If `e : G ≃* G'` and each `e g` acts on `E` as `g` does, then the orbits and
the disjointness of translates are the same for both actions. -/
theorem _root_.IsQuotientCoveringMap.of_smul_eq {G' : Type*} [Group G'] [MulAction G' E]
    (hq : IsQuotientCoveringMap q G) (e : G ≃* G') (he : ∀ {g : G} {x : E}, e g • x = g • x) :
    IsQuotientCoveringMap q G' := by
  have he' (g' : G') (x : E) : g' • x = e.symm g' • x := by
    rw [← he, MulEquiv.apply_symm_apply]
  refine
    { toIsQuotientMap := hq.toIsQuotientMap
      continuous_const_smul g' := by
        simpa only [he'] using hq.continuous_const_smul (e.symm g')
      apply_eq_iff_mem_orbit := fun {e₁ e₂} ↦ ?_
      disjoint x := ?_ }
  · rw [hq.apply_eq_iff_mem_orbit]
    exact ⟨fun ⟨g, hg⟩ ↦ ⟨e g, he.trans hg⟩,
      fun ⟨g', hg'⟩ ↦ ⟨e.symm g', (he' g' e₂).symm.trans hg'⟩⟩
  · obtain ⟨U, hU, hdisj⟩ := hq.disjoint x
    refine ⟨U, hU, fun g' hg' ↦ ?_⟩
    simp only [he'] at hg'
    simpa using hdisj (e.symm g') hg'

/-! ### Quotient covers by `ℤˣ` -/

/-- For any action of `ℤˣ`, the action of `-1` is an involution. -/
theorem involutive_of_forall_eq_neg_one_smul {α : Type*} [MulAction ℤˣ α] {σ : α → α}
    (hσ : ∀ a, σ a = (-1 : ℤˣ) • a) : Function.Involutive σ := fun a ↦ by
  rw [hσ, hσ, smul_smul, neg_one_mul, neg_neg, one_smul]

section Units

variable [MulAction ℤˣ E] (hq : IsQuotientCoveringMap q ℤˣ) {σ : E → E}
  (hσ : ∀ e, σ e = (-1 : ℤˣ) • e)

include hq hσ

/-- The involution `e ↦ -1 • e` of a quotient cover by `ℤˣ` lies over the base. -/
theorem _root_.IsQuotientCoveringMap.comp_eq_of_forall_eq_neg_one_smul : q ∘ σ = q :=
  funext fun e ↦ (congrArg q (hσ e)).trans (hq.map_smul _)

/-- The involution `e ↦ -1 • e` of a quotient cover by `ℤˣ` fixes no point, the action being
free. -/
theorem _root_.IsQuotientCoveringMap.ne_self_of_forall_eq_neg_one_smul (e : E) : σ e ≠ e := by
  have := hq.isCancelSMul
  rw [hσ]
  intro h
  exact absurd (IsCancelSMul.right_cancel _ _ e (h.trans (one_smul ℤˣ e).symm)) (by decide)

/-- Two points of a quotient cover by `ℤˣ` with the same image are equal or exchanged by
`e ↦ -1 • e`. -/
theorem _root_.IsQuotientCoveringMap.eq_or_eq_of_forall_eq_neg_one_smul (e e' : E)
    (h : q e' = q e) : e' = e ∨ e' = σ e := by
  obtain ⟨u, rfl⟩ := hq.apply_eq_iff_mem_orbit.1 h
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact .inl (one_smul ℤˣ e)
  · exact .inr (hσ e).symm

end Units

/-- **A quotient covering map restricts to a quotient covering map over any subset.** Let `t` be
the full preimage `q ⁻¹' s` of a subset `s` of the base, given as a subset of `E` with
`Set.MapsTo q t s` and `q ⁻¹' s ⊆ t`, and let `G` act on `t` through its action on `E`. Then the
restriction `t → s` of `q` is the quotient covering map of the restricted action. -/
theorem _root_.IsQuotientCoveringMap.restrict (hq : IsQuotientCoveringMap q G) {t : Set E}
    {s : Set X} [MulAction G t] (hsmul : ∀ (g : G) (e : t), ((g • e : t) : E) = g • (e : E))
    (h : Set.MapsTo q t s) (ht : q ⁻¹' s ⊆ t) : IsQuotientCoveringMap (h.restrict q t s) G := by
  have := hq.toContinuousConstSMul
  -- The restriction is `Set.restrictPreimage`, once `t` is identified with `q ⁻¹' s`.
  obtain rfl : t = q ⁻¹' s := h.subset_preimage.antisymm ht
  refine (isQuotientCoveringMap_iff_isCoveringMap_and _ G).2
    ⟨hq.isCoveringMap.restrictPreimage s, s.restrictPreimage_surjective hq.surjective,
      ⟨fun g ↦ ?_⟩, isCancelSMul_iff_eq_one_of_smul_eq.2 fun g e he ↦ ?_, fun {e₁ e₂} ↦ ?_⟩
  · refine Topology.IsInducing.subtypeVal.continuous_iff.2 ?_
    simpa only [Function.comp_def, hsmul] using (continuous_const_smul g).comp continuous_subtypeVal
  · have := hq.isCancelSMul
    exact IsCancelSMul.eq_one_of_smul (x := e.val) (by rw [← hsmul, he])
  · simp only [Subtype.ext_iff, Set.MapsTo.val_restrict_apply, MulAction.mem_orbit_iff, hsmul]
    exact hq.apply_eq_iff_mem_orbit

end TauCeti

/-- The orbit projection `E → E / L` for translation by a discrete additive subgroup `L` of a
topological additive group is a quotient covering map for the translation action of `L`. -/
theorem AddSubgroup.isAddQuotientCoveringMap_quotientMk {E : Type*} [AddGroup E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (L : AddSubgroup E) [DiscreteTopology L] :
    IsAddQuotientCoveringMap (Quotient.mk (AddAction.orbitRel L E)) L :=
  isQuotientMap_quotient_mk'.isAddQuotientCoveringMap_of_addSubgroup L
    (isDiscrete_iff_discreteTopology.2 ‹_›) fun {_ _} ↦
      Quotient.eq.trans QuotientAddGroup.rightRel_apply

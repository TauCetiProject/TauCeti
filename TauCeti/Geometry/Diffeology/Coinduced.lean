/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Subduction

/-!
# Coinduced and quotient diffeologies

This file constructs the diffeology coinduced by an arbitrary map `q : X → Q` from a
diffeological space. A map from an open subset of a Cartesian space to `Q` is a plot precisely
when, near each point, it either lifts through `q` to a plot of `X` or is constant. This is the
finest diffeology making `q` smooth, and a function out of `Q` is diffeologically smooth exactly
when its composite with `q` is smooth.

When `q` is surjective, the constant case is subsumed by lifts, so the coinduced diffeology is the
quotient diffeology: its plots are the maps that locally lift through `q`. The surjection `q` is
then a subduction, and a diffeology on `Q` makes `q` a subduction exactly when it is the coinduced
diffeology.

The D-topology of the coinduced diffeology is the topology coinduced by `q` from the D-topology of
`X`. In particular, every subduction is a quotient map for the D-topologies, so a subduction that
is also a quotient map for given topologies carries compatibility of the topology with the
D-topology from its source to its target.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Articles 1.43--1.51, and Chapter 2 for the D-topology.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Q Y : Type*} [DiffeologicalSpace X]

/-! ### Local lifts or constants -/

/-- A map to the target locally lifts through a map or is locally constant on a subset if every
point has an open neighborhood in the subset on which the map either locally lifts or is
constant. -/
def LocallyLiftsOrConst (q : X → Q) {n : ℕ} (u : Set (𝔼ⁿ)) (p : 𝔼ⁿ → Q) : Prop :=
  ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ v ⊆ u ∧
    (LocallyLifts q v p ∨ ∃ y, EqOn p (fun _ ↦ y) v)

/-- A map locally lifts or is locally constant on a subset exactly when every point has an open
neighborhood in the subset on which the map either locally lifts or is constant. -/
theorem locallyLiftsOrConst_iff {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q} :
    LocallyLiftsOrConst q u p ↔ ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ v ⊆ u ∧
      (LocallyLifts q v p ∨ ∃ y, EqOn p (fun _ ↦ y) v) :=
  Iff.rfl

/-- Constant maps on an open set are local lifts or constants. -/
theorem locallyLiftsOrConst_const {n : ℕ} (q : X → Q) {u : Set (𝔼ⁿ)} (hu : IsOpen u) (y : Q) :
    LocallyLiftsOrConst q u (fun _ ↦ y) :=
  fun _ hz ↦ ⟨u, hu, hz, Subset.rfl, .inr ⟨y, eqOn_refl _ _⟩⟩

/-- Local lifts are local lifts or constants. -/
theorem LocallyLifts.locallyLiftsOrConst {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hp : LocallyLifts q u p) (hu : IsOpen u) : LocallyLiftsOrConst q u p :=
  fun _ hz ↦ ⟨u, hu, hz, Subset.rfl, .inl hp⟩

/-- Through a surjection, local lifts or constants on an open set are just local lifts. -/
theorem locallyLiftsOrConst_iff_locallyLifts {n : ℕ} {q : X → Q} (hq : Surjective q)
    {u : Set (𝔼ⁿ)} (hu : IsOpen u) {p : 𝔼ⁿ → Q} :
    LocallyLiftsOrConst q u p ↔ LocallyLifts q u p := by
  refine ⟨fun hp ↦ locallyLifts_of_locally hu fun z hz ↦ ?_, fun hp ↦ hp.locallyLiftsOrConst hu⟩
  obtain ⟨v, hv, hzv, -, hl | ⟨y, hy⟩⟩ := hp z hz
  · exact ⟨v, hv, hzv, hl⟩
  · obtain ⟨x, rfl⟩ := hq y
    exact ⟨v, hv, hzv, (locallyLifts_const q hv x).congr fun _ ha ↦ (hy ha).symm⟩

/-- Local lifts or constants depend only on the restriction of the map to its domain. -/
theorem LocallyLiftsOrConst.congr {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p p' : 𝔼ⁿ → Q}
    (hp : LocallyLiftsOrConst q u p) (hpp' : EqOn p p' u) : LocallyLiftsOrConst q u p' := by
  intro z hz
  obtain ⟨v, hv, hzv, hvu, h⟩ := hp z hz
  exact ⟨v, hv, hzv, hvu, h.imp (·.congr (hpp'.mono hvu))
    fun ⟨y, hy⟩ ↦ ⟨y, (hpp'.mono hvu).symm.trans hy⟩⟩

/-- Local lifts or constants are stable under smooth reparametrization on open subsets. -/
theorem LocallyLiftsOrConst.comp_contDiffOn {n m : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)}
    {v : Set (𝔼ᵐ)} {p : 𝔼ⁿ → Q} {f : 𝔼ᵐ → 𝔼ⁿ}
    (hp : LocallyLiftsOrConst q u p) (hv : IsOpen v) (hf : ContDiffOn ℝ ∞ f v)
    (hfu : MapsTo f v u) : LocallyLiftsOrConst q v (p ∘ f) := by
  intro z hz
  obtain ⟨w, hw, hfw, -, h⟩ := hp (f z) (hfu hz)
  have ha : IsOpen (v ∩ f ⁻¹' w) := hf.continuousOn.isOpen_inter_preimage hv hw
  have haw : MapsTo f (v ∩ f ⁻¹' w) w := fun _ hy ↦ hy.2
  exact ⟨v ∩ f ⁻¹' w, ha, ⟨hz, hfw⟩, inter_subset_left,
    h.imp (·.comp_contDiffOn ha (hf.mono inter_subset_left) haw)
      fun ⟨y, hy⟩ ↦ ⟨y, fun _ hx ↦ hy (haw hx)⟩⟩

/-- Locally holding local lifts or constants glue to local lifts or constants. -/
theorem locallyLiftsOrConst_of_locally {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hu : IsOpen u)
    (hp : ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ LocallyLiftsOrConst q v p) :
    LocallyLiftsOrConst q u p := by
  intro z hz
  obtain ⟨v, _, hzv, hpv⟩ := hp z hz
  obtain ⟨w, hw, hzw, -, h⟩ := hpv z hzv
  exact ⟨w ∩ u, hw.inter hu, ⟨hzw, hz⟩, inter_subset_right,
    h.imp (·.mono (hw.inter hu) inter_subset_left)
      fun ⟨y, hy⟩ ↦ ⟨y, hy.mono inter_subset_left⟩⟩

/-- Postcomposing both the map and the map lifted through with a function preserves local lifts
or constants. -/
theorem LocallyLiftsOrConst.comp_left {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hp : LocallyLiftsOrConst q u p) (f : Q → Y) :
    LocallyLiftsOrConst (f ∘ q) u (f ∘ p) := by
  intro z hz
  obtain ⟨v, hv, hzv, hvu, h⟩ := hp z hz
  exact ⟨v, hv, hzv, hvu, h.imp (·.comp_left f) fun ⟨y, hy⟩ ↦ ⟨f y, hy.comp_left (g := f)⟩⟩

/-- A map that locally lifts through a smooth map or is locally constant is a plot on its
domain. -/
theorem LocallyLiftsOrConst.isPlotOn [DiffeologicalSpace Q] {n : ℕ} {q : X → Q}
    {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q} (hp : LocallyLiftsOrConst q u p)
    (hq : _root_.Diffeology.DSmooth q) : IsPlotOn u p := by
  refine isPlotOn_of_locally fun z hz ↦ ?_
  obtain ⟨v, hv, hzv, _, h⟩ := hp z hz
  refine ⟨v, hv, hzv, h.elim (·.isPlotOn hq) fun ⟨y, hy⟩ ↦ ?_⟩
  exact (isPlotOn_const v y).congr hy.symm

/-! ### The coinduced diffeology -/

/-- The diffeology coinduced by a map. Its plots are the maps that, near each point, lift through
the map to plots of the source or are constant. This is the pushforward diffeology of
Iglesias-Zemmour, *Diffeology*, Article 1.43. -/
@[instance_reducible]
def coinducedDiffeology (q : X → Q) : DiffeologicalSpace Q :=
  DiffeologicalSpace.ofCorePlotsOn {
    isPlotOn := fun _ p ↦ LocallyLiftsOrConst q _ p
    isPlotOn_congr := fun _ _ _ h ↦ ⟨fun hp ↦ hp.congr h, fun hp ↦ hp.congr h.symm⟩
    isPlot_const := fun y ↦ locallyLiftsOrConst_const q isOpen_univ y
    isPlotOn_reparam := by
      intro n m u v hu hv p f h hp hf
      exact LocallyLiftsOrConst.comp_contDiffOn hp hv hf h
    locality := by
      intro n u hu p hp
      apply locallyLiftsOrConst_of_locally hu
      intro z hz
      obtain ⟨v, hv, hzv, hpv⟩ := hp z hz
      exact ⟨v, hv, hzv, hpv⟩ }

/-- A map is a plot of the coinduced diffeology exactly when, near each point, it lifts to a
source plot or is constant. -/
theorem isPlot_coinducedDiffeology_iff (q : X → Q) {n : ℕ} {p : 𝔼ⁿ → Q} :
    @_root_.Diffeology.IsPlot Q (coinducedDiffeology q) n p ↔ LocallyLiftsOrConst q univ p :=
  Iff.rfl

/-- For a surjection, a map is a plot of the coinduced diffeology exactly when it locally lifts
through the surjection. -/
theorem isPlot_coinducedDiffeology_iff_locallyLifts {q : X → Q} (hq : Surjective q) {n : ℕ}
    {p : 𝔼ⁿ → Q} :
    @_root_.Diffeology.IsPlot Q (coinducedDiffeology q) n p ↔ LocallyLifts q univ p :=
  (isPlot_coinducedDiffeology_iff q).trans (locallyLiftsOrConst_iff_locallyLifts hq isOpen_univ)

/-- A map is smooth for the diffeology it coinduces. -/
theorem dSmooth_coinducedDiffeology_rng (q : X → Q) :
    @_root_.Diffeology.DSmooth X Q inferInstance (coinducedDiffeology q) q := by
  intro n p hp
  rw [isPlot_coinducedDiffeology_iff]
  exact ((isPlotOn_of_isPlot hp univ).locallyLifts_comp q isOpen_univ).locallyLiftsOrConst
    isOpen_univ

/-- The coinduced diffeology is the finest diffeology making the map smooth. -/
theorem coinducedDiffeology_le_iff (q : X → Q) {d : DiffeologicalSpace Q} :
    coinducedDiffeology q ≤ d ↔ @_root_.Diffeology.DSmooth X Q inferInstance d q := by
  refine ⟨fun h n p hp ↦ DiffeologicalSpace.le_iff'.mp h n _
    (dSmooth_coinducedDiffeology_rng q n p hp), fun hq ↦ ?_⟩
  refine DiffeologicalSpace.le_iff'.mpr fun n p hp ↦ ?_
  exact (LocallyLiftsOrConst.isPlotOn ((isPlot_coinducedDiffeology_iff q).mp hp) hq).isPlot

/-- A function from a coinduced diffeology is smooth exactly when its composite with the map is
smooth. -/
theorem dSmooth_coinducedDiffeology_dom [DiffeologicalSpace Y] (q : X → Q) (f : Q → Y) :
    @_root_.Diffeology.DSmooth Q Y (coinducedDiffeology q) inferInstance f ↔
      _root_.Diffeology.DSmooth (f ∘ q) := by
  let := coinducedDiffeology q
  refine ⟨fun hf ↦ hf.comp (dSmooth_coinducedDiffeology_rng q), fun hf n p hp ↦ ?_⟩
  exact ((((isPlot_coinducedDiffeology_iff q).mp hp).comp_left f).isPlotOn hf).isPlot

/-! ### Quotient diffeologies -/

/-- A surjection, equipped with the diffeology it coinduces, is a subduction. -/
theorem isSubduction_coinducedDiffeology {q : X → Q} (hq : Surjective q) :
    @IsSubduction X Q inferInstance (coinducedDiffeology q) q := by
  let := coinducedDiffeology q
  exact ⟨hq, dSmooth_coinducedDiffeology_rng q,
    (isPlot_coinducedDiffeology_iff_locallyLifts hq).mp⟩

/-- A map is a subduction exactly when it is surjective and the target carries the coinduced
diffeology. -/
theorem isSubduction_iff_eq_coinducedDiffeology [d : DiffeologicalSpace Q] {q : X → Q} :
    IsSubduction q ↔ Surjective q ∧ d = coinducedDiffeology q := by
  refine ⟨fun h ↦ ⟨h.surjective, le_antisymm ?_ ((coinducedDiffeology_le_iff q).mpr h.dSmooth)⟩,
    fun ⟨hq, hd⟩ ↦ hd ▸ isSubduction_coinducedDiffeology hq⟩
  exact DiffeologicalSpace.le_iff'.mpr fun n p hp ↦
    (isPlot_coinducedDiffeology_iff_locallyLifts h.surjective).mpr (h.locallyLifts hp)

/-! ### D-topologies -/

/-- The D-topology of the coinduced diffeology is the topology coinduced from the D-topology of
the source. -/
theorem dTopology_coinducedDiffeology (q : X → Q) :
    @_root_.Diffeology.dTopology Q (coinducedDiffeology q) =
      TopologicalSpace.coinduced q _root_.Diffeology.dTopology := by
  let := coinducedDiffeology q
  ext s
  rw [isOpen_coinduced, _root_.Diffeology.isOpen_iff_preimages_plots,
    _root_.Diffeology.isOpen_iff_preimages_plots]
  refine ⟨fun hs n p hp ↦ hs n (q ∘ p) (dSmooth_coinducedDiffeology_rng q n p hp),
    fun hs n p hp ↦ isOpen_iff_forall_mem_open.mpr fun z hz ↦ ?_⟩
  obtain ⟨v, hv, hzv, -, hl | ⟨y, hy⟩⟩ := (isPlot_coinducedDiffeology_iff q).mp hp z (mem_univ z)
  · -- Near `z`, the plot is `q ∘ lift`, so its preimage of `s` is the preimage of `q ⁻¹' s`.
    obtain ⟨w, hw, hzw, -, lift, hlift, hq⟩ := locallyLifts_iff.mp hl z hzv
    let : TopologicalSpace X := _root_.Diffeology.dTopology
    refine ⟨w ∩ lift ⁻¹' (q ⁻¹' s), fun x hx ↦ ?_, (hlift.continuousOn hw).isOpen_inter_preimage hw
      (_root_.Diffeology.isOpen_iff_preimages_plots.mpr hs), hzw, ?_⟩
    · rw [mem_preimage, ← hq hx.1]
      exact hx.2
    · rw [mem_preimage, mem_preimage, ← comp_apply (f := q), hq hzw]
      exact hz
  · refine ⟨v, fun x hx ↦ ?_, hv, hzv⟩
    rw [mem_preimage, (hy hx).trans (hy hzv).symm]
    exact hz

/-- A subduction is a quotient map for the D-topologies. -/
theorem IsSubduction.isQuotientMap_dTopology [DiffeologicalSpace Q] {q : X → Q}
    (hq : IsSubduction q) :
    @Topology.IsQuotientMap X Q _root_.Diffeology.dTopology _root_.Diffeology.dTopology q := by
  obtain ⟨hs, hd⟩ := isSubduction_iff_eq_coinducedDiffeology.mp hq
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  let : TopologicalSpace Q := _root_.Diffeology.dTopology
  exact ⟨⟨hd ▸ dTopology_coinducedDiffeology q⟩, hs⟩

/-- If the topology of the source of a subduction is its D-topology and the subduction is a
quotient map for given topologies, then the topology of the target is its D-topology. -/
theorem IsSubduction.isDTopologyCompatible [TopologicalSpace X]
    [_root_.Diffeology.IsDTopologyCompatible X] [TopologicalSpace Q] [DiffeologicalSpace Q]
    {q : X → Q} (hq : IsSubduction q) (h : Topology.IsQuotientMap q) :
    _root_.Diffeology.IsDTopologyCompatible Q where
  dTop_eq := by
    obtain ⟨-, rfl⟩ := isSubduction_iff_eq_coinducedDiffeology.mp hq
    rw [dTopology_coinducedDiffeology, _root_.Diffeology.IsDTopologyCompatible.dTop_eq X,
      h.eq_coinduced]

end TauCeti.Diffeology

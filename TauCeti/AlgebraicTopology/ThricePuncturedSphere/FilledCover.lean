/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.CompactCore
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoodComponents
public import TauCeti.GroupTheory.Perm.OrbitCount.Basic
public import TauCeti.Topology.Covering.PuncturedDisc
public import TauCeti.Topology.PunctureFilling

import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Filling the punctures of a finite cover of the thrice-punctured sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Over the standard punctured
neighbourhood `D_q*` of each puncture `q ∈ {0, 1, ∞}`, every connected component `C` of
`p ⁻¹' D_q*` is a finite connected cover of a punctured disc, hence isomorphic over `D_q*` to the
power map `w ↦ w ^ e` on the punctured unit disc `𝔻*` for some `e ≠ 0`. The **filled cover**
`FilledCover p` adds one point to `E` for each such component, the centre of the disc
parametrising it: it is the puncture filling `TauCeti.PunctureFilling` of `E` along the
parametrisations `FilledCover.chart p i : 𝔻* → E` of the components `i`, one of which is chosen
for each component. Different choices differ by a rotation by an `e`-th root of unity
(`TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`).

The filled cover is a compact Hausdorff space containing `E` as an open dense subspace
(`TauCeti.PunctureFilling.isOpenEmbedding_incl`, `TauCeti.PunctureFilling.denseRange_incl`); it is
connected when `E` is (`TauCeti.PunctureFilling.connectedSpace`). When the fibre over `1/2` is
numbered, the added points are the cycles of the three permutations of the monodromy triple, so
there are `c(σ0) + c(σ1) + c(σinf)` of them, counting fixed points as cycles. This is the
topological space underlying the branched cover of the Riemann sphere attached to `p`.

## Main declarations

* `TauCeti.FilledCover.Index p`: the components of `p ⁻¹' D_q*`, for the three punctures `q`.
* `TauCeti.FilledCover.chart p i`: the chosen parametrisation of the component `i` by `𝔻*`, under
  which `p` is `w ↦ w ^ e` in the standard coordinate of `D_q*`
  (`TauCeti.FilledCover.exists_homeomorph_chart_eq`).
* `TauCeti.FilledCover p`: the cover `E` with the punctures of its components filled in.
* `TauCeti.FilledCover.t2Space`, `TauCeti.FilledCover.compactSpace`,
  `TauCeti.FilledCover.secondCountableTopology`: the filled cover is Hausdorff and compact, and
  second countable when `E` is.
* `TauCeti.FilledCover.indexEquiv`: the added points are the cycles of `σ0`, `σ1` and `σinf`.
* `TauCeti.FilledCover.card_range_center`: there are `c(σ0) + c(σ1) + c(σinf)` added points.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: filling the punctures of a finite unramified cover).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4.
-/

public section

noncomputable section

namespace TauCeti

open Filter Function Metric Set Topology ThricePuncturedSphere Equiv.Perm

/-- The punctured unit disc of `ℂ`, as a subtype. -/
local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

namespace FilledCover

/-- The points added when the punctures of `p` are filled in: the connected components of the
preimages `p ⁻¹' D_q*` of the standard punctured neighbourhoods of the three punctures `q`. -/
abbrev Index : Type _ :=
  Σ q : Puncture, ConnectedComponents (p ⁻¹' q.neighborhood)

/-- The connected component of `p ⁻¹' D_q*` indexed by `i = ⟨q, c⟩`, as a subset of
`p ⁻¹' D_q*`. -/
def component (i : Index p) : Set (p ⁻¹' i.1.neighborhood) :=
  ConnectedComponents.mk ⁻¹' {i.2}

@[simp]
theorem mem_component_iff {i : Index p} {y : p ⁻¹' i.1.neighborhood} :
    y ∈ component p i ↔ ConnectedComponents.mk y = i.2 :=
  Iff.rfl

/-- The **filling chart** of the component `i` of `p ⁻¹' D_q*`: a parametrisation `𝔻* → E` of
that component under which `p` is `w ↦ w ^ e` in the standard coordinate of `D_q*`, for some
`e ≠ 0`. One is chosen for each component. Such a parametrisation exists when `p` is a covering
map with finite fibres (`FilledCover.exists_homeomorph_chart_eq`); otherwise the chart is an
unspecified map. -/
def chart (i : Index p) : 𝔻* → E :=
  haveI : Nonempty (𝔻* → E) :=
    (ConnectedComponents.surjective_coe i.2).elim fun x _ ↦ ⟨fun _ ↦ x⟩
  Classical.epsilon fun φ ↦ ∃ (e : ℕ) (he : e ≠ 0) (h : component p i ≃ₜ 𝔻*),
    puncturedDiscPow he ∘ h =
        (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ∧
      φ = fun w ↦ ((h.symm w : p ⁻¹' i.1.neighborhood) : E)

end FilledCover

/-- The **filled cover** of a cover `p : E → ℂ ∖ {0, 1}`: the space `E` with one point added for
each connected component of the preimage `p ⁻¹' D_q*` of the standard punctured neighbourhood of
each puncture `q ∈ {0, 1, ∞}`, filling the puncture of that component along its filling chart
`FilledCover.chart p`. When `p` is a covering map with finite fibres, this is a compact Hausdorff
space containing `E` as an open dense subspace. -/
abbrev FilledCover : Type _ :=
  PunctureFilling (FilledCover.chart p)

namespace FilledCover

variable {p}

/-- The components of the preimage of a standard punctured neighbourhood are open and closed. -/
private theorem isClopen_component (hp : IsCoveringMap p) (i : Index p) :
    IsClopen (component p i) := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (p ⁻¹' i.1.neighborhood) :=
    (i.1.isOpen_neighborhood.preimage hp.continuous).locallyPathConnectedSpace
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe i.2
  rw [component, ← hx, connectedComponents_preimage_singleton]
  exact isClopen_connectedComponent

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- Each component of the preimage of a standard punctured neighbourhood is isomorphic over `𝔻*`
to a power map: it is a finite connected cover of the punctured disc. -/
private theorem exists_homeomorph_puncturedDiscPow (i : Index p) :
    ∃ (e : ℕ) (he : e ≠ 0) (h : component p i ≃ₜ 𝔻*),
      puncturedDiscPow he ∘ h =
        (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) := by
  let f := i.1.coord ∘ i.1.neighborhood.restrictPreimage p
  have hf : IsCoveringMap f := (hp.restrictPreimage _).homeomorph_comp i.1.coord
  -- The fibres of `f` are finite, being contained in fibres of `p`.
  have hffin (w : 𝔻*) : (f ⁻¹' {w}).Finite := by
    have := finite_fiber_of_finite_fiber hp hfin (i.1.coord.symm w : ThricePuncturedSphere)
    refine (Set.toFinite (p ⁻¹' {(i.1.coord.symm w : ThricePuncturedSphere)})).preimage
      Subtype.val_injective.injOn |>.subset fun z hz ↦ ?_
    exact congrArg Subtype.val (i.1.coord.eq_symm_apply.2 hz)
  have hcov : IsCoveringMap ((component p i).domRestrict f) :=
    hf.domRestrict_of_isClopen hffin (isClopen_component hp i)
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe i.2
  have : ConnectedSpace (component p i) := isConnected_iff_connectedSpace.1 <| by
    rw [component, ← hx, connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  have : Nonempty (component p i) := ⟨⟨x, hx⟩⟩
  have hfinC : Finite ((component p i).domRestrict f ⁻¹' {puncturedDiscBasepoint}) :=
    ((hffin _).preimage Subtype.val_injective.injOn).to_subtype
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  obtain ⟨y, hy⟩ := hcov.surjective puncturedDiscBasepoint
  have he : Nat.card ((component p i).domRestrict f ⁻¹' {puncturedDiscBasepoint}) ≠ 0 :=
    Nat.card_ne_zero.2 ⟨⟨⟨y, hy⟩⟩, hfinC⟩
  exact ⟨_, he, (hcov.exists_homeomorph_puncturedDiscPow_comp_eq_iff he _).2 rfl⟩

/-- **The filling charts.** The filling chart of the component `i` of `p ⁻¹' D_q*` is the inverse
of a homeomorphism `h` from that component onto `𝔻*` under which `p` becomes the power map
`w ↦ w ^ e`, for some `e ≠ 0`, in the standard coordinate `q.coord` of `D_q*`. -/
theorem exists_homeomorph_chart_eq (i : Index p) :
    ∃ (e : ℕ) (he : e ≠ 0) (h : component p i ≃ₜ 𝔻*),
      puncturedDiscPow he ∘ h =
          (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ∧
        chart p i = fun w ↦ ((h.symm w : p ⁻¹' i.1.neighborhood) : E) := by
  obtain ⟨e, he, h, hh⟩ := exists_homeomorph_puncturedDiscPow hp hfin i
  exact Classical.epsilon_spec (p := fun φ ↦ ∃ (e : ℕ) (he : e ≠ 0) (h : component p i ≃ₜ 𝔻*),
    puncturedDiscPow he ∘ h =
        (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ∧
      φ = fun w ↦ ((h.symm w : p ⁻¹' i.1.neighborhood) : E)) ⟨_, e, he, h, hh, rfl⟩

/-- In the standard coordinate of `D_q*`, the cover `p` is the power map `w ↦ w ^ e` along the
filling chart of each component over `q`, for some `e ≠ 0`. -/
theorem exists_coe_coord_chart_eq_pow (i : Index p) :
    ∃ e ≠ 0, ∀ w : 𝔻*, ∃ hw : p (chart p i w) ∈ i.1.neighborhood,
      ConnectedComponents.mk (⟨chart p i w, hw⟩ : p ⁻¹' i.1.neighborhood) = i.2 ∧
        (i.1.coord ⟨p (chart p i w), hw⟩ : ℂ) = (w : ℂ) ^ e := by
  obtain ⟨e, he, h, hh, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  refine ⟨e, he, fun w ↦ ?_⟩
  rw [hchart]
  refine ⟨(h.symm w : p ⁻¹' i.1.neighborhood).2, (h.symm w).2, ?_⟩
  have := congrArg Subtype.val (congr_fun hh (h.symm w))
  rw [comp_apply, Homeomorph.apply_symm_apply, coe_puncturedDiscPow_apply] at this
  exact this.symm

/-- The filling chart of the component `i` of `p ⁻¹' D_q*` parametrises exactly the points of
that component. -/
theorem range_chart (i : Index p) :
    range (chart p i) =
      {y | ∃ hy : p y ∈ i.1.neighborhood, ConnectedComponents.mk ⟨y, hy⟩ = i.2} := by
  obtain ⟨-, -, h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  ext y
  rw [hchart]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(h.symm w : p ⁻¹' i.1.neighborhood).2, (h.symm w).2⟩
  · rintro ⟨hy, hc⟩
    exact ⟨h ⟨⟨y, hy⟩, hc⟩, by simp⟩

/-- The filling charts are open embeddings. -/
theorem isOpenEmbedding_chart (i : Index p) : IsOpenEmbedding (chart p i) := by
  obtain ⟨-, -, h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  rw [hchart]
  exact (i.1.isOpen_neighborhood.preimage hp.continuous).isOpenEmbedding_subtypeVal.comp
    ((isClopen_component hp i).isOpen.isOpenEmbedding_subtypeVal.comp
      h.symm.isOpenEmbedding)

/-- Approaching the puncture of a filling chart, a point goes to infinity in `ℂ ∖ {0, 1}`. -/
private theorem tendsto_comp_chart_cocompact (i : Index p) :
    Tendsto (p ∘ chart p i) (comap (↑) (𝓝 (0 : ℂ))) (cocompact ThricePuncturedSphere) := by
  obtain ⟨e, he, hpow⟩ := exists_coe_coord_chart_eq_pow hp hfin i
  refine ThricePuncturedSphere.hasBasis_cocompact.tendsto_right_iff.2 fun ρ hρ ↦ ?_
  set ρ' := min ρ (1 / 2)
  have hρ' : 0 < ρ' := lt_min hρ one_half_pos
  filter_upwards [preimage_mem_comap (ball_mem_nhds (0 : ℂ) (mul_pos two_pos hρ'))] with w hw
  obtain ⟨hw', -, hcoord⟩ := hpow w
  intro hcore
  have h2ρ := (i.1.mem_compactCore_iff hρ' (min_le_right _ _) hw').1
    (compactCore_subset_compactCore hρ' (min_le_left _ _) hcore)
  rw [hcoord, norm_pow] at h2ρ
  rw [mem_preimage, mem_ball_zero_iff] at hw
  have hle : ‖(w : ℂ)‖ ^ e ≤ ‖(w : ℂ)‖ :=
    pow_le_of_le_one (norm_nonneg _) (mem_ball_zero_iff.1 w.2.1).le he
  linarith

/-- The filling charts of distinct components have disjoint ranges. -/
private theorem disjoint_range_chart {i j : Index p} (hij : i ≠ j) :
    Disjoint (range (chart p i)) (range (chart p j)) := by
  rw [range_chart hp hfin, range_chart hp hfin, Set.disjoint_left]
  rintro y ⟨hyi, hci⟩ ⟨hyj, hcj⟩
  obtain ⟨q, c⟩ := i
  obtain ⟨q', c'⟩ := j
  obtain rfl | hq := eq_or_ne q q'
  · exact hij (congrArg (Sigma.mk q) (hci.symm.trans hcj))
  · exact Set.disjoint_left.1 (Puncture.pairwise_disjoint_neighborhood hq) hyi hyj

/-- **The filled cover is Hausdorff.** -/
theorem t2Space : T2Space (FilledCover p) := by
  -- The total space of a cover of a Hausdorff space is Hausdorff.
  have : T2Space E := by
    rw [t2Space_iff_disjoint_nhds]
    intro x y hxy
    by_cases h : p x = p y
    · exact isSeparatedMap_iff_disjoint_nhds.1 hp.isSeparatedMap x y h hxy
    · exact disjoint_of_map ((disjoint_nhds_nhds.2 h).mono (hp.continuous.tendsto x)
        (hp.continuous.tendsto y))
  have : LocallyCompactSpace ThricePuncturedSphere := isOpenEmbedding_coe.locallyCompactSpace
  refine PunctureFilling.t2Space (isOpenEmbedding_chart hp hfin) (fun i x ↦ ?_) fun i j hij ↦ ?_
  · -- A point of `E` lies over a point of `ℂ ∖ {0, 1}`, while the ends of the charts go to
    -- infinity there.
    refine disjoint_of_map (f := p) ?_
    rw [map_map]
    exact (disjoint_nhds_cocompact (p x)).mono (hp.continuous.tendsto x)
      (tendsto_comp_chart_cocompact hp hfin i)
  · exact disjoint_of_disjoint_of_mem (disjoint_range_chart hp hfin hij) range_mem_map
      range_mem_map

omit hfin in
/-- **The added points are the cycles of the monodromy.** For a cover whose fibre over `1/2` is
numbered by `ν`, the components of `p ⁻¹' D_q*` over the punctures `0`, `1` and `∞`, which are
the points added in `FilledCover p`, are the cycles of `σ0`, `σ1` and `σinf` respectively
(`IsCoveringMap.sameCycleQuotientσ0EquivConnectedComponents` and its analogues). -/
def indexEquiv {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) :
    Index p ≃ Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ0) ⊕
      Quotient (SameCycle.setoid (hp.monodromyTriple ν).σ1) ⊕
        Quotient (SameCycle.setoid (hp.monodromyTriple ν).σinf) where
  toFun
    | ⟨.zero, c⟩ => .inl ((hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm c)
    | ⟨.one, c⟩ => .inr (.inl ((hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm c))
    | ⟨.inf, c⟩ => .inr (.inr ((hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm c))
  invFun
    | .inl a => ⟨.zero, hp.sameCycleQuotientσ0EquivConnectedComponents ν a⟩
    | .inr (.inl a) => ⟨.one, hp.sameCycleQuotientσ1EquivConnectedComponents ν a⟩
    | .inr (.inr a) => ⟨.inf, hp.sameCycleQuotientσinfEquivConnectedComponents ν a⟩
  left_inv := by
    rintro ⟨_ | _ | _, c⟩ <;> exact congrArg (Sigma.mk _) (Equiv.apply_symm_apply _ c)
  right_inv := by rintro (a | a | a) <;> simp

omit hfin in
@[simp]
theorem indexEquiv_symm_inl {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inl a) = ⟨.zero, hp.sameCycleQuotientσ0EquivConnectedComponents ν a⟩ :=
  (rfl)

omit hfin in
@[simp]
theorem indexEquiv_symm_inr_inl {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inr (.inl a)) =
      ⟨.one, hp.sameCycleQuotientσ1EquivConnectedComponents ν a⟩ :=
  (rfl)

omit hfin in
@[simp]
theorem indexEquiv_symm_inr_inr {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (a) :
    (indexEquiv hp ν).symm (.inr (.inr a)) =
      ⟨.inf, hp.sameCycleQuotientσinfEquivConnectedComponents ν a⟩ :=
  (rfl)

/-- A finite cover has finitely many components over the three punctured neighbourhoods. -/
private theorem finite_index : Finite (Index p) := by
  have := finite_fiber_of_finite_fiber hp hfin basePt
  exact Finite.of_equiv _ (indexEquiv hp (Finite.equivFin _)).symm

/-- **The filled cover is compact**: outside the images of the discs of radius `1 / 2` under the
filling charts, a finite cover lies over a compact core of `ℂ ∖ {0, 1}`. -/
theorem compactSpace : CompactSpace (FilledCover p) := by
  have := finite_index hp hfin
  refine PunctureFilling.compactSpace (r := 1 / 2) (by norm_num) ?_
  choose e he hpow using exists_coe_coord_chart_eq_pow hp hfin
  have hK : IsCompact (p ⁻¹' compactCore (1 / 2) ∪ ⋃ i, p ⁻¹' compactCore ((1 / 2) ^ e i / 2)) :=
    (hp.isCompact_preimage_compactCore hfin _).union
      (isCompact_iUnion fun _ ↦ hp.isCompact_preimage_compactCore hfin _)
  refine hK.of_isClosed_subset (isOpen_iUnion fun i ↦ (isOpenEmbedding_chart hp hfin i).isOpenMap _
    (isOpen_lt continuous_subtype_val.norm continuous_const)).isClosed_compl fun y hy ↦ ?_
  by_cases hD : ∃ q : Puncture, p y ∈ q.neighborhood
  · -- A point over the punctured neighbourhood of `q` is in the range of the chart of its
    -- component, at a point of norm at least `1 / 2`.
    obtain ⟨q, hq⟩ := hD
    let i : Index p := ⟨q, ConnectedComponents.mk ⟨y, hq⟩⟩
    obtain ⟨w, hwy⟩ : y ∈ range (chart p i) := by
      rw [range_chart hp hfin]
      exact ⟨hq, rfl⟩
    have hwr : 1 / 2 ≤ ‖(w : ℂ)‖ := not_lt.1 fun h ↦ hy (mem_iUnion.2 ⟨i, w, h, hwy⟩)
    obtain ⟨hw, -, hcoord⟩ := hpow i w
    refine Or.inr (mem_iUnion.2 ⟨i, ?_⟩)
    have hpos : (0 : ℝ) < (1 / 2) ^ e i / 2 := by positivity
    have hle : (1 / 2 : ℝ) ^ e i / 2 ≤ 1 / 2 := by
      have := pow_le_one₀ (n := e i) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      linarith
    rw [mem_preimage, ← hwy, i.1.mem_compactCore_iff hpos hle hw, hcoord, norm_pow]
    linarith [pow_le_pow_left₀ (by norm_num) hwr (e i)]
  · -- A point over none of the three punctured neighbourhoods lies over the compact core of
    -- radius `1 / 2`.
    rw [not_exists] at hD
    refine Or.inl ?_
    rw [mem_preimage, compactCore_one_half, mem_compl_iff, mem_union, mem_union, not_or, not_or]
    exact ⟨⟨hD .zero, hD .one⟩, hD .inf⟩

/-- **The filled cover of a second-countable cover is second countable.** -/
theorem secondCountableTopology [SecondCountableTopology E] :
    SecondCountableTopology (FilledCover p) :=
  have := finite_index hp hfin
  PunctureFilling.secondCountableTopology (isOpenEmbedding_chart hp hfin)

omit hfin in
/-- **The number of added points.** For a cover whose fibre over `1/2` is numbered by `ν`, the
filled cover has `c(σ0) + c(σ1) + c(σinf)` added points, where `c(σ)` is the number of cycles of
`σ`, fixed points included. -/
theorem card_range_center {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) :
    Nat.card (range (PunctureFilling.center (chart p))) =
      orbitCount (hp.monodromyTriple ν).σ0 + orbitCount (hp.monodromyTriple ν).σ1 +
        orbitCount (hp.monodromyTriple ν).σinf := by
  rw [← Nat.card_congr (Equiv.ofInjective _ PunctureFilling.center_injective),
    Nat.card_congr (indexEquiv hp ν), Nat.card_sum, Nat.card_sum, add_assoc, orbitCount_def,
    orbitCount_def, orbitCount_def]

end FilledCover

end TauCeti

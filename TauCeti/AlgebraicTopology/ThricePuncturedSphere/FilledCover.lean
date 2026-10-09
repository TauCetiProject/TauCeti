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

import TauCeti.AlgebraicTopology.ThricePuncturedSphere.ComponentCharts
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.IsLocalHomeomorph
import TauCeti.Topology.SeparatedMap

/-!
# Filling the punctures of a finite cover of the thrice-punctured sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Over the standard punctured
neighbourhood `D_q*` of each puncture `q ∈ {0, 1, ∞}`, every connected component `C` of
`p ⁻¹' D_q*` is a finite connected cover of a punctured disc, hence isomorphic over `D_q*` to the
power map `w ↦ w ^ e` on the punctured unit disc `𝔻*`, where `e ≠ 0` is the local degree
`FilledCover.degree p i` of the component. The **filled cover**
`FilledCover p` adds one point to `E` for each such component, the centre of the disc
parametrising it: it is the puncture filling `TauCeti.PunctureFilling` of `E` along the
parametrisations `FilledCover.chart p i : 𝔻* → E` of the components `i`, one of which is chosen
for each component. Different choices differ by a rotation by an `e`-th root of unity
(`TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`).

The filled cover is a compact Hausdorff space containing `E` as an open dense subspace
(`TauCeti.PunctureFilling.isOpenEmbedding_incl`, `TauCeti.PunctureFilling.denseRange_incl`); it is
connected when `E` is (`TauCeti.PunctureFilling.connectedSpace`). When the fibre over `1/2` is
numbered, the added points are the cycles of the three permutations of the monodromy triple, so
there are `c(σ0) + c(σ1) + c(σinf)` of them, counting fixed points as cycles, and the local degree
of each component is the length of its cycle. This is the
topological space underlying the branched cover of the Riemann sphere attached to `p`.

## Main declarations

* `TauCeti.FilledCover.Index p`: the components of `p ⁻¹' D_q*`, for the three punctures `q`.
* `TauCeti.FilledCover.degree p i`: the local degree of the component `i`.
* `TauCeti.FilledCover.chart p i`: the chosen parametrisation of the component `i` by `𝔻*`, under
  which `p` is `w ↦ w ^ degree p i` in the standard coordinate of `D_q*`
  (`TauCeti.FilledCover.exists_homeomorph_chart_eq`).
* `TauCeti.FilledCover p`: the cover `E` with the punctures of its components filled in.
* `TauCeti.FilledCover.t2Space`, `TauCeti.FilledCover.compactSpace`,
  `TauCeti.FilledCover.secondCountableTopology`: the filled cover is Hausdorff and compact, and
  second countable when `E` is.
* `TauCeti.FilledCover.finite_index`: a finite cover has finitely many added points.
* `TauCeti.FilledCover.indexEquiv`: the added points are the cycles of `σ0`, `σ1` and `σinf`.
* `TauCeti.FilledCover.degree_indexEquiv_symm_inl`,
  `TauCeti.FilledCover.degree_indexEquiv_symm_inr_inl`,
  `TauCeti.FilledCover.degree_indexEquiv_symm_inr_inr`: the local degree of the component of a
  cycle is its length.
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

/-- The **local degree** of the component `i` of `p ⁻¹' D_q*`: the number of its points over the
basepoint of `𝔻*` in the standard coordinate of `D_q*`. When `p` is a covering map with finite
fibres, it is nonzero (`FilledCover.degree_ne_zero`), `p` is `w ↦ w ^ degree p i` along the
filling chart (`FilledCover.exists_homeomorph_chart_eq`), and it is the length of the cycle of the
monodromy labelling `i` (`FilledCover.degree_indexEquiv_symm_inl` and its analogues). -/
def degree (i : Index p) : ℕ :=
  Nat.card ((component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ⁻¹'
    {puncturedDiscBasepoint})

/-- `φ` parametrises the component `i` of `p ⁻¹' D_q*` by `𝔻*`, with `p` becoming the power map
`w ↦ w ^ degree p i` in the standard coordinate of `D_q*`. -/
private def IsFillingChart (i : Index p) (φ : 𝔻* → E) : Prop :=
  ∃ (he : degree p i ≠ 0) (h : component p i ≃ₜ 𝔻*),
    puncturedDiscPow he ∘ h =
        (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ∧
      φ = fun w ↦ ((h.symm w : p ⁻¹' i.1.neighborhood) : E)

/-- The **filling chart** of the component `i` of `p ⁻¹' D_q*`: a parametrisation `𝔻* → E` of
that component under which `p` is `w ↦ w ^ degree p i` in the standard coordinate of `D_q*`. One
is chosen for each component. Such a parametrisation exists when `p` is a covering map with finite
fibres (`FilledCover.exists_homeomorph_chart_eq`); otherwise the chart is an unspecified map. -/
def chart (i : Index p) : 𝔻* → E :=
  haveI : Nonempty (𝔻* → E) :=
    (ConnectedComponents.surjective_coe i.2).elim fun x _ ↦ ⟨fun _ ↦ x⟩
  Classical.epsilon (IsFillingChart p i)

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

/-- Each component of the preimage of a standard punctured neighbourhood is the connected
component of any of its points. -/
private theorem exists_component_eq (i : Index p) : ∃ x, component p i = connectedComponent x := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe i.2
  exact ⟨x, by rw [component, ← hx, connectedComponents_preimage_singleton]⟩

/-- The components of the preimage of a standard punctured neighbourhood are open and closed. -/
private theorem isClopen_component (hp : IsCoveringMap p) (i : Index p) :
    IsClopen (component p i) := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (p ⁻¹' i.1.neighborhood) :=
    (i.1.isOpen_neighborhood.preimage hp.continuous).locallyPathConnectedSpace
  obtain ⟨x, hx⟩ := exists_component_eq i
  rw [hx]
  exact isClopen_connectedComponent

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- Each component of the preimage of a standard punctured neighbourhood has a filling chart: it
is a finite connected cover of the punctured disc, so isomorphic over `𝔻*` to a power map. -/
private theorem exists_isFillingChart (i : Index p) : ∃ φ, IsFillingChart p i φ := by
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
  obtain ⟨x, hx⟩ := exists_component_eq i
  have : ConnectedSpace (component p i) := isConnected_iff_connectedSpace.1 <| by
    rw [hx]
    exact isConnected_connectedComponent
  have : Nonempty (component p i) := ⟨⟨x, hx ▸ mem_connectedComponent⟩⟩
  have hfinC : Finite ((component p i).domRestrict f ⁻¹' {puncturedDiscBasepoint}) :=
    ((hffin _).preimage Subtype.val_injective.injOn).to_subtype
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) one_pos
  obtain ⟨y, hy⟩ := hcov.surjective puncturedDiscBasepoint
  have he : degree p i ≠ 0 := Nat.card_ne_zero.2 ⟨⟨⟨y, hy⟩⟩, hfinC⟩
  obtain ⟨h, hh⟩ := (hcov.exists_homeomorph_puncturedDiscPow_comp_eq_iff he _).2 rfl
  exact ⟨_, he, h, hh, rfl⟩

/-- The local degree of each component of the preimage of a standard punctured neighbourhood is
nonzero. -/
theorem degree_ne_zero (i : Index p) : degree p i ≠ 0 := by
  obtain ⟨_, he, -⟩ := exists_isFillingChart hp hfin i
  exact he

/-- **The filling charts.** The filling chart of the component `i` of `p ⁻¹' D_q*` is the inverse
of a homeomorphism `h` from that component onto `𝔻*` under which `p` becomes the power map
`w ↦ w ^ degree p i` in the standard coordinate `q.coord` of `D_q*`. -/
theorem exists_homeomorph_chart_eq (i : Index p) :
    ∃ h : component p i ≃ₜ 𝔻*,
      puncturedDiscPow (degree_ne_zero hp hfin i) ∘ h =
          (component p i).domRestrict (i.1.coord ∘ i.1.neighborhood.restrictPreimage p) ∧
        chart p i = fun w ↦ ((h.symm w : p ⁻¹' i.1.neighborhood) : E) := by
  obtain ⟨_, h, hh, hchart⟩ := Classical.epsilon_spec (exists_isFillingChart hp hfin i)
  exact ⟨h, hh, hchart⟩

/-- In the standard coordinate of `D_q*`, the cover `p` is the power map `w ↦ w ^ degree p i`
along the filling chart of each component `i` over `q`. -/
theorem exists_coe_coord_chart_eq_pow (i : Index p) (w : 𝔻*) :
    ∃ hw : p (chart p i w) ∈ i.1.neighborhood,
      ConnectedComponents.mk (⟨chart p i w, hw⟩ : p ⁻¹' i.1.neighborhood) = i.2 ∧
        (i.1.coord ⟨p (chart p i w), hw⟩ : ℂ) = (w : ℂ) ^ degree p i := by
  obtain ⟨h, hh, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
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
  obtain ⟨h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  ext y
  rw [hchart]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(h.symm w : p ⁻¹' i.1.neighborhood).2, (h.symm w).2⟩
  · rintro ⟨hy, hc⟩
    exact ⟨h ⟨⟨y, hy⟩, hc⟩, by simp⟩

/-- The filling charts are open embeddings. -/
theorem isOpenEmbedding_chart (i : Index p) : IsOpenEmbedding (chart p i) := by
  obtain ⟨h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  rw [hchart]
  exact (i.1.isOpen_neighborhood.preimage hp.continuous).isOpenEmbedding_subtypeVal.comp
    ((isClopen_component hp i).isOpen.isOpenEmbedding_subtypeVal.comp
      h.symm.isOpenEmbedding)

/-- Approaching the puncture of a filling chart, a point goes to infinity in `ℂ ∖ {0, 1}`. -/
private theorem tendsto_comp_chart_cocompact (i : Index p) :
    Tendsto (p ∘ chart p i) (comap (↑) (𝓝 (0 : ℂ))) (cocompact ThricePuncturedSphere) := by
  refine ThricePuncturedSphere.hasBasis_cocompact.tendsto_right_iff.2 fun ρ hρ ↦ ?_
  filter_upwards [preimage_mem_comap (ball_mem_nhds (0 : ℂ) (mul_pos two_pos hρ))] with w hw
  obtain ⟨hw', -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  intro hcore
  have h2ρ := (i.1.mem_compactCore_iff hρ hw').1 hcore
  rw [hcoord, norm_pow] at h2ρ
  rw [mem_preimage, mem_ball_zero_iff] at hw
  have hle : ‖(w : ℂ)‖ ^ degree p i ≤ ‖(w : ℂ)‖ :=
    pow_le_of_le_one (norm_nonneg _) (mem_ball_zero_iff.1 w.2.1).le (degree_ne_zero hp hfin i)
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
  have : T2Space E := hp.isSeparatedMap.t2Space hp.continuous
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
theorem indexEquiv_zero {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν ⟨.zero, c⟩ = .inl ((hp.sameCycleQuotientσ0EquivConnectedComponents ν).symm c) :=
  (rfl)

omit hfin in
@[simp]
theorem indexEquiv_one {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν ⟨.one, c⟩ =
      .inr (.inl ((hp.sameCycleQuotientσ1EquivConnectedComponents ν).symm c)) :=
  (rfl)

omit hfin in
@[simp]
theorem indexEquiv_inf {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (c) :
    indexEquiv hp ν ⟨.inf, c⟩ =
      .inr (.inr ((hp.sameCycleQuotientσinfEquivConnectedComponents ν).symm c)) :=
  (rfl)

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

omit hfin in
/-- **The local degree over `0` is the cycle length.** The component of `p ⁻¹' D₀*` labelled by
the cycle of the sheet `j` under `σ0` has local degree the length of that cycle. -/
theorem degree_indexEquiv_symm_inl {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p ((indexEquiv hp ν).symm (.inl (Quotient.mk _ j))) =
      minimalPeriod (hp.monodromyTriple ν).σ0 j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  rw [indexEquiv_symm_inl, hp.sameCycleQuotientσ0EquivConnectedComponents_mk]
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ0 ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_zero]
  exact (exists_homeomorph_chart_eq hp hfin ⟨.zero, _⟩).imp fun _ h ↦ h.1

omit hfin in
/-- **The local degree over `1` is the cycle length.** The component of `p ⁻¹' D₁*` labelled by
the cycle of the sheet `j` under `σ1` has local degree the length of that cycle. -/
theorem degree_indexEquiv_symm_inr_inl {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p ((indexEquiv hp ν).symm (.inr (.inl (Quotient.mk _ j)))) =
      minimalPeriod (hp.monodromyTriple ν).σ1 j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  rw [indexEquiv_symm_inr_inl, hp.sameCycleQuotientσ1EquivConnectedComponents_mk]
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ1 ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_one]
  exact (exists_homeomorph_chart_eq hp hfin ⟨.one, _⟩).imp fun _ h ↦ h.1

omit hfin in
/-- **The local degree over `∞` is the cycle length.** The component of `p ⁻¹' D∞*` labelled by
the cycle of the sheet `j` under `σinf` has local degree the length of that cycle. -/
theorem degree_indexEquiv_symm_inr_inr {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p ((indexEquiv hp ν).symm (.inr (.inr (Quotient.mk _ j)))) =
      minimalPeriod (hp.monodromyTriple ν).σinf j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  rw [indexEquiv_symm_inr_inr, hp.sameCycleQuotientσinfEquivConnectedComponents_mk]
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σinf ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_inf]
  exact (exists_homeomorph_chart_eq hp hfin ⟨.inf, _⟩).imp fun _ h ↦ h.1

/-- A finite cover has finitely many components over the three punctured neighbourhoods, so its
filled cover has finitely many added points. -/
theorem finite_index : Finite (Index p) := by
  have := finite_fiber_of_finite_fiber hp hfin basePt
  exact Finite.of_equiv _ (indexEquiv hp (Finite.equivFin _)).symm

/-- **The filled cover is compact**: outside the images of the discs of radius `1 / 2` under the
filling charts, a finite cover lies over a compact core of `ℂ ∖ {0, 1}`. -/
theorem compactSpace : CompactSpace (FilledCover p) := by
  have := finite_index hp hfin
  refine PunctureFilling.compactSpace (r := 1 / 2) (by norm_num) ?_
  have hK : IsCompact
      (p ⁻¹' compactCore (1 / 2) ∪ ⋃ i, p ⁻¹' compactCore ((1 / 2) ^ degree p i / 2)) :=
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
    obtain ⟨hw, -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
    refine Or.inr (mem_iUnion.2 ⟨i, ?_⟩)
    have hpos : (0 : ℝ) < (1 / 2) ^ degree p i / 2 := by positivity
    rw [mem_preimage, ← hwy, i.1.mem_compactCore_iff hpos hw, hcoord, norm_pow]
    linarith [pow_le_pow_left₀ (by norm_num) hwr (degree p i)]
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

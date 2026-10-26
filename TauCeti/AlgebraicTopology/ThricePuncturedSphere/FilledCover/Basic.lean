/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.CompactCore
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Points
public import TauCeti.Topology.Covering.PuncturedDisc
public import TauCeti.Topology.PunctureFilling

import TauCeti.AlgebraicTopology.ThricePuncturedSphere.ComponentCharts
import TauCeti.Topology.Covering.Clopen
import TauCeti.Topology.IsLocalHomeomorph
import TauCeti.Topology.SeparatedMap

import TauCeti.Analysis.Normed.Module.Connected

/-!
# Filling the punctures of a finite cover of the thrice-punctured sphere

Let `p : E → ℂ ∖ {0, 1}` be a covering map with finite fibres. Over the standard punctured
neighbourhood `D_q*` of each puncture `q ∈ {0, 1, ∞}`, every connected component `C` of
`p ⁻¹' D_q*` is a finite connected cover of a punctured disc, hence isomorphic over `D_q*` to the
power map `w ↦ w ^ e` on the punctured unit disc `𝔻*`, where `e ≠ 0` is the local degree
`FilledCover.degree p i` of the component. The **filled cover**
`FilledCover p` adds one point to `E` for each such component (these are the points
`TauCeti.FilledPoint p`), the centre of the disc parametrising it: it is the puncture filling
`TauCeti.PunctureFilling` of `E` along the parametrisations `FilledCover.chart p i : 𝔻* → E`
of the components `i`, one of which is chosen for each component. Different choices differ by a
rotation by an `e`-th root of unity (`TauCeti.existsUnique_rootsOfUnity_smul_homeomorph`).

The filled cover is a compact Hausdorff space containing `E` as an open dense subspace
(`TauCeti.PunctureFilling.isOpenEmbedding_incl`, `TauCeti.PunctureFilling.denseRange_incl`); it is
connected when `E` is (`TauCeti.PunctureFilling.connectedSpace`). When the fibre over `1/2` is
numbered, the added points are the cycles of the three permutations of the monodromy triple, so
there are `c(σ0) + c(σ1) + c(σinf)` of them, counting fixed points as cycles, and the local degree
of each component is the length of its cycle. This is the
topological space underlying the branched cover of the Riemann sphere attached to `p`.

## Main declarations

* `TauCeti.FilledPoint.sigmaEquiv p`: the added points `TauCeti.FilledPoint p`, the components of
  `p ⁻¹' D_q*`, as pairs of a puncture `q` and a component over it.
* `TauCeti.FilledCover.degree p i`: the local degree of the component `i`.
* `TauCeti.FilledCover.chart p i`: the chosen parametrisation of the component `i` by `𝔻*`, under
  which `p` is `w ↦ w ^ degree p i` in the standard coordinate of `D_q*`
  (`TauCeti.FilledCover.exists_homeomorph_chart_eq`).
* `TauCeti.FilledCover p`: the cover `E` with the punctures of its components filled in.
* `TauCeti.FilledCover.t2Space`, `TauCeti.FilledCover.compactSpace`,
  `TauCeti.FilledCover.secondCountableTopology`: the filled cover is Hausdorff and compact, and
  second countable when `E` is.
* `TauCeti.FilledCover.finite_filledPoint`: a finite cover has finitely many added points.
* `TauCeti.FilledCover.indexEquiv`: the added points are the cycles of `σ0`, `σ1` and `σinf`.
* `TauCeti.FilledCover.degree_overZero_mk_monodromy`,
  `TauCeti.FilledCover.degree_overOne_mk_monodromy`,
  `TauCeti.FilledCover.degree_overInf_mk_monodromy`: the local degree of the component of a
  cycle is its length.
* `TauCeti.FilledCover.natCard_range_center`: there are `c(σ0) + c(σ1) + c(σinf)` added points.

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

open FilledPoint

namespace FilledCover

/-- The connected component of `p ⁻¹' D_q*` giving the added point `i`, as a subset of
`p ⁻¹' D_q*`, where `q` is the puncture of `i`. -/
def component (i : FilledPoint p) : Set (p ⁻¹' (sigmaEquiv p i).1.neighborhood) :=
  ConnectedComponents.mk ⁻¹' {(sigmaEquiv p i).2}

@[simp]
theorem mem_component_iff {i : FilledPoint p} {y : p ⁻¹' (sigmaEquiv p i).1.neighborhood} :
    y ∈ component p i ↔ ConnectedComponents.mk y = (sigmaEquiv p i).2 :=
  Iff.rfl

/-- The **local degree** of the component `i` of `p ⁻¹' D_q*`: the number of its points over the
basepoint of `𝔻*` in the standard coordinate of `D_q*`. When `p` is a covering map with finite
fibres, it is nonzero (`FilledCover.degree_ne_zero`), `p` is `w ↦ w ^ degree p i` along the
filling chart (`FilledCover.exists_homeomorph_chart_eq`), and it is the length of the cycle of the
monodromy labelling `i` (`FilledCover.degree_overZero_mk_monodromy` and its analogues). -/
def degree (i : FilledPoint p) : ℕ :=
  Nat.card ((component p i).domRestrict
    ((sigmaEquiv p i).1.coord ∘ (sigmaEquiv p i).1.neighborhood.restrictPreimage p) ⁻¹'
      {puncturedDiscBasepoint})

/-- The local degree is the cardinality of the component fibre over the standard basepoint of
the punctured disc. -/
theorem degree_def (i : FilledPoint p) :
    degree p i = Nat.card ((component p i).domRestrict
      ((sigmaEquiv p i).1.coord ∘ (sigmaEquiv p i).1.neighborhood.restrictPreimage p) ⁻¹'
        {puncturedDiscBasepoint}) :=
  (rfl)

/-- `φ` parametrises the component `i` of `p ⁻¹' D_q*` by `𝔻*`, with `p` becoming the power map
`w ↦ w ^ degree p i` in the standard coordinate of `D_q*`. -/
private def IsFillingChart (i : FilledPoint p) (φ : 𝔻* → E) : Prop :=
  ∃ (he : degree p i ≠ 0) (h : component p i ≃ₜ 𝔻*),
    puncturedDiscPow he ∘ h =
        (component p i).domRestrict
          ((sigmaEquiv p i).1.coord ∘ (sigmaEquiv p i).1.neighborhood.restrictPreimage p) ∧
      φ = fun w ↦ ((h.symm w : p ⁻¹' (sigmaEquiv p i).1.neighborhood) : E)

/-- The **filling chart** of the component `i` of `p ⁻¹' D_q*`: a parametrisation `𝔻* → E` of
that component under which `p` is `w ↦ w ^ degree p i` in the standard coordinate of `D_q*`. One
is chosen for each component. Such a parametrisation exists when `p` is a covering map with finite
fibres (`FilledCover.exists_homeomorph_chart_eq`); otherwise the chart is an unspecified map. -/
def chart (i : FilledPoint p) : 𝔻* → E :=
  haveI : Nonempty (𝔻* → E) :=
    (ConnectedComponents.surjective_coe (sigmaEquiv p i).2).elim fun x _ ↦ ⟨fun _ ↦ x⟩
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
private theorem exists_component_eq (i : FilledPoint p) :
    ∃ x, component p i = connectedComponent x := by
  obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (sigmaEquiv p i).2
  exact ⟨x, by rw [component, ← hx, connectedComponents_preimage_singleton]⟩

/-- The components of the preimage of a standard punctured neighbourhood are open and closed. -/
private theorem isClopen_component (hp : IsCoveringMap p) (i : FilledPoint p) :
    IsClopen (component p i) := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace (p ⁻¹' (sigmaEquiv p i).1.neighborhood) :=
    ((sigmaEquiv p i).1.isOpen_neighborhood.preimage hp.continuous).locallyPathConnectedSpace
  obtain ⟨x, hx⟩ := exists_component_eq i
  rw [hx]
  exact isClopen_connectedComponent

variable (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- Each component of the preimage of a standard punctured neighbourhood has a filling chart: it
is a finite connected cover of the punctured disc, so isomorphic over `𝔻*` to a power map. -/
private theorem exists_isFillingChart (i : FilledPoint p) : ∃ φ, IsFillingChart p i φ := by
  let f := (sigmaEquiv p i).1.coord ∘ (sigmaEquiv p i).1.neighborhood.restrictPreimage p
  have hf : IsCoveringMap f := (hp.restrictPreimage _).homeomorph_comp (sigmaEquiv p i).1.coord
  -- The fibres of `f` are finite, being contained in fibres of `p`.
  have hffin (w : 𝔻*) : (f ⁻¹' {w}).Finite := by
    let z : ThricePuncturedSphere := (sigmaEquiv p i).1.coord.symm w
    have := finite_fiber_of_finite_fiber hp hfin z
    refine (Set.toFinite (p ⁻¹' {z})).preimage Subtype.val_injective.injOn |>.subset fun z hz ↦ ?_
    exact congrArg Subtype.val ((sigmaEquiv p i).1.coord.eq_symm_apply.2 hz)
  have hcov : IsCoveringMap ((component p i).domRestrict f) :=
    hf.domRestrict_of_isClopen hffin (isClopen_component hp i)
  obtain ⟨x, hx⟩ := exists_component_eq i
  have : ConnectedSpace (component p i) := isConnected_iff_connectedSpace.1 <| by
    rw [hx]
    exact isConnected_connectedComponent
  have : Nonempty (component p i) := ⟨⟨x, hx ▸ mem_connectedComponent⟩⟩
  have hfinC : Finite ((component p i).domRestrict f ⁻¹' {puncturedDiscBasepoint}) :=
    ((hffin _).preimage Subtype.val_injective.injOn).to_subtype
  have := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex])
      (0 : ℂ) one_pos)
  obtain ⟨y, hy⟩ := hcov.surjective puncturedDiscBasepoint
  have he : degree p i ≠ 0 := Nat.card_ne_zero.2 ⟨⟨⟨y, hy⟩⟩, hfinC⟩
  obtain ⟨h, hh⟩ := (hcov.exists_homeomorph_puncturedDiscPow_comp_eq_iff he _).2 rfl
  exact ⟨_, he, h, hh, rfl⟩

/-- The local degree of each component of the preimage of a standard punctured neighbourhood is
nonzero. -/
theorem degree_ne_zero (i : FilledPoint p) : degree p i ≠ 0 := by
  obtain ⟨_, he, -⟩ := exists_isFillingChart hp hfin i
  exact he

/-- **The filling charts.** The filling chart of the component `i` of `p ⁻¹' D_q*` is the inverse
of a homeomorphism `h` from that component onto `𝔻*` under which `p` becomes the power map
`w ↦ w ^ degree p i` in the standard coordinate `q.coord` of `D_q*`. -/
theorem exists_homeomorph_chart_eq (i : FilledPoint p) :
    ∃ h : component p i ≃ₜ 𝔻*,
      puncturedDiscPow (degree_ne_zero hp hfin i) ∘ h =
          (component p i).domRestrict
            ((sigmaEquiv p i).1.coord ∘ (sigmaEquiv p i).1.neighborhood.restrictPreimage p) ∧
        chart p i = fun w ↦ ((h.symm w : p ⁻¹' (sigmaEquiv p i).1.neighborhood) : E) := by
  obtain ⟨_, h, hh, hchart⟩ := Classical.epsilon_spec (exists_isFillingChart hp hfin i)
  exact ⟨h, hh, hchart⟩

/-- In the standard coordinate of `D_q*`, the cover `p` is the power map `w ↦ w ^ degree p i`
along the filling chart of each component `i` over `q`. -/
theorem exists_coe_coord_chart_eq_pow (i : FilledPoint p) (w : 𝔻*) :
    ∃ hw : p (chart p i w) ∈ (sigmaEquiv p i).1.neighborhood,
      ConnectedComponents.mk (⟨chart p i w, hw⟩ : p ⁻¹' (sigmaEquiv p i).1.neighborhood) =
          (sigmaEquiv p i).2 ∧
        ((sigmaEquiv p i).1.coord ⟨p (chart p i w), hw⟩ : ℂ) = (w : ℂ) ^ degree p i := by
  obtain ⟨h, hh, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  rw [hchart]
  refine ⟨(h.symm w : p ⁻¹' (sigmaEquiv p i).1.neighborhood).2, (h.symm w).2, ?_⟩
  have := congrArg Subtype.val (congr_fun hh (h.symm w))
  rw [comp_apply, Homeomorph.apply_symm_apply, coe_puncturedDiscPow_apply] at this
  exact this.symm

/-- The filling chart of the component `i` of `p ⁻¹' D_q*` parametrises exactly the points of
that component. -/
theorem range_chart (i : FilledPoint p) :
    range (chart p i) =
      {y | ∃ hy : p y ∈ (sigmaEquiv p i).1.neighborhood,
        ConnectedComponents.mk ⟨y, hy⟩ = (sigmaEquiv p i).2} := by
  obtain ⟨h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  ext y
  rw [hchart]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨(h.symm w : p ⁻¹' (sigmaEquiv p i).1.neighborhood).2, (h.symm w).2⟩
  · rintro ⟨hy, hc⟩
    exact ⟨h ⟨⟨y, hy⟩, hc⟩, by simp⟩

/-- The filling charts are open embeddings. -/
theorem isOpenEmbedding_chart (i : FilledPoint p) : IsOpenEmbedding (chart p i) := by
  obtain ⟨h, -, hchart⟩ := exists_homeomorph_chart_eq hp hfin i
  rw [hchart]
  exact ((sigmaEquiv p i).1.isOpen_neighborhood.preimage
    hp.continuous).isOpenEmbedding_subtypeVal.comp
      ((isClopen_component hp i).isOpen.isOpenEmbedding_subtypeVal.comp h.symm.isOpenEmbedding)

/-- Approaching the puncture of a filling chart, a point goes to infinity in `ℂ ∖ {0, 1}`. -/
private theorem tendsto_comp_chart_cocompact (i : FilledPoint p) :
    Tendsto (p ∘ chart p i) (comap (↑) (𝓝 (0 : ℂ))) (cocompact ThricePuncturedSphere) := by
  refine ThricePuncturedSphere.hasBasis_cocompact.tendsto_right_iff.2 fun ρ hρ ↦ ?_
  filter_upwards [preimage_mem_comap (ball_mem_nhds (0 : ℂ) (mul_pos two_pos hρ))] with w hw
  obtain ⟨hw', -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  intro hcore
  have h2ρ := ((sigmaEquiv p i).1.mem_compactCore_iff hρ hw').1 hcore
  rw [hcoord, norm_pow] at h2ρ
  rw [mem_preimage, mem_ball_zero_iff] at hw
  have hle : ‖(w : ℂ)‖ ^ degree p i ≤ ‖(w : ℂ)‖ :=
    pow_le_of_le_one (norm_nonneg _) (mem_ball_zero_iff.1 w.2.1).le (degree_ne_zero hp hfin i)
  linarith

/-- **The end of a filling chart.** Approaching the puncture of `𝔻*` along the filling chart of
the component `i` of `p ⁻¹' D_q*` is the same as going to infinity in `ℂ ∖ {0, 1}` within that
component: the image of the end of `𝔻*` is the filter of points of the component whose images
under `p` eventually leave every compact subset of `ℂ ∖ {0, 1}`. In particular, the end does not
depend on the chosen chart. -/
theorem map_chart_comap_nhds_zero (i : FilledPoint p) :
    map (chart p i) (comap (↑) (𝓝 (0 : ℂ))) =
      𝓟 (range (chart p i)) ⊓ comap p (cocompact ThricePuncturedSphere) := by
  refine le_antisymm (le_inf (le_principal_iff.2 range_mem_map) (map_le_iff_le_comap.1 ?_))
    fun S hS ↦ ?_
  · rw [map_map]
    exact tendsto_comp_chart_cocompact hp hfin i
  -- A point of the component outside the image of the disc of radius `r` lies over the compact
  -- core of radius `r ^ degree p i / 2`.
  obtain ⟨t, ht, hts⟩ := mem_comap.1 (mem_map.1 hS)
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 ht
  have hρ : 0 < r ^ degree p i / 2 := by positivity
  refine mem_inf_of_inter (mem_principal_self _)
    (preimage_mem_comap (hasBasis_cocompact.mem_of_mem hρ)) ?_
  rintro _ ⟨⟨w, rfl⟩, hw⟩
  refine hts (hrt (mem_ball_zero_iff.2 (not_le.1 fun hle ↦ hw ?_)))
  obtain ⟨hw', -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  rw [(sigmaEquiv p i).1.mem_compactCore_iff hρ hw', hcoord, norm_pow]
  linarith [pow_le_pow_left₀ hr.le hle (degree p i)]

/-- The filling charts of distinct components have disjoint ranges. -/
private theorem disjoint_range_chart {i j : FilledPoint p} (hij : i ≠ j) :
    Disjoint (range (chart p i)) (range (chart p j)) := by
  rw [range_chart hp hfin, range_chart hp hfin, Set.disjoint_left]
  rintro y ⟨hyi, hci⟩ ⟨hyj, hcj⟩
  replace hij := (sigmaEquiv p).injective.ne hij
  revert hyi hci hyj hcj hij
  generalize sigmaEquiv p i = a
  generalize sigmaEquiv p j = b
  rintro hyi hci hyj hcj hij
  obtain ⟨q, c⟩ := a
  obtain ⟨q', c'⟩ := b
  obtain rfl | hq := eq_or_ne q q'
  · exact hij (congrArg (Sigma.mk q) (hci.symm.trans hcj))
  · exact Set.disjoint_left.1 (Puncture.pairwise_disjoint_neighborhood hq) hyi hyj

/-- **The filled cover is Hausdorff.** -/
theorem t2Space : T2Space (FilledCover p) := by
  have : T2Space E := hp.t2Space
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
/-- **The local degree over `0` is the cycle length.** The component of `p ⁻¹' D₀*` containing the
endpoint of the lift of `αZero` from the sheet `ν.symm j` has local degree the length of the cycle
of `j` under `σ0`. This is the component that `FilledCover.indexEquiv` labels by that cycle, so
`simp` rewrites `degree p ((indexEquiv hp ν).symm (.inl (Quotient.mk _ j)))` to the cycle length. -/
@[simp]
theorem degree_overZero_mk_monodromy {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p (overZero p (ConnectedComponents.mk ⟨hp.monodromy (.mk αZero) (ν.symm j),
      hp.monodromy_αZero_mem_preimage (ν.symm j)⟩)) =
      minimalPeriod (hp.monodromyTriple ν).σ0 j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  have key := (exists_homeomorph_chart_eq hp hfin (overZero p
    (ConnectedComponents.mk ⟨_, hp.monodromy_αZero_mem_preimage (ν.symm j)⟩))).imp fun _ h ↦ h.1
  rw [component, sigmaEquiv_overZero] at key
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ0 ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_zero]
  exact key

omit hfin in
/-- **The local degree over `1` is the cycle length.** The component of `p ⁻¹' D₁*` containing the
endpoint of the lift of `αOne` from the sheet `ν.symm j` has local degree the length of the cycle of
`j` under `σ1`. This is the component that `FilledCover.indexEquiv` labels by that cycle, so `simp`
rewrites `degree p ((indexEquiv hp ν).symm (.inr (.inl (Quotient.mk _ j))))` to the cycle length. -/
@[simp]
theorem degree_overOne_mk_monodromy {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p (overOne p (ConnectedComponents.mk ⟨hp.monodromy (.mk αOne) (ν.symm j),
      hp.monodromy_αOne_mem_preimage (ν.symm j)⟩)) =
      minimalPeriod (hp.monodromyTriple ν).σ1 j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  have key := (exists_homeomorph_chart_eq hp hfin (overOne p
    (ConnectedComponents.mk ⟨_, hp.monodromy_αOne_mem_preimage (ν.symm j)⟩))).imp fun _ h ↦ h.1
  rw [component, sigmaEquiv_overOne] at key
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σ1 ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_one]
  exact key

omit hfin in
/-- **The local degree over `∞` is the cycle length.** The component of `p ⁻¹' D∞*` containing the
endpoint of the lift of `αPlus` from the sheet `ν.symm j` has local degree the length of the cycle
of `j` under `σinf`. This is the component that `FilledCover.indexEquiv` labels by that cycle, so
`simp` rewrites `degree p ((indexEquiv hp ν).symm (.inr (.inr (Quotient.mk _ j))))` to the cycle
length. -/
@[simp]
theorem degree_overInf_mk_monodromy {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) (j : Fin n) :
    degree p (overInf p (ConnectedComponents.mk ⟨hp.monodromy (.mk αPlus) (ν.symm j),
      hp.monodromy_αPlus_mem_preimage (ν.symm j)⟩)) =
      minimalPeriod (hp.monodromyTriple ν).σinf j := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  have key := (exists_homeomorph_chart_eq hp hfin (overInf p
    (ConnectedComponents.mk ⟨_, hp.monodromy_αPlus_mem_preimage (ν.symm j)⟩))).imp fun _ h ↦ h.1
  rw [component, sigmaEquiv_overInf] at key
  refine ((hp.exists_homeomorph_puncturedDiscPow_iff_minimalPeriod_σinf ν j
    (degree_ne_zero hp hfin _)).1 ?_).symm
  rw [← connectedComponents_preimage_singleton, ← Puncture.coord_inf]
  exact key

/-- **The filled cover is compact**: outside the images of the discs of radius `1 / 2` under the
filling charts, a finite cover lies over a compact core of `ℂ ∖ {0, 1}`. -/
theorem compactSpace : CompactSpace (FilledCover p) := by
  have := finite_filledPoint hp hfin
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
    obtain ⟨i, hi⟩ := (sigmaEquiv p).surjective ⟨q, ConnectedComponents.mk ⟨y, hq⟩⟩
    obtain ⟨w, hwy⟩ : y ∈ range (chart p i) := by
      rw [range_chart hp hfin, hi]
      exact ⟨hq, rfl⟩
    have hwr : 1 / 2 ≤ ‖(w : ℂ)‖ := not_lt.1 fun h ↦ hy (mem_iUnion.2 ⟨i, w, h, hwy⟩)
    obtain ⟨hw, -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
    refine Or.inr (mem_iUnion.2 ⟨i, ?_⟩)
    have hpos : (0 : ℝ) < (1 / 2) ^ degree p i / 2 := by positivity
    rw [mem_preimage, ← hwy, (sigmaEquiv p i).1.mem_compactCore_iff hpos hw, hcoord, norm_pow]
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
  have := finite_filledPoint hp hfin
  PunctureFilling.secondCountableTopology (isOpenEmbedding_chart hp hfin)

omit hfin in
/-- **The number of added points.** For a cover whose fibre over `1/2` is numbered by `ν`, the
filled cover has `c(σ0) + c(σ1) + c(σinf)` added points, where `c(σ)` is the number of cycles of
`σ`, fixed points included (`FilledPoint.natCard_eq_cycleCounts`). -/
theorem natCard_range_center {n : ℕ} (ν : p ⁻¹' {basePt} ≃ Fin n) :
    Nat.card (range (PunctureFilling.center (chart p))) =
      (hp.monodromyTriple ν).cycleCounts.1 + (hp.monodromyTriple ν).cycleCounts.2.1 +
        (hp.monodromyTriple ν).cycleCounts.2.2 := by
  rw [← Nat.card_congr (Equiv.ofInjective _ PunctureFilling.center_injective),
    FilledPoint.natCard_eq_cycleCounts p hp ν]

end FilledCover

end TauCeti

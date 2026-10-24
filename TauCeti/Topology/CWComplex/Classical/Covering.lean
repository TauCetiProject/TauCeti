/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Algebra.Group.Action.Sigma
public import Mathlib.Topology.Covering.Quotient
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.Covering.Convex
public import TauCeti.Topology.SeparatedMap

/-!
# Lifting a CW structure along a covering map

Let `p : E → B` be a covering map and let `C` be a CW complex in the Hausdorff space `B`.
The closed unit ball is convex, so the characteristic map of each cell of `C` lifts through `p`,
uniquely once the lift of one point is prescribed
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_convex`). Lifting every characteristic map
through every point over the centre of its cell makes `p ⁻¹' C` a CW complex
(`TauCeti.cwComplexPreimage`):

* its `n`-cells are the pairs of an `n`-cell `i` of `C` and a point of `E` over the centre
  `map n i 0` (`TauCeti.cellPreimageEquiv`);
* the characteristic map of such a pair lifts the characteristic map of `i`
  (`TauCeti.apply_map_cellPreimageEquiv_symm`) and sends the centre to the chosen point
  (`TauCeti.map_cellPreimageEquiv_symm_zero`).

The open cells of distinct pairs are disjoint because two lifts of one characteristic map that
meet are equal, and every point of `E` over a closed cell of `C` lies on a lift of that cell, which
gives the covering of `p ⁻¹' C` by the closed lifted cells. Near a point of a lift, every point
over the characteristic map lies on that same lift, because `p` is a local homeomorphism. Two
consequences of this local rigidity finish the construction. Only finitely many lifts of a cell
meet a compact set, which bounds the boundary of a lifted cell by finitely many lifted cells. And
the lift has the weak topology: a set meeting every closed lifted cell in a closed set is, near
each point, the preimage under a local inverse of `p` of a set meeting every closed cell of `C` in
a closed set. The covering map is cellular for the lifted structure
(`TauCeti.isCellular_restrictPreimage`).

When `p` is the quotient covering map of a free action of a group `G` on `E`
(`IsQuotientCoveringMap p G`), the group permutes the lifted cells
(`TauCeti.cellPreimageMulAction`), translating characteristic maps
(`TauCeti.map_smul_cellPreimage`). The action is free (`TauCeti.isCancelSMul_cellPreimage`), and
there is exactly one orbit over each cell of `C` (`TauCeti.exists_cellPreimageEquiv_fst_eq` and
`TauCeti.exists_smul_eq_iff_cellPreimageEquiv_fst_eq`): for a choice `s` of lifts of the cells
of `C`, the lifted cells are the translates `g • s i`, each exactly once
(`TauCeti.sigmaSMulLiftEquiv`). Translation by `g`, restricted to `p ⁻¹' C`
(`TauCeti.preimageSMul`), is cellular (`TauCeti.isCellular_preimageSMul`).

For a finite CW complex and a cover with finite fibres the lift is finite
(`TauCeti.finite_cwComplexPreimage`). Counting cells, if `C` has finitely many cells in each
dimension, `p ⁻¹' C` has, in each dimension, the sum over the cells of `C` of the number of points
over their centres
(`TauCeti.nat_card_cell_preimage`), so `d` times as many cells as `C` when every fibre over `C`
has `d` points (`TauCeti.nat_card_cell_preimage_of_card_fiber`). This is the input for the
multiplicativity of the Euler characteristic in finite covers. In particular the total space of
such a cover of a finite CW complex has finite CW type (`IsCoveringMap.finiteCWType`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, Proposition 1.33 (the lifting criterion), and the exercises of Section 2.2 on
  the Euler characteristic of an `n`-sheeted covering space.
* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 (free `G`-CW complexes).
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {C : Set B} [CWComplex C]

variable (p C) in
/-- The `n`-cells of the lifted CW structure: an `n`-cell of `C` together with a point of the fibre
of `p` over the image of the centre of its characteristic map. -/
private abbrev CoverCell (n : ℕ) : Type u := Σ i : cell C n, p ⁻¹' {map n i 0}

/-- The characteristic map of a cell, as a continuous map on the closed unit ball. -/
private def cellBallMap {n : ℕ} (i : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, B) :=
  ⟨(closedBall 0 1).domRestrict (map n i), (continuousOn n i).domRestrict⟩

/-- The centre of the closed unit ball. -/
private def ballCentre (n : ℕ) : closedBall (0 : Fin n → ℝ) 1 :=
  ⟨0, mem_closedBall_self zero_le_one⟩

section Lift

variable (hp : IsCoveringMap p)
include hp

/-- The lift of the characteristic map of `c.1` through `p` sending the centre to `c.2`. -/
private def coverLift {n : ℕ} (c : CoverCell p C n) : C(closedBall (0 : Fin n → ℝ) 1, E) :=
  (hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1)
      (cellBallMap c.1) (ballCentre n) c.2 c.2.2).exists.choose

private theorem coverLift_ballCentre {n : ℕ} (c : CoverCell p C n) :
    coverLift hp c (ballCentre n) = c.2 :=
  (hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1)
      (cellBallMap c.1) (ballCentre n) c.2 c.2.2).exists.choose_spec.1

private theorem comp_coverLift {n : ℕ} (c : CoverCell p C n) :
    p ∘ coverLift hp c = cellBallMap c.1 :=
  (hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1)
      (cellBallMap c.1) (ballCentre n) c.2 c.2.2).exists.choose_spec.2

private theorem coverLift_apply {n : ℕ} (c : CoverCell p C n) (x : closedBall (0 : Fin n → ℝ) 1) :
    p (coverLift hp c x) = map n c.1 x :=
  congr_fun (comp_coverLift hp c) x

/-- Every point over the image of a point `x` of the closed ball under the characteristic map of
`i` is the value at `x` of the lift attached to some point over the centre. -/
private theorem exists_coverLift_eq {n : ℕ} (i : cell C n) (x : closedBall (0 : Fin n → ℝ) 1)
    {e : E} (he : p e = map n i x) :
    ∃ e₀ : p ⁻¹' {map n i 0}, coverLift hp ⟨i, e₀⟩ x = e := by
  obtain ⟨F, ⟨hFx, hF⟩, -⟩ :=
    hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1) (cellBallMap i) x e he
  have hF₀ : F (ballCentre n) ∈ p ⁻¹' {map n i 0} := congr_fun hF (ballCentre n)
  refine ⟨⟨_, hF₀⟩, ?_⟩
  obtain ⟨G, -, hG⟩ := hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1)
      (cellBallMap i) (ballCentre n) _ hF₀
  rw [hG (coverLift hp ⟨i, ⟨_, hF₀⟩⟩) ⟨coverLift_ballCentre hp _, comp_coverLift hp _⟩,
    ← hG F ⟨rfl, hF⟩, hFx]

/-- Two lifts of the characteristic map of the same cell which agree at one point are equal. -/
private theorem eq_of_coverLift_eq {n : ℕ} {i : cell C n} {e₀ e₁ : p ⁻¹' {map n i 0}}
    (x : closedBall (0 : Fin n → ℝ) 1) (h : coverLift hp ⟨i, e₀⟩ x = coverLift hp ⟨i, e₁⟩ x) :
    e₀ = e₁ := by
  obtain ⟨G, -, hG⟩ := hp.existsUnique_continuousMap_lifts_of_convex (convex_closedBall 0 1)
      (cellBallMap i) x _ (coverLift_apply hp ⟨i, e₀⟩ x)
  have := (hG _ ⟨rfl, comp_coverLift hp _⟩).trans (hG _ ⟨h.symm, comp_coverLift hp _⟩).symm
  exact Subtype.ext (by
    rw [← coverLift_ballCentre hp ⟨i, e₀⟩, ← coverLift_ballCentre hp ⟨i, e₁⟩, this])

open scoped Classical in
/-- The lift `coverLift hp c`, extended to all of `Fin n → ℝ` by the point `c.2` off the closed
ball. -/
private def coverLiftFun {n : ℕ} (c : CoverCell p C n) (x : Fin n → ℝ) : E :=
  if hx : x ∈ closedBall 0 1 then coverLift hp c ⟨x, hx⟩ else c.2

private theorem coverLiftFun_of_mem {n : ℕ} (c : CoverCell p C n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) : coverLiftFun hp c x = coverLift hp c ⟨x, hx⟩ := by
  classical
  exact dite_eq_left hx

private theorem coverLiftFun_apply {n : ℕ} (c : CoverCell p C n) {x : Fin n → ℝ}
    (hx : x ∈ closedBall 0 1) : p (coverLiftFun hp c x) = map n c.1 x := by
  rw [coverLiftFun_of_mem hp c hx, coverLift_apply hp c]

private theorem coverLiftFun_of_notMem {n : ℕ} (c : CoverCell p C n) {x : Fin n → ℝ}
    (hx : x ∉ closedBall 0 1) : coverLiftFun hp c x = c.2 := by
  classical
  exact dite_eq_right hx

/-- The characteristic map of a lifted cell: the lift of the characteristic map of `c.1` through
`p` sending the centre to `c.2`, with inverse the inverse of the characteristic map of `c.1`
after `p`. -/
private def coverCellMap {n : ℕ} (c : CoverCell p C n) : PartialEquiv (Fin n → ℝ) E where
  toFun := coverLiftFun hp c
  invFun y := (map n c.1).symm (p y)
  source := ball 0 1
  target := coverLiftFun hp c '' ball 0 1
  map_source' x hx := mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [coverLiftFun_apply hp c (ball_subset_closedBall hx),
      (map n c.1).left_inv (by rwa [source_eq])]
    exact hx
  left_inv' x hx := by
    rw [coverLiftFun_apply hp c (ball_subset_closedBall hx),
      (map n c.1).left_inv (by rwa [source_eq])]
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [coverLiftFun_apply hp c (ball_subset_closedBall hx),
      (map n c.1).left_inv (by rwa [source_eq])]

private theorem coverCellMap_apply {n : ℕ} (c : CoverCell p C n) (x : Fin n → ℝ) :
    coverCellMap hp c x = coverLiftFun hp c x :=
  (rfl)

private theorem continuousOn_coverCellMap {n : ℕ} (c : CoverCell p C n) :
    ContinuousOn (coverCellMap hp c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert (coverLift hp c).continuous using 1
  funext x
  exact coverLiftFun_of_mem hp c x.2

private theorem continuousOn_symm_coverCellMap {n : ℕ} (c : CoverCell p C n) :
    ContinuousOn (coverCellMap hp c).symm (coverCellMap hp c).target := by
  refine (continuousOn_symm n c.1).comp hp.continuous.continuousOn ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← (map n c.1).image_source_eq_target, source_eq]
  exact ⟨x, hx, (coverLiftFun_apply hp c (ball_subset_closedBall hx)).symm⟩

/-- Distinct lifted cells have disjoint open cells: their images under `p` lie in the open cells
of the underlying cells, on whose interiors the characteristic maps are injective, and two lifts of
the same characteristic map that meet are equal. -/
private theorem pairwiseDisjoint_coverCellMap :
    (univ : Set (Σ n, CoverCell p C n)).PairwiseDisjoint
      (fun c ↦ coverCellMap hp c.2 '' ball 0 1) := by
  rintro ⟨n, i, e⟩ - ⟨n', i', e'⟩ - hne
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', h⟩
  have hb : map n' i' x' = map n i x := by
    rw [← coverLiftFun_apply hp ⟨i', e'⟩ (ball_subset_closedBall hx'),
      ← coverLiftFun_apply hp ⟨i, e⟩ (ball_subset_closedBall hx)]
    exact congrArg p h
  have hcell : (⟨n, i⟩ : Σ n, cell C n) = ⟨n', i'⟩ := by
    by_contra hni
    exact Set.disjoint_left.1 (disjoint_openCell_of_ne hni) (mem_image_of_mem _ hx)
      (hb ▸ mem_image_of_mem _ hx')
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.1 hcell
  obtain rfl := eq_of_heq hi
  have hxx : x' = x := (map n i).injOn (by rwa [source_eq]) (by rwa [source_eq]) hb
  rw [hxx] at h
  obtain rfl := eq_of_coverLift_eq hp (e₀ := e) (e₁ := e') ⟨x, ball_subset_closedBall hx⟩ (by
    rw [← coverLiftFun_of_mem hp _ (ball_subset_closedBall hx),
      ← coverLiftFun_of_mem hp _ (ball_subset_closedBall hx)]
    exact h.symm)
  exact hne rfl

/-- The image of the closed ball under a lift of a characteristic map is its closed lifted cell. -/
private theorem range_coverLift {n : ℕ} (c : CoverCell p C n) :
    range (coverLift hp c) = coverCellMap hp c '' closedBall 0 1 := by
  ext e
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, by rw [coverCellMap_apply, coverLiftFun_of_mem hp c x.2]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, by rw [coverCellMap_apply, coverLiftFun_of_mem hp c hx]⟩

/-- Near a point `(coverLift hp c y, y)` of the fibre product of `p` and the characteristic map,
every point of the fibre product lies on the graph of the same lift: `p` is injective on a
neighbourhood of `coverLift hp c y`, and the lift is continuous. -/
private theorem eventually_coverLift_eq {n : ℕ} (c : CoverCell p C n)
    (y : closedBall (0 : Fin n → ℝ) 1) :
    ∀ᶠ q : E × closedBall (0 : Fin n → ℝ) 1 in 𝓝 (coverLift hp c y, y),
      p q.1 = map n c.1 q.2 → coverLift hp c q.2 = q.1 := by
  obtain ⟨h, hyh, hph⟩ := hp.isLocalHomeomorph (coverLift hp c y)
  have hV : h.source ∈ 𝓝 (coverLift hp c y) := h.open_source.mem_nhds hyh
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hV,
    ((coverLift hp c).continuous.comp continuous_snd).continuousAt.preimage_mem_nhds hV]
    with q hq₁ hq₂ hpq
  have hinj : InjOn p h.source := by rw [hph]; exact h.injOn
  exact hinj hq₂ hq₁ ((coverLift_apply hp c q.2).trans hpq.symm)

/-- Only finitely many lifts of the characteristic map of a cell meet a compact set: the fibre
product of the compact set and the closed ball over `B` is compact, and by
`eventually_coverLift_eq` each of its points has a neighbourhood meeting a single lift. -/
private theorem finite_setOf_coverLift_mem [T2Space B] {m : ℕ} (k : cell C m) {K : Set E}
    (hK : IsCompact K) :
    {e₀ : p ⁻¹' {map m k 0} | ∃ y, coverLift hp ⟨k, e₀⟩ y ∈ K}.Finite := by
  have := isCompact_iff_compactSpace.1 (isCompact_closedBall (0 : Fin m → ℝ) 1)
  set S : Set (E × closedBall (0 : Fin m → ℝ) 1) := K ×ˢ univ ∩ {q | p q.1 = cellBallMap k q.2}
  have hS : IsCompact S := (hK.prod isCompact_univ).inter_right <|
    isClosed_eq (hp.continuous.comp continuous_fst) ((cellBallMap k).continuous.comp continuous_snd)
  have hlift (q : S) : ∃ e₀ : p ⁻¹' {map m k 0}, coverLift hp ⟨k, e₀⟩ q.1.2 = q.1.1 :=
    exists_coverLift_eq hp k q.1.2 q.2.2
  choose e he using hlift
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover'
    (fun q hq ↦ {q' | p q'.1 = map m k q'.2 → coverLift hp ⟨k, e ⟨q, hq⟩⟩ q'.2 = q'.1})
    fun q hq ↦ by
      have := eventually_coverLift_eq hp ⟨k, e ⟨q, hq⟩⟩ q.2
      rwa [he ⟨q, hq⟩, Prod.mk.eta] at this
  refine ((t.finite_toSet.image e).subset ?_)
  rintro e₀ ⟨y, hy⟩
  have hq : (coverLift hp ⟨k, e₀⟩ y, y) ∈ S := ⟨⟨hy, mem_univ _⟩, coverLift_apply hp _ y⟩
  obtain ⟨q', hq't, hq'⟩ := mem_iUnion₂.1 (ht hq)
  exact ⟨q', hq't, eq_of_coverLift_eq hp y (hq' (coverLift_apply hp _ y))⟩

/-- The boundary of a lifted cell lies in finitely many lifted cells of smaller dimension: its
image under `p` lies in finitely many closed cells of smaller dimension, every point over such a
closed cell lies in a lift of it, and only finitely many of these lifts meet the compact image of
the boundary. -/
private theorem mapsTo_coverCellMap [T2Space B] (n : ℕ) (c : CoverCell p C n) :
    ∃ I : Π m, Finset (CoverCell p C m), MapsTo (coverCellMap hp c) (sphere 0 1)
      (⋃ (m < n) (c' ∈ I m), coverCellMap hp c' '' closedBall 0 1) := by
  have hK : IsCompact (coverCellMap hp c '' sphere 0 1) :=
    (isCompact_sphere 0 1).image_of_continuousOn
      ((continuousOn_coverCellMap hp c).mono sphere_subset_closedBall)
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n c.1
  refine ⟨fun m ↦ (I m).sigma fun k ↦ (finite_setOf_coverLift_mem hp k hK).toFinset, ?_⟩
  intro x hx
  have hxc : x ∈ closedBall 0 1 := sphere_subset_closedBall hx
  obtain ⟨m, hm, k, hk, y, hy, hyx⟩ := by simpa using hI (mem_image_of_mem _ hx)
  obtain ⟨e₀, he₀⟩ := exists_coverLift_eq hp k ⟨y, hy⟩ (e := coverLiftFun hp c x)
    (by rw [coverLiftFun_apply hp c hxc, ← hyx])
  refine mem_iUnion₂.2 ⟨m, hm, mem_iUnion₂.2 ⟨⟨k, e₀⟩, ?_, y, hy, ?_⟩⟩
  · exact Finset.mem_sigma.2 ⟨hk, (Set.Finite.mem_toFinset _).2 ⟨⟨y, hy⟩, he₀ ▸ ⟨x, hx, rfl⟩⟩⟩
  · rw [coverCellMap_apply, coverLiftFun_of_mem hp _ hy, he₀, coverCellMap_apply]

/-- The lifted cells give the preimage of `C` the weak topology. Let `x` be a point outside `A`
and `h` a local inverse of `p` around `x`. The points of `C` that are either outside the target
of `h` or images of points of `A` in its source form a closed set: on each closed cell of `C`, near
a point of the target, they are read off a single lift of the characteristic map, which meets `A`
in a closed set. The preimage of its complement inside the source of `h` is a neighbourhood of `x`
disjoint from `A`. -/
private theorem isClosed_of_isClosed_inter_coverCellMap [T2Space B] {A : Set E}
    (hAC : A ⊆ p ⁻¹' C)
    (hA : ∀ n (c : CoverCell p C n), IsClosed (A ∩ coverCellMap hp c '' closedBall 0 1)) :
    IsClosed A := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨h, hxh, hph⟩ := hp.isLocalHomeomorph x
  have hpinj : InjOn p h.source := by rw [hph]; exact h.injOn
  have hpmap : MapsTo p h.source h.target := by rw [hph]; exact h.mapsTo
  set T : Set B := p '' (A ∩ h.source) ∪ h.targetᶜ
  have hT {n : ℕ} (j : cell C n) : IsClosed (cellBallMap j ⁻¹' T) := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    simp only [T, mem_compl_iff, mem_preimage, mem_union, not_or, not_not] at hy
    obtain ⟨hyA, hyt⟩ := hy
    have hsy : p (h.symm (cellBallMap j y)) = cellBallMap j y := by
      rw [hph]; exact h.right_inv hyt
    obtain ⟨e₀, he₀⟩ := exists_coverLift_eq hp j y hsy
    have hs : coverLift hp ⟨j, e₀⟩ y ∈ h.source := he₀ ▸ h.map_target hyt
    have hnA : coverLift hp ⟨j, e₀⟩ y ∉ A := fun hA' ↦ hyA ⟨_, ⟨hA', hs⟩, he₀ ▸ hsy⟩
    have hcl : IsClosed (coverLift hp ⟨j, e₀⟩ ⁻¹' A) := by
      rw [← preimage_inter_range, range_coverLift]
      exact (hA n ⟨j, e₀⟩).preimage (coverLift hp ⟨j, e₀⟩).continuous
    filter_upwards [(coverLift hp ⟨j, e₀⟩).continuous.continuousAt.preimage_mem_nhds
      (h.open_source.mem_nhds hs), hcl.isOpen_compl.mem_nhds hnA] with y' hy's hy'A
    simp only [mem_preimage, mem_compl_iff] at hy's hy'A
    have hpy' : p (coverLift hp ⟨j, e₀⟩ y') = cellBallMap j y' := coverLift_apply hp _ y'
    rintro (⟨a, ⟨haA, has⟩, hay⟩ | hy't)
    · exact hy'A (hpinj has hy's (hay.trans hpy'.symm) ▸ haA)
    · exact hy't (hpy' ▸ hpmap hy's)
  have hF : IsClosed (C ∩ T) := by
    refine (CWComplex.closed C _ inter_subset_left).2 fun n j ↦ ?_
    have hr : closedCell n j = range (cellBallMap j) := (range_domRestrict _ _).symm
    rw [inter_assoc, inter_comm T, ← inter_assoc,
      inter_eq_right.2 (closedCell_subset_complex n j), hr, ← image_preimage_eq_range_inter]
    exact ((hT j).isCompact.image (cellBallMap j).continuous).isClosed
  refine ⟨h.source ∩ p ⁻¹' (C ∩ T)ᶜ, ?_, h.open_source.inter
    (hF.isOpen_compl.preimage hp.continuous), hxh, ?_⟩
  · rintro a ⟨has, haT⟩ haA
    exact haT ⟨hAC haA, .inl ⟨a, ⟨haA, has⟩, rfl⟩⟩
  · rintro ⟨-, ⟨a, ⟨haA, has⟩, hax⟩ | hxt⟩
    · exact hx (hpinj has hxh hax ▸ haA)
    · exact hxt (hpmap hxh)

/-- The closed lifted cells cover the preimage of `C`. -/
private theorem iUnion_coverCellMap :
    ⋃ (n : ℕ) (c : CoverCell p C n), coverCellMap hp c '' closedBall 0 1 = p ⁻¹' C := by
  ext e
  simp only [mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨n, c, x, hx, rfl⟩
    rw [coverCellMap_apply, coverLiftFun_apply hp c hx]
    exact closedCell_subset_complex n c.1 (mem_image_of_mem _ hx)
  · intro he
    rw [← CWComplex.union (C := C)] at he
    obtain ⟨n, i, x, hx, hxe⟩ := by simpa using he
    obtain ⟨e₀, h⟩ := exists_coverLift_eq hp i ⟨x, hx⟩ hxe.symm
    exact ⟨n, ⟨i, e₀⟩, x, hx, by rw [coverCellMap_apply, coverLiftFun_of_mem hp _ hx, h]⟩

end Lift

section Structure

variable [T2Space B] (C) (hp : IsCoveringMap p)

/-- **A CW structure lifts along a covering map.** If `C` is a CW complex in the Hausdorff space
`B` and `p : E → B` is a covering map, then `p ⁻¹' C` is a CW complex in `E`. Its `n`-cells are the
pairs of an `n`-cell of `C` and a point of `E` over the centre of that cell
(`TauCeti.cellPreimageEquiv`); the characteristic map of such a pair is the lift of the
characteristic map of the cell through `p` sending the centre to the chosen point. -/
@[instance_reducible]
def cwComplexPreimage : CWComplex (p ⁻¹' C) where
  cell := CoverCell p C
  map _ c := coverCellMap hp c
  source_eq _ _ := rfl
  continuousOn _ c := continuousOn_coverCellMap hp c
  continuousOn_symm _ c := continuousOn_symm_coverCellMap hp c
  pairwiseDisjoint' := pairwiseDisjoint_coverCellMap hp
  mapsTo' := mapsTo_coverCellMap hp
  closed' _ hAC hA := isClosed_of_isClosed_inter_coverCellMap hp hAC hA
  union' := iUnion_coverCellMap hp

/-- The `n`-cells of the lift of `C` along `p` are the pairs of an `n`-cell `i` of `C` and a point
of `E` over the centre `map n i 0` of that cell. -/
def cellPreimageEquiv (n : ℕ) :
    letI := cwComplexPreimage C hp
    cell (p ⁻¹' C) n ≃ Σ i : cell C n, p ⁻¹' {map n i 0} :=
  Equiv.refl _

/-- The characteristic maps of `TauCeti.cwComplexPreimage` are the extended lifts
`coverLiftFun`, by construction. -/
private theorem map_eq_coverLiftFun {n : ℕ}
    (c : letI := cwComplexPreimage C hp; cell (p ⁻¹' C) n) (x : Fin n → ℝ) :
    letI := cwComplexPreimage C hp
    map n c x = coverLiftFun hp c x :=
  (rfl)

variable {n : ℕ} (c : Σ i : cell C n, p ⁻¹' {map n i 0})

/-- The characteristic maps of `TauCeti.cwComplexPreimage` are the maps `coverCellMap`, by
construction. -/
private theorem map_cellPreimageEquiv_symm :
    letI := cwComplexPreimage C hp
    map n ((cellPreimageEquiv C hp n).symm c) = coverCellMap hp c :=
  (rfl)

/-- The characteristic map of a lifted cell sends the centre to the chosen point over the centre
of the underlying cell. -/
theorem map_cellPreimageEquiv_symm_zero :
    letI := cwComplexPreimage C hp
    map n ((cellPreimageEquiv C hp n).symm c) 0 = c.2 := by
  rw [map_cellPreimageEquiv_symm, coverCellMap_apply,
    coverLiftFun_of_mem hp c (mem_closedBall_self zero_le_one)]
  exact coverLift_ballCentre hp c

/-- The characteristic map of a lifted cell lifts the characteristic map of the underlying cell
on the closed unit ball. -/
theorem apply_map_cellPreimageEquiv_symm {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := cwComplexPreimage C hp
    p (map n ((cellPreimageEquiv C hp n).symm c) x) = map n c.1 x := by
  rw [map_cellPreimageEquiv_symm, coverCellMap_apply, coverLiftFun_apply hp c hx]

omit c in
/-- Over a surjective covering map, every cell of `C` has a lift. -/
theorem exists_cellPreimageEquiv_fst_eq (hsurj : Function.Surjective p) (i : cell C n) :
    letI := cwComplexPreimage C hp
    ∃ c : cell (p ⁻¹' C) n, (cellPreimageEquiv C hp n c).1 = i := by
  let := cwComplexPreimage C hp
  obtain ⟨e, he⟩ := hsurj (map n i 0)
  exact ⟨(cellPreimageEquiv C hp n).symm ⟨i, e, he⟩, by rw [Equiv.apply_symm_apply]⟩

section Finite

variable (hfin : ∀ b, Finite ↥(p ⁻¹' {b}))

omit c in
omit [TopologicalSpace E] [T2Space B] in
include hfin in
private theorem finite_coverCell [RelCWComplex.FiniteType C] (n : ℕ) :
    _root_.Finite (CoverCell p C n) :=
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  inferInstance

omit c in
omit [TopologicalSpace E] [T2Space B] in
private theorem eventually_isEmpty_coverCell [RelCWComplex.FiniteDimensional C] :
    ∀ᶠ n in Filter.atTop, IsEmpty (CoverCell p C n) :=
  (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)).mono
    fun _ h ↦ ⟨fun c ↦ h.false c.1⟩

include hfin

omit c in
/-- The lift of a finite CW complex along a covering map with finite fibres is finite. -/
theorem finite_cwComplexPreimage [RelCWComplex.Finite C] :
    letI := cwComplexPreimage C hp
    RelCWComplex.Finite (p ⁻¹' C) :=
  letI := cwComplexPreimage C hp
  { eventually_isEmpty_cell := eventually_isEmpty_coverCell C
    finite_cell := finite_coverCell C hfin }

omit c in
/-- The number of `n`-cells of the lift of `C` along `p` is the sum, over the `n`-cells of `C`, of
the number of points over their centres. -/
theorem nat_card_cell_preimage [RelCWComplex.FiniteType C] :
    letI := cwComplexPreimage C hp
    Nat.card (cell (p ⁻¹' C) n) = ∑ᶠ i : cell C n, Nat.card ↥(p ⁻¹' {map n i 0}) := by
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := Fintype.ofFinite (cell C n)
  rw [Nat.card_congr (cellPreimageEquiv C hp n), Nat.card_sigma, finsum_eq_sum_of_fintype]

omit c in
/-- **Cells of a `d`-sheeted cover.** If every fibre of `p` over `C` has `d` points, the lift of `C`
along `p` has `d` times as many `n`-cells as `C`. -/
theorem nat_card_cell_preimage_of_card_fiber [RelCWComplex.FiniteType C] {d : ℕ}
    (hd : ∀ b ∈ C, Nat.card ↥(p ⁻¹' {b}) = d) :
    letI := cwComplexPreimage C hp
    Nat.card (cell (p ⁻¹' C) n) = d * Nat.card (cell C n) := by
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := Fintype.ofFinite (cell C n)
  have hc (i : cell C n) : Nat.card ↥(p ⁻¹' {map n i 0}) = d :=
    hd _ (closedCell_subset_complex n i (map_zero_mem_closedCell n i))
  rw [nat_card_cell_preimage C hp hfin, finsum_eq_sum_of_fintype]
  simp [hc, mul_comm]

end Finite

omit c in
include hp in
/-- The total space of a covering, with finite fibres, of a finite CW complex has finite CW type: it
is a finite CW complex itself. -/
theorem _root_.IsCoveringMap.finiteCWType [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) : FiniteCWType E := by
  let := cwComplexPreimage univ hp
  have := finite_cwComplexPreimage univ hp hfin
  have := hp.t2Space
  exact ((Homeomorph.setCongr (preimage_univ (f := p))).trans
    (Homeomorph.Set.univ E)).symm.finiteCWType

end Structure

section Cellular

variable [T2Space B] (C) (hp : IsCoveringMap p)

/-- **The covering map is cellular** for the lifted CW structure, as a map from `p ⁻¹' C` to `C`:
the lifted open `n`-cells lie over the open `n`-cells of `C`. -/
theorem isCellular_restrictPreimage :
    letI := cwComplexPreimage C hp
    haveI := hp.t2Space
    IsCellular (p ⁻¹' C) C
      (TopCat.ofHom ⟨C.restrictPreimage p, hp.continuous.restrictPreimage⟩) := by
  let := cwComplexPreimage C hp
  have := hp.t2Space
  rintro n ⟨x, hxC⟩ hx
  simp only [CWComplex.mem_skeletonLT_iff] at hx ⊢
  obtain ⟨m, hm, c, y, hy, rfl⟩ := hx
  refine ⟨m, hm, c.1, y, hy, ?_⟩
  exact (coverLiftFun_apply hp c (ball_subset_closedBall hy)).symm

end Cellular

section Deck

/-! ### The deck action on the lifted cells

When `p` is the quotient covering map of a free action of a group `G` on `E`
(`IsQuotientCoveringMap p G`), the group permutes the lifted cells: `g` carries the lift through
a point `e` over the centre of a cell to the lift through `g • e`. The action is free, and its
orbits are exactly the sets of lifts of one cell of `C`. -/

variable [T2Space B] (C) {G : Type*} [Group G] [MulAction G E] (hG : IsQuotientCoveringMap p G)

omit [T2Space B] [CWComplex C] in
/-- Translation by `g`, restricted to the preimage `p ⁻¹' C`, which it preserves because `p` is
invariant under the action. -/
def preimageSMul (g : G) : TopCat.of (p ⁻¹' C) ⟶ TopCat.of (p ⁻¹' C) :=
  haveI := hG.toContinuousConstSMul
  TopCat.ofHom ⟨fun x ↦ ⟨g • x.1, by simpa only [mem_preimage, hG.map_smul] using x.2⟩,
    by fun_prop⟩

omit [T2Space B] [CWComplex C] in
@[simp]
theorem coe_preimageSMul_apply (g : G) (x : p ⁻¹' C) :
    (preimageSMul C hG g x : E) = g • (x : E) :=
  (rfl)

/-- The action of `G` on the `n`-cells of the lift of `C` along a quotient covering map, by its
action on the points over the centres of the cells of `C`. -/
@[implicit_reducible]
def cellPreimageMulAction (n : ℕ) :
    letI := cwComplexPreimage C hG.isCoveringMap
    MulAction G (cell (p ⁻¹' C) n) :=
  letI (i : cell C n) := hG.mulActionFiber (map n i 0)
  inferInstanceAs (MulAction G (Σ i : cell C n, p ⁻¹' {map n i 0}))

variable {n : ℕ} (g : G) (c : Σ i : cell C n, p ⁻¹' {map n i 0})

omit [T2Space B] in
/-- Translating a lift of a characteristic map by `g` gives the lift through the translated point
over the centre. -/
private theorem coverLift_smul (hgc : p (g • (c.2 : E)) = map n c.1 0)
    (x : closedBall (0 : Fin n → ℝ) 1) :
    coverLift hG.isCoveringMap ⟨c.1, ⟨g • (c.2 : E), hgc⟩⟩ x =
      g • coverLift hG.isCoveringMap c x := by
  have := hG.toContinuousConstSMul
  have : PreconnectedSpace (closedBall (0 : Fin n → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_closedBall 0 1).isPreconnected
  refine congr_fun (hG.isCoveringMap.eq_of_comp_eq (coverLift _ _).continuous
    ((continuous_const_smul g).comp (coverLift hG.isCoveringMap c).continuous) ?_ (ballCentre n)
    ?_) x
  · funext z
    simp only [Function.comp_apply, hG.map_smul, coverLift_apply]
  · simp only [Function.comp_apply, coverLift_ballCentre]

/-- The first component of `cellPreimageEquiv` of a translated cell: translation does not move
the underlying cell of `C`. -/
@[simp]
theorem cellPreimageEquiv_smul_fst (c : letI := cwComplexPreimage C hG.isCoveringMap
      cell (p ⁻¹' C) n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    (cellPreimageEquiv C hG.isCoveringMap n (g • c)).1 =
      (cellPreimageEquiv C hG.isCoveringMap n c).1 :=
  (rfl)

/-- The second component of `cellPreimageEquiv` of a translated cell: the chosen point over the
centre is translated. -/
@[simp]
theorem coe_cellPreimageEquiv_smul_snd (c : letI := cwComplexPreimage C hG.isCoveringMap
      cell (p ⁻¹' C) n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    ((cellPreimageEquiv C hG.isCoveringMap n (g • c)).2 : E) =
      g • ((cellPreimageEquiv C hG.isCoveringMap n c).2 : E) :=
  (rfl)

/-- The characteristic map of a translated cell is the translate of the characteristic map. -/
theorem map_smul_cellPreimage (c : letI := cwComplexPreimage C hG.isCoveringMap
      cell (p ⁻¹' C) n) (x : Fin n → ℝ) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    map n (g • c) x = g • map n c x := by
  let := cwComplexPreimage C hG.isCoveringMap
  let := cellPreimageMulAction C hG n
  rw [map_eq_coverLiftFun, map_eq_coverLiftFun]
  by_cases hx : x ∈ closedBall 0 1
  · rw [coverLiftFun_of_mem _ _ hx, coverLiftFun_of_mem _ _ hx]
    exact coverLift_smul C hG g c _ ⟨x, hx⟩
  · rw [coverLiftFun_of_notMem _ _ hx, coverLiftFun_of_notMem _ _ hx]
    rfl

/-- `G` acts freely on the lifted cells. -/
theorem isCancelSMul_cellPreimage :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    IsCancelSMul G (cell (p ⁻¹' C) n) := by
  let := cwComplexPreimage C hG.isCoveringMap
  let := cellPreimageMulAction C hG n
  have := hG.isCancelSMul
  refine ⟨fun g g' c h ↦ IsCancelSMul.right_cancel g g' ((cellPreimageEquiv C _ n c).2 : E) ?_⟩
  rw [← coe_cellPreimageEquiv_smul_snd C hG, ← coe_cellPreimageEquiv_smul_snd C hG, h]

/-- Two lifted cells lie in the same `G`-orbit exactly when they lift the same cell of `C`. -/
theorem exists_smul_eq_iff_cellPreimageEquiv_fst_eq
    (c c' : letI := cwComplexPreimage C hG.isCoveringMap; cell (p ⁻¹' C) n) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    (∃ g : G, g • c = c') ↔
      (cellPreimageEquiv C hG.isCoveringMap n c).1 =
        (cellPreimageEquiv C hG.isCoveringMap n c').1 := by
  let := cwComplexPreimage C hG.isCoveringMap
  let := cellPreimageMulAction C hG n
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    exact cellPreimageEquiv_smul_fst C hG g c
  -- `cellPreimageEquiv` is `Equiv.refl`, so a lifted cell is a pair of a cell and a point.
  obtain ⟨i, e⟩ := c
  obtain ⟨i', e'⟩ := c'
  obtain rfl : i = i' := h
  obtain ⟨g, hg⟩ := hG.apply_eq_iff_mem_orbit.1 (e'.2.trans e.2.symm)
  exact ⟨g, Sigma.ext rfl (heq_of_eq (Subtype.ext hg))⟩

/-- **Translation by a group element is cellular** for the lifted CW structure. -/
theorem isCellular_preimageSMul (g : G) :
    letI := cwComplexPreimage C hG.isCoveringMap
    haveI := hG.isCoveringMap.t2Space
    IsCellular (p ⁻¹' C) (p ⁻¹' C) (preimageSMul C hG g) := by
  let := cwComplexPreimage C hG.isCoveringMap
  let := cellPreimageMulAction C hG
  have := hG.isCoveringMap.t2Space
  exact isCellular_of_map_eq _ _ (fun _ h ↦ h.elim) fun n c ↦
    ⟨g • c, fun x _ _ ↦ (map_smul_cellPreimage C hG g c x).symm⟩

section Lifts

variable (s : cell C n → letI := cwComplexPreimage C hG.isCoveringMap; cell (p ⁻¹' C) n)
  (hs : ∀ i, (cellPreimageEquiv C hG.isCoveringMap n (s i)).1 = i)

/-- Given a lift `s i` of each `n`-cell `i` of `C`, the lifted `n`-cells are the translates
`g • s i`, each exactly once. -/
def sigmaSMulLiftEquiv :
    letI := cwComplexPreimage C hG.isCoveringMap
    (Σ _ : cell C n, G) ≃ cell (p ⁻¹' C) n :=
  letI := cwComplexPreimage C hG.isCoveringMap
  letI := cellPreimageMulAction C hG n
  haveI := isCancelSMul_cellPreimage C hG (n := n)
  Equiv.ofBijective (fun x ↦ x.2 • s x.1) <| by
    refine ⟨fun ⟨i, g⟩ ⟨i', g'⟩ h ↦ ?_, fun c ↦ ?_⟩
    · obtain rfl : i = i' := by
        simpa only [cellPreimageEquiv_smul_fst, hs] using
          congrArg (fun c ↦ (cellPreimageEquiv C hG.isCoveringMap n c).1) h
      obtain rfl : g = g' := IsCancelSMul.right_cancel g g' (s i) h
      rfl
    · obtain ⟨g, hg⟩ := (exists_smul_eq_iff_cellPreimageEquiv_fst_eq C hG
        (s (cellPreimageEquiv C hG.isCoveringMap n c).1) c).2 (hs _)
      exact ⟨⟨_, g⟩, hg⟩

/-- The lifted cell indexed by `⟨i, g⟩` is the translate `g • s i`. -/
@[simp]
theorem sigmaSMulLiftEquiv_apply (x : Σ _ : cell C n, G) :
    letI := cwComplexPreimage C hG.isCoveringMap
    letI := cellPreimageMulAction C hG n
    sigmaSMulLiftEquiv C hG s hs x = x.2 • s x.1 :=
  (rfl)

end Lifts

end Deck

end TauCeti

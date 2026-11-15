/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CWComplex.Classical.CellAction
public import TauCeti.Topology.CWComplex.Classical.FreeAction
public import TauCeti.Topology.CWComplex.Classical.Map
public import TauCeti.Topology.CWComplex.Classical.OpenCells
public import TauCeti.Topology.Covering.Quotient

/-!
# The CW structure on the orbit space of a free cellular action

Let `G` act on a Hausdorff CW complex `E`, and let `p : E → B` be the quotient covering map of
the action (`IsQuotientCoveringMap p G`). Suppose that each element of `G` carries every open
`n`-cell of `E` onto an open `n`-cell, and that `G` acts freely on the set of cells: `g` carries
an open cell onto itself only when `g = 1`. Then `B` is a CW complex
(`IsQuotientCoveringMap.cwComplexQuotient`):

* the translation of open cells is an action of `G` on the `n`-cells of `E`
  (`TauCeti.cellMulAction`, characterised by `TauCeti.smul_openCell`), free by hypothesis
  (`TauCeti.isCancelSMul_cell`), and the `n`-cells of `B` are its orbits
  (`IsQuotientCoveringMap.cellQuotientEquiv`);
* the characteristic map of an orbit is `p ∘ φ` for the characteristic map `φ` of its chosen
  representative (`IsQuotientCoveringMap.map_cellQuotientEquiv_symm`);
* the covering map carries each open cell, closed cell, and skeleton of `E` onto the corresponding
  open cell, closed cell, and skeleton of `B` (`IsQuotientCoveringMap.image_openCell`,
  `IsQuotientCoveringMap.image_closedCell`, and `IsQuotientCoveringMap.image_skeletonLT`), and is
  therefore cellular (`IsQuotientCoveringMap.isCellular_cwComplexQuotient`);
* for any CW structure on `B` whose open cells are the images of those of `E`, choosing one lift
  over each `n`-cell of `B` parametrizes the `n`-cells of `E` via translation
  (`Function.Surjective.exists_image_openCell_eq` and
  `IsQuotientCoveringMap.sigmaSMulCellLiftEquiv`).

Only the characteristic maps of the representatives are used, and the hypotheses on the action
concern open cells rather than characteristic maps: a translation need not carry the
characteristic map of a cell to the characteristic map of the translated cell. This is the
situation of a group acting by simplicial automorphisms on a realization, whose cells are
parametrized through an order on the vertices that the action need not preserve.

The key point is that `p` restricts to a homeomorphism from each open cell onto its image
(`IsQuotientCoveringMap.injOn_openCell` and `IsQuotientCoveringMap.continuousOn_invFunOn_openCell`).
It is injective there, since a translate of an open cell meeting it is the cell itself, and hence
translation by `1`.
Its inverse is continuous because near a point `y` of an open `n`-cell `c` there is an open set
that misses every other closed `n`-cell and the `(n - 1)`-skeleton, so a point of the image of
`c` close to `p y` has exactly one preimage close to `y`, the one in `c`, and it is given by a
local inverse of `p`.

The CW structure `IsQuotientCoveringMap.cwComplexQuotient` itself does not use that `B` is
Hausdorff; Mathlib's classical CW complexes do not require it. Cellularity in `TauCeti.IsCellular`
uses `IsQuotientCoveringMap.t2Space_of_cwComplex`.

The action on cells is constructed more generally for a monoid acting on a relative CW complex
and carrying each open cell onto an open cell of the same dimension. If its translations are
continuous and the ambient space is Hausdorff, they carry the corresponding closed cells onto
each other as well.

## References

* T. tom Dieck, *Transformation Groups*, de Gruyter, 1987, Section II.1 (free `G`-CW complexes
  and their orbit spaces).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3 (covering spaces) and the Appendix, Topology of Cell Complexes.
-/

public section

noncomputable section

open CategoryTheory Function Metric Set Topology Topology.RelCWComplex
open scoped Pointwise

universe u

namespace TauCeti

variable {E : Type u} [TopologicalSpace E] {G : Type*}

section Quotient

variable {B : Type u} [TopologicalSpace B] [CWComplex (univ : Set E)]
  [Group G] [MulAction G E] [T2Space E] {p : E → B} (hp : IsQuotientCoveringMap p G)
  (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
    ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
  (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n), g • openCell n i = openCell n i → g = 1)

include hcell hfree in
/-- If the translate by `g` of a point of an open `n`-cell lies outside the `(n - 1)`-skeleton
and every other closed `n`-cell, then `g = 1`. -/
private theorem eq_one_of_smul_mem_openCell {n : ℕ} {i : cell (univ : Set E) n} {g : G} {y : E}
    (hy : y ∈ openCell n i)
    (hgy : g • y ∉ (skeletonLT (univ : Set E) (n : ℕ∞) : Set E) ∪
      ⋃ j ∈ ({i}ᶜ : Set (cell (univ : Set E) n)), closedCell n j) : g = 1 := by
  let := cellMulAction hcell n
  have hmem : g • y ∈ openCell n (g • i) := smul_mem_openCell_smul hcell g hy
  have hgi : g • i = i := by
    by_contra hne
    exact hgy (subset_union_right (mem_biUnion (mem_compl_singleton_iff.2 hne)
      (openCell_subset_closedCell n _ hmem)))
  exact hfree g n i (by rw [smul_openCell hcell, hgi])

omit [T2Space E] in
include hp hcell hfree in
/-- The covering map is injective on every open cell, without any separation assumption on `E`. -/
theorem _root_.IsQuotientCoveringMap.injOn_openCell {n : ℕ} (i : cell (univ : Set E) n) :
    InjOn p (openCell n i) := by
  intro x hx y hy hxy
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (hp.apply_eq_iff_mem_orbit.1 hxy)
  rw [eq_one_of_mem_openCell_of_smul_mem hcell hfree hy hx, one_smul]

include hp hcell hfree in
/-- The inverse of the restriction of the covering map to an open cell is continuous on the
image: together with `IsQuotientCoveringMap.injOn_openCell`, `p` maps each open cell
homeomorphically onto its image. -/
theorem _root_.IsQuotientCoveringMap.continuousOn_invFunOn_openCell [Nonempty E] {n : ℕ}
    (i : cell (univ : Set E) n) :
    ContinuousOn (invFunOn p (openCell n i)) (p '' openCell n i) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨e, hye, hpe⟩ := hp.isCoveringMap.isLocalHomeomorph y
  -- Near `y`, the open set `V` misses every closed `n`-cell other than `i` and the
  -- `(n - 1)`-skeleton, and `p` agrees with the partial homeomorphism `e`.
  set T := (skeletonLT (univ : Set E) (n : ℕ∞) : Set E) ∪
    ⋃ j ∈ ({i}ᶜ : Set (cell (univ : Set E) n)), closedCell n j
  set V := e.source ∩ Tᶜ
  have hV : IsOpen V :=
    e.open_source.inter (isClosed_skeletonLT_union_iUnion_closedCell n _).isOpen_compl
  have hyV : y ∈ V := ⟨hye, notMem_skeletonLT_union_of_mem_openCell n hy⟩
  have hinv : invFunOn p (openCell n i) (p y) = y :=
    (hp.injOn_openCell hcell hfree i).leftInvOn_invFunOn hy
  -- On the image of `V`, the inverse of the restriction of `p` to the open cell is `e.symm`.
  have heq : EqOn (invFunOn p (openCell n i)) e.symm (p '' V ∩ p '' openCell n i) := by
    rintro _ ⟨⟨v, hv, rfl⟩, y', hy', hvy'⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (hp.apply_eq_iff_mem_orbit.1 hvy'.symm)
    obtain rfl := eq_one_of_smul_mem_openCell hcell hfree hy' hv.2
    rw [one_smul] at hv ⊢
    rw [(hp.injOn_openCell hcell hfree i).leftInvOn_invFunOn hy', hpe]
    exact (e.left_inv hv.1).symm
  have hcont : ContinuousAt e.symm (p y) := by
    rw [hpe]
    exact e.continuousAt_symm (e.map_source hye)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · exact Filter.eventually_of_mem (inter_mem_nhdsWithin _
      ((hp.isCoveringMap.isOpenMap V hV).mem_nhds (mem_image_of_mem p hyV)))
      fun z hz ↦ heq ⟨hz.2, hz.1⟩
  · rw [hinv, hpe]
    exact (e.left_inv hye).symm

/-- The characteristic map of an orbit of `n`-cells: the characteristic map of its chosen
representative, followed by the covering map, which is injective on the open cell. -/
private def quotientCellMap (n : ℕ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n)) :
    PartialEquiv (Fin n → ℝ) B :=
  haveI : Nonempty E := ⟨map n o.out 0⟩
  (map n o.out).trans <|
    Set.InjOn.toPartialEquiv p (openCell n o.out) (hp.injOn_openCell hcell hfree o.out)

omit [T2Space E] in
private theorem image_quotientCellMap {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n))
    (S : Set (Fin n → ℝ)) : quotientCellMap hp hcell hfree n o '' S = p '' (map n o.out '' S) :=
  image_comp p (map n o.out) S

omit [T2Space E] in
/-- The chosen representative of the orbit of a cell is a translate of it. -/
private theorem exists_smul_eq_out {n : ℕ} (i : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    ∃ g : G, g • i = (Quotient.mk'' i : MulAction.orbitRel.Quotient G _).out :=
  letI := cellMulAction hcell n
  MulAction.mem_orbit_iff.1 (Quotient.exact' (Quotient.out_eq' (Quotient.mk'' i :
    MulAction.orbitRel.Quotient G (cell (univ : Set E) n))))

omit [T2Space E] in
include hp in
private theorem image_openCell_out {n : ℕ} (i : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    p '' openCell n (Quotient.mk'' i : MulAction.orbitRel.Quotient G _).out =
      p '' openCell n i := by
  let := cellMulAction hcell n
  obtain ⟨g, hg⟩ := exists_smul_eq_out hcell i
  rw [← hg, ← smul_openCell, hp.image_smul_set]

include hp in
private theorem image_closedCell_out {n : ℕ} (i : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    p '' closedCell n (Quotient.mk'' i : MulAction.orbitRel.Quotient G _).out =
      p '' closedCell n i := by
  let := cellMulAction hcell n
  have := hp.toContinuousConstSMul
  obtain ⟨g, hg⟩ := exists_smul_eq_out hcell i
  rw [← hg, ← smul_closedCell, hp.image_smul_set]

omit [T2Space E] in
private theorem source_quotientCellMap {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n)) :
    (quotientCellMap hp hcell hfree n o).source = ball 0 1 := by
  have : Nonempty E := ⟨map n o.out 0⟩
  rw [quotientCellMap, PartialEquiv.trans_source, source_eq, inter_eq_left]
  exact fun x hx ↦ mem_image_of_mem _ hx

private theorem continuousOn_symm_quotientCellMap {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n)) :
    ContinuousOn (quotientCellMap hp hcell hfree n o).symm
      (quotientCellMap hp hcell hfree n o).target := by
  have : Nonempty E := ⟨map n o.out 0⟩
  have hinv := hp.continuousOn_invFunOn_openCell hcell hfree o.out
  have hmaps : MapsTo (invFunOn p (openCell n o.out)) (p '' openCell n o.out)
      (map n o.out).target := by
    rw [target_map_eq_openCell]
    exact (surjOn_image p _).mapsTo_invFunOn
  rw [quotientCellMap, PartialEquiv.coe_trans_symm, PartialEquiv.trans_target]
  exact ((continuousOn_symm n o.out).comp hinv hmaps).mono inter_subset_left

omit [T2Space E] in
private theorem pairwiseDisjoint_quotientCellMap :
    (univ : Set (Σ n, letI := cellMulAction hcell n;
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n))).PairwiseDisjoint
      (fun ni ↦ quotientCellMap hp hcell hfree ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n, o⟩ - ⟨m, o'⟩ - hne
  simp only [onFun, image_quotientCellMap]
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  let := cellMulAction hcell m
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (hp.apply_eq_iff_mem_orbit.1 hxy.symm)
  have hgy : g • y ∈ openCell m (g • o'.out) := smul_mem_openCell_smul hcell g hy
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 <| eq_of_not_disjoint_openCell <|
    not_disjoint_iff.2 ⟨g • y, hx, hgy⟩
  refine hne (Sigma.ext rfl (heq_of_eq ?_))
  rw [← Quotient.out_eq' o, ← Quotient.out_eq' o', eq_of_heq h]
  exact Quotient.sound' (MulAction.mem_orbit _ g)

include hp in
private theorem image_quotientCellMap_mk_closedBall {n : ℕ} (i : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    quotientCellMap hp hcell hfree n (Quotient.mk'' i) '' closedBall 0 1 = p '' closedCell n i := by
  rw [image_quotientCellMap]
  exact image_closedCell_out hp hcell i

omit [T2Space E] in
include hp in
private theorem image_quotientCellMap_mk_ball {n : ℕ} (i : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    quotientCellMap hp hcell hfree n (Quotient.mk'' i) '' ball 0 1 = p '' openCell n i := by
  rw [image_quotientCellMap]
  exact image_openCell_out hp hcell i

private theorem mapsTo_quotientCellMap (n : ℕ)
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n)) :
    ∃ I : Π m, Finset (letI := cellMulAction hcell m;
      MulAction.orbitRel.Quotient G (cell (univ : Set E) m)),
      MapsTo (quotientCellMap hp hcell hfree n o) (sphere 0 1)
        (⋃ (m < n) (j ∈ I m), quotientCellMap hp hcell hfree m j '' closedBall 0 1) := by
  classical
  obtain ⟨I, hI⟩ := CWComplex.mapsTo n o.out
  refine ⟨fun m ↦ letI := cellMulAction hcell m; (I m).image Quotient.mk'', fun x hx ↦ ?_⟩
  obtain ⟨m, hm, j, hj, hxj⟩ := by simpa only [mem_iUnion, exists_prop] using hI hx
  simp only [mem_iUnion, exists_prop]
  refine ⟨m, hm, _, Finset.mem_image_of_mem _ hj, ?_⟩
  rw [image_quotientCellMap_mk_closedBall hp hcell hfree j]
  exact ⟨_, hxj, rfl⟩

private theorem isClosed_of_isClosed_inter_quotientCellMap (A : Set B)
    (hA : ∀ n (o : letI := cellMulAction hcell n;
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n)),
      IsClosed (A ∩ quotientCellMap hp hcell hfree n o '' closedBall 0 1)) : IsClosed A := by
  refine hp.toIsQuotientMap.isClosed_preimage.1 <|
    (CWComplex.closed (univ : Set E) _ (subset_univ _)).2 fun n j ↦ ?_
  have : p ⁻¹' A ∩ closedCell n j =
      closedCell n j ∩ p ⁻¹' (A ∩ quotientCellMap hp hcell hfree n (Quotient.mk'' j) ''
        closedBall 0 1) := by
    rw [image_quotientCellMap_mk_closedBall hp hcell hfree j, preimage_inter, inter_comm,
      ← inter_assoc]
    exact (inter_eq_left.2 (inter_subset_left.trans (subset_preimage_image p _))).symm
  rw [this]
  exact isClosed_closedCell.inter ((hA n _).preimage hp.continuous)

private theorem iUnion_quotientCellMap :
    ⋃ (n : ℕ) (o : letI := cellMulAction hcell n;
      MulAction.orbitRel.Quotient G (cell (univ : Set E) n)),
      quotientCellMap hp hcell hfree n o '' closedBall 0 1 = univ := by
  refine eq_univ_of_forall fun b ↦ ?_
  obtain ⟨x, rfl⟩ := hp.surjective b
  obtain ⟨n, j, hx⟩ := mem_iUnion₂.1 ((CWComplex.union (C := (univ : Set E))).symm ▸ mem_univ x)
  refine mem_iUnion₂.2 ⟨n, Quotient.mk'' j, ?_⟩
  rw [image_quotientCellMap_mk_closedBall hp hcell hfree j]
  exact mem_image_of_mem p hx

/-- **The orbit space of a free cellular action is a CW complex.** Let `p : E → B` be the quotient
covering map of an action of `G` on the Hausdorff CW complex `E` that carries every open `n`-cell
onto an open `n`-cell, and carries an open cell onto itself only by `1`. Then `B` is a CW complex
whose `n`-cells are the `G`-orbits of `n`-cells of `E`
(`IsQuotientCoveringMap.cellQuotientEquiv`). The characteristic map of an orbit is `p ∘ φ`, for
`φ` the characteristic map of the chosen representative of the orbit
(`IsQuotientCoveringMap.map_cellQuotientEquiv_symm`). -/
@[instance_reducible]
def _root_.IsQuotientCoveringMap.cwComplexQuotient : CWComplex (univ : Set B) where
  cell n := letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n)
  map := quotientCellMap hp hcell hfree
  source_eq _ := source_quotientCellMap hp hcell hfree
  continuousOn n o := hp.continuous.comp_continuousOn (continuousOn n o.out)
  continuousOn_symm _ := continuousOn_symm_quotientCellMap hp hcell hfree
  pairwiseDisjoint' := pairwiseDisjoint_quotientCellMap hp hcell hfree
  mapsTo' := mapsTo_quotientCellMap hp hcell hfree
  closed' A _ := isClosed_of_isClosed_inter_quotientCellMap hp hcell hfree A
  union' := iUnion_quotientCellMap hp hcell hfree

/-- The `n`-cells of the orbit space are the `G`-orbits of `n`-cells of `E`. -/
def _root_.IsQuotientCoveringMap.cellQuotientEquiv (n : ℕ) :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    cell (univ : Set B) n ≃ MulAction.orbitRel.Quotient G (cell (univ : Set E) n) :=
  Equiv.refl _

/-- The characteristic map of an orbit of cells is the covering map composed with the
characteristic map of the chosen representative. -/
theorem _root_.IsQuotientCoveringMap.map_cellQuotientEquiv_symm {n : ℕ}
    (o : letI := cellMulAction hcell n; MulAction.orbitRel.Quotient G (cell (univ : Set E) n))
    (x : Fin n → ℝ) :
    letI := hp.cwComplexQuotient hcell hfree
    map n ((hp.cellQuotientEquiv hcell hfree n).symm o) x = p (map n o.out x) :=
  (rfl)

/-- The covering map carries an open cell onto the open cell of its orbit. -/
theorem _root_.IsQuotientCoveringMap.image_openCell {n : ℕ} (i : cell (univ : Set E) n) :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    p '' openCell n i = openCell n ((hp.cellQuotientEquiv hcell hfree n).symm (Quotient.mk'' i)) :=
  (image_quotientCellMap_mk_ball hp hcell hfree i).symm

/-- The covering map carries a closed cell onto the closed cell of its orbit. -/
theorem _root_.IsQuotientCoveringMap.image_closedCell {n : ℕ} (i : cell (univ : Set E) n) :
    letI := hp.cwComplexQuotient hcell hfree
    letI := cellMulAction hcell n
    p '' closedCell n i =
      closedCell n ((hp.cellQuotientEquiv hcell hfree n).symm (Quotient.mk'' i)) :=
  (image_quotientCellMap_mk_closedBall hp hcell hfree i).symm

/-- The covering map carries every skeleton of `E` onto the corresponding skeleton of `B`. -/
theorem _root_.IsQuotientCoveringMap.image_skeletonLT (n : ℕ∞) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    p '' (skeletonLT (univ : Set E) n : Set E) = (skeletonLT (univ : Set B) n : Set B) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.t2Space_of_cwComplex hcell hfree
  let act := cellMulAction hcell
  rw [← CWComplex.iUnion_openCell_eq_skeletonLT, ← CWComplex.iUnion_openCell_eq_skeletonLT,
    image_iUnion₂]
  refine iUnion₂_congr fun m _ ↦ ?_
  let := act m
  rw [image_iUnion]
  simp_rw [hp.image_openCell hcell hfree]
  exact ((hp.cellQuotientEquiv hcell hfree m).symm.surjective.comp
    Quotient.mk''_surjective).iUnion_comp (openCell (C := (univ : Set B)) m)

/-- The covering map preserves every stage of the skeletal filtration. -/
theorem _root_.IsQuotientCoveringMap.mapsTo_skeletonLT (n : ℕ∞) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    MapsTo p (skeletonLT (univ : Set E) n) (skeletonLT (univ : Set B) n) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.t2Space_of_cwComplex hcell hfree
  exact mapsTo_iff_image_subset.2 (hp.image_skeletonLT hcell hfree n).subset

/-- The preimage under the covering map of a skeleton of `B` is the corresponding skeleton of
`E`. -/
theorem _root_.IsQuotientCoveringMap.preimage_skeletonLT (n : ℕ∞) :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    p ⁻¹' (skeletonLT (univ : Set B) n : Set B) = (skeletonLT (univ : Set E) n : Set E) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.t2Space_of_cwComplex hcell hfree
  refine Subset.antisymm (fun x hx ↦ ?_) (hp.mapsTo_skeletonLT hcell hfree n).subset_preimage
  obtain ⟨y, hy, hyx⟩ := (hp.image_skeletonLT hcell hfree n).symm.subset hx
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (hp.apply_eq_iff_mem_orbit.1 hyx.symm)
  exact smul_mem_skeletonLT g (hcell g) hy

/-- **The quotient covering map of a free cellular action is cellular** for the orbit-space CW
structure `IsQuotientCoveringMap.cwComplexQuotient`. -/
theorem _root_.IsQuotientCoveringMap.isCellular_cwComplexQuotient :
    letI := hp.cwComplexQuotient hcell hfree
    haveI := hp.t2Space_of_cwComplex hcell hfree
    IsCellular (univ : Set E) (univ : Set B)
      (TopCat.ofHom ⟨univ.restrictPreimage p, hp.continuous.restrictPreimage⟩) := by
  let := hp.cwComplexQuotient hcell hfree
  have := hp.t2Space_of_cwComplex hcell hfree
  exact fun n _ hx ↦ hp.mapsTo_skeletonLT hcell hfree n hx

end Quotient

section CellLift

variable {B : Type*} [TopologicalSpace B] [CWComplex (univ : Set E)]
  [Group G] [MulAction G E] {p : E → B}

/-- Two `n`-cells of `E` lie in the same `G`-orbit exactly when their open cells have the same
image under the quotient covering map. -/
theorem _root_.IsQuotientCoveringMap.exists_smul_cell_eq_iff_image_openCell_eq
    (hp : IsQuotientCoveringMap p G)
    (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
    {n : ℕ} (i j : cell (univ : Set E) n) :
    letI := cellMulAction hcell n
    (∃ g : G, g • i = j) ↔ p '' openCell n i = p '' openCell n j := by
  let := cellMulAction hcell n
  refine ⟨?_, fun hij ↦ ?_⟩
  · rintro ⟨g, rfl⟩
    rw [← smul_openCell hcell, hp.image_smul_set]
  · have hx : map n i 0 ∈ openCell n i := map_zero_mem_openCell n i
    obtain ⟨z, hz, hzx⟩ := hij ▸ mem_image_of_mem p hx
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (hp.apply_eq_iff_mem_orbit.1 hzx)
    have hgi : (⟨n, j⟩ : Σ m, cell (univ : Set E) m) = ⟨n, g • i⟩ :=
      eq_of_not_disjoint_openCell
        (not_disjoint_iff.2 ⟨g • map n i 0, hz, smul_mem_openCell_smul hcell g hx⟩)
    exact ⟨g, (eq_of_heq (Sigma.mk.inj_iff.1 hgi).2).symm⟩

/-- If a surjective map between CW complexes sends every open cell of `E` onto an open cell of `B`
of the same dimension, then every open cell of `B` is the image of an open cell of `E`. -/
theorem _root_.Function.Surjective.exists_image_openCell_eq [CWComplex (univ : Set B)]
    (hp : Function.Surjective p)
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (b : cell (univ : Set B) n) :
    ∃ i : cell (univ : Set E) n, p '' openCell n i = openCell n b := by
  obtain ⟨x, hx⟩ := hp (map n b 0)
  have hxE : x ∈ ∅ ∪ ⋃ (m : ℕ) (i : cell (univ : Set E) m), openCell m i := by
    rw [RelCWComplex.union_iUnion_openCell_eq_complex]
    exact mem_univ x
  rw [empty_union, mem_iUnion₂] at hxE
  obtain ⟨m, i, hxi⟩ := hxE
  obtain ⟨b', hb'⟩ := hp_cell m i
  have hmb : (⟨m, b'⟩ : Σ k, cell (univ : Set B) k) = ⟨n, b⟩ :=
    eq_of_not_disjoint_openCell
      (not_disjoint_iff.2 ⟨map n b 0, hb' ▸ hx ▸ mem_image_of_mem p hxi, map_zero_mem_openCell n b⟩)
  obtain rfl : m = n := (Sigma.mk.inj_iff.1 hmb).1
  obtain rfl : b' = b := eq_of_heq (Sigma.mk.inj_iff.1 hmb).2
  exact ⟨i, hb'⟩

/-- **Parametrization of the cells of a free cellular cover by chosen lifts of the base cells.**
Given a CW structure on `B` whose open cells are the images of the open cells of `E`, and a lift
`s b` of each `n`-cell `b` of `B`, translating the chosen lifts gives a bijection
`(Σ _ : cell (univ : Set B) n, G) ≃ cell (univ : Set E) n`. -/
def _root_.IsQuotientCoveringMap.sigmaSMulCellLiftEquiv [CWComplex (univ : Set B)]
    (hp : IsQuotientCoveringMap p G)
    (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
    (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      g • openCell n i = openCell n i → g = 1)
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (s : cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : ∀ b, p '' openCell n (s b) = openCell n b) :
    (Σ _ : cell (univ : Set B) n, G) ≃ cell (univ : Set E) n :=
  letI := cellMulAction hcell n
  haveI := isCancelSMul_cell hcell hfree n
  Equiv.ofBijective (fun p ↦ p.2 • s p.1) (by
    refine ⟨?_, fun i ↦ ?_⟩
    · rintro ⟨b₁, g₁⟩ ⟨b₂, g₂⟩ (h : g₁ • s b₁ = g₂ • s b₂)
      have hb : openCell n b₁ = openCell n b₂ := by
        rw [← hs b₁, ← hs b₂, ← hp.image_smul_set g₁, smul_openCell hcell, h,
          ← smul_openCell hcell, hp.image_smul_set]
      obtain rfl : b₁ = b₂ := openCell_congr n hb
      exact Sigma.ext rfl (heq_of_eq (IsCancelSMul.right_cancel g₁ g₂ (s b₁) h))
    · obtain ⟨b, hb⟩ := hp_cell n i
      obtain ⟨g, hg⟩ := (hp.exists_smul_cell_eq_iff_image_openCell_eq hcell (s b) i).2
        ((hs b).trans hb.symm)
      exact ⟨⟨b, g⟩, hg⟩)

/-- Evaluating `IsQuotientCoveringMap.sigmaSMulCellLiftEquiv` at `⟨b, g⟩` translates the chosen
lift `s b` by `g`. -/
@[simp]
theorem _root_.IsQuotientCoveringMap.sigmaSMulCellLiftEquiv_apply [CWComplex (univ : Set B)]
    (hp : IsQuotientCoveringMap p G)
    (hcell : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      ∃ j : cell (univ : Set E) n, g • openCell n i = openCell n j)
    (hfree : ∀ (g : G) (n : ℕ) (i : cell (univ : Set E) n),
      g • openCell n i = openCell n i → g = 1)
    (hp_cell : ∀ (n : ℕ) (i : cell (univ : Set E) n),
      ∃ b : cell (univ : Set B) n, p '' openCell n i = openCell n b)
    {n : ℕ} (s : cell (univ : Set B) n → cell (univ : Set E) n)
    (hs : ∀ b, p '' openCell n (s b) = openCell n b) (b : cell (univ : Set B) n) (g : G) :
    letI := cellMulAction hcell n
    hp.sigmaSMulCellLiftEquiv hcell hfree hp_cell s hs ⟨b, g⟩ = g • s b :=
  (rfl)

end CellLift

end TauCeti

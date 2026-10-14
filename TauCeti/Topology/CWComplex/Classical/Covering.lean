/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.CWComplex.Classical.Finite
public import TauCeti.Topology.CWComplex.Classical.FiniteCWType
public import TauCeti.Topology.Covering.Convex
public import TauCeti.Topology.SeparatedMap

/-!
# Lifting a finite CW structure along a covering map

Let `p : E → B` be a covering map with finite fibres and let `C` be a finite CW complex in `B`.
The closed unit ball is convex, so the characteristic map of each cell of `C` lifts through `p`,
uniquely once the lift of one point is prescribed
(`IsCoveringMap.existsUnique_continuousMap_lifts_of_convex`). Lifting every characteristic map
through every point over the centre of its cell makes `p ⁻¹' C` a finite CW complex
(`TauCeti.cwComplexPreimage`):

* its `n`-cells are the pairs of an `n`-cell `i` of `C` and a point of `E` over the centre
  `map n i 0` (`TauCeti.cellPreimageEquiv`);
* the characteristic map of such a pair lifts the characteristic map of `i`
  (`TauCeti.apply_map_cellPreimageEquiv_symm`) and sends the centre to the chosen point
  (`TauCeti.map_cellPreimageEquiv_symm_zero`).

The open cells of distinct pairs are disjoint because two lifts of one characteristic map that
meet are equal, and every point of `E` over a closed cell of `C` lies on a lift of that cell, which
gives both the boundary condition and the covering of `p ⁻¹' C` by the closed lifted cells. With
finitely many cells the weak topology condition is automatic (`Topology.CWComplex.mkFinite`).

Counting cells, `p ⁻¹' C` has, in each dimension, the sum over the cells of `C` of the number of
points over their centres (`TauCeti.nat_card_cell_preimage`), so `d` times as many cells as `C`
when every fibre over `C` has `d` points (`TauCeti.nat_card_cell_preimage_of_card_fiber`). This is
the input for the multiplicativity of the Euler characteristic in finite covers. In particular the
total space of such a cover of a finite CW complex has finite CW type
(`IsCoveringMap.finiteCWType`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, Proposition 1.33 (the lifting criterion), and the exercises of Section 2.2 on
  the Euler characteristic of an `n`-sheeted covering space.
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

/-- The boundary of a lifted cell lies in the lifted cells of smaller dimension: its image lies in
closed cells of smaller dimension, and every point over such a closed cell lies in a lift of it. -/
private theorem mapsTo_coverCellMap (n : ℕ) (c : CoverCell p C n) :
    MapsTo (coverCellMap hp c) (sphere 0 1)
      (⋃ (m < n) (c' : CoverCell p C m), coverCellMap hp c' '' closedBall 0 1) := by
  intro x hx
  have hxc : x ∈ closedBall 0 1 := sphere_subset_closedBall hx
  obtain ⟨I, hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n c.1
  obtain ⟨m, hm, k, -, y, hy, hyx⟩ := by simpa using hI (mem_image_of_mem _ hx)
  obtain ⟨e₀, he₀⟩ := exists_coverLift_eq hp k ⟨y, hy⟩ (e := coverLiftFun hp c x)
    (by rw [coverLiftFun_apply hp c hxc, ← hyx])
  refine mem_iUnion₂.2 ⟨m, hm, mem_iUnion.2 ⟨⟨k, e₀⟩, y, hy, ?_⟩⟩
  rw [coverCellMap_apply, coverCellMap_apply, coverLiftFun_of_mem hp _ hy, he₀]

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

variable (C) (hp : IsCoveringMap p) (hfin : ∀ b, Finite ↥(p ⁻¹' {b})) [RelCWComplex.Finite C]

omit [TopologicalSpace E] [RelCWComplex.Finite C] in
include hfin in
private theorem finite_coverCell [RelCWComplex.FiniteType C] (n : ℕ) :
    _root_.Finite (CoverCell p C n) :=
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  inferInstance

omit [TopologicalSpace E] [RelCWComplex.Finite C] in
private theorem eventually_isEmpty_coverCell [RelCWComplex.FiniteDimensional C] :
    ∀ᶠ n in Filter.atTop, IsEmpty (CoverCell p C n) :=
  (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := ∅)).mono
    fun _ h ↦ ⟨fun c ↦ h.false c.1⟩

/-- **A finite CW structure lifts along a covering map with finite fibres.** If `C` is a finite CW
complex in `B` and `p : E → B` is a covering map with finite fibres, then `p ⁻¹' C` is a finite CW
complex in `E`. Its `n`-cells are the pairs of an `n`-cell of `C` and a point of `E` over the
centre of that cell (`TauCeti.cellPreimageEquiv`); the characteristic map of such a pair is the
lift of the characteristic map of the cell through `p` sending the centre to the chosen point. -/
@[instance_reducible]
def cwComplexPreimage : CWComplex (p ⁻¹' C) :=
  CWComplex.mkFinite (p ⁻¹' C) (CoverCell p C) (fun _ c ↦ coverCellMap hp c)
    (eventually_isEmpty_coverCell C) (finite_coverCell C hfin) (fun _ _ ↦ rfl)
    (fun _ c ↦ continuousOn_coverCellMap hp c) (fun _ c ↦ continuousOn_symm_coverCellMap hp c)
    (pairwiseDisjoint_coverCellMap hp) (mapsTo_coverCellMap hp) (iUnion_coverCellMap hp)

/-- The lift of a finite CW complex along a covering map with finite fibres is finite. -/
theorem finite_cwComplexPreimage :
    letI := cwComplexPreimage C hp hfin
    RelCWComplex.Finite (p ⁻¹' C) :=
  CWComplex.finite_mkFinite _ _ _ _ _ _ _ _ _ _ _

/-- The `n`-cells of the lift of `C` along `p` are the pairs of an `n`-cell `i` of `C` and a point
of `E` over the centre `map n i 0` of that cell. -/
def cellPreimageEquiv (n : ℕ) :
    letI := cwComplexPreimage C hp hfin
    cell (p ⁻¹' C) n ≃ Σ i : cell C n, p ⁻¹' {map n i 0} :=
  Equiv.refl _

variable {n : ℕ} (c : Σ i : cell C n, p ⁻¹' {map n i 0})

/-- The characteristic maps of `TauCeti.cwComplexPreimage` are the maps `coverCellMap`, by
construction (`Topology.CWComplex.mkFinite` takes the supplied family as its `map` field). -/
private theorem map_cellPreimageEquiv_symm :
    letI := cwComplexPreimage C hp hfin
    map n ((cellPreimageEquiv C hp hfin n).symm c) = coverCellMap hp c :=
  (rfl)

/-- The characteristic map of a lifted cell sends the centre to the chosen point over the centre
of the underlying cell. -/
theorem map_cellPreimageEquiv_symm_zero :
    letI := cwComplexPreimage C hp hfin
    map n ((cellPreimageEquiv C hp hfin n).symm c) 0 = c.2 := by
  rw [map_cellPreimageEquiv_symm, coverCellMap_apply,
    coverLiftFun_of_mem hp c (mem_closedBall_self zero_le_one)]
  exact coverLift_ballCentre hp c

/-- The characteristic map of a lifted cell lifts the characteristic map of the underlying cell
on the closed unit ball. -/
theorem apply_map_cellPreimageEquiv_symm {x : Fin n → ℝ} (hx : x ∈ closedBall 0 1) :
    letI := cwComplexPreimage C hp hfin
    p (map n ((cellPreimageEquiv C hp hfin n).symm c) x) = map n c.1 x := by
  rw [map_cellPreimageEquiv_symm, coverCellMap_apply, coverLiftFun_apply hp c hx]

omit c

/-- The number of `n`-cells of the lift of `C` along `p` is the sum, over the `n`-cells of `C`, of
the number of points over their centres. -/
theorem nat_card_cell_preimage :
    letI := cwComplexPreimage C hp hfin
    Nat.card (cell (p ⁻¹' C) n) = ∑ᶠ i : cell C n, Nat.card ↥(p ⁻¹' {map n i 0}) := by
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := Fintype.ofFinite (cell C n)
  rw [Nat.card_congr (cellPreimageEquiv C hp hfin n), Nat.card_sigma, finsum_eq_sum_of_fintype]

/-- **Cells of a `d`-sheeted cover.** If every fibre of `p` over `C` has `d` points, the lift of `C`
along `p` has `d` times as many `n`-cells as `C`. -/
theorem nat_card_cell_preimage_of_card_fiber {d : ℕ} (hd : ∀ b ∈ C, Nat.card ↥(p ⁻¹' {b}) = d) :
    letI := cwComplexPreimage C hp hfin
    Nat.card (cell (p ⁻¹' C) n) = d * Nat.card (cell C n) := by
  have : _root_.Finite (cell C n) := FiniteType.finite_cell n
  have := Fintype.ofFinite (cell C n)
  have hc (i : cell C n) : Nat.card ↥(p ⁻¹' {map n i 0}) = d :=
    hd _ (closedCell_subset_complex n i (map_zero_mem_closedCell n i))
  rw [nat_card_cell_preimage C hp hfin, finsum_eq_sum_of_fintype]
  simp [hc, mul_comm]

include hp hfin in
/-- The total space of a covering, with finite fibres, of a finite CW complex has finite CW type: it
is a finite CW complex itself. -/
theorem _root_.IsCoveringMap.finiteCWType [T2Space B] [CWComplex (univ : Set B)]
    [RelCWComplex.Finite (univ : Set B)] : FiniteCWType E := by
  let := cwComplexPreimage univ hp hfin
  have := finite_cwComplexPreimage univ hp hfin
  have := hp.t2Space
  exact ((Homeomorph.setCongr (preimage_univ (f := p))).trans
    (Homeomorph.Set.univ E)).symm.finiteCWType

end Structure

end TauCeti

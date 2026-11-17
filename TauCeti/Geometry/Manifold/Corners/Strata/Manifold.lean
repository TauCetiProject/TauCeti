/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Corners.Strata.Basic
import TauCeti.Geometry.Manifold.Boundary.SmoothMap
import TauCeti.Geometry.Manifold.SmoothEmbedding.Extension

/-!
# The smooth manifold structure on depth strata

When the model range `range I` of a real `C^m` manifold with corners `M` (`m ≠ 0`) is cut out by
the nonnegativity of a set `S` of coordinates in a linear coordinate system `L : E ≃L[ℝ] (ι → ℝ)`,
each depth stratum `I.depthStratum M k = {x : M | I.depth x = k}` is a locally closed boundaryless
submanifold of `M` of dimension `dim E - k`.

Near a point `p ∈ I.depthStratum M k`, restricting an ambient chart `e` to the open subset where
the coordinates of `S` strictly positive at `p` remain strictly positive cuts out the stratum by
the vanishing of the `k` coordinates of `S` that vanish at `p`. Deleting those `k` coordinates
gives a chart of `I.depthStratum M k` onto an open subset of
`EuclideanSpace ℝ (Fin (finrank ℝ E - k))`. Transitions between such charts are ambient coordinate
changes precomposed with zero insertion and followed by coordinate deletion, hence are `C^m`.

Thus `I.depthStratum M k` carries a boundaryless `C^m` manifold structure
(`ModelWithCorners.depthStratumChartedSpace`, `ModelWithCorners.isManifold_depthStratum`) for which
the inclusion `Subtype.val : I.depthStratum M k → M` is a `C^m` smooth embedding
(`ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`). Maps into a depth stratum are `C^m`
precisely when their ambient composites are `C^m`
(`ModelWithCorners.contMDiff_iff_comp_subtypeVal_depthStratum`), every `C^m` diffeomorphism induces
a `C^m` diffeomorphism between depth strata (`ModelWithCorners.depthStratumDiffeomorph`) — showing
in particular that the smooth structure does not depend on the choice of `(L, S)` — the depth-zero
stratum is canonically diffeomorphic to the open interior submanifold
(`ModelWithCorners.depthStratumZeroDiffeomorphInterior`), and on a half-space manifold the
depth-one stratum is canonically diffeomorphic to the boundary manifold of
`TauCeti.boundaryChartedSpace` (`ModelWithCorners.depthStratumOneDiffeomorphBoundary`).

## Main definitions

* `ModelWithCorners.depthStratumChartedSpace`: the named, non-instance charted-space structure on
  `I.depthStratum M k` modelled on `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`.
* `ModelWithCorners.depthStratumDiffeomorph`: the `C^m` diffeomorphism between depth strata induced
  by a `C^m` diffeomorphism of ambient manifolds (in particular, independence of `(L, S)`).
* `ModelWithCorners.depthStratumZeroDiffeomorphInterior`: canonical diffeomorphism identifying the
  depth-zero stratum with the open interior submanifold `⟨I.interior M, I.isOpen_interior _⟩`.
* `ModelWithCorners.depthStratumOneDiffeomorphBoundary`: canonical diffeomorphism identifying the
  depth-one stratum of a half-space manifold with its boundary manifold.

## Main results

* `ModelWithCorners.isManifold_depthStratum`: each depth stratum is a boundaryless `C^m` manifold
  of dimension `dim E - k`.
* `ModelWithCorners.isImmersion_subtypeVal_depthStratum`,
  `ModelWithCorners.isSmoothEmbedding_subtypeVal_depthStratum`,
  `ModelWithCorners.contMDiff_subtypeVal_depthStratum`,
  `ModelWithCorners.injective_mfderiv_subtypeVal_depthStratum`: the inclusion of a depth stratum
  into `M` is a `C^m` smooth embedding.
* `ModelWithCorners.contMDiffWithinAt_iff_comp_subtypeVal_depthStratum`,
  `ModelWithCorners.contMDiff_iff_comp_subtypeVal_depthStratum`: universal property of smooth maps
  into a depth stratum.

## References

* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (depth strata of manifolds with corners).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*.
-/

public section

noncomputable section

open Set Filter Function Module Topology
open scoped Manifold ContDiff

namespace ModelWithCorners

/-! ### Coordinate slices and depth-stratum charts -/

section CoordSlice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Finite ι]

/-- The finite set of coordinates in `S` vanishing at a point `y : E`. -/
private def vanishSet (L : E ≃L[ℝ] (ι → ℝ)) (S : Set ι) (y : E) : Finset ι :=
  letI := Fintype.ofFinite ι
  letI := Classical.decPred (· ∈ S)
  Finset.univ.filter fun i ↦ i ∈ S ∧ L y i = 0

/-- The finite set of coordinates in `S` strictly positive at a point `y : E`. -/
private def posSet (L : E ≃L[ℝ] (ι → ℝ)) (S : Set ι) (y : E) : Finset ι :=
  letI := Fintype.ofFinite ι
  letI := Classical.decPred (· ∈ S)
  Finset.univ.filter fun i ↦ i ∈ S ∧ 0 < L y i

private theorem mem_vanishSet (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι} {y : E} {i : ι} :
    i ∈ vanishSet L S y ↔ i ∈ S ∧ L y i = 0 := by
  let _ := Fintype.ofFinite ι
  simp [vanishSet]

private theorem mem_posSet (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι} {y : E} {i : ι} :
    i ∈ posSet L S y ↔ i ∈ S ∧ 0 < L y i := by
  let _ := Fintype.ofFinite ι
  simp [posSet]

/-- The dimension of `E` equals `Fintype.card ι` via `L : E ≃L[ℝ] (ι → ℝ)`. -/
private theorem finrank_eq_card_of_equiv (L : E ≃L[ℝ] (ι → ℝ)) :
    letI := Fintype.ofFinite ι
    finrank ℝ E = Fintype.card ι := by
  let _ := Fintype.ofFinite ι
  rw [L.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- Equivalence enumerating the coordinates outside `Z` by `Fin (finrank ℝ E - k)` when
`Z.card = k`. -/
private def complEquiv (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k) :
    {i : ι // i ∉ Z} ≃ Fin (finrank ℝ E - k) :=
  letI := Fintype.ofFinite ι
  letI := Classical.decEq ι
  Fintype.equivFinOfCardEq <| by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, finrank_eq_card_of_equiv L, hk]

/-- Equivalence enumerating the coordinates in `Z` by `Fin k` when `Z.card = k`. -/
private def memEquiv (Z : Finset ι) {k : ℕ} (hk : Z.card = k) : {i : ι // i ∈ Z} ≃ Fin k :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hk])

open scoped Classical in
/-- The continuous linear equivalence splitting `E` into the coordinates outside `Z` (parametrized
by `EuclideanSpace ℝ (Fin (finrank ℝ E - k))`) and the coordinates in `Z` (parametrized by
`EuclideanSpace ℝ (Fin k)`). -/
private def sliceEquiv (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k) :
    (EuclideanSpace ℝ (Fin (finrank ℝ E - k)) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ] E :=
  haveI : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ L.symm fun i ↦
        if hi : i ∉ Z then p.1 (complEquiv L Z hk ⟨i, hi⟩)
        else p.2 (memEquiv Z hk ⟨i, not_not.1 hi⟩)
      invFun := fun y ↦
        (WithLp.toLp 2 fun j ↦ L y ((complEquiv L Z hk).symm j).1,
         WithLp.toLp 2 fun j ↦ L y ((memEquiv Z hk).symm j).1)
      map_add' := fun p q ↦ by
        rw [← map_add]
        congr 1
        ext i
        by_cases hi : i ∈ Z <;> simp [hi]
      map_smul' := fun c p ↦ by
        rw [← map_smul]
        congr 1
        ext i
        by_cases hi : i ∈ Z <;> simp [hi]
      left_inv := fun ⟨z, w⟩ ↦ by
        refine Prod.ext ?_ ?_
        · ext j
          have hj : ((complEquiv L Z hk).symm j).1 ∉ Z := ((complEquiv L Z hk).symm j).2
          simp [hj]
        · ext j
          simp
      right_inv := fun y ↦ by
        apply L.injective
        rw [L.apply_symm_apply]
        ext i
        by_cases hi : i ∉ Z
        · simp [hi]
        · simp [hi] }

/-- Insert zeros at the coordinates in `Z` and place the entries of `z` in the remaining
coordinates. -/
private def sliceParam (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k) :
    EuclideanSpace ℝ (Fin (finrank ℝ E - k)) →L[ℝ] E :=
  (sliceEquiv L Z hk).toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      (EuclideanSpace ℝ (Fin k)))

/-- Delete the coordinates in `Z` and read the remaining coordinates in
`EuclideanSpace ℝ (Fin (finrank ℝ E - k))`. -/
private def sliceProj (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k) :
    E →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ E - k)) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - k)))
      (EuclideanSpace ℝ (Fin k))).comp
    (sliceEquiv L Z hk).symm.toContinuousLinearMap

private theorem sliceEquiv_zero (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k)
    (z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))) :
    sliceEquiv L Z hk (z, 0) = sliceParam L Z hk z :=
  rfl

private theorem apply_sliceParam_of_mem (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ}
    (hk : Z.card = k) (z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))) {i : ι} (hi : i ∈ Z) :
    L (sliceParam L Z hk z) i = 0 := by
  have hnot : ¬ (i ∉ Z) := not_not.2 hi
  simp [sliceParam, sliceEquiv, hnot]

private theorem sliceProj_sliceParam (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k)
    (z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))) :
    sliceProj L Z hk (sliceParam L Z hk z) = z := by
  simp [sliceProj, sliceParam]

private theorem sliceParam_sliceProj (L : E ≃L[ℝ] (ι → ℝ)) (Z : Finset ι) {k : ℕ} (hk : Z.card = k)
    {y : E} (hy : ∀ i ∈ Z, L y i = 0) :
    sliceParam L Z hk (sliceProj L Z hk y) = y := by
  apply L.injective
  ext i
  by_cases hi : i ∈ Z
  · rw [apply_sliceParam_of_mem L Z hk _ hi, hy i hi]
  · simp [sliceParam, sliceProj, sliceEquiv, hi]

end CoordSlice

section StrataCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}

/-- The cardinality of `vanishSet L S y` equals `I.depthAt y` for `y ∈ range I`. -/
private theorem card_vanishSet (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) {y : E}
    (hy : y ∈ range I) : (vanishSet L S y).card = I.depthAt y := by
  let _ := Fintype.ofFinite ι
  classical
  rw [depthAt_eq_natCard_of_range_eq_equiv L hI hy, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 1

section OpenSet

variable {M : Type*} [TopologicalSpace M]

/-- The open subset of an ambient chart `e` on which every coordinate in `S` that is strictly
positive at `p` remains strictly positive. -/
private def stratumOpen (S : Set ι) (e : OpenPartialHomeomorph M H) (p : M) : Set M :=
  {q ∈ e.source | ∀ i ∈ posSet L S (e.extend I p), 0 < L (e.extend I q) i}

private theorem mem_stratumOpen_self {e : OpenPartialHomeomorph M H} {p : M}
    (hp : p ∈ e.source) : p ∈ stratumOpen (I := I) L S e p :=
  ⟨hp, fun _ hi ↦ ((mem_posSet L).1 hi).2⟩

private theorem isOpen_stratumOpen {e : OpenPartialHomeomorph M H} {p : M} :
    IsOpen (stratumOpen (I := I) L S e p) := by
  have hopen : IsOpen {y : E | ∀ i ∈ posSet L S (e.extend I p), 0 < L y i} := by
    convert isOpen_biInter_finset (s := posSet L S (e.extend I p)) fun i _ ↦
      isOpen_lt (continuous_const : Continuous fun _ : E ↦ (0 : ℝ))
        ((continuous_apply i).comp L.continuous) using 1
    ext y
    simp
  have h := (e.continuousOn_extend (I := I)).isOpen_inter_preimage
    (e.isOpen_extend_source (I := I)) hopen
  simpa only [stratumOpen, OpenPartialHomeomorph.extend_source, inter_def, mem_preimage,
    mem_ofPred_eq] using h

/-- On `stratumOpen L S e p`, no new coordinates of `S` can vanish: the vanishing set at `q` is a
subset of the vanishing set at `p`. -/
private theorem vanishSet_subset_of_mem_stratumOpen (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {e : OpenPartialHomeomorph M H} {p q : M}
    (hq : q ∈ stratumOpen (I := I) L S e p) :
    vanishSet L S (e.extend I q) ⊆ vanishSet L S (e.extend I p) := by
  intro i hi
  obtain ⟨hiS, hqi⟩ := (mem_vanishSet L).1 hi
  refine (mem_vanishSet L).2 ⟨hiS, ?_⟩
  have hnonneg : 0 ≤ L (e.extend I p) i := by
    have hmem : e.extend I p ∈ range I := by
      rw [e.extend_coe]
      exact mem_range_self _
    rw [hI] at hmem
    exact hmem i hiS
  by_contra hne
  have hpos : i ∈ posSet L S (e.extend I p) :=
    (mem_posSet L).2 ⟨hiS, lt_of_le_of_ne hnonneg (Ne.symm hne)⟩
  exact (hq.2 i hpos).ne' hqi

end OpenSet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Within `stratumOpen L S e p`, a point has the same depth as `p` precisely when all coordinates
in `vanishSet L S (e.extend I p)` vanish there. -/
private theorem depth_eq_iff_forall_vanish_of_mem_stratumOpen
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    {p q : M} (hp : p ∈ e.source) (hq : q ∈ stratumOpen (I := I) L S e p) :
    I.depth q = I.depth p ↔ ∀ i ∈ vanishSet L S (e.extend I p), L (e.extend I q) i = 0 := by
  have : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  have hsub := vanishSet_subset_of_mem_stratumOpen L hI hq
  rw [← depthAt_extend_eq_depth one_ne_zero he hq.1, ← depthAt_extend_eq_depth one_ne_zero he hp,
    ← card_vanishSet L hI (by rw [e.extend_coe]; exact mem_range_self _),
    ← card_vanishSet L hI (by rw [e.extend_coe]; exact mem_range_self _)]
  constructor
  · intro hcard i hi
    have heq : vanishSet L S (e.extend I q) = vanishSet L S (e.extend I p) :=
      Finset.eq_of_subset_of_card_le hsub hcard.ge
    exact ((mem_vanishSet L).1 (heq ▸ hi)).2
  · intro hvan
    have heq : vanishSet L S (e.extend I q) = vanishSet L S (e.extend I p) := by
      refine Finset.Subset.antisymm hsub fun i hi ↦ ?_
      exact (mem_vanishSet L).2 ⟨((mem_vanishSet L).1 hi).1, hvan i hi⟩
    rw [heq]

/-- For a chart `e` and a point `p ∈ I.depthStratum M k` in `e.source`, the vanishing set of
`e.extend I p` has cardinality `k`. -/
private theorem card_vanishSet_extend (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {k : ℕ} {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    {p : I.depthStratum M k} (hp : p.1 ∈ e.source) :
    (vanishSet L S (e.extend I p.1)).card = k := by
  have : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  rw [card_vanishSet L hI (by rw [e.extend_coe]; exact mem_range_self _),
    depthAt_extend_eq_depth one_ne_zero he hp]
  exact mem_depthStratum.1 p.2

/-- A point on the coordinate slice of `vanishSet L S (e.extend I p)` whose coordinates in
`posSet L S (e.extend I p)` are positive lies in `range I`. -/
private theorem sliceParam_mem_range_of_pos (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] {k : ℕ} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) {p : I.depthStratum M k} (hp : p.1 ∈ e.source)
    {z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))}
    (hpos : ∀ i ∈ posSet L S (e.extend I p.1),
      0 < L (sliceParam L (vanishSet L S (e.extend I p.1))
        (card_vanishSet_extend L hI he hp) z) i) :
    sliceParam L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp) z ∈
      range I := by
  rw [hI]
  intro i hiS
  by_cases h0 : L (e.extend I p.1) i = 0
  · rw [apply_sliceParam_of_mem L _ _ _ ((mem_vanishSet L).2 ⟨hiS, h0⟩)]
  · have hnonneg : 0 ≤ L (e.extend I p.1) i := by
      have hmem : e.extend I p.1 ∈ range I := by
        rw [e.extend_coe]
        exact mem_range_self _
      rw [hI] at hmem
      exact hmem i hiS
    have hlt : 0 < L (e.extend I p.1) i := lt_of_le_of_ne hnonneg (Ne.symm h0)
    exact (hpos i ((mem_posSet L).2 ⟨hiS, hlt⟩)).le

/-- The open target of the depth-stratum chart around `p` induced by an ambient chart `e`. -/
private def stratumChartTarget (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {k : ℕ} {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : I.depthStratum M k) (hp : p.1 ∈ e.source) :
    Set (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) :=
  let Z := vanishSet L S (e.extend I p.1)
  let hk := card_vanishSet_extend L hI he hp
  {z | I.symm (sliceParam L Z hk z) ∈ e.target ∧
    ∀ i ∈ posSet L S (e.extend I p.1), 0 < L (sliceParam L Z hk z) i}

private theorem isOpen_stratumChartTarget (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] {k : ℕ} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (p : I.depthStratum M k) (hp : p.1 ∈ e.source) :
    IsOpen (stratumChartTarget L hI he p hp) := by
  let Z := vanishSet L S (e.extend I p.1)
  let hk := card_vanishSet_extend L hI he hp
  have h1 : IsOpen {z | I.symm (sliceParam L Z hk z) ∈ e.target} :=
    e.open_target.preimage (I.continuous_symm.comp (sliceParam L Z hk).continuous)
  have h2 : IsOpen {z | ∀ i ∈ posSet L S (e.extend I p.1), 0 < L (sliceParam L Z hk z) i} := by
    convert isOpen_biInter_finset (s := posSet L S (e.extend I p.1)) fun i _ ↦
      isOpen_lt (continuous_const : Continuous fun _ : _ ↦ (0 : ℝ))
        (((continuous_apply i).comp L.continuous).comp (sliceParam L Z hk).continuous) using 1
    ext z
    simp
  exact h1.inter h2

private theorem sliceParam_mem_extend_target (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] {k : ℕ} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (p : I.depthStratum M k) (hp : p.1 ∈ e.source)
    {z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))} (hz : z ∈ stratumChartTarget L hI he p hp) :
    sliceParam L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp) z ∈
      (e.extend I).target := by
  rw [e.extend_target]
  exact ⟨hz.1, sliceParam_mem_range_of_pos L hI he hp hz.2⟩

private theorem extend_symm_sliceParam_mem (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] {k : ℕ} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (p : I.depthStratum M k) (hp : p.1 ∈ e.source)
    {z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))} (hz : z ∈ stratumChartTarget L hI he p hp) :
    (e.extend I).symm
        (sliceParam L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp) z) ∈
      stratumOpen (I := I) L S e p.1 ∧
    (e.extend I).symm
        (sliceParam L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp) z) ∈
      I.depthStratum M k := by
  let Z := vanishSet L S (e.extend I p.1)
  let hk := card_vanishSet_extend L hI he hp
  have htgt := sliceParam_mem_extend_target L hI he p hp hz
  have hsrc : (e.extend I).symm (sliceParam L Z hk z) ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target htgt
  have hrinv : e.extend I ((e.extend I).symm (sliceParam L Z hk z)) = sliceParam L Z hk z :=
    (e.extend I).right_inv htgt
  have hopen : (e.extend I).symm (sliceParam L Z hk z) ∈ stratumOpen (I := I) L S e p.1 :=
    ⟨hsrc, fun i hi ↦ by rw [hrinv]; exact hz.2 i hi⟩
  refine ⟨hopen, ?_⟩
  rw [mem_depthStratum,
    (depth_eq_iff_forall_vanish_of_mem_stratumOpen L hI he hp hopen).2 fun i hi ↦ by
      rw [hrinv]
      exact apply_sliceParam_of_mem L Z hk z hi]
  exact mem_depthStratum.1 p.2

open scoped Classical in
/-- The depth-stratum chart around `p ∈ I.depthStratum M k` induced by an ambient chart `e` of
the `C¹` maximal atlas containing `p`: restrict to `stratumOpen L S e p`, read through `e.extend I`,
and delete the `k` coordinates of `S` vanishing at `p`. -/
private def stratumChart (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {k : ℕ} {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : I.depthStratum M k) (hp : p.1 ∈ e.source) :
    OpenPartialHomeomorph (I.depthStratum M k) (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) where
  toFun q := sliceProj L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp)
    (e.extend I q.1)
  invFun z :=
    if hz : z ∈ stratumChartTarget L hI he p hp then
      ⟨(e.extend I).symm (sliceParam L (vanishSet L S (e.extend I p.1))
        (card_vanishSet_extend L hI he hp) z),
        (extend_symm_sliceParam_mem L hI he p hp hz).2⟩
    else p
  source := Subtype.val ⁻¹' stratumOpen (I := I) L S e p.1
  target := stratumChartTarget L hI he p hp
  map_source' q hq := by
    have hvan : ∀ i ∈ vanishSet L S (e.extend I p.1), L (e.extend I q.1) i = 0 :=
      (depth_eq_iff_forall_vanish_of_mem_stratumOpen L hI he hp hq).1
        ((mem_depthStratum.1 q.2).trans (mem_depthStratum.1 p.2).symm)
    have hrec := sliceParam_sliceProj L (vanishSet L S (e.extend I p.1))
      (card_vanishSet_extend L hI he hp) hvan
    refine ⟨?_, fun i hi ↦ by rw [hrec]; exact hq.2 i hi⟩
    rw [hrec]
    exact (e.extend_target (I := I) ▸ (e.extend I).map_source (by simpa using hq.1)).1
  map_target' z hz := by
    simp only [mem_preimage, dite_eq_left hz]
    exact (extend_symm_sliceParam_mem L hI he p hp hz).1
  left_inv' q hq := by
    have hvan : ∀ i ∈ vanishSet L S (e.extend I p.1), L (e.extend I q.1) i = 0 :=
      (depth_eq_iff_forall_vanish_of_mem_stratumOpen L hI he hp hq).1
        ((mem_depthStratum.1 q.2).trans (mem_depthStratum.1 p.2).symm)
    have hrec := sliceParam_sliceProj L (vanishSet L S (e.extend I p.1))
      (card_vanishSet_extend L hI he hp) hvan
    have hmem : sliceProj L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp)
        (e.extend I q.1) ∈ stratumChartTarget L hI he p hp := by
      refine ⟨?_, fun i hi ↦ by rw [hrec]; exact hq.2 i hi⟩
      rw [hrec]
      exact (e.extend_target (I := I) ▸ (e.extend I).map_source (by simpa using hq.1)).1
    ext
    simp only [dite_eq_left hmem, hrec]
    exact (e.extend I).left_inv (by simpa using hq.1)
  right_inv' z hz := by
    simp only [dite_eq_left hz]
    rw [(e.extend I).right_inv (sliceParam_mem_extend_target L hI he p hp hz),
      sliceProj_sliceParam]
  open_source := (isOpen_stratumOpen L).preimage continuous_subtype_val
  open_target := isOpen_stratumChartTarget L hI he p hp
  continuousOn_toFun :=
    (sliceProj L _ _).continuous.comp_continuousOn <|
      (e.continuousOn_extend (I := I)).comp continuous_subtype_val.continuousOn
        fun q hq ↦ by simpa only [OpenPartialHomeomorph.extend_source] using hq.1
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ContinuousOn.congr
      ((e.continuousOn_extend_symm (I := I)).comp (sliceParam L _ _).continuous.continuousOn
        fun z hz ↦ sliceParam_mem_extend_target L hI he p hp hz) fun z hz ↦ ?_
    simp [hz]

private theorem stratumChart_source (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {k : ℕ} {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : I.depthStratum M k) (hp : p.1 ∈ e.source) :
    (stratumChart L hI he p hp).source = Subtype.val ⁻¹' stratumOpen (I := I) L S e p.1 :=
  rfl

private theorem stratumChart_apply (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M]
    {k : ℕ} {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : I.depthStratum M k) (hp : p.1 ∈ e.source) (q : I.depthStratum M k) :
    stratumChart L hI he p hp q =
      sliceProj L (vanishSet L S (e.extend I p.1)) (card_vanishSet_extend L hI he hp)
        (e.extend I q.1) :=
  rfl

private theorem coe_stratumChart_symm_apply (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] {k : ℕ} {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (p : I.depthStratum M k) (hp : p.1 ∈ e.source)
    {z : EuclideanSpace ℝ (Fin (finrank ℝ E - k))}
    (hz : z ∈ (stratumChart L hI he p hp).target) :
    ((stratumChart L hI he p hp).symm z : M) =
      (e.extend I).symm (sliceParam L (vanishSet L S (e.extend I p.1))
        (card_vanishSet_extend L hI he hp) z) := by
  classical
  have hz' : z ∈ stratumChartTarget L hI he p hp := hz
  change (if h : z ∈ stratumChartTarget L hI he p hp then _ else p).1 = _
  rw [dite_eq_left hz']

/-! ### The manifold structure on depth strata -/

variable (I M) in
/-- The named, non-instance charted-space structure on the depth-`k` stratum `I.depthStratum M k`
of a `C¹` manifold `M` whose model range is cut out by nonnegative coordinates under
`L : E ≃L[ℝ] (ι → ℝ)`. Each preferred chart restricts the preferred ambient chart to the open
subset where coordinates positive at `p` stay positive and deletes the `k` vanishing coordinates.
The implementation is opaque; use the characteristic lemmas below to reason about its atlas and
charts. -/
@[irreducible]
def depthStratumChartedSpace (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) [IsManifold I 1 M] (k : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (I.depthStratum M k) where
  atlas := range fun p : I.depthStratum M k ↦
    stratumChart L hI (IsManifold.chart_mem_maximalAtlas p.1) p (mem_chart_source H p.1)
  chartAt p :=
    stratumChart L hI (IsManifold.chart_mem_maximalAtlas p.1) p (mem_chart_source H p.1)
  mem_chart_source p := mem_stratumOpen_self L (mem_chart_source H p.1)
  chart_mem_atlas p := mem_range_self p

private theorem depthStratumChartedSpace_chartAt (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] (k : ℕ) (p : I.depthStratum M k) :
    letI := I.depthStratumChartedSpace M L hI k
    chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p =
      stratumChart L hI (IsManifold.chart_mem_maximalAtlas p.1) p (mem_chart_source H p.1) := by
  unfold depthStratumChartedSpace
  rfl

/-- The atlas of `depthStratumChartedSpace` is the range of its preferred charts. -/
theorem depthStratumChartedSpace_atlas (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] (k : ℕ) :
    letI := I.depthStratumChartedSpace M L hI k
    atlas (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) (I.depthStratum M k) =
      range fun p : I.depthStratum M k ↦
        chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p := by
  unfold atlas depthStratumChartedSpace chartAt
  rfl

/-- The source of the preferred depth-stratum chart at `p` consists of the points of the stratum in
the ambient preferred chart at `p` where every coordinate of `S` strictly positive at `p` remains
strictly positive. -/
theorem depthStratumChartedSpace_chartAt_source (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] (k : ℕ) (p : I.depthStratum M k) :
    letI := I.depthStratumChartedSpace M L hI k
    (chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p).source =
      {q : I.depthStratum M k | q.1 ∈ (chartAt H p.1).source ∧
        ∀ i ∈ S, 0 < L (extChartAt I p.1 p.1) i → 0 < L (extChartAt I p.1 q.1) i} := by
  let _ := I.depthStratumChartedSpace M L hI k
  rw [depthStratumChartedSpace_chartAt, stratumChart_source]
  ext q
  simp only [mem_preimage, stratumOpen, mem_ofPred_eq, mem_posSet, extChartAt]
  exact and_congr_right fun _ ↦
    ⟨fun h i hiS hpos ↦ h i ⟨hiS, hpos⟩, fun h i ⟨hiS, hpos⟩ ↦ h i hiS hpos⟩

/-- The transition map between two depth-stratum charts is `C^m`: it is an ambient coordinate
change precomposed with zero insertion and followed by coordinate deletion. -/
private theorem contDiffOn_stratumChart_symm_trans (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : WithTop ℕ∞} (hm : m ≠ 0) [IsManifold I m M] {k : ℕ}
    {e₁ e₂ : OpenPartialHomeomorph M H}
    (he₁ : e₁ ∈ IsManifold.maximalAtlas I m M) (he₂ : e₂ ∈ IsManifold.maximalAtlas I m M)
    (p₁ p₂ : I.depthStratum M k) (hp₁ : p₁.1 ∈ e₁.source) (hp₂ : p₂.1 ∈ e₂.source) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    let he₁' : e₁ ∈ IsManifold.maximalAtlas I 1 M :=
      IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.2 hm) he₁
    let he₂' : e₂ ∈ IsManifold.maximalAtlas I 1 M :=
      IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.2 hm) he₂
    ContDiffOn ℝ m
      ((stratumChart L hI he₁' p₁ hp₁).symm ≫ₕ stratumChart L hI he₂' p₂ hp₂)
      ((stratumChart L hI he₁' p₁ hp₁).symm ≫ₕ stratumChart L hI he₂' p₂ hp₂).source := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let he₁' : e₁ ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.2 hm) he₁
  let he₂' : e₂ ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.2 hm) he₂
  let c₁ := stratumChart L hI he₁' p₁ hp₁
  let c₂ := stratumChart L hI he₂' p₂ hp₂
  let Z₁ := vanishSet L S (e₁.extend I p₁.1)
  let Z₂ := vanishSet L S (e₂.extend I p₂.1)
  let hk₁ := card_vanishSet_extend L hI he₁' hp₁
  let hk₂ := card_vanishSet_extend L hI he₂' hp₂
  have hcoord : ContDiffOn ℝ m (I.extendCoordChange e₁ e₂) (I.extendCoordChange e₁ e₂).source :=
    I.contDiffOn_extendCoordChange he₁ he₂
  have hmaps : MapsTo (sliceParam L Z₁ hk₁) (c₁.symm ≫ₕ c₂).source
      (I.extendCoordChange e₁ e₂).source := by
    intro z hz
    have hz₁ : z ∈ c₁.target := hz.1
    have hz₂ : c₁.symm z ∈ c₂.source := hz.2
    have hq₁ : (c₁.symm z : M) ∈ e₁.source := (c₁.map_target hz₁).1
    have hq₂ : (c₁.symm z : M) ∈ e₂.source := hz₂.1
    rw [← OpenPartialHomeomorph.extend_image_source_inter]
    refine ⟨(c₁.symm z : M), ⟨hq₁, hq₂⟩, ?_⟩
    rw [coe_stratumChart_symm_apply L hI he₁' p₁ hp₁ hz₁,
      (e₁.extend I).right_inv (sliceParam_mem_extend_target L hI he₁' p₁ hp₁ hz₁)]
  refine ContDiffOn.congr
    ((sliceProj L Z₂ hk₂).contDiff.comp_contDiffOn
      (hcoord.comp (sliceParam L Z₁ hk₁).contDiff.contDiffOn hmaps)) fun z hz ↦ ?_
  have hz₁ : z ∈ c₁.target := hz.1
  simp only [OpenPartialHomeomorph.coe_trans, comp_apply, stratumChart_apply]
  rw [coe_stratumChart_symm_apply L hI he₁' p₁ hp₁ hz₁]
  simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
    OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, comp_apply]
  rfl

/-- **Each depth stratum of a `C^m` manifold with corners is a boundaryless `C^m` manifold** of
dimension `dim E - k`. -/
theorem isManifold_depthStratum (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : WithTop ℕ∞} (hm : m ≠ 0) [IsManifold I m M] (k : ℕ) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) m (I.depthStratum M k) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  refine isManifold_of_contDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) m
    (I.depthStratum M k) ?_
  rw [depthStratumChartedSpace_atlas]
  rintro f₁ f₂ ⟨p₁, rfl⟩ ⟨p₂, rfl⟩
  simpa only [depthStratumChartedSpace_chartAt, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, preimage_id_eq, inter_univ, id_comp, comp_id,
    id_eq] using
    contDiffOn_stratumChart_symm_trans L hI hm
      (IsManifold.chart_mem_maximalAtlas p₁.1) (IsManifold.chart_mem_maximalAtlas p₂.1)
      p₁ p₂ (mem_chart_source H p₁.1) (mem_chart_source H p₂.1)

/-- **The inclusion of a depth stratum into the ambient manifold is a `C^m` immersion.** In the
preferred stratum and ambient charts at `p`, it is the linear insertion of zeros at the `k`
coordinates vanishing at `p`, with complement `EuclideanSpace ℝ (Fin k)`. -/
theorem isImmersion_subtypeVal_depthStratum (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : WithTop ℕ∞} (hm : m ≠ 0) [IsManifold I m M] (k : ℕ) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    Manifold.IsImmersion 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I m
      (Subtype.val : I.depthStratum M k → M) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  let _ := I.isManifold_depthStratum (M := M) L hI hm k
  apply Manifold.IsImmersionOfComplement.isImmersion (F := EuclideanSpace ℝ (Fin k))
  intro p
  let Z := vanishSet L S ((chartAt H p.1).extend I p.1)
  let hk := card_vanishSet_extend L hI (IsManifold.chart_mem_maximalAtlas p.1)
    (mem_chart_source H p.1)
  apply Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (sliceEquiv L Z hk)
    (chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p)
    (chartAt H p.1)
    (mem_chart_source _ p) (mem_chart_source H p.1)
    (IsManifold.chart_mem_maximalAtlas p) (IsManifold.chart_mem_maximalAtlas p.1)
  intro z hz
  rw [OpenPartialHomeomorph.extend_target] at hz
  have hzdom : z ∈ (chartAt (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) p).target := by
    simpa only [modelWithCornersSelf_coe_symm, preimage_id_eq, id_eq] using hz.1
  rw [depthStratumChartedSpace_chartAt] at hzdom
  simp only [comp_apply, OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe_symm,
    id_eq, depthStratumChartedSpace_chartAt]
  rw [coe_stratumChart_symm_apply L hI (IsManifold.chart_mem_maximalAtlas p.1) p
      (mem_chart_source H p.1) hzdom,
    ((chartAt H p.1).extend I).right_inv
      (sliceParam_mem_extend_target L hI (IsManifold.chart_mem_maximalAtlas p.1) p
        (mem_chart_source H p.1) hzdom),
    sliceEquiv_zero]

/-- **The inclusion of a depth stratum into the ambient manifold is a `C^m` smooth embedding.** -/
theorem isSmoothEmbedding_subtypeVal_depthStratum (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : WithTop ℕ∞} (hm : m ≠ 0) [IsManifold I m M] (k : ℕ) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    Manifold.IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I m
      (Subtype.val : I.depthStratum M k → M) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  exact ⟨isImmersion_subtypeVal_depthStratum L hI hm k, Topology.IsEmbedding.subtypeVal⟩

/-- The inclusion of a depth stratum into the ambient manifold is `C^m`. -/
theorem contMDiff_subtypeVal_depthStratum (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : WithTop ℕ∞} (hm : m ≠ 0) [IsManifold I m M] (k : ℕ) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I m
      (Subtype.val : I.depthStratum M k → M) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  exact (isSmoothEmbedding_subtypeVal_depthStratum L hI hm k).contMDiff

/-- The inclusion of a depth stratum has injective manifold derivative at every point. -/
theorem injective_mfderiv_subtypeVal_depthStratum (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    [IsManifold I 1 M] (k : ℕ) (p : I.depthStratum M k) :
    letI := I.depthStratumChartedSpace M L hI k
    Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) I
      (Subtype.val : I.depthStratum M k → M) p) := by
  let _ := I.depthStratumChartedSpace M L hI k
  exact (isImmersion_subtypeVal_depthStratum L hI one_ne_zero k).mfderiv_injective one_ne_zero p

/-! ### Universal property and canonicality of the smooth structure -/

section Universal

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]

/-- **Universal property of a depth stratum:** a map into `I.depthStratum M k` is `C^m` within a
set (`m ≠ 0`) precisely when its composite with `Subtype.val : I.depthStratum M k → M` is `C^m`
within that set. -/
theorem contMDiffWithinAt_iff_comp_subtypeVal_depthStratum
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M]
    (k : ℕ) {f : X → I.depthStratum M k} {s : Set X} {x : X} :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiffWithinAt IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) m f s x ↔
      ContMDiffWithinAt IX I m (Subtype.val ∘ f) s x := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  let _ := I.isManifold_depthStratum (M := M) L hI hm k
  have hi := isSmoothEmbedding_subtypeVal_depthStratum (I := I) (M := M) L hI hm k
  refine ⟨fun hf ↦ hi.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hf, fun hf ↦ ?_⟩
  obtain ⟨V, hV, hxV, r, hr, hrf⟩ :=
    (hi.isImmersion.isImmersionAt (f x)).exists_contMDiffOn_retraction hi.isEmbedding
  have hrc := (hr _ hxV).contMDiffAt (hV.mem_nhds hxV)
  have hh := hrc.comp_contMDiffWithinAt x hf
  apply hh.congr_of_eventuallyEq
  · filter_upwards [hf.continuousWithinAt.preimage_mem_nhdsWithin (hV.mem_nhds hxV)] with y hy
    exact (hrf (f y) hy).symm
  · exact (hrf (f x) hxV).symm

/-- Smoothness of a map into a depth stratum can be checked after composing with the inclusion
into the ambient manifold. -/
theorem contMDiff_iff_comp_subtypeVal_depthStratum
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i}) {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M]
    (k : ℕ) {f : X → I.depthStratum M k} :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    ContMDiff IX 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))) m f ↔
      ContMDiff IX I m (Subtype.val ∘ f) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  let _ := I.depthStratumChartedSpace M L hI k
  simp only [ContMDiff, ← contMDiffWithinAt_univ,
    contMDiffWithinAt_iff_comp_subtypeVal_depthStratum L hI hm k]

end Universal

/-- **Functoriality and independence of the linear coordinate system:** a `C^m` diffeomorphism
`Φ : M ≃ₘ^m⟮I, I'⟯ N` (`m ≠ 0`) between manifolds whose model ranges are cut out by nonnegative
coordinates restricts to a `C^m` diffeomorphism between their depth-`k` strata. Taking
`Φ = Diffeomorph.refl I M m` shows that the smooth structure on `I.depthStratum M k` is
independent of the coordinate description `(L, S)`. -/
def depthStratumDiffeomorph (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M] [IsManifold I' m N]
    (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI : IsManifold I' 1 N := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    letI := I'.depthStratumChartedSpace N L' hI' k
    (I.depthStratum M k) ≃ₘ^m⟮
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k))),
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E' - k)))⟯
      (I'.depthStratum N k) := by
  haveI : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional ℝ E' := L'.symm.toLinearEquiv.finiteDimensional
  letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  letI : IsManifold I' 1 N := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  letI := I.depthStratumChartedSpace M L hI k
  letI := I'.depthStratumChartedSpace N L' hI' k
  refine
    { toFun := fun x ↦
        ⟨Φ x.1, by rw [mem_depthStratum, Φ.depth_eq hm]; exact mem_depthStratum.1 x.2⟩
      invFun := fun y ↦
        ⟨Φ.symm y.1, by rw [mem_depthStratum, Φ.symm.depth_eq hm]; exact mem_depthStratum.1 y.2⟩
      left_inv := fun x ↦ Subtype.ext (Φ.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (Φ.apply_symm_apply y.1)
      contMDiff_toFun :=
        (contMDiff_iff_comp_subtypeVal_depthStratum L' hI' hm k).2
          (Φ.contMDiff.comp (contMDiff_subtypeVal_depthStratum L hI hm k))
      contMDiff_invFun :=
        (contMDiff_iff_comp_subtypeVal_depthStratum L hI hm k).2
          (Φ.symm.contMDiff.comp (contMDiff_subtypeVal_depthStratum L' hI' hm k)) }

@[simp]
theorem coe_depthStratumDiffeomorph (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M] [IsManifold I' m N]
    (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) (x : I.depthStratum M k) :
    ((depthStratumDiffeomorph L hI L' hI' hm Φ k x : I'.depthStratum N k) : N) = Φ x.1 :=
  (rfl)

@[simp]
theorem coe_depthStratumDiffeomorph_symm (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {ι' : Type*} [Finite ι'] (L' : E' ≃L[ℝ] (ι' → ℝ)) {S' : Set ι'}
    (hI' : range I' = {y | ∀ i ∈ S', 0 ≤ L' y i})
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M] [IsManifold I' m N]
    (Φ : M ≃ₘ^m⟮I, I'⟯ N) (k : ℕ) (y : I'.depthStratum N k) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI : IsManifold I' 1 N := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI k
    letI := I'.depthStratumChartedSpace N L' hI' k
    (((depthStratumDiffeomorph L hI L' hI' hm Φ k).symm y : I.depthStratum M k) : M) =
      Φ.symm y.1 :=
  (rfl)

/-- **Comparison with the interior:** the depth-zero stratum `I.depthStratum M 0` is canonically
diffeomorphic to the open interior submanifold `⟨I.interior M, I.isOpen_interior hm⟩`. -/
def depthStratumZeroDiffeomorphInterior (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M] :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI 0
    (I.depthStratum M 0) ≃ₘ^m⟮𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - 0))), I⟯
      (⟨I.interior M, I.isOpen_interior hm⟩ : TopologicalSpace.Opens M) := by
  haveI : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  letI := I.depthStratumChartedSpace M L hI 0
  let U : TopologicalSpace.Opens M := ⟨I.interior M, I.isOpen_interior hm⟩
  refine
    { toFun := fun x ↦ ⟨x.1, I.depth_eq_zero_iff.1 (mem_depthStratum.1 x.2)⟩
      invFun := fun x ↦ ⟨x.1, mem_depthStratum.2 (I.depth_eq_zero_iff.2 x.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := fun x ↦
        (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
          (f := fun x : I.depthStratum M 0 ↦
            (⟨x.1, I.depth_eq_zero_iff.1 (mem_depthStratum.1 x.2)⟩ : U)) univ x).1
          (contMDiff_subtypeVal_depthStratum L hI hm 0 x)
      contMDiff_invFun :=
        (contMDiff_iff_comp_subtypeVal_depthStratum L hI hm 0).2 contMDiff_subtype_val }

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M] (x : I.depthStratum M 0) :
    ((depthStratumZeroDiffeomorphInterior L hI hm x :
      (⟨I.interior M, I.isOpen_interior hm⟩ : TopologicalSpace.Opens M)) : M) = x.1 :=
  (rfl)

@[simp]
theorem coe_depthStratumZeroDiffeomorphInterior_symm (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    {m : ℕ∞ω} (hm : m ≠ 0) [IsManifold I m M]
    (x : (⟨I.interior M, I.isOpen_interior hm⟩ : TopologicalSpace.Opens M)) :
    letI : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := I.depthStratumChartedSpace M L hI 0
    (((depthStratumZeroDiffeomorphInterior L hI hm).symm x : I.depthStratum M 0) : M) = x.1 :=
  (rfl)

end StrataCharts

/-- **Comparison with the half-space boundary:** on a `C^m` manifold (`m ≠ 0`) modelled on
`𝓡∂ (n + 1)`, the depth-one stratum with its depth-stratum smooth structure is canonically
diffeomorphic to the boundary manifold of `TauCeti.boundaryChartedSpace`. -/
def depthStratumOneDiffeomorphBoundary {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] {m : ℕ∞ω} (hm : m ≠ 0)
    [IsManifold (𝓡∂ (n + 1)) m X] :
    letI : IsManifold (𝓡∂ (n + 1)) 1 X :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := (𝓡∂ (n + 1)).depthStratumChartedSpace X
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearEquiv
      (range_modelWithCornersEuclideanHalfSpace_eq_equiv (n + 1)) 1
    ((𝓡∂ (n + 1)).depthStratum X 1) ≃ₘ^m⟮
        𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) - 1))),
        𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
      ↥((𝓡∂ (n + 1)).boundary X) := by
  letI : IsManifold (𝓡∂ (n + 1)) 1 X :=
    IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
  letI := (𝓡∂ (n + 1)).depthStratumChartedSpace X
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearEquiv
    (range_modelWithCornersEuclideanHalfSpace_eq_equiv (n + 1)) 1
  refine
    { toFun := fun x ↦
        ⟨x.1, depth_modelWithCornersEuclideanHalfSpace_eq_one_iff.1 (mem_depthStratum.1 x.2)⟩
      invFun := fun x ↦
        ⟨x.1, mem_depthStratum.2 (depth_modelWithCornersEuclideanHalfSpace_eq_one_iff.2 x.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      contMDiff_toFun :=
        (TauCeti.contMDiff_iff_comp_subtypeVal_boundary hm).2
          (contMDiff_subtypeVal_depthStratum
            (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearEquiv
            (range_modelWithCornersEuclideanHalfSpace_eq_equiv (n + 1)) hm 1)
      contMDiff_invFun :=
        (contMDiff_iff_comp_subtypeVal_depthStratum
            (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearEquiv
            (range_modelWithCornersEuclideanHalfSpace_eq_equiv (n + 1)) hm 1).2
          (TauCeti.isSmoothEmbedding_subtypeVal_boundary X hm).contMDiff }

@[simp]
theorem coe_depthStratumOneDiffeomorphBoundary {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] {m : ℕ∞ω} (hm : m ≠ 0)
    [IsManifold (𝓡∂ (n + 1)) m X] (x : (𝓡∂ (n + 1)).depthStratum X 1) :
    ((depthStratumOneDiffeomorphBoundary hm x : (𝓡∂ (n + 1)).boundary X) : X) = x.1 :=
  (rfl)

@[simp]
theorem coe_depthStratumOneDiffeomorphBoundary_symm {n : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) X] {m : ℕ∞ω} (hm : m ≠ 0)
    [IsManifold (𝓡∂ (n + 1)) m X] (x : (𝓡∂ (n + 1)).boundary X) :
    letI : IsManifold (𝓡∂ (n + 1)) 1 X :=
      IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hm)
    letI := (𝓡∂ (n + 1)).depthStratumChartedSpace X
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).toContinuousLinearEquiv
      (range_modelWithCornersEuclideanHalfSpace_eq_equiv (n + 1)) 1
    (((depthStratumOneDiffeomorphBoundary hm).symm x : (𝓡∂ (n + 1)).depthStratum X 1) : X) =
      x.1 :=
  (rfl)

end ModelWithCorners

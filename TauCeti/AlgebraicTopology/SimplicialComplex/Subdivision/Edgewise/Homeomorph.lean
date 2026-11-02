/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Realization

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import TauCeti.Algebra.Order.BigOperators.Sum.UnitSlices
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.ClosedMap

/-!
# The edgewise subdivision realization homeomorphism

For `k ≠ 0`, the canonical map from the realization of the `k`-th edgewise subdivision of a
simplicial complex `K` with linearly ordered vertices to the realization of `K` is a
homeomorphism. It is injective by
`AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap_injective` and closed by
`AbstractSimplicialComplex.isClosedMap_of_edgewisePoint_formula`; this file proves that it is
surjective and assembles the homeomorphism. So the edgewise subdivision is a subdivision in the
geometric sense, and transporting a triangulation along this homeomorphism refines it into
simplices which are small and uniformly fat.

Let `y` be a point of `|K|` with carrier `σ`, and for a vertex `i` let `S i` be the coordinate
sum of `y` over the vertices of `σ` that are `≤ i`. For `t ∈ [0, 1)` let `Q t` be the first
vertex `i` of `σ` with `t < S i`. To an offset `θ ∈ [0, 1)` assign the monotone `k`-tuple whose
entry `l` is `Q ((l + θ) / k)`. As `θ` increases these tuples increase, and any two of them
interleave, so the tuples assigned to the offsets in `[0, 1)` span a face of the subdivision.
Give the tuple `u` the barycentric coordinate equal to the length of the set of offsets assigned
to `u`. For a lower set `p` of vertices, entry `l` of the tuple of `θ` lies in `p` exactly when
`l + θ < k * P`, where `P` is the coordinate sum of `y` over `p`; summing these lengths over `l`
gives `k * P`. Taking `p` to be the vertices `≤ i` and `< i` shows that the point with these
coordinates is mapped to `y`.

## Main results

* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap_surjective`: the edgewise
  realization map is surjective for `k ≠ 0`.
* `AbstractSimplicialComplex.isClosedMap_edgewiseSubdivisionRealizationMap`: the edgewise
  realization map is closed.
* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationHomeomorph`: the canonical
  homeomorphism from the realization of the `k`-th edgewise subdivision to the realization of `K`.

## References

* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
* H. Edelsbrunner, D. R. Grayson, *Edgewise subdivision of a simplex*, Discrete Comput. Geom. 24
  (2000), 707–719.
-/

public section

noncomputable section

open Finset MeasureTheory TauCeti PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] {K : AbstractSimplicialComplex ι} {k : ℕ}

variable (y : Realization K)

omit [LinearOrder ι] in
private theorem support_nonempty : y.1.support.Nonempty := by
  simpa using K.isRelLowerSet_faces.prop_of_mem (support_mem K y)

omit [LinearOrder ι] in
private theorem sum_support : ∑ j ∈ y.1.support, y.1 j = 1 := by
  rw [← Realization.sum_eq_one K y, Finsupp.sum]

/-- The first vertex `j` of the carrier of `y` at which the coordinate sum of `y` over the
vertices `≤ j` exceeds `t`, or the last vertex of the carrier if there is none. -/
private def quantile (t : ℝ) : ι :=
  (insert (y.1.support.max' (support_nonempty y))
    {j ∈ y.1.support | t < ∑ j' ∈ y.1.support with j' ≤ j, y.1 j'}).min' (insert_nonempty _ _)

private theorem quantile_mem_insert (t : ℝ) :
    quantile y t ∈ insert (y.1.support.max' (support_nonempty y))
      {j ∈ y.1.support | t < ∑ j' ∈ y.1.support with j' ≤ j, y.1 j'} :=
  min'_mem _ _

private theorem quantile_mem (t : ℝ) : quantile y t ∈ y.1.support := by
  rcases mem_insert.mp (quantile_mem_insert y t) with h | h
  · rw [h]
    exact max'_mem _ _
  · exact (mem_filter.mp h).1

private theorem quantile_mono : Monotone (quantile y) := by
  intro t t' htt'
  refine min'_le _ _ (mem_of_subset ?_ (min'_mem _ _))
  refine insert_subset_insert _ (monotone_filter_right _ fun j _ hj => ?_)
  exact htt'.trans_lt hj

variable {y} in
/-- For `0 ≤ t < 1` and a lower set `p` of vertices, the vertex `quantile y t` lies in `p` exactly
when `t` is below the coordinate sum of `y` over `p`. -/
private theorem quantile_mem_iff {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t < 1) {p : ι → Prop}
    [DecidablePred p] (hp : Antitone p) :
    p (quantile y t) ↔ t < ∑ j ∈ y.1.support with p j, y.1 j := by
  set σ := y.1.support
  set m := quantile y t
  have hsum : ∑ j ∈ σ, y.1 j = 1 := sum_support y
  have hy0 (j : ι) : 0 ≤ y.1 j := Realization.nonneg K y j
  -- The coordinate sum up to `m` exceeds `t`, and that up to any earlier vertex does not.
  have hm : t < ∑ j ∈ σ with j ≤ m, y.1 j := by
    rcases mem_insert.mp (quantile_mem_insert y t) with h | h
    · rw [show m = σ.max' (support_nonempty y) from h,
        filter_true_of_mem fun j hj => le_max' σ j hj, hsum]
      exact h₁
    · exact (mem_filter.mp h).2
  have hlt (j : ι) (hj : j ∈ σ) (hjm : j < m) : ∑ j' ∈ σ with j' ≤ j, y.1 j' ≤ t := by
    by_contra! h
    exact hjm.not_ge (min'_le _ _ (mem_insert_of_mem (mem_filter.mpr ⟨hj, h⟩)))
  constructor
  · intro hpm
    refine hm.trans_le (sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hy0 j)
    exact monotone_filter_right _ fun j _ hj => hp hj hpm
  · intro ht
    by_contra hpm
    have hsub : σ.filter p ⊆ σ.filter (· < m) :=
      monotone_filter_right _ fun j _ hj => lt_of_not_ge fun hmj => hpm (hp hmj hj)
    -- The coordinate sum below `m` is at most `t`: it is the sum up to the vertex before `m`.
    have hbelow : ∑ j ∈ σ with j < m, y.1 j ≤ t := by
      rcases (σ.filter (· < m)).eq_empty_or_nonempty with he | hne
      · rw [he, sum_empty]
        exact h₀
      · obtain ⟨hm's, hm'm⟩ := mem_filter.mp (max'_mem _ hne)
        rw [show σ.filter (· < m) = σ.filter (· ≤ (σ.filter (· < m)).max' hne) by
          ext j
          simp only [mem_filter, and_congr_right_iff]
          exact fun hj => ⟨fun hjm => le_max' _ j (mem_filter.mpr ⟨hj, hjm⟩),
            fun hjm => hjm.trans_lt hm'm⟩]
        exact hlt _ hm's hm'm
    linarith [sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hy0 j]

/-- The monotone `k`-tuple of vertices which the preimage of `y` under the edgewise realization
map assigns to the offset `θ`: its entry `l` is `quantile y ((l + θ) / k)`. -/
private def edgewiseTuple (θ : ℝ) : Fin k → ι :=
  fun l => quantile y ((l + θ) / k)

private theorem edgewiseTuple_mem (θ : ℝ) (l : Fin k) : edgewiseTuple y θ l ∈ y.1.support :=
  quantile_mem y _

private theorem edgewiseTuple_le_edgewiseTuple {θ θ' : ℝ} {l l' : Fin k}
    (h : (l : ℝ) + θ ≤ l' + θ') : edgewiseTuple y θ l ≤ edgewiseTuple y θ' l' :=
  quantile_mono y (div_le_div_of_nonneg_right h (Nat.cast_nonneg k))

private theorem monotone_edgewiseTuple (θ : ℝ) : Monotone (edgewiseTuple (k := k) y θ) :=
  fun l l' hll' => edgewiseTuple_le_edgewiseTuple y (by gcongr; exact_mod_cast hll')

private theorem edgewiseTuple_mono {θ θ' : ℝ} (h : θ ≤ θ') :
    edgewiseTuple (k := k) y θ ≤ edgewiseTuple y θ' :=
  fun l => edgewiseTuple_le_edgewiseTuple y (by gcongr)

private theorem edgewiseTuple_le_of_lt {θ θ' : ℝ} (hθ : θ < 1) (hθ' : 0 ≤ θ') {j j' : Fin k}
    (hjj' : j < j') : edgewiseTuple y θ j ≤ edgewiseTuple y θ' j' := by
  refine edgewiseTuple_le_edgewiseTuple y ?_
  have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast Nat.succ_le_of_lt hjj'
  linarith

variable {y} in
/-- For `0 ≤ θ < 1` and a lower set `p` of vertices, the entry `l` of `edgewiseTuple y θ` lies
in `p` exactly when `l + θ` is below `k` times the coordinate sum of `y` over `p`. -/
private theorem edgewiseTuple_mem_iff {θ : ℝ} (hθ : θ ∈ Set.Ico 0 1) {l : Fin k}
    {p : ι → Prop} [DecidablePred p] (hp : Antitone p) :
    p (edgewiseTuple y θ l) ↔ l + θ < k * ∑ j ∈ y.1.support with p j, y.1 j := by
  have hk : (0 : ℝ) < k := by exact_mod_cast l.pos
  have hl : (l : ℝ) + 1 ≤ k := by exact_mod_cast l.isLt
  rw [edgewiseTuple, quantile_mem_iff (by have := hθ.1; positivity)
    ((div_lt_one hk).mpr (by linarith [hθ.2])) hp, div_lt_iff₀' hk]

/-- The offsets `θ ∈ [0, 1)` to which `edgewiseTuple` assigns the vertex `u`. -/
private def offsets (u : K.EdgewiseVertex k) : Set ℝ :=
  {θ ∈ Set.Ico 0 1 | edgewiseTuple y θ = u.1}

private theorem measurableSet_offsets (u : K.EdgewiseVertex k) :
    MeasurableSet (offsets y u) := by
  refine Set.OrdConnected.measurableSet ⟨fun a ha b hb θ hθ => ⟨⟨ha.1.1.trans hθ.1,
    hθ.2.trans_lt hb.1.2⟩, le_antisymm ?_ ?_⟩⟩
  · exact hb.2 ▸ edgewiseTuple_mono y hθ.2
  · exact ha.2 ▸ edgewiseTuple_mono y hθ.1

/-- The vertices of the edgewise subdivision with all entries in the carrier of `y`. -/
private def vertices : Finset (K.EdgewiseVertex k) :=
  (finite_edgewiseVertex_entries_subset _ k y.1.support).toFinset

/-- Every offset `θ ∈ [0, 1)` is assigned a vertex. -/
private theorem exists_mem_vertices_mem_offsets (hk : k ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ico 0 1) :
    ∃ u ∈ vertices (k := k) y, θ ∈ offsets y u := by
  refine ⟨⟨edgewiseTuple y θ, monotone_edgewiseTuple y θ, ?_⟩, ?_, hθ, rfl⟩
  · refine K.isRelLowerSet_faces.mem_of_le (support_mem K y)
      (image_subset_iff.mpr fun l _ => edgewiseTuple_mem y θ l)
      ((univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩).image _)
  · simpa [vertices] using edgewiseTuple_mem y θ

private theorem pairwiseDisjoint_offsets (s : Finset (K.EdgewiseVertex k)) :
    (s : Set (K.EdgewiseVertex k)).PairwiseDisjoint (offsets y) :=
  fun _ _ _ _ huw => Set.disjoint_left.mpr fun _ hu hw =>
    huw (Subtype.ext (hu.2.symm.trans hw.2))

private theorem measure_offsets_ne_top (u : K.EdgewiseVertex k) : volume (offsets y u) ≠ ⊤ :=
  ((measure_mono fun _ (hθ : _ ∈ offsets y u) => hθ.1).trans_lt measure_Ico_lt_top).ne

/-- The offsets assigned to vertices whose entry `l` lies in a lower set `p` form `[0, 1)` cut
at `k` times the coordinate sum of `y` over `p`, minus `l`. -/
private theorem biUnion_offsets_eq (hk : k ≠ 0) (l : Fin k) {p : ι → Prop} [DecidablePred p]
    (hp : Antitone p) :
    ⋃ u ∈ (vertices y).filter (p <| ·.1 l), offsets y u =
      Set.Ico 0 (min 1 (k * ∑ j ∈ y.1.support with p j, y.1 j - l)) := by
  ext θ
  simp only [Set.mem_iUnion, mem_filter, exists_prop, Set.mem_Ico, lt_min_iff]
  constructor
  · rintro ⟨u, ⟨-, hpu⟩, hθ, hθu⟩
    rw [← hθu, edgewiseTuple_mem_iff hθ (l := l) hp] at hpu
    exact ⟨hθ.1, hθ.2, by linarith⟩
  · rintro ⟨hθ₀, hθ₁, hθP⟩
    obtain ⟨u, hu, hθu⟩ := exists_mem_vertices_mem_offsets y hk ⟨hθ₀, hθ₁⟩
    refine ⟨u, ⟨hu, ?_⟩, hθu⟩
    rw [← hθu.2, edgewiseTuple_mem_iff hθu.1 (l := l) hp]
    linarith

/-- The total length of the offsets assigned to vertices whose entry `l` lies in a lower set
`p`, summed over `l`, is `k` times the coordinate sum of `y` over `p`. -/
private theorem sum_measureReal_offsets_mul_card (hk : k ≠ 0) {p : ι → Prop} [DecidablePred p]
    (hp : Antitone p) :
    ∑ u ∈ vertices (k := k) y, volume.real (offsets y u) * #{l | p (u.1 l)} =
      k * ∑ j ∈ y.1.support with p j, y.1 j := by
  set P := ∑ j ∈ y.1.support with p j, y.1 j
  have hP₀ : 0 ≤ P := sum_nonneg fun j _ => Realization.nonneg K y j
  have hP₁ : P ≤ 1 := (sum_support y).symm ▸
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun j _ _ => Realization.nonneg K y j
  -- For each `l`, the offsets of the vertices whose entry `l` lies in `p` form `[0, 1)` cut at
  -- `k * P - l`.
  have hl (l : Fin k) : ∑ u ∈ vertices y with p (u.1 l), volume.real (offsets y u) =
      max (min 1 (k * P - l)) 0 := by
    rw [← measureReal_biUnion_finset (pairwiseDisjoint_offsets y _)
      (fun u _ => measurableSet_offsets y u) fun u _ => measure_offsets_ne_top y u,
      biUnion_offsets_eq y hk l hp, Real.volume_real_Ico, sub_zero]
  calc ∑ u ∈ vertices y, volume.real (offsets y u) * #{l | p (u.1 l)}
      = ∑ l : Fin k, ∑ u ∈ vertices y with p (u.1 l), volume.real (offsets y u) := by
        simp only [card_filter, Nat.cast_sum, mul_sum, Nat.cast_ite, Nat.cast_one,
          Nat.cast_zero, mul_ite, mul_one, mul_zero]
        rw [sum_comm]
        simp only [sum_filter]
    _ = ∑ l ∈ range k, max (min 1 (k * P - l)) 0 := by
        rw [← Fin.sum_univ_eq_sum_range (fun l => max (min 1 (k * P - l)) 0)]
        exact sum_congr rfl fun l _ => hl l
    _ = k * P := sum_range_max_min_one_sub k (by positivity) (by nlinarith)

private theorem mem_vertices_of_measureReal_ne_zero {u : K.EdgewiseVertex k}
    (hu : volume.real (offsets y u) ≠ 0) : u ∈ vertices y := by
  obtain ⟨θ, -, hθu⟩ := nonempty_of_measureReal_ne_zero hu
  simpa [vertices, ← hθu] using edgewiseTuple_mem y θ

/-- The barycentric coordinates of the preimage of `y` under the edgewise realization map: the
coordinate at `u` is the length of the set of offsets assigned to `u`. -/
private def preimageCoord : K.EdgewiseVertex k →₀ ℝ :=
  Finsupp.ofSupportFinite (fun u => volume.real (offsets y u))
    ((vertices y).finite_toSet.subset fun _ hu => mem_vertices_of_measureReal_ne_zero y hu)

private theorem preimageCoord_apply (u : K.EdgewiseVertex k) :
    preimageCoord y u = volume.real (offsets y u) := by
  rw [preimageCoord, Finsupp.ofSupportFinite_coe]

private theorem exists_offset_of_mem_support {u : K.EdgewiseVertex k}
    (hu : u ∈ (preimageCoord y).support) :
    ∃ θ ∈ Set.Ico (0 : ℝ) 1, edgewiseTuple y θ = u.1 := by
  obtain ⟨θ, hθ, hθu⟩ := nonempty_of_measureReal_ne_zero
    (by rwa [Finsupp.mem_support_iff, preimageCoord_apply] at hu)
  exact ⟨θ, hθ, hθu⟩

private theorem sum_preimageCoord_mul_card (hk : k ≠ 0) {p : ι → Prop} [DecidablePred p]
    (hp : Antitone p) :
    ∑ u ∈ (preimageCoord (k := k) y).support, preimageCoord y u * #{l | p (u.1 l)} =
      k * ∑ j ∈ y.1.support with p j, y.1 j := by
  rw [sum_subset (fun u hu => mem_vertices_of_measureReal_ne_zero y
      (by rwa [Finsupp.mem_support_iff, preimageCoord_apply] at hu))
    fun u _ hu => by rw [Finsupp.notMem_support_iff.mp hu, zero_mul]]
  simpa only [preimageCoord_apply] using sum_measureReal_offsets_mul_card y hk hp

private theorem sum_preimageCoord (hk : k ≠ 0) :
    ∑ u ∈ (preimageCoord (k := k) y).support, preimageCoord y u = 1 := by
  have h := sum_preimageCoord_mul_card y hk (p := fun _ => True) fun _ _ _ _ => trivial
  simp only [filter_true_of_mem fun _ _ => trivial, card_univ, Fintype.card_fin, ← sum_mul] at h
  refine (mul_left_inj' (Nat.cast_ne_zero.mpr hk)).mp (h.trans ?_)
  rw [sum_support, mul_one, one_mul]

private theorem support_preimageCoord_mem (hk : k ≠ 0) :
    (preimageCoord (k := k) y).support ∈ K.edgewiseSubdivision k := by
  have hne : (preimageCoord (k := k) y).support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr fun h => by simpa [h] using sum_preimageCoord y hk
  refine mem_edgewiseSubdivision_iff.mpr ⟨hne, ?_, fun u hu w hw _ => ?_,
    fun u hu w hw j j' hjj' => ?_⟩
  · refine K.isRelLowerSet_faces.mem_of_le (support_mem K y)
      (biUnion_subset.mpr fun u hu => ?_) ?_
    · obtain ⟨θ, -, hθu⟩ := exists_offset_of_mem_support y hu
      exact image_subset_iff.mpr fun l _ => hθu ▸ edgewiseTuple_mem y θ l
    · obtain ⟨u, hu⟩ := hne
      exact ⟨u.1 ⟨0, Nat.pos_of_ne_zero hk⟩,
        mem_biUnion.mpr ⟨u, hu, mem_image_of_mem _ (mem_univ _)⟩⟩
  · obtain ⟨θ, -, hθu⟩ := exists_offset_of_mem_support y hu
    obtain ⟨θ', -, hθw⟩ := exists_offset_of_mem_support y hw
    rcases le_total θ θ' with h | h
    · exact Or.inl (Subtype.coe_le_coe.mp (hθu ▸ hθw ▸ edgewiseTuple_mono y h))
    · exact Or.inr (Subtype.coe_le_coe.mp (hθu ▸ hθw ▸ edgewiseTuple_mono y h))
  · obtain ⟨θ, hθ, hθu⟩ := exists_offset_of_mem_support y hu
    obtain ⟨θ', hθ', hθw⟩ := exists_offset_of_mem_support y hw
    rw [← hθu, ← hθw]
    exact edgewiseTuple_le_of_lt y hθ.2 hθ'.1 hjj'

/-- The edgewise realization map is surjective: every point of the realization of `K` is the
image of a point of the `k`-th edgewise subdivision, for `k ≠ 0`. -/
theorem edgewiseSubdivisionRealizationMap_surjective (hk : k ≠ 0) :
    Function.Surjective (edgewiseSubdivisionRealizationMap K k) := by
  intro y
  have hx : preimageCoord (k := k) y ∈
      (standardGeometricComplex (K.edgewiseSubdivision k)).space := by
    refine mem_realization_iff.mpr ⟨_, support_preimageCoord_mem y hk, ?_⟩
    have hsum : (preimageCoord (k := k) y).sum (fun _ r => r) = 1 := by
      rw [Finsupp.sum]
      exact sum_preimageCoord y hk
    have hmem := mem_standardSimplex_iff.mpr ⟨fun u => by
      rw [preimageCoord_apply]
      exact measureReal_nonneg, hsum, subset_rfl⟩
    simpa only [coe_image] using hmem
  refine ⟨⟨preimageCoord y, hx⟩, Subtype.ext (Finsupp.ext fun i => ?_)⟩
  simp only [edgewiseSubdivisionRealizationMap_val, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul, edgewisePoint_apply]
  -- The number of entries equal to `i` is the number at most `i` minus the number below `i`.
  have hcount (u : K.EdgewiseVertex k) :
      (#{l | u.1 l = i} : ℝ) = #{l | u.1 l ≤ i} - #{l | u.1 l < i} := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_add, Nat.cast_inj, ← card_union_of_disjoint
      (disjoint_filter.mpr fun l _ h h' => h'.ne h)]
    congr 1
    ext l
    simp [le_iff_eq_or_lt]
  -- The coordinate of `y` at `i` is a difference of two coordinate sums over lower sets.
  have hy : ∑ j ∈ y.1.support with j ≤ i, y.1 j - ∑ j ∈ y.1.support with j < i, y.1 j = y.1 i := by
    rw [sum_filter, sum_filter, ← sum_sub_distrib]
    rw [sum_congr rfl fun j _ => show (if j ≤ i then y.1 j else 0) - (if j < i then y.1 j else 0) =
      if j = i then y.1 j else 0 by
        rcases lt_trichotomy j i with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [h.not_ge, h.not_gt, h.ne'], sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  calc ∑ u ∈ (preimageCoord y).support, preimageCoord y u * ((k : ℝ)⁻¹ * #{l | u.1 l = i})
      = (k : ℝ)⁻¹ * (∑ u ∈ (preimageCoord y).support, preimageCoord y u * #{l | u.1 l ≤ i} -
          ∑ u ∈ (preimageCoord y).support, preimageCoord y u * #{l | u.1 l < i}) := by
        rw [← sum_sub_distrib, mul_sum]
        exact sum_congr rfl fun u _ => by rw [hcount]; ring
    _ = y.1 i := by
        rw [sum_preimageCoord_mul_card y hk (p := (· ≤ i)) antitone_le,
          sum_preimageCoord_mul_card y hk (p := (· < i)) antitone_lt, ← mul_sub, hy, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk), one_mul]

/-- The edgewise realization map is bijective for `k ≠ 0`. -/
theorem edgewiseSubdivisionRealizationMap_bijective (hk : k ≠ 0) :
    Function.Bijective (edgewiseSubdivisionRealizationMap K k) :=
  ⟨edgewiseSubdivisionRealizationMap_injective, edgewiseSubdivisionRealizationMap_surjective hk⟩

/-- The edgewise realization map is closed for the weak topologies on both realizations. -/
theorem isClosedMap_edgewiseSubdivisionRealizationMap :
    IsClosedMap (edgewiseSubdivisionRealizationMap K k) :=
  isClosedMap_of_edgewisePoint_formula continuous_edgewiseSubdivisionRealizationMap
    edgewiseSubdivisionRealizationMap_val

variable (K) in
/-- The canonical homeomorphism from the realization of the `k`-th edgewise subdivision of `K`
to the realization of `K`, for `k ≠ 0`. It sends each vertex `u` of the subdivision to
`edgewisePoint u`, the average of its entries, and is linear in barycentric coordinates on every
simplex. -/
def edgewiseSubdivisionRealizationHomeomorph (hk : k ≠ 0) :
    Realization (K.edgewiseSubdivision k) ≃ₜ Realization K :=
  (Equiv.ofBijective _
    (edgewiseSubdivisionRealizationMap_bijective hk)).toHomeomorphOfContinuousClosed
      continuous_edgewiseSubdivisionRealizationMap isClosedMap_edgewiseSubdivisionRealizationMap

/-- The edgewise realization homeomorphism has the edgewise realization map as its forward
map. -/
@[simp]
theorem edgewiseSubdivisionRealizationHomeomorph_apply (hk : k ≠ 0)
    (x : Realization (K.edgewiseSubdivision k)) :
    edgewiseSubdivisionRealizationHomeomorph K hk x = edgewiseSubdivisionRealizationMap K k x :=
  (rfl)

end AbstractSimplicialComplex

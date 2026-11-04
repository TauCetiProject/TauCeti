/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Basic

import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Data.Fintype.CardFilterOrder

/-!
# The realization map of an edgewise subdivision

Every vertex `u` of the `k`-th edgewise subdivision of a simplicial complex `K` with linearly
ordered vertices is a monotone `k`-tuple of vertices of `K`. Send it to the average
`edgewisePoint u` of its entries and extend linearly in barycentric coordinates over every
simplex. The entries of the vertices of a face of the subdivision span a face of `K`, so this
lands in the realization of `K`. This file constructs that continuous map
`|K.edgewiseSubdivision k| → |K|` and proves that it is injective.

Injectivity says that a point `y` of `|K|` determines the face of the subdivision carrying a
preimage, together with its barycentric coordinates there. Let `y` be the image of a point with
coordinates `x u > 0` on the vertices `u⁰ < u¹ < ⋯ < uᵐ` of a face. For a vertex `i` of `K`, `k`
times the coordinate sum of `y` over the vertices `≤ i` is `∑ a, x uᵃ * c uᵃ i`, where `c u i` is
the number of entries of `u` that are `≤ i`. Along the chain these counts drop by at most one in
total. So for an offset `θ` in the interval `[x u⁰ + ⋯ + x uᵃ⁻¹, x u⁰ + ⋯ + x uᵃ)`, the count
`c uᵃ i` is the integer `⌈k * (∑ j ≤ i, y j) - θ⌉` for every `i`. Hence `uᵃ` is the unique
monotone tuple with these counts, and is determined by `y` and `θ`. These intervals cover
`[0, 1)`. So the vertices of the face and the intervals, whose lengths are the coordinates, can
be read off from `y`.

The edgewise subdivision is how a smooth triangulation is refined into simplices that are both
small and uniformly fat, which Whitehead's secant approximation needs. Surjectivity of the map,
and the resulting homeomorphism, are proved in
`TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Homeomorph`.

## Main definitions

* `AbstractSimplicialComplex.edgewiseSubdivisionFaceMap`: the map from the closed simplex on a
  face of the edgewise subdivision to the closed simplex on a set `σ` containing the entries of
  its vertices, sending each vertex `u` to `edgewisePoint u`.
* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap`: the canonical continuous map
  from the realization of the edgewise subdivision to the realization of `K`.

## Main results

* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap_vertex`: a vertex `u` of the
  subdivision is sent to `edgewisePoint u`.
* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap_comp_faceInclusion`: on a simplex
  of the subdivision, the realization map is the face map followed by a face inclusion.
* `AbstractSimplicialComplex.continuous_edgewiseSubdivisionRealizationMap`: the realization map
  is continuous.
* `AbstractSimplicialComplex.edgewiseSubdivisionRealizationMap_injective`: the realization map is
  injective.

## References

* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
* G. Segal, *Configuration-spaces and iterated loop-spaces*, Invent. Math. 21 (1973), 213–221,
  Appendix 1.
* H. Edelsbrunner, D. R. Grayson, *Edgewise subdivision of a simplex*, Discrete Comput. Geom. 24
  (2000), 707–719.
-/

public section

noncomputable section

open Finset TauCeti TauCeti.SetLike PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] {K : AbstractSimplicialComplex ι} {k : ℕ}

/-! ### The face map -/

private theorem linearCombination_edgewisePoint_mem {ρ : Finset (K.EdgewiseVertex k)}
    {σ : Finset ι} (hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) (x : StandardSimplex ρ) :
    Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1 ∈
      convexHull ℝ ((fun v => Finsupp.single v (1 : ℝ)) '' (σ : Set ι)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine (convex_convexHull ℝ _).sum_mem (fun u _ => StandardSimplex.nonneg x u)
    (by simpa [Finsupp.sum] using StandardSimplex.sum_eq_one x) fun u hu => ?_
  exact edgewisePoint_mem_convexHull u.ne_zero
    (hρσ u (StandardSimplex.support_subset x hu))

/-- The map from the closed simplex on a set `ρ` of vertices of the edgewise subdivision to the
closed simplex on a set `σ` of vertices of `K` containing all their entries. It is linear in
barycentric coordinates and sends the vertex `u` to `edgewisePoint u`. -/
def edgewiseSubdivisionFaceMap {ρ : Finset (K.EdgewiseVertex k)} {σ : Finset ι}
    (hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) : StandardSimplex ρ → StandardSimplex σ :=
  fun x => ⟨Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1, by
    simpa only [coe_image] using linearCombination_edgewisePoint_mem hρσ x⟩

/-- The edgewise face map is the linear combination of the points `edgewisePoint u`. -/
@[simp]
theorem edgewiseSubdivisionFaceMap_val {ρ : Finset (K.EdgewiseVertex k)} {σ : Finset ι}
    (hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) (x : StandardSimplex ρ) :
    (edgewiseSubdivisionFaceMap hρσ x : ι →₀ ℝ) =
      Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1 :=
  (rfl)

/-- The coordinates of the edgewise face map: the coordinate at `i` is the combination of the
coordinates at `i` of the points `edgewisePoint u`, weighted by the barycentric coordinates. -/
theorem edgewiseSubdivisionFaceMap_apply {ρ : Finset (K.EdgewiseVertex k)} {σ : Finset ι}
    (hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) (x : StandardSimplex ρ) (i : ι) :
    (edgewiseSubdivisionFaceMap hρσ x : ι →₀ ℝ) i = ∑ u ∈ ρ, x.1 u * edgewisePoint u.1 i := by
  have hsupp : x.1 ∈ Finsupp.supported ℝ ℝ (↑ρ : Set (K.EdgewiseVertex k)) :=
    (Finsupp.mem_supported ℝ x.1).mpr (StandardSimplex.support_subset x)
  rw [edgewiseSubdivisionFaceMap_val, Finsupp.linearCombination_apply_of_mem_supported ℝ hsupp]
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]

/-- The edgewise face map is continuous. -/
theorem continuous_edgewiseSubdivisionFaceMap {ρ : Finset (K.EdgewiseVertex k)} {σ : Finset ι}
    (hρσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) : Continuous (edgewiseSubdivisionFaceMap hρσ) := by
  refine continuous_induced_rng.mpr (continuous_pi fun i => ?_)
  simp only [Function.comp_apply, edgewiseSubdivisionFaceMap_apply]
  have hcoe : Continuous fun x : StandardSimplex ρ => (x.1 : K.EdgewiseVertex k → ℝ) :=
    continuous_induced_dom
  exact continuous_finsetSum _ fun u _ => ((continuous_apply u).comp hcoe).mul continuous_const

/-! ### The realization map -/

/-- Every entry of a vertex of `ρ` is an entry of some vertex of `ρ`. -/
private theorem mem_biUnion_image (ρ : Finset (K.EdgewiseVertex k)) :
    ∀ u ∈ ρ, ∀ l, u.1 l ∈ ρ.biUnion fun u => univ.image u.1 :=
  fun u hu l => mem_biUnion.mpr ⟨u, hu, mem_image_of_mem _ (mem_univ l)⟩

private theorem linearCombination_edgewisePoint_mem_realization
    (x : Realization (K.edgewiseSubdivision k)) :
    Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1 ∈
      (standardGeometricComplex K).space :=
  mem_realization_iff.mpr ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision (support_mem _ x), by
    simpa only [coe_image] using linearCombination_edgewisePoint_mem (mem_biUnion_image _)
      ⟨x.1, by simpa only [carrier_val] using mem_convexHull_carrier _ x⟩⟩

variable (K k) in
/-- The canonical map from the realization of the `k`-th edgewise subdivision of `K` to the
realization of `K`. It sends each vertex `u` of the subdivision to `edgewisePoint u`, the average
of its entries, and is linear in barycentric coordinates on every simplex. -/
def edgewiseSubdivisionRealizationMap :
    Realization (K.edgewiseSubdivision k) → Realization K :=
  fun x => ⟨Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1,
    linearCombination_edgewisePoint_mem_realization x⟩

/-- The edgewise realization map is the linear combination of the points `edgewisePoint u`. -/
@[simp]
theorem edgewiseSubdivisionRealizationMap_val (x : Realization (K.edgewiseSubdivision k)) :
    (edgewiseSubdivisionRealizationMap K k x : ι →₀ ℝ) =
      Finsupp.linearCombination ℝ (fun u : K.EdgewiseVertex k => edgewisePoint u.1) x.1 :=
  (rfl)

/-- A vertex `u` of the edgewise subdivision is sent to `edgewisePoint u`, the average of its
entries. -/
theorem edgewiseSubdivisionRealizationMap_vertex (u : K.EdgewiseVertex k) :
    (edgewiseSubdivisionRealizationMap K k (vertex _ u) : ι →₀ ℝ) = edgewisePoint u.1 := by
  simp

/-- On a simplex `ρ` of the edgewise subdivision whose vertices have their entries in a face `σ`
of `K`, the edgewise realization map is the edgewise face map followed by the face inclusion
of `σ`. -/
theorem edgewiseSubdivisionRealizationMap_comp_faceInclusion (ρ : Face (K.edgewiseSubdivision k))
    (σ : Face K) (hρσ : ∀ u ∈ ρ.1, ∀ l, u.1 l ∈ σ.1) :
    edgewiseSubdivisionRealizationMap K k ∘ faceInclusion _ ρ =
      faceInclusion K σ ∘ edgewiseSubdivisionFaceMap hρσ := by
  funext x
  apply Subtype.ext
  simp only [Function.comp_apply, edgewiseSubdivisionRealizationMap_val, faceInclusion_val,
    edgewiseSubdivisionFaceMap_val]

/-- The edgewise realization map is continuous for the weak topologies on both realizations. -/
theorem continuous_edgewiseSubdivisionRealizationMap :
    Continuous (edgewiseSubdivisionRealizationMap K k) := by
  refine continuous_iff_faceInclusion.mpr fun ρ => ?_
  rw [edgewiseSubdivisionRealizationMap_comp_faceInclusion ρ
    ⟨_, biUnion_image_mem_of_mem_edgewiseSubdivision ρ.2⟩ (mem_biUnion_image ρ.1)]
  exact (continuous_faceInclusion K _).comp
    (continuous_edgewiseSubdivisionFaceMap (mem_biUnion_image ρ.1))

/-! ### Injectivity -/

/-- `k` times the coordinate sum over the vertices `≤ i` of the image of a point of the edgewise
subdivision is the combination of the numbers of entries `≤ i` of the vertices of its carrier. -/
private theorem mul_sum_le_edgewiseSubdivisionRealizationMap
    (x : Realization (K.edgewiseSubdivision k)) (i : ι) :
    (k : ℝ) * Finsupp.linearCombination ℝ (fun j : ι => if j ≤ i then (1 : ℝ) else 0)
        (edgewiseSubdivisionRealizationMap K k x : ι →₀ ℝ) =
      ∑ w ∈ x.1.support, x.1 w * #{l | w.1 l ≤ i} := by
  rw [edgewiseSubdivisionRealizationMap_val, Finsupp.apply_linearCombination,
    Finsupp.linearCombination_apply, Finsupp.sum, mul_sum]
  refine sum_congr rfl fun w _ => ?_
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr w.ne_zero
  rw [Function.comp_apply, linearCombination_edgewisePoint, sum_boole, smul_eq_mul]
  field_simp

open scoped Classical in
/-- Let `x` be a point of the edgewise subdivision, `u` a vertex of its carrier, and `θ` an offset
in the interval `[∑ w < u, x w, ∑ w ≤ u, x w)`. Then `k` times the coordinate sum over the
vertices `≤ i` of the image of `x`, minus `θ`, lies in `(c - 1, c]`, where `c` is the number of
entries of `u` that are `≤ i`. -/
private theorem card_sub_one_lt_and_le (x : Realization (K.edgewiseSubdivision k))
    {u : K.EdgewiseVertex k} (hu : u ∈ x.1.support) {θ : ℝ}
    (hθ : ∑ w ∈ x.1.support with w < u, x.1 w ≤ θ)
    (hθ' : θ < ∑ w ∈ x.1.support with w < u, x.1 w + x.1 u) (i : ι) :
    (#{l | u.1 l ≤ i} : ℝ) - 1 < ∑ w ∈ x.1.support, x.1 w * #{l | w.1 l ≤ i} - θ ∧
      ∑ w ∈ x.1.support, x.1 w * #{l | w.1 l ≤ i} - θ ≤ #{l | u.1 l ≤ i} := by
  set s := x.1.support
  have hρ : s ∈ K.edgewiseSubdivision k := support_mem _ x
  set c : K.EdgewiseVertex k → ℕ := fun w => #{l | w.1 l ≤ i}
  have hx0 (w : K.EdgewiseVertex k) : 0 ≤ x.1 w := Realization.nonneg _ x w
  have hsum : ∑ w ∈ s, x.1 w = 1 := Realization.sum_eq_one _ x
  -- Counts of vertices below `u` are `c u` or `c u + 1`, those above are `c u - 1` or `c u`.
  have hbelow (w) (hw : w ∈ s) (hwu : w ≤ u) : c u ≤ c w ∧ c w ≤ c u + 1 :=
    ⟨card_filter_le_card_filter_of_le hwu (p := (· ≤ i)) antitone_le,
      card_filter_le_card_filter_add_one_of_mem_edgewiseSubdivision hρ hw hu
        (p := (· ≤ i)) antitone_le⟩
  have habove (w) (hw : w ∈ s) (huw : u ≤ w) : c w ≤ c u ∧ c u ≤ c w + 1 :=
    ⟨card_filter_le_card_filter_of_le huw (p := (· ≤ i)) antitone_le,
      card_filter_le_card_filter_add_one_of_mem_edgewiseSubdivision hρ hu hw
        (p := (· ≤ i)) antitone_le⟩
  -- The mass of `x` splits into the parts below `u`, at `u`, and above `u`.
  have hsplit : ∑ w ∈ s with w < u, x.1 w + x.1 u + ∑ w ∈ s with u < w, x.1 w = 1 := by
    rw [← hsum, sum_filter, sum_filter, ← sum_ite_eq_of_mem' s u (fun w => x.1 w) hu,
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun w hw => ?_
    rcases lt_or_eq_or_lt_of_mem_edgewiseSubdivision hρ hw hu with h | rfl | h
    · simp [h, h.ne, h.not_gt]
    · simp
    · simp [h, h.ne', h.not_gt]
  have hT0 : 0 ≤ ∑ w ∈ s with w < u, x.1 w := sum_nonneg fun w _ => hx0 w
  have hR0 : 0 ≤ ∑ w ∈ s with u < w, x.1 w := sum_nonneg fun w _ => hx0 w
  -- The combination of counts is `c u` plus the weighted deviations from `c u`.
  have hdev : ∑ w ∈ s, x.1 w * (c w : ℝ) =
      c u + ∑ w ∈ s, x.1 w * ((c w : ℝ) - c u) := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hsum, one_mul, add_sub_cancel]
  rw [hdev]
  by_cases hA : ∀ w ∈ s, u < w → c w = c u
  · -- No count drops above `u`, so the deviation lies in `[0, ∑ w < u, x w]`.
    have hD : ∀ w ∈ s, 0 ≤ x.1 w * ((c w : ℝ) - c u) ∧
        x.1 w * ((c w : ℝ) - c u) ≤ if w < u then x.1 w else 0 := by
      intro w hw
      rcases lt_or_eq_or_lt_of_mem_edgewiseSubdivision hρ hw hu with h | rfl | h
      · obtain ⟨h₁, h₂⟩ := hbelow w hw h.le
        have h₁' : (c u : ℝ) ≤ c w := by exact_mod_cast h₁
        have h₂' : (c w : ℝ) ≤ c u + 1 := by exact_mod_cast h₂
        rw [ite_eq_left h]
        exact ⟨mul_nonneg (hx0 w) (by linarith), mul_le_of_le_one_right (hx0 w) (by linarith)⟩
      · simp
      · simp [hA w hw h, h.not_gt]
    have h₁ := sum_nonneg fun w hw => (hD w hw).1
    have h₂ := sum_le_sum fun w hw => (hD w hw).2
    rw [← sum_filter] at h₂
    constructor <;> linarith
  · -- Some count drops above `u`, so none rises below `u`, and the deviation lies in
    -- `[-∑ w > u, x w, 0]`.
    push Not at hA
    obtain ⟨w', hw', huw', hne⟩ := hA
    have hw'u : c w' + 1 = c u := by
      have := habove w' hw' huw'.le
      omega
    have hD : ∀ w ∈ s, -(if u < w then x.1 w else 0) ≤ x.1 w * ((c w : ℝ) - c u) ∧
        x.1 w * ((c w : ℝ) - c u) ≤ 0 := by
      intro w hw
      rcases lt_or_eq_or_lt_of_mem_edgewiseSubdivision hρ hw hu with h | rfl | h
      · have h₁ := (hbelow w hw h.le).1
        have h₂ : c w ≤ c w' + 1 :=
          card_filter_le_card_filter_add_one_of_mem_edgewiseSubdivision hρ hw hw'
            (p := (· ≤ i)) antitone_le
        have hcw : c w = c u := by omega
        simp [hcw, h.not_gt]
      · simp
      · obtain ⟨h₁, h₂⟩ := habove w hw h.le
        have h₁' : (c w : ℝ) ≤ c u := by exact_mod_cast h₁
        have h₂' : (c u : ℝ) ≤ c w + 1 := by exact_mod_cast h₂
        rw [ite_eq_left h]
        constructor
        · nlinarith [hx0 w]
        · exact mul_nonpos_of_nonneg_of_nonpos (hx0 w) (by linarith)
    have h₁ := sum_le_sum fun w hw => (hD w hw).1
    have h₂ := sum_nonpos fun w hw => (hD w hw).2
    rw [sum_neg_distrib, ← sum_filter] at h₁
    constructor <;> linarith

open scoped Classical in
/-- The intervals `[∑ w < u, x w, ∑ w ≤ u, x w)`, for the vertices `u` of the carrier of a point
`x` of the edgewise subdivision, cover `[0, 1)`. -/
private theorem exists_mem_support_sum_le_lt (x : Realization (K.edgewiseSubdivision k))
    {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    ∃ u ∈ x.1.support, ∑ w ∈ x.1.support with w < u, x.1 w ≤ θ ∧
      θ < ∑ w ∈ x.1.support with w < u, x.1 w + x.1 u := by
  set s := x.1.support
  have hρ : s ∈ K.edgewiseSubdivision k := support_mem _ x
  have hsum : ∑ w ∈ s, x.1 w = 1 := Realization.sum_eq_one _ x
  have hle (u) (hu : u ∈ s) : ∑ w ∈ s with w ≤ u, x.1 w = ∑ w ∈ s with w < u, x.1 w + x.1 u := by
    rw [show {w ∈ s | w ≤ u} = insert u {w ∈ s | w < u} by
      ext w
      simp only [mem_filter, mem_insert, le_iff_lt_or_eq]
      constructor
      · rintro ⟨hw, h | rfl⟩
        exacts [Or.inr ⟨hw, h⟩, Or.inl rfl]
      · rintro (rfl | ⟨hw, h⟩)
        exacts [⟨hu, Or.inr rfl⟩, ⟨hw, Or.inl h⟩],
      sum_insert (by simp), add_comm]
  -- A minimal vertex has nothing below it; take the largest vertex whose interval starts by `θ`.
  obtain ⟨m, hm⟩ := Finset.exists_minimal (mem_edgewiseSubdivision_iff.mp hρ).1
  obtain ⟨u, hu⟩ := Finset.exists_maximal (s := {u ∈ s | ∑ w ∈ s with w < u, x.1 w ≤ θ})
    ⟨m, mem_filter.mpr ⟨hm.prop, by
      rw [filter_eq_empty_iff.mpr fun w hw hwm => hwm.not_ge (hm.2 hw hwm.le), sum_empty]
      exact hθ₀⟩⟩
  obtain ⟨hus, huθ⟩ := mem_filter.mp hu.prop
  refine ⟨u, hus, huθ, lt_of_not_ge fun hlt => ?_⟩
  rcases {w ∈ s | u < w}.eq_empty_or_nonempty with hB | hB
  · -- Every vertex is at most `u`, so the interval of `u` ends at `1`.
    have hall : {w ∈ s | w ≤ u} = s := filter_true_of_mem fun w hw => by
      rcases lt_or_eq_or_lt_of_mem_edgewiseSubdivision hρ hw hus with h | rfl | h
      · exact h.le
      · exact le_rfl
      · exact absurd h (filter_eq_empty_iff.mp hB hw)
    rw [← hle u hus, hall, hsum] at hlt
    linarith
  · -- The next vertex `w` after `u` has its interval starting where that of `u` ends.
    obtain ⟨w, hw⟩ := Finset.exists_minimal hB
    obtain ⟨hws, huw⟩ := mem_filter.mp hw.prop
    have heq : {w' ∈ s | w' < w} = {w' ∈ s | w' ≤ u} := by
      ext w'
      simp only [mem_filter]
      refine ⟨fun ⟨hw's, hw'w⟩ => ⟨hw's, ?_⟩, fun ⟨hw's, hw'u⟩ => ⟨hw's, hw'u.trans_lt huw⟩⟩
      rcases lt_or_eq_or_lt_of_mem_edgewiseSubdivision hρ hw's hus with h | rfl | h
      · exact h.le
      · exact le_rfl
      · exact absurd (hw.2 (mem_filter.mpr ⟨hw's, h⟩) hw'w.le) hw'w.not_ge
    have hwθ : ∑ w' ∈ s with w' < w, x.1 w' ≤ θ := by
      rw [heq, hle u hus]
      exact hlt
    exact huw.not_ge (hu.2 (mem_filter.mpr ⟨hws, hwθ⟩) huw.le)

/-- A vertex of the edgewise subdivision is determined by a real vector `z` and an offset `θ` for
which, for every `i`, `z i - θ` lies in `(c - 1, c]`, where `c` is the number of its entries
`≤ i`. -/
private theorem eq_of_card_sub_one_lt_and_le {u w : K.EdgewiseVertex k} {z : ι → ℝ} {θ : ℝ}
    (hu : ∀ i, (#{l | u.1 l ≤ i} : ℝ) - 1 < z i - θ ∧ z i - θ ≤ #{l | u.1 l ≤ i})
    (hw : ∀ i, (#{l | w.1 l ≤ i} : ℝ) - 1 < z i - θ ∧ z i - θ ≤ #{l | w.1 l ≤ i}) :
    u = w := by
  -- Both counts are the least integer `≥ z i - θ`, and a monotone tuple is determined by its
  -- counts.
  have hle (u w : K.EdgewiseVertex k)
      (hu : ∀ i, (#{l | u.1 l ≤ i} : ℝ) - 1 < z i - θ ∧ z i - θ ≤ #{l | u.1 l ≤ i})
      (hw : ∀ i, (#{l | w.1 l ≤ i} : ℝ) - 1 < z i - θ ∧ z i - θ ≤ #{l | w.1 l ≤ i}) :
      u ≤ w := fun j => by
    have h : (#{l | w.1 l ≤ w.1 j} : ℝ) < #{l | u.1 l ≤ w.1 j} + 1 := by
      linarith [hu (w.1 j), hw (w.1 j)]
    have h' : #{l | w.1 l ≤ w.1 j} ≤ #{l | u.1 l ≤ w.1 j} :=
      Nat.lt_add_one_iff.mp (by exact_mod_cast h)
    exact (Tuple.lt_card_le_iff_apply_le_of_monotone u.2.1).mp
      (((Tuple.lt_card_le_iff_apply_le_of_monotone w.2.1).mpr le_rfl).trans_le h')
  exact le_antisymm (hle u w hu hw) (hle w u hw hu)

open scoped Classical in
/-- If two points of the edgewise subdivision have the same image, then every vertex `u` of the
carrier of the first is a vertex of the carrier of the second, and its interval
`[∑ w < u, x w, ∑ w ≤ u, x w)` for the first is contained in that for the second. -/
private theorem mem_support_and_Ico_subset {x x' : Realization (K.edgewiseSubdivision k)}
    (h : edgewiseSubdivisionRealizationMap K k x = edgewiseSubdivisionRealizationMap K k x')
    {u : K.EdgewiseVertex k} (hu : u ∈ x.1.support) :
    u ∈ x'.1.support ∧
      Set.Ico (∑ w ∈ x.1.support with w < u, x.1 w)
          (∑ w ∈ x.1.support with w < u, x.1 w + x.1 u) ⊆
        Set.Ico (∑ w ∈ x'.1.support with w < u, x'.1 w)
          (∑ w ∈ x'.1.support with w < u, x'.1 w + x'.1 u) := by
  -- Every offset `θ` in the interval of `u` for `x` lies in the interval of some vertex `w` for
  -- `x'`, and the counts of both `u` and `w` are then determined by the common image.
  have key : ∀ θ ∈ Set.Ico (∑ w ∈ x.1.support with w < u, x.1 w)
      (∑ w ∈ x.1.support with w < u, x.1 w + x.1 u), u ∈ x'.1.support ∧
        θ ∈ Set.Ico (∑ w ∈ x'.1.support with w < u, x'.1 w)
          (∑ w ∈ x'.1.support with w < u, x'.1 w + x'.1 u) := by
    rintro θ ⟨hθ, hθ'⟩
    have hsplit : ∑ w ∈ x.1.support with w < u, x.1 w + x.1 u ≤ 1 := by
      refine (?_ : _ ≤ ∑ w ∈ x.1.support, x.1 w).trans_eq (Realization.sum_eq_one _ x)
      rw [← sum_filter_add_sum_filter_not x.1.support (· < u)]
      gcongr
      · exact single_le_sum (fun w _ => Realization.nonneg _ x w)
          (mem_filter.mpr ⟨hu, lt_irrefl u⟩)
    obtain ⟨w, hw, hwθ, hwθ'⟩ := exists_mem_support_sum_le_lt x'
      ((sum_nonneg fun w _ => Realization.nonneg _ x w).trans hθ) (hθ'.trans_le hsplit)
    have hcu := card_sub_one_lt_and_le x hu hθ hθ'
    have hcw := card_sub_one_lt_and_le x' hw hwθ hwθ'
    simp only [← mul_sum_le_edgewiseSubdivisionRealizationMap, h] at hcu hcw
    obtain rfl := eq_of_card_sub_one_lt_and_le hcw hcu
    exact ⟨hw, hwθ, hwθ'⟩
  exact ⟨(key _ ⟨le_rfl, lt_add_of_pos_right _ (Realization.pos_of_mem_support _ x hu)⟩).1,
    fun θ hθ => (key θ hθ).2⟩

/-- The edgewise realization map is injective: a point of the realization of `K` determines the
simplex of the edgewise subdivision carrying a preimage, and its barycentric coordinates
there. -/
theorem edgewiseSubdivisionRealizationMap_injective :
    Function.Injective (edgewiseSubdivisionRealizationMap K k) := by
  classical
  intro x x' h
  refine Subtype.ext (Finsupp.ext fun u => ?_)
  by_cases hu : u ∈ x.1.support
  · obtain ⟨hu', h₁⟩ := mem_support_and_Ico_subset h hu
    obtain ⟨-, h₂⟩ := mem_support_and_Ico_subset h.symm hu'
    have hpos := Realization.pos_of_mem_support _ x hu
    have := (Set.Ico_eq_Ico_iff (Or.inl (lt_add_of_pos_right _ hpos))).mp (h₁.antisymm h₂)
    linarith [this.1, this.2]
  · have hu' : u ∉ x'.1.support := fun hu' => hu (mem_support_and_Ico_subset h.symm hu').1
    rw [Finsupp.notMem_support_iff.mp hu, Finsupp.notMem_support_iff.mp hu']

end AbstractSimplicialComplex

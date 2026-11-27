/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height

/-!
# Heights on regions

A height function on a region `R` is a function `H : ℤ × ℤ → ℤ` whose increment along every edge
of `R` lies in `{0, 1}`; only its values on the vertices of `R` matter. Its free tiling is the set
of edges of `R` along which the increment is not the neutral one. For a simply connected region
`R`, a vertex `v₀` of `R` and `m : ℤ`, this is a bijection from the height functions on `R` with
`H(v₀) = m` (normalised to vanish off the vertices of `R`) onto the free tilings of `R`; its inverse
sends a free tiling to the primitive of its height cochain. The tilings of `R` correspond to the
height functions whose increment along every boundary edge is neutral. Restricting a plane tiling
to `R` commutes with restricting its height function.

## Main definitions

* `TauCeti.IsHeightFunctionOn R H`: the increments of `H` along the edges of `R` lie in `{0, 1}`.
* `TauCeti.tilingOfHeightOn R H`: the edges of `R` along which the increment of `H` is not neutral.

## Main statements

* `TauCeti.IsHeightFunctionOn.isFreeTiling_tilingOfHeightOn`: the free tiling of a height function
  on `R` is a free tiling of `R`; `TauCeti.IsHeightFunctionOn.isCochainPrimitiveOn` makes `H` a
  primitive of its height cochain on `R`.
* `TauCeti.IsCochainPrimitiveOn.isHeightFunctionOn`,
  `TauCeti.IsFreeTiling.tilingOfHeightOn_eq_of_isCochainPrimitiveOn`: a primitive on `R` of the
  height cochain of a free tiling `M` of `R` is a height function on `R` whose free tiling is `M`.
* `TauCeti.IsSimplyConnectedRegion.exists_isHeightFunctionOn`: on a simply connected region every
  free tiling has a height function taking any prescribed value at any vertex;
  `TauCeti.IsConnectedRegion.eqOn_of_tilingOfHeightOn_eq`: on a connected region it is unique on
  the vertices.
* `TauCeti.IsSimplyConnectedRegion.tilingOfHeightOn_bijOn`: free tilings of a simply connected
  region correspond bijectively to normalised height functions on it.
* `TauCeti.IsHeightFunctionOn.isTiling_tilingOfHeightOn_iff`: the free tiling of a height function
  is a tiling exactly when the increment along every boundary edge is neutral.
* `TauCeti.IsTiling.tilingOfHeightOn_tilingHeight`: the free tiling on `R` of the height function of
  a plane tiling `M` is the restriction `M ∩ E(R)`.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

namespace TauCeti

variable {R : Set TriFace} {M : Set TriEdge} {H H' : ℤ × ℤ → ℤ}

/-- A height function on the region `R`: the increment of `H` along every edge of `R` is `0` or
`1`. Only the values of `H` on the vertices of `R` matter. -/
def IsHeightFunctionOn (R : Set TriFace) (H : ℤ × ℤ → ℤ) : Prop :=
  ∀ e ∈ regionEdges R, H e.target - H e.v = 0 ∨ H e.target - H e.v = 1

/-- The free tiling of a height function on `R`: the edges of `R` along which the increment of `H`
is not the neutral one. -/
def tilingOfHeightOn (R : Set TriFace) (H : ℤ × ℤ → ℤ) : Set TriEdge :=
  tilingOfHeight H ∩ regionEdges R

theorem isHeightFunctionOn_def : IsHeightFunctionOn R H ↔
    ∀ e ∈ regionEdges R, H e.target - H e.v = 0 ∨ H e.target - H e.v = 1 := Iff.rfl

theorem tilingOfHeightOn_def (R : Set TriFace) (H : ℤ × ℤ → ℤ) :
    tilingOfHeightOn R H = tilingOfHeight H ∩ regionEdges R := (rfl)

@[simp] theorem mem_tilingOfHeightOn {e : TriEdge} : e ∈ tilingOfHeightOn R H ↔
    H e.target - H e.v = 1 - neutralIncrement e ∧ e ∈ regionEdges R := by
  rw [tilingOfHeightOn_def, Set.mem_inter_iff, mem_tilingOfHeight]

@[simp] theorem isHeightFunctionOn_univ : IsHeightFunctionOn Set.univ H ↔ IsHeightFunction H := by
  simp [isHeightFunctionOn_def, isHeightFunction_def, mem_regionEdges_iff]

@[simp] theorem tilingOfHeightOn_univ : tilingOfHeightOn Set.univ H = tilingOfHeight H := by
  ext e
  simp [mem_regionEdges_iff]

theorem IsHeightFunction.isHeightFunctionOn (hH : IsHeightFunction H) (R : Set TriFace) :
    IsHeightFunctionOn R H :=
  fun e _ => isHeightFunction_def.1 hH e

theorem IsHeightFunctionOn.mono {S : Set TriFace} (hH : IsHeightFunctionOn S H) (hRS : R ⊆ S) :
    IsHeightFunctionOn R H :=
  fun e he => hH e (regionEdges_mono hRS he)

/-- Two functions agreeing on the vertices of `R` have the same increment along every edge of
`R`. -/
theorem _root_.Set.EqOn.target_sub_v_eq (hHH' : Set.EqOn H H' (regionVertices R)) {e : TriEdge}
    (he : e ∈ regionEdges R) : H e.target - H e.v = H' e.target - H' e.v := by
  rw [hHH' (mem_regionVertices_of_mem_endpoints he (TriEdge.mem_endpoints.2 (Or.inr rfl))),
    hHH' (mem_regionVertices_of_mem_endpoints he (TriEdge.mem_endpoints.2 (Or.inl rfl)))]

/-- Two functions agreeing on the vertices of `R` are height functions on `R` together. -/
theorem IsHeightFunctionOn.congr (hH : IsHeightFunctionOn R H)
    (hHH' : Set.EqOn H H' (regionVertices R)) : IsHeightFunctionOn R H' := fun e he => by
  rw [← hHH'.target_sub_v_eq he]
  exact hH e he

/-- Two functions agreeing on the vertices of `R` have the same free tiling on `R`. -/
theorem tilingOfHeightOn_congr (hHH' : Set.EqOn H H' (regionVertices R)) :
    tilingOfHeightOn R H = tilingOfHeightOn R H' := by
  ext e
  simp only [mem_tilingOfHeightOn]
  exact and_congr_left fun he => by rw [hHH'.target_sub_v_eq he]

namespace IsHeightFunctionOn

variable (hH : IsHeightFunctionOn R H)
include hH

/-- **The free tiling of a height function on `R` is a free tiling of `R`.** -/
theorem isFreeTiling_tilingOfHeightOn : IsFreeTiling R (tilingOfHeightOn R H) := by
  refine isFreeTiling_def.2 ⟨Set.inter_subset_right, fun f hf => ?_⟩
  obtain ⟨e, ⟨he, hef⟩, hu⟩ := f.existsUnique_mem_tilingOfHeight_edges (H := H) fun k =>
    hH _ (edges_subset_regionEdges hf (f.edge_mem_edges k))
  exact ⟨e, ⟨mem_tilingOfHeightOn.2 ⟨mem_tilingOfHeight.1 he, edges_subset_regionEdges hf hef⟩,
    hef⟩, fun e' he' => hu e' ⟨mem_tilingOfHeight.2 (mem_tilingOfHeightOn.1 he'.1).1, he'.2⟩⟩

/-- A height function on `R` is a primitive on `R` of the height cochain of its free tiling. -/
theorem isCochainPrimitiveOn :
    IsCochainPrimitiveOn R (heightCochain (tilingOfHeightOn R H)) H := by
  rw [isCochainPrimitiveOn_def]
  intro e he
  by_cases hm : e ∈ tilingOfHeightOn R H
  · rw [heightCochain_of_mem hm, (mem_tilingOfHeightOn.1 hm).1]
  · rw [heightCochain_of_notMem hm]
    rw [mem_tilingOfHeightOn, not_and_or] at hm
    rcases hm with hm | hm
    · exact ((ne_one_sub_neutralIncrement_iff (hH e he)).1 hm).symm
    · exact absurd he hm

/-- Along an edge of `R`, the height cochain of the free tiling of a height function on `R` is
the increment of the height function. -/
theorem heightCochain_tilingOfHeightOn {e : TriEdge} (he : e ∈ regionEdges R) :
    heightCochain (tilingOfHeightOn R H) e = H e.target - H e.v :=
  isCochainPrimitiveOn_def.1 hH.isCochainPrimitiveOn e he

end IsHeightFunctionOn

/-- A primitive on `R` of the height cochain of any set of edges is a height function on `R`. -/
theorem IsCochainPrimitiveOn.isHeightFunctionOn
    (hg : IsCochainPrimitiveOn R (heightCochain M) H) : IsHeightFunctionOn R H := fun e he => by
  rw [← isCochainPrimitiveOn_def.1 hg e he]
  exact heightCochain_eq_zero_or_eq_one M e

namespace IsFreeTiling

variable (h : IsFreeTiling R M)
include h

/-- The free tiling of a primitive on `R` of the height cochain of a free tiling `M` of `R` is
`M`. -/
theorem tilingOfHeightOn_eq_of_isCochainPrimitiveOn
    (hg : IsCochainPrimitiveOn R (heightCochain M) H) : tilingOfHeightOn R H = M := by
  ext e
  rw [mem_tilingOfHeightOn]
  by_cases he : e ∈ regionEdges R
  · rw [← isCochainPrimitiveOn_def.1 hg e he, heightCochain_eq_one_sub_neutralIncrement_iff]
    exact ⟨fun h' => h'.1, fun h' => ⟨h', he⟩⟩
  · exact ⟨fun h' => absurd h'.2 he, fun h' => absurd ((isFreeTiling_def.1 h).1 h') he⟩

end IsFreeTiling

/-- **Existence of heights on simply connected regions**: a free tiling `M` of a simply connected
region `R` has a height function on `R` with free tiling `M` taking any prescribed value `m` at any
point `v₀`. -/
theorem IsSimplyConnectedRegion.exists_isHeightFunctionOn (hR : IsSimplyConnectedRegion R)
    (h : IsFreeTiling R M) (v₀ : ℤ × ℤ) (m : ℤ) :
    ∃ H, IsHeightFunctionOn R H ∧ tilingOfHeightOn R H = M ∧ H v₀ = m := by
  obtain ⟨g, hg⟩ := isExactCochainOn_def.1
    (hR.isExactCochainOn_of_isClosedCochainOn _ h.isClosedCochainOn_heightCochain)
  have hg' := hg.add_const (m - g v₀)
  refine ⟨_, hg'.isHeightFunctionOn,
    h.tilingOfHeightOn_eq_of_isCochainPrimitiveOn hg', ?_⟩
  simp

/-- **Uniqueness of heights on connected regions**: two height functions on a connected region
with the same free tiling and the same value at a vertex `v₀` agree on the vertices. -/
theorem IsConnectedRegion.eqOn_of_tilingOfHeightOn_eq (hR : IsConnectedRegion R)
    (hH : IsHeightFunctionOn R H) (hH' : IsHeightFunctionOn R H')
    (hHH' : tilingOfHeightOn R H = tilingOfHeightOn R H') {v₀ : ℤ × ℤ}
    (hv₀ : v₀ ∈ regionVertices R) (h₀ : H v₀ = H' v₀) : Set.EqOn H H' (regionVertices R) :=
  fun u hu => by
    have := hR.sub_eq_sub_of_isCochainPrimitiveOn hH.isCochainPrimitiveOn
      (hHH' ▸ hH'.isCochainPrimitiveOn) hu hv₀
    omega

/-- **Heights on simply connected regions.** For a simply connected region `R`, a vertex `v₀` of
`R` and `m : ℤ`, `tilingOfHeightOn R` is a bijection from the height functions on `R` with
`H(v₀) = m`, normalised to vanish off the vertices of `R`, onto the free tilings of `R`. -/
theorem IsSimplyConnectedRegion.tilingOfHeightOn_bijOn (hR : IsSimplyConnectedRegion R)
    {v₀ : ℤ × ℤ} (hv₀ : v₀ ∈ regionVertices R) (m : ℤ) :
    Set.BijOn (tilingOfHeightOn R)
      {H | IsHeightFunctionOn R H ∧ H v₀ = m ∧ ∀ u ∉ regionVertices R, H u = 0}
      {M | IsFreeTiling R M} := by
  classical
  refine ⟨fun H hH => hH.1.isFreeTiling_tilingOfHeightOn, fun H hH H' hH' hHH' => ?_,
    fun M hM => ?_⟩
  · have hEq := hR.isConnectedRegion.eqOn_of_tilingOfHeightOn_eq hH.1 hH'.1 hHH' hv₀
      (hH.2.1.trans hH'.2.1.symm)
    funext u
    by_cases hu : u ∈ regionVertices R
    · exact hEq hu
    · rw [hH.2.2 u hu, hH'.2.2 u hu]
  · obtain ⟨H, hH, hHM, hHm⟩ := hR.exists_isHeightFunctionOn hM v₀ m
    let H₀ : ℤ × ℤ → ℤ := fun u => if u ∈ regionVertices R then H u else 0
    have hEq : Set.EqOn H H₀ (regionVertices R) := fun u hu => by simp [H₀, hu]
    refine ⟨H₀, ⟨hH.congr hEq, by simp [H₀, hv₀, hHm], fun u hu => by simp [H₀, hu]⟩, ?_⟩
    rw [← tilingOfHeightOn_congr hEq, hHM]

/-- **Tilings are the heights with neutral boundary increments**: the free tiling of a height
function on `R` is a tiling of `R` exactly when the increment of `H` along every boundary edge of
`R` is the neutral one. -/
theorem IsHeightFunctionOn.isTiling_tilingOfHeightOn_iff (hH : IsHeightFunctionOn R H) :
    IsTiling R (tilingOfHeightOn R H) ↔
      ∀ e ∈ boundaryEdges R, H e.target - H e.v = neutralIncrement e := by
  rw [hH.isFreeTiling_tilingOfHeightOn.isTiling_iff, Set.disjoint_right]
  refine forall₂_congr fun e he => ?_
  have heR := boundaryEdges_subset_regionEdges he
  rw [mem_tilingOfHeightOn, not_and_or, or_iff_left (not_not.2 heR)]
  exact ne_one_sub_neutralIncrement_iff (hH e heR)

/-- **Restriction commutes with heights**: the free tiling on a region `R` of the height function
of a plane tiling `M` is the restriction `M ∩ E(R)`. That this height function is a height function
on `R` follows from `IsTiling.isHeightFunction_tilingHeight` and
`IsHeightFunction.isHeightFunctionOn`. -/
theorem IsTiling.tilingOfHeightOn_tilingHeight (h : IsTiling Set.univ M) (R : Set TriFace) :
    tilingOfHeightOn R (tilingHeight M) = M ∩ regionEdges R := by
  rw [tilingOfHeightOn_def, h.tilingOfHeight_tilingHeight]

end TauCeti

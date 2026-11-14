/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
public import TauCeti.Combinatorics.Hypergraph.Complex.TwoComplex.Relabel
import Mathlib.Basic.Real.Pointwise
import TauCeti.Order.Hom.PowersetCard

/-!
# Orientation independence, relabelling, and change of coefficients for 1-cochains

Reversing an oriented edge inverts its gauge-transformed value `(β u)⁻¹ * α u v * β v`, so every
group norm assigns the same weight to both orientations of an edge. Consequently `Cochain.cost`
equals an unoriented sum over `X.edges`, and hence `Cochain.cost` (with reindexed gauge) and its
infimum `Cochain.gaugeDist` do not depend on the `LinearOrder` chosen on `V` and are invariant
under relabelling vertices along any bijection `V ≃ W`.

When the group norm `ℓ` is conjugation invariant, cyclically rotating or reversing the vertices of a
filled triangle also preserves the norm of `Cochain.holonomy`, and every holonomy norm around three
mutually adjacent vertices bounds `Cochain.gaugeDist` from below
(`Cochain.norm_holonomy_le_gaugeDist`), witnessing positive gauge distance over any nontrivial group
once `X.triangles` is nonempty. Moreover, `Cochain.defect` equals an unoriented sum over
`X.triangles`, is independent of the vertex `LinearOrder`, and is preserved by vertex relabellings.

Pushing a cochain forward along a norm-nonincreasing homomorphism `φ : G →* H` (`Cochain.map φ`)
does not increase `defect` or `gaugeDist`. Specializing `φ` to `L.subtype` for a subgroup `L ≤ G`
shows that embedding `L`-valued cochains into `G` preserves `defect` and `cost` (on embedded gauges)
and can only decrease `gaugeDist`.

## References

* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles I: equivalence*,
  arXiv:2310.17474v2, Eur. J. Math. 11 (2025), art. 13, §5.1.
* M. Chapman and A. Lubotzky, *Stability of homomorphisms, coverings and cocycles II: examples,
  applications and open problems*, arXiv:2311.06706v3, Adv. Math. 463 (2025), 110117, §2.2.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

namespace Cochain

/-! ### Edge and holonomy symmetries and unoriented sums -/

section Unoriented

variable {V G : Type*} [Group G] {X : TwoComplex V}

/-- Reversing any pair of vertices inverts its gauge-transformed value, so any group norm gives the
same weight to both orientations. -/
theorem norm_inv_mul_apply_mul_swap (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (u v : V) :
    ℓ ((β v)⁻¹ * α v u * β u) = ℓ ((β u)⁻¹ * α u v * β v) := by
  have hinv : ((β u)⁻¹ * α u v * β v)⁻¹ = (β v)⁻¹ * α v u * β u := by rw [α.apply_swap u v]; group
  rw [← hinv, map_inv_eq_map]

/-- Under a conjugation-invariant norm, cyclically rotating a triple preserves the norm of its
holonomy. -/
theorem norm_holonomy_rotate {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (u v w : V) :
    ℓ (α.holonomy v w u) = ℓ (α.holonomy u v w) := by
  simpa only [holonomy_def, mul_assoc, GroupNorm.toGroupSeminorm_eq_coe] using
    hℓ.map_mul_comm (α v w * α w u) (α u v)

/-- Under a conjugation-invariant norm, exchanging the first two vertices of any triple preserves
the norm of the holonomy. -/
theorem norm_holonomy_swap {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (u v w : V) :
    ℓ (α.holonomy v u w) = ℓ (α.holonomy u v w) := by
  rw [← map_inv_eq_map ℓ (α.holonomy v u w), α.inv_holonomy, α.norm_holonomy_rotate hℓ u v w]

/-- Under a conjugation-invariant norm, all six vertex orderings of a filled triangle have the same
holonomy norm. -/
theorem norm_holonomy_eq_of_mem_triangles {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) {t : Finset V}
    (ht : t ∈ X.triangles) {u v w u' v' w' : V}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu' : u' ∈ t) (hv' : v' ∈ t) (hw' : w' ∈ t)
    (hu'v' : u' ≠ v') (hu'w' : u' ≠ w') (hv'w' : v' ≠ w') :
    ℓ (α.holonomy u' v' w') = ℓ (α.holonomy u v w) := by
  classical
  have hcard3 : ({u, v, w} : Finset V).card = 3 := card_triple_eq_three_iff.mpr ⟨huv, huw, hvw⟩
  have ht_eq : t = {u, v, w} :=
    (eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv, hw])
      (by rw [X.triangle_card t ht, hcard3])).symm
  rw [ht_eq] at hu' hv' hw'
  simp only [mem_insert, mem_singleton] at hu' hv' hw'
  rcases hu' with h₁ | h₁ | h₁ <;> rcases hv' with h₂ | h₂ | h₂ <;> rcases hw' with h₃ | h₃ | h₃
  all_goals rw [h₁, h₂] at hu'v'; rw [h₁, h₃] at hu'w'; rw [h₂, h₃] at hv'w'
  all_goals try exact (hu'v' rfl).elim
  all_goals try exact (hu'w' rfl).elim
  all_goals try exact (hv'w' rfl).elim
  all_goals rw [h₁, h₂, h₃]
  · rw [α.norm_holonomy_rotate hℓ v u w, α.norm_holonomy_swap hℓ u v w]
  · exact α.norm_holonomy_swap hℓ u v w
  · exact α.norm_holonomy_rotate hℓ u v w
  · rw [α.norm_holonomy_rotate hℓ v w u, α.norm_holonomy_rotate hℓ u v w]
  · rw [α.norm_holonomy_swap hℓ v w u, α.norm_holonomy_rotate hℓ u v w]

/-- The gauge cost contribution of an unoriented edge `e`, or `0` if `e ∉ X.edges`. -/
noncomputable def edgeCost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (e : Finset V) : ℝ := by
  classical
  exact if he : e ∈ X.edges then
    ℓ ((β (X.exists_vertices_of_mem_edges he).choose)⁻¹ *
      α (X.exists_vertices_of_mem_edges he).choose
        (X.exists_vertices_of_mem_edges he).choose_spec.choose *
      β (X.exists_vertices_of_mem_edges he).choose_spec.choose)
  else 0

/-- Evaluating `edgeCost` on any edge `e ∈ X.edges` via its two distinct endpoints. -/
theorem edgeCost_of_mem_edges (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {e : Finset V} (he : e ∈ X.edges) {u v : V} (huv : u ≠ v) (hu : u ∈ e) (hv : v ∈ e) :
    α.edgeCost ℓ β e = ℓ ((β u)⁻¹ * α u v * β v) := by
  classical
  simp only [edgeCost, he, ↓reduceDIte]
  obtain ⟨hu'v', hu', hv'⟩ := (X.exists_vertices_of_mem_edges he).choose_spec.choose_spec
  have he₁ :
      ({(X.exists_vertices_of_mem_edges he).choose,
        (X.exists_vertices_of_mem_edges he).choose_spec.choose} : Finset V) = e :=
    eq_of_subset_of_card_le (insert_subset_iff.mpr ⟨hu', singleton_subset_iff.mpr hv'⟩)
      (by rw [X.edge_card e he, card_pair hu'v'])
  have he₂ : ({u, v} : Finset V) = e :=
    eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv])
      (by rw [X.edge_card e he, card_pair huv])
  have hpair := he₁.trans he₂.symm
  rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
  rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₂, h₁]
  · rw [h₂, h₁]; exact α.norm_inv_mul_apply_mul_swap ℓ β u v

/-- Evaluating `edgeCost` directly on a pair `{u, v} ∈ X.edges`. -/
@[simp, grind =]
theorem edgeCost_pair [DecidableEq V] (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {u v : V} (he : ({u, v} : Finset V) ∈ X.edges) :
    α.edgeCost ℓ β {u, v} = ℓ ((β u)⁻¹ * α u v * β v) :=
  α.edgeCost_of_mem_edges ℓ β he ((X.adj_iff_pair_mem_edges u v).mpr he).ne (by simp) (by simp)

@[simp]
theorem edgeCost_of_notMem_edges (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {e : Finset V} (he : e ∉ X.edges) : α.edgeCost ℓ β e = 0 := by classical simp [edgeCost, he]

theorem edgeCost_nonneg (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (e : Finset V) :
    0 ≤ α.edgeCost ℓ β e := by
  classical
  by_cases he : e ∈ X.edges <;> simp [edgeCost, he, apply_nonneg]

@[simp]
theorem edgeCost_one_one (ℓ : GroupNorm G) (e : Finset V) :
    (1 : Cochain X G).edgeCost ℓ 1 e = 0 := by
  classical
  by_cases he : e ∈ X.edges <;> simp [edgeCost, he]

@[simp]
theorem edgeCost_smul (ℓ : GroupNorm G) (α : Cochain X G) (β γ : V → G) (e : Finset V) :
    (β • α).edgeCost ℓ γ e = α.edgeCost ℓ (β * γ) e := by
  by_cases he : e ∈ X.edges
  · obtain ⟨u, v, huv, hu, hv⟩ := X.exists_vertices_of_mem_edges he
    rw [(β • α).edgeCost_of_mem_edges ℓ γ he huv hu hv,
      α.edgeCost_of_mem_edges ℓ (β * γ) he huv hu hv]
    simp [smul_apply_of_adj β α ((X.adj_iff u v).mpr ⟨huv, e, he, hu, hv⟩), mul_assoc]
  · simp [he]

/-- The holonomy defect of an unoriented triangle `t`, or `0` if `t ∉ X.triangles`. Well-defined
independently of orientation whenever `ℓ` is conjugation invariant. -/
noncomputable def triangleDefect (ℓ : GroupNorm G) (α : Cochain X G) (t : Finset V) : ℝ := by
  classical
  exact if ht : t ∈ X.triangles then
    ℓ (α.holonomy
      (X.exists_vertices_of_mem_triangles ht).choose
      (X.exists_vertices_of_mem_triangles ht).choose_spec.choose
      (X.exists_vertices_of_mem_triangles ht).choose_spec.choose_spec.choose)
  else 0

/-- Under a conjugation-invariant norm, `triangleDefect` on `t ∈ X.triangles` agrees with the norm
of the holonomy in any ordering of the three vertices of `t`. -/
theorem triangleDefect_of_mem_triangles {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) {t : Finset V}
    (ht : t ∈ X.triangles) {u v w : V} (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    α.triangleDefect ℓ t = ℓ (α.holonomy u v w) := by
  classical
  simp only [triangleDefect, ht, ↓reduceDIte]
  obtain ⟨hu'v', hu'w', hv'w', hu', hv', hw'⟩ :=
    (X.exists_vertices_of_mem_triangles ht).choose_spec.choose_spec.choose_spec
  exact α.norm_holonomy_eq_of_mem_triangles hℓ ht hu hv hw huv huw hvw hu' hv' hw' hu'v' hu'w' hv'w'

/-- Under a conjugation-invariant norm, evaluating `triangleDefect` directly on a filled triangle
`{u, v, w} ∈ X.triangles`. -/
theorem triangleDefect_triple [DecidableEq V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) {u v w : V}
    (ht : ({u, v, w} : Finset V) ∈ X.triangles) :
    α.triangleDefect ℓ {u, v, w} = ℓ (α.holonomy u v w) := by
  obtain ⟨huv, huw, hvw⟩ := card_triple_eq_three_iff.mp (X.triangle_card _ ht)
  exact α.triangleDefect_of_mem_triangles hℓ ht (by simp) (by simp) (by simp) huv huw hvw

@[simp]
theorem triangleDefect_of_notMem_triangles (ℓ : GroupNorm G) (α : Cochain X G)
    {t : Finset V} (ht : t ∉ X.triangles) : α.triangleDefect ℓ t = 0 := by
  classical simp [triangleDefect, ht]

theorem triangleDefect_nonneg (ℓ : GroupNorm G) (α : Cochain X G) (t : Finset V) :
    0 ≤ α.triangleDefect ℓ t := by
  classical
  by_cases ht : t ∈ X.triangles <;> simp [triangleDefect, ht, apply_nonneg]

@[simp]
theorem triangleDefect_one (ℓ : GroupNorm G) (t : Finset V) :
    (1 : Cochain X G).triangleDefect ℓ t = 0 := by
  classical
  by_cases ht : t ∈ X.triangles <;> simp [triangleDefect, ht]

theorem triangleDefect_smul {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (β : V → G) (t : Finset V) :
    (β • α).triangleDefect ℓ t = α.triangleDefect ℓ t := by
  by_cases ht : t ∈ X.triangles
  · obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw⟩ := X.exists_vertices_of_mem_triangles ht
    rw [(β • α).triangleDefect_of_mem_triangles hℓ ht hu hv hw huv huw hvw,
      α.triangleDefect_of_mem_triangles hℓ ht hu hv hw huv huw hvw,
      holonomy_smul β α (X.adj_of_mem_triangles ht hu hv huv)
        (X.adj_of_mem_triangles ht hv hw hvw) (X.adj_of_mem_triangles ht hw hu huw.symm)]
    exact hℓ.map_inv_mul_mul (α.holonomy u v w) (β u)
  · simp [ht]

/-- `cost` equals the sum of `edgeCost` over the unoriented edges `X.edges`. -/
theorem cost_eq_sum_edges [Fintype V] [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G)
    (β : V → G) : α.cost ℓ β = ∑ e ∈ X.edges, α.edgeCost ℓ β e := by
  rw [cost_def]
  refine sum_bij (fun p _ => ({p.1, p.2} : Finset V)) (fun p hp => (mem_filter.mp hp).2.2) ?_ ?_
    (fun p hp => (α.edgeCost_pair ℓ β (mem_filter.mp hp).2.2).symm)
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ hpair
    have hlt₁ : u₁ < v₁ := (mem_filter.mp hp₁).2.1
    have hlt₂ : u₂ < v₂ := (mem_filter.mp hp₂).2.1
    rw [← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff] at hpair
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm hlt₁ hlt₂).elim
  · intro e he
    obtain ⟨u, v, hlt, hset⟩ := X.exists_increasing_of_mem_edges he
    exact ⟨(u, v), mem_filter.mpr ⟨mem_univ _, hlt, hset ▸ he⟩, hset⟩

/-- Under a conjugation-invariant norm, the holonomy norm around three mutually adjacent vertices
is bounded above by the cost of any gauge `β`. -/
theorem norm_holonomy_le_cost [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (β : V → G) {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    ℓ (α.holonomy u v w) ≤ α.cost ℓ β := by
  suffices h1 : ∀ γ : Cochain X G, ℓ (γ.holonomy u v w) ≤ γ.cost ℓ 1 by
    have hconj : ℓ ((β • α).holonomy u v w) = ℓ (α.holonomy u v w) := by
      rw [holonomy_smul β α huv hvw hwu]; exact hℓ.map_inv_mul_mul _ (β u)
    simpa [hconj, cost_smul] using h1 (β • α)
  intro γ
  have he₁ : ({u, v} : Finset V) ∈ X.edges := (X.adj_iff_pair_mem_edges u v).mp huv
  have he₂ : ({v, w} : Finset V) ∈ X.edges := (X.adj_iff_pair_mem_edges v w).mp hvw
  have he₃ : ({w, u} : Finset V) ∈ X.edges := (X.adj_iff_pair_mem_edges w u).mp hwu
  have hne {a b c : V} (hab : a ≠ b) (hac : a ≠ c) : ({a, b} : Finset V) ≠ {b, c} := by
    rw [ne_eq, ← coe_inj, coe_pair, coe_pair, Set.pair_eq_pair_iff]
    rintro (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> contradiction
  have hsub : ({{u, v}, {v, w}, {w, u}} : Finset (Finset V)) ⊆ X.edges := by
    simp [insert_subset_iff, he₁, he₂, he₃]
  have hsum := sum_le_sum_of_subset_of_nonneg hsub fun e _ _ => γ.edgeCost_nonneg ℓ 1 e
  rw [← γ.cost_eq_sum_edges ℓ 1,
    sum_insert (by simp [hne huv.ne hwu.ne.symm, (hne hwu.ne hvw.ne.symm).symm]),
    sum_pair (hne hvw.ne huv.ne.symm),
    γ.edgeCost_pair ℓ 1 he₁, γ.edgeCost_pair ℓ 1 he₂, γ.edgeCost_pair ℓ 1 he₃] at hsum
  simp only [Pi.one_apply, inv_one, one_mul, mul_one, ← add_assoc] at hsum
  rw [holonomy_def]
  exact ((map_mul_le_add ℓ _ _).trans (add_le_add (map_mul_le_add ℓ _ _) le_rfl)).trans hsum

/-- Under a conjugation-invariant norm, the holonomy norm around three mutually adjacent vertices
bounds `gaugeDist` from below. -/
theorem norm_holonomy_le_gaugeDist [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    ℓ (α.holonomy u v w) ≤ α.gaugeDist ℓ :=
  (α.le_gaugeDist_iff ℓ).mpr fun β => α.norm_holonomy_le_cost hℓ β huv hvw hwu

/-- Under a conjugation-invariant norm, any cochain with a non-identity holonomy around three
mutually adjacent vertices has strictly positive gauge distance, without requiring `G` to be
finite. -/
theorem gaugeDist_pos_of_holonomy_ne_one_of_isConjInvariant [Fintype V] [LinearOrder V]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) {α : Cochain X G} {u v w : V}
    (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u)
    (h : α.holonomy u v w ≠ 1) : 0 < α.gaugeDist ℓ :=
  lt_of_lt_of_le ((apply_nonneg ℓ _).lt_of_ne' (mt (map_eq_zero_iff_eq_one ℓ).mp h))
    (α.norm_holonomy_le_gaugeDist hℓ huv hvw hwu)

/-- Under a conjugation-invariant norm, `defect` equals the sum of `triangleDefect` over the
unoriented triangles `X.triangles`. -/
theorem defect_eq_sum_triangles [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    α.defect ℓ = ∑ t ∈ X.triangles, α.triangleDefect ℓ t := by
  rw [defect_def]
  refine sum_bij (fun p _ => ({p.1, p.2.1, p.2.2} : Finset V))
    (fun p hp => (mem_filter.mp hp).2.2.2) ?_ ?_
    (fun p hp => (α.triangleDefect_triple hℓ (mem_filter.mp hp).2.2.2).symm)
  · rintro ⟨u₁, v₁, w₁⟩ hp₁ ⟨u₂, v₂, w₂⟩ hp₂ htri
    obtain ⟨huv₁, hvw₁, _⟩ := (mem_filter.mp hp₁).2
    obtain ⟨huv₂, hvw₂, _⟩ := (mem_filter.mp hp₂).2
    exact congrArg Subtype.val
      (Set.powersetCard.ofLtTriple.injective
        (a₁ := ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩) (a₂ := ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩)
        (Subtype.ext <| (Set.powersetCard.val_ofLtTriple ⟨(u₁, v₁, w₁), huv₁, hvw₁⟩).trans
          (htri.trans (Set.powersetCard.val_ofLtTriple ⟨(u₂, v₂, w₂), huv₂, hvw₂⟩).symm)))
  · intro t ht
    obtain ⟨u, v, w, huv, hvw, hset⟩ := X.exists_increasing_of_mem_triangles ht
    exact ⟨(u, v, w), mem_filter.mpr ⟨mem_univ _, huv, hvw, hset ▸ ht⟩, hset⟩

/-! ### Independence of the vertex linear order -/

/-- `cost` does not depend on the `LinearOrder` chosen on `V`, for every group norm `ℓ`. -/
theorem cost_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (ℓ : GroupNorm G)
    (α : Cochain X G) (β : V → G) :
    @cost V G _ l₁ _ X ℓ α β = @cost V G _ l₂ _ X ℓ α β :=
  (@cost_eq_sum_edges V G _ X _ l₁ ℓ α β).trans (@cost_eq_sum_edges V G _ X _ l₂ ℓ α β).symm

/-- `gaugeDist` does not depend on the `LinearOrder` chosen on `V`, for every group norm `ℓ`. -/
theorem gaugeDist_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) (ℓ : GroupNorm G)
    (α : Cochain X G) :
    @gaugeDist V G _ l₁ _ X ℓ α = @gaugeDist V G _ l₂ _ X ℓ α := by
  simp only [@gaugeDist_def V G _ l₁ _ X ℓ α, @gaugeDist_def V G _ l₂ _ X ℓ α,
    cost_congr_linearOrder l₁ l₂ ℓ α]

/-- Under a conjugation-invariant norm, `defect` does not depend on the `LinearOrder` chosen on
`V`. -/
theorem defect_congr_linearOrder [Fintype V] (l₁ l₂ : LinearOrder V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    @defect V G _ l₁ _ X ℓ α = @defect V G _ l₂ _ X ℓ α :=
  (@defect_eq_sum_triangles V G _ X _ l₁ ℓ hℓ α).trans
    (@defect_eq_sum_triangles V G _ X _ l₂ ℓ hℓ α).symm

end Unoriented

/-! ### Relabelling along vertex bijections -/

section Relabel

variable {V W G : Type*} [Group G] {X : TwoComplex V}

/-- Transport a cochain along a bijection `e : V ≃ W` to a cochain on `X.relabel e`. -/
def relabel (α : Cochain X G) (e : V ≃ W) : Cochain (X.relabel e) G where
  toFun u v := α (e.symm u) (e.symm v)
  inv_symm u v _ := α.apply_swap (e.symm u) (e.symm v)
  apply_eq_one_of_not_adj' u v huv := α.apply_eq_one_of_not_adj (mt (X.adj_relabel e u v).mpr huv)

@[simp, grind =]
theorem relabel_apply (α : Cochain X G) (e : V ≃ W) (u v : W) :
    α.relabel e u v = α (e.symm u) (e.symm v) := (rfl)

@[simp]
theorem relabel_one (e : V ≃ W) : (1 : Cochain X G).relabel e = 1 := by ext u v _; rfl

@[simp]
theorem relabel_smul (β : V → G) (α : Cochain X G) (e : V ≃ W) :
    (β • α).relabel e = (β ∘ e.symm) • α.relabel e := by
  ext u v huv
  simp [smul_apply_of_adj _ _ huv, smul_apply_of_adj _ _ ((X.adj_relabel e u v).mp huv)]

/-- Bijection between cochains on `X` and cochains on `X.relabel e` induced by `e : V ≃ W`. -/
def relabelEquiv (X : TwoComplex V) (e : V ≃ W) : Cochain X G ≃ Cochain (X.relabel e) G where
  toFun α := α.relabel e
  invFun α :=
    { toFun u v := α (e u) (e v)
      inv_symm u v _ := α.apply_swap (e u) (e v)
      apply_eq_one_of_not_adj' u v huv :=
        α.apply_eq_one_of_not_adj (mt (X.adj_relabel_apply e u v).mp huv) }
  left_inv α := by ext u v _; simp
  right_inv α := by ext u v _; simp

@[simp]
theorem relabelEquiv_apply (X : TwoComplex V) (e : V ≃ W) (α : Cochain X G) :
    relabelEquiv X e α = α.relabel e := (rfl)

@[simp, grind =]
theorem relabelEquiv_symm_apply (X : TwoComplex V) (e : V ≃ W)
    (α : Cochain (X.relabel e) G) (u v : V) :
    (relabelEquiv X e).symm α u v = α (e u) (e v) := (rfl)

@[simp]
theorem holonomy_relabel (α : Cochain X G) (e : V ≃ W) (u v w : W) :
    (α.relabel e).holonomy u v w = α.holonomy (e.symm u) (e.symm v) (e.symm w) := by
  simp [holonomy_def]

@[simp]
theorem edgeCost_relabel (ℓ : GroupNorm G) (α : Cochain X G) (γ : W → G) (e : V ≃ W)
    (s : Finset W) :
    (α.relabel e).edgeCost ℓ γ s = α.edgeCost ℓ (γ ∘ e) (s.map e.symm.toEmbedding) := by
  by_cases hs : s ∈ (X.relabel e).edges
  · obtain ⟨u, v, huv, hu, hv⟩ := (X.relabel e).exists_vertices_of_mem_edges hs
    rw [(α.relabel e).edgeCost_of_mem_edges ℓ γ hs huv hu hv,
      α.edgeCost_of_mem_edges ℓ (γ ∘ e) ((X.mem_edges_relabel e s).mp hs)
        (e.symm.injective.ne huv) (mem_map_of_mem _ hu) (mem_map_of_mem _ hv)]
    simp
  · rw [edgeCost_of_notMem_edges _ _ _ hs,
      edgeCost_of_notMem_edges _ _ _ (mt (X.mem_edges_relabel e s).mpr hs)]

theorem edgeCost_relabel_map (ℓ : GroupNorm G) (α : Cochain X G) (γ : W → G) (e : V ≃ W)
    (s : Finset V) :
    (α.relabel e).edgeCost ℓ γ (s.map e.toEmbedding) = α.edgeCost ℓ (γ ∘ e) s := by
  rw [α.edgeCost_relabel ℓ γ e]
  congr 1; ext; simp

/-- Relabelling a cochain along `e : V ≃ W` pulls the gauge back along `e` in `cost`. -/
@[simp]
theorem cost_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain X G) (γ : W → G) (e : V ≃ W) :
    (α.relabel e).cost ℓ γ = α.cost ℓ (γ ∘ e) := by
  rw [cost_eq_sum_edges, cost_eq_sum_edges, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCost_relabel_map ℓ γ e s

/-- Relabelling a cochain along `e : V ≃ W` preserves `gaugeDist` for every group norm `ℓ`. -/
@[simp]
theorem gaugeDist_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).gaugeDist ℓ = α.gaugeDist ℓ := by
  rw [gaugeDist_def, gaugeDist_def]
  exact (Equiv.arrowCongr e.symm (Equiv.refl G)).iInf_congr fun γ => (α.cost_relabel ℓ γ e).symm

theorem triangleDefect_relabel {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (e : V ≃ W) (t : Finset W) :
    (α.relabel e).triangleDefect ℓ t = α.triangleDefect ℓ (t.map e.symm.toEmbedding) := by
  by_cases ht : t ∈ (X.relabel e).triangles
  · obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw⟩ :=
      (X.relabel e).exists_vertices_of_mem_triangles ht
    rw [(α.relabel e).triangleDefect_of_mem_triangles hℓ ht hu hv hw huv huw hvw,
      α.triangleDefect_of_mem_triangles hℓ ((X.mem_triangles_relabel e t).mp ht)
        (mem_map_of_mem _ hu) (mem_map_of_mem _ hv) (mem_map_of_mem _ hw)
        (e.symm.injective.ne huv) (e.symm.injective.ne huw) (e.symm.injective.ne hvw)]
    simp
  · rw [triangleDefect_of_notMem_triangles _ _ ht,
      triangleDefect_of_notMem_triangles _ _ (mt (X.mem_triangles_relabel e t).mpr ht)]

theorem triangleDefect_relabel_map {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (e : V ≃ W) (t : Finset V) :
    (α.relabel e).triangleDefect ℓ (t.map e.toEmbedding) = α.triangleDefect ℓ t := by
  rw [α.triangleDefect_relabel hℓ e]
  congr 1; ext; simp

/-- Under a conjugation-invariant norm, relabelling a cochain along `e : V ≃ W` preserves
`defect`. -/
theorem defect_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).defect ℓ = α.defect ℓ := by
  rw [defect_eq_sum_triangles hℓ, defect_eq_sum_triangles hℓ, X.sum_triangles_relabel e]
  exact sum_congr rfl fun t _ => α.triangleDefect_relabel_map hℓ e t

@[simp]
theorem isCoboundary_relabel (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).IsCoboundary ↔ α.IsCoboundary := by
  simp only [isCoboundary_def]
  exact ⟨fun ⟨β, hβ⟩ => ⟨β ∘ e, fun u v huv => by
      simpa using hβ (e u) (e v) ((X.adj_relabel_apply e u v).mpr huv)⟩,
    fun ⟨β, hβ⟩ => ⟨β ∘ e.symm, fun u v huv =>
      hβ (e.symm u) (e.symm v) ((X.adj_relabel e u v).mp huv)⟩⟩

/-- Transport a cochain on `complete V` along `e : V ≃ W` directly to `complete W`, avoiding casts
along `relabel_complete`. -/
def relabelComplete [Fintype V] [Fintype W] (α : Cochain (complete V) G) (e : V ≃ W) :
    Cochain (complete W) G where
  toFun u v := α (e.symm u) (e.symm v)
  inv_symm u v _ := α.apply_swap (e.symm u) (e.symm v)
  apply_eq_one_of_not_adj' u v huv := by
    obtain rfl : u = v := not_ne_iff.mp (mt (adj_complete u v).mpr huv); simp

@[simp, grind =]
theorem relabelComplete_apply [Fintype V] [Fintype W] (α : Cochain (complete V) G) (e : V ≃ W)
    (u v : W) : α.relabelComplete e u v = α (e.symm u) (e.symm v) := (rfl)

@[simp]
theorem relabelComplete_one [Fintype V] [Fintype W] (e : V ≃ W) :
    (1 : Cochain (complete V) G).relabelComplete e = 1 := by ext u v _; rfl

@[simp]
theorem relabelComplete_smul [Fintype V] [Fintype W] (β : V → G)
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (β • α).relabelComplete e = (β ∘ e.symm) • α.relabelComplete e := by ext u v _; simp

@[simp]
theorem holonomy_relabelComplete [Fintype V] [Fintype W] (α : Cochain (complete V) G) (e : V ≃ W)
    (u v w : W) :
    (α.relabelComplete e).holonomy u v w = α.holonomy (e.symm u) (e.symm v) (e.symm w) := by
  simp [holonomy_def]

@[simp]
theorem relabelComplete_refl [Fintype V] (α : Cochain (complete V) G) :
    α.relabelComplete (Equiv.refl V) = α := by ext u v _; rfl

@[simp]
theorem relabelComplete_relabelComplete {U : Type*} [Fintype V] [Fintype W] [Fintype U]
    (α : Cochain (complete V) G) (e : V ≃ W) (f : W ≃ U) :
    (α.relabelComplete e).relabelComplete f = α.relabelComplete (e.trans f) := by ext u v _; rfl

/-- Bijection between cochains on `complete V` and `complete W` induced by `e : V ≃ W`. -/
def relabelCompleteEquiv [Fintype V] [Fintype W] (e : V ≃ W) :
    Cochain (complete V) G ≃ Cochain (complete W) G where
  toFun α := α.relabelComplete e
  invFun α := α.relabelComplete e.symm
  left_inv α := by simp
  right_inv α := by simp

@[simp]
theorem relabelCompleteEquiv_apply [Fintype V] [Fintype W] (e : V ≃ W)
    (α : Cochain (complete V) G) : relabelCompleteEquiv e α = α.relabelComplete e := (rfl)

@[simp]
theorem relabelCompleteEquiv_symm_apply [Fintype V] [Fintype W] (e : V ≃ W)
    (α : Cochain (complete W) G) :
    (relabelCompleteEquiv e).symm α = α.relabelComplete e.symm := (rfl)

private theorem congr_complex {γ : Sort*} (F : ∀ X : TwoComplex W, Cochain X G → γ)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂) {α₁ : Cochain X₁ G} {α₂ : Cochain X₂ G}
    (hα : ∀ u v, α₁ u v = α₂ u v) : F X₁ α₁ = F X₂ α₂ := by
  subst hX; congr 1; ext u v _; exact hα u v

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` pulls the gauge back along `e` in
`cost`. -/
@[simp]
theorem cost_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (complete V) G) (γ : W → G) (e : V ≃ W) :
    (α.relabelComplete e).cost ℓ γ = α.cost ℓ (γ ∘ e) :=
  (congr_complex (fun _ δ => δ.cost ℓ γ) (relabel_complete e).symm
    fun _ _ => rfl).trans (α.cost_relabel ℓ γ e)

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDist`. -/
@[simp]
theorem gaugeDist_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDist ℓ = α.gaugeDist ℓ :=
  (congr_complex (fun _ γ => γ.gaugeDist ℓ) (relabel_complete e).symm
    fun _ _ => rfl).trans (α.gaugeDist_relabel ℓ e)

/-- Under a conjugation-invariant norm, relabelling a cochain on `complete V` along `e : V ≃ W`
preserves `defect`. -/
theorem defect_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).defect ℓ = α.defect ℓ :=
  (congr_complex (fun _ γ => γ.defect ℓ) (relabel_complete e).symm
    fun _ _ => rfl).trans (α.defect_relabel hℓ e)

@[simp]
theorem isCoboundary_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).IsCoboundary ↔ α.IsCoboundary :=
  (congr_complex (fun _ γ => γ.IsCoboundary) (relabel_complete e).symm
    fun _ _ => rfl).to_iff.trans (α.isCoboundary_relabel e)

end Relabel

/-! ### Change of coefficients and positive norm scaling -/

section ChangeOfCoefficients

variable {V G H K : Type*} [Group G] [Group H] [Group K] {X : TwoComplex V}

/-- Push a cochain forward along a group homomorphism `φ : G →* H`. -/
def map (φ : G →* H) (α : Cochain X G) : Cochain X H where
  toFun u v := φ (α u v)
  inv_symm u v _ := by rw [α.apply_swap u v, map_inv]
  apply_eq_one_of_not_adj' u v huv := by rw [α.apply_eq_one_of_not_adj huv, map_one]

@[simp, grind =]
theorem map_apply (φ : G →* H) (α : Cochain X G) (u v : V) : α.map φ u v = φ (α u v) := (rfl)

@[simp]
theorem map_id (α : Cochain X G) : α.map (MonoidHom.id G) = α := by ext u v _; rfl

@[simp]
theorem map_map (ψ : H →* K) (φ : G →* H) (α : Cochain X G) :
    (α.map φ).map ψ = α.map (ψ.comp φ) := by ext u v _; rfl

@[simp]
theorem map_one (φ : G →* H) : (1 : Cochain X G).map φ = 1 := by ext u v _; simp

@[simp]
theorem map_smul (φ : G →* H) (β : V → G) (α : Cochain X G) :
    (β • α).map φ = (φ ∘ β) • α.map φ := by ext u v huv; simp [huv]

theorem map_relabel {W : Type*} (φ : G →* H) (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).map φ = (α.map φ).relabel e := by ext u v _; rfl

theorem map_relabelComplete {W : Type*} [Fintype V] [Fintype W] (φ : G →* H)
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).map φ = (α.map φ).relabelComplete e := by ext u v _; rfl

@[simp]
theorem holonomy_map (φ : G →* H) (α : Cochain X G) (u v w : V) :
    (α.map φ).holonomy u v w = φ (α.holonomy u v w) := by simp [holonomy_def]

theorem IsCoboundary.map {α : Cochain X G} (hα : α.IsCoboundary) (φ : G →* H) :
    (α.map φ).IsCoboundary := by
  rw [isCoboundary_def] at hα ⊢; obtain ⟨β, hβ⟩ := hα
  exact ⟨φ ∘ β, fun u v huv => by simp [hβ u v huv]⟩

section Metric

variable [Fintype V] [LinearOrder V]

/-- Pushing a cochain forward along a norm-nonincreasing homomorphism does not increase `defect`. -/
theorem defect_map_le {φ : G →* H} {ℓ_G : GroupNorm G} {ℓ_H : GroupNorm H}
    (hφ : ∀ g, ℓ_H (φ g) ≤ ℓ_G g) (α : Cochain X G) :
    (α.map φ).defect ℓ_H ≤ α.defect ℓ_G := by
  rw [defect_def, defect_def]
  exact sum_le_sum fun p _ => by simpa using hφ (α.holonomy p.1 p.2.1 p.2.2)

/-- Pushing a cochain and a gauge forward along a norm-nonincreasing homomorphism does not increase
`cost`. -/
theorem cost_map_le {φ : G →* H} {ℓ_G : GroupNorm G} {ℓ_H : GroupNorm H}
    (hφ : ∀ g, ℓ_H (φ g) ≤ ℓ_G g) (α : Cochain X G) (β : V → G) :
    (α.map φ).cost ℓ_H (φ ∘ β) ≤ α.cost ℓ_G β := by
  rw [cost_def, cost_def]
  exact sum_le_sum fun p _ => by simpa [map_mul, map_inv] using hφ ((β p.1)⁻¹ * α p.1 p.2 * β p.2)

/-- Pushing a cochain forward along a norm-nonincreasing homomorphism does not increase
`gaugeDist`. -/
theorem gaugeDist_map_le {φ : G →* H} {ℓ_G : GroupNorm G} {ℓ_H : GroupNorm H}
    (hφ : ∀ g, ℓ_H (φ g) ≤ ℓ_G g) (α : Cochain X G) :
    (α.map φ).gaugeDist ℓ_H ≤ α.gaugeDist ℓ_G :=
  (α.le_gaugeDist_iff ℓ_G).mpr fun β =>
    ((α.map φ).gaugeDist_le_cost ℓ_H (φ ∘ β)).trans (α.cost_map_le hφ β)

/-- Along a norm-preserving homomorphism, `defect` is unchanged. -/
theorem defect_map_eq {φ : G →* H} {ℓ_G : GroupNorm G} {ℓ_H : GroupNorm H}
    (hφ : ∀ g, ℓ_H (φ g) = ℓ_G g) (α : Cochain X G) :
    (α.map φ).defect ℓ_H = α.defect ℓ_G := by
  rw [defect_def, defect_def]; exact sum_congr rfl fun _ _ => by simp [hφ]

/-- Along a norm-preserving homomorphism, `cost` is unchanged. -/
theorem cost_map_eq {φ : G →* H} {ℓ_G : GroupNorm G} {ℓ_H : GroupNorm H}
    (hφ : ∀ g, ℓ_H (φ g) = ℓ_G g) (α : Cochain X G) (β : V → G) :
    (α.map φ).cost ℓ_H (φ ∘ β) = α.cost ℓ_G β := by
  rw [cost_def, cost_def]; refine sum_congr rfl fun _ _ => ?_
  rw [Function.comp_apply, Function.comp_apply, map_apply, ← map_inv, ← map_mul, ← map_mul, hφ]

/-- Embedding an `L`-valued cochain into `G` along a subgroup `L ≤ G` preserves `defect` relative
to the restricted norm `ℓ.comp L.subtype_injective`. -/
@[simp]
theorem defect_map_subtype (ℓ : GroupNorm G) (L : Subgroup G) (α : Cochain X L) :
    (α.map L.subtype).defect ℓ = α.defect (ℓ.comp L.subtype_injective) :=
  α.defect_map_eq fun x => (ℓ.comp_apply L.subtype_injective x).symm

/-- Embedding an `L`-valued cochain and gauge into `G` along a subgroup `L ≤ G` preserves `cost`
relative to the restricted norm `ℓ.comp L.subtype_injective`. -/
@[simp]
theorem cost_map_subtype (ℓ : GroupNorm G) (L : Subgroup G) (α : Cochain X L) (β : V → L) :
    (α.map L.subtype).cost ℓ (Subtype.val ∘ β) = α.cost (ℓ.comp L.subtype_injective) β :=
  α.cost_map_eq (fun x => (ℓ.comp_apply L.subtype_injective x).symm) β

/-- Embedding an `L`-valued cochain into `G` along a subgroup `L ≤ G` gives a `gaugeDist` in `G`
at most its `gaugeDist` in `L`. -/
theorem gaugeDist_map_subtype_le (ℓ : GroupNorm G) (L : Subgroup G) (α : Cochain X L) :
    (α.map L.subtype).gaugeDist ℓ ≤ α.gaugeDist (ℓ.comp L.subtype_injective) :=
  α.gaugeDist_map_le fun x => (ℓ.comp_apply L.subtype_injective x).symm.le

/-- Scaling a group norm by a positive real `r` scales `defect` by `r`. -/
@[simp]
theorem defect_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) :
    α.defect (ℓ.smulOfPos hr) = r * α.defect ℓ := by simp [defect_def, mul_sum]

/-- Scaling a group norm by a positive real `r` scales `cost` by `r`. -/
@[simp]
theorem cost_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) (β : V → G) :
    α.cost (ℓ.smulOfPos hr) β = r * α.cost ℓ β := by simp [cost_def, mul_sum]

/-- Scaling a group norm by a positive real `r` scales `gaugeDist` by `r`. -/
@[simp]
theorem gaugeDist_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) :
    α.gaugeDist (ℓ.smulOfPos hr) = r * α.gaugeDist ℓ := by
  simp_rw [gaugeDist_def, cost_smulOfPos, ← Real.mul_iInf_of_nonneg hr.le]

end Metric

end ChangeOfCoefficients

end Cochain

/-! ### Positive-gauge-distance witnesses under conjugation-invariant norms -/

section Existence

/-- Whenever `X` has at least one filled triangle, `G` is nontrivial, and `ℓ` is conjugation
invariant, some 1-cochain on `X` has strictly positive gauge distance (without requiring `G` to be
finite). -/
theorem exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant {V G : Type*}
    [Fintype V] [LinearOrder V] [Group G] [Nontrivial G] {X : TwoComplex V}
    (htri : X.triangles.Nonempty) {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    ∃ α : Cochain X G, 0 < α.gaugeDist ℓ := by
  obtain ⟨α, u, v, w, huv, hvw, hwu, hhol⟩ :=
    exists_holonomy_ne_one_of_triangles_nonempty (G := G) htri
  exact ⟨α, Cochain.gaugeDist_pos_of_holonomy_ne_one_of_isConjInvariant hℓ huv hvw hwu hhol⟩

/-- On `complete V` with `3 ≤ Fintype.card V`, nontrivial `G`, and conjugation-invariant `ℓ`,
there exists a cochain at strictly positive gauge distance (without requiring `G` to be finite). -/
theorem exists_gaugeDist_pos_complete_of_isConjInvariant {V G : Type*} [Fintype V] [LinearOrder V]
    [Group G] [Nontrivial G] (hV : 3 ≤ Fintype.card V) {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) :
    ∃ α : Cochain (complete V) G, 0 < α.gaugeDist ℓ :=
  exists_gaugeDist_pos_of_triangles_nonempty_of_isConjInvariant
    (card_pos.mp (card_triangles_complete (V := V) ▸ Nat.choose_pos hV)) hℓ

end Existence

end TauCeti

end

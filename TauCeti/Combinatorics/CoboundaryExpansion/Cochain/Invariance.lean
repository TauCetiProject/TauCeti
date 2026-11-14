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

/-!
# Orientation independence, relabelling, and change of coefficients for 1-cochains

Reversing an oriented edge inverts its gauge-transformed value `(β u)⁻¹ * α u v * β v`, so every
group norm assigns the same weight to both orientations of an edge. Consequently `Cochain.cost` and
`Cochain.gaugeDist` equal unoriented sums over `X.edges`, do not depend on the `LinearOrder` chosen
on `V`, and are invariant under relabelling vertices along any bijection `V ≃ W`.

When the group norm `ℓ` is conjugation invariant, cyclically rotating or reversing the vertices of a
filled triangle also preserves the norm of `Cochain.holonomy`. Thus `Cochain.defect` equals an
unoriented sum over `X.triangles`, is independent of the vertex `LinearOrder`, and is preserved by
vertex relabellings.

Pushing a cochain forward along a norm-nonincreasing homomorphism `φ : G →* H` (`Cochain.map φ`)
does not increase `defect` or `gaugeDist`. Specializing `φ` to `K.subtype` for a subgroup `K ≤ G`
shows that embedding `K`-valued cochains into `G` preserves `defect` and can only decrease
`gaugeDist`.

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

/-- Reversing an oriented edge inverts its gauge-transformed value, so any group norm gives the
same weight to both orientations. -/
theorem norm_edge_term_swap (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) {u v : V}
    (h : X.Adj u v) :
    ℓ ((β v)⁻¹ * α v u * β u) = ℓ ((β u)⁻¹ * α u v * β v) := by
  have hinv : ((β u)⁻¹ * α u v * β v)⁻¹ = (β v)⁻¹ * α v u * β u := by
    rw [α.map_swap h]
    group
  rw [← hinv, map_inv_eq_map]

/-- Under a conjugation-invariant norm, cyclically rotating a triple preserves the norm of its
holonomy. -/
theorem norm_holonomy_rotate {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (u v w : V) :
    ℓ (α.holonomy v w u) = ℓ (α.holonomy u v w) := by
  simpa only [holonomy_def, mul_assoc, GroupNorm.toGroupSeminorm_eq_coe] using
    hℓ.map_mul_comm (α v w * α w u) (α u v)

/-- Under a conjugation-invariant norm, exchanging the first two vertices of three mutually
adjacent vertices preserves the norm of the holonomy. -/
theorem norm_holonomy_swap {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) {u v w : V} (huv : X.Adj u v) (hvw : X.Adj v w) (hwu : X.Adj w u) :
    ℓ (α.holonomy v u w) = ℓ (α.holonomy u v w) := by
  have hinv : (α.holonomy v u w)⁻¹ = α.holonomy v w u := by
    rw [holonomy_def, holonomy_def, α.map_swap huv.symm, α.map_swap hwu.symm, α.map_swap hvw]
    group
  rw [← map_inv_eq_map ℓ (α.holonomy v u w), hinv, α.norm_holonomy_rotate hℓ u v w]

/-- Under a conjugation-invariant norm, all six vertex orderings of a filled triangle have the same
holonomy norm. -/
theorem norm_holonomy_eq_of_mem_triangle {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) {t : Finset V}
    (ht : t ∈ X.triangles) {u v w u' v' w' : V}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu' : u' ∈ t) (hv' : v' ∈ t) (hw' : w' ∈ t)
    (hu'v' : u' ≠ v') (hu'w' : u' ≠ w') (hv'w' : v' ≠ w') :
    ℓ (α.holonomy u' v' w') = ℓ (α.holonomy u v w) := by
  classical
  have hcard3 : ({u, v, w} : Finset V).card = 3 :=
    card_eq_three.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩
  have ht_eq : t = {u, v, w} :=
    (eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv, hw])
      (by rw [X.triangle_card t ht, hcard3])).symm
  have hadj_uv : X.Adj u v := X.adj_of_mem_triangle ht hu hv huv
  have hadj_vw : X.Adj v w := X.adj_of_mem_triangle ht hv hw hvw
  have hadj_wu : X.Adj w u := X.adj_of_mem_triangle ht hw hu huw.symm
  rw [ht_eq] at hu' hv' hw'
  simp only [mem_insert, mem_singleton] at hu' hv' hw'
  rcases hu' with h₁ | h₁ | h₁ <;>
    rcases hv' with h₂ | h₂ | h₂ <;>
    rcases hw' with h₃ | h₃ | h₃
  all_goals rw [h₁, h₂] at hu'v'; rw [h₁, h₃] at hu'w'; rw [h₂, h₃] at hv'w'
  all_goals try exact (hu'v' rfl).elim
  all_goals try exact (hu'w' rfl).elim
  all_goals try exact (hv'w' rfl).elim
  all_goals rw [h₁, h₂, h₃]
  · rw [α.norm_holonomy_rotate hℓ v u w, α.norm_holonomy_swap hℓ hadj_uv hadj_vw hadj_wu]
  · exact α.norm_holonomy_swap hℓ hadj_uv hadj_vw hadj_wu
  · exact α.norm_holonomy_rotate hℓ u v w
  · rw [α.norm_holonomy_rotate hℓ v w u, α.norm_holonomy_rotate hℓ u v w]
  · rw [α.norm_holonomy_swap hℓ hadj_vw hadj_wu hadj_uv, α.norm_holonomy_rotate hℓ u v w]

private theorem exists_vertices_of_mem_edges {e : Finset V} (he : e ∈ X.edges) :
    ∃ u v, u ≠ v ∧ u ∈ e ∧ v ∈ e := by
  classical
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp (X.edge_card e he)
  exact ⟨u, v, huv, by simp, by simp⟩

private theorem exists_vertices_of_mem_triangles {t : Finset V} (ht : t ∈ X.triangles) :
    ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ u ∈ t ∧ v ∈ t ∧ w ∈ t := by
  classical
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := card_eq_three.mp (X.triangle_card t ht)
  exact ⟨u, v, w, huv, huw, hvw, by simp, by simp, by simp⟩

/-- The gauge cost contribution of an unoriented edge `e`, or `0` if `e ∉ X.edges`. -/
noncomputable def edgeCost (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (e : Finset V) : ℝ := by
  classical
  exact if he : e ∈ X.edges then
    ℓ ((β (exists_vertices_of_mem_edges he).choose)⁻¹ *
      α (exists_vertices_of_mem_edges he).choose
        (exists_vertices_of_mem_edges he).choose_spec.choose *
      β (exists_vertices_of_mem_edges he).choose_spec.choose)
  else 0

/-- Evaluating `edgeCost` on any edge `e ∈ X.edges` via its two distinct endpoints. -/
theorem edgeCost_of_mem_edges (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {e : Finset V} (he : e ∈ X.edges) {u v : V} (huv : u ≠ v) (hu : u ∈ e) (hv : v ∈ e) :
    α.edgeCost ℓ β e = ℓ ((β u)⁻¹ * α u v * β v) := by
  classical
  simp only [edgeCost, he, ↓reduceDIte]
  obtain ⟨hu'v', hu', hv'⟩ := (exists_vertices_of_mem_edges he).choose_spec.choose_spec
  have he_eq : e = {u, v} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · simp [insert_subset_iff, hu, hv]
    · rw [X.edge_card e he, card_pair huv]
  have hu'mem : (exists_vertices_of_mem_edges he).choose ∈ ({u, v} : Finset V) := he_eq ▸ hu'
  have hv'mem : (exists_vertices_of_mem_edges he).choose_spec.choose ∈ ({u, v} : Finset V) :=
    he_eq ▸ hv'
  simp only [mem_insert, mem_singleton] at hu'mem hv'mem
  rcases hu'mem with h1 | h1 <;> rcases hv'mem with h2 | h2
  · exact (hu'v' (h1.trans h2.symm)).elim
  · rw [h2, h1]
  · rw [h2, h1]
    exact α.norm_edge_term_swap ℓ β ((X.adj_iff u v).mpr ⟨huv, e, he, hu, hv⟩)
  · exact (hu'v' (h1.trans h2.symm)).elim

@[simp]
theorem edgeCost_of_notMem_edges (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G)
    {e : Finset V} (he : e ∉ X.edges) : α.edgeCost ℓ β e = 0 := by
  classical
  simp [edgeCost, he]

/-- The holonomy defect of an unoriented triangle `t`, or `0` if `t ∉ X.triangles`. Well-defined
independently of orientation whenever `ℓ` is conjugation invariant. -/
noncomputable def triangleDefect (ℓ : GroupNorm G) (α : Cochain X G) (t : Finset V) : ℝ := by
  classical
  exact if ht : t ∈ X.triangles then
    ℓ (α.holonomy
      (exists_vertices_of_mem_triangles ht).choose
      (exists_vertices_of_mem_triangles ht).choose_spec.choose
      (exists_vertices_of_mem_triangles ht).choose_spec.choose_spec.choose)
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
    (exists_vertices_of_mem_triangles ht).choose_spec.choose_spec.choose_spec
  exact α.norm_holonomy_eq_of_mem_triangle hℓ ht hu hv hw huv huw hvw
    hu' hv' hw' hu'v' hu'w' hv'w'

@[simp]
theorem triangleDefect_of_notMem_triangles (ℓ : GroupNorm G) (α : Cochain X G)
    {t : Finset V} (ht : t ∉ X.triangles) : α.triangleDefect ℓ t = 0 := by
  classical
  simp [triangleDefect, ht]

/-- `cost` equals the sum of `edgeCost` over the unoriented edges `X.edges`. -/
theorem cost_eq_sum_edges [Fintype V] [LinearOrder V] (ℓ : GroupNorm G) (α : Cochain X G)
    (β : V → G) :
    α.cost ℓ β = ∑ e ∈ X.edges, α.edgeCost ℓ β e := by
  rw [cost_def]
  refine sum_bij (fun p _ => ({p.1, p.2} : Finset V)) ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_filter.mp hp).2.2
  · rintro ⟨u₁, v₁⟩ hp₁ ⟨u₂, v₂⟩ hp₂ hpair
    have hlt₁ : u₁ < v₁ := (mem_filter.mp hp₁).2.1
    have hlt₂ : u₂ < v₂ := (mem_filter.mp hp₂).2.1
    have hu₁ : u₁ ∈ ({u₂, v₂} : Finset V) := hpair ▸ by simp
    have hv₁ : v₁ ∈ ({u₂, v₂} : Finset V) := hpair ▸ by simp
    simp only [mem_insert, mem_singleton] at hu₁ hv₁
    rcases hu₁ with rfl | rfl <;> rcases hv₁ with rfl | rfl
    · exact (hlt₁.ne rfl).elim
    · rfl
    · exact (lt_asymm hlt₁ hlt₂).elim
    · exact (hlt₁.ne rfl).elim
  · intro e he
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (X.edge_card e he)
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact ⟨(a, b), mem_filter.mpr ⟨mem_univ _, hlt, he⟩, rfl⟩
    · refine ⟨(b, a), mem_filter.mpr ⟨mem_univ _, hgt, ?_⟩, pair_comm b a⟩
      rwa [pair_comm]
  · intro p hp
    obtain ⟨hlt, he⟩ := (mem_filter.mp hp).2
    exact (α.edgeCost_of_mem_edges ℓ β he hlt.ne (by simp) (by simp)).symm

private theorem exists_increasing_of_mem_triangles [LinearOrder V] {t : Finset V}
    (ht : t ∈ X.triangles) : ∃ u v w, u < v ∧ v < w ∧ ({u, v, w} : Finset V) = t := by
  have ht3 : t.card = 3 := X.triangle_card t ht
  have hne : t.Nonempty := card_pos.mp (by omega)
  let u := t.min' hne
  have hu : u ∈ t := min'_mem t hne
  let t' := t.erase u
  have ht'2 : t'.card = 2 := by rw [card_erase_of_mem hu, ht3]
  have hne' : t'.Nonempty := card_pos.mp (by omega)
  let v := t'.min' hne'
  let w := t'.max' hne'
  have hv' : v ∈ t' := min'_mem t' hne'
  have hw' : w ∈ t' := max'_mem t' hne'
  have hv : v ∈ t := mem_of_mem_erase hv'
  have hw : w ∈ t := mem_of_mem_erase hw'
  have huv : u < v := lt_of_le_of_ne (min'_le t v hv) (ne_of_mem_erase hv').symm
  have hvw : v < w := by
    refine lt_of_le_of_ne (min'_le t' w hw') fun hvw_eq => ?_
    have hsub : t' ⊆ {v} := fun x hx =>
      mem_singleton.mpr (le_antisymm (hvw_eq ▸ le_max' t' x hx) (min'_le t' x hx))
    have hle := card_le_card hsub
    simp [ht'2] at hle
  have hcard3 : ({u, v, w} : Finset V).card = 3 :=
    card_eq_three.mpr ⟨u, v, w, huv.ne, (huv.trans hvw).ne, hvw.ne, rfl⟩
  have hset : ({u, v, w} : Finset V) = t :=
    eq_of_subset_of_card_le (by simp [insert_subset_iff, hu, hv, hw]) (by rw [ht3, hcard3])
  exact ⟨u, v, w, huv, hvw, hset⟩

/-- Under a conjugation-invariant norm, `defect` equals the sum of `triangleDefect` over the
unoriented triangles `X.triangles`. -/
theorem defect_eq_sum_triangles [Fintype V] [LinearOrder V] {ℓ : GroupNorm G}
    (hℓ : ℓ.toGroupSeminorm.IsConjInvariant) (α : Cochain X G) :
    α.defect ℓ = ∑ t ∈ X.triangles, α.triangleDefect ℓ t := by
  rw [defect_def]
  refine sum_bij (fun p _ => ({p.1, p.2.1, p.2.2} : Finset V)) ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_filter.mp hp).2.2.2
  · rintro ⟨u₁, v₁, w₁⟩ hp₁ ⟨u₂, v₂, w₂⟩ hp₂ htri
    obtain ⟨huv₁, hvw₁, _⟩ := (mem_filter.mp hp₁).2
    obtain ⟨huv₂, hvw₂, _⟩ := (mem_filter.mp hp₂).2
    have hle₁ : ∀ x ∈ ({u₁, v₁, w₁} : Finset V), u₁ ≤ x := by
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨le_rfl, huv₁.le, (huv₁.trans hvw₁).le⟩
    have hle₂ : ∀ x ∈ ({u₂, v₂, w₂} : Finset V), u₂ ≤ x := by
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨le_rfl, huv₂.le, (huv₂.trans hvw₂).le⟩
    have hu : u₁ = u₂ := le_antisymm
      (hle₁ u₂ (htri ▸ by simp)) (hle₂ u₁ (htri.symm ▸ by simp))
    have hge₁ : ∀ x ∈ ({u₁, v₁, w₁} : Finset V), x ≤ w₁ := by
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨(huv₁.trans hvw₁).le, hvw₁.le, le_rfl⟩
    have hge₂ : ∀ x ∈ ({u₂, v₂, w₂} : Finset V), x ≤ w₂ := by
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨(huv₂.trans hvw₂).le, hvw₂.le, le_rfl⟩
    have hw : w₁ = w₂ := le_antisymm
      (hge₂ w₁ (htri ▸ by simp)) (hge₁ w₂ (htri.symm ▸ by simp))
    subst hu hw
    have hv₁_mem : v₁ ∈ ({u₁, v₂, w₁} : Finset V) := htri ▸ by simp
    simp only [mem_insert, mem_singleton] at hv₁_mem
    rcases hv₁_mem with h | h | h
    · exact (huv₁.ne h.symm).elim
    · subst h; rfl
    · exact (hvw₁.ne h).elim
  · intro t ht
    obtain ⟨u, v, w, huv, hvw, hset⟩ := exists_increasing_of_mem_triangles ht
    exact ⟨(u, v, w), mem_filter.mpr ⟨mem_univ _, huv, hvw, hset ▸ ht⟩, hset⟩
  · intro p hp
    obtain ⟨huv, hvw, ht⟩ := (mem_filter.mp hp).2
    exact (α.triangleDefect_of_mem_triangles hℓ ht (by simp) (by simp) (by simp)
      huv.ne (huv.trans hvw).ne hvw.ne).symm

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
  inv_symm u v huv := α.map_swap ((X.adj_relabel e u v).mp huv)
  apply_eq_one_of_not_adj u v huv := α.map_of_not_adj (mt (X.adj_relabel e u v).mpr huv)

@[simp]
theorem relabel_apply (α : Cochain X G) (e : V ≃ W) (u v : W) :
    α.relabel e u v = α (e.symm u) (e.symm v) := (rfl)

@[simp]
theorem relabel_one (e : V ≃ W) : (1 : Cochain X G).relabel e = 1 := by
  ext u v _
  rfl

/-- Bijection between cochains on `X` and cochains on `X.relabel e` induced by `e : V ≃ W`. -/
def relabelEquiv (X : TwoComplex V) (e : V ≃ W) : Cochain X G ≃ Cochain (X.relabel e) G where
  toFun α := α.relabel e
  invFun α :=
    { toFun u v := α (e u) (e v)
      inv_symm u v huv := α.map_swap ((X.map_adj_relabel e u v).mpr huv)
      apply_eq_one_of_not_adj u v huv := α.map_of_not_adj (mt (X.map_adj_relabel e u v).mp huv) }
  left_inv α := by ext u v _; simp
  right_inv α := by ext u v _; simp

@[simp]
theorem relabelEquiv_apply (X : TwoComplex V) (e : V ≃ W) (α : Cochain X G) :
    relabelEquiv X e α = α.relabel e := (rfl)

@[simp]
theorem holonomy_relabel (α : Cochain X G) (e : V ≃ W) (u v w : W) :
    (α.relabel e).holonomy u v w = α.holonomy (e.symm u) (e.symm v) (e.symm w) := by
  simp [holonomy_def]

theorem edgeCost_relabel_map (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (e : V ≃ W)
    (s : Finset V) :
    (α.relabel e).edgeCost ℓ (β ∘ e.symm) (s.map e.toEmbedding) = α.edgeCost ℓ β s := by
  by_cases hs : s ∈ X.edges
  · classical
    obtain ⟨u, v, huv, hu, hv⟩ := exists_vertices_of_mem_edges hs
    have hs' : s.map e.toEmbedding ∈ (X.relabel e).edges := (X.map_mem_edges_relabel e s).mpr hs
    rw [(α.relabel e).edgeCost_of_mem_edges ℓ (β ∘ e.symm) hs' (e.injective.ne huv)
      (mem_map_of_mem _ hu) (mem_map_of_mem _ hv),
      α.edgeCost_of_mem_edges ℓ β hs huv hu hv]
    simp
  · simp [hs]

/-- Relabelling a cochain and its gauge along `e : V ≃ W` preserves `cost`. -/
theorem cost_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain X G) (β : V → G) (e : V ≃ W) :
    (α.relabel e).cost ℓ (β ∘ e.symm) = α.cost ℓ β := by
  rw [cost_eq_sum_edges, cost_eq_sum_edges, X.sum_edges_relabel e]
  exact sum_congr rfl fun s _ => α.edgeCost_relabel_map ℓ β e s

/-- Relabelling a cochain along `e : V ≃ W` preserves `gaugeDist` for every group norm `ℓ`. -/
@[simp]
theorem gaugeDist_relabel [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain X G) (e : V ≃ W) :
    (α.relabel e).gaugeDist ℓ = α.gaugeDist ℓ := by
  rw [gaugeDist_def, gaugeDist_def]
  exact ((Equiv.arrowCongr e (Equiv.refl G)).iInf_congr fun β =>
    α.cost_relabel ℓ β e).symm

theorem triangleDefect_relabel_map {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain X G) (e : V ≃ W) (t : Finset V) :
    (α.relabel e).triangleDefect ℓ (t.map e.toEmbedding) = α.triangleDefect ℓ t := by
  by_cases ht : t ∈ X.triangles
  · obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw⟩ := exists_vertices_of_mem_triangles ht
    have ht' : t.map e.toEmbedding ∈ (X.relabel e).triangles :=
      (X.map_mem_triangles_relabel e t).mpr ht
    rw [(α.relabel e).triangleDefect_of_mem_triangles hℓ ht'
      (mem_map_of_mem _ hu) (mem_map_of_mem _ hv) (mem_map_of_mem _ hw)
      (e.injective.ne huv) (e.injective.ne huw) (e.injective.ne hvw),
      α.triangleDefect_of_mem_triangles hℓ ht hu hv hw huv huw hvw]
    simp
  · simp [ht]

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
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨β ∘ e, fun u v huv => ?_⟩
    simpa using hβ (e u) (e v) ((X.map_adj_relabel e u v).mpr huv)
  · rintro ⟨β, hβ⟩
    refine ⟨β ∘ e.symm, fun u v huv => ?_⟩
    exact hβ (e.symm u) (e.symm v) ((X.adj_relabel e u v).mp huv)

/-- Transport a cochain on `complete V` along `e : V ≃ W` directly to `complete W`, avoiding casts
along `relabel_complete`. -/
def relabelComplete [Fintype V] [Fintype W] (α : Cochain (complete V) G) (e : V ≃ W) :
    Cochain (complete W) G where
  toFun u v := α (e.symm u) (e.symm v)
  inv_symm u v huv :=
    α.map_swap ((adj_complete _ _).mpr (e.symm.injective.ne ((adj_complete u v).mp huv)))
  apply_eq_one_of_not_adj u v huv := by
    have heq : u = v := not_ne_iff.mp (mt (adj_complete u v).mpr huv)
    subst heq
    simp

@[simp]
theorem relabelComplete_apply [Fintype V] [Fintype W] (α : Cochain (complete V) G) (e : V ≃ W)
    (u v : W) : α.relabelComplete e u v = α (e.symm u) (e.symm v) := (rfl)

@[simp]
theorem relabelComplete_refl [Fintype V] (α : Cochain (complete V) G) :
    α.relabelComplete (Equiv.refl V) = α := by
  ext u v _
  rfl

@[simp]
theorem relabelComplete_symm_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).relabelComplete e.symm = α := by
  ext u v _
  simp

/-- Bijection between cochains on `complete V` and `complete W` induced by `e : V ≃ W`. -/
def relabelCompleteEquiv [Fintype V] [Fintype W] (e : V ≃ W) :
    Cochain (complete V) G ≃ Cochain (complete W) G where
  toFun α := α.relabelComplete e
  invFun α := α.relabelComplete e.symm
  left_inv α := α.relabelComplete_symm_relabelComplete e
  right_inv α := α.relabelComplete_symm_relabelComplete e.symm

private theorem cost_congr_complex [Fintype W] [LinearOrder W] (ℓ : GroupNorm G)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂) {α₁ : Cochain X₁ G} {α₂ : Cochain X₂ G}
    (hα : ∀ u v, α₁ u v = α₂ u v) (β : W → G) :
    α₁.cost ℓ β = α₂.cost ℓ β := by
  subst hX
  congr 1
  ext u v _
  exact hα u v

private theorem gaugeDist_congr_complex [Fintype W] [LinearOrder W] (ℓ : GroupNorm G)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂) {α₁ : Cochain X₁ G} {α₂ : Cochain X₂ G}
    (hα : ∀ u v, α₁ u v = α₂ u v) :
    α₁.gaugeDist ℓ = α₂.gaugeDist ℓ := by
  subst hX
  congr 1
  ext u v _
  exact hα u v

private theorem defect_congr_complex [Fintype W] [LinearOrder W] (ℓ : GroupNorm G)
    {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂) {α₁ : Cochain X₁ G} {α₂ : Cochain X₂ G}
    (hα : ∀ u v, α₁ u v = α₂ u v) :
    α₁.defect ℓ = α₂.defect ℓ := by
  subst hX
  congr 1
  ext u v _
  exact hα u v

private theorem isCoboundary_congr_complex {X₁ X₂ : TwoComplex W} (hX : X₁ = X₂)
    {α₁ : Cochain X₁ G} {α₂ : Cochain X₂ G} (hα : ∀ u v, α₁ u v = α₂ u v) :
    α₁.IsCoboundary ↔ α₂.IsCoboundary := by
  subst hX
  suffices α₁ = α₂ by rw [this]
  ext u v _
  exact hα u v

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `cost`. -/
theorem cost_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (complete V) G) (β : V → G) (e : V ≃ W) :
    (α.relabelComplete e).cost ℓ (β ∘ e.symm) = α.cost ℓ β :=
  (cost_congr_complex ℓ (relabel_complete e).symm (fun _ _ => rfl) (β ∘ e.symm)).trans
    (α.cost_relabel ℓ β e)

/-- Relabelling a cochain on `complete V` along `e : V ≃ W` preserves `gaugeDist`. -/
@[simp]
theorem gaugeDist_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    (ℓ : GroupNorm G) (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).gaugeDist ℓ = α.gaugeDist ℓ :=
  (gaugeDist_congr_complex ℓ (relabel_complete e).symm (fun _ _ => rfl)).trans
    (α.gaugeDist_relabel ℓ e)

/-- Under a conjugation-invariant norm, relabelling a cochain on `complete V` along `e : V ≃ W`
preserves `defect`. -/
theorem defect_relabelComplete [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
    {ℓ : GroupNorm G} (hℓ : ℓ.toGroupSeminorm.IsConjInvariant)
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).defect ℓ = α.defect ℓ :=
  (defect_congr_complex ℓ (relabel_complete e).symm (fun _ _ => rfl)).trans
    (α.defect_relabel hℓ e)

@[simp]
theorem isCoboundary_relabelComplete [Fintype V] [Fintype W]
    (α : Cochain (complete V) G) (e : V ≃ W) :
    (α.relabelComplete e).IsCoboundary ↔ α.IsCoboundary :=
  (isCoboundary_congr_complex (relabel_complete e).symm (fun _ _ => rfl)).trans
    (α.isCoboundary_relabel e)

end Relabel

/-! ### Change of coefficients and positive norm scaling -/

section ChangeOfCoefficients

variable {V G H K : Type*} [Group G] [Group H] [Group K] {X : TwoComplex V}

/-- Push a cochain forward along a group homomorphism `φ : G →* H`. -/
def map (φ : G →* H) (α : Cochain X G) : Cochain X H where
  toFun u v := φ (α u v)
  inv_symm u v huv := by rw [α.map_swap huv, map_inv]
  apply_eq_one_of_not_adj u v huv := by rw [α.map_of_not_adj huv, map_one]

@[simp]
theorem map_apply (φ : G →* H) (α : Cochain X G) (u v : V) :
    α.map φ u v = φ (α u v) := (rfl)

@[simp]
theorem map_id (α : Cochain X G) : α.map (MonoidHom.id G) = α := by
  ext u v _
  rfl

theorem map_comp (ψ : H →* K) (φ : G →* H) (α : Cochain X G) :
    α.map (ψ.comp φ) = (α.map φ).map ψ := by
  ext u v _
  rfl

@[simp]
theorem map_one (φ : G →* H) : (1 : Cochain X G).map φ = 1 := by
  ext u v _
  simp

theorem map_smul (φ : G →* H) (β : V → G) (α : Cochain X G) :
    (β • α).map φ = (φ ∘ β) • α.map φ := by
  ext u v huv
  simp [huv]

@[simp]
theorem holonomy_map (φ : G →* H) (α : Cochain X G) (u v w : V) :
    (α.map φ).holonomy u v w = φ (α.holonomy u v w) := by
  simp [holonomy_def]

theorem IsCoboundary.map {α : Cochain X G} (hα : α.IsCoboundary) (φ : G →* H) :
    (α.map φ).IsCoboundary := by
  rw [isCoboundary_def] at hα ⊢
  obtain ⟨β, hβ⟩ := hα
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
  rw [defect_def, defect_def]
  exact sum_congr rfl fun p _ => by simp [hφ]

/-- Embedding a `K`-valued cochain into `G` along a subgroup `K ≤ G` preserves `defect` relative
to the restricted norm `ℓ.comp K.subtype_injective`. -/
@[simp]
theorem defect_map_subtype (ℓ : GroupNorm G) (L : Subgroup G) (α : Cochain X L) :
    (α.map L.subtype).defect ℓ = α.defect (ℓ.comp L.subtype_injective) :=
  α.defect_map_eq fun x => (ℓ.comp_apply L.subtype_injective x).symm

/-- Embedding a `K`-valued cochain into `G` along a subgroup `K ≤ G` gives a `gaugeDist` in `G`
at most its `gaugeDist` in `K`. -/
theorem gaugeDist_map_subtype_le (ℓ : GroupNorm G) (L : Subgroup G) (α : Cochain X L) :
    (α.map L.subtype).gaugeDist ℓ ≤ α.gaugeDist (ℓ.comp L.subtype_injective) :=
  α.gaugeDist_map_le fun x => (ℓ.comp_apply L.subtype_injective x).symm.le

/-- Scaling a group norm by a positive real `r` scales `defect` by `r`. -/
@[simp]
theorem defect_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) :
    α.defect (ℓ.smulOfPos hr) = r * α.defect ℓ := by
  simp [defect_def, mul_sum]

/-- Scaling a group norm by a positive real `r` scales `cost` by `r`. -/
@[simp]
theorem cost_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) (β : V → G) :
    α.cost (ℓ.smulOfPos hr) β = r * α.cost ℓ β := by
  simp [cost_def, mul_sum]

/-- Scaling a group norm by a positive real `r` scales `gaugeDist` by `r`. -/
@[simp]
theorem gaugeDist_smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (α : Cochain X G) :
    α.gaugeDist (ℓ.smulOfPos hr) = r * α.gaugeDist ℓ := by
  simp_rw [gaugeDist_def, cost_smulOfPos, ← Real.mul_iInf_of_nonneg hr.le]

end Metric

end ChangeOfCoefficients

end Cochain

end TauCeti

end

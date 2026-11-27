/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.CheegerConstant
public import TauCeti.Combinatorics.Optimization.Replication

/-!
# Balanced replication of cochains on the complete complex

For a cochain `α` on the complete two-complex `complete V` and a finite type `ι`, the balanced
replication `α.replicate ι` is the cochain on `complete (V ×ₗ ι)` that reads every pair of
vertices through the cluster projection `x ↦ (ofLex x).1` (a special case of the pullback
`Cochain.comapComplete`). Each vertex `i : V` becomes the cluster `{i} ×ₗ ι`, edges inside a
cluster carry `α i i = 1`, and every edge from cluster `i` to cluster `j ≠ i` carries `α i j`.

With the lexicographic order on `V ×ₗ ι` and for every group norm `ℓ` (no conjugation invariance
is needed):

* `Cochain.defect_replicate`: the defect is multiplied by `(Fintype.card ι) ^ 3`, because a
  triangle meeting three clusters carries the holonomy of the underlying triangle, each triangle
  of `complete V` has `(Fintype.card ι) ^ 3` lifts, and every other triangle has trivial holonomy;
* `Cochain.gaugeDist_replicate`: the gauge distance is multiplied by `(Fintype.card ι) ^ 2`.
  Copying a gauge across each cluster gives the upper bound. The lower bound averages over the
  sections choosing one vertex in each cluster (`Finset.ciInf_add_sum_eq_card_sq_mul_ciInf_sum`),
  without assuming that gauges are constant on clusters or that the infimum is attained;
* `Cochain.cost_replicate_comp`: a gauge constant on each cluster has cost multiplied by
  `(Fintype.card ι) ^ 2`;
* `Cochain.defect_div_gaugeDist_replicate`: hence the expansion ratio is multiplied by
  `Fintype.card ι`, and `TauCeti.h1_complete_lex_le_card_mul_div` bounds the Cheeger constant of
  `complete (V ×ₗ ι)` by `Fintype.card ι` times the ratio of any cochain on `complete V` at
  positive gauge distance.

In particular, if `ι` is nonempty and a cochain on `complete V` at positive gauge distance has
ratio `Fintype.card V / 3`, then its replication has positive gauge distance and ratio
`Fintype.card (V ×ₗ ι) / 3`. When `ℓ` is moreover conjugation invariant, the star bound
`TauCeti.card_div_three_le_h1` then shows that this value equals `h1 (complete (V ×ₗ ι)) ℓ`.

## References

* Jeromie Beasley, *The Permutation Coboundary Constant of the Complete Complex Is k/3 for Every
  k≥4*, Zenodo, doi:10.5281/zenodo.23245792, version 7, Lemma 6.
-/

public section

open Finset

namespace TauCeti

open TwoComplex

namespace Cochain

variable {V G : Type*} [Group G] [Fintype V]

/-! ### The replicated cochain -/

/-- The balanced replication of a cochain on `complete V` along a finite type `ι`: the pullback of
`α` to `complete (V ×ₗ ι)` along the cluster projection `x ↦ (ofLex x).1`. Edges inside a cluster
carry `1`. -/
def replicate (α : Cochain (complete V) G) (ι : Type*) [Fintype ι] :
    Cochain (complete (V ×ₗ ι)) G :=
  α.comapComplete fun x => (ofLex x).1

variable {ι : Type*} [Fintype ι]

@[simp, grind =] theorem replicate_apply (α : Cochain (complete V) G) (x y : V ×ₗ ι) :
    α.replicate ι x y = α (ofLex x).1 (ofLex y).1 :=
  comapComplete_apply α _ x y

/-- On increasing pairs, replication uses the seed between distinct clusters and gives the
identity within a cluster. -/
theorem replicate_ofLt [LinearOrder V] [LinearOrder ι] (f : V → V → G) :
    (ofLt (complete V) f).replicate ι =
      ofLt (complete (V ×ₗ ι)) fun x y =>
        if (ofLex x).1 = (ofLex y).1 then 1 else f (ofLex x).1 (ofLex y).1 := by
  apply ext_of_lt
  intro x y hxy hadj
  rw [replicate_apply, ofLt_apply_of_lt _ hadj hxy]
  have h : (ofLex x).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 := by
    rcases Prod.Lex.toLex_lt_toLex.mp hxy with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  rcases h with h | h
  · rw [ite_eq_right h.ne, ofLt_apply_of_lt _ ((adj_complete _ _).mpr h.ne) h]
  · rw [ite_eq_left h, h, apply_self]

@[simp] theorem replicate_one : (1 : Cochain (complete V) G).replicate ι = 1 :=
  comapComplete_one _

/-- Replication intertwines the gauge action with pulling gauges back along the cluster
projection. -/
@[simp] theorem replicate_smul (β : V → G) (α : Cochain (complete V) G) :
    (β • α).replicate ι = (fun x : V ×ₗ ι => β (ofLex x).1) • α.replicate ι :=
  comapComplete_smul β α _

@[simp, grind =] theorem holonomy_replicate (α : Cochain (complete V) G) (x y z : V ×ₗ ι) :
    (α.replicate ι).holonomy x y z = α.holonomy (ofLex x).1 (ofLex y).1 (ofLex z).1 :=
  holonomy_comapComplete α _ x y z

/-- With at least one vertex per cluster, the replication of `α` is a coboundary exactly when `α`
is one. -/
@[simp] theorem isCoboundary_replicate_iff [Nonempty ι] (α : Cochain (complete V) G) :
    (α.replicate ι).IsCoboundary ↔ α.IsCoboundary :=
  α.isCoboundary_comapComplete_iff fun i => ⟨toLex (i, Classical.arbitrary ι), rfl⟩

/-! ### Defect -/

variable [LinearOrder V] [LinearOrder ι]

/-- Balanced replication multiplies the defect by `(Fintype.card ι) ^ 3`, for every group norm. -/
@[simp] theorem defect_replicate (ℓ : GroupNorm G) (α : Cochain (complete V) G) :
    (α.replicate ι).defect ℓ = (Fintype.card ι : ℝ) ^ 3 * α.defect ℓ := by
  rw [defect_complete, defect_complete]
  simp only [holonomy_replicate]
  rw [Fintype.sum_filter_lt_lex_triple (ι := ι) (fun t => ℓ (α.holonomy t.1 t.2.1 t.2.2))
    (by simp) (by simp), nsmul_eq_mul, Nat.cast_pow]

/-! ### Gauge distance -/

/-- Balanced replication multiplies the gauge distance by `(Fintype.card ι) ^ 2`, for every group
norm, even when no optimal gauge exists. -/
@[simp] theorem gaugeDist_replicate (ℓ : GroupNorm G) (α : Cochain (complete V) G) :
    (α.replicate ι).gaugeDist ℓ = (Fintype.card ι : ℝ) ^ 2 * α.gaugeDist ℓ := by
  set E : Finset (V × V) := {p : V × V | p.1 < p.2}
  -- Reindex gauges on `V ×ₗ ι` as families of gauges on the clusters.
  let ev : (V → ι → G) ≃ ((V ×ₗ ι) → G) :=
    (Equiv.curry V ι G).symm.trans (Equiv.arrowCongr toLex (.refl _))
  have hev (β : V → ι → G) (v : V) (a : ι) : ev β (toLex (v, a)) = β v a := by simp [ev]
  -- The intra-cluster cost: nonnegative, and zero on gauges constant on each cluster.
  let c (β : V → ι → G) : ℝ := ∑ v : V, ∑ q : ι × ι with q.1 < q.2, ℓ ((β v q.1)⁻¹ * β v q.2)
  have hc (β : V → ι → G) : 0 ≤ c β := sum_nonneg fun _ _ => sum_nonneg fun _ _ => apply_nonneg ℓ _
  have hc_const (β : V → G) : c (fun v _ => β v) = 0 := by simp [c]
  have hsplit (β : V → ι → G) : (α.replicate ι).cost ℓ (ev β) =
      c β + ∑ e ∈ E, ∑ a : ι, ∑ b : ι, ℓ ((β e.1 a)⁻¹ * α e.1 e.2 * β e.2 b) := by
    rw [cost_complete, Fintype.sum_filter_lt_lex (V := V) (ι := ι)]
    simp [hev, c, E]
  rw [gaugeDist_def, ← ev.iInf_congr hsplit,
    E.ciInf_add_sum_eq_card_sq_mul_ciInf_sum (fun _ he => ne_of_lt (mem_filter.mp he).2)
      (fun e g h => ℓ (g⁻¹ * α e.1 e.2 * h)) c hc hc_const, gaugeDist_def]
  simp_rw [cost_complete, E]

/-- A gauge pulled back along the cluster projection has cost multiplied by `(Fintype.card ι) ^ 2`:
edges inside a cluster carry `1`, and each base edge is copied once for every pair of cluster
points. -/
theorem cost_replicate_comp (ℓ : GroupNorm G) (α : Cochain (complete V) G) (β : V → G) :
    (α.replicate ι).cost ℓ (β ∘ fun x => (ofLex x).1) =
      (Fintype.card ι : ℝ) ^ 2 * α.cost ℓ β := by
  rw [cost_complete, cost_complete, Fintype.sum_filter_lt_lex (V := V) (ι := ι)]
  simp only [Function.comp_apply, replicate_apply, ofLex_toLex, apply_self, mul_one,
    inv_mul_cancel, map_one_eq_zero, sum_const_zero, zero_add, sum_const, card_univ,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [← mul_assoc, ← pow_two]

/-- Balanced replication multiplies the expansion ratio `defect / gaugeDist` by `Fintype.card ι`.
No hypothesis is needed: when `ι` is empty or `α` has gauge distance zero, both sides vanish. -/
theorem defect_div_gaugeDist_replicate (ℓ : GroupNorm G) (α : Cochain (complete V) G) :
    (α.replicate ι).defect ℓ / (α.replicate ι).gaugeDist ℓ =
      Fintype.card ι * (α.defect ℓ / α.gaugeDist ℓ) := by
  rw [defect_replicate, gaugeDist_replicate]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with h | h
  · simp [h]
  · rw [mul_div_mul_comm, pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero 2 h)]

/-- The replication of `α` has positive gauge distance exactly when `ι` is nonempty and `α` has
positive gauge distance. -/
theorem gaugeDist_replicate_pos_iff (ℓ : GroupNorm G) (α : Cochain (complete V) G) :
    0 < (α.replicate ι).gaugeDist ℓ ↔ Nonempty ι ∧ 0 < α.gaugeDist ℓ := by
  rw [gaugeDist_replicate, ← Fintype.card_pos_iff]
  constructor
  · intro h
    have hd := α.gaugeDist_nonneg ℓ
    exact ⟨Nat.pos_of_ne_zero fun h0 => by simp [h0] at h,
      lt_of_le_of_ne hd fun h0 => by simp [← h0] at h⟩
  · rintro ⟨hι, hα⟩
    positivity

end Cochain

/-- Replicating any cochain at positive gauge distance on `complete V` along a finite type `ι`
bounds the Cheeger constant of `complete (V ×ₗ ι)` by `Fintype.card ι` times its expansion ratio. -/
theorem h1_complete_lex_le_card_mul_div {V ι G : Type*} [Group G] [Fintype V] [LinearOrder V]
    [Fintype ι] [LinearOrder ι] {ℓ : GroupNorm G} {α : Cochain (complete V) G}
    (hα : 0 < α.gaugeDist ℓ) :
    h1 (complete (V ×ₗ ι)) ℓ ≤ Fintype.card ι * (α.defect ℓ / α.gaugeDist ℓ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Without vertices every cochain is trivial, so both sides vanish.
    rw [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
    refine (h1_eq_zero_of_forall_gaugeDist_eq_zero fun α' => ?_).le
    rw [show α' = 1 from Cochain.ext fun x => isEmptyElim (ofLex x).2, Cochain.gaugeDist_one]
  · exact (h1_le_div ((Cochain.gaugeDist_replicate_pos_iff ℓ α).mpr ⟨hι, hα⟩)).trans_eq
      (Cochain.defect_div_gaugeDist_replicate ℓ α)

end TauCeti

end

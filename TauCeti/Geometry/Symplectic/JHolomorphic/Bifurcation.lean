/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.ConfigurationCount

/-!
# Invariance of the weighted configuration count under local bifurcations

Along a generic path of almost complex structures the set of embedded pseudoholomorphic curves
changes only through local bifurcations. Two ordinary curves of opposite determinant signs are
born or die together; two square-zero tori with opposite determinant signs are born or die
together; a torus undergoes period doubling, in which one of its twisted normal operators changes
sign while a torus in twice its class appears or disappears. Taubes's weighted count is invariant
because each of these changes leaves the local contribution of the curves involved unchanged.
This file proves that cancellation for the abstract count
`TauCeti.configurationCount r cls w s A` of compatible configurations.

The curves taking part in a bifurcation are close to each other, so they form a *cluster* `K`:
every candidate `d` outside the cluster is compatible with either all or none of its members.
Writing `U` for the candidates compatible with the cluster, a configuration of `K ∪ s` either
avoids `K`, or splits into a nonempty configuration of `K` in some class `B` and a configuration
of `U` in class `A - B`. Hence (`TauCeti.configurationCount_union`)

`N_{K ∪ s}(A) = N_s(A) + ∑ᶠ B ≠ 0, N_K(B) N_U(A - B)`,

so the count depends on the cluster only through its *local counts* `N_K(B)`, `B ≠ 0`. Replacing
`K` by a cluster `K'` with the same compatibility with `s` and the same local counts does not
change any count (`TauCeti.configurationCount_union_eq_union`). The local counts are then
computed for the three bifurcations:

* **Ordinary birth and death.** Two incompatible candidates `c` and `d` of the same class, with
  the same compatibility with the other candidates and opposite weights `w d k = -w c k`, have
  vanishing local counts. Adding them does not change the count
  (`TauCeti.configurationCount_insert_insert_of_weight_eq_neg`).
* **Tori on a ray.** The local counts of a compatible cluster of tori on the ray of a class `A₀`
  that is not torsion are the coefficients of its ray series `∏ f_(σ c, i c)(t ^ m c)`
  (`TauCeti.rayTorusWeightSeries`). Two such clusters with the same ray series give the same
  counts (`TauCeti.configurationCount_union_eq_union_of_rayTorusWeightSeries_eq`). In particular,
  adding two compatible tori of the same class and index with opposite determinant signs does not
  change the count (`TauCeti.configurationCount_insert_insert_torusWeight_not`), and neither does
  period doubling: a torus of label `(σ, j)` contributes as much as a torus of label `(σ, j + 1)`
  in the same class together with a torus of label `(σ, j % 2)` in twice its class
  (`TauCeti.configurationCount_insert_eq_insert_insert_torusWeight_castSucc`), or with a torus of
  label `(!σ, j % 2)` when the first torus has label `(σ, j + 1)` and is replaced by one of label
  `(σ, j)` (`TauCeti.configurationCount_insert_eq_insert_insert_torusWeight_succ`).

The ray-series identities behind the torus statements are
`TauCeti.torusWeightSeries_mul_not`, `TauCeti.torusWeightSeries_castSucc` and
`TauCeti.torusWeightSeries_succ`. Unlike the ray-series statements of
`TauCeti.Geometry.Symplectic.JHolomorphic.TorusWeight`, the invariance here holds for the count
over an arbitrary set of candidates, whose members need not be pairwise compatible and need not
lie on one ray.

The candidates, their classes, weights and compatibility, and the description of a bifurcation
as the replacement of one cluster by another, are inputs here; constructing the one-dimensional
bifurcation models of a generic path of almost complex structures is separate.

## Main results

* `TauCeti.configurationCount_union`: the cluster expansion of the count.
* `TauCeti.configurationCount_union_eq_union`: replacing a cluster by one with the same local
  counts.
* `TauCeti.configurationCount_insert_insert_of_weight_eq_neg`: ordinary birth and death.
* `TauCeti.configurationCount_union_eq_union_of_rayTorusWeightSeries_eq`: replacing a cluster of
  tori by one with the same ray series.
* `TauCeti.configurationCount_insert_insert_torusWeight_not`: birth and death of tori.
* `TauCeti.configurationCount_insert_eq_insert_insert_torusWeight_castSucc`,
  `TauCeti.configurationCount_insert_eq_insert_insert_torusWeight_succ`: period doubling.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* D. McDuff, *Lectures on Gromov invariants for symplectic 4-manifolds*, arXiv:dg-ga/9606005.
-/

public section

open PowerSeries

namespace TauCeti

variable {ι H R : Type*}

section Cluster

variable [AddCommGroup H] {r : ι → ι → Prop} {cls : ι → H} {K K' s U : Set ι} {A B : H}
  {ω : H →+ ℝ}

/-- A configuration `m` of the cluster `K` together with a configuration `n` of the candidates
`U` compatible with `K` is a configuration of `K ∪ s`, and splitting it along `K` recovers `m`
and `n`. -/
private theorem add_mem_compatibleConfigurations_union [DecidablePred (· ∈ K)]
    (hKs : Disjoint K s) (hUs : U ⊆ s) (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    {m n : ι →₀ ℕ} (hm : m ∈ compatibleConfigurations r cls K B)
    (hn : n ∈ compatibleConfigurations r cls U (A - B)) :
    m + n ∈ compatibleConfigurations r cls (K ∪ s) A ∧ (m + n).filter (· ∈ K) = m ∧
      (m + n).filter (· ∉ K) = n := by
  classical
  rw [mem_compatibleConfigurations] at hm hn
  rw [mem_compatibleConfigurations]
  have hnK : ∀ d ∈ n.support, d ∉ K := fun d hd hdK ↦
    Set.disjoint_left.1 hKs hdK (hUs (hn.1 hd))
  have hsupp : ↑(m + n).support ⊆ (↑m.support ∪ ↑n.support : Set ι) := by
    exact_mod_cast Finsupp.support_add
  refine ⟨⟨fun d hd ↦ ?_, ?_, ?_⟩, ?_, ?_⟩
  · rcases hsupp hd with hd | hd
    exacts [Or.inl (hm.1 hd), Or.inr (hUs (hn.1 hd))]
  · refine Set.Pairwise.mono hsupp (Set.pairwise_union.2 ⟨hm.2.1, hn.2.1, fun a ha b hb _ ↦ ?_⟩)
    exact (hU a (hm.1 ha) b (hUs (hn.1 hb))).2 (hn.1 hb)
  · rw [map_add, hm.2.2, hn.2.2, add_sub_cancel]
  · rw [Finsupp.filter_add,
      (Finsupp.filter_eq_self_iff _ _).2 fun d hd ↦ hm.1 (Finsupp.mem_support_iff.2 hd),
      (Finsupp.filter_eq_zero_iff _ _).2 fun d hd ↦ Finsupp.notMem_support_iff.1 fun h ↦ hnK d h hd,
      add_zero]
  · rw [Finsupp.filter_add,
      (Finsupp.filter_eq_zero_iff _ _).2 fun d hd ↦
        Finsupp.notMem_support_iff.1 fun h ↦ hd (hm.1 h),
      (Finsupp.filter_eq_self_iff _ _).2 fun d hd ↦ hnK d (Finsupp.mem_support_iff.2 hd), zero_add]

/-- A configuration of `K ∪ s` meeting the cluster `K` splits into a configuration of `K` and a
configuration of the candidates `U` compatible with `K`. -/
private theorem filter_mem_compatibleConfigurations [DecidablePred (· ∈ K)]
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U) {l : ι →₀ ℕ}
    (hl : l ∈ compatibleConfigurations r cls (K ∪ s) A) (hlK : l.filter (· ∈ K) ≠ 0) :
    l.filter (· ∈ K) ∈ compatibleConfigurations r cls K
        (Finsupp.linearCombination ℕ cls (l.filter (· ∈ K))) ∧
      l.filter (· ∉ K) ∈ compatibleConfigurations r cls U
        (A - Finsupp.linearCombination ℕ cls (l.filter (· ∈ K))) := by
  classical
  rw [mem_compatibleConfigurations] at hl
  rw [mem_compatibleConfigurations, mem_compatibleConfigurations]
  have hsub (p : ι → Prop) [DecidablePred p] : ↑(l.filter p).support ⊆ (↑l.support : Set ι) :=
    fun d hd ↦ by
      rw [Finset.mem_coe, Finsupp.support_filter, Finset.mem_filter] at hd
      exact hd.1
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hlK
  rw [Finsupp.support_filter, Finset.mem_filter] at hk
  refine ⟨⟨fun d hd ↦ ?_, hl.2.1.mono (hsub _), rfl⟩, ⟨fun d hd ↦ ?_, hl.2.1.mono (hsub _), ?_⟩⟩
  · rw [Finset.mem_coe, Finsupp.support_filter, Finset.mem_filter] at hd
    exact hd.2
  · rw [Finset.mem_coe, Finsupp.support_filter, Finset.mem_filter] at hd
    have hds : d ∈ s := (hl.1 hd.1).resolve_left hd.2
    exact (hU k hk.2 d hds).1 ⟨hl.2.1 hk.1 hd.1 fun h ↦ hd.2 (h ▸ hk.2),
      hl.2.1 hd.1 hk.1 fun h ↦ hd.2 (h ▸ hk.2)⟩
  · rw [eq_sub_iff_add_eq', ← map_add, Finsupp.filter_add_filter_not, hl.2.2]

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Cluster expansion of the count.** Let `K` be a cluster of candidates, disjoint from `s`,
such that a candidate `d ∈ s` is compatible with a member of `K` exactly when `d ∈ U`. If the
candidates of `K ∪ s` have positive area `ω`, with finitely many of area at most `ω A`, then the
count in class `A` over `K ∪ s` is the count over `s` plus the contributions of the nonempty
configurations of `K`: the local count `N_K(B)` in each class `B ≠ 0`, times the count over `U`
in the complementary class `A - B`. -/
theorem configurationCount_union (hKs : Disjoint K s) (hUs : U ⊆ s)
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U) (hpos : ∀ c ∈ K ∪ s, 0 < ω (cls c))
    (hfin : {c ∈ K ∪ s | ω (cls c) ≤ ω A}.Finite) :
    configurationCount r cls w (K ∪ s) A =
      configurationCount r cls w s A +
        ∑ᶠ B ∈ {B : H | B ≠ 0},
          configurationCount r cls w K B * configurationCount r cls w U (A - B) := by
  classical
  have hposK : ∀ c ∈ K, 0 < ω (cls c) := fun c hc ↦ hpos c (Or.inl hc)
  have hposU : ∀ c ∈ U, 0 < ω (cls c) := fun c hc ↦ hpos c (Or.inr (hUs hc))
  have hfinA := finite_compatibleConfigurations (r := r) hpos hfin
  set F := hfinA.toFinset
  -- The class of the part of a configuration lying in `K`.
  set κ : (ι →₀ ℕ) → H := fun l ↦ Finsupp.linearCombination ℕ cls (l.filter (· ∈ K))
  -- The configurations of `K` and of `U` occurring in a splitting are finite in number.
  have hsplit {l : ι →₀ ℕ} (hl : l ∈ F) (hlK : l.filter (· ∈ K) ≠ 0) :
      κ l ≠ 0 ∧ (compatibleConfigurations r cls K (κ l)).Finite ∧
        (compatibleConfigurations r cls U (A - κ l)).Finite := by
    rw [Set.Finite.mem_toFinset] at hl
    obtain ⟨hm, hn⟩ := filter_mem_compatibleConfigurations hU hl hlK
    have hB := area_nonneg_of_mem_compatibleConfigurations (fun c hc ↦ (hposK c hc).le) hm
    have hAB := area_nonneg_of_mem_compatibleConfigurations (fun c hc ↦ (hposU c hc).le) hn
    have hω : ω A = ω (κ l) + ω (A - κ l) := by rw [← map_add, add_sub_cancel]
    refine ⟨fun h ↦ hlK (eq_zero_of_mem_compatibleConfigurations_of_area_nonpos hposK hm
      (by simp only [κ] at h; rw [h, map_zero])),
      finite_compatibleConfigurations hposK (hfin.subset ?_),
      finite_compatibleConfigurations hposU (hfin.subset ?_)⟩
    · exact fun c hc ↦ ⟨Or.inl hc.1, hc.2.trans (by linarith)⟩
    · exact fun c hc ↦ ⟨Or.inr (hUs hc.1), hc.2.trans (by linarith)⟩
  rw [configurationCount_eq_sum hfinA,
    ← Finset.sum_filter_add_sum_filter_not F fun l ↦ l.filter (· ∈ K) = 0]
  congr 1
  · -- The configurations avoiding `K` are the configurations of `s`.
    have hfins : (compatibleConfigurations r cls s A).Finite :=
      hfinA.subset (compatibleConfigurations_mono Set.subset_union_right)
    rw [configurationCount_eq_sum hfins]
    refine Finset.sum_congr (Finset.ext fun l ↦ ?_) fun _ _ ↦ rfl
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset,
      Finsupp.filter_eq_zero_iff, mem_compatibleConfigurations, mem_compatibleConfigurations]
    refine ⟨fun ⟨hl, hK⟩ ↦ ⟨fun c hc ↦ (hl.1 hc).resolve_left fun hcK ↦
      Finsupp.mem_support_iff.1 hc (hK c hcK), hl.2⟩, fun hl ↦
      ⟨⟨hl.1.trans Set.subset_union_right, hl.2⟩, fun c hcK ↦
        Finsupp.notMem_support_iff.1 fun hc ↦ Set.disjoint_left.1 hKs hcK (hl.1 hc)⟩⟩
  · -- The configurations meeting `K` are grouped by the class of their part in `K`.
    set F₁ := F.filter fun l ↦ ¬l.filter (· ∈ K) = 0
    rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := F₁.image κ) ?_,
      ← Finset.sum_fiberwise_of_maps_to fun l hl ↦ Finset.mem_image_of_mem κ hl]
    · refine Finset.sum_congr rfl fun B hB ↦ ?_
      obtain ⟨l₀, hl₀, rfl⟩ := Finset.mem_image.1 hB
      rw [Finset.mem_filter] at hl₀
      obtain ⟨-, hKfin, hUfin⟩ := hsplit hl₀.1 hl₀.2
      rw [configurationCount_eq_sum hKfin, configurationCount_eq_sum hUfin, Finset.sum_mul_sum,
        ← Finset.sum_product']
      refine Finset.sum_nbij' (fun l ↦ (l.filter (· ∈ K), l.filter (· ∉ K)))
        (fun p ↦ p.1 + p.2) (fun l hl ↦ ?_) (fun p hp ↦ ?_) (fun l _ ↦ ?_) (fun p hp ↦ ?_)
        fun l _ ↦ ?_
      · rw [Finset.mem_filter, Finset.mem_filter] at hl
        obtain ⟨hm, hn⟩ := filter_mem_compatibleConfigurations hU
          ((Set.Finite.mem_toFinset _).1 hl.1.1) hl.1.2
        rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
        exact ⟨hl.2 ▸ hm, hl.2 ▸ hn⟩
      · rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
        obtain ⟨hmn, hK, -⟩ := add_mem_compatibleConfigurations_union hKs hUs hU hp.1 hp.2
        have hκ : κ (p.1 + p.2) = κ l₀ := by
          simp only [κ, hK, (mem_compatibleConfigurations.1 hp.1).2.2]
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hmn, ?_⟩,
          hκ⟩
        rw [hK]
        intro h0
        exact (hsplit hl₀.1 hl₀.2).1
          (by rw [← (mem_compatibleConfigurations.1 hp.1).2.2, h0, map_zero])
      · exact Finsupp.filter_add_filter_not l _
      · rw [Finset.mem_product, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hp
        obtain ⟨-, hK, hnK⟩ := add_mem_compatibleConfigurations_union hKs hUs hU hp.1 hp.2
        exact Prod.ext hK hnK
      · exact (Finsupp.prod_filter_mul_prod_filter_not (f := l) (p := (· ∈ K)) w).symm
    · -- Only the classes of the parts in `K` of configurations meeting `K` contribute.
      ext B
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.coe_image,
        Set.mem_image, Finset.mem_coe]
      refine ⟨fun ⟨hB, hNB⟩ ↦ ⟨?_, hNB⟩, fun ⟨⟨l, hl, hlB⟩, hNB⟩ ↦ ⟨?_, hNB⟩⟩
      · rw [configurationCount_def, configurationCount_def] at hNB
        obtain ⟨m, hm, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero (left_ne_zero_of_mul hNB)
        obtain ⟨n, hn, -⟩ := exists_ne_zero_of_finsum_mem_ne_zero (right_ne_zero_of_mul hNB)
        obtain ⟨hmn, hK, -⟩ := add_mem_compatibleConfigurations_union hKs hUs hU hm hn
        refine ⟨m + n, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hmn, ?_⟩, ?_⟩
        · rw [hK]
          intro h0
          exact hB (by rw [← (mem_compatibleConfigurations.1 hm).2.2, h0, map_zero])
        · simp only [κ, hK, (mem_compatibleConfigurations.1 hm).2.2]
      · rw [Finset.mem_filter] at hl
        exact hlB ▸ (hsplit hl.1 hl.2).1

/-- **Replacing a cluster.** Let `K` and `K'` be two clusters of candidates, disjoint from `s`,
with the same compatibility with `s`: a candidate `d ∈ s` is compatible with a member of `K`, or
of `K'`, exactly when `d ∈ U`. If `K` and `K'` have the same local counts `N_K(B) = N_K'(B)` in
every class `B ≠ 0`, then replacing `K` by `K'` does not change the count in any class. -/
theorem configurationCount_union_eq_union (hKs : Disjoint K s) (hK's : Disjoint K' s)
    (hUs : U ⊆ s) (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hU' : ∀ k ∈ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U) (hpos : ∀ c ∈ K ∪ s, 0 < ω (cls c))
    (hpos' : ∀ c ∈ K' ∪ s, 0 < ω (cls c)) (hfin : {c ∈ K ∪ s | ω (cls c) ≤ ω A}.Finite)
    (hfin' : {c ∈ K' ∪ s | ω (cls c) ≤ ω A}.Finite)
    (hK : ∀ B ≠ 0, configurationCount r cls w K B = configurationCount r cls w K' B) :
    configurationCount r cls w (K ∪ s) A = configurationCount r cls w (K' ∪ s) A := by
  rw [configurationCount_union hKs hUs hU hpos hfin, configurationCount_union hK's hUs hU' hpos'
    hfin']
  exact congrArg _ (finsum_mem_congr rfl fun B hB ↦ by rw [hK B hB])

end Cluster

/-! ### Ordinary birth and death -/

section BirthDeath

variable [AddCommGroup H] [CommRing R] {r : ι → ι → Prop} {cls : ι → H} {w : ι → ℕ → R}
  {s : Set ι} {A B : H} {ω : H →+ ℝ} {c d : ι}

/-- The weight of a single candidate taken with positive multiplicity. -/
private theorem prod_single_of_ne_zero (e : ι) {k : ℕ} (hk : k ≠ 0) :
    (Finsupp.single e k).prod w = w e k := by
  rw [Finsupp.prod, Finsupp.support_single _ hk, Finset.prod_singleton,
    Finsupp.single_eq_same]

/-- The local counts of two incompatible candidates of the same class with opposite weights
vanish in every nonzero class. -/
private theorem configurationCount_pair_eq_zero (hcd : c ≠ d) (hr : ¬(r c d ∧ r d c))
    (hcls : cls d = cls c) (hw : ∀ k ≠ 0, w d k = -w c k)
    (hpos : ∀ e ∈ ({c, d} : Set ι), 0 < ω (cls e)) (hB : B ≠ 0) :
    configurationCount r cls w {c, d} B = 0 := by
  classical
  have hfin := finite_compatibleConfigurations (r := r) (A := B) hpos
    ((Set.toFinite {c, d}).subset fun e he ↦ he.1)
  -- Since `c` and `d` are incompatible, a configuration is one of them with some multiplicity.
  have hsingle (l : ι →₀ ℕ) (hl : l ∈ compatibleConfigurations r cls {c, d} B) :
      ∃ e ∈ ({c, d} : Set ι), ∃ k ≠ 0, l = Finsupp.single e k ∧ k • cls e = B := by
    rw [mem_compatibleConfigurations] at hl
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hB (by rw [← hl.2.2, map_zero])
    obtain ⟨e, he⟩ := Finsupp.support_nonempty_iff.2 hl0
    have hsupp : l.support ⊆ {e} := fun e' he' ↦ by
      by_contra hne
      rw [Finset.mem_singleton] at hne
      have h₁ := hl.2.1 he' he hne
      have h₂ := hl.2.1 he he' (Ne.symm hne)
      rcases hl.1 he with rfl | rfl <;> rcases hl.1 he' with rfl | rfl
      exacts [hne rfl, hr ⟨h₂, h₁⟩, hr ⟨h₁, h₂⟩, hne rfl]
    have hle : l = Finsupp.single e (l e) := Finsupp.eq_single_iff.2 ⟨hsupp, rfl⟩
    refine ⟨e, hl.1 he, l e, Finsupp.mem_support_iff.1 he, hle, ?_⟩
    rw [← hl.2.2, hle, Finsupp.linearCombination_single, Finsupp.single_eq_same]
  have hswap {e : ι} (he : e ∈ ({c, d} : Set ι)) :
      Equiv.swap c d e ∈ ({c, d} : Set ι) ∧ cls (Equiv.swap c d e) = cls e ∧
        Equiv.swap c d e ≠ e := by
    rcases he with rfl | rfl
    · refine ⟨by simp, by rw [Equiv.swap_apply_left, hcls], ?_⟩
      rw [Equiv.swap_apply_left]
      exact hcd.symm
    · refine ⟨by simp, by rw [Equiv.swap_apply_right, hcls], ?_⟩
      rw [Equiv.swap_apply_right]
      exact hcd
  -- Exchanging `c` and `d` pairs off the configurations, with opposite weights.
  rw [configurationCount_eq_sum hfin]
  refine Finset.sum_involution (fun l _ ↦ l.equivMapDomain (Equiv.swap c d)) (fun l hl ↦ ?_)
    (fun l hl _ ↦ ?_) (fun l hl ↦ ?_) fun l hl ↦ ?_
  · obtain ⟨e, he, k, hk, rfl, -⟩ := hsingle l ((Set.Finite.mem_toFinset _).1 hl)
    rw [Finsupp.equivMapDomain_single, prod_single_of_ne_zero e hk, prod_single_of_ne_zero _ hk]
    rcases he with rfl | rfl
    · rw [Equiv.swap_apply_left, hw k hk, add_neg_cancel]
    · rw [Equiv.swap_apply_right, hw k hk, neg_add_cancel]
  · obtain ⟨e, he, k, hk, rfl, -⟩ := hsingle l ((Set.Finite.mem_toFinset _).1 hl)
    rw [Finsupp.equivMapDomain_single, Ne, Finsupp.single_left_inj hk]
    exact (hswap he).2.2
  · obtain ⟨e, he, k, hk, rfl, hkB⟩ := hsingle l ((Set.Finite.mem_toFinset _).1 hl)
    rw [Set.Finite.mem_toFinset, Finsupp.equivMapDomain_single, mem_compatibleConfigurations,
      Finsupp.support_single _ hk, Finset.coe_singleton, Finsupp.linearCombination_single,
      (hswap he).2.1]
    exact ⟨Set.singleton_subset_iff.2 (hswap he).1, Set.pairwise_singleton _ _, hkB⟩
  · obtain ⟨e, -, k, -, rfl, -⟩ := hsingle l ((Set.Finite.mem_toFinset _).1 hl)
    rw [Finsupp.equivMapDomain_single, Finsupp.equivMapDomain_single, Equiv.swap_apply_self]

/-- **Ordinary birth and death.** Let `c` and `d` be two incompatible candidates outside `s` of
the same class, with the same compatibility with the candidates of `s` and opposite weights
`w d k = -w c k` for `k ≠ 0`. If the candidates have positive area `ω`, with finitely many of area
at most `ω A`, then adding `c` and `d` to `s` does not change the count in class `A`. Two distinct
embedded curves in the same class of positive square intersect, so they are incompatible. -/
theorem configurationCount_insert_insert_of_weight_eq_neg (hcd : c ≠ d) (hc : c ∉ s)
    (hd : d ∉ s) (hr : ¬(r c d ∧ r d c)) (hcls : cls d = cls c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) (hw : ∀ k ≠ 0, w d k = -w c k)
    (hpos : ∀ e ∈ insert c (insert d s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert d s) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c (insert d s)) A = configurationCount r cls w s A := by
  classical
  have hunion : insert c (insert d s) = ({c, d} : Set ι) ∪ s := by
    rw [Set.insert_union, Set.singleton_union]
  have hKs : Disjoint ({c, d} : Set ι) s := Set.disjoint_left.2 fun e he hes ↦ by
    rcases he with rfl | rfl
    exacts [hc hes, hd hes]
  have hsub : ∅ ∪ s ⊆ insert c (insert d s) := by
    rw [Set.empty_union]
    exact (Set.subset_insert d s).trans (Set.subset_insert c _)
  rw [hunion] at hpos hfin
  rw [hunion, configurationCount_union_eq_union (K' := ∅) (U := {e ∈ s | r c e ∧ r e c}) hKs
    (Set.empty_disjoint s) (Set.sep_subset _ _) (fun k hk e he ↦ ?_) (fun k hk ↦ hk.elim) hpos
    (fun e he ↦ hpos e (hunion ▸ hsub he)) hfin
    (hfin.subset fun e he ↦ ⟨hunion ▸ hsub he.1, he.2⟩) fun B hB ↦ ?_, Set.empty_union]
  · rw [Set.mem_sep_iff]
    rcases hk with rfl | rfl
    · exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · exact ⟨fun h ↦ ⟨he, (hcomp e he).1 h⟩, fun h ↦ (hcomp e he).2 h.2⟩
  · rw [configurationCount_pair_eq_zero hcd hr hcls hw (fun e he ↦ hpos e (Or.inl he)) hB,
      configurationCount_empty, ite_eq_right_iff.2 fun h ↦ (hB h).elim]

end BirthDeath

/-! ### Tori on a ray -/

section Ray

variable [AddCommGroup H] {r : ι → ι → Prop} {cls : ι → H} {w : ι → ℕ → ℤ}
  {s U : Set ι} {A A₀ : H} {ω : H →+ ℝ} {m : ι → ℕ+} {σ : ι → Bool} {i : ι → Fin 4}

/-- A configuration of candidates on the ray of `A₀` has its class on that ray. -/
private theorem exists_eq_nsmul_of_mem_compatibleConfigurations {T : Set ι}
    (hcls : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) {l : ι →₀ ℕ}
    (hl : l ∈ compatibleConfigurations r cls T A) : ∃ j : ℕ, A = j • A₀ := by
  rw [mem_compatibleConfigurations] at hl
  refine ⟨∑ c ∈ l.support, l c * m c, ?_⟩
  rw [← hl.2.2, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun c hc ↦ by rw [hcls c (hl.1 hc), smul_smul]

variable [DecidableEq ι]

/-- Two compatible families of tori on the ray of `A₀` with the same ray series have the same
counts in every class. -/
private theorem configurationCount_eq_of_rayTorusWeightSeries_eq {K K' : Finset ι}
    (hK : (K : Set ι).Pairwise r) (hK' : (K' : Set ι).Pairwise r)
    (hcls : ∀ c ∈ K ∪ K', cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    (hw : ∀ c ∈ K ∪ K', w c = torusWeight (σ c) (i c))
    (hseries : rayTorusWeightSeries K m σ i = rayTorusWeightSeries K' m σ i) (B : H) :
    configurationCount r cls w K B = configurationCount r cls w K' B := by
  have hclsK : ∀ c ∈ (K : Set ι), cls c = (m c : ℕ) • A₀ := fun c hc ↦
    hcls c (Finset.mem_union_left _ hc)
  have hclsK' : ∀ c ∈ (K' : Set ι), cls c = (m c : ℕ) • A₀ := fun c hc ↦
    hcls c (Finset.mem_union_right _ hc)
  by_cases hB : ∃ j : ℕ, B = j • A₀
  · obtain ⟨j, rfl⟩ := hB
    rw [configurationCount_eq_coeff_rayTorusWeightSeries hK hclsK hA₀
      (fun c hc ↦ hw c (Finset.mem_union_left _ hc)) subset_rfl fun c hc _ ↦ hc,
      configurationCount_eq_coeff_rayTorusWeightSeries hK' hclsK' hA₀
      (fun c hc ↦ hw c (Finset.mem_union_right _ hc)) subset_rfl fun c hc _ ↦ hc, hseries]
  · have h₀ {T : Set ι} (hT : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) :
        configurationCount r cls w T B = 0 := by
      rw [configurationCount_def]
      exact finsum_mem_eq_zero_of_forall_eq_zero fun l hl ↦
        (hB (exists_eq_nsmul_of_mem_compatibleConfigurations hT hl)).elim
    rw [h₀ hclsK, h₀ hclsK']

/-- **Replacing a cluster of tori.** Let `K` and `K'` be finite families of pairwise compatible
tori, disjoint from `s`, on the ray of a class `A₀` that is not torsion, the torus `c` having
class `m c • A₀` and the four-twist weights `w c = w_(σ c, i c)`. Suppose that a candidate
`d ∈ s` is compatible with a torus of `K` or of `K'` exactly when `d ∈ U`. If the candidates have
positive area `ω`, with finitely many of area at most `ω A`, and `K` and `K'` have the same ray
series `∏ f_(σ c, i c)(t ^ m c)`, then replacing `K` by `K'` does not change the count in
class `A`. -/
theorem configurationCount_union_eq_union_of_rayTorusWeightSeries_eq {K K' : Finset ι}
    (hKs : Disjoint (K : Set ι) s) (hK's : Disjoint (K' : Set ι) s) (hUs : U ⊆ s)
    (hU : ∀ k ∈ K ∪ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hK : (K : Set ι).Pairwise r) (hK' : (K' : Set ι).Pairwise r)
    (hcls : ∀ c ∈ K ∪ K', cls c = (m c : ℕ) • A₀) (hA₀ : Function.Injective fun n : ℕ ↦ n • A₀)
    (hw : ∀ c ∈ K ∪ K', w c = torusWeight (σ c) (i c))
    (hpos : ∀ c ∈ (↑(K ∪ K') : Set ι) ∪ s, 0 < ω (cls c))
    (hfin : {c ∈ (↑(K ∪ K') : Set ι) ∪ s | ω (cls c) ≤ ω A}.Finite)
    (hseries : rayTorusWeightSeries K m σ i = rayTorusWeightSeries K' m σ i) :
    configurationCount r cls w (↑K ∪ s) A = configurationCount r cls w (↑K' ∪ s) A := by
  have hsub : (↑K ∪ s : Set ι) ⊆ ↑(K ∪ K') ∪ s :=
    Set.union_subset_union_left _ (Finset.coe_subset.2 Finset.subset_union_left)
  have hsub' : (↑K' ∪ s : Set ι) ⊆ ↑(K ∪ K') ∪ s :=
    Set.union_subset_union_left _ (Finset.coe_subset.2 Finset.subset_union_right)
  exact configurationCount_union_eq_union hKs hK's hUs
    (fun k hk ↦ hU k (Finset.mem_union_left _ hk)) (fun k hk ↦ hU k (Finset.mem_union_right _ hk))
    (fun c hc ↦ hpos c (hsub hc)) (fun c hc ↦ hpos c (hsub' hc))
    (hfin.subset fun c hc ↦ ⟨hsub hc.1, hc.2⟩) (hfin.subset fun c hc ↦ ⟨hsub' hc.1, hc.2⟩)
    fun B _ ↦ configurationCount_eq_of_rayTorusWeightSeries_eq hK hK' hcls hA₀ hw hseries B

/-- A class of positive area is not torsion. -/
private theorem injective_nsmul_of_area_pos {B : H} (hB : 0 < ω B) :
    Function.Injective fun n : ℕ ↦ n • B := fun n n' h ↦ by
  have h' := congrArg ω h
  simp only [map_nsmul, nsmul_eq_mul] at h'
  exact_mod_cast mul_right_cancel₀ hB.ne' h'

omit [DecidableEq ι] in
/-- **Birth and death of tori.** Let `c` and `d` be two compatible tori outside `s` of the same
class, with the same compatibility with the candidates of `s`, with the same index and opposite
determinant signs: `w c = w_(σ, j)` and `w d = w_(!σ, j)`. If the candidates have positive area
`ω`, with finitely many of area at most `ω A`, then adding `c` and `d` to `s` does not change the
count in class `A`. -/
theorem configurationCount_insert_insert_torusWeight_not {c d : ι} (hcd : c ≠ d) (hc : c ∉ s)
    (hd : d ∉ s) (hr : r c d ∧ r d c) (hcls : cls d = cls c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 4}
    (hwc : w c = torusWeight σ₀ j) (hwd : w d = torusWeight (!σ₀) j)
    (hpos : ∀ e ∈ insert c (insert d s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert d s) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c (insert d s)) A = configurationCount r cls w s A := by
  classical
  have hK : (↑(insert c (insert d ∅) : Finset ι) : Set ι) ∪ s = insert c (insert d s) := by
    simp [Set.insert_union]
  have hKK : (↑(insert c (insert d ∅) ∪ ∅ : Finset ι) : Set ι) ∪ s = insert c (insert d s) := by
    rw [Finset.union_empty, hK]
  have hmem {e : ι} (he : e ∈ (insert c (insert d ∅) ∪ ∅ : Finset ι)) : e = c ∨ e = d := by
    simpa using he
  rw [← hK]
  conv_rhs => rw [← Set.empty_union s, ← Finset.coe_empty]
  refine configurationCount_union_eq_union_of_rayTorusWeightSeries_eq (m := fun _ ↦ 1)
    (σ := fun e ↦ if e = c then σ₀ else !σ₀) (i := fun _ ↦ j) (A₀ := cls c)
    (U := {e ∈ s | r c e ∧ r e c}) ?_ (by simp) (Set.sep_subset _ _) (fun k hk e he ↦ ?_) ?_
    (by simp) (fun e he ↦ ?_) (injective_nsmul_of_area_pos (hpos c (Set.mem_insert c _)))
    (fun e he ↦ ?_) (hKK ▸ hpos) (hKK ▸ hfin) ?_
  · exact Set.disjoint_left.2 fun e he hes ↦ by
      rcases hmem (Finset.mem_union_left _ he) with rfl | rfl
      exacts [hc hes, hd hes]
  · rw [Set.mem_sep_iff]
    rcases hmem hk with rfl | rfl
    · exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · exact ⟨fun h ↦ ⟨he, (hcomp e he).1 h⟩, fun h ↦ (hcomp e he).2 h.2⟩
  · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_empty, LawfulSingleton.insert_empty_eq]
    exact Set.pairwise_pair.2 fun _ ↦ hr
  · rcases hmem he with rfl | rfl
    · simp
    · simp [hcls]
  · rcases hmem he with rfl | rfl
    · simp [hwc]
    · simp [hwd, Ne.symm hcd]
  · exact rayTorusWeightSeries_insert_insert (c := c) (d := d) (s := ∅) (by simp)
      (Finset.notMem_empty d) rfl (by simp [Ne.symm hcd]) rfl

/-- The common bookkeeping of the two period-doubling statements: replacing the torus `c` by the
compatible tori `c'` and `d`, all with the same compatibility with `s`, where `c'` has the class of
`c` and `d` twice that class, and the ray series of `{c}` and `{c', d}` agree. -/
private theorem configurationCount_insert_eq_insert_insert_of_rayTorusWeightSeries_eq
    {c c' d : ι} (hcc' : c ≠ c') (hcd : c ≠ d) (hc'd : c' ≠ d) (hc : c ∉ s) (hc' : c' ∉ s)
    (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c) (hclsd : cls d = 2 • cls c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c)
    (hm : ∀ e, m e = if e = d then 2 else 1)
    (hw : ∀ e ∈ ({c, c', d} : Set ι), w e = torusWeight (σ e) (i e))
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite)
    (hseries : rayTorusWeightSeries {c} m σ i = rayTorusWeightSeries {c', d} m σ i) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A := by
  have hK : (↑({c} : Finset ι) : Set ι) ∪ s = insert c s := by simp
  have hK' : (↑({c', d} : Finset ι) : Set ι) ∪ s = insert c' (insert d s) := by
    simp [Set.insert_union]
  have hKK : (↑({c} ∪ {c', d} : Finset ι) : Set ι) ∪ s = insert c (insert c' (insert d s)) := by
    ext e
    simp only [Finset.coe_union, Finset.coe_singleton, Finset.coe_insert, Set.mem_union,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hmem {e : ι} (he : e ∈ ({c} ∪ {c', d} : Finset ι)) : e = c ∨ e = c' ∨ e = d := by
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert] at he
    tauto
  rw [← hK, ← hK']
  refine configurationCount_union_eq_union_of_rayTorusWeightSeries_eq (A₀ := cls c)
    (U := {e ∈ s | r c e ∧ r e c}) (by simpa using hc) (by simp [hc', hd]) (Set.sep_subset _ _)
    (fun k hk e he ↦ ?_) (by simp) ?_ (fun e he ↦ ?_)
    (injective_nsmul_of_area_pos (hpos c (Set.mem_insert c _))) (fun e he ↦ ?_) (hKK ▸ hpos)
    (hKK ▸ hfin) hseries
  · rw [Set.mem_sep_iff]
    rcases hmem hk with rfl | rfl | rfl
    · exact ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩
    · exact ⟨fun h ↦ ⟨he, (hcomp' e he).1 h⟩, fun h ↦ (hcomp' e he).2 h.2⟩
    · exact ⟨fun h ↦ ⟨he, (hcompd e he).1 h⟩, fun h ↦ (hcompd e he).2 h.2⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton]
    exact Set.pairwise_pair.2 fun _ ↦ hr
  · rcases hmem he with rfl | rfl | rfl
    · simp [hm, hcd]
    · simp [hm, hc'd, hcls']
    · simp [hm, hclsd]
  · rcases hmem he with rfl | rfl | rfl
    exacts [hw _ (Or.inl rfl), hw _ (Or.inr (Or.inl rfl)), hw _ (Or.inr (Or.inr rfl))]

omit [DecidableEq ι] in
/-- **Period doubling.** Let `c` be a torus outside `s` of label `(σ, j)`, `j ∈ {0, 1, 2}`, and let
`c'` and `d` be compatible tori outside `s`: `c'` of the class of `c` and label `(σ, j + 1)`, and
`d` of twice that class and label `(σ, j % 2)`, all three with the same compatibility with the
candidates of `s`. If the candidates have positive area `ω`, with finitely many of area at most
`ω A`, then replacing `c` by `c'` and `d` does not change the count in class `A`. -/
theorem configurationCount_insert_eq_insert_insert_torusWeight_castSucc {c c' d : ι}
    (hcc' : c ≠ c') (hcd : c ≠ d) (hc'd : c' ≠ d) (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s)
    (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c) (hclsd : cls d = 2 • cls c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.castSucc) (hwc' : w c' = torusWeight σ₀ j.succ)
    (hwd : w d = torusWeight σ₀ (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A := by
  classical
  set m : ι → ℕ+ := fun e ↦ if e = d then 2 else 1 with hm
  set i : ι → Fin 4 := fun e ↦ if e = c then j.castSucc else if e = c' then j.succ else
    (j % 2).castSucc with hi
  refine configurationCount_insert_eq_insert_insert_of_rayTorusWeightSeries_eq (σ := fun _ ↦ σ₀)
    (m := m) (i := i) hcc' hcd hc'd hc hc' hd hr hcls' hclsd hcomp' hcompd (fun _ ↦ rfl)
    (fun e he ↦ ?_) hpos hfin ?_
  · rcases he with rfl | rfl | rfl
    · simp [hi, hwc]
    · simp [hi, hwc', Ne.symm hcc']
    · simp [hi, hwd, Ne.symm hcd, Ne.symm hc'd]
  · have hd' : d ∉ ({c'} : Finset ι) := by simp [hc'd.symm]
    rw [show ({c', d} : Finset ι) = insert d {c'} from Finset.pair_comm c' d,
      rayTorusWeightSeries_insert_eq_update_castSucc (j := j) (Finset.mem_singleton_self c') hd'
        (by simp [hm, hc'd]) rfl (by simp [hi, Ne.symm hcc'])
        (by simp [hi, Ne.symm hcd, Ne.symm hc'd]),
      rayTorusWeightSeries_def, rayTorusWeightSeries_def, Finset.prod_singleton,
      Finset.prod_singleton, Function.update_self, show m c' = m c by simp [hm, hc'd, hcd]]
    simp [hi]

omit [DecidableEq ι] in
/-- **Period doubling**, in the other direction. Let `c` be a torus outside `s` of label
`(σ, j + 1)`, `j ∈ {0, 1, 2}`, and let `c'` and `d` be compatible tori outside `s`: `c'` of the
class of `c` and label `(σ, j)`, and `d` of twice that class and label `(!σ, j % 2)`, all three
with the same compatibility with the candidates of `s`. If the candidates have positive area `ω`,
with finitely many of area at most `ω A`, then replacing `c` by `c'` and `d` does not change the
count in class `A`. -/
theorem configurationCount_insert_eq_insert_insert_torusWeight_succ {c c' d : ι}
    (hcc' : c ≠ c') (hcd : c ≠ d) (hc'd : c' ≠ d) (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s)
    (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c) (hclsd : cls d = 2 • cls c)
    (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.succ) (hwc' : w c' = torusWeight σ₀ j.castSucc)
    (hwd : w d = torusWeight (!σ₀) (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A := by
  classical
  set m : ι → ℕ+ := fun e ↦ if e = d then 2 else 1 with hm
  set σ : ι → Bool := fun e ↦ if e = d then !σ₀ else σ₀ with hσ
  set i : ι → Fin 4 := fun e ↦ if e = c then j.succ else if e = c' then j.castSucc else
    (j % 2).castSucc with hi
  refine configurationCount_insert_eq_insert_insert_of_rayTorusWeightSeries_eq (σ := σ)
    (m := m) (i := i) hcc' hcd hc'd hc hc' hd hr hcls' hclsd hcomp' hcompd (fun _ ↦ rfl)
    (fun e he ↦ ?_) hpos hfin ?_
  · rcases he with rfl | rfl | rfl
    · simp [hi, hσ, hwc, hcd]
    · simp [hi, hσ, hwc', Ne.symm hcc', hc'd]
    · simp [hi, hσ, hwd, Ne.symm hcd, Ne.symm hc'd]
  · have hd' : d ∉ ({c'} : Finset ι) := by simp [hc'd.symm]
    rw [show ({c', d} : Finset ι) = insert d {c'} from Finset.pair_comm c' d,
      rayTorusWeightSeries_insert_eq_update_succ (j := j) (Finset.mem_singleton_self c') hd'
        (by simp [hm, hc'd]) (by simp [hσ, hc'd]) (by simp [hi, Ne.symm hcc'])
        (by simp [hi, Ne.symm hcd, Ne.symm hc'd]),
      rayTorusWeightSeries_def, rayTorusWeightSeries_def, Finset.prod_singleton,
      Finset.prod_singleton, Function.update_self, show m c' = m c by simp [hm, hc'd, hcd],
      show σ c' = σ c by simp [hσ, hc'd, hcd]]
    simp [hi]

end Ray

end TauCeti

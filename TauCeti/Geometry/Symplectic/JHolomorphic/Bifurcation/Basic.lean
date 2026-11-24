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
of `U` in class `A - B`. Hence, when the configurations of `K ∪ s` in class `A` are finite in
number (`TauCeti.configurationCount_union`),

`N_{K ∪ s}(A) = N_s(A) + ∑ᶠ B ≠ 0, N_K(B) N_U(A - B)`,

so the count in class `A` depends on the cluster only through its *local counts* `N_K(B)` in the
classes `B ≠ 0` for which `U` has a configuration in class `A - B`; for candidates of nonnegative
area `ω`, these classes have `ω B ≤ ω A`. Replacing `K` by a cluster `K'` with the same
compatibility with `s` and the same local counts in these classes does not change the count in
class `A` (`TauCeti.configurationCount_union_eq_union`). The local counts are then computed for
the three bifurcations:

* **Ordinary birth and death.** Two incompatible candidates `c` and `d` of the same class, with
  the same compatibility with the other candidates and opposite weights `w d k = -w c k`, have
  vanishing local counts (`TauCeti.configurationCount_pair_eq_zero`). Adding them does not change
  the count (`TauCeti.configurationCount_insert_insert_of_weight_eq_neg`).
* **Tori on a ray.** For candidates of positive area `ω` with finitely many of area at most
  `ω A`, the local counts of a finite pairwise compatible cluster of tori on the ray of a class
  `A₀` are the coefficients of its ray series `∏ f_(σ c, i c)(t ^ m c)`
  (`TauCeti.rayTorusWeightSeries`). Two such clusters whose ray series agree up to area `ω A`
  give the same count in class `A`
  (`TauCeti.configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq`). In particular,
  adding two compatible tori of the same class and index with opposite determinant signs does not
  change the count (`TauCeti.configurationCount_insert_insert_of_eq_torusWeight_not`), and neither
  does period doubling: a torus of label `(σ, j)` contributes as much as a torus of label
  `(σ, j + 1)` in the same class together with a torus of label `(σ, j % 2)` in twice its class
  (`TauCeti.configurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc`), or with a
  torus of label `(!σ, j % 2)` when the first torus has label `(σ, j + 1)` and is replaced by one
  of label `(σ, j)` (`TauCeti.configurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ`).
  When the double cover of a torus has area larger than `ω A`, its index may change with no other
  torus appearing (`TauCeti.configurationCount_insert_eq_insert_of_area_lt_two_mul`).

The ray-series identities behind the torus statements are
`TauCeti.torusWeightSeries_mul_not`, `TauCeti.torusWeightSeries_castSucc` and
`TauCeti.torusWeightSeries_succ`. Unlike the ray-series statements of
`TauCeti.Geometry.Symplectic.JHolomorphic.TorusWeight`, the invariance here holds for the count
over a set of candidates whose members need not be pairwise compatible and need not lie on one
ray.

The candidates, their classes, weights and compatibility, and the description of a bifurcation
as the replacement of one cluster by another, are inputs here; constructing the one-dimensional
bifurcation models of a generic path of almost complex structures is separate.

## Main results

* `TauCeti.configurationCount_union`: the cluster expansion of the count.
* `TauCeti.configurationCount_union_eq_union`: replacing a cluster by one with the same local
  counts.
* `TauCeti.configurationCount_insert_insert_of_weight_eq_neg`: ordinary birth and death.
* `TauCeti.configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq`: replacing a
  cluster of tori by one with the same ray series up to the area cutoff.
* `TauCeti.configurationCount_insert_insert_of_eq_torusWeight_not`: birth and death of tori.
* `TauCeti.configurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc`,
  `TauCeti.configurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ`: period doubling.
* `TauCeti.configurationCount_insert_eq_insert_of_area_lt_two_mul`: changing the index of a torus
  whose double cover lies beyond the area cutoff.

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

/-- The configurations of `K ∪ s` avoiding the cluster `K` are the configurations of `s`. -/
private theorem mem_compatibleConfigurations_union_and_filter_eq_zero_iff
    [DecidablePred (· ∈ K)] (hKs : Disjoint K s) {l : ι →₀ ℕ} :
    l ∈ compatibleConfigurations r cls (K ∪ s) A ∧ l.filter (· ∈ K) = 0 ↔
      l ∈ compatibleConfigurations r cls s A := by
  rw [Finsupp.filter_eq_zero_iff, mem_compatibleConfigurations, mem_compatibleConfigurations]
  refine ⟨fun ⟨hl, hK⟩ ↦ ⟨fun c hc ↦ (hl.1 hc).resolve_left fun hcK ↦
    Finsupp.mem_support_iff.1 hc (hK c hcK), hl.2⟩, fun hl ↦
    ⟨⟨hl.1.trans Set.subset_union_right, hl.2⟩, fun c hcK ↦
      Finsupp.notMem_support_iff.1 fun hc ↦ Set.disjoint_left.1 hKs hcK (hl.1 hc)⟩⟩

/-- If the configurations of `T` in class `A` are finite in number, then the part in `K` of such a
configuration, when nonempty, has nonzero class: a nonempty part of class zero could be added to
the configuration any number of times. -/
private theorem linearCombination_filter_ne_zero_of_finite [DecidablePred (· ∈ K)] {T : Set ι}
    (hfin : (compatibleConfigurations r cls T A).Finite) {l : ι →₀ ℕ}
    (hl : l ∈ compatibleConfigurations r cls T A) (hlK : l.filter (· ∈ K) ≠ 0) :
    Finsupp.linearCombination ℕ cls (l.filter (· ∈ K)) ≠ 0 := by
  intro h
  rw [mem_compatibleConfigurations] at hl
  have hsupp (j : ℕ) : ↑(l + j • l.filter (· ∈ K)).support ⊆ (↑l.support : Set ι) :=
    fun d hd ↦ by
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.coe_add, Finsupp.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finsupp.filter_apply] at hd ⊢
      intro hd'
      simp [hd'] at hd
  refine hfin.not_infinite (Set.infinite_of_injective_forall_mem
    (f := fun j : ℕ ↦ l + j • l.filter (· ∈ K)) (fun j j' hj ↦ ?_) fun j ↦ ?_)
  · obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hlK
    have := DFunLike.congr_fun (add_left_cancel hj) k
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at this
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hk)) this
  · rw [mem_compatibleConfigurations]
    exact ⟨(hsupp j).trans hl.1, hl.2.1.mono (hsupp j), by
      rw [map_add, map_nsmul, h, smul_zero, add_zero, hl.2.2]⟩

/-- If the configurations of `K ∪ s` in class `A` are finite in number, then so are those of the
cluster `K` in every class `B` for which the candidates `U` compatible with `K` have a
configuration in class `A - B`. -/
theorem finite_compatibleConfigurations_of_union (hKs : Disjoint K s) (hUs : U ⊆ s)
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hfin : (compatibleConfigurations r cls (K ∪ s) A).Finite)
    (hn : (compatibleConfigurations r cls U (A - B)).Nonempty) :
    (compatibleConfigurations r cls K B).Finite := by
  classical
  obtain ⟨n, hn⟩ := hn
  exact (hfin.preimage (add_left_injective n).injOn).subset fun m hm ↦
    (add_mem_compatibleConfigurations_union hKs hUs hU hm hn).1

/-- If every member `k` of a cluster, given by a predicate `p`, has the same compatibility with the
candidates of `s` as `c`, then a candidate of `s` is compatible with a member of the cluster exactly
when it lies in the set of candidates of `s` compatible with `c`. -/
private theorem compatible_iff_mem_sep {p : ι → Prop} {c : ι}
    (hcomp : ∀ k, p k → ∀ e ∈ s, r k e ∧ r e k ↔ r c e ∧ r e c) :
    ∀ k, p k → ∀ e ∈ s, r k e ∧ r e k ↔ e ∈ {e ∈ s | r c e ∧ r e c} :=
  fun k hk e he ↦ (hcomp k hk e he).trans ⟨fun h ↦ ⟨he, h⟩, fun h ↦ h.2⟩

variable [CommSemiring R] {w : ι → ℕ → R}

/-- **Cluster expansion of the count.** Let `K` be a cluster of candidates, disjoint from `s`,
such that a candidate `d ∈ s` is compatible with a member of `K` exactly when `d ∈ U`. If the
configurations of `K ∪ s` in class `A` are finite in number, then the count in class `A` over
`K ∪ s` is the count over `s` plus the contributions of the nonempty configurations of `K`: the
local count `N_K(B)` in each class `B ≠ 0`, times the count over `U` in the complementary class
`A - B`. -/
theorem configurationCount_union (hKs : Disjoint K s) (hUs : U ⊆ s)
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hfin : (compatibleConfigurations r cls (K ∪ s) A).Finite) :
    configurationCount r cls w (K ∪ s) A =
      configurationCount r cls w s A +
        ∑ᶠ B ∈ {B : H | B ≠ 0},
          configurationCount r cls w K B * configurationCount r cls w U (A - B) := by
  classical
  set F := hfin.toFinset
  -- The class of the part of a configuration lying in `K`.
  set κ : (ι →₀ ℕ) → H := fun l ↦ Finsupp.linearCombination ℕ cls (l.filter (· ∈ K))
  -- The configurations of `K` and of `U` occurring in a splitting are finite in number.
  have hsplit {l : ι →₀ ℕ} (hl : l ∈ F) (hlK : l.filter (· ∈ K) ≠ 0) :
      κ l ≠ 0 ∧ (compatibleConfigurations r cls K (κ l)).Finite ∧
        (compatibleConfigurations r cls U (A - κ l)).Finite := by
    rw [Set.Finite.mem_toFinset] at hl
    obtain ⟨hm, hn⟩ := filter_mem_compatibleConfigurations hU hl hlK
    exact ⟨linearCombination_filter_ne_zero_of_finite hfin hl hlK,
      finite_compatibleConfigurations_of_union hKs hUs hU hfin ⟨_, hn⟩,
      (hfin.preimage (add_right_injective _).injOn).subset fun n hn' ↦
        (add_mem_compatibleConfigurations_union hKs hUs hU hm hn').1⟩
  rw [configurationCount_eq_sum hfin,
    ← Finset.sum_filter_add_sum_filter_not F fun l ↦ l.filter (· ∈ K) = 0]
  congr 1
  · -- The configurations avoiding `K` are the configurations of `s`.
    have hfins : (compatibleConfigurations r cls s A).Finite :=
      hfin.subset (compatibleConfigurations_mono Set.subset_union_right)
    rw [configurationCount_eq_sum hfins]
    refine Finset.sum_congr (Finset.ext fun l ↦ ?_) fun _ _ ↦ rfl
    rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact mem_compatibleConfigurations_union_and_filter_eq_zero_iff hKs
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
of `K'`, exactly when `d ∈ U`. Suppose that the configurations of `K ∪ s` and of `K' ∪ s` in
class `A` are finite in number. If `K` and `K'` have the same local counts `N_K(B) = N_K'(B)` in
every class `B ≠ 0` for which `U` has a configuration in class `A - B`, then replacing `K` by `K'`
does not change the count in class `A`. When the candidates of `U` have nonnegative area `ω`, only
the classes `B` with `ω B ≤ ω A` matter. -/
theorem configurationCount_union_eq_union (hKs : Disjoint K s) (hK's : Disjoint K' s)
    (hUs : U ⊆ s) (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hU' : ∀ k ∈ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hfin : (compatibleConfigurations r cls (K ∪ s) A).Finite)
    (hfin' : (compatibleConfigurations r cls (K' ∪ s) A).Finite)
    (hK : ∀ B ≠ 0, (compatibleConfigurations r cls U (A - B)).Nonempty →
      configurationCount r cls w K B = configurationCount r cls w K' B) :
    configurationCount r cls w (K ∪ s) A = configurationCount r cls w (K' ∪ s) A := by
  rw [configurationCount_union hKs hUs hU hfin, configurationCount_union hK's hUs hU' hfin']
  refine congrArg _ (finsum_mem_congr rfl fun B hB ↦ ?_)
  by_cases hn : (compatibleConfigurations r cls U (A - B)).Nonempty
  · rw [hK B hB hn]
  · rw [configurationCount_def (s := U), Set.not_nonempty_iff_eq_empty.1 hn, finsum_mem_empty,
      mul_zero, mul_zero]

end Cluster

/-! ### Ordinary birth and death -/

section BirthDeath

variable [AddCommGroup H] [CommRing R] {r : ι → ι → Prop} {cls : ι → H} {w : ι → ℕ → R}
  {s : Set ι} {A B : H} {c d : ι}

/-- **Local count of a birth or death pair.** Two distinct incompatible candidates of the same
class with opposite weights `w d k = -w c k` have vanishing local count in every nonzero class `B`
in which they have finitely many configurations. -/
theorem configurationCount_pair_eq_zero (hcd : c ≠ d) (hr : ¬(r c d ∧ r d c))
    (hcls : cls d = cls c) (hw : ∀ k ≠ 0, w d k = -w c k)
    (hfin : (compatibleConfigurations r cls {c, d} B).Finite) (hB : B ≠ 0) :
    configurationCount r cls w {c, d} B = 0 := by
  classical
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
    simp only [Finsupp.equivMapDomain_single, Finsupp.prod, Finsupp.support_single _ hk,
      Finset.prod_singleton, Finsupp.single_eq_same]
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
`w d k = -w c k` for `k ≠ 0`. If the configurations of `s ∪ {c, d}` in class `A` are finite in
number, then adding `c` and `d` to `s` does not change the count in class `A`. Two distinct
embedded curves in the same class of positive square intersect, so they are incompatible. -/
theorem configurationCount_insert_insert_of_weight_eq_neg (hcd : c ≠ d) (hc : c ∉ s)
    (hd : d ∉ s) (hr : ¬(r c d ∧ r d c)) (hcls : cls d = cls c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) (hw : ∀ k ≠ 0, w d k = -w c k)
    (hfin : (compatibleConfigurations r cls (insert c (insert d s)) A).Finite) :
    configurationCount r cls w (insert c (insert d s)) A = configurationCount r cls w s A := by
  classical
  have hunion : insert c (insert d s) = ({c, d} : Set ι) ∪ s := by
    rw [Set.insert_union, Set.singleton_union]
  have hKs : Disjoint ({c, d} : Set ι) s := by simp [hc, hd]
  have hU := compatible_iff_mem_sep (r := r) (s := s) (p := (· ∈ ({c, d} : Set ι))) (c := c) <| by
    rintro k (rfl | rfl) e he
    exacts [Iff.rfl, hcomp e he]
  have hsub : ∅ ∪ s ⊆ insert c (insert d s) := by
    rw [Set.empty_union]
    exact (Set.subset_insert d s).trans (Set.subset_insert c _)
  rw [hunion] at hfin
  rw [hunion, configurationCount_union_eq_union (K' := ∅) hKs (Set.empty_disjoint s)
    (Set.sep_subset _ _) hU (fun k hk ↦ hk.elim) hfin
    (hfin.subset (compatibleConfigurations_mono (hunion ▸ hsub))) fun B hB hn ↦ ?_,
    Set.empty_union]
  rw [configurationCount_pair_eq_zero hcd hr hcls hw
      (finite_compatibleConfigurations_of_union hKs (Set.sep_subset _ _) hU hfin hn) hB,
    configurationCount_empty, ite_eq_right_iff.2 fun h ↦ (hB h).elim]

end BirthDeath

/-! ### Tori on a ray -/

section Ray

variable [AddCommGroup H] {r : ι → ι → Prop} {cls : ι → H} {w : ι → ℕ → ℤ}
  {s U : Set ι} {A A₀ : H} {ω : H →+ ℝ} {m : ι → ℕ+} {σ : ι → Bool} {i : ι → Fin 4}

/-- **Replacing a cluster of tori.** Let `K` and `K'` be finite families of pairwise compatible
tori, disjoint from `s`, on the ray of a class `A₀`, the torus `c` having class `m c • A₀` and
the four-twist weights `w c = w_(σ c, i c)`. Suppose that a candidate `d ∈ s` is compatible with
a torus of `K`, or of `K'`, exactly when `d ∈ U`. If the candidates have positive area `ω`, with
finitely many of area at most `ω A`, and the ray series `∏ f_(σ c, i c)(t ^ m c)` of `K` and `K'`
have the same coefficients up to area `ω A`, then replacing `K` by `K'` does not change the count
in class `A`. -/
theorem configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq {K K' : Finset ι}
    (hKs : Disjoint (K : Set ι) s) (hK's : Disjoint (K' : Set ι) s) (hUs : U ⊆ s)
    (hU : ∀ k ∈ K, ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U) (hU' : ∀ k ∈ K', ∀ d ∈ s, r k d ∧ r d k ↔ d ∈ U)
    (hK : (K : Set ι).Pairwise r) (hK' : (K' : Set ι).Pairwise r)
    (hcls : ∀ c ∈ (↑K ∪ ↑K' : Set ι), cls c = (m c : ℕ) • A₀)
    (hw : ∀ c ∈ (↑K ∪ ↑K' : Set ι), w c = torusWeight (σ c) (i c))
    (hpos : ∀ c ∈ (↑K ∪ ↑K' : Set ι) ∪ s, 0 < ω (cls c))
    (hfin : {c ∈ (↑K ∪ ↑K' : Set ι) ∪ s | ω (cls c) ≤ ω A}.Finite)
    (hseries : ∀ j : ℕ, ω (j • A₀) ≤ ω A →
      coeff j (rayTorusWeightSeries K m σ i) = coeff j (rayTorusWeightSeries K' m σ i)) :
    configurationCount r cls w (↑K ∪ s) A = configurationCount r cls w (↑K' ∪ s) A := by
  have hsub : (↑K ∪ s : Set ι) ⊆ (↑K ∪ ↑K') ∪ s :=
    Set.union_subset_union_left _ Set.subset_union_left
  have hsub' : (↑K' ∪ s : Set ι) ⊆ (↑K ∪ ↑K') ∪ s :=
    Set.union_subset_union_left _ Set.subset_union_right
  refine configurationCount_union_eq_union hKs hK's hUs hU hU'
    (finite_compatibleConfigurations (fun c hc ↦ hpos c (hsub hc))
      (hfin.subset fun c hc ↦ ⟨hsub hc.1, hc.2⟩))
    (finite_compatibleConfigurations (fun c hc ↦ hpos c (hsub' hc))
      (hfin.subset fun c hc ↦ ⟨hsub' hc.1, hc.2⟩)) fun B _ ⟨n, hn⟩ ↦ ?_
  by_cases hB : ∃ j : ℕ, B = j • A₀
  · obtain ⟨j, rfl⟩ := hB
    rcases Set.eq_empty_or_nonempty (↑K ∪ ↑K' : Set ι) with h | ⟨c, hc⟩
    · rw [(Set.union_empty_iff.1 h).1, (Set.union_empty_iff.1 h).2]
    -- The class `A₀` has positive area, so it is not torsion.
    have hA₀ : 0 < ω A₀ := by
      have := hpos c (Or.inl hc)
      rw [hcls c hc, map_nsmul, nsmul_eq_mul] at this
      exact pos_of_mul_pos_right this (Nat.cast_nonneg _)
    have hinj : Function.Injective fun n : ℕ ↦ n • A₀ := .of_comp (f := ω) <| by
      simpa only [Function.comp_def, map_nsmul] using (nsmul_left_strictMono hA₀).injective
    -- The class `j • A₀` is at most `A` in area, as `U` has a configuration in class `A - j • A₀`.
    have hj : ω (j • A₀) ≤ ω A := by
      have := area_nonneg_of_mem_compatibleConfigurations
        (fun c hc ↦ (hpos c (Or.inr (hUs hc))).le) hn
      rw [map_sub] at this
      linarith
    rw [configurationCount_eq_coeff_rayTorusWeightSeries hK (fun c hc ↦ hcls c (Or.inl hc)) hinj
      (fun c hc ↦ hw c (Or.inl hc)) subset_rfl fun c hc _ ↦ hc,
      configurationCount_eq_coeff_rayTorusWeightSeries hK' (fun c hc ↦ hcls c (Or.inr hc)) hinj
      (fun c hc ↦ hw c (Or.inr hc)) subset_rfl fun c hc _ ↦ hc, hseries j hj]
  · -- Off the ray, neither cluster has a configuration.
    have h₀ {T : Set ι} (hT : ∀ c ∈ T, cls c = (m c : ℕ) • A₀) :
        configurationCount r cls w T B = 0 := by
      rw [configurationCount_def]
      refine finsum_mem_eq_zero_of_forall_eq_zero fun l hl ↦ ?_
      rw [mem_compatibleConfigurations] at hl
      exact (hB ⟨_, hl.2.2.symm.trans (linearCombination_eq_nsmul_of_support_subset hT hl.1)⟩).elim
    rw [h₀ fun c hc ↦ hcls c (Or.inl hc), h₀ fun c hc ↦ hcls c (Or.inr hc)]

/-- **Birth and death of tori.** Let `c` and `d` be two compatible tori outside `s` of the same
class, with the same compatibility with the candidates of `s`, with the same index and opposite
determinant signs: `w c = w_(σ, j)` and `w d = w_(!σ, j)`. If the candidates have positive area
`ω`, with finitely many of area at most `ω A`, then adding `c` and `d` to `s` does not change the
count in class `A`. -/
theorem configurationCount_insert_insert_of_eq_torusWeight_not {c d : ι} (hc : c ∉ s)
    (hd : d ∉ s) (hr : r c d ∧ r d c) (hcls : cls d = cls c)
    (hcomp : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 4}
    (hwc : w c = torusWeight σ₀ j) (hwd : w d = torusWeight (!σ₀) j)
    (hpos : ∀ e ∈ insert c (insert d s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert d s) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c (insert d s)) A = configurationCount r cls w s A := by
  classical
  -- The tori have opposite weights `±1` with multiplicity one, so they are distinct.
  have hcd : c ≠ d := by
    rintro rfl
    have := congrFun (hwc.symm.trans hwd) 1
    cases σ₀ <;> simp at this
  have hK : (↑(insert c (insert d ∅) : Finset ι) : Set ι) ∪ s = insert c (insert d s) := by
    simp [Set.insert_union]
  have hKK : (↑(insert c (insert d ∅) : Finset ι) ∪ ↑(∅ : Finset ι) : Set ι) ∪ s =
      insert c (insert d s) := by
    rw [Finset.coe_empty, Set.union_empty, hK]
  have hmem {e : ι} (he : e ∈ (↑(insert c (insert d ∅) : Finset ι) ∪ ↑(∅ : Finset ι) : Set ι)) :
      e = c ∨ e = d := by
    simpa using he
  rw [← hK]
  conv_rhs => rw [← Set.empty_union s, ← Finset.coe_empty]
  refine configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq (m := fun _ ↦ 1)
    (σ := fun e ↦ if e = c then σ₀ else !σ₀) (i := fun _ ↦ j) (A₀ := cls c)
    (U := {e ∈ s | r c e ∧ r e c}) (by simp [hc, hd]) (by simp) (Set.sep_subset _ _)
    (compatible_iff_mem_sep fun k hk e he ↦ ?_) (by simp) ?_ (by simp) (fun e he ↦ ?_)
    (fun e he ↦ ?_) (hKK ▸ hpos) (hKK ▸ hfin) fun _ _ ↦ ?_
  · rcases hmem (Or.inl hk) with rfl | rfl
    exacts [Iff.rfl, hcomp e he]
  · rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_empty, LawfulSingleton.insert_empty_eq]
    exact Set.pairwise_pair.2 fun _ ↦ hr
  · rcases hmem he with rfl | rfl
    · simp
    · simp [hcls]
  · rcases hmem he with rfl | rfl
    · simp [hwc]
    · simp [hwd, Ne.symm hcd]
  · rw [rayTorusWeightSeries_insert_insert (c := c) (d := d) (s := ∅) (by simp)
      (Finset.notMem_empty d) rfl (by simp [Ne.symm hcd]) rfl]

/-- **Replacing a torus by a pair.** Let `c` be a torus outside `s` of label `(σc, ic)`, and let
`c'` and `d` be compatible tori outside `s`, of labels `(σc', ic')` and `(σd, id)`, `c'` of the
class of `c` and `d` of twice that class, all three with the same compatibility with the
candidates of `s`. If the candidates have positive area `ω`, with finitely many of area at most
`ω A`, and the local series satisfy `f_(σc, ic)(t) = f_(σc', ic')(t) f_(σd, id)(t ^ 2)`, then
replacing `c` by `c'` and `d` does not change the count in class `A`. -/
private theorem configurationCount_insert_eq_insert_insert_of_torusWeightSeries_eq {c c' d : ι}
    (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c)
    (hclsd : cls d = 2 • cls c) (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σc σc' σd : Bool} {ic ic' id : Fin 4}
    (hwc : w c = torusWeight σc ic) (hwc' : w c' = torusWeight σc' ic')
    (hwd : w d = torusWeight σd id)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite)
    (hseries : torusWeightSeries σc ic =
      torusWeightSeries σc' ic' * expand 2 two_ne_zero (torusWeightSeries σd id)) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A := by
  classical
  -- The three tori are distinct: `d` has twice the positive area of `c` and `c'`, and `c'` has a
  -- different weight series from `c`, since the factor `f_(σd, id)(t ^ 2)` is not `1`.
  have hcd : c ≠ d := by
    rintro rfl
    have := hpos c (Set.mem_insert c _)
    rw [two_nsmul, left_eq_add] at hclsd
    rw [hclsd, map_zero] at this
    exact this.false
  have hc'd : c' ≠ d := by
    rintro rfl
    have := hpos c (Set.mem_insert c _)
    rw [hcls', two_nsmul, left_eq_add] at hclsd
    rw [hclsd, map_zero] at this
    exact this.false
  have hcc' : c ≠ c' := by
    rintro rfl
    have hf : torusWeightSeries σc ic = torusWeightSeries σc' ic' :=
      PowerSeries.ext fun n ↦ by simpa using congrFun (hwc.symm.trans hwc') n
    rw [hf] at hseries
    have h1 := congrArg (coeff 2) ((isUnit_torusWeightSeries σc' ic').mul_left_cancel
      (hseries.symm.trans (mul_one _).symm))
    rw [coeff_expand, coeff_one] at h1
    cases σd <;> simp at h1
  set m : ι → ℕ+ := fun e ↦ if e = d then 2 else 1 with hm
  set σ : ι → Bool := fun e ↦ if e = c then σc else if e = c' then σc' else σd with hσ
  set i : ι → Fin 4 := fun e ↦ if e = c then ic else if e = c' then ic' else id with hi
  have hK : (↑({c} : Finset ι) : Set ι) ∪ s = insert c s := by simp
  have hK' : (↑({c', d} : Finset ι) : Set ι) ∪ s = insert c' (insert d s) := by
    simp [Set.insert_union]
  have hKK : (↑({c} : Finset ι) ∪ ↑({c', d} : Finset ι) : Set ι) ∪ s =
      insert c (insert c' (insert d s)) := by
    ext e
    simp only [Finset.coe_singleton, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hmem {e : ι} (he : e ∈ (↑({c} : Finset ι) ∪ ↑({c', d} : Finset ι) : Set ι)) :
      e = c ∨ e = c' ∨ e = d := by
    simp only [Finset.coe_singleton, Finset.coe_insert, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at he
    tauto
  rw [← hK, ← hK']
  refine configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq (A₀ := cls c)
    (m := m) (σ := σ) (i := i) (U := {e ∈ s | r c e ∧ r e c}) (by simpa using hc)
    (by simp [hc', hd]) (Set.sep_subset _ _)
    (compatible_iff_mem_sep fun k hk e _ ↦ by rw [Finset.mem_singleton.1 hk])
    (compatible_iff_mem_sep fun k hk e he ↦ ?_) (by simp) ?_ (fun e he ↦ ?_) (fun e he ↦ ?_)
    (hKK ▸ hpos) (hKK ▸ hfin) fun j _ ↦ ?_
  · rcases Finset.mem_insert.1 hk with rfl | hk
    exacts [hcomp' e he, Finset.mem_singleton.1 hk ▸ hcompd e he]
  · simp only [Finset.coe_insert, Finset.coe_singleton]
    exact Set.pairwise_pair.2 fun _ ↦ hr
  · rcases hmem he with rfl | rfl | rfl
    · simp [hm, hcd]
    · simp [hm, hc'd, hcls']
    · simp [hm, hclsd]
  · rcases hmem he with rfl | rfl | rfl
    · simp [hσ, hi, hwc]
    · simp [hσ, hi, hwc', Ne.symm hcc']
    · simp [hσ, hi, hwd, Ne.symm hcd, Ne.symm hc'd]
  · rw [rayTorusWeightSeries_def, rayTorusWeightSeries_def, Finset.prod_singleton,
      Finset.prod_pair hc'd]
    simp [hm, hσ, hi, hcd, hc'd, Ne.symm hcc', Ne.symm hcd, Ne.symm hc'd, hseries]

/-- **Period doubling.** Let `c` be a torus outside `s` of label `(σ, j)`, `j ∈ {0, 1, 2}`, and let
`c'` and `d` be compatible tori outside `s`: `c'` of the class of `c` and label `(σ, j + 1)`, and
`d` of twice that class and label `(σ, j % 2)`, all three with the same compatibility with the
candidates of `s`. If the candidates have positive area `ω`, with finitely many of area at most
`ω A`, then replacing `c` by `c'` and `d` does not change the count in class `A`. -/
theorem configurationCount_insert_eq_insert_insert_of_eq_torusWeight_castSucc {c c' d : ι}
    (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c)
    (hclsd : cls d = 2 • cls c) (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.castSucc) (hwc' : w c' = torusWeight σ₀ j.succ)
    (hwd : w d = torusWeight σ₀ (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A :=
  configurationCount_insert_eq_insert_insert_of_torusWeightSeries_eq hc hc' hd hr hcls' hclsd
    hcomp' hcompd hwc hwc' hwd hpos hfin (torusWeightSeries_castSucc σ₀ j)

/-- **Period doubling**, in the other direction. Let `c` be a torus outside `s` of label
`(σ, j + 1)`, `j ∈ {0, 1, 2}`, and let `c'` and `d` be compatible tori outside `s`: `c'` of the
class of `c` and label `(σ, j)`, and `d` of twice that class and label `(!σ, j % 2)`, all three
with the same compatibility with the candidates of `s`. If the candidates have positive area `ω`,
with finitely many of area at most `ω A`, then replacing `c` by `c'` and `d` does not change the
count in class `A`. -/
theorem configurationCount_insert_eq_insert_insert_of_eq_torusWeight_succ {c c' d : ι}
    (hc : c ∉ s) (hc' : c' ∉ s) (hd : d ∉ s) (hr : r c' d ∧ r d c') (hcls' : cls c' = cls c)
    (hclsd : cls d = 2 • cls c) (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    (hcompd : ∀ e ∈ s, r d e ∧ r e d ↔ r c e ∧ r e c) {σ₀ : Bool} {j : Fin 3}
    (hwc : w c = torusWeight σ₀ j.succ) (hwc' : w c' = torusWeight σ₀ j.castSucc)
    (hwd : w d = torusWeight (!σ₀) (j % 2).castSucc)
    (hpos : ∀ e ∈ insert c (insert c' (insert d s)), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' (insert d s)) | ω (cls e) ≤ ω A}.Finite) :
    configurationCount r cls w (insert c s) A =
      configurationCount r cls w (insert c' (insert d s)) A :=
  configurationCount_insert_eq_insert_insert_of_torusWeightSeries_eq hc hc' hd hr hcls' hclsd
    hcomp' hcompd hwc hwc' hwd hpos hfin (torusWeightSeries_succ σ₀ j)

/-- **Changing the index of a torus below its double cover.** Let `c` and `c'` be tori outside
`s` of the same class and the same determinant sign `σ`, with any indices `j` and `j'`, and with
the same compatibility with the candidates of `s`. If the candidates have positive area `ω`, with
finitely many of area at most `ω A`, and `ω A` is less than the area of the double cover of `c`,
then replacing `c` by `c'` does not change the count in class `A`: only the weights
`w_(σ, j)(1) = w_(σ, j')(1) = ±1` of the tori taken once contribute. -/
theorem configurationCount_insert_eq_insert_of_area_lt_two_mul {c c' : ι} (hc : c ∉ s)
    (hc' : c' ∉ s) (hcls' : cls c' = cls c) (hcomp' : ∀ e ∈ s, r c' e ∧ r e c' ↔ r c e ∧ r e c)
    {σ₀ : Bool} {j j' : Fin 4} (hwc : w c = torusWeight σ₀ j) (hwc' : w c' = torusWeight σ₀ j')
    (hpos : ∀ e ∈ insert c (insert c' s), 0 < ω (cls e))
    (hfin : {e ∈ insert c (insert c' s) | ω (cls e) ≤ ω A}.Finite) (hA : ω A < 2 * ω (cls c)) :
    configurationCount r cls w (insert c s) A = configurationCount r cls w (insert c' s) A := by
  classical
  rcases eq_or_ne c c' with rfl | hcc'
  · rfl
  have hK (e : ι) : (↑({e} : Finset ι) : Set ι) ∪ s = insert e s := by simp
  have hKK : (↑({c} : Finset ι) ∪ ↑({c'} : Finset ι) : Set ι) ∪ s = insert c (insert c' s) := by
    ext e
    simp only [Finset.coe_singleton, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hmem {e : ι} (he : e ∈ (↑({c} : Finset ι) ∪ ↑({c'} : Finset ι) : Set ι)) :
      e = c ∨ e = c' := by
    simpa only [Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff] using he
  rw [← hK, ← hK]
  refine configurationCount_union_eq_union_of_coeff_rayTorusWeightSeries_eq (A₀ := cls c)
    (m := fun _ ↦ 1) (σ := fun _ ↦ σ₀) (i := fun e ↦ if e = c then j else j')
    (U := {e ∈ s | r c e ∧ r e c}) (by simpa using hc) (by simpa using hc') (Set.sep_subset _ _)
    (compatible_iff_mem_sep fun k hk e _ ↦ by rw [Finset.mem_singleton.1 hk])
    (compatible_iff_mem_sep fun k hk e he ↦ Finset.mem_singleton.1 hk ▸ hcomp' e he) (by simp)
    (by simp) (fun e he ↦ ?_) (fun e he ↦ ?_) (hKK ▸ hpos) (hKK ▸ hfin) fun n hn ↦ ?_
  · rcases hmem he with rfl | rfl
    · simp
    · simp [hcls']
  · rcases hmem he with rfl | rfl
    · simp [hwc]
    · simp [hwc', Ne.symm hcc']
  · -- Only the coefficients of `t ^ 0` and `t ^ 1` are below the cutoff.
    have hn2 : n < 2 := by
      rw [map_nsmul, nsmul_eq_mul] at hn
      have := hpos c (Set.mem_insert c _)
      exact_mod_cast lt_of_mul_lt_mul_right (hn.trans_lt hA) this.le
    simp only [rayTorusWeightSeries_def, Finset.prod_singleton, PNat.one_coe, expand_one,
      AlgHom.id_apply, Ne.symm hcc', ↓reduceIte]
    interval_cases n
    · rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
        constantCoeff_torusWeightSeries, constantCoeff_torusWeightSeries]
    · simp

end Ray

end TauCeti

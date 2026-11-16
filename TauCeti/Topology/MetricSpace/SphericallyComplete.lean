/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Spherically complete spaces

A pseudometric space is *spherically complete* if every decreasing sequence of closed balls has a
common point. Unlike completeness, the radii are not required to tend to zero. For a
nonarchimedean field this is the hypothesis of the nonarchimedean Hahn–Banach theorem, and
Bhatt and Scholze use it to show that bounded lattices saturated with respect to the maximal
ideal are finite free.

Every proper space, for instance every locally compact nonarchimedean field such as `ℚ_p`, is
spherically complete. So is every complete ultrapseudometric space whose nonzero distances are
powers of a fixed real number greater than one, even without local compactness. The field `ℂ_p`
is complete but not spherically complete. Conversely, every spherically complete pseudometric space
is complete (`TauCeti.SphericallyCompleteSpace.completeSpace`).

In an ultrapseudometric space, strict inclusion of closed balls forces a strict inequality of
diameters (`IsUltrametricDist.diam_lt_of_closedBall_ssubset`). Consequently, every chain of closed
balls either has a smallest element or contains a cofinal decreasing sequence, so countable-chain
spherical completeness is equivalent to arbitrary-chain spherical completeness
(`TauCeti.sphericallyCompleteSpace_iff_isChain`) and to the binary intersection property for closed
balls (`TauCeti.sphericallyCompleteSpace_iff_pairwise_inter_closedBall`).

## Main definitions

* `TauCeti.SphericallyCompleteSpace α`: every decreasing sequence of closed balls in `α` with
  nonnegative radii has nonempty intersection.

## Main results

* `TauCeti.SphericallyCompleteSpace.completeSpace`: every spherically complete pseudometric space
  is complete.
* `TauCeti.sphericallyCompleteSpace_iff_isChain`: in an ultrapseudometric space, spherical
  completeness is equivalent to every nonempty chain of closed balls having nonempty intersection.
* `TauCeti.sphericallyCompleteSpace_iff_pairwise_inter_closedBall`: in an ultrapseudometric space,
  spherical completeness is equivalent to every pairwise intersecting family of closed balls having
  nonempty intersection.
* `TauCeti.sphericallyCompleteSpace_of_antitone_radii`: in an ultrapseudometric space, it suffices
  to verify spherical completeness for sequences with antitone radii satisfying
  `dist (c (n + 1)) (c n) ≤ r n`.
* `TauCeti.sphericallyCompleteSpace_of_dist_eq_zpow`: completeness implies spherical
  completeness when nonzero distances lie in a discrete geometric progression.
* `TauCeti.SphericallyCompleteSpace.exists_forall_mem_of_dist_le`: in a spherically complete
  ultrametric space `X`, let `A n` be sets of families `ι → X` and `r` an antitone sequence of
  nonnegative radii. Suppose that each `A n` contains the closed polydisc of radius `r n` about
  each of its points, that every point of `A n` is within `r n` of a point of `A (n + 1)`, and
  that `A 0` is nonempty. Then the sets `A n` have a common point.

## References

* A. W. Ingleton, *The Hahn–Banach theorem for non-Archimedean valued fields*,
  Proc. Cambridge Philos. Soc. **48** (1952), 41–45.
* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §9.
* C. Perez-Garcia and W. H. Schikhof, *Locally convex spaces over non-Archimedean valued fields*,
  Cambridge Studies in Advanced Mathematics 119, Cambridge University Press, 2010, §2.4.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 6.14.
-/

public section

open Metric

namespace TauCeti

/-- A pseudometric space is *spherically complete* if every decreasing sequence of closed balls
with nonnegative radii has a common point. The radii need not tend to zero. -/
class SphericallyCompleteSpace (α : Type*) [PseudoMetricSpace α] : Prop where
  /-- Every decreasing sequence of closed balls with nonnegative radii has a common point. -/
  nonempty_iInter_closedBall {c : ℕ → α} {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n)
    (h : Antitone fun n ↦ closedBall (c n) (r n)) : (⋂ n, closedBall (c n) (r n)).Nonempty

/-- Every proper space is spherically complete: closed balls are compact. -/
instance (priority := 100) SphericallyCompleteSpace.of_properSpace (α : Type*)
    [PseudoMetricSpace α] [ProperSpace α] : SphericallyCompleteSpace α where
  nonempty_iInter_closedBall hr h :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n ↦ h (Nat.le_succ n)) (fun n ↦ nonempty_closedBall.2 (hr n))
      (isCompact_closedBall _ _) fun _ ↦ isClosed_closedBall

/-- In a spherically complete ultrametric space `X`, let `A n` be sets of families `ι → X` such
that `A n` contains the closed polydisc of radius `r n` about each of its points, and every point
of `A n` is within `r n` of some point of `A (n + 1)`. If the radii decrease and `A 0` is
nonempty, the sets `A n` have a common point. -/
theorem SphericallyCompleteSpace.exists_forall_mem_of_dist_le {X ι : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] [SphericallyCompleteSpace X] {A : ℕ → Set (ι → X)} {r : ℕ → ℝ}
    (hr : Antitone r) (h0 : (A 0).Nonempty)
    (hstep : ∀ n, ∀ c ∈ A n, ∃ c' ∈ A (n + 1), ∀ i, dist (c' i) (c i) ≤ r n)
    (hball : ∀ n, ∀ c ∈ A n, ∀ t : ι → X, (∀ i, dist (t i) (c i) ≤ r n) → t ∈ A n) :
    ∃ t : ι → X, ∀ n, t ∈ A n := by
  choose! g hgA hg using hstep
  obtain ⟨c₀, hc₀⟩ := h0
  -- The centres `c n ∈ A n`, defined recursively by `c (n + 1) = g n (c n)`.
  let c : ℕ → ι → X := fun n ↦ Nat.rec c₀ g n
  have hcA (n : ℕ) : c n ∈ A n := by
    induction n with
    | zero => exact hc₀
    | succ n ih => exact hgA n (c n) ih
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨c 0, fun n ↦ by rw [Subsingleton.elim (c 0) (c n)]; exact hcA n⟩
  have hr0 (n : ℕ) : 0 ≤ r n := (dist_nonneg).trans (hg n (c n) (hcA n) i₀)
  have hball' (i : ι) : (⋂ n, closedBall (c n i) (r n)).Nonempty := by
    refine SphericallyCompleteSpace.nonempty_iInter_closedBall hr0
      (antitone_nat_of_succ_le fun n ↦ ?_)
    have hmem : c (n + 1) i ∈ closedBall (c n i) (r n) := hg n (c n) (hcA n) i
    rw [IsUltrametricDist.closedBall_eq_of_mem hmem]
    exact closedBall_subset_closedBall (hr n.le_succ)
  choose t ht using hball'
  exact ⟨t, fun n ↦ hball n (c n) (hcA n) t fun i ↦ Set.mem_iInter.1 (ht i) n⟩

/-- A complete ultrapseudometric space whose nonzero distances are integer powers of a fixed
real number is spherically complete. No local compactness is required. -/
theorem sphericallyCompleteSpace_of_dist_eq_zpow {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] [CompleteSpace X] {b : ℝ}
    (hdiscrete : ∀ x y : X, dist x y ≠ 0 → ∃ k : ℤ, dist x y = b ^ k) :
    SphericallyCompleteSpace X := by
  obtain ⟨b, hb, hdiscrete⟩ :
      ∃ b : ℝ, 1 < b ∧ ∀ x y : X, dist x y ≠ 0 → ∃ k : ℤ, dist x y = b ^ k := by
    have habs (x y : X) (h : dist x y ≠ 0) : ∃ k : ℤ, dist x y = |b| ^ k := by
      obtain ⟨k, hk⟩ := hdiscrete x y h
      exact ⟨k, by rw [← abs_zpow, ← hk, abs_of_nonneg dist_nonneg]⟩
    rcases lt_trichotomy |b| 1 with h | h | h
    · rcases (abs_nonneg b).eq_or_lt with h0 | h0
      · refine ⟨2, one_lt_two, fun x y hxy ↦ ?_⟩
        obtain ⟨k, hk⟩ := habs x y hxy
        rw [← h0] at hk
        obtain rfl : k = 0 := by
          by_contra hk0
          exact hxy (hk.trans (zero_zpow _ hk0))
        exact ⟨0, by simpa using hk⟩
      · refine ⟨|b|⁻¹, one_lt_inv₀ h0 |>.2 h, fun x y hxy ↦ ?_⟩
        obtain ⟨k, hk⟩ := habs x y hxy
        exact ⟨-k, by rw [hk, zpow_neg, inv_zpow, inv_inv]⟩
    · refine ⟨2, one_lt_two, fun x y hxy ↦ ?_⟩
      obtain ⟨k, hk⟩ := habs x y hxy
      exact ⟨0, by simpa [h] using hk⟩
    · exact ⟨|b|, h, habs⟩
  refine ⟨fun {c r} hr hballs ↦ ?_⟩
  -- Replace the radii by their running minima without changing the intersection.
  let s : ℕ → ℝ := fun n ↦ (Finset.range (n + 1)).inf' (by simp) r
  have hs0 (n : ℕ) : 0 ≤ s n := Finset.le_inf' (by simp) r fun i _ ↦ hr i
  have hsle (n : ℕ) : s n ≤ r n := Finset.inf'_le _ (by simp)
  have hsanti : Antitone s := by
    intro m n hmn
    exact Finset.le_inf' (by simp) r fun i hi ↦ Finset.inf'_le r
      (Finset.range_mono (by omega) hi)
  have hcs (m n : ℕ) (hmn : m ≤ n) : dist (c n) (c m) ≤ s m := by
    refine Finset.le_inf' (by simp) r fun i hi ↦ ?_
    have him : i ≤ m := by simpa using hi
    exact (IsUltrametricDist.dist_triangle_max (c n) (c i) (c m)).trans
      (max_le (hballs (him.trans hmn) (mem_closedBall_self (hr n)))
        (by simpa [dist_comm] using hballs him (mem_closedBall_self (hr m))))
  have hbounded : BddBelow (Set.range s) := ⟨0, by rintro _ ⟨n, rfl⟩; exact hs0 n⟩
  have hs_lim := tendsto_atTop_ciInf hsanti hbounded
  have hinf0 : 0 ≤ ⨅ n, s n := le_ciInf hs0
  by_cases hz : (⨅ n, s n) = 0
  · have hcauchy : CauchySeq c := cauchySeq_of_le_tendsto_0' s (fun m n hmn ↦ by
      simpa [dist_comm] using hcs m n hmn) (hz ▸ hs_lim)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨x, Set.mem_iInter.2 fun n ↦ ?_⟩
    exact isClosed_closedBall.mem_of_tendsto hx (Filter.eventually_atTop.2
      ⟨n, fun m hm ↦ hballs hm (mem_closedBall_self (hr m))⟩)
  · have hpos : 0 < ⨅ n, s n := lt_of_le_of_ne hinf0 (Ne.symm hz)
    obtain ⟨k, hklo, hkhi⟩ := exists_mem_Ico_zpow hpos hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hs_lim.eventually_lt_const hkhi)
    refine ⟨c N, Set.mem_iInter.2 fun n ↦ ?_⟩
    rcases le_total n N with hn | hn
    · exact hballs hn (mem_closedBall_self (hr N))
    · by_cases hcn : dist (c N) (c n) = 0
      · simpa only [mem_closedBall, hcn] using hr n
      obtain ⟨j, hj⟩ := hdiscrete (c N) (c n) hcn
      have hjlt : b ^ j < b ^ (k + 1) := by
        rw [← hj, dist_comm]
        exact (hcs N n hn).trans_lt (hN N le_rfl)
      have hjk : j ≤ k := by
        have := (zpow_lt_zpow_iff_right₀ hb).1 hjlt
        omega
      exact (hj.trans_le (zpow_le_zpow_right₀ hb.le hjk)).trans
        (hklo.trans ((ciInf_le hbounded n).trans (hsle n)))

end TauCeti

namespace IsUltrametricDist

variable {α : Type*} [PseudoMetricSpace α] [IsUltrametricDist α]

/-- In an ultrapseudometric space, the diameter of a closed ball of nonnegative radius is at most
its radius. -/
theorem diam_closedBall_le {x : α} {r : ℝ} (hr : 0 ≤ r) : diam (closedBall x r) ≤ r :=
  diam_le_of_forall_dist_le hr fun a ha b hb ↦
    (dist_triangle_max a x b).trans (max_le ha (dist_comm b x ▸ hb))

/-- In an ultrapseudometric space, a strict inclusion of closed balls forces a strict inequality of
their diameters. -/
theorem diam_lt_of_closedBall_ssubset {x y : α} {r s : ℝ} (hr : 0 ≤ r)
    (h : closedBall x r ⊂ closedBall y s) :
    diam (closedBall x r) < diam (closedBall y s) := by
  obtain ⟨z, hz, hzx⟩ := Set.exists_of_ssubset h
  have hrx : r < dist z x := by simpa only [mem_closedBall, not_le] using hzx
  have hx : x ∈ closedBall y s := h.1 (mem_closedBall_self hr)
  exact (diam_closedBall_le hr).trans_lt
    (hrx.trans_le (dist_le_diam_of_mem isBounded_closedBall hz hx))

/-- In an ultrapseudometric space, two closed balls of nonnegative radii meet if and only if the
distance between their centres is at most the larger radius. -/
theorem nonempty_inter_closedBall_iff {x y : α} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (closedBall x r ∩ closedBall y s).Nonempty ↔ dist x y ≤ max r s := by
  refine ⟨fun ⟨z, hzx, hzy⟩ ↦ ?_, fun h ↦ ?_⟩
  · exact (dist_triangle_max x z y).trans
      (max_le_max (by simpa only [mem_closedBall, dist_comm] using hzx) hzy)
  · rcases le_total r s with hrs | hsr
    · rw [max_eq_right hrs] at h
      exact ⟨x, mem_closedBall_self hr, h⟩
    · rw [max_eq_left hsr] at h
      exact ⟨y, by simpa [dist_comm] using h, mem_closedBall_self hs⟩

end IsUltrametricDist

namespace TauCeti

/-- Every spherically complete pseudometric space is complete. No ultrametric hypothesis is
required. -/
theorem SphericallyCompleteSpace.completeSpace (α : Type*) [PseudoMetricSpace α]
    [SphericallyCompleteSpace α] : CompleteSpace α := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hN : ∀ n : ℕ, ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N, dist (u j) (u k) < (1 / 2 : ℝ) ^ (n + 1) :=
    fun n ↦ Metric.cauchySeq_iff.1 hu _ (by positivity)
  choose N hN using hN
  let φ : ℕ → ℕ := Nat.rec (N 0) fun n prev ↦ max (prev + 1) (N (n + 1))
  have hφ_strict : StrictMono φ := strictMono_nat_of_lt_succ fun n ↦
    lt_of_lt_of_le (Nat.lt_succ_self (φ n)) (le_max_left _ _)
  have hφ_ge (n : ℕ) : N n ≤ φ n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have hdist (n : ℕ) : dist (u (φ (n + 1))) (u (φ n)) < (1 / 2 : ℝ) ^ (n + 1) :=
    hN n _ ((hφ_ge n).trans (hφ_strict n.lt_succ_self).le) _ (hφ_ge n)
  have hanti : Antitone fun n ↦ closedBall (u (φ n)) ((1 / 2 : ℝ) ^ n) := by
    refine antitone_nat_of_succ_le fun n x hx ↦ ?_
    calc
      dist x (u (φ n)) ≤ dist x (u (φ (n + 1))) + dist (u (φ (n + 1))) (u (φ n)) :=
        dist_triangle _ _ _
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ (n + 1) := add_le_add hx (hdist n).le
      _ = (1 / 2 : ℝ) ^ n := by ring
  obtain ⟨x, hx⟩ := SphericallyCompleteSpace.nonempty_iInter_closedBall
    (fun n ↦ by positivity) hanti
  refine ⟨x, tendsto_nhds_of_cauchySeq_of_subseq hu hφ_strict.tendsto_atTop ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  simpa only [Function.comp_apply, dist_comm, ← mem_closedBall] using Set.mem_iInter.1 hx n

/-- In an ultrapseudometric space, spherical completeness may be checked on sequences of closed
balls with antitone radii such that each centre lies in the preceding ball. -/
theorem sphericallyCompleteSpace_of_antitone_radii {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X]
    (h : ∀ {c : ℕ → X} {r : ℕ → ℝ}, (∀ n, 0 ≤ r n) → Antitone r →
      (∀ n, dist (c (n + 1)) (c n) ≤ r n) → (⋂ n, closedBall (c n) (r n)).Nonempty) :
    SphericallyCompleteSpace X := by
  refine ⟨fun {c r} hr hballs ↦ ?_⟩
  let s : ℕ → ℝ := fun n ↦ (Finset.range (n + 1)).inf' (by simp) r
  have hs0 (n : ℕ) : 0 ≤ s n := Finset.le_inf' (by simp) r fun i _ ↦ hr i
  have hsle (n : ℕ) : s n ≤ r n := Finset.inf'_le _ (by simp)
  have hsanti : Antitone s := fun m n hmn ↦
    Finset.le_inf' (by simp) r fun i hi ↦ Finset.inf'_le r (Finset.range_mono (by omega) hi)
  have hstep (n : ℕ) : dist (c (n + 1)) (c n) ≤ s n := by
    refine Finset.le_inf' (by simp) r fun i hi ↦ ?_
    have hin : i ≤ n := by simpa using hi
    exact (IsUltrametricDist.dist_triangle_max (c (n + 1)) (c i) (c n)).trans
      (max_le (hballs (hin.trans n.le_succ) (mem_closedBall_self (hr (n + 1))))
        (by simpa [dist_comm] using hballs hin (mem_closedBall_self (hr n))))
  obtain ⟨x, hx⟩ := h hs0 hsanti hstep
  exact ⟨x, Set.mem_iInter.2 fun n ↦ closedBall_subset_closedBall (hsle n) (Set.mem_iInter.1 hx n)⟩

/-- In a spherically complete ultrapseudometric space, every nonempty chain of closed balls with
nonnegative radii has nonempty intersection. -/
theorem SphericallyCompleteSpace.nonempty_sInter_of_isChain {α : Type*} [PseudoMetricSpace α]
    [IsUltrametricDist α] [SphericallyCompleteSpace α] {c : Set (Set α)}
    (hc_ne : c.Nonempty) (hc_chain : IsChain (· ⊆ ·) c)
    (hc_ball : ∀ B ∈ c, ∃ x : α, ∃ r : ℝ, 0 ≤ r ∧ B = closedBall x r) :
    (⋂₀ c).Nonempty := by
  have hc_bdd {B : Set α} (hB : B ∈ c) : Bornology.IsBounded B := by
    obtain ⟨_, _, -, rfl⟩ := hc_ball B hB; exact isBounded_closedBall
  have hsub_of_diam_lt {A B : Set α} (hA : A ∈ c) (hB : B ∈ c) (h : diam A < diam B) : A ⊆ B :=
    (hc_chain.total hA hB).resolve_right fun hBA ↦ h.not_ge (diam_mono hBA (hc_bdd hA))
  let D : Set ℝ := diam '' c
  have hD_ne : D.Nonempty := hc_ne.image _
  have hD_bdd : BddBelow D := ⟨0, by rintro _ ⟨_, _, rfl⟩; exact diam_nonneg⟩
  let δ : ℝ := sInf D
  by_cases hδ : δ ∈ D
  · -- When the infimum diameter is attained, that ball is contained in every ball of the chain.
    obtain ⟨B₀, hB₀c, hB₀d⟩ := hδ
    obtain ⟨x₀, r₀, hr₀, rfl⟩ := hc_ball B₀ hB₀c
    refine ⟨x₀, Set.mem_sInter.2 fun B hB ↦ ?_⟩
    rcases hc_chain.total hB₀c hB with hsub | hsub
    · exact hsub (mem_closedBall_self hr₀)
    · rcases hsub.eq_or_ssubset with rfl | hssub
      · exact mem_closedBall_self hr₀
      · obtain ⟨x, r, hr, rfl⟩ := hc_ball B hB
        exact absurd (csInf_le hD_bdd ⟨_, hB, rfl⟩)
          (hB₀d ▸ IsUltrametricDist.diam_lt_of_closedBall_ssubset hr hssub).not_ge
  · -- Otherwise, extract a cofinal decreasing sequence of balls whose diameters approach `δ`.
    have hlt_diam {B : Set α} (hB : B ∈ c) : δ < diam B :=
      lt_of_le_of_ne (csInf_le hD_bdd ⟨B, hB, rfl⟩) fun heq ↦ hδ ⟨B, hB, heq.symm⟩
    have hstep (n : ℕ) (A : Set α) (hA : A ∈ c) :
        ∃ B ∈ c, B ⊆ A ∧ diam B < δ + 1 / (n + 2 : ℝ) := by
      obtain ⟨_, ⟨B, hB, rfl⟩, hBlt⟩ := exists_lt_of_csInf_lt hD_ne
        (lt_min (hlt_diam hA) (lt_add_of_pos_right δ (by positivity : (0 : ℝ) < 1 / (n + 2 : ℝ))))
      exact ⟨B, hB, hsub_of_diam_lt hB hA (lt_of_lt_of_le hBlt (min_le_left _ _)),
        lt_of_lt_of_le hBlt (min_le_right _ _)⟩
    obtain ⟨_, ⟨B₀, hB₀c, rfl⟩, hB₀lt⟩ := exists_lt_of_csInf_lt hD_ne (lt_add_one δ)
    choose next hnext_mem hnext_sub hnext_lt using hstep
    let seq : ℕ → { B : Set α // B ∈ c } :=
      Nat.rec ⟨B₀, hB₀c⟩ fun n p ↦ ⟨next n p.1 p.2, hnext_mem n p.1 p.2⟩
    have hseq_lt (n : ℕ) : diam (seq n).1 < δ + 1 / (n + 1 : ℝ) := by
      cases n with
      | zero => simpa [seq] using hB₀lt
      | succ n =>
        simpa only [seq, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
          hnext_lt n (seq n).1 (seq n).2
    choose ctr rad hrad hseq_eq using fun n ↦ hc_ball (seq n).1 (seq n).2
    have hanti : Antitone fun n ↦ closedBall (ctr n) (rad n) :=
      antitone_nat_of_succ_le fun n ↦ by
        simpa only [← hseq_eq] using hnext_sub n (seq n).1 (seq n).2
    obtain ⟨z, hz⟩ := SphericallyCompleteSpace.nonempty_iInter_closedBall hrad hanti
    refine ⟨z, Set.mem_sInter.2 fun A hA ↦ ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hlt_diam hA))
    exact hsub_of_diam_lt (seq n).2 hA ((hseq_lt n).trans (by linarith))
      (hseq_eq n ▸ Set.mem_iInter.1 hz n)

/-- In an ultrapseudometric space, spherical completeness is equivalent to every nonempty chain of
closed balls with nonnegative radii having nonempty intersection. -/
theorem sphericallyCompleteSpace_iff_isChain {α : Type*} [PseudoMetricSpace α]
    [IsUltrametricDist α] :
    SphericallyCompleteSpace α ↔
      ∀ c : Set (Set α), c.Nonempty → IsChain (· ⊆ ·) c →
        (∀ B ∈ c, ∃ x : α, ∃ r : ℝ, 0 ≤ r ∧ B = closedBall x r) →
        (⋂₀ c).Nonempty := by
  refine ⟨fun _ _ hne hch hball ↦ SphericallyCompleteSpace.nonempty_sInter_of_isChain hne hch hball,
    fun h ↦ ⟨fun {c r} hr hanti ↦ ?_⟩⟩
  rw [← Set.sInter_range]
  refine h (Set.range fun n ↦ closedBall (c n) (r n)) (Set.range_nonempty _) ?_ ?_
  · rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ -
    rcases le_total m n with hmn | hnm
    · exact Or.inr (hanti hmn)
    · exact Or.inl (hanti hnm)
  · rintro _ ⟨n, rfl⟩
    exact ⟨c n, r n, hr n, rfl⟩

/-- In a spherically complete ultrapseudometric space, every nonempty family of closed balls that
intersect pairwise has a common point. -/
theorem SphericallyCompleteSpace.nonempty_iInter_closedBall_of_pairwise {α ι : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α] [SphericallyCompleteSpace α] [Nonempty ι]
    {c : ι → α} {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hp : ∀ i j, dist (c i) (c j) ≤ max (r i) (r j)) :
    (⋂ i, closedBall (c i) (r i)).Nonempty := by
  rw [← Set.sInter_range]
  refine SphericallyCompleteSpace.nonempty_sInter_of_isChain (Set.range_nonempty _) ?_ ?_
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := c i) (r := r i) (y := c j)
        (s := r j) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ((IsUltrametricDist.nonempty_inter_closedBall_iff (hr i) (hr j)).2 (hp i j))
        (Set.not_nonempty_iff_eq_empty.2 h.inter_eq)
  · rintro _ ⟨i, rfl⟩
    exact ⟨c i, r i, hr i, rfl⟩

/-- In an ultrapseudometric space, spherical completeness is equivalent to the binary intersection
property for closed balls: every nonempty family of closed balls that meet pairwise has nonempty
intersection. -/
theorem sphericallyCompleteSpace_iff_pairwise_inter_closedBall {α : Type*} [PseudoMetricSpace α]
    [IsUltrametricDist α] :
    SphericallyCompleteSpace α ↔
      ∀ c : Set (Set α), c.Nonempty →
        (∀ A ∈ c, ∀ B ∈ c, (A ∩ B).Nonempty) →
        (∀ B ∈ c, ∃ x : α, ∃ r : ℝ, 0 ≤ r ∧ B = closedBall x r) →
        (⋂₀ c).Nonempty := by
  rw [sphericallyCompleteSpace_iff_isChain]
  refine ⟨fun h c hne hpair hball ↦ h c hne ?_ hball,
    fun h c hne hch hball ↦ h c hne ?_ hball⟩
  · intro A hA B hB _
    obtain ⟨x, r, -, rfl⟩ := hball A hA
    obtain ⟨y, s, -, rfl⟩ := hball B hB
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := x) (r := r) (y := y)
        (s := s) with hsub | hsub | hdisj
    · exact Or.inl hsub
    · exact Or.inr hsub
    · exact absurd (hpair _ hA _ hB) (Set.not_nonempty_iff_eq_empty.2 hdisj.inter_eq)
  · intro A hA B hB
    obtain ⟨x, r, hr, rfl⟩ := hball A hA
    obtain ⟨y, s, hs, rfl⟩ := hball B hB
    rcases hch.total hA hB with hsub | hsub
    · exact ⟨x, mem_closedBall_self hr, hsub (mem_closedBall_self hr)⟩
    · exact ⟨y, hsub (mem_closedBall_self hs), mem_closedBall_self hs⟩

end TauCeti

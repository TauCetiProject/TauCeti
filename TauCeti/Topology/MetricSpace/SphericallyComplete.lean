/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Ultra.Basic

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
is complete but not spherically complete.

## Main definitions

* `TauCeti.SphericallyCompleteSpace α`: every decreasing sequence of closed balls in `α` with
  nonnegative radii has nonempty intersection.

## Main results

* `TauCeti.sphericallyCompleteSpace_of_dist_eq_zpow`: completeness implies spherical
  completeness when nonzero distances lie in a discrete geometric progression.
* `TauCeti.SphericallyCompleteSpace.exists_forall_mem_of_dist_le`: in a spherically complete
  ultrametric space `X`, let `A n` be sets of families `ι → X` and `r` an antitone sequence of
  nonnegative radii. Suppose that each `A n` contains the closed polydisc of radius `r n` about
  each of its points, that every point of `A n` is within `r n` of a point of `A (n + 1)`, and
  that `A 0` is nonempty. Then the sets `A n` have a common point.

## References

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
    (hr : Antitone r) (hr0 : ∀ n, 0 ≤ r n) (h0 : (A 0).Nonempty)
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
  have hball' (i : ι) : (⋂ n, closedBall (c n i) (r n)).Nonempty := by
    refine SphericallyCompleteSpace.nonempty_iInter_closedBall hr0
      (antitone_nat_of_succ_le fun n ↦ ?_)
    have hmem : c (n + 1) i ∈ closedBall (c n i) (r n) := hg n (c n) (hcA n) i
    rw [IsUltrametricDist.closedBall_eq_of_mem hmem]
    exact closedBall_subset_closedBall (hr n.le_succ)
  choose t ht using hball'
  exact ⟨t, fun n ↦ hball n (c n) (hcA n) t fun i ↦ Set.mem_iInter.1 (ht i) n⟩

/-- A complete ultrapseudometric space whose nonzero distances are integer powers of a fixed
real number greater than one is spherically complete. No local compactness is required. -/
theorem sphericallyCompleteSpace_of_dist_eq_zpow {X : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] [CompleteSpace X] {b : ℝ} (hb : 1 < b)
    (hdiscrete : ∀ x y : X, dist x y ≠ 0 → ∃ k : ℤ, dist x y = b ^ k) :
    SphericallyCompleteSpace X := by
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

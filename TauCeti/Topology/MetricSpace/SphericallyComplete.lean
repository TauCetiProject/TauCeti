/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Isometry
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

* `Isometry.sphericallyCompleteSpace`: spherical completeness transfers backward along a
  surjective isometry.
* `TauCeti.SphericallyCompleteSpace.completeSpace`: every spherically complete pseudometric space
  is complete.
* `TauCeti.sphericallyCompleteSpace_iff_nonempty_sInter_isChain_closedBall`: an ultrapseudometric
  space is spherically complete iff every nonempty chain of nonempty closed balls has nonempty
  intersection.
* `TauCeti.SphericallyCompleteSpace.nonempty_iInter_closedBall_of_inter_nonempty` and
  `TauCeti.SphericallyCompleteSpace.nonempty_iInter_closedBall_of_dist_le_max`: in a spherically
  complete ultrapseudometric space, every pairwise-intersecting family of closed balls has a
  common point.
* `TauCeti.sphericallyCompleteSpace_of_dist_eq_zpow`: completeness implies spherical
  completeness when nonzero distances lie in a discrete geometric progression.
* `TauCeti.SphericallyCompleteSpace.exists_forall_mem_of_dist_le`: in a spherically complete
  ultrametric space `X`, let `A n` be sets of families `ι → X` and `r` an antitone sequence of
  nonnegative radii. Suppose that each `A n` contains the closed polydisc of radius `r n` about
  each of its points, that every point of `A n` is within `r n` of a point of `A (n + 1)`, and
  that `A 0` is nonempty. Then the sets `A n` have a common point.

## References

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

/-- Spherical completeness pulls back along a surjective isometry. -/
theorem _root_.Isometry.sphericallyCompleteSpace {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [SphericallyCompleteSpace β] {f : α → β}
    (hf : Isometry f) (hsurj : Function.Surjective f) : SphericallyCompleteSpace α where
  nonempty_iInter_closedBall {c r} hr hanti := by
    have hanti' : Antitone fun n ↦ closedBall (f (c n)) (r n) := by
      intro m n hmn y hy
      obtain ⟨x, rfl⟩ := hsurj y
      rw [mem_closedBall, hf.dist_eq] at hy ⊢
      exact hanti hmn hy
    obtain ⟨y, hy⟩ := SphericallyCompleteSpace.nonempty_iInter_closedBall hr hanti'
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, Set.mem_iInter.2 fun n ↦ by
      have hn := Set.mem_iInter.1 hy n
      rwa [mem_closedBall, hf.dist_eq] at hn⟩

/-- Every spherically complete pseudometric space is complete. Not an instance to avoid adding a
`SphericallyCompleteSpace` branch to every `CompleteSpace` typeclass search. -/
theorem SphericallyCompleteSpace.completeSpace (α : Type*) [PseudoMetricSpace α]
    [SphericallyCompleteSpace α] : CompleteSpace α := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  have hstep (n : ℕ) : ∃ N, ∀ k ≥ N, ∀ l ≥ N, dist (u k) (u l) < (1 / 2 : ℝ) ^ (n + 1) :=
    Metric.cauchySeq_iff.1 hu _ (by positivity)
  choose N hN using hstep
  let φ : ℕ → ℕ := Nat.rec (N 0) fun n prev ↦ max (prev + 1) (N (n + 1))
  have hφ_mono : StrictMono φ :=
    strictMono_nat_of_lt_succ fun n ↦ Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφ_ge (n : ℕ) : N n ≤ φ n := by
    cases n with
    | zero => exact le_rfl
    | succ n => exact le_max_right _ _
  have hanti : Antitone fun n ↦ closedBall (u (φ n)) ((1 / 2 : ℝ) ^ n) := by
    refine antitone_nat_of_succ_le fun n x hx ↦ ?_
    have hdist : dist (u (φ (n + 1))) (u (φ n)) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
      (hN n (φ (n + 1)) ((hφ_ge n).trans (hφ_mono n.lt_succ_self).le) (φ n) (hφ_ge n)).le
    have hsum : (1 / 2 : ℝ) ^ (n + 1) + (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      ring
    exact (dist_triangle x (u (φ (n + 1))) (u (φ n))).trans
      ((add_le_add hx hdist).trans hsum.le)
  obtain ⟨x, hx⟩ :=
    SphericallyCompleteSpace.nonempty_iInter_closedBall (fun _ ↦ by positivity) hanti
  refine ⟨x, tendsto_nhds_of_cauchySeq_of_subseq hu hφ_mono.tendsto_atTop ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hε hhalf
  refine ⟨M, fun n hn ↦ ?_⟩
  have hxn : dist (u (φ n)) x ≤ (1 / 2 : ℝ) ^ n := by
    simpa [dist_comm] using Set.mem_iInter.1 hx n
  exact hxn.trans_lt ((pow_le_pow_of_le_one (by positivity) (by norm_num) hn).trans_lt hM)

/-- In a spherically complete ultrapseudometric space, every nonempty chain of nonempty closed
balls has nonempty intersection. -/
theorem SphericallyCompleteSpace.nonempty_sInter_of_isChain_closedBall {α : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α] [SphericallyCompleteSpace α]
    {c : Set (Set α)} (hcne : c.Nonempty) (hchain : IsChain (· ⊆ ·) c)
    (hball : ∀ B ∈ c, ∃ x r, 0 ≤ r ∧ B = closedBall x r) : (⋂₀ c).Nonempty := by
  let ρ : Set α → ℝ := fun B ↦ sInf {r : ℝ | 0 ≤ r ∧ ∃ x, B = closedBall x r}
  have hρ_nonneg (B : Set α) : 0 ≤ ρ B := Real.sInf_nonneg fun _ hr ↦ hr.1
  -- Strict inclusion of nonempty closed balls strictly increases their infimal radius.
  have hρ_lt {B₁ B₂ : Set α} (hB₁ : B₁ ∈ c) (hB₂ : B₂ ∈ c) (hss : B₁ ⊂ B₂) : ρ B₁ < ρ B₂ := by
    obtain ⟨x₁, s₀, hs₀, rfl⟩ := hball B₁ hB₁
    obtain ⟨x₂, r₂, hr₂, hB₂eq⟩ := hball B₂ hB₂
    obtain ⟨y, hy₂, hy₁⟩ := Set.exists_of_ssubset hss
    have hx₁ : x₁ ∈ closedBall x₁ s₀ := mem_closedBall_self hs₀
    have hρ₁ : ρ (closedBall x₁ s₀) ≤ s₀ :=
      csInf_le ⟨0, fun _ hr ↦ hr.1⟩ ⟨hs₀, x₁, rfl⟩
    have hs₀_lt : s₀ < dist x₁ y := by
      simpa only [mem_closedBall, not_le, dist_comm] using hy₁
    have hle_ρ₂ : dist x₁ y ≤ ρ B₂ := by
      refine le_csInf ⟨r₂, hr₂, x₂, hB₂eq⟩ ?_
      rintro r ⟨_, a, rfl⟩
      exact (IsUltrametricDist.dist_triangle_max x₁ a y).trans
        (max_le (hss.1 hx₁) (by simpa [dist_comm] using hy₂))
    exact hρ₁.trans_lt (hs₀_lt.trans_le hle_ρ₂)
  have hsub_of_le {B₁ B₂ : Set α} (hB₁ : B₁ ∈ c) (hB₂ : B₂ ∈ c) (hle : ρ B₁ ≤ ρ B₂) :
      B₁ ⊆ B₂ := by
    by_contra hnot
    rcases hchain.total hB₁ hB₂ with h | h
    · exact hnot h
    · exact (hρ_lt hB₂ hB₁ (h.ssubset_of_ne fun heq ↦ hnot (heq ▸ Set.Subset.rfl))).not_ge hle
  let L : ℝ := sInf (ρ '' c)
  have hbdd : BddBelow (ρ '' c) := ⟨0, by rintro _ ⟨B, _, rfl⟩; exact hρ_nonneg B⟩
  by_cases hmin : ∃ B₀ ∈ c, ρ B₀ = L
  · obtain ⟨B₀, hB₀c, hB₀L⟩ := hmin
    obtain ⟨x, r, hr, rfl⟩ := hball B₀ hB₀c
    refine ⟨x, Set.mem_sInter.2 fun B hBc ↦ ?_⟩
    exact hsub_of_le hB₀c hBc (hB₀L.trans_le (csInf_le hbdd ⟨B, hBc, rfl⟩)) (mem_closedBall_self hr)
  · obtain ⟨t, ht_anti, ht_lim, ht_mem⟩ := exists_seq_tendsto_sInf (hcne.image ρ) hbdd
    choose B hBc hBρ using fun n ↦ ht_mem n
    choose x r hr hBeq using fun n ↦ hball (B n) (hBc n)
    have hanti : Antitone fun n ↦ closedBall (x n) (r n) := fun m n hmn ↦ by
      dsimp only
      rw [← hBeq m, ← hBeq n]
      exact hsub_of_le (hBc n) (hBc m) (by rw [hBρ n, hBρ m]; exact ht_anti hmn)
    obtain ⟨z, hz⟩ := SphericallyCompleteSpace.nonempty_iInter_closedBall hr hanti
    refine ⟨z, Set.mem_sInter.2 fun C hCc ↦ ?_⟩
    have hLlt : L < ρ C :=
      (csInf_le hbdd ⟨C, hCc, rfl⟩).lt_of_ne fun heq ↦ hmin ⟨C, hCc, heq.symm⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (ht_lim.eventually_lt_const hLlt)
    have hBN : B N ⊆ C := hsub_of_le (hBc N) hCc (by rw [hBρ N]; exact (hN N le_rfl).le)
    exact hBN (hBeq N ▸ Set.mem_iInter.1 hz N)

/-- An ultrapseudometric space is spherically complete iff every nonempty chain of nonempty
closed balls has nonempty intersection. -/
theorem sphericallyCompleteSpace_iff_nonempty_sInter_isChain_closedBall {α : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α] :
    SphericallyCompleteSpace α ↔
      ∀ c : Set (Set α), c.Nonempty → IsChain (· ⊆ ·) c →
        (∀ B ∈ c, ∃ x r, 0 ≤ r ∧ B = closedBall x r) → (⋂₀ c).Nonempty := by
  refine ⟨fun _ c hcne hchain hball ↦
    SphericallyCompleteSpace.nonempty_sInter_of_isChain_closedBall hcne hchain hball, fun h ↦ ?_⟩
  refine ⟨fun {c r} hr hanti ↦ ?_⟩
  let S : Set (Set α) := Set.range fun n ↦ closedBall (c n) (r n)
  have hSchain : IsChain (· ⊆ ·) S := by
    rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _
    rcases le_total m n with hmn | hmn
    · exact Or.inr (hanti hmn)
    · exact Or.inl (hanti hmn)
  have hne := h S ⟨_, 0, rfl⟩ hSchain (by rintro _ ⟨n, rfl⟩; exact ⟨c n, r n, hr n, rfl⟩)
  rwa [Set.sInter_range] at hne

/-- Binary intersection property: in a spherically complete ultrapseudometric space, every
nonempty family of closed balls that intersect pairwise has a common point. -/
theorem SphericallyCompleteSpace.nonempty_iInter_closedBall_of_inter_nonempty {α ι : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α] [SphericallyCompleteSpace α] [Nonempty ι]
    {c : ι → α} {r : ι → ℝ}
    (h : ∀ i j, (closedBall (c i) (r i) ∩ closedBall (c j) (r j)).Nonempty) :
    (⋂ i, closedBall (c i) (r i)).Nonempty := by
  let S : Set (Set α) := Set.range fun i ↦ closedBall (c i) (r i)
  have hSchain : IsChain (· ⊆ ·) S := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    rcases IsUltrametricDist.closedBall_subset_trichotomy (c i) (c j) (r i) (r j) with
      hij | hji | hdisj
    · exact Or.inl hij
    · exact Or.inr hji
    · exact (Set.not_disjoint_iff_nonempty_inter.2 (h i j) hdisj).elim
  have hball : ∀ B ∈ S, ∃ x s, 0 ≤ s ∧ B = closedBall x s := by
    rintro _ ⟨i, rfl⟩
    have hi : (closedBall (c i) (r i)).Nonempty := (h i i).mono Set.inter_subset_left
    exact ⟨c i, r i, nonempty_closedBall.1 hi, rfl⟩
  have hne := SphericallyCompleteSpace.nonempty_sInter_of_isChain_closedBall
    (Set.range_nonempty _) hSchain hball
  rwa [Set.sInter_range] at hne

/-- In a spherically complete ultrapseudometric space, any nonempty family of closed balls
`closedBall (c i) (r i)` with `dist (c i) (c j) ≤ max (r i) (r j)` has a common point. -/
theorem SphericallyCompleteSpace.nonempty_iInter_closedBall_of_dist_le_max {α ι : Type*}
    [PseudoMetricSpace α] [IsUltrametricDist α] [SphericallyCompleteSpace α] [Nonempty ι]
    {c : ι → α} {r : ι → ℝ} (h : ∀ i j, dist (c i) (c j) ≤ max (r i) (r j)) :
    (⋂ i, closedBall (c i) (r i)).Nonempty := by
  have hr (i : ι) : 0 ≤ r i := by
    simpa only [dist_self, max_self] using h i i
  refine SphericallyCompleteSpace.nonempty_iInter_closedBall_of_inter_nonempty fun i j ↦ ?_
  rcases le_total (r i) (r j) with hij | hji
  · refine ⟨c i, mem_closedBall_self (hr i), ?_⟩
    rw [mem_closedBall]
    exact (h i j).trans (max_le hij le_rfl)
  · refine ⟨c j, ?_, mem_closedBall_self (hr j)⟩
    rw [mem_closedBall, dist_comm]
    exact (h i j).trans (max_le le_rfl hji)

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Analysis.Polynomial.Monic.RootBound
import TauCeti.Data.Multiset.Rel
import TauCeti.Topology.Algebra.Polynomial.Basic
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# Root graphs of families of monic polynomials

Let `q x` be monic polynomials of a fixed degree `n` over a proper algebraically closed normed
field `K`, `ℂ` being the case of interest, depending on a parameter `x` in a set `s`. Their
**root graph** is the set `{(x, z) | x ∈ s, q x (z) = 0}` in `X × K`
(`Polynomial.rootGraph`). Over each `x ∈ s` it has at most `n` points, the roots of `q x`, which
carry the multiplicities `rootMultiplicity z (q x)`. If the coefficients of `q` are continuous on
`s`, the root graph is closed when `s` is (`Polynomial.isClosed_rootGraph`) and compact when `s`
is (`Polynomial.isCompact_rootGraph`): a finite closed multigraph over `s`.

The main result is that root graphs depend continuously on the coefficients, uniformly over a
compact parameter set. If the coefficients of monic polynomials `p i x` of degree `n` converge
to those of `q x` uniformly on a compact set `s` and those of `q` are continuous on `s`, then
eventually, for **every** `x ∈ s` at once, the roots of `p i x` and of `q x` are matched
bijectively, with multiplicity, by pairs at distance less than `ε`
(`Polynomial.eventually_forall_rel_roots_norm_sub_lt`). This is the uniform form of the
continuity of roots of `Polynomial.Monic.exists_rel_roots_norm_sub_lt`, obtained from it by
compactness. Matched roots lie over the same parameter, so the root graphs converge in the
Hausdorff extended distance of `X × K` (`Polynomial.tendsto_hausdorffEDist_rootGraph`).

Consequently, sets `A i` that are Hausdorff-close to the root graphs of `p i` converge to the root
graph of `q` (`Polynomial.tendsto_hausdorffEDist_rootGraph_of_tendsto`), and every limit of points
of the `A i` lies on that root graph (`Polynomial.mem_rootGraph_of_tendsto`). Such sets could be
the zero sets of fields whose Newton polynomials are `p i`, once a support estimate shows that they
are Hausdorff-close to the root graphs of `p i`; that estimate is not proved here but assumed. In
Taubes's analysis of Seiberg–Witten solutions near a pseudoholomorphic curve, `p i x` are the
Newton polynomials of the normal moments of the curvature currents over the base point `x` of the
curve. Given such a support estimate, these statements give the convergence of the rescaled zero
sets to the root multigraph of the limiting coefficients, with every marked zero retained in the
limit.

## Main results

* `Polynomial.eventually_forall_rel_roots_norm_sub_lt`: uniform continuity of roots, with
  multiplicity, on a compact parameter set.
* `Polynomial.isClosed_rootGraph`, `Polynomial.isCompact_rootGraph`,
  `Polynomial.mk_mem_rootGraph_iff`, `Polynomial.ncard_mk_preimage_rootGraph_le`: the root
  graph is a closed (compact) multigraph with at most `n` points over each parameter.
* `Polynomial.tendsto_hausdorffEDist_rootGraph`: convergence of root graphs.
* `Polynomial.tendsto_hausdorffEDist_rootGraph_of_tendsto`, `Polynomial.mem_rootGraph_of_tendsto`:
  sets approaching the root graphs of `p i` converge to the root graph of `q` and retain their
  limit points.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of the roots of a polynomial with respect to its coefficients).
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Filter Metric Set Topology

namespace Polynomial

variable {X : Type*}

section Graph

variable {R : Type*} [Semiring R] {p : X → R[X]} {s : Set X}

variable (p s) in
/-- The **root graph** of a family of polynomials `p x` over a set `s` of parameters: the pairs
`(x, z)` with `x ∈ s` and `z` a root of `p x`. -/
def rootGraph : Set (X × R) :=
  {y | y.1 ∈ s ∧ (p y.1).IsRoot y.2}

@[simp]
theorem mem_rootGraph {y : X × R} : y ∈ rootGraph p s ↔ y.1 ∈ s ∧ (p y.1).IsRoot y.2 :=
  Iff.rfl

/-- **The root graph is closed.** If `s` is closed, the polynomials `p x` have degree at most `n`
and their coefficients of index at most `n` are continuous on `s`, then the root graph of `p`
over `s` is closed. -/
theorem isClosed_rootGraph [TopologicalSpace X] [TopologicalSpace R] [IsTopologicalSemiring R]
    [T1Space R] {n : ℕ} (hs : IsClosed s) (hdeg : ∀ x ∈ s, (p x).natDegree ≤ n)
    (hc : ∀ k ≤ n, ContinuousOn (fun x ↦ (p x).coeff k) s) : IsClosed (rootGraph p s) := by
  -- On `s × R` the root condition is the vanishing of a polynomial in the coefficients.
  let F : X × R → R := fun y ↦ ∑ k ∈ Finset.range (n + 1), (p y.1).coeff k * y.2 ^ k
  have hF : ContinuousOn F (s ×ˢ univ) := continuousOn_finsetSum _ fun k hk ↦
    ((hc k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).comp continuousOn_fst
      fun y (hy : y ∈ s ×ˢ univ) ↦ hy.1).mul (continuous_snd.pow k).continuousOn
  have heq : rootGraph p s = s ×ˢ univ ∩ F ⁻¹' {0} := by
    ext ⟨x, z⟩
    simp only [mem_rootGraph, IsRoot.def, mem_inter_iff, mem_prod, mem_univ, and_true,
      mem_preimage, mem_singleton_iff, F]
    exact and_congr_right fun hx ↦ by rw [eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg x hx))]
  rw [heq]
  exact hF.preimage_isClosed_of_isClosed (hs.prod isClosed_univ) isClosed_singleton

end Graph

section Roots

variable {R : Type*} [CommRing R] [IsDomain R] {p : X → R[X]} {s : Set X}

/-- Over a parameter where the polynomial is nonzero, the root graph consists of its roots. -/
theorem mk_mem_rootGraph_iff {x : X} (hx : p x ≠ 0) {z : R} :
    (x, z) ∈ rootGraph p s ↔ x ∈ s ∧ z ∈ (p x).roots := by
  rw [mem_rootGraph, mem_roots hx]

/-- The root graph has at most `natDegree (p x)` points over each parameter `x` with `p x ≠ 0`. -/
theorem ncard_mk_preimage_rootGraph_le {x : X} (hx : p x ≠ 0) :
    (Prod.mk x ⁻¹' rootGraph p s).ncard ≤ (p x).natDegree := by
  classical
  calc (Prod.mk x ⁻¹' rootGraph p s).ncard ≤ ((p x).roots.toFinset : Set R).ncard :=
        ncard_le_ncard (fun z hz ↦ by
          simpa using ((mk_mem_rootGraph_iff hx).1 hz).2) (Finset.finite_toSet _)
    _ = (p x).roots.toFinset.card := ncard_coe_finset _
    _ ≤ Multiset.card (p x).roots := Multiset.toFinset_card_le _
    _ ≤ (p x).natDegree := card_roots' _

end Roots

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K] {ι : Type*} {l : Filter ι}
  {p : ι → X → K[X]} {q : X → K[X]} {s : Set X} {n : ℕ}

omit [IsAlgClosed K] in
/-- **The root graph is compact.** If `s` is compact, the polynomials `q x` are monic of degree
`n` and their lower coefficients are continuous on `s`, then the root graph of `q` over `s` is
compact. -/
theorem isCompact_rootGraph [TopologicalSpace X] [T2Space X] (hs : IsCompact s)
    (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s) : IsCompact (rootGraph q s) := by
  -- The coefficients are bounded on `s`, hence so are the roots, by Fujiwara's bound.
  have hbdd : ∀ k < n, ∃ C, ∀ x ∈ s, ‖(q x).coeff k‖ ≤ C := fun k hk ↦
    hs.exists_bound_of_continuousOn (hqc k hk)
  choose! C hC using hbdd
  set c := max 1 (∑ k ∈ Finset.range n, C k)
  have hcoeff : ∀ x ∈ s, ∀ k < n, ‖(q x).coeff k‖ ≤ c ^ (n - k) := fun x hx k hk ↦
    calc ‖(q x).coeff k‖ ≤ C k := hC k hk x hx
      _ ≤ ∑ j ∈ Finset.range n, C j :=
        Finset.single_le_sum (fun j hj ↦ (norm_nonneg _).trans (hC j (Finset.mem_range.1 hj) x hx))
          (Finset.mem_range.2 hk)
      _ ≤ c := le_max_right _ _
      _ = c ^ 1 := (pow_one c).symm
      _ ≤ c ^ (n - k) := pow_le_pow_right₀ (le_max_left _ _) (by omega)
  have hsub : rootGraph q s ⊆ s ×ˢ closedBall 0 (2 * c) := fun y hy ↦
    ⟨hy.1, mem_closedBall_zero_iff.2 <| IsRoot.norm_le_two_mul (hq y.1 hy.1).1
      (fun k hk ↦ by rw [(hq y.1 hy.1).2] at hk ⊢; exact hcoeff y.1 hy.1 k hk) hy.2⟩
  exact (hs.prod (isCompact_closedBall 0 (2 * c))).of_isClosed_subset
    (isClosed_rootGraph hs.isClosed (fun x hx ↦ (hq x hx).2.le)
      fun _ ↦ continuousOn_coeff_of_monic (fun x hx ↦ (hq x hx).1) (fun x hx ↦ (hq x hx).2) hqc)
    hsub

/-- Locally near each parameter `x₀ ∈ s`, there is a single `δ > 0` such that every monic
polynomial of degree `n` whose lower coefficients are `δ`-close to those of `q x` has its roots
`ε`-matched with those of `q x`. -/
private theorem exists_nhdsWithin_rel_roots_norm_sub_lt [TopologicalSpace X]
    (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s) {ε : ℝ} (hε : 0 < ε) {x₀ : X}
    (hx₀ : x₀ ∈ s) :
    ∃ U ∈ 𝓝[s] x₀, ∃ δ > 0, ∀ x ∈ U ∩ s, ∀ g : K[X], g.Monic → g.natDegree = n →
      (∀ k < n, ‖g.coeff k - (q x).coeff k‖ < δ) →
        (q x).roots.Rel (fun z w ↦ ‖z - w‖ < ε) g.roots := by
  obtain ⟨hm₀, hn₀⟩ := hq x₀ hx₀
  obtain ⟨δ, hδ, hmatch⟩ := hm₀.exists_rel_roots_norm_sub_lt (half_pos hε)
  rw [hn₀] at hmatch
  -- Near `x₀` the coefficients of `q x` are `δ / 2`-close to those of `q x₀`.
  have hU : ∀ᶠ x in 𝓝[s] x₀, ∀ k < n, ‖(q x).coeff k - (q x₀).coeff k‖ < δ / 2 :=
    (eventually_all_finite (finite_lt_nat n)).2 fun k hk ↦ by
      simpa [dist_eq_norm] using
        ((hqc k hk) x₀ hx₀).eventually (ball_mem_nhds _ (half_pos hδ))
  refine ⟨_, hU, δ / 2, half_pos hδ, fun x ⟨hxU, hx⟩ g hg hgn hgx ↦ ?_⟩
  -- Both `q x` and `g` are matched with `q x₀` within `ε / 2`; compose the two matchings.
  have hclose : ∀ g : K[X], (∀ k < n, ‖g.coeff k - (q x).coeff k‖ < δ / 2) →
      ∀ k < n, ‖g.coeff k - (q x₀).coeff k‖ < δ := fun g hg k hk ↦
    (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans_lt (by linarith [hg k hk, hxU k hk])
  have h₁ := hmatch (q x) (hq x hx).1 (hq x hx).2
    (hclose _ fun k _ ↦ by simpa using half_pos hδ)
  have h₂ := hmatch g hg hgn (hclose g hgx)
  refine ((Multiset.rel_flip.2 h₁).comp h₂).mono fun z _ w _ ⟨v, hzv, hvw⟩ ↦ ?_
  calc ‖z - w‖ ≤ ‖z - v‖ + ‖v - w‖ := norm_sub_le_norm_sub_add_norm_sub z v w
    _ < ε / 2 + ε / 2 := add_lt_add (by rwa [norm_sub_rev]) hvw
    _ = ε := add_halves ε

/-- **Uniform continuity of roots on a compact parameter set.** Let `q x` be monic polynomials of
degree `n` whose lower coefficients are continuous on a compact set `s`, and let `p i x` be monic
polynomials of degree `n` whose lower coefficients converge to those of `q x` uniformly on `s`.
Then for every `ε > 0`, eventually, for every `x ∈ s`, the roots of `q x` and of `p i x` are
matched bijectively, counted with multiplicity, by pairs at distance less than `ε`. -/
theorem eventually_forall_rel_roots_norm_sub_lt [TopologicalSpace X] (hs : IsCompact s)
    (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hp : ∀ᶠ i in l, ∀ x ∈ s, (p i x).Monic ∧ (p i x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ k < n, TendstoUniformlyOn (fun i x ↦ (p i x).coeff k) (fun x ↦ (q x).coeff k) l s)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ x ∈ s, (q x).roots.Rel (fun z w ↦ ‖z - w‖ < ε) (p i x).roots := by
  choose! U hU δ hδ hmatch using fun x₀ (hx₀ : x₀ ∈ s) ↦
    exists_nhdsWithin_rel_roots_norm_sub_lt hq hqc hε hx₀
  obtain ⟨t, hts, hst⟩ := hs.elim_nhdsWithin_subcover U hU
  -- Eventually the coefficients are `δ x₀`-close for each of the finitely many centres `x₀ ∈ t`.
  have hclose : ∀ᶠ i in l, ∀ x₀ ∈ t, ∀ x ∈ s, ∀ k < n,
      ‖(p i x).coeff k - (q x).coeff k‖ < δ x₀ := by
    refine t.eventually_all.2 fun x₀ hx₀ ↦ ?_
    have := (eventually_all_finite (finite_lt_nat n)).2 fun k (hk : k < n) ↦
      Metric.tendstoUniformlyOn_iff.1 (hpq k hk) (δ x₀) (hδ x₀ (hts x₀ hx₀))
    filter_upwards [this] with i hi x hx k hk
    simpa [dist_eq_norm, norm_sub_rev] using hi k hk x hx
  filter_upwards [hp, hclose] with i hpi hi x hx
  obtain ⟨x₀, hx₀t, hxU⟩ := mem_iUnion₂.1 (hst hx)
  exact hmatch x₀ (hts x₀ hx₀t) x ⟨hxU, hx⟩ (p i x) (hpi x hx).1 (hpi x hx).2
    (hi x₀ hx₀t x hx)

/-- **Convergence of root graphs.** Under the hypotheses of
`Polynomial.eventually_forall_rel_roots_norm_sub_lt`, the root graphs of `p i` over `s` converge
to the root graph of `q` over `s` in the Hausdorff extended distance of `X × K`. -/
theorem tendsto_hausdorffEDist_rootGraph [PseudoEMetricSpace X] (hs : IsCompact s)
    (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hp : ∀ᶠ i in l, ∀ x ∈ s, (p i x).Monic ∧ (p i x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ k < n, TendstoUniformlyOn (fun i x ↦ (p i x).coeff k) (fun x ↦ (q x).coeff k) l s) :
    Tendsto (fun i ↦ hausdorffEDist (rootGraph (p i) s) (rootGraph q s)) l (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε ↦ ?_
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  filter_upwards [hp, eventually_forall_rel_roots_norm_sub_lt hs hq hp hqc hpq hr'] with i hpi hi
  -- Matched roots lie over the same parameter, at distance `‖z - w‖ < r`.
  have hedist : ∀ (x : X) (z w : K), ‖z - w‖ < r → edist (x, z) (x, w) ≤ ENNReal.ofReal r :=
    fun x z w hzw ↦ by
      rw [Prod.edist_eq, edist_self, zero_max, edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal hzw.le
  refine (hausdorffEDist_le_of_mem_edist (fun y hy ↦ ?_) fun y hy ↦ ?_).trans hrε.le
  · obtain ⟨x, w⟩ := y
    rw [mk_mem_rootGraph_iff (hpi x hy.1).1.ne_zero] at hy
    obtain ⟨z, hz, hzw⟩ :=
      Multiset.exists_mem_of_rel_of_mem (Multiset.rel_flip.2 (hi x hy.1)) hy.2
    exact ⟨(x, z), (mk_mem_rootGraph_iff (hq x hy.1).1.ne_zero).2 ⟨hy.1, hz⟩,
      hedist x w z (by rwa [norm_sub_rev])⟩
  · obtain ⟨x, z⟩ := y
    rw [mk_mem_rootGraph_iff (hq x hy.1).1.ne_zero] at hy
    obtain ⟨w, hw, hzw⟩ := Multiset.exists_mem_of_rel_of_mem (hi x hy.1) hy.2
    exact ⟨(x, w), (mk_mem_rootGraph_iff (hpi x hy.1).1.ne_zero).2 ⟨hy.1, hw⟩,
      hedist x z w hzw⟩

/-- **Sets near the root graphs converge to the limit root graph.** Under the hypotheses of
`Polynomial.eventually_forall_rel_roots_norm_sub_lt`, if sets `A i ⊆ X × K` approach the root
graphs of `p i` over `s` in the Hausdorff extended distance, then they converge to the root graph
of `q` over `s`. -/
theorem tendsto_hausdorffEDist_rootGraph_of_tendsto [PseudoEMetricSpace X] (hs : IsCompact s)
    (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hp : ∀ᶠ i in l, ∀ x ∈ s, (p i x).Monic ∧ (p i x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ k < n, TendstoUniformlyOn (fun i x ↦ (p i x).coeff k) (fun x ↦ (q x).coeff k) l s)
    {A : ι → Set (X × K)}
    (hA : Tendsto (fun i ↦ hausdorffEDist (A i) (rootGraph (p i) s)) l (𝓝 0)) :
    Tendsto (fun i ↦ hausdorffEDist (A i) (rootGraph q s)) l (𝓝 0) :=
  tendsto_hausdorffEDist_of_tendsto_of_tendsto hA
    (tendsto_hausdorffEDist_rootGraph hs hq hp hqc hpq)

/-- **Retention of limit points.** Under the hypotheses of
`Polynomial.eventually_forall_rel_roots_norm_sub_lt` with `s` closed, if sets `A i ⊆ X × K`
approach the root graphs of `p i` over `s` in the Hausdorff extended distance, then every limit
of points `y i ∈ A i` lies on the root graph of `q` over `s`. -/
theorem mem_rootGraph_of_tendsto [PseudoEMetricSpace X] [l.NeBot] (hs : IsCompact s)
    (hs' : IsClosed s) (hq : ∀ x ∈ s, (q x).Monic ∧ (q x).natDegree = n)
    (hp : ∀ᶠ i in l, ∀ x ∈ s, (p i x).Monic ∧ (p i x).natDegree = n)
    (hqc : ∀ k < n, ContinuousOn (fun x ↦ (q x).coeff k) s)
    (hpq : ∀ k < n, TendstoUniformlyOn (fun i x ↦ (p i x).coeff k) (fun x ↦ (q x).coeff k) l s)
    {A : ι → Set (X × K)}
    (hA : Tendsto (fun i ↦ hausdorffEDist (A i) (rootGraph (p i) s)) l (𝓝 0))
    {y : ι → X × K} (hy : ∀ᶠ i in l, y i ∈ A i) {y₀ : X × K} (hy₀ : Tendsto y l (𝓝 y₀)) :
    y₀ ∈ rootGraph q s :=
  mem_of_tendsto_hausdorffEDist (isClosed_rootGraph (n := n) hs' (fun x hx ↦ (hq x hx).2.le)
    fun _ ↦ continuousOn_coeff_of_monic (fun x hx ↦ (hq x hx).1) (fun x hx ↦ (hq x hx).2) hqc)
    (tendsto_hausdorffEDist_rootGraph_of_tendsto hs hq hp hqc hpq hA) hy hy₀

end Polynomial

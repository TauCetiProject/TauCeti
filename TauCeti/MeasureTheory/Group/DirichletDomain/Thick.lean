/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.DirichletDomain.Basic
public import TauCeti.MeasureTheory.Group.FundamentalDomain
public import TauCeti.Topology.MetricSpace.ThickPart

/-!
# The thick part of a Dirichlet domain

Let a group `G` act by isometries on a metric space `X`, and recall that the `ε`-thick part
`TauCeti.thickPart G ε` is the set of points moved a distance at least `ε` by every nonidentity
element of `G`. Suppose that `G` is countable and preserves a measure `μ` for which it has a
fundamental domain of finite measure, and that the balls of radius `ε / 2` have measure bounded
below by a positive constant. Then the `ε`-thick part of every Dirichlet domain is bounded
(`TauCeti.isBounded_dirichletDomain_inter_thickPart`). Indeed, a point of a Dirichlet domain is a
point of its orbit closest to the centre, so if thick points `x` and `y` of the domain have
distances from the centre differing by at least `ε`, then `g • x` and `y` are at distance at least
`ε` for every `g`. Infinitely many such points would give infinitely many balls of radius `ε / 2`
whose translates are pairwise disjoint, and the measure of their union would be infinite yet at
most the measure of a fundamental domain.

For a properly discontinuous action on a proper space every orbit meets the Dirichlet domain, so
the image of the thick part in the orbit space is then compact
(`TauCeti.isCompact_image_thickPart`). For a Fuchsian group of finite covolume this is the
compactness of the thick part of the quotient surface, the starting point of its thick-thin
decomposition.

## Main declarations

* `TauCeti.isBounded_dirichletDomain_inter_thickPart`: for a lattice, the thick part of a
  Dirichlet domain is bounded.
* `TauCeti.isCompact_image_thickPart`: for a lattice acting properly discontinuously on a proper
  space, the thick part of the orbit space is compact.

## References

* Riccardo Benedetti and Carlo Petronio, *Lectures on Hyperbolic Geometry*, Universitext,
  Springer, 1992, Chapter D (the thick part of a finite-volume hyperbolic manifold).
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §§3.2 and 4.1 (Dirichlet regions of groups of finite covolume).
-/

public section

open MeasureTheory Metric MulAction Set

open scoped ENNReal Pointwise

namespace TauCeti

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]

/-- If `y` is at least `ε` closer to the centre than a point `x` of the Dirichlet domain, then
every translate of `x` is at distance at least `ε` from `y`. -/
private theorem le_dist_smul_of_mem_dirichletDomain {p x y : X} {ε : ℝ}
    (hx : x ∈ dirichletDomain G p) (hxy : dist y p + ε ≤ dist x p) (g : G) :
    ε ≤ dist (g • x) y := by
  linarith [dist_le_dist_smul_of_mem_dirichletDomain hx g, dist_triangle (g • x) y p]

variable [MeasurableSpace X] [OpensMeasurableSpace X] [Countable G] [MeasurableConstSMul G X]
  {μ : Measure X} [SMulInvariantMeasure G X μ] {s : Set X}

/-- **The thick part of a Dirichlet domain of a lattice is bounded.** Let `G` act isometrically
on `X`, preserving a measure `μ` with a fundamental domain `s` of finite measure. If the balls of
radius `ε / 2` have measure at least `c ≠ 0`, then the points of a Dirichlet domain moved at least
`ε` by every nonidentity element form a bounded set. -/
theorem isBounded_dirichletDomain_inter_thickPart (hs : IsFundamentalDomain G s μ)
    (hμs : μ s ≠ ∞) {ε : ℝ} {c : ℝ≥0∞} (hc : c ≠ 0) (hball : ∀ x, c ≤ μ (ball x (ε / 2)))
    (p : X) : Bornology.IsBounded (dirichletDomain G p ∩ thickPart G ε) := by
  have hε : 0 < ε := by
    by_contra! h
    have hp := hball p
    rw [ball_eq_empty.2 (by linarith), measure_empty, nonpos_iff_eq_zero] at hp
    exact hc hp
  by_contra hT
  -- The thick part of the domain has points arbitrarily far from the centre.
  have hfar (R : ℝ) : ∃ x ∈ dirichletDomain G p ∩ thickPart G ε, R ≤ dist x p := by
    by_contra! h
    exact hT (isBounded_closedBall.subset fun x hx ↦ mem_closedBall.2 (h x hx).le)
  choose F hFT hFdist using hfar
  -- Choose such points `x n` whose distances from the centre increase by at least `ε` each step.
  let r : ℕ → ℝ := fun n ↦ Nat.rec 0 (fun _ ρ ↦ dist (F ρ) p + ε) n
  let x : ℕ → X := fun n ↦ F (r n)
  -- By definition `r (n + 1)` is `dist (x n) p + ε`.
  have hstep (n : ℕ) : dist (x n) p + ε ≤ dist (x (n + 1)) p := hFdist (r (n + 1))
  have hmono {m n : ℕ} (hmn : m < n) : dist (x m) p + ε ≤ dist (x n) p := by
    induction n, hmn using Nat.le_induction with
    | base => exact hstep m
    | succ n _ ih => linarith [hstep n]
  -- Any translate of one of the balls misses every other ball, and the nonidentity translates
  -- of a ball miss the ball itself.
  have hdisj (g : G) (m n : ℕ) (h : g ≠ 1 ∨ m ≠ n) :
      Disjoint (g • ball (x m) (ε / 2)) (ball (x n) (ε / 2)) := by
    rw [Metric.smul_ball]
    refine ball_disjoint_ball ?_
    rw [add_halves]
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · exact le_dist_smul_of_mem_dirichletDomain (hFT _).1 (hmono hnm) g
    · exact mem_thickPart.1 (hFT _).2 g (h.resolve_right (not_not.2 rfl))
    · rw [← dist_smul g⁻¹, inv_smul_smul, dist_comm]
      exact le_dist_smul_of_mem_dirichletDomain (hFT _).1 (hmono hmn) g⁻¹
  set t := ⋃ n, ball (x n) (ε / 2)
  have ht {g : G} (hg : g ≠ 1) : Disjoint (g • t) t := by
    rw [smul_set_iUnion]
    exact disjoint_iUnion_left.2 fun m ↦ disjoint_iUnion_right.2 fun n ↦ hdisj g m n (.inl hg)
  -- The union of the balls embeds in the quotient, so its measure is at most that of `s`.
  have hle : μ t ≤ μ s := hs.measure_le_of_disjoint_smul
    (MeasurableSet.iUnion fun _ ↦ measurableSet_ball).nullMeasurableSet fun _ ↦ ht
  -- But the balls are pairwise disjoint and each has measure at least `c ≠ 0`.
  have htop : μ t = ∞ := by
    rw [measure_iUnion (fun m n hmn ↦ by simpa using hdisj 1 m n (.inr hmn))
      fun _ ↦ measurableSet_ball]
    exact top_unique <| (ENNReal.tsum_const_eq_top_of_ne_zero hc).symm.le.trans <|
      ENNReal.tsum_le_tsum fun _ ↦ hball _
  exact hμs (top_unique (htop ▸ hle))

/-- **The thick part of the orbit space of a lattice is compact.** Let `G` act isometrically and
properly discontinuously on a proper metric space `X`, preserving a measure `μ` with a fundamental
domain `s` of finite measure. If the balls of radius `ε / 2` have measure at least `c ≠ 0`, then
the image in the orbit space of the points moved at least `ε` by every nonidentity element is
compact. -/
theorem isCompact_image_thickPart [ProperSpace X] [ProperlyDiscontinuousSMul G X]
    (hs : IsFundamentalDomain G s μ) (hμs : μ s ≠ ∞) {ε : ℝ} {c : ℝ≥0∞} (hc : c ≠ 0)
    (hball : ∀ x, c ≤ μ (ball x (ε / 2))) :
    IsCompact (Quotient.mk (orbitRel G X) '' thickPart G ε) := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨p⟩⟩
  · simp [Set.eq_empty_of_isEmpty (thickPart G ε)]
  have hK : IsCompact (dirichletDomain G p ∩ thickPart G ε) :=
    isCompact_of_isClosed_isBounded
      ((isClosed_dirichletDomain G p).inter (isClosed_thickPart G ε))
      (isBounded_dirichletDomain_inter_thickPart hs hμs hc hball p)
  -- Every orbit meeting the thick part meets it inside the Dirichlet domain.
  have himage : Quotient.mk (orbitRel G X) '' thickPart G ε =
      Quotient.mk (orbitRel G X) '' (dirichletDomain G p ∩ thickPart G ε) := by
    refine Subset.antisymm ?_ (image_mono inter_subset_right)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨g, hg⟩ := exists_smul_mem_dirichletDomain (G := G) p y
    exact ⟨g • y, ⟨hg, (smul_mem_thickPart_iff g).2 hy⟩, Quotient.sound ⟨g, rfl⟩⟩
  rw [himage]
  exact hK.image continuous_quot_mk

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Dirichlet domains

Let a group `G` act by isometries on a metric space `X`, and fix a centre `p : X`. The
**Dirichlet domain** of `p` is the set of points at least as close to `p` as to every other point
of its orbit,
`{x | ∀ g : G, dist x p ≤ dist x (g • p)}`.

For a properly discontinuous action on a proper space, every orbit meets the Dirichlet domain:
the orbit of `p` has only finitely many points in each closed ball, so the distance from a point
to the orbit of `p` is attained. If two translates of the Dirichlet domain meet, every common
point is equidistant from the two corresponding translates of `p`. Consequently, when the centre
has trivial stabilizer and the equidistant set of any two distinct orbit points is null, the
Dirichlet domain is a measurable fundamental domain. In the hyperbolic plane these equidistant
sets are geodesics, which is how the Dirichlet polygon of a Fuchsian group arises.

## Main declarations

* `TauCeti.dirichletDomain G p`: the Dirichlet domain of the centre `p`.
* `TauCeti.isClosed_dirichletDomain`: it is closed.
* `TauCeti.smul_dirichletDomain`: translating the Dirichlet domain translates its centre.
* `TauCeti.finite_dirichletCompetitors`: on a bounded set, only finitely many acting elements can
  move the centre to a point at least as close as the centre.
* `TauCeti.exists_finset_dirichletDomain_inter_eq`: on a bounded set, the Dirichlet domain is
  cut out by finitely many of its defining inequalities.
* `TauCeti.exists_smul_mem_dirichletDomain`: for a properly discontinuous isometric action on a
  proper space, every orbit meets it.
* `TauCeti.dirichletDomain_inter_dirichletDomain_smul_subset`: the Dirichlet domains of two
  points of one orbit meet only in points equidistant from them.
* `TauCeti.isFundamentalDomain_dirichletDomain`: it is a fundamental domain when the centre has
  trivial stabilizer and equidistant sets of distinct orbit points are null.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §3.2.
-/

public section

open MeasureTheory Metric MulAction Set

open scoped Pointwise

namespace TauCeti

variable (G : Type*) {X : Type*} [PseudoMetricSpace X]

section SMul

variable [SMul G X]

/-- The **Dirichlet domain** of a centre `p`: the points at least as close to `p` as to every
point `g • p` of its orbit. -/
def dirichletDomain (p : X) : Set X :=
  {x | ∀ g : G, dist x p ≤ dist x (g • p)}

variable {G}

/-- Membership in a Dirichlet domain, unfolded. -/
@[simp]
theorem mem_dirichletDomain {p x : X} :
    x ∈ dirichletDomain G p ↔ ∀ g : G, dist x p ≤ dist x (g • p) :=
  Iff.rfl

/-- The centre lies in its Dirichlet domain. -/
theorem self_mem_dirichletDomain (p : X) : p ∈ dirichletDomain G p := fun g ↦ by
  simp [dist_nonneg]

variable (G) in
/-- A Dirichlet domain is closed, being an intersection of closed sets. -/
theorem isClosed_dirichletDomain (p : X) : IsClosed (dirichletDomain G p) := by
  simp_rw [dirichletDomain, ofPred_forall]
  exact isClosed_iInter fun g ↦ isClosed_le (continuous_id.dist continuous_const)
    (continuous_id.dist continuous_const)

variable (G) in
/-- A Dirichlet domain is measurable. -/
theorem measurableSet_dirichletDomain [MeasurableSpace X] [OpensMeasurableSpace X] (p : X) :
    MeasurableSet (dirichletDomain G p) :=
  (isClosed_dirichletDomain G p).measurableSet

variable (G) in
/-- The acting elements whose images of `p` compete with `p` somewhere on `K`: for some
`x ∈ K`, the point `g • p` is at least as close to `x` as `p` is. Equivalently, these are the
`g` whose defining inequality of the Dirichlet domain does not hold strictly everywhere on `K`.
Every constraint that cuts into `K` is indexed by a competitor, but a competitor's constraint
may still be redundant. -/
def dirichletCompetitors (p : X) (K : Set X) : Set G :=
  {g | ∃ x ∈ K, dist x (g • p) ≤ dist x p}

/-- Membership in the set of competitors of a Dirichlet centre on a set. -/
@[simp]
theorem mem_dirichletCompetitors {p : X} {K : Set X} {g : G} :
    g ∈ dirichletCompetitors G p K ↔ ∃ x ∈ K, dist x (g • p) ≤ dist x p :=
  Iff.rfl

/-- **Only finitely many acting elements compete with a Dirichlet centre on a bounded set.**
For a properly discontinuous action on a proper metric space, a bounded set `K`
meets the region where `g • p` is at least as close as `p` for only finitely many `g`. -/
theorem finite_dirichletCompetitors [ProperSpace X] [ProperlyDiscontinuousSMul G X] (p : X)
    {K : Set X} (hK : Bornology.IsBounded K) : (dirichletCompetitors G p K).Finite := by
  -- If `K ⊆ closedBall p r`, every competing `g • p` lies in `closedBall p (2 * r)`.
  obtain ⟨r, hr⟩ := hK.subset_closedBall p
  refine (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (K := {p})
    (L := closedBall p (2 * r)) isCompact_singleton (isCompact_closedBall p (2 * r))).subset ?_
  intro g hg
  obtain ⟨x, hxK, hxg⟩ := hg
  refine ⟨g • p, ⟨⟨p, Set.mem_singleton p, rfl⟩, ?_⟩⟩
  have hxp : dist x p ≤ r := hr hxK
  rw [mem_closedBall, dist_comm]
  calc
    dist p (g • p) ≤ dist p x + dist x (g • p) := dist_triangle _ _ _
    _ ≤ r + r := add_le_add (by simpa [dist_comm] using hxp) (hxg.trans hxp)
    _ = 2 * r := by ring

/-- **A Dirichlet domain has finitely many defining inequalities on every bounded set.**
For a bounded `K`, there is a finite set `s` of acting elements such that intersecting `K` with
the full Dirichlet domain is the same as imposing only the inequalities indexed by `s` on `K`.
This is the local-finiteness input for viewing Dirichlet domains as locally finite intersections
of the distance-dominance regions `{x | dist x p ≤ dist x (g • p)}`. -/
theorem exists_finset_dirichletDomain_inter_eq [ProperSpace X] [ProperlyDiscontinuousSMul G X]
    (p : X) {K : Set X} (hK : Bornology.IsBounded K) :
    ∃ s : Finset G,
      dirichletDomain G p ∩ K =
        (⋂ g ∈ s, {x | dist x p ≤ dist x (g • p)}) ∩ K := by
  let S := dirichletCompetitors G p K
  have hS : S.Finite := finite_dirichletCompetitors p hK
  refine ⟨hS.toFinset, Set.ext fun x ↦ ?_⟩
  simp only [Set.mem_inter_iff, mem_dirichletDomain, Set.mem_iInter, Set.mem_ofPred_eq,
    hS.mem_toFinset]
  constructor
  · exact fun ⟨hx, hxK⟩ ↦ ⟨fun g _ ↦ hx g, hxK⟩
  · rintro ⟨hx, hxK⟩
    refine ⟨fun g ↦ ?_, hxK⟩
    by_cases hg : g ∈ S
    · exact hx g hg
    · exact le_of_not_ge fun h ↦ hg ⟨x, hxK, h⟩

end SMul

variable {G} [Group G] [MulAction G X]

/-- The Dirichlet domains of two points of one orbit meet only in points equidistant from
them. -/
theorem dirichletDomain_inter_dirichletDomain_smul_subset (p : X) (g : G) :
    dirichletDomain G p ∩ dirichletDomain G (g • p) ⊆ {x | dist x p = dist x (g • p)} :=
  fun _ ⟨hp, hgp⟩ ↦ le_antisymm (hp g) (by simpa using hgp g⁻¹)

variable [IsIsometricSMul G X]

/-- Translating a Dirichlet domain by a group element gives the Dirichlet domain of the translated
centre. -/
@[simp]
theorem smul_dirichletDomain (g : G) (p : X) :
    g • dirichletDomain G p = dirichletDomain G (g • p) := by
  ext x
  have e (y : X) : dist (g⁻¹ • x) y = dist x (g • y) := by rw [← dist_smul g, smul_inv_smul]
  simp only [mem_smul_set_iff_inv_smul_mem, mem_dirichletDomain, e]
  refine ⟨fun H h ↦ ?_, fun H h ↦ ?_⟩
  · simpa [mul_smul] using H (g⁻¹ * h * g)
  · simpa [mul_smul] using H (g * h * g⁻¹)

variable [ProperSpace X] [ProperlyDiscontinuousSMul G X]

/-- **Every orbit meets the Dirichlet domain.** For a properly discontinuous isometric action on a
proper space, each point has a translate in the Dirichlet domain of any centre: translate it by
the inverse of an element `g` for which `g • p` is a closest point of the orbit of `p`. -/
theorem exists_smul_mem_dirichletDomain (p x : X) : ∃ g : G, g • x ∈ dirichletDomain G p := by
  -- Only finitely many points of the orbit of `p` are at most as far from `x` as `p` is.
  set S := dirichletCompetitors G p {x}
  have hS : S.Finite := finite_dirichletCompetitors p Bornology.isBounded_singleton
  have hmemS {g : G} : g ∈ S ↔ dist x (g • p) ≤ dist x p := by
    simp [S]
  have h1 : (1 : G) ∈ S := hmemS.mpr (by simp)
  obtain ⟨g, hgS, hmin⟩ := exists_min_image S (fun g ↦ dist x (g • p)) hS ⟨1, h1⟩
  refine ⟨g⁻¹, fun h ↦ ?_⟩
  calc dist (g⁻¹ • x) p = dist x (g • p) := by
        rw [← dist_smul g, smul_inv_smul]
    _ ≤ dist x ((g * h) • p) := by
        by_cases hh : g * h ∈ S
        · exact hmin _ hh
        · exact (hmemS.mp hgS).trans (not_le.mp (hmemS.not.mp hh)).le
    _ = dist (g⁻¹ • x) (h • p) := by
        rw [← dist_smul g (g⁻¹ • x), smul_inv_smul, mul_smul]

/-- The translates of a Dirichlet domain cover the whole space. -/
theorem iUnion_smul_dirichletDomain (p : X) : ⋃ g : G, g • dirichletDomain G p = univ := by
  refine eq_univ_of_forall fun x ↦ mem_iUnion.mpr ?_
  obtain ⟨g, hg⟩ := exists_smul_mem_dirichletDomain (G := G) p x
  exact ⟨g⁻¹, by rwa [mem_smul_set_iff_inv_smul_mem, inv_inv]⟩

/-- **The Dirichlet domain is a fundamental domain.** For a properly discontinuous isometric
action on a proper space, the Dirichlet domain of a centre with trivial stabilizer is a
fundamental domain for any measure in which the equidistant set of any two distinct points of the
orbit of the centre is null. -/
theorem isFundamentalDomain_dirichletDomain [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) {p : X} (hp : stabilizer G p = ⊥)
    (hμ : ∀ g h : G, g • p ≠ h • p → μ {x | dist x (g • p) = dist x (h • p)} = 0) :
    IsFundamentalDomain G (dirichletDomain G p) μ where
  nullMeasurableSet := (measurableSet_dirichletDomain G p).nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall (exists_smul_mem_dirichletDomain p)
  aedisjoint g h hgh := by
    have hsub : dirichletDomain G (g • p) ∩ dirichletDomain G (h • p) ⊆
        {x | dist x (g • p) = dist x (h • p)} := by
      simpa [smul_smul] using dirichletDomain_inter_dirichletDomain_smul_subset (g • p) (h * g⁻¹)
    rw [Function.onFun, AEDisjoint, smul_dirichletDomain, smul_dirichletDomain]
    refine measure_mono_null hsub (hμ g h fun hgp ↦ hgh ?_)
    have hmem : h⁻¹ * g ∈ stabilizer G p := by
      rw [mem_stabilizer_iff, mul_smul, hgp, inv_smul_smul]
    rw [hp, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hmem.symm

end TauCeti

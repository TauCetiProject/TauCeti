/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The orbit-space metric of an isometric group action

Let a group `G` act by isometries on a pseudometric space `X`. The orbit space
`MulAction.orbitRel.Quotient G X` carries the pseudometric

`dist ⟦x⟧ ⟦y⟧ = ⨅ g : G, dist x (g • y)`,

the distance from `x` to the orbit of `y` (`MulAction.orbitRel.Quotient.dist_mk_mk`). Since `G`
acts by isometries this does not depend on the chosen representatives, it is symmetric, and it
satisfies the triangle inequality. The quotient map is `1`-Lipschitz, and the ball of radius `ε`
about `⟦x⟧` is the image of the ball of radius `ε` about `x`
(`MulAction.orbitRel.Quotient.ball_mk`). As the quotient map is also open, the pseudometric
induces exactly the quotient topology; the instance is built so that its topology is the existing
quotient topology `instTopologicalSpaceQuotient`. Keeping the quotient topology definitionally,
and proving that the metric induces it rather than letting the metric define a new topology,
follows Mathlib's quotient seminorm on normed groups, `QuotientGroup.instSeminormedCommGroup`.

If an orbit is closed, the distance of `⟦x⟧` to its class vanishes only when `x` lies in it
(`MulAction.orbitRel.Quotient.dist_mk_mk_eq_zero_iff`). This applies when `G` is a compact
topological group acting continuously on a metric space: the orbits are then compact, the
infimum is a minimum, `dist ⟦x⟧ ⟦y⟧ = dist x (g • y)` for some `g`
(`MulAction.orbitRel.Quotient.exists_dist_mk_mk_eq`), and the orbit space is a metric space.
Its Hausdorff, paracompactness and, for separable `X`, second-countability properties then follow
from this metric through the general metric-space instances, with no appeal to a metrization
theorem for proper actions.

This is the construction used for configuration spaces in gauge theory, where the gauge group or
its residual circle acts isometrically on a metric space of configurations: the circle orbit
space then carries the metric `min_{c ∈ S¹} d(v, c w)`.

## Main results

* `MulAction.orbitRel.Quotient.instPseudoMetricSpace`: the orbit-space pseudometric of an
  isometric action, inducing the quotient topology.
* `MulAction.orbitRel.Quotient.dist_mk_mk`: `dist ⟦x⟧ ⟦y⟧ = ⨅ g : G, dist x (g • y)`.
* `MulAction.orbitRel.Quotient.dist_mk_mk_le`: the quotient map is `1`-Lipschitz.
* `MulAction.orbitRel.Quotient.ball_mk`: balls in the orbit space are images of balls.
* `MulAction.orbitRel.Quotient.dist_mk_mk_eq_zero_iff`: definiteness at a closed orbit.
* `MulAction.orbitRel.Quotient.exists_dist_mk_mk_eq`: for a compact group the infimum is
  attained.
* `MulAction.orbitRel.Quotient.instMetricSpace`: for a compact group acting continuously on a
  metric space, the orbit space is a metric space.

Each of these has an additive version for additive actions, in `AddAction.orbitRel.Quotient`.

## References

* D. Burago, Yu. Burago and S. Ivanov, *A Course in Metric Geometry*, Graduate Studies in
  Mathematics 33, American Mathematical Society (2001), Section 3.3 (quotients by groups of
  isometries).
-/

public section

noncomputable section

open Metric Set
open scoped Topology

namespace MulAction.orbitRel.Quotient

variable {G X : Type*} [Group G] [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]

/-- The distance from a point to an orbit does not change when the point is moved by `g`. -/
@[to_additive]
private theorem infDist_smul_orbit (g : G) (x y : X) :
    infDist (g • x) (MulAction.orbit G y) = infDist x (MulAction.orbit G y) := by
  have h := infDist_image (x := x) (t := MulAction.orbit G y) (isometry_smul X g)
  rwa [image_smul, MulAction.smul_orbit] at h

/-- The distance from `x` to the orbit of `y` is at most the distance from `y` to the orbit
of `x`. -/
@[to_additive]
private theorem infDist_orbit_le_comm (x y : X) :
    infDist x (MulAction.orbit G y) ≤ infDist y (MulAction.orbit G x) := by
  refine (le_infDist (MulAction.nonempty_orbit x)).2 ?_
  rintro _ ⟨g, rfl⟩
  rw [← infDist_smul_orbit g x y, dist_comm]
  exact infDist_le_dist_of_mem (MulAction.mem_orbit_self y)

/-- The triangle inequality for distances between orbits. -/
@[to_additive]
private theorem infDist_orbit_triangle (x y z : X) :
    infDist x (MulAction.orbit G z) ≤
      infDist x (MulAction.orbit G y) + infDist y (MulAction.orbit G z) := by
  -- Compare with `g • y` for every `g`, then take the infimum over the orbit of `y`.
  rw [← sub_le_iff_le_add]
  refine (le_infDist (MulAction.nonempty_orbit y)).2 ?_
  rintro _ ⟨g, rfl⟩
  have h := infDist_le_infDist_add_dist (x := x) (y := g • y) (s := MulAction.orbit G z)
  rw [infDist_smul_orbit] at h
  linarith

section Aux

/-! The two facts below hold for every pseudometric structure on the orbit space whose distance
is the distance between orbits; they are applied to the instance before and after its topology is
replaced by the quotient topology. -/

variable (m : PseudoMetricSpace (orbitRel.Quotient G X))
  (hm : ∀ x y : X, m.dist ⟦x⟧ ⟦y⟧ = infDist x (MulAction.orbit G y))
include hm

omit [IsIsometricSMul G X] in
@[to_additive]
private theorem ball_mk_aux (x : X) (ε : ℝ) :
    @ball _ m ⟦x⟧ ε = Quotient.mk _ '' ball x ε := by
  ext q
  induction q using Quotient.inductionOn with | h y => ?_
  rw [@mem_ball _ m, @dist_comm _ m, hm]
  constructor
  · intro h
    obtain ⟨_, ⟨g, rfl⟩, hg⟩ := (infDist_lt_iff (MulAction.nonempty_orbit y)).1 h
    exact ⟨g • y, mem_ball.2 (by rwa [dist_comm]), quotient_smul_eq⟩
  · rintro ⟨_, hz, hzy⟩
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (orbitRel_apply.1 (Quotient.exact hzy))
    exact (infDist_le_dist_of_mem (MulAction.mem_orbit y g)).trans_lt
      (by rwa [dist_comm, ← mem_ball])

omit [IsIsometricSMul G X] in
/-- The distance between orbits induces the quotient topology. -/
@[to_additive]
private theorem instTopologicalSpaceQuotient_eq_aux :
    (instTopologicalSpaceQuotient : TopologicalSpace (orbitRel.Quotient G X)) =
      m.toUniformSpace.toTopologicalSpace := by
  ext U
  rw [isOpen_coinduced, @Metric.isOpen_iff _ m, Metric.isOpen_iff]
  constructor
  · -- An open saturated set contains a ball about each point, and balls are images of balls.
    intro hU p hp
    induction p using Quotient.inductionOn with | h x => ?_
    obtain ⟨ε, hε, hball⟩ := hU x hp
    refine ⟨ε, hε, ?_⟩
    rw [ball_mk_aux m hm, image_subset_iff]
    exact hball
  · -- Conversely, the ball about `x` maps into the ball about its orbit.
    intro hU x hx
    obtain ⟨ε, hε, hball⟩ := hU _ hx
    exact ⟨ε, hε, fun y hy ↦ hball <| (ball_mk_aux m hm x ε).symm ▸ mem_image_of_mem _ hy⟩

end Aux

/-- **The orbit-space pseudometric of an isometric action**:
`dist ⟦x⟧ ⟦y⟧ = ⨅ g : G, dist x (g • y)` (`MulAction.orbitRel.Quotient.dist_mk_mk`). Its topology
is the quotient topology of the orbit space. -/
@[to_additive /-- **The orbit-space pseudometric of an isometric additive action**:
`dist ⟦x⟧ ⟦y⟧ = ⨅ g : G, dist x (g +ᵥ y)` (`AddAction.orbitRel.Quotient.dist_mk_mk`). Its topology
is the quotient topology of the orbit space. -/]
instance instPseudoMetricSpace : PseudoMetricSpace (orbitRel.Quotient G X) :=
  PseudoMetricSpace.replaceTopology
    { dist p q := Quotient.liftOn₂' p q (fun x y ↦ infDist x (MulAction.orbit G y))
        fun x₁ y₁ x₂ y₂ hx hy ↦ by
          obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 (orbitRel_apply.1 hx)
          rw [MulAction.orbit_eq_iff.2 (orbitRel_apply.1 hy), infDist_smul_orbit]
      dist_self p := by
        induction p using Quotient.inductionOn with | h x => ?_
        exact infDist_zero_of_mem (MulAction.mem_orbit_self x)
      dist_comm p q := by
        induction p, q using Quotient.inductionOn₂ with | h x y => ?_
        exact (infDist_orbit_le_comm x y).antisymm (infDist_orbit_le_comm y x)
      dist_triangle p q r := by
        induction p, q, r using Quotient.inductionOn₃ with | h x y z => ?_
        exact infDist_orbit_triangle x y z }
    (by exact instTopologicalSpaceQuotient_eq_aux _ fun _ _ ↦ rfl)

/-- The distance between two orbits is the distance from a representative of the first to the
second orbit. -/
@[to_additive /-- The distance between two orbits is the distance from a representative of the
first to the second orbit. -/]
theorem dist_mk_mk_eq_infDist (x y : X) :
    dist (⟦x⟧ : orbitRel.Quotient G X) ⟦y⟧ = infDist x (MulAction.orbit G y) :=
  (rfl)

/-- The distance between two orbits is `⨅ g : G, dist x (g • y)`. -/
@[to_additive /-- The distance between two orbits is `⨅ g : G, dist x (g +ᵥ y)`. -/]
theorem dist_mk_mk (x y : X) :
    dist (⟦x⟧ : orbitRel.Quotient G X) ⟦y⟧ = ⨅ g : G, dist x (g • y) := by
  rw [dist_mk_mk_eq_infDist]
  refine le_antisymm (le_ciInf fun g ↦ infDist_le_dist_of_mem (MulAction.mem_orbit y g)) ?_
  refine (le_infDist (MulAction.nonempty_orbit y)).2 ?_
  rintro _ ⟨g, rfl⟩
  exact ciInf_le ⟨0, by rintro _ ⟨g', rfl⟩; exact dist_nonneg⟩ g

/-- The quotient map to the orbit space does not increase distances. -/
@[to_additive /-- The quotient map to the orbit space does not increase distances. -/]
theorem dist_mk_mk_le (x y : X) : dist (⟦x⟧ : orbitRel.Quotient G X) ⟦y⟧ ≤ dist x y :=
  infDist_le_dist_of_mem (MulAction.mem_orbit_self y)

/-- The ball of radius `ε` about the orbit of `x` is the image of the ball of radius `ε`
about `x`. -/
@[to_additive /-- The ball of radius `ε` about the orbit of `x` is the image of the ball of
radius `ε` about `x`. -/]
theorem ball_mk (x : X) (ε : ℝ) :
    ball (⟦x⟧ : orbitRel.Quotient G X) ε = Quotient.mk _ '' ball x ε :=
  ball_mk_aux _ (fun _ _ ↦ rfl) x ε

/-- At a closed orbit the orbit-space pseudometric is definite: the distance from `⟦x⟧` to
`⟦y⟧` vanishes exactly when `x` and `y` lie in the same orbit. -/
@[to_additive /-- At a closed orbit the orbit-space pseudometric is definite: the distance from
`⟦x⟧` to `⟦y⟧` vanishes exactly when `x` and `y` lie in the same orbit. -/]
theorem dist_mk_mk_eq_zero_iff {x y : X} (hy : IsClosed (MulAction.orbit G y)) :
    dist (⟦x⟧ : orbitRel.Quotient G X) ⟦y⟧ = 0 ↔ (⟦x⟧ : orbitRel.Quotient G X) = ⟦y⟧ := by
  rw [dist_mk_mk_eq_infDist, ← hy.mem_iff_infDist_zero (MulAction.nonempty_orbit y), Quotient.eq,
    orbitRel_apply]

section Compact

variable [TopologicalSpace G] [CompactSpace G] [ContinuousSMul G X]

/-- For a compact group acting continuously, the distance between two orbits is attained:
`dist ⟦x⟧ ⟦y⟧ = dist x (g • y)` for some `g`. -/
@[to_additive /-- For a compact additive group acting continuously, the distance between two
orbits is attained: `dist ⟦x⟧ ⟦y⟧ = dist x (g +ᵥ y)` for some `g`. -/]
theorem exists_dist_mk_mk_eq (x y : X) :
    ∃ g : G, dist (⟦x⟧ : orbitRel.Quotient G X) ⟦y⟧ = dist x (g • y) := by
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ := IsCompact.exists_infDist_eq_dist
    (isCompact_range (by fun_prop : Continuous fun g : G ↦ g • y)) (MulAction.nonempty_orbit y) x
  exact ⟨g, hg⟩

end Compact

/-- **The orbit space of a compact group acting continuously by isometries on a metric space is a
metric space**, with the distance `dist ⟦x⟧ ⟦y⟧ = min_g dist x (g • y)`. -/
@[to_additive /-- **The orbit space of a compact additive group acting continuously by isometries
on a metric space is a metric space**, with the distance `dist ⟦x⟧ ⟦y⟧ = min_g dist x (g +ᵥ y)`.
-/]
instance instMetricSpace {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
    [MetricSpace X] [MulAction G X] [IsIsometricSMul G X] [ContinuousSMul G X] :
    MetricSpace (orbitRel.Quotient G X) where
  eq_of_dist_eq_zero {p q} h := by
    induction p, q using Quotient.inductionOn₂ with | h x y => ?_
    exact (dist_mk_mk_eq_zero_iff
      (isCompact_range (by fun_prop : Continuous fun g : G ↦ g • y)).isClosed).1 h

end MulAction.orbitRel.Quotient

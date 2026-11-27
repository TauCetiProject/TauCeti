/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PhaseSpace
public import TauCeti.Dynamics.Billiard.PolygonalTable.HalfDisc
import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.Frontier
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Billiard trajectories in a polygonal table

A state `(x, v)` of a polygonal table `P`, with position `x ∈ ℂ` and direction `v ∈ Circle`,
*points inward* when `x + t v` lies in the interior of `P` for all small `t > 0`
(`TauCeti.PolygonalTable.PointsInward`). This holds for every direction at an interior point, and
at a point of the relative interior of a side `S` for exactly one of `v` and `σ_S v` when `v` is
not parallel to `S`; a direction parallel to `S` never points inward there.

From an inward state the trajectory moves in a straight line at unit speed through the interior
of `P` for the free flight time `τ(x, v) > 0` (`TauCeti.PolygonalTable.flightTime`), and then hits
the frontier at `y = x + τ v`. If `y` is not a vertex, it lies in the relative interior of exactly
one side `S`, the direction `v` points out of `P` there, and the reflected direction `σ_S v` points
inward again, so the trajectory continues from `(y, σ_S v)`; the two states agree in the phase
space `Z_P`. Iterating gives the collision states `TauCeti.PolygonalTable.collisionState` and the
collision times `TauCeti.PolygonalTable.collisionTime` of the trajectory. This construction models
the billiard only until a collision point is a vertex: there `TauCeti.PolygonalTable.reflectAt`
keeps the direction, and the later collision data has no billiard meaning.

**Accumulation at a vertex.** If the trajectory never reaches a vertex and its collision times
stay bounded, then its collision points converge to a vertex of the table
(`TauCeti.PolygonalTable.PointsInward.exists_mem_vertexSet_tendsto_collisionState`). Hence
infinitely many reflections in bounded time can happen only on the way into a vertex. Route: the
collision points form a Cauchy sequence, since consecutive ones are at distance the free flight
time; near a point of the relative interior of a side the frontier lies in that side, and two
consecutive collision points on the same side would force the straight segment between them,
which runs through the interior, to lie on the side.

## Main definitions

* `TauCeti.PolygonalTable.PointsInward`: the state `(x, v)` points into the interior.
* `TauCeti.PolygonalTable.flightTime`: the free flight time to the frontier.
* `TauCeti.PolygonalTable.hitPoint`: the point where the trajectory hits the frontier.
* `TauCeti.PolygonalTable.reflectAt`: the direction after the reflection at a point of the frontier.
* `TauCeti.PolygonalTable.bounce`: the state after the next reflection.
* `TauCeti.PolygonalTable.collisionState`, `TauCeti.PolygonalTable.collisionTime`: the `n`-th
  collision state and its time.
* `TauCeti.PolygonalTable.reflectionCount`, `TauCeti.PolygonalTable.trajectory`: the number of
  reflections up to time `t`, and the state at time `t`.

## Main results

* `TauCeti.PolygonalTable.PointsInward.flightTime_pos`,
  `TauCeti.PolygonalTable.PointsInward.hitPoint_mem_frontier`,
  `TauCeti.PolygonalTable.PointsInward.add_mul_mem_interior`: the free flight.
* `TauCeti.PolygonalTable.PointsInward.im_conj_direction_mul_ne_zero`,
  `TauCeti.PolygonalTable.PointsInward.pointsInward_directionReflection`: at a hit point in the
  relative interior of a side, the incoming direction is not parallel to the side and the reflected
  direction points inward.
* `TauCeti.PolygonalTable.PointsInward.eventually_add_mul_notMem_carrier`: there the incoming
  direction points out of the table.
* `TauCeti.PolygonalTable.PointsInward.pointsInward_collisionState`: the collision states point
  inward until the trajectory reaches a vertex.
* `TauCeti.PolygonalTable.trajectory_eq`,
  `TauCeti.PolygonalTable.PointsInward.trajectory_mem_interior`,
  `TauCeti.PolygonalTable.tendsto_trajectory_collisionTime_succ`: between collisions the trajectory
  is a straight line at unit speed through the interior, reaching the next collision point.
* `TauCeti.PolygonalTable.PointsInward.exists_mem_vertexSet_tendsto_collisionState`: infinitely many
  reflections in bounded time accumulate at a vertex.

## References

* S. Tabachnikov, *Geometry and Billiards*, Chapter 7.
* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
-/

public section

open Set Metric Topology Filter ComplexConjugate

namespace TauCeti

namespace PolygonalTable

variable (T : PolygonalTable)

/-- The state `(x, v)` **points inward**: `x + t v` lies in the interior of the table for all
small `t > 0`. -/
def PointsInward (x : ℂ) (v : Circle) : Prop :=
  ∀ᶠ t : ℝ in 𝓝[>] 0, x + (t : ℂ) * v ∈ interior T.carrier

/-- The **free flight time** of the state `(x, v)`: the infimum of the times `t > 0` at which
`x + t v` lies in the frontier of the table. For an inward state it is positive and attained
(`TauCeti.PolygonalTable.PointsInward.flightTime_pos`,
`TauCeti.PolygonalTable.PointsInward.hitPoint_mem_frontier`); it is `0` when there is no such
time. -/
noncomputable def flightTime (x : ℂ) (v : Circle) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ x + t * (v : ℂ) ∈ frontier T.carrier}

/-- The point `x + τ v` where the straight trajectory of `(x, v)` hits the frontier. -/
noncomputable def hitPoint (x : ℂ) (v : Circle) : ℂ :=
  x + T.flightTime x v * (v : ℂ)

open scoped Classical in
/-- The direction after the reflection at `y`: `σ_S v` when `y` lies in the relative interior of a
side `S`, and `v` otherwise. -/
noncomputable def reflectAt (y : ℂ) (v : Circle) : Circle :=
  if h : ∃ s : T.Side, y ∈ T.sideInterior s then
    Billiard.directionReflection h.choose.direction v
  else v

/-- The state after the next reflection: the hit point of `(x, v)` with the reflected direction. -/
noncomputable def bounce (q : ℂ × Circle) : ℂ × Circle :=
  (T.hitPoint q.1 q.2, T.reflectAt (T.hitPoint q.1 q.2) q.2)

/-- The `n`-th **collision state** of the trajectory of `q`: the state after `n` reflections. -/
noncomputable def collisionState (q : ℂ × Circle) (n : ℕ) : ℂ × Circle :=
  T.bounce^[n] q

/-- The `n`-th **collision time** of the trajectory of `q`: the sum of the first `n` free flight
times. -/
noncomputable def collisionTime (q : ℂ × Circle) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, T.flightTime (T.collisionState q k).1 (T.collisionState q k).2

/-- The number of reflections of the trajectory of `q` up to time `t`: the largest `n` with
`collisionTime q n ≤ t`. This is meaningful only for `0 ≤ t` below the supremum of the collision
times, where such a largest `n` exists; otherwise the value is the junk value `0`. -/
noncomputable def reflectionCount (q : ℂ × Circle) (t : ℝ) : ℕ :=
  sSup {n | T.collisionTime q n ≤ t}

/-- The **trajectory** of `q` at time `t ≥ 0`: after the last reflection before `t`, at the
collision state `(y_n, v_n)` and time `T_n`, the state `(y_n + (t − T_n) v_n, v_n)`. It is the
billiard trajectory for an inward initial state (`PointsInward q.1 q.2`) and `0 ≤ t` below the
supremum of the collision times, as long as no collision point is a vertex. -/
noncomputable def trajectory (q : ℂ × Circle) (t : ℝ) : ℂ × Circle :=
  ((T.collisionState q (T.reflectionCount q t)).1 +
      ((t - T.collisionTime q (T.reflectionCount q t) : ℝ) : ℂ) *
        ((T.collisionState q (T.reflectionCount q t)).2 : ℂ),
    (T.collisionState q (T.reflectionCount q t)).2)

variable {T}

theorem pointsInward_iff (x : ℂ) (v : Circle) :
    T.PointsInward x v ↔ ∀ᶠ t : ℝ in 𝓝[>] 0, x + (t : ℂ) * v ∈ interior T.carrier :=
  Iff.rfl

theorem flightTime_def (x : ℂ) (v : Circle) :
    T.flightTime x v = sInf {t : ℝ | 0 < t ∧ x + t * (v : ℂ) ∈ frontier T.carrier} :=
  (rfl)

theorem hitPoint_def (x : ℂ) (v : Circle) : T.hitPoint x v = x + T.flightTime x v * (v : ℂ) :=
  (rfl)

theorem reflectionCount_def (q : ℂ × Circle) (t : ℝ) :
    T.reflectionCount q t = sSup {n | T.collisionTime q n ≤ t} :=
  (rfl)

theorem trajectory_def (q : ℂ × Circle) (t : ℝ) :
    T.trajectory q t =
      ((T.collisionState q (T.reflectionCount q t)).1 +
          ((t - T.collisionTime q (T.reflectionCount q t) : ℝ) : ℂ) *
            ((T.collisionState q (T.reflectionCount q t)).2 : ℂ),
        (T.collisionState q (T.reflectionCount q t)).2) :=
  (rfl)

theorem reflectAt_of_mem_sideInterior {y : ℂ} {s : T.Side} (hy : y ∈ T.sideInterior s)
    (v : Circle) : T.reflectAt y v = Billiard.directionReflection s.direction v := by
  have h : ∃ s : T.Side, y ∈ T.sideInterior s := ⟨s, hy⟩
  rw [reflectAt, dite_eq_left_of_eq_true (eq_true h)]
  exact congrArg (fun t : T.Side => Billiard.directionReflection t.direction v)
    (T.eq_of_mem_sideInterior h.choose_spec hy)

theorem reflectAt_of_forall_notMem {y : ℂ} (hy : ∀ s : T.Side, y ∉ T.sideInterior s)
    (v : Circle) : T.reflectAt y v = v := by
  rw [reflectAt, dite_eq_right_of_eq_false (eq_false (not_exists.2 hy))]

/-- The reflection at a point of the table does not change the state in the phase space. -/
theorem PhaseSpace.mk_reflectAt (y : T.carrier) (v : Circle) :
    PhaseSpace.mk (y, T.reflectAt y v) = PhaseSpace.mk (y, v) := by
  by_cases h : ∃ s : T.Side, (y : ℂ) ∈ T.sideInterior s
  · obtain ⟨s, hs⟩ := h
    rw [reflectAt_of_mem_sideInterior hs, PhaseSpace.mk_directionReflection hs]
  · rw [reflectAt_of_forall_notMem (not_exists.1 h)]

theorem bounce_fst (q : ℂ × Circle) : (T.bounce q).1 = T.hitPoint q.1 q.2 :=
  (rfl)

theorem bounce_snd (q : ℂ × Circle) :
    (T.bounce q).2 = T.reflectAt (T.hitPoint q.1 q.2) q.2 :=
  (rfl)

@[simp]
theorem collisionState_zero (q : ℂ × Circle) : T.collisionState q 0 = q :=
  (rfl)

/-- The first collision point is the hit point of the initial state. -/
theorem collisionState_one_fst (q : ℂ × Circle) :
    (T.collisionState q 1).1 = T.hitPoint q.1 q.2 :=
  (rfl)

theorem collisionState_succ (q : ℂ × Circle) (n : ℕ) :
    T.collisionState q (n + 1) = T.bounce (T.collisionState q n) :=
  Function.iterate_succ_apply' _ _ _

/-- The next collision point is reached from the current one in a straight line. -/
theorem collisionState_succ_fst (q : ℂ × Circle) (n : ℕ) :
    (T.collisionState q (n + 1)).1 = (T.collisionState q n).1 +
      T.flightTime (T.collisionState q n).1 (T.collisionState q n).2 *
        ((T.collisionState q n).2 : ℂ) := by
  rw [collisionState_succ, bounce_fst, hitPoint_def]

@[simp]
theorem collisionTime_zero (q : ℂ × Circle) : T.collisionTime q 0 = 0 :=
  Finset.sum_range_zero _

theorem collisionTime_succ (q : ℂ × Circle) (n : ℕ) :
    T.collisionTime q (n + 1) = T.collisionTime q n +
      T.flightTime (T.collisionState q n).1 (T.collisionState q n).2 :=
  Finset.sum_range_succ _ _

/-- The free flight time is nonnegative. -/
theorem flightTime_nonneg (x : ℂ) (v : Circle) : 0 ≤ T.flightTime x v :=
  Real.sInf_nonneg fun _ ht => ht.1.le

/-- The collision times are monotone. -/
theorem monotone_collisionTime (q : ℂ × Circle) : Monotone (T.collisionTime q) :=
  monotone_nat_of_le_succ fun n => by
    rw [collisionTime_succ]
    linarith [flightTime_nonneg (T := T) (T.collisionState q n).1 (T.collisionState q n).2]

/-- Between the `n`-th and the `(n+1)`-st collision times the trajectory has made `n`
reflections. -/
theorem reflectionCount_eq {q : ℂ × Circle} {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (T.collisionTime q n) (T.collisionTime q (n + 1))) :
    T.reflectionCount q t = n := by
  refine IsGreatest.csSup_eq ⟨ht.1, fun m hm => ?_⟩
  by_contra! hnm
  exact (lt_of_lt_of_le ht.2 (monotone_collisionTime q hnm)).not_ge hm

/-- **Between two collisions the trajectory moves in a straight line at unit speed with constant
direction.** -/
theorem trajectory_eq {q : ℂ × Circle} {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (T.collisionTime q n) (T.collisionTime q (n + 1))) :
    T.trajectory q t = ((T.collisionState q n).1 +
      ((t - T.collisionTime q n : ℝ) : ℂ) * ((T.collisionState q n).2 : ℂ),
        (T.collisionState q n).2) := by
  rw [trajectory, reflectionCount_eq ht]

/-! ### Inward states and the free flight -/

/-- Every direction points inward at an interior point. -/
theorem pointsInward_of_mem_interior {x : ℂ} (hx : x ∈ interior T.carrier) (v : Circle) :
    T.PointsInward x v := by
  have hT : Tendsto (fun t : ℝ => x + t * (v : ℂ)) (𝓝 0) (𝓝 x) :=
    (by fun_prop : Continuous fun t : ℝ => x + t * (v : ℂ)).tendsto' 0 x (by simp)
  exact (hT.eventually (isOpen_interior.mem_nhds hx)).filter_mono nhdsWithin_le_nhds

/-- The position of an inward state lies in the table. -/
theorem PointsInward.mem_carrier {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    x ∈ T.carrier := by
  have hT : Tendsto (fun t : ℝ => x + t * (v : ℂ)) (𝓝[>] 0) (𝓝 x) :=
    ((by fun_prop : Continuous fun t : ℝ => x + t * (v : ℂ)).tendsto' 0 x (by simp)).mono_left
      nhdsWithin_le_nhds
  exact T.isClosed_carrier.mem_of_tendsto hT (h.mono fun _ ht => interior_subset ht)

/-- An inward state has an initial interval of times `(0, δ)` spent in the interior. -/
theorem PointsInward.exists_Ioo {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, x + t * (v : ℂ) ∈ interior T.carrier := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  exact ⟨δ, hδ, fun t ht => hsub ht⟩

/-- The straight trajectory of an inward state hits the frontier at some positive time. -/
theorem PointsInward.exists_mem_frontier {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    ∃ t : ℝ, 0 < t ∧ x + t * (v : ℂ) ∈ frontier T.carrier := by
  obtain ⟨t₀, hint, ht₀⟩ := (h.and self_mem_nhdsWithin).exists
  obtain ⟨R, hR⟩ := T.isCompact_carrier.isBounded.subset_closedBall 0
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (mem_closedBall_zero_iff.1 (hR h.mem_carrier))
  set t₁ := t₀ + ‖x‖ + R + 1
  have hout : x + t₁ * (v : ℂ) ∉ T.carrier := by
    intro hmem
    have h₁ := mem_closedBall_zero_iff.1 (hR hmem)
    have h₂ : ‖(t₁ : ℂ) * v‖ = t₁ := by
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg]
      have : (0 : ℝ) ≤ t₀ := ht₀.le
      positivity
    have h₃ := norm_sub_norm_le ((t₁ : ℂ) * v) (-x)
    rw [sub_neg_eq_add, norm_neg, h₂, add_comm] at h₃
    have : 0 ≤ ‖x‖ := norm_nonneg x
    linarith
  have ht₀₁ : t₀ ≤ t₁ := by
    have : 0 ≤ ‖x‖ := norm_nonneg x
    simp only [t₁]
    linarith
  have hpre : IsPreconnected ((fun t : ℝ => x + t * (v : ℂ)) '' Icc t₀ t₁) :=
    isPreconnected_Icc.image _ (by fun_prop)
  obtain ⟨_, ⟨t, ht, rfl⟩, hf⟩ := hpre.inter_frontier_nonempty
    ⟨_, ⟨t₀, ⟨le_rfl, ht₀₁⟩, rfl⟩, interior_subset hint⟩ ⟨_, ⟨t₁, ⟨ht₀₁, le_rfl⟩, rfl⟩, hout⟩
  exact ⟨t, lt_of_lt_of_le ht₀ ht.1, hf⟩

/-- The times at which the straight trajectory of an inward state lies in the frontier are bounded
below by a positive time. -/
theorem PointsInward.exists_pos_forall_le {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → x + t * (v : ℂ) ∈ frontier T.carrier → δ ≤ t := by
  obtain ⟨δ, hδ, hint⟩ := h.exists_Ioo
  refine ⟨δ, hδ, fun t ht hf => le_of_not_gt fun htδ => ?_⟩
  exact Set.disjoint_left.1 disjoint_interior_frontier (hint t ⟨ht, htδ⟩) hf

/-- The free flight time of an inward state is positive and attained: the trajectory lies in the
frontier at that time. -/
theorem PointsInward.flightTime_pos_and_hitPoint_mem_frontier {x : ℂ} {v : Circle}
    (h : T.PointsInward x v) :
    0 < T.flightTime x v ∧ T.hitPoint x v ∈ frontier T.carrier := by
  obtain ⟨δ, hδ, hle⟩ := h.exists_pos_forall_le
  have hS : {t : ℝ | 0 < t ∧ x + t * (v : ℂ) ∈ frontier T.carrier} =
      Ici δ ∩ (fun t : ℝ => x + t * (v : ℂ)) ⁻¹' frontier T.carrier := by
    ext t
    exact ⟨fun ⟨ht, hf⟩ => ⟨hle t ht hf, hf⟩, fun ⟨ht, hf⟩ => ⟨lt_of_lt_of_le hδ ht, hf⟩⟩
  have hclosed : IsClosed (Ici δ ∩ (fun t : ℝ => x + t * (v : ℂ)) ⁻¹' frontier T.carrier) :=
    isClosed_Ici.inter (isClosed_frontier.preimage (by fun_prop))
  have hne := h.exists_mem_frontier
  have hmem := hclosed.csInf_mem (hS ▸ hne) ⟨δ, fun t ht => ht.1⟩
  rw [← hS] at hmem
  exact hmem

/-- **The free flight time of an inward state is positive.** -/
theorem PointsInward.flightTime_pos {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    0 < T.flightTime x v :=
  h.flightTime_pos_and_hitPoint_mem_frontier.1

/-- **The straight trajectory of an inward state hits the frontier at its free flight time.** -/
theorem PointsInward.hitPoint_mem_frontier {x : ℂ} {v : Circle} (h : T.PointsInward x v) :
    T.hitPoint x v ∈ frontier T.carrier :=
  h.flightTime_pos_and_hitPoint_mem_frontier.2

/-- The straight trajectory of a state does not meet the frontier before its free flight time. -/
theorem add_mul_notMem_frontier_of_mem_Ioo {x : ℂ} {v : Circle} {t : ℝ}
    (ht : t ∈ Ioo 0 (T.flightTime x v)) : x + t * (v : ℂ) ∉ frontier T.carrier := by
  intro hf
  have hle : T.flightTime x v ≤ t :=
    csInf_le ⟨0, fun s (hs : 0 < s ∧ _) => hs.1.le⟩ (show 0 < t ∧ _ from ⟨ht.1, hf⟩)
  exact hle.not_gt ht.2

/-- **Before its free flight time, the straight trajectory of an inward state runs through the
interior of the table.** -/
theorem PointsInward.add_mul_mem_interior {x : ℂ} {v : Circle} (h : T.PointsInward x v)
    {t : ℝ} (ht : t ∈ Ioo 0 (T.flightTime x v)) : x + t * (v : ℂ) ∈ interior T.carrier := by
  obtain ⟨δ, hδ, hint⟩ := h.exists_Ioo
  have hpre : IsPreconnected ((fun t : ℝ => x + t * (v : ℂ)) '' Ioo 0 (T.flightTime x v)) :=
    isPreconnected_Ioo.image _ (by fun_prop)
  have hdisj : Disjoint ((fun t : ℝ => x + t * (v : ℂ)) '' Ioo 0 (T.flightTime x v))
      (frontier T.carrier) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩
    exact add_mul_notMem_frontier_of_mem_Ioo ht
  have hτ := h.flightTime_pos
  set t₀ := min (δ / 2) (T.flightTime x v / 2)
  have ht₀ : t₀ ∈ Ioo 0 (T.flightTime x v) :=
    ⟨lt_min (half_pos hδ) (half_pos hτ), (min_le_right _ _).trans_lt (half_lt_self hτ)⟩
  have ht₀δ : t₀ ∈ Ioo 0 δ := ⟨ht₀.1, (min_le_left _ _).trans_lt (half_lt_self hδ)⟩
  rcases hpre.subset_interior_or_subset_compl_of_isClosed T.isClosed_carrier hdisj with hs | hs
  · exact hs ⟨t, ht, rfl⟩
  · exact (hs ⟨t₀, ht₀, rfl⟩ (interior_subset (hint t₀ ht₀δ))).elim

/-! ### The reflection at a side -/

/-- The signed rate of change of the distance from a side along the reflected direction is
opposite to that along the original direction. -/
theorem im_conj_direction_mul_directionReflection (s : T.Side) (v : Circle) :
    (conj (s.direction : ℂ) * (Billiard.directionReflection s.direction v : ℂ)).im =
      -(conj (s.direction : ℂ) * (v : ℂ)).im := by
  rw [Billiard.coe_directionReflection, Billiard.sideReflection_apply]
  simp [sq, ← mul_assoc, Circle.conj_coe_mul_self, add_comm]

/-- At a point of the relative interior of a side, a direction points inward exactly when the
table lies on its side of the line through the side: in a half-disc about the point,
`ε · Im (conj d · v) > 0`. -/
theorem pointsInward_iff_of_halfDisc {s : T.Side} {y : ℂ} {r ε : ℝ} (hr : 0 < r)
    (hball : ∀ z ∈ ball y r, z ∈ interior T.carrier ↔ 0 < ε * sideHeight s y z) (v : Circle) :
    T.PointsInward y v ↔ 0 < ε * (conj (s.direction : ℂ) * (v : ℂ)).im := by
  have hmem (t : ℝ) (ht : t ∈ Ioo 0 r) : y + t * (v : ℂ) ∈ ball y r := by
    simpa [dist_eq_norm, abs_of_pos ht.1] using ht.2
  have hh (t : ℝ) : sideHeight s y (y + t * (v : ℂ)) = t * (conj (s.direction : ℂ) * v).im := by
    rw [sideHeight_add_mul, sideHeight_self, zero_add]
  have hIoo : Ioo 0 r ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr
  constructor
  · intro h
    obtain ⟨t, ht, htr⟩ := (h.and hIoo).exists
    have := (hball _ (hmem t htr)).1 ht
    rw [hh] at this
    nlinarith [htr.1]
  · intro hpos
    filter_upwards [hIoo] with t ht
    rw [hball _ (hmem t ht), hh]
    nlinarith [ht.1]

/-- At a point of the relative interior of a side, a direction parallel to the side does not point
inward. -/
theorem not_pointsInward_of_mem_sideInterior {s : T.Side} {y : ℂ} (hy : y ∈ T.sideInterior s)
    {v : Circle} (hv : (conj (s.direction : ℂ) * (v : ℂ)).im = 0) : ¬ T.PointsInward y v := by
  obtain ⟨r, hr, ε, -, hball⟩ := T.exists_halfDisc hy
  rw [pointsInward_iff_of_halfDisc hr (fun z hz => (hball z hz).1), hv, mul_zero]
  exact lt_irrefl 0

/-- **At a point of the relative interior of a side `S`, of a direction `v` not parallel to `S`
and its reflection `σ_S v`, exactly one points inward.** -/
theorem pointsInward_iff_not_pointsInward_directionReflection {s : T.Side} {y : ℂ}
    (hy : y ∈ T.sideInterior s) {v : Circle} (hv : (conj (s.direction : ℂ) * (v : ℂ)).im ≠ 0) :
    T.PointsInward y v ↔ ¬ T.PointsInward y (Billiard.directionReflection s.direction v) := by
  obtain ⟨r, hr, ε, hε, hball⟩ := T.exists_halfDisc hy
  have hball' z (hz : z ∈ ball y r) := (hball z hz).1
  rw [pointsInward_iff_of_halfDisc hr hball', pointsInward_iff_of_halfDisc hr hball',
    im_conj_direction_mul_directionReflection, not_lt, mul_neg, neg_nonpos]
  have hε0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (mul_ne_zero hε0 hv).symm⟩

/-- The incoming direction at the hit point lies strictly on the outer side of the line through
the side hit: in a half-disc about the hit point, `ε · Im (conj d · v) < 0`. -/
theorem PointsInward.mul_im_neg_of_halfDisc {x : ℂ} {v : Circle} (h : T.PointsInward x v)
    {s : T.Side} {r ε : ℝ} (hr : 0 < r)
    (hball : ∀ z ∈ ball (T.hitPoint x v) r, z ∈ interior T.carrier →
      0 < ε * sideHeight s (T.hitPoint x v) z) :
    ε * (conj (s.direction : ℂ) * (v : ℂ)).im < 0 := by
  have hτ := h.flightTime_pos
  set t := min (T.flightTime x v) r / 2
  have ht : 0 < t := half_pos (lt_min hτ hr)
  have htτ : t < T.flightTime x v := (half_lt_self (lt_min hτ hr)).trans_le (min_le_left _ _)
  have htr : t < r := (half_lt_self (lt_min hτ hr)).trans_le (min_le_right _ _)
  have hint := h.add_mul_mem_interior (t := T.flightTime x v - t) ⟨by linarith, by linarith⟩
  have heq : x + ((T.flightTime x v - t : ℝ) : ℂ) * (v : ℂ) =
      T.hitPoint x v + ((-t : ℝ) : ℂ) * (v : ℂ) := by
    rw [hitPoint_def]
    push_cast
    ring
  rw [heq] at hint
  have hmem : T.hitPoint x v + ((-t : ℝ) : ℂ) * (v : ℂ) ∈ ball (T.hitPoint x v) r :=
    by simpa [dist_eq_norm, abs_of_pos ht] using htr
  have := hball _ hmem hint
  rw [sideHeight_add_mul, sideHeight_self, zero_add] at this
  nlinarith

/-- **At a hit point in the relative interior of a side, the incoming direction points out of the
table.** -/
theorem PointsInward.eventually_add_mul_notMem_carrier {x : ℂ} {v : Circle}
    (h : T.PointsInward x v) {s : T.Side} (hy : T.hitPoint x v ∈ T.sideInterior s) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, T.hitPoint x v + (t : ℂ) * v ∉ T.carrier := by
  obtain ⟨r, hr, ε, -, hball⟩ := T.exists_halfDisc hy
  have hneg := h.mul_im_neg_of_halfDisc hr fun z hz => (hball z hz).1.1
  filter_upwards [Ioo_mem_nhdsGT hr] with t ht
  have hmem : T.hitPoint x v + t * (v : ℂ) ∈ ball (T.hitPoint x v) r := by
    simpa [dist_eq_norm, abs_of_pos ht.1] using ht.2
  rw [(hball _ hmem).2, sideHeight_add_mul, sideHeight_self, zero_add, not_le]
  nlinarith [ht.1]

/-- At a hit point in the relative interior of a side `S`, the incoming direction is not parallel
to `S`. -/
theorem PointsInward.im_conj_direction_mul_ne_zero {x : ℂ} {v : Circle}
    (h : T.PointsInward x v) {s : T.Side} (hy : T.hitPoint x v ∈ T.sideInterior s) :
    (conj (s.direction : ℂ) * (v : ℂ)).im ≠ 0 := by
  obtain ⟨r, hr, ε, -, hball⟩ := T.exists_halfDisc hy
  have hneg := h.mul_im_neg_of_halfDisc hr fun z hz => (hball z hz).1.1
  exact fun h0 => by simp [h0] at hneg

/-- **The reflection law.** At a hit point in the relative interior of a side `S`, the reflected
direction `σ_S v` points into the table. -/
theorem PointsInward.pointsInward_directionReflection {x : ℂ} {v : Circle}
    (h : T.PointsInward x v) {s : T.Side} (hy : T.hitPoint x v ∈ T.sideInterior s) :
    T.PointsInward (T.hitPoint x v) (Billiard.directionReflection s.direction v) := by
  obtain ⟨r, hr, ε, -, hball⟩ := T.exists_halfDisc hy
  have hneg := h.mul_im_neg_of_halfDisc hr fun z hz => (hball z hz).1.1
  rw [pointsInward_iff_of_halfDisc hr fun z hz => (hball z hz).1,
    im_conj_direction_mul_directionReflection]
  linarith

/-- If an inward state does not hit a vertex, the state after the reflection points inward. -/
theorem PointsInward.bounce {q : ℂ × Circle} (h : T.PointsInward q.1 q.2)
    (hv : T.hitPoint q.1 q.2 ∉ T.vertexSet) : T.PointsInward (T.bounce q).1 (T.bounce q).2 := by
  obtain ⟨s, hs, -⟩ := T.existsUnique_mem_sideInterior h.hitPoint_mem_frontier hv
  rw [bounce_fst, bounce_snd, reflectAt_of_mem_sideInterior hs]
  exact h.pointsInward_directionReflection hs

/-! ### Collision sequences -/

/-- **Until the trajectory reaches a vertex, its collision states point inward.** -/
theorem PointsInward.pointsInward_collisionState {q : ℂ × Circle} (h : T.PointsInward q.1 q.2)
    {n : ℕ} (hv : ∀ k < n, (T.collisionState q (k + 1)).1 ∉ T.vertexSet) :
    T.PointsInward (T.collisionState q n).1 (T.collisionState q n).2 := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have ih' := ih fun k hk => hv k (hk.trans (Nat.lt_succ_self n))
    have hvn := hv n (Nat.lt_succ_self n)
    rw [collisionState_succ] at hvn ⊢
    exact ih'.bounce hvn

/-- The collision points after the start lie in the frontier, until the trajectory reaches a
vertex. -/
theorem PointsInward.collisionState_succ_mem_frontier {q : ℂ × Circle}
    (h : T.PointsInward q.1 q.2) {n : ℕ}
    (hv : ∀ k < n, (T.collisionState q (k + 1)).1 ∉ T.vertexSet) :
    (T.collisionState q (n + 1)).1 ∈ frontier T.carrier := by
  rw [collisionState_succ]
  exact (h.pointsInward_collisionState hv).hitPoint_mem_frontier

/-- Until the trajectory reaches a vertex, its collision times are strictly increasing. -/
theorem PointsInward.collisionTime_lt_succ {q : ℂ × Circle} (h : T.PointsInward q.1 q.2) {n : ℕ}
    (hv : ∀ k < n, (T.collisionState q (k + 1)).1 ∉ T.vertexSet) :
    T.collisionTime q n < T.collisionTime q (n + 1) := by
  rw [collisionTime_succ]
  linarith [(h.pointsInward_collisionState hv).flightTime_pos]

/-- If the trajectory never reaches a vertex, its collision times are strictly increasing. -/
theorem PointsInward.strictMono_collisionTime {q : ℂ × Circle} (h : T.PointsInward q.1 q.2)
    (hv : ∀ n, (T.collisionState q (n + 1)).1 ∉ T.vertexSet) :
    StrictMono (T.collisionTime q) :=
  strictMono_nat_of_lt_succ fun _ => h.collisionTime_lt_succ fun k _ => hv k

/-- **Accumulation at a vertex.** If the trajectory of an inward state never reaches a vertex and
its collision times are bounded, then its collision points converge to a vertex of the table. So
infinitely many reflections in bounded time can happen only on the way into a vertex. -/
theorem PointsInward.exists_mem_vertexSet_tendsto_collisionState {q : ℂ × Circle}
    (h : T.PointsInward q.1 q.2) (hv : ∀ n, (T.collisionState q (n + 1)).1 ∉ T.vertexSet)
    (hB : BddAbove (range (T.collisionTime q))) :
    ∃ c ∈ T.vertexSet, Tendsto (fun n => (T.collisionState q n).1) atTop (𝓝 c) := by
  have hin (n : ℕ) := h.pointsInward_collisionState (n := n) fun k _ => hv k
  set τ : ℕ → ℝ := fun n => T.flightTime (T.collisionState q n).1 (T.collisionState q n).2
  obtain ⟨C, hC⟩ := hB
  have hsum : Summable τ :=
    summable_of_sum_range_le (fun n => (hin n).flightTime_pos.le)
      fun n => hC (mem_range_self n)
  have hdist (n : ℕ) : dist (T.collisionState q n).1 (T.collisionState q n.succ).1 ≤ τ n := by
    rw [collisionState_succ_fst]
    simp [τ, dist_eq_norm, abs_of_pos (hin n).flightTime_pos]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable τ hdist hsum)
  have hfr : ∀ n, (T.collisionState q (n + 1)).1 ∈ frontier T.carrier := fun n =>
    h.collisionState_succ_mem_frontier fun k _ => hv k
  have hc1 : Tendsto (fun n => (T.collisionState q (n + 1)).1) atTop (𝓝 c) :=
    (tendsto_add_atTop_iff_nat 1).2 hc
  have hcf : c ∈ frontier T.carrier :=
    isClosed_frontier.mem_of_tendsto hc1 (Eventually.of_forall hfr)
  refine ⟨c, by_contra fun hcv => ?_, hc⟩
  obtain ⟨s, hs, -⟩ := T.existsUnique_mem_sideInterior hcf hcv
  obtain ⟨r, hr, hrf⟩ := T.exists_ball_inter_frontier_subset_side hs
  obtain ⟨N, hN⟩ :=
    (hc1.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).exists_forall_of_atTop
  -- Two consecutive collision points near `c` lie on the side `s`, and so does the straight
  -- segment between them, which runs through the interior.
  have h₁ : (T.collisionState q (N + 1)).1 ∈ T.side s := hrf ⟨hN N le_rfl, hfr N⟩
  have h₂ : (T.collisionState q (N + 1 + 1)).1 ∈ T.side s := hrf ⟨hN (N + 1) N.le_succ, hfr _⟩
  have hτ := (hin (N + 1)).flightTime_pos
  have hmid := (hin (N + 1)).add_mul_mem_interior (t := τ (N + 1) / 2)
    ⟨half_pos hτ, half_lt_self hτ⟩
  have hseg : (T.collisionState q (N + 1)).1 + ((τ (N + 1) / 2 : ℝ) : ℂ) *
      ((T.collisionState q (N + 1)).2 : ℂ) ∈ T.side s := by
    rw [side_eq_segment] at h₁ h₂ ⊢
    refine (convex_segment _ _).segment_subset h₁ h₂ ?_
    rw [segment_eq_image']
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    simp only [collisionState_succ_fst (n := N + 1), add_sub_cancel_left, Complex.real_smul, τ]
    push_cast
    ring
  exact Set.disjoint_left.1 disjoint_interior_frontier hmid (T.side_subset_frontier s hseg)

/-! ### The trajectory as a function of time -/

/-- At a collision time before the next collision, the trajectory is at the collision state. -/
theorem trajectory_collisionTime {q : ℂ × Circle} {n : ℕ}
    (hn : T.collisionTime q n < T.collisionTime q (n + 1)) :
    T.trajectory q (T.collisionTime q n) = T.collisionState q n := by
  rw [trajectory_eq ⟨le_rfl, hn⟩, sub_self, Complex.ofReal_zero, zero_mul, add_zero]

/-- **Between two collisions an inward trajectory runs through the interior of the table.** -/
theorem PointsInward.trajectory_mem_interior {q : ℂ × Circle} (h : T.PointsInward q.1 q.2)
    {n : ℕ} (hv : ∀ k < n, (T.collisionState q (k + 1)).1 ∉ T.vertexSet) {t : ℝ}
    (ht : t ∈ Ioo (T.collisionTime q n) (T.collisionTime q (n + 1))) :
    (T.trajectory q t).1 ∈ interior T.carrier := by
  rw [trajectory_eq (Ioo_subset_Ico_self ht)]
  refine (h.pointsInward_collisionState hv).add_mul_mem_interior ⟨sub_pos.2 ht.1, ?_⟩
  rw [sub_lt_iff_lt_add', ← collisionTime_succ]
  exact ht.2

/-- **Reflection continuation.** Approaching the `(n+1)`-st collision time from the left, the
position of the trajectory tends to the `(n+1)`-st collision point. -/
theorem tendsto_trajectory_collisionTime_succ (q : ℂ × Circle) (n : ℕ)
    (hn : T.collisionTime q n < T.collisionTime q (n + 1)) :
    Tendsto (fun t => (T.trajectory q t).1) (𝓝[<] (T.collisionTime q (n + 1)))
      (𝓝 (T.collisionState q (n + 1)).1) := by
  have hc : Continuous fun t : ℝ => (T.collisionState q n).1 +
      ((t - T.collisionTime q n : ℝ) : ℂ) * ((T.collisionState q n).2 : ℂ) := by fun_prop
  have hlim := (hc.tendsto (T.collisionTime q (n + 1))).mono_left
    (nhdsWithin_le_nhds (s := Iio (T.collisionTime q (n + 1))))
  have hval : (T.collisionState q n).1 + ((T.collisionTime q (n + 1) - T.collisionTime q n : ℝ) :
      ℂ) * ((T.collisionState q n).2 : ℂ) = (T.collisionState q (n + 1)).1 := by
    rw [collisionTime_succ, add_sub_cancel_left, ← collisionState_succ_fst]
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hn] with t ht
  rw [trajectory_eq (Ioo_subset_Ico_self ht)]

/-- At a collision with a point of the relative interior of a side, the trajectory replaces the
incoming direction `v_n` by the reflected direction; the two states agree in the phase space
(`TauCeti.PolygonalTable.PhaseSpace.mk_reflectAt`). -/
theorem collisionState_succ_snd_of_mem_sideInterior {q : ℂ × Circle} {n : ℕ} {s : T.Side}
    (hs : (T.collisionState q (n + 1)).1 ∈ T.sideInterior s) :
    (T.collisionState q (n + 1)).2 =
      Billiard.directionReflection s.direction (T.collisionState q n).2 := by
  rw [collisionState_succ] at hs ⊢
  exact reflectAt_of_mem_sideInterior hs _

end PolygonalTable

end TauCeti

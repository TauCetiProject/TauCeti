/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit

/-!
# The closed orbits of the suspension flow are the periodic orbits of the monodromy

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism with smooth mapping torus `Y_φ` and suspension flow
`[t, x] ↦ [t + s, x]` (`TauCeti.SmoothMappingTorus.flow`). This file identifies the closed orbits of
this flow, in the sense of the general theory of closed orbits of real flows
(`Flow.ClosedOrbit`: periodic trajectories up to rotation, with period, minimal period,
multiplicity and support), with the periodic points of `φ`, and records which of the numerical
invariants attached to them coincide.

No point of `Y_φ` is a rest point of the suspension flow, and the periods of the point `[t, x]` are
the integer multiples of the least period of `x` under `φ`, so the minimal period of `[t, x]` under
the flow is the least period of `x` (`TauCeti.SmoothMappingTorus.minimalPeriod_flow_mk`). For a
point `x` of positive period `d`, the trajectory through `[0, x]` with return time `d` is a closed
orbit `TauCeti.SmoothMappingTorus.flowClosedOrbit φ h hd` of the flow. Its period is `d`, its
minimal period is the least period `m` of `x`, its support is the image of the parametrization
`TauCeti.SmoothMappingTorus.closedOrbit φ h` of `ℝ / dℤ`, and its multiplicity, the covering degree
over the underlying simple loop, is `d / m` (for `M` locally compact and Hausdorff, where the
general theory of multiplicities applies). It is primitive exactly when `d = m`, and its underlying
primitive closed orbit is the closed orbit through `x` of period `m`. The `k`-fold iterate of the
closed orbit of period `d` is the closed orbit of period `k d` through the same point. Conversely
every closed orbit of the suspension flow arises in this way, with a positive integer period
(`TauCeti.SmoothMappingTorus.exists_flowClosedOrbit_eq`), and two of these closed orbits agree
exactly when they have the same period and their points lie on one orbit of `φ`
(`TauCeti.SmoothMappingTorus.flowClosedOrbit_eq_flowClosedOrbit_iff`).

So in the suspension coordinates the real period of a closed orbit is a positive integer (the flow
covers the unit-speed rotation of the base circle `ℝ / ℤ`), its minimal period is the least period
of the underlying periodic orbit of `φ`, and its multiplicity is the quotient of the two; the
multiplicity is not the period. In particular the closed orbits of period `N` are the
`φ`-orbits of the fixed points of `φ^[N]`, and the closed orbit of period `N` through `x` is hit by
exactly the `m = N / p` fixed points of `φ^[N]` on the orbit of `x`, where `p` is its multiplicity
(`TauCeti.SmoothMappingTorus.card_flowClosedOrbitOfFixedPt_preimage`). Summing over these
fibres converts sums over the fixed points of `φ^[N]` into sums over the closed orbits of period
`N`, each weighted by `N / p` (`TauCeti.SmoothMappingTorus.finsum_flowClosedOrbitOfFixedPt`). Over
a division ring of characteristic zero this is

`∑_{γ, period N} f(γ) / p(γ) = (1 / N) ∑_{φ^[N] x = x} f(γ_x)`

(`TauCeti.SmoothMappingTorus.finsum_div_multiplicity_eq`), the identity that matches the orbit sum
`∑_γ ε(γ) / p(γ) · e^[γ]` of the dynamical zeta function of a flow with the Lefschetz fixed-point
sums `∑_N (1 / N) ∑_{φ^[N] x = x} ε(x) e^[γ_x]` of the iterates of its return map.

## Main definitions

* `TauCeti.SmoothMappingTorus.periodicTrajectory φ h hd`: the periodic trajectory of the
  suspension flow through `[0, x]` with return time `d`.
* `TauCeti.SmoothMappingTorus.flowClosedOrbit φ h hd`: its closed orbit.
* `TauCeti.SmoothMappingTorus.flowClosedOrbitOfFixedPt φ hN`: the map from the fixed points of
  `φ^[N]` to the closed orbits of period `N`.

## Main results

* `TauCeti.SmoothMappingTorus.periods_flow_mk`,
  `TauCeti.SmoothMappingTorus.minimalPeriod_flow_mk`: the periods and the minimal period of
  `[t, x]` under the suspension flow.
* `TauCeti.SmoothMappingTorus.period_flowClosedOrbit`,
  `TauCeti.SmoothMappingTorus.minimalPeriod_flowClosedOrbit`,
  `TauCeti.SmoothMappingTorus.support_flowClosedOrbit`,
  `TauCeti.SmoothMappingTorus.multiplicity_mul_minimalPeriod_flowClosedOrbit`,
  `TauCeti.SmoothMappingTorus.isPrimitive_flowClosedOrbit_iff`,
  `TauCeti.SmoothMappingTorus.primitive_flowClosedOrbit`: the invariants of the closed orbit
  through a periodic point.
* `TauCeti.SmoothMappingTorus.exists_flowClosedOrbit_eq`: every closed orbit of the suspension
  flow is the closed orbit through a periodic point of `φ`.
* `TauCeti.SmoothMappingTorus.flowClosedOrbit_eq_flowClosedOrbit_iff`: when two of these closed
  orbits agree.
* `TauCeti.SmoothMappingTorus.flowClosedOrbitOfFixedPt_surjective`,
  `TauCeti.SmoothMappingTorus.image_val_flowClosedOrbitOfFixedPt_preimage`: every closed orbit of
  period `N` passes through a fixed point of `φ^[N]`, and the fixed points on it form one
  `φ`-orbit.
* `TauCeti.SmoothMappingTorus.card_flowClosedOrbitOfFixedPt_preimage`,
  `TauCeti.SmoothMappingTorus.finsum_flowClosedOrbitOfFixedPt`,
  `TauCeti.SmoothMappingTorus.finsum_div_multiplicity_eq`: counting the fixed points of `φ^[N]`
  by the closed orbits of period `N`.

## References

* D. Fried, *Lefschetz formulas for flows*, Contemp. Math. 58, Part III (1987), 19–69.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861–888.
-/

public noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

namespace SmoothMappingTorus

variable {φ : M ≃ₘ^n⟮I, I⟯ M} {d e N : ℕ} {x y : M}

/-! ### Periods of points under the suspension flow -/

/-- The periods of `[t, x]` under the suspension flow are the integer multiples of the least period
of `x` under `φ`. -/
@[simp]
theorem periods_flow_mk (t : ℝ) (x : M) :
    (flow φ).periods (mk φ t x) = AddSubgroup.zmultiples (minimalPeriod φ x : ℝ) := by
  ext s
  rw [Flow.mem_periods]
  exact isFixedPt_flow_mk_iff_mem_zmultiples (φ := φ)

/-! ### The closed orbit through a periodic point -/

variable (φ) in
/-- The periodic trajectory of the suspension flow through `[0, x]` with return time `d`, for a
point `x` of positive period `d` under `φ`. -/
def periodicTrajectory (h : IsPeriodicPt φ d x) (hd : 0 < d) : (flow φ).PeriodicTrajectory where
  point := mk φ 0 x
  period := d
  period_pos := Nat.cast_pos.2 hd
  apply_period := by
    rw [flow_mk]
    exact periodic_mk h 0
  exists_apply_ne := exists_flow_ne _

@[simp]
theorem point_periodicTrajectory (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (periodicTrajectory φ h hd).point = mk φ 0 x :=
  (rfl)

@[simp]
theorem period_periodicTrajectory (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (periodicTrajectory φ h hd).period = d :=
  (rfl)

variable (φ) in
/-- The closed orbit of the suspension flow through `[0, x]` with period `d`, for a point `x` of
positive period `d` under `φ`: the trajectory `TauCeti.SmoothMappingTorus.periodicTrajectory` up
to rotation. Its parametrization by `ℝ / dℤ` is `TauCeti.SmoothMappingTorus.closedOrbit φ h`. -/
def flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) : (flow φ).ClosedOrbit :=
  .mk (periodicTrajectory φ h hd)

theorem flowClosedOrbit_def (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    flowClosedOrbit φ h hd = .mk (periodicTrajectory φ h hd) :=
  (rfl)

/-- The period of the closed orbit through a point of period `d` is `d`. -/
@[simp]
theorem period_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (flowClosedOrbit φ h hd).period = d := by
  rw [flowClosedOrbit_def, Flow.ClosedOrbit.period_mk, period_periodicTrajectory]

/-- The support of the closed orbit through a point `x` of period `d` is the image of its
parametrization `ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`. -/
@[simp]
theorem support_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (flowClosedOrbit φ h hd).support = range (closedOrbit φ h) := by
  rw [flowClosedOrbit_def, Flow.ClosedOrbit.support_mk, point_periodicTrajectory,
    range_closedOrbit]

/-- The `k`-fold iterate of the closed orbit through `x` with period `d` is the closed orbit
through `x` with period `k d`. -/
@[simp]
theorem iterate_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) (k : ℕ+) :
    (flowClosedOrbit φ h hd).iterate k = flowClosedOrbit φ (h.const_mul k) (by positivity) := by
  ext
  · rw [Flow.ClosedOrbit.support_iterate, support_flowClosedOrbit, support_flowClosedOrbit,
      range_closedOrbit, range_closedOrbit]
  · simp

/-- Two closed orbits through periodic points of `φ` agree exactly when they have the same period
and their points lie on one orbit of `φ`. -/
theorem flowClosedOrbit_eq_flowClosedOrbit_iff (h : IsPeriodicPt φ d x) (hd : 0 < d)
    (h' : IsPeriodicPt φ e y) (he : 0 < e) :
    flowClosedOrbit φ h hd = flowClosedOrbit φ h' he ↔ d = e ∧ ∃ k : ℤ, (φ ^ k) x = y := by
  have : Fact (0 < (d : ℝ)) := ⟨Nat.cast_pos.2 hd⟩
  have hx : x ∈ periodicPts φ := ⟨d, hd, h⟩
  -- Equality of the images is equality of the `φ`-orbits.
  have hrange : range (closedOrbit φ h) = range (closedOrbit φ h') ↔ ∃ k : ℤ, (φ ^ k) x = y := by
    rw [range_closedOrbit_eq_iff h h', Diffeomorph.exists_zpow_apply_eq_iff hx]
    refine ⟨fun ⟨j, hj⟩ ↦ ?_, fun ⟨j, _, hj⟩ ↦ ⟨j, hj⟩⟩
    refine ⟨j % minimalPeriod φ x, Nat.mod_lt _ (minimalPeriod_pos_of_mem_periodicPts hx), ?_⟩
    rw [iterate_mod_minimalPeriod_eq, hj]
  constructor
  · intro heq
    have hper := congrArg Flow.ClosedOrbit.period heq
    have hsupp := congrArg Flow.ClosedOrbit.support heq
    rw [period_flowClosedOrbit, period_flowClosedOrbit, Nat.cast_inj] at hper
    rw [support_flowClosedOrbit, support_flowClosedOrbit] at hsupp
    exact ⟨hper, hrange.1 hsupp⟩
  · rintro ⟨rfl, hk⟩
    ext
    · rw [support_flowClosedOrbit, support_flowClosedOrbit, hrange.2 hk]
    · simp

/-- Every closed orbit of the suspension flow is the closed orbit through a point `x` of `φ` of
some positive period `d`. In particular its period is a positive integer. -/
theorem exists_flowClosedOrbit_eq (γ : (flow φ).ClosedOrbit) :
    ∃ (x : M) (d : ℕ) (h : IsPeriodicPt φ d x) (hd : 0 < d), flowClosedOrbit φ h hd = γ := by
  induction γ using Flow.ClosedOrbit.ind with | h τ => ?_
  obtain ⟨⟨t, x⟩, hz⟩ := uncurry_mk_surjective φ τ.point
  simp only [uncurry_apply_pair] at hz
  -- The return time of `[t, x]` is a positive multiple `k m` of the least period `m` of `x`.
  have hper := τ.apply_period
  rw [← hz, ← Flow.mem_periods, periods_flow_mk] at hper
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hper
  rw [zsmul_eq_mul] at hk
  have hm : 0 < minimalPeriod φ x := by
    by_contra hm
    rw [Nat.eq_zero_of_not_pos hm, Nat.cast_zero, mul_zero] at hk
    exact τ.period_pos.ne hk
  have hk₀ : (0 : ℝ) < k := pos_of_mul_pos_left (hk ▸ τ.period_pos) (Nat.cast_nonneg _)
  lift k to ℕ using (by exact_mod_cast hk₀.le)
  have hk₀' : 0 < k := by exact_mod_cast hk₀
  refine ⟨x, k * minimalPeriod φ x, (isPeriodicPt_minimalPeriod φ x).const_mul k,
    Nat.mul_pos hk₀' hm, Flow.ClosedOrbit.mk_eq_mk_iff.2 ⟨-t, ?_⟩⟩
  -- Flowing back by `t` moves the base point to the fibre over `0`.
  ext
  · rw [Flow.PeriodicTrajectory.point_vadd, ← hz, flow_mk, add_neg_cancel,
      point_periodicTrajectory]
  · rw [Flow.PeriodicTrajectory.period_vadd, period_periodicTrajectory, ← hk]
    push_cast
    ring

/-! ### The closed orbits through the fixed points of `φ^[N]` -/

variable (φ) in
/-- For `N > 0`, the closed orbit of period `N` through each fixed point of `φ^[N]`, as a closed
orbit of period `N`. -/
def flowClosedOrbitOfFixedPt (hN : 0 < N) (x : {x // IsPeriodicPt φ N x}) :
    {γ : (flow φ).ClosedOrbit // γ.period = N} :=
  ⟨flowClosedOrbit φ x.property hN, period_flowClosedOrbit x.property hN⟩

@[simp]
theorem coe_flowClosedOrbitOfFixedPt (hN : 0 < N) (x : {x // IsPeriodicPt φ N x}) :
    (flowClosedOrbitOfFixedPt φ hN x : (flow φ).ClosedOrbit) = flowClosedOrbit φ x.property hN :=
  (rfl)

/-- Every closed orbit of period `N` passes through a fixed point of `φ^[N]`. -/
theorem flowClosedOrbitOfFixedPt_surjective (hN : 0 < N) :
    Surjective (flowClosedOrbitOfFixedPt φ hN) := by
  rintro ⟨γ, hγ⟩
  obtain ⟨x, d, h, hd, rfl⟩ := exists_flowClosedOrbit_eq γ
  rw [period_flowClosedOrbit, Nat.cast_inj] at hγ
  subst hγ
  exact ⟨⟨x, h⟩, rfl⟩

/-- Two fixed points of `φ^[N]` have the same closed orbit of period `N` exactly when they lie on
one orbit of `φ`. -/
theorem flowClosedOrbitOfFixedPt_eq_iff (hN : 0 < N) {x y : {x // IsPeriodicPt φ N x}} :
    flowClosedOrbitOfFixedPt φ hN y = flowClosedOrbitOfFixedPt φ hN x ↔
      ∃ k : ℤ, (φ ^ k) (x : M) = y := by
  rw [← Subtype.coe_inj, coe_flowClosedOrbitOfFixedPt, coe_flowClosedOrbitOfFixedPt, eq_comm,
    flowClosedOrbit_eq_flowClosedOrbit_iff, and_iff_right rfl]

/-- The fixed points of `φ^[N]` whose closed orbit of period `N` is the one through `x` are the
points of the `φ`-orbit of `x`. -/
theorem image_val_flowClosedOrbitOfFixedPt_preimage (hN : 0 < N) (x : {x // IsPeriodicPt φ N x}) :
    (↑) '' (flowClosedOrbitOfFixedPt φ hN ⁻¹' {flowClosedOrbitOfFixedPt φ hN x}) =
      range fun k : ℤ ↦ (φ ^ k) (x : M) := by
  ext y
  simp only [mem_image, mem_preimage, mem_singleton_iff, flowClosedOrbitOfFixedPt_eq_iff,
    Subtype.exists, exists_and_right, exists_eq_right, mem_range]
  refine ⟨fun hy ↦ hy.2, ?_⟩
  rintro ⟨k, rfl⟩
  refine ⟨?_, k, rfl⟩
  -- Every point of the `φ`-orbit of a fixed point of `φ^[N]` is a forward iterate of it, hence
  -- again fixed by `φ^[N]`.
  obtain ⟨j, -, hj⟩ := (Diffeomorph.exists_zpow_apply_eq_iff ⟨N, hN, x.property⟩).1 ⟨k, rfl⟩
  rw [← hj]
  exact x.property.apply_iterate j

/-! ### Minimal periods -/

/-- The minimal period of `[t, x]` under the suspension flow is the least period of `x` under `φ`.
Both are zero exactly when `x` is not a periodic point of `φ`. -/
@[simp]
theorem minimalPeriod_flow_mk (t : ℝ) (x : M) :
    (flow φ).minimalPeriod (mk φ t x) = minimalPeriod φ x :=
  (flow φ).minimalPeriod_eq_of_periods_eq_zmultiples (periods_flow_mk t x) (Nat.cast_nonneg _)

/-- The minimal period of the closed orbit through `x` is the least period of `x` under `φ`. -/
@[simp]
theorem minimalPeriod_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (flowClosedOrbit φ h hd).minimalPeriod = minimalPeriod φ x := by
  rw [flowClosedOrbit_def, Flow.ClosedOrbit.minimalPeriod_mk, point_periodicTrajectory,
    minimalPeriod_flow_mk]

/-- The closed orbit through `x` with period `d` is primitive exactly when `d` is the least period
of `x`. -/
@[simp]
theorem isPrimitive_flowClosedOrbit_iff (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (flowClosedOrbit φ h hd).IsPrimitive ↔ minimalPeriod φ x = d := by
  rw [Flow.ClosedOrbit.isPrimitive_iff, period_flowClosedOrbit, minimalPeriod_flowClosedOrbit,
    eq_comm, Nat.cast_inj]

/-! ### Multiplicities and primitive closed orbits -/

section Multiplicity

variable [T2Space M] [LocallyCompactSpace M]

/-- The primitive closed orbit underlying the closed orbit through `x` is the closed orbit through
`x` whose period is the least period of `x`. -/
@[simp]
theorem primitive_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    (flowClosedOrbit φ h hd).primitive =
      flowClosedOrbit φ (isPeriodicPt_minimalPeriod φ x) (h.minimalPeriod_pos hd) := by
  ext
  · rw [Flow.ClosedOrbit.support_primitive, support_flowClosedOrbit, support_flowClosedOrbit,
      range_closedOrbit, range_closedOrbit]
  · rw [Flow.ClosedOrbit.period_primitive, minimalPeriod_flowClosedOrbit, period_flowClosedOrbit]

/-- The period `d` of the closed orbit through `x` is its multiplicity times the least period of
`x`. -/
theorem multiplicity_mul_minimalPeriod_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    ((flowClosedOrbit φ h hd).multiplicity : ℕ) * minimalPeriod φ x = d := by
  have hmul := (flowClosedOrbit φ h hd).multiplicity_mul_minimalPeriod
  rw [period_flowClosedOrbit, minimalPeriod_flowClosedOrbit] at hmul
  exact_mod_cast hmul

/-- The multiplicity of the closed orbit through `x` with period `d` is `d` divided by the least
period of `x`. -/
@[simp]
theorem multiplicity_flowClosedOrbit (h : IsPeriodicPt φ d x) (hd : 0 < d) :
    ((flowClosedOrbit φ h hd).multiplicity : ℕ) = d / minimalPeriod φ x :=
  (Nat.div_eq_of_eq_mul_left (h.minimalPeriod_pos hd)
    (multiplicity_mul_minimalPeriod_flowClosedOrbit h hd).symm).symm

/-! ### Counting fixed points of `φ^[N]` by closed orbits of period `N` -/

/-- The closed orbit of period `N` through `x` passes through exactly `N / p` fixed points of
`φ^[N]`, where `p` is its multiplicity: the points of the `φ`-orbit of `x`, as many as the least
period of `x`. -/
theorem card_flowClosedOrbitOfFixedPt_preimage (hN : 0 < N)
    (γ : {γ : (flow φ).ClosedOrbit // γ.period = N}) :
    Nat.card (flowClosedOrbitOfFixedPt φ hN ⁻¹' {γ}) =
      N / (γ : (flow φ).ClosedOrbit).multiplicity := by
  obtain ⟨x, rfl⟩ := flowClosedOrbitOfFixedPt_surjective hN γ
  rw [coe_flowClosedOrbitOfFixedPt, multiplicity_flowClosedOrbit,
    Nat.div_div_self x.property.minimalPeriod_dvd hN.ne', Nat.card_coe_set_eq,
    ← ncard_image_of_injective _ Subtype.val_injective, image_val_flowClosedOrbitOfFixedPt_preimage,
    ← mk_preimage_range_closedOrbit_eq_range_zpow x.property 0, ncard_mk_preimage_range_closedOrbit]

/-- **Fixed points of `φ^[N]` and closed orbits of period `N`.** If `φ^[N]` has finitely many fixed
points and `N > 0`, then summing a function `f` of the closed orbits over the fixed points of
`φ^[N]` counts each closed orbit `γ` of period `N` exactly `N / p(γ)` times, where `p(γ)` is its
multiplicity. -/
theorem finsum_flowClosedOrbitOfFixedPt {R : Type*} [AddCommMonoid R] (hN : 0 < N)
    [Finite {x // IsPeriodicPt φ N x}] (f : (flow φ).ClosedOrbit → R) :
    ∑ᶠ x : {x // IsPeriodicPt φ N x}, f (flowClosedOrbit φ x.property hN) =
      ∑ᶠ γ : {γ : (flow φ).ClosedOrbit // γ.period = N},
        (N / (γ : (flow φ).ClosedOrbit).multiplicity : ℕ) • f γ := by
  have : Finite {γ : (flow φ).ClosedOrbit // γ.period = N} :=
    Finite.of_surjective _ (flowClosedOrbitOfFixedPt_surjective hN)
  let := Fintype.ofFinite {x // IsPeriodicPt φ N x}
  let := Fintype.ofFinite {γ : (flow φ).ClosedOrbit // γ.period = N}
  classical
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
    ← Finset.sum_fiberwise Finset.univ (flowClosedOrbitOfFixedPt φ hN)]
  refine Finset.sum_congr rfl fun γ _ ↦ ?_
  -- On the fibre over `γ` the summand is constant, and the fibre has `N / p(γ)` points.
  rw [Finset.sum_congr rfl fun x hx ↦ by
      rw [← coe_flowClosedOrbitOfFixedPt, (Finset.mem_filter.1 hx).2],
    Finset.sum_const, ← card_flowClosedOrbitOfFixedPt_preimage hN γ, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp only [mem_preimage, mem_singleton_iff]

/-- **The orbit sum of the suspension flow in period `N`.** Over a division ring of characteristic
zero, if `φ^[N]` has finitely many fixed points and `N > 0`, the sum of `f(γ) / p(γ)` over the
closed orbits `γ` of period `N`, with `p(γ)` the multiplicity, is `1 / N` times the sum of `f`
over the closed orbits through the fixed points of `φ^[N]`. -/
theorem finsum_div_multiplicity_eq {K : Type*} [DivisionRing K] [CharZero K] (hN : 0 < N)
    [Finite {x // IsPeriodicPt φ N x}] (f : (flow φ).ClosedOrbit → K) :
    ∑ᶠ γ : {γ : (flow φ).ClosedOrbit // γ.period = N},
        f γ / ((γ : (flow φ).ClosedOrbit).multiplicity : ℕ) =
      (N : K)⁻¹ * ∑ᶠ x : {x // IsPeriodicPt φ N x}, f (flowClosedOrbit φ x.property hN) := by
  rw [finsum_flowClosedOrbitOfFixedPt hN, mul_finsum]
  refine finsum_congr fun γ ↦ ?_
  -- `p(γ)` divides `N`, so `(N / p(γ)) • f γ = N * (f γ / p(γ))`.
  obtain ⟨x, rfl⟩ := flowClosedOrbitOfFixedPt_surjective hN γ
  have hp := multiplicity_mul_minimalPeriod_flowClosedOrbit x.property hN
  set p := ((flowClosedOrbit φ x.property hN).multiplicity : ℕ)
  have hp₀ : (p : K) ≠ 0 := by exact_mod_cast (PNat.pos _).ne'
  have hN' : (N : K) ≠ 0 := by exact_mod_cast hN.ne'
  rw [coe_flowClosedOrbitOfFixedPt, nsmul_eq_mul, Nat.cast_div (Dvd.intro _ hp) hp₀]
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hN', one_mul]
  exact (Nat.cast_commute p _).inv_left₀.eq.symm

end Multiplicity

end SmoothMappingTorus

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.LevelCrossing
public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Logic.Relation

/-!
# Level slices of transverse trajectories of an adapted pseudo-gradient

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
pseudo-gradient field adapted to `f`, and `a ≠ b` critical points of `f`. Along a trajectory from
`a` to `b` the function `f` strictly decreases from `f a` to `f b`, so the trajectory crosses each
intermediate level `{f = c}` exactly once
(`TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`). The
level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` therefore contains one point of each unparametrized
trajectory from `a` to `b`.

This file shows that, where `W^u(a)` and `W^s(b)` meet transversally, the slice is an embedded
submanifold of dimension `ind a - ind b - 1`. The level `{f = c}` cuts `W^u(a) ∩ W^s(b)`
transversally: the velocity `X y` of the trajectory through a point `y` of the slice is tangent to
`W^u(a) ∩ W^s(b)`, while `df_y (X y) < 0`. Hence a chart of the maximal atlas flattens the slice
onto the tangent space of `W^u(a) ∩ W^s(b)` at `y` cut by `ker df_y`, which has one dimension less.

Under the Morse–Smale condition the slice is therefore a smooth manifold of dimension
`ind a - ind b - 1`, and when the Morse indices differ by one it is discrete: its points are the
isolated trajectories that the Morse differential counts. These are the manifold forms of the
results of `TauCeti.Analysis.Calculus.Morse.TrajectorySpace` for a negative-gradient flow on a
vector space.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.mem_Ioo_of_mem_unstableSet_inter_stableSet`: the points of a
  trajectory from `a` to `b` have values strictly between `f b` and `f a`.
* `TauCeti.IsAdaptedPseudoGradient.mem_Icc_of_mem_unstableSet_inter_stableSet`: the points whose
  orbits run from `a` to `b`, possibly equal, have values between `f b` and `f a`.
* `TauCeti.IsAdaptedPseudoGradient.mem_Ioo_of_apply_flow_ne`: the points of a trajectory from `a`
  to a critical point `b`, possibly equal to `a`, whose value is not `f a` have values strictly
  between `f b` and `f a`.
* `TauCeti.IsAdaptedPseudoGradient.FlowsTo`: a trajectory runs from one point to another.
* `TauCeti.IsAdaptedPseudoGradient.apply_lt_apply_of_reflTransGen` and
  `TauCeti.IsAdaptedPseudoGradient.eq_of_reflTransGen_of_reflTransGen`: `f` strictly decreases
  along chains of trajectories, which therefore form a partial order.
* `TauCeti.IsAdaptedPseudoGradient.eq_or_mfderiv_eq_zero_of_reflTransGen` and
  `TauCeti.IsAdaptedPseudoGradient.finite_setOf_reflTransGen`: the points reached from `p` by
  chains of trajectories are `p` and finitely many critical points.
* `IsMorseSmale.manifoldMorseIndex_lt_of_reflTransGen` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient`): the Morse index strictly decreases along chains of
  trajectories.
* `TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet`: a
  trajectory from `a` to `b` crosses each value strictly between `f b` and `f a` exactly once.
* `TauCeti.IsAdaptedPseudoGradient.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet`
  (the case `c = (f a + f b) / 2`): a trajectory from `a` to `b` crosses the middle level exactly
  once.
* `TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_value_eq`: a point of such a trajectory is
  determined by its orbit and its level.
* `TauCeti.IsAdaptedPseudoGradient.exists_tendsto_flow_of_tendsto`: if a point of such a
  trajectory is the limit of a family of points, the crossings of an intermediate level by their
  orbits converge to the crossing of the limit orbit.
* `TauCeti.IsAdaptedPseudoGradient.bijOn_flow_levelCrossingTime_midpoint`: following the flow
  from the middle level to any intermediate level is a bijection between the level slices.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet`:
  the time at which an orbit crosses the level of a point `y` of such a trajectory depends
  continuously on the orbit near `y`.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet`:
  so does the point at which it crosses that level.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet`
  is the same for orbits passing, at some times, through points tending to that point.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_flow_levelCrossingTime`: the point where an orbit
  crosses a level depends continuously on the orbit near a connecting trajectory.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top`:
  every level of `f` is transverse to `W^u(a) ∩ W^s(b)`.
* `TauCeti.IsAdaptedPseudoGradient.exists_unstableSet_inter_stableSet_level_chart`: under
  transversality, a chart of the maximal atlas flattens the level slice.
* `TauCeti.IsAdaptedPseudoGradient.span_mtangentConeAt_unstableSet_inter_stableSet_level`: its
  tangent space is the intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with
  `ker df_y`.
* `finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex` (in the
  namespace `TauCeti.IsAdaptedPseudoGradient`): the slice has dimension `ind a - ind b - 1`.
* `TauCeti.IsAdaptedPseudoGradient.isDiscrete_unstableSet_inter_stableSet_level`: if the Morse
  indices differ by one, the transverse slice is discrete.
* `IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient`): under the Morse–Smale condition, the slice is a smooth
  manifold of dimension `ind a - ind b - 1`.
* `TauCeti.IsAdaptedPseudoGradient.levelPoint`: the point of an orbit on a level, at the crossing
  time `Flow.levelCrossingTime`. Along a trajectory between distinct critical points it is the
  unique point of the orbit on the level (`TauCeti.IsAdaptedPseudoGradient.levelPoint_eq`), it lies
  on the trajectory (`TauCeti.IsAdaptedPseudoGradient.mapsTo_levelPoint`), and it depends
  continuously on the point (`TauCeti.IsAdaptedPseudoGradient.tendsto_levelPoint`).
* `TauCeti.IsAdaptedPseudoGradient.upperLevelPoint` and
  `TauCeti.IsAdaptedPseudoGradient.lowerLevelPoint`: the points of the orbit of `x` on the levels
  `max (f x) c` and `min (f x) c`, which depend continuously on `x` in `W^u(p)` for `c < f p`
  (`TauCeti.IsAdaptedPseudoGradient.continuousOn_upperLevelPoint`), respectively in `W^s(r)` for
  `f r < c` (`TauCeti.IsAdaptedPseudoGradient.continuousOn_lowerLevelPoint`), and are exchanged by
  reversing the pseudo-gradient
  (`TauCeti.IsAdaptedPseudoGradient.upperLevelPoint_eq_lowerLevelPoint_neg`,
  `TauCeti.IsAdaptedPseudoGradient.lowerLevelPoint_eq_upperLevelPoint_neg`).

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (spaces of trajectories).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b y : M} {c : ℝ}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- Along a trajectory joining distinct critical points, `df_y (X y) < 0`, read in the preferred
chart at `y`. -/
private theorem fderiv_comp_chartAt_symm_apply_lt_zero
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) (X y) < 0 := by
  rw [TauCeti.fderiv_comp_chartAt_symm]
  exact hX.mvfderiv_apply_lt_zero y (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hab hy)

/-- Along a trajectory joining distinct critical points, `df_y` is onto `ℝ`, read in the preferred
chart at `y`: it does not vanish on `X y`. -/
private theorem surjective_fderiv_comp_chartAt_symm
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Function.Surjective (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)) := by
  -- A linear form that is negative on some vector `v` of the model space is nonzero.
  have key : ∀ v : E, fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) v < 0 →
      (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ) ≠ 0 := fun v hv h0 ↦
    hv.ne (by rw [← ContinuousLinearMap.coe_coe, h0, LinearMap.zero_apply])
  exact LinearMap.surjective_of_ne_zero
    (key _ (hX.fderiv_comp_chartAt_symm_apply_lt_zero hab hy))

/-- **`f` strictly decreases along a connecting trajectory.** A trajectory from a critical point
`a` to a different critical point `b` meets no critical point, so `f` is strictly antitone along
it. -/
theorem strictAnti_flow_of_mem_unstableSet_inter_stableSet
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    StrictAnti fun t ↦ f (hX.flow t y) :=
  hX.strictAnti_comp (hX.isMIntegralCurve_flow y)
    fun t ↦ hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet
      hab (hX.flow.isInvariant_unstableSet_inter_stableSet a b t hy)

/-- **Connecting trajectories lie strictly between the critical values of their ends.** A point
`y` on a trajectory from a critical point `a` to a different critical point `b` satisfies
`f b < f y < f a`. -/
theorem mem_Ioo_of_mem_unstableSet_inter_stableSet
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    f y ∈ Ioo (f b) (f a) := by
  have hf := hX.mdifferentiable
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  -- Compare `y` with its images at times `1` and `-1`, which lie on the same trajectory.
  have hb : f b ≤ f (hX.flow 1 y) := Flow.le_of_mem_stableSet_of_antitone
    ((Flow.apply_mem_stableSet_iff _ 1).2 hy.2) hf.continuous.continuousAt
    (hX.antitone_flow _)
  have ha : f (hX.flow (-1) y) ≤ f a := Flow.le_of_mem_unstableSet_of_antitone
    ((Flow.apply_mem_unstableSet_iff _ (-1)).2 hy.1) hf.continuous.continuousAt
    (hX.antitone_flow _)
  have h₁ : f (hX.flow 1 y) < f y := by
    simpa only [Flow.map_zero_apply] using hanti zero_lt_one
  have h₂ : f y < f (hX.flow (-1) y) := by
    simpa only [Flow.map_zero_apply] using hanti (neg_lt_zero.2 zero_lt_one)
  exact ⟨hb.trans_lt h₁, h₂.trans_le ha⟩

/-- **Trajectories lie between the critical values of their ends.** A point `y` whose orbit
converges to `a` in backward time and to `b` in forward time satisfies `f b ≤ f y ≤ f a`. Unlike
`mem_Ioo_of_mem_unstableSet_inter_stableSet`, this allows `a = b`, where `y = a`. -/
theorem mem_Icc_of_mem_unstableSet_inter_stableSet
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) : f y ∈ Icc (f b) (f a) :=
  ⟨Flow.le_of_mem_stableSet_of_antitone hy.2 hX.mdifferentiable.continuous.continuousAt
    (hX.antitone_flow y),
    Flow.le_of_mem_unstableSet_of_antitone hy.1 hX.mdifferentiable.continuous.continuousAt
      (hX.antitone_flow y)⟩

/-- Along a trajectory from a critical point `a` to a critical point `b`, every value of `f` other
than `f a` lies strictly between `f b` and `f a`. If `a = b` the trajectory is the constant one at
`a`, so there is no such value. -/
theorem mem_Ioo_of_apply_flow_ne (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (t : ℝ)
    (hne : f (hX.flow t y) ≠ f a) : f (hX.flow t y) ∈ Ioo (f b) (f a) := by
  by_cases hab : a = b
  · subst hab
    rw [hX.eq_of_mem_unstableSet_inter_stableSet hy,
      hX.flow_apply_of_mfderiv_eq_zero (hX.mfderiv_eq_zero_of_mem_stableSet hy.2)] at hne
    exact (hne rfl).elim
  · exact hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hab
      (hX.flow.isInvariant_unstableSet_inter_stableSet a b t hy)

/-- **A trajectory runs from `a` to `b`**: the unstable manifold `W^u(a)` meets the stable manifold
`W^s(b)`. Its reflexive and transitive closure `Relation.ReflTransGen hX.FlowsTo` relates `a` to `b`
when `b = a` or a finite chain of trajectories, broken at critical points, runs from `a` to `b`. -/
def FlowsTo (a b : M) : Prop :=
  (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty

omit hX in
/-- A trajectory runs from `a` to `b` exactly when `W^u(a) ∩ W^s(b)` is nonempty. -/
theorem flowsTo_iff {hX : IsAdaptedPseudoGradient f X} {a b : M} :
    hX.FlowsTo a b ↔ (hX.flow.unstableSet a ∩ hX.flow.stableSet b).Nonempty :=
  Iff.rfl

omit hX in
/-- **Points below `p` are critical.** A point reached from `p` by a chain of trajectories is `p`
itself or a critical point of `f`, the forward limit of the last trajectory. -/
theorem eq_or_mfderiv_eq_zero_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) :
    q = p ∨ mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 := by
  rcases hpq.cases_tail with rfl | ⟨b, -, hbq⟩
  · exact Or.inl rfl
  · obtain ⟨y, -, hy⟩ := flowsTo_iff.1 hbq
    exact Or.inr (hX.mfderiv_eq_zero_of_mem_stableSet hy)

omit hX in
/-- **Finitely many points lie below `p`.** For a Morse function on a compact manifold, the points
reached from `p` by chains of trajectories form a finite set: besides `p` they are critical points
of `f`. -/
theorem finite_setOf_reflTransGen {hX : IsAdaptedPseudoGradient f X} (hf : IsMorse 𝓘(ℝ, E) f)
    (p : M) :
    {q | Relation.ReflTransGen hX.FlowsTo p q}.Finite := by
  refine (hf.finite_criticalPoints.insert p).subset fun q hq ↦ ?_
  rcases eq_or_mfderiv_eq_zero_of_reflTransGen hq with rfl | hq
  · exact mem_insert _ _
  · exact mem_insert_of_mem _ (mem_criticalPoints_iff_mfderiv_eq_zero.2 hq)

omit hX in
/-- **The function strictly decreases along chains of trajectories.** If a chain of trajectories
runs from `p` to a different point `q`, then `f q < f p`. -/
theorem apply_lt_apply_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) (hqp : q ≠ p) :
    f q < f p :=
  -- A trajectory from `b` to `c ≠ b` lies strictly between their critical values.
  hpq.lt_of_forall_ne (fun _ _ hbc hbc' ↦
    let ⟨_, hy⟩ := flowsTo_iff.1 hbc
    have hy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hbc' hy
    hy.1.trans hy.2) hqp

omit hX in
/-- **Chains of trajectories form a partial order.** If chains of trajectories run from `p` to `q`
and from `q` to `p`, then `p = q`. -/
theorem eq_of_reflTransGen_of_reflTransGen {hX : IsAdaptedPseudoGradient f X} {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q)
    (hqp : Relation.ReflTransGen hX.FlowsTo q p) :
    p = q := by
  by_contra hne
  exact (apply_lt_apply_of_reflTransGen hpq (Ne.symm hne)).asymm
    (apply_lt_apply_of_reflTransGen hqp hne)

omit hX in
/-- **The Morse index strictly decreases along chains of trajectories.** Under the Morse–Smale
condition, if a chain of trajectories runs from `p` to a different point `q`, then
`ind q < ind p`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_reflTransGen {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hpq : Relation.ReflTransGen hX.FlowsTo p q) (hqp : q ≠ p) :
    manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f p :=
  hpq.lt_of_forall_ne (fun _ _ hbc hbc' ↦ h.manifoldMorseIndex_lt hf hbc'
    (flowsTo_iff.1 hbc)) hqp

/-- **A trajectory crosses each intermediate level exactly once.** Along a trajectory from a
critical point `a` to a different critical point `b`, the function `f` strictly decreases from
`f a` to `f b`, so it takes each value `c` with `f b < c < f a` at exactly one time. -/
theorem existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hbc : f b < c)
    (hca : c < f a) :
    ∃! t : ℝ, f (hX.flow t y) = c := by
  have hf := hX.mdifferentiable
  exact Flow.existsUnique_apply_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf.continuous.comp (hX.flow.continuous continuous_id continuous_const))
    hf.continuous.continuousAt hf.continuous.continuousAt
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy) hy ⟨hbc, hca⟩

/-- **A trajectory crosses the middle level exactly once.** Along a trajectory from a critical
point `a` to a different critical point `b`, the function `f` takes the value `(f a + f b) / 2`
at exactly one time. -/
theorem existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    ∃! t : ℝ, f (hX.flow t y) = (f a + f b) / 2 := by
  have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hab hy
  exact hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hab hy
    (by linarith [hval.1, hval.2]) (by linarith [hval.1, hval.2])

/-- **A point of a trajectory is determined by its orbit and its level.** Two points that lie on a
common orbit and a common level coincide, if one of them is on a trajectory between distinct
points. -/
theorem eq_of_flow_eq_of_value_eq {y' : M}
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {t t' : ℝ}
    (h : hX.flow t y = hX.flow t' y') (hv : f y = f y') : y = y' := by
  have hy' : y' = hX.flow (t - t') y := by
    rw [show t - t' = -t' + t by ring, Flow.map_add, h, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  have h0 := (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy).injective
    (show f (hX.flow (t - t') y) = f (hX.flow 0 y) by rw [← hy', Flow.map_zero_apply, hv])
  rw [hy', h0, Flow.map_zero_apply]

/-- **Following the flow from the middle level is a bijection.** Let `a ≠ b` be critical points
and `f b < c < f a`. Sending a point of the middle slice `W^u(a) ∩ W^s(b) ∩ {f = (f a + f b) / 2}`
to the point of its trajectory on the level `c` is a bijection onto the slice
`W^u(a) ∩ W^s(b) ∩ {f = c}`. -/
theorem bijOn_flow_levelCrossingTime_midpoint
    (hab : a ≠ b) (hbc : f b < c) (hca : c < f a) :
    BijOn (fun z ↦ hX.flow (Flow.levelCrossingTime hX.flow f c z) z)
      ((hX.flow.unstableSet a ∩ hX.flow.stableSet b) ∩ {z | f z = (f a + f b) / 2})
      ((hX.flow.unstableSet a ∩ hX.flow.stableSet b) ∩ {z | f z = c}) :=
  Flow.bijOn_flow_levelCrossingTime
    (fun _ hy ↦ hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy)
    (fun _ hy ↦ (hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hab
      hy).exists)
    (fun _ hy ↦ (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hab hy hbc
      hca).exists)

/-- **Level-crossing times depend continuously on the point.** Let `y` lie on a trajectory from a
critical point `a` to a different critical point `b`, and let `w` tend to `y`. If the orbit of each
`w i` meets the level of `y` at the time `σ i`, then `σ i` tends to `0`, the time at which the orbit
of `y` meets that level. -/
theorem tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet {ι : Type*} {l : Filter ι}
    (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {w : ι → M} (hw : Tendsto w l (𝓝 y))
    {σ : ι → ℝ} (hσ : ∀ i, f (hX.flow (σ i) (w i)) = f y) : Tendsto σ l (𝓝 0) := by
  have hf := hX.mdifferentiable
  have hfw : ∀ t, Tendsto (fun i ↦ f (hX.flow t (w i))) l (𝓝 (f (hX.flow t y))) := fun t ↦
    ((hf.continuous.comp (hX.contMDiff_flow_apply t).continuous).tendsto y).comp hw
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  -- For `t ≠ 0`, the orbit of `w i` is eventually on the same side of the level at time `t` as
  -- the orbit of `y`; since `f` decreases along orbits, it crosses the level between `0` and `t`.
  refine tendsto_order.2 ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have hlt : f y < f (hX.flow t y) := by simpa using hanti ht
    filter_upwards [(hfw t).eventually (lt_mem_nhds hlt)] with i hi
    by_contra! hle
    exact (hX.antitone_flow (w i) hle).not_gt ((hσ i).trans_lt hi)
  · have hlt : f (hX.flow t y) < f y := by simpa using hanti ht
    filter_upwards [(hfw t).eventually (gt_mem_nhds hlt)] with i hi
    by_contra! hle
    exact (hX.antitone_flow (w i) hle).not_gt (hi.trans_eq (hσ i).symm)

/-- **Level crossings converge along converging orbits.** Let `w` lie on a trajectory from `a` to
`b`, and `c` a value strictly between `f b` and `f a`. If `u i → w` and the orbit of `u i` meets
the level `c` at time `s i`, then the crossing points converge to the point where the orbit of `w`
meets the level `c`. -/
theorem exists_tendsto_flow_of_tendsto {w : M}
    (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) (hbc : f b < c)
    (hca : c < f a) {ι : Type*} {l : Filter ι} {u : ι → M} (hu : Tendsto u l (𝓝 w))
    {s : ι → ℝ} (hs : ∀ i, f (hX.flow (s i) (u i)) = c) :
    ∃ σ : ℝ, f (hX.flow σ w) = c ∧
      Tendsto (fun i ↦ hX.flow (s i) (u i)) l (𝓝 (hX.flow σ w)) := by
  have hab : a ≠ b := by rintro rfl; exact (hbc.trans hca).false
  obtain ⟨σ, hσ, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hab hw hbc hca
  -- Move everything to the crossing point `flow σ w`, where the crossing time is `0`.
  have hu' : Tendsto (fun i ↦ hX.flow σ (u i)) l (𝓝 (hX.flow σ w)) :=
    ((hX.flow.continuous continuous_const continuous_id).tendsto w).comp hu
  have ht := hX.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet hab
    (hX.flow.isInvariant_unstableSet_inter_stableSet a b σ hw) hu' (σ := fun i ↦ s i - σ)
    fun i ↦ by rw [← Flow.map_add, sub_add_cancel, hs, hσ]
  refine ⟨σ, hσ, ?_⟩
  simpa only [Function.comp_def, ← Flow.map_add, sub_add_cancel, zero_add] using
    ((hX.flow.continuous continuous_fst continuous_snd).tendsto (0, hX.flow σ w)).comp
      (ht.prodMk_nhds hu')

/-- **Level points depend continuously on the orbit.** Let `y` lie on a trajectory from a critical
point `a` to a different critical point `b`, whose orbit meets the level `c` at the time `σ`, and
let `w` tend to `y`. If the orbit of each `w i` meets the level `c` at the time `s i`, then these
level points tend to the level point of the orbit of `y`. -/
theorem tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet {ι : Type*} {l : Filter ι}
    (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {σ : ℝ} (hσ : f (hX.flow σ y) = c)
    {w : ι → M} (hw : Tendsto w l (𝓝 y)) {s : ι → ℝ} (hs : ∀ i, f (hX.flow (s i) (w i)) = c) :
    Tendsto (fun i ↦ hX.flow (s i) (w i)) l (𝓝 (hX.flow σ y)) := by
  have hw' : Tendsto (fun i ↦ hX.flow σ (w i)) l (𝓝 (hX.flow σ y)) :=
    ((hX.contMDiff_flow_apply σ).continuous.tendsto y).comp hw
  -- Measured from the level point of `y`, the crossing times tend to `0`.
  have h0 := hX.tendsto_zero_of_flow_eq_of_mem_unstableSet_inter_stableSet hab
    (hX.flow.isInvariant_unstableSet_inter_stableSet a b σ hy) hw' (σ := fun i ↦ s i - σ)
    fun i ↦ by rw [← Flow.map_add, sub_add_cancel, hs, hσ]
  have hlim := (hX.contMDiff_flow_uncurry.continuous.tendsto ((0 : ℝ), hX.flow σ y)).comp
    (h0.prodMk_nhds hw')
  rw [Function.comp_def, Flow.map_zero_apply] at hlim
  exact hlim.congr fun i ↦ by rw [← Flow.map_add, sub_add_cancel]

/-- **Level points of orbits passing near a trajectory.** Let `y` lie on a trajectory from a
critical point `a` to a different critical point `b`, whose orbit meets the level `c` at the time
`σ`, and let the orbits of points `w i` pass, at the times `s i`, through points tending to `y`. If
the orbit of each `w i` meets the level `c` at the time `τ i`, then these level points tend to the
level point of the orbit of `y`. -/
theorem tendsto_flow_of_tendsto_flow_of_mem_unstableSet_inter_stableSet {ι : Type*}
    {l : Filter ι} (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {σ : ℝ}
    (hσ : f (hX.flow σ y) = c) {w : ι → M} {s τ : ι → ℝ}
    (hw : Tendsto (fun i ↦ hX.flow (s i) (w i)) l (𝓝 y))
    (hτ : ∀ i, f (hX.flow (τ i) (w i)) = c) :
    Tendsto (fun i ↦ hX.flow (τ i) (w i)) l (𝓝 (hX.flow σ y)) := by
  have hshift (i : ι) : hX.flow (τ i - s i) (hX.flow (s i) (w i)) = hX.flow (τ i) (w i) := by
    rw [← Flow.map_add, sub_add_cancel]
  simpa only [hshift] using hX.tendsto_flow_of_flow_eq_of_mem_unstableSet_inter_stableSet hab hy
    hσ hw (s := fun i ↦ τ i - s i) fun i ↦ by rw [hshift]; exact hτ i

/-- Orbits through points near a point `y` of a trajectory between distinct critical points cross
the level of `y` at times in `[-δ, δ]`. -/
theorem eventually_exists_mem_Icc_apply_flow_eq
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ w in 𝓝 y, ∃ σ ∈ Icc (-δ) δ, f (hX.flow σ w) = f y := by
  have hf := hX.mdifferentiable
  have hanti := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hy
  have hcont : ∀ t, Continuous fun w ↦ f (hX.flow t w) := fun t ↦
    hf.continuous.comp (hX.contMDiff_flow_apply t).continuous
  have h₁ : f (hX.flow δ y) < f y := by simpa using hanti hδ
  have h₂ : f y < f (hX.flow (-δ) y) := by simpa using hanti (neg_lt_zero.2 hδ)
  filter_upwards [(hcont δ).continuousAt.eventually (gt_mem_nhds h₁),
    (hcont (-δ)).continuousAt.eventually (lt_mem_nhds h₂)] with w hw₁ hw₂
  exact intermediate_value_Icc' (by linarith)
    (hf.continuous.comp (hX.flow.continuous continuous_id continuous_const)).continuousOn
    ⟨hw₁.le, hw₂.le⟩

/-- **The level point of an orbit depends continuously on the orbit.** Let `y` lie on a trajectory
between distinct critical points, with `f (flow σ₀ y) = c`. For points `w i` tending to `y` along
whose orbits `f` strictly decreases, the points where these orbits cross the level `c` tend to
`flow σ₀ y`. -/
theorem tendsto_flow_levelCrossingTime (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {σ₀ : ℝ}
    (hσ₀ : f (hX.flow σ₀ y) = c) {ι : Type*} {l : Filter ι} {w : ι → M}
    (hw : Tendsto w l (𝓝 y)) (hanti : ∀ᶠ i in l, StrictAnti fun t ↦ f (hX.flow t (w i))) :
    Tendsto (fun i ↦ hX.flow (Flow.levelCrossingTime hX.flow f c (w i)) (w i)) l
      (𝓝 (hX.flow σ₀ y)) := by
  set z := hX.flow σ₀ y
  have hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b :=
    hX.flow.isInvariant_unstableSet_inter_stableSet a b σ₀ hy
  have hw' : Tendsto (fun i ↦ hX.flow σ₀ (w i)) l (𝓝 z) :=
    ((hX.flow.continuous_toFun σ₀).tendsto y).comp hw
  set τ := fun i ↦ Flow.levelCrossingTime hX.flow f c (w i) - σ₀
  -- The crossing time of `w i` differs from `σ₀` by a crossing time of `flow σ₀ (w i)` near `0`.
  have hτ : ∀ δ > 0, ∀ᶠ i in l, τ i ∈ Icc (-δ) δ := fun δ hδ ↦ by
    filter_upwards [hw'.eventually (hX.eventually_exists_mem_Icc_apply_flow_eq hab hz hδ),
      hanti] with i ⟨σ, hσ, hσc⟩ hi
    rw [hσ₀, ← Flow.map_add] at hσc
    have := (Flow.eq_levelCrossingTime_iff hi ⟨_, hσc⟩).2 hσc
    simp only [τ, ← this, add_sub_cancel_right]
    exact hσ
  have hτ0 : Tendsto τ l (𝓝 0) := tendsto_order.2
    ⟨fun r hr ↦ (hτ (-r / 2) (by linarith)).mono fun i hi ↦ by linarith [hi.1],
      fun r hr ↦ (hτ (r / 2) (by linarith)).mono fun i hi ↦ by linarith [hi.2]⟩
  have h := (hX.flow.cont'.tendsto (0, z)).comp (hτ0.prodMk_nhds hw')
  simp only [Function.comp_def, Function.uncurry_apply_pair, Flow.map_zero_apply] at h
  refine h.congr fun i ↦ ?_
  rw [← Flow.map_add, sub_add_cancel]

/-- **Levels are transverse to connecting trajectories.** At a point `y` of `W^u(a) ∩ W^s(b)` with
`a ≠ b`, the tangent space of `W^u(a) ∩ W^s(b)` and the kernel of `df_y`, the tangent space of the
level of `f` through `y`, span the tangent space of `M`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) :
    Submodule.span ℝ
        (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊔
      (mvfderiv 𝓘(ℝ, E) f y).ker = ⊤ := by
  have hmem := hX.mem_span_mtangentConeAt_unstableSet_inter_stableSet hy
  rw [TauCeti.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm]
  refine top_unique ?_
  rw [← LinearMap.span_singleton_sup_ker_eq_top
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
    (hX.fderiv_comp_chartAt_symm_apply_lt_zero hab hy).ne]
  exact sup_le_sup_right ((Submodule.span_singleton_le_iff_mem (R := ℝ) (M := E) _ _).2 hmem) _

/-- Under transversality, the level slice through `y` is cut out of `W^u(a) ∩ W^s(b)` by a
transverse regular level set: it is flattened by a chart of the maximal atlas, and its tangent
space is that of `W^u(a) ∩ W^s(b)` cut by `ker df_y`. -/
private theorem level_slice (hf : IsMorse 𝓘(ℝ, E) f) (hab : a ≠ b)
    (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    (∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c})) ∧
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ
          (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  obtain ⟨q, hyq, hq, hs⟩ := hX.exists_unstableSet_inter_stableSet_chart hX hf hy htr
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet hX hf hy htr] at hs
  -- The level `{f = c}` is a regular level set near `y`, since `df_y (X y) < 0`.
  have hlevel : {x | f x = c} = f ⁻¹' {c} := by
    ext
    simp
  have hrange : (mvfderiv 𝓘(ℝ, E) f y).range = ⊤ := by
    rw [← TauCeti.fderiv_comp_chartAt_symm]
    exact LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm hab hy)
  have htr' := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top
    hab hy
  -- In finite dimensions every subspace is complemented.
  have hcc (p : Submodule ℝ E) : p.ClosedComplemented :=
    .of_finiteDimensional_quotient (Submodule.isClosed_of_finiteDimensional _)
  rw [hlevel]
  exact ⟨exists_isSliceChart_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs
      hyq isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr'
      (hcc _) (hcc _) (hcc _),
    span_mtangentConeAt_inter_preimage_of_span_mtangentConeAt_sup_ker_eq_top (by simp) hq hs hyq
      isOpen_univ (mem_univ y) hf.contMDiff.contMDiffOn hyc hrange htr'
      (hcc _) (hcc _) (hcc _)⟩

/-- **The level slice of a transverse intersection is an embedded submanifold.** If the unstable
manifold of a critical point `a` and the stable manifold of a different critical point `b` meet
transversally at `y`, and `f y = c`, then near `y` a chart of the maximal atlas flattens the level
slice `W^u(a) ∩ W^s(b) ∩ {f = c}` onto the intersection of the tangent spaces of `W^u(a)` and
`W^s(b)` with `ker df_y`. -/
theorem exists_unstableSet_inter_stableSet_level_chart (hf : IsMorse 𝓘(ℝ, E) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    ∃ q : OpenPartialHomeomorph M E, y ∈ q.source ∧
      q ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      IsSliceChart q ((Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
          Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
          (mvfderiv 𝓘(ℝ, E) f y).ker : Submodule ℝ E) : Set E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  obtain ⟨⟨q, hyq, hq, hs⟩, -⟩ := hX.level_slice hf hab hy htr hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet hX hf hy htr] at hs
  exact ⟨q, hyq, hq, hs⟩

/-- **The tangent space of a transverse level slice.** If the unstable manifold of a critical point
`a` and the stable manifold of a different critical point `b` meet transversally at `y`, and
`f y = c`, then the tangent space of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` at `y` is the
intersection of the tangent spaces of `W^u(a)` and `W^s(b)` with `ker df_y`. -/
theorem span_mtangentConeAt_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y) =
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊓
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) ⊓
        (mvfderiv 𝓘(ℝ, E) f y).ker := by
  rw [(hX.level_slice hf hab hy htr hyc).2,
    hX.span_mtangentConeAt_unstableSet_inter_stableSet hX hf hy htr]

/-- **The level slice has dimension the index difference minus one.** If the unstable manifold of a
critical point `a` and the stable manifold of a different critical point `b` meet transversally at
`y`, then the tangent space at `y` of the level slice `W^u(a) ∩ W^s(b) ∩ {f = f y}` has dimension
`ind a - ind b - 1`. -/
theorem finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex
    (hf : IsMorse 𝓘(ℝ, E) f)
    (hab : a ≠ b) (hy : y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b)
    (htr : Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤)
    (hyc : f y = c) :
    Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
        (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) +
      manifoldMorseIndex 𝓘(ℝ, E) f b + 1 = manifoldMorseIndex 𝓘(ℝ, E) f a := by
  have hsup := hX.span_mtangentConeAt_unstableSet_inter_stableSet_sup_ker_eq_top hab hy
  have hslice := (hX.level_slice hf hab hy htr hyc).2
  rw [TauCeti.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm] at hsup hslice
  -- Cutting by the hyperplane `ker df_y`, which is transverse, lowers the dimension by one.
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ
      (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a ∩ hX.flow.stableSet b) y))
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y)).ker
  rw [hsup, finrank_top, ← hslice] at hdim
  have hker := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℝ (f ∘ (chartAt E y).symm) (chartAt E y y) : E →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top_of_surjective _
      (hX.surjective_fderiv_comp_chartAt_symm hab hy), finrank_top,
    Module.finrank_self] at hker
  have hW :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_add_manifoldMorseIndex hX hf hy htr
  omega

/-- **Index-difference-one level slices are discrete.** If the Morse indices of critical points `a`
and `b` differ by one and the unstable manifold of `a` meets the stable manifold of `b`
transversally at every point of the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}`, then the slice is
discrete: each of the trajectories it parametrizes is isolated. -/
theorem isDiscrete_unstableSet_inter_stableSet_level (hf : IsMorse 𝓘(ℝ, E) f)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1)
    (htr : ∀ y ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c},
      Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet a) y) ⊔
        Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.stableSet b) y) = ⊤) :
    IsDiscrete (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) := by
  have hab : a ≠ b := by rintro rfl; omega
  refine isDiscrete_of_forall_exists_isSliceChart_zero (F := E) fun y hy ↦ ?_
  have htry := htr y hy
  obtain ⟨hyab, hyc⟩ := hy
  -- The slice is zero-dimensional, so the chart at `y` flattens it onto the point `0`.
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf
      hab hyab htry hyc
  obtain ⟨q, hyq, -, hq⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf hab hyab htry hyc
  have h0 : Module.finrank ℝ (Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y)) = 0 := by
    omega
  rw [← hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf hab hyab htry hyc,
    Submodule.finrank_eq_zero.1 h0, Submodule.bot_coe] at hq
  exact ⟨q, hyq, hq⟩

omit hX in
/-- **Spaces of unparametrized trajectories are manifolds.** Under the Morse–Smale condition, if
some trajectory from a critical point `a` to a different critical point `b` crosses the level
`{f = c}`, then the level slice `W^u(a) ∩ W^s(b) ∩ {f = c}` carries a smooth manifold structure,
modelled on a subspace of dimension `ind a - ind b - 1`, with its subspace topology and a smooth
inclusion into `M`. -/
theorem IsMorseSmale.exists_unstableSet_inter_stableSet_level_isManifold
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hab : a ≠ b) (hne : (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}).Nonempty) :
    ∃ L : Submodule ℝ E,
      Module.finrank ℝ L + manifoldMorseIndex 𝓘(ℝ, E) f b + 1 =
        manifoldMorseIndex 𝓘(ℝ, E) f a ∧
      ∃ C : ChartedSpace L ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}),
        letI := C
        IsManifold 𝓘(ℝ, L) ∞ ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) ∧
        ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, E) ∞
          (Subtype.val : ↥(hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) → M) := by
  obtain ⟨y₀, hy₀, hy₀c⟩ := hne
  have htr₀ := h.span_mtangentConeAt_sup_eq_top hy₀
  have hdim₀ :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf
      hab hy₀ htr₀ hy₀c
  -- Every tangent space of the slice has dimension `ind a - ind b - 1`; model it on one of them.
  refine ⟨Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {x | f x = c}) y₀), hdim₀,
    exists_isManifold_of_finrankSubspaceCharts fun y hy ↦ ?_⟩
  obtain ⟨hyab, hyc⟩ := hy
  have htry := h.span_mtangentConeAt_sup_eq_top hyab
  obtain ⟨q, hyq, hq, hs⟩ :=
    hX.exists_unstableSet_inter_stableSet_level_chart hf hab hyab htry hyc
  have hdim :=
    hX.finrank_span_mtangentConeAt_unstableSet_inter_stableSet_level_add_manifoldMorseIndex hf
      hab hyab htry hyc
  rw [hX.span_mtangentConeAt_unstableSet_inter_stableSet_level hf hab hyab htry
    hyc] at hdim
  exact ⟨q, _, hyq, fun z hz ↦ contMDiffAt_of_mem_maximalAtlas hq hz,
    fun z hz ↦ contMDiffAt_symm_of_mem_maximalAtlas hq hz, isSliceChart_iff.1 hs, by omega⟩

/-! ### Points of an orbit on a level -/

section LevelPoint

/-- The orbit of a point of `W^u(p)` below the level `c < f p` meets that level. -/
theorem exists_flow_eq_of_mem_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) {p x : M}
    (hx : x ∈ hX.flow.unstableSet p) {c : ℝ} (hcp : c < f p) (hxc : f x < c) :
    ∃ t, f (hX.flow t x) = c := by
  obtain ⟨a, hpa, hxa⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_unstableSet hf hx
    (ne_of_apply_ne f (hxc.trans hcp).ne)
  exact (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpa hxa
    ((hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa hxa).1.trans hxc) hcp).exists

/-- The orbit of a point of `W^s(r)` above the level `c > f r` meets that level. -/
theorem exists_flow_eq_of_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f) {r x : M}
    (hx : x ∈ hX.flow.stableSet r) {c : ℝ} (hrc : f r < c) (hcx : c < f x) :
    ∃ t, f (hX.flow t x) = c := by
  obtain ⟨b, hbr, hxb⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet hf hx
    (ne_of_apply_ne f (hrc.trans hcx).ne')
  exact (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hbr hxb hrc
    (hcx.trans (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr hxb).2)).exists

/-- The point of the orbit of `x` on the level `c`, at the crossing time
`Flow.levelCrossingTime`, when the orbit meets that level, and `x` otherwise. -/
noncomputable def levelPoint (c : ℝ) (x : M) : M :=
  hX.flow (Flow.levelCrossingTime hX.flow f c x) x

/-- The level point is the point of the orbit at the crossing time. -/
theorem levelPoint_def (c : ℝ) (x : M) :
    hX.levelPoint c x = hX.flow (Flow.levelCrossingTime hX.flow f c x) x :=
  (rfl)

/-- When the orbit of `x` meets the level `c`, its level point lies on that level. -/
theorem apply_levelPoint {c : ℝ} {x : M} (h : ∃ t, f (hX.flow t x) = c) :
    f (hX.levelPoint c x) = c :=
  Flow.apply_flow_levelCrossingTime h

/-- Along a trajectory between distinct critical points, the level point is the unique point of
the orbit on the level. -/
theorem levelPoint_eq {a b x : M} (hab : a ≠ b)
    (hx : x ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {t c : ℝ}
    (ht : f (hX.flow t x) = c) : hX.levelPoint c x = hX.flow t x :=
  congrArg (hX.flow · x) ((Flow.eq_levelCrossingTime_iff
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hx) ⟨t, ht⟩).2 ht).symm

/-- On a trajectory between distinct critical points crossing the level `c`, the level point lies
on the trajectory and on the level. -/
theorem mapsTo_levelPoint {a b : M} (hab : a ≠ b) {c : ℝ} (hbc : f b < c) (hca : c < f a) :
    MapsTo (hX.levelPoint c) (hX.flow.unstableSet a ∩ hX.flow.stableSet b)
      (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {z | f z = c}) := fun z hz ↦ by
  obtain ⟨s, hs, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hab hz hbc hca
  rw [hX.levelPoint_eq hab hz hs]
  exact ⟨hX.flow.isInvariant_unstableSet_inter_stableSet a b s hz, hs⟩

/-- Moving a point of a trajectory between distinct critical points along its orbit does not move
its level point, when the orbit crosses the level. -/
theorem levelPoint_flow {a b x : M} (hab : a ≠ b)
    (hx : x ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ}
    (hex : ∃ t, f (hX.flow t x) = c) (t : ℝ) :
    hX.levelPoint c (hX.flow t x) = hX.levelPoint c x := by
  obtain ⟨s, hs⟩ := hex
  exact (Flow.flow_levelCrossingTime_flow
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hx) hs t).trans
      (hX.levelPoint_eq hab hx hs).symm

/-- **Level points converge.** If points `u i` whose orbits meet the level `c` converge to a point
`w` of a trajectory from `a` to `b` crossing that level, then their level points converge to that
of `w`. -/
theorem tendsto_levelPoint {a b w : M}
    (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ} (hbc : f b < c)
    (hca : c < f a) {ι : Type*} {l : Filter ι} {u : ι → M} (hu : Tendsto u l (𝓝 w))
    (hex : ∀ᶠ i in l, ∃ t, f (hX.flow t (u i)) = c) :
    Tendsto (fun i ↦ hX.levelPoint c (u i)) l (𝓝 (hX.levelPoint c w)) := by
  have hab : a ≠ b := by rintro rfl; exact (hbc.trans hca).false
  set T := {i | ∃ t, f (hX.flow t (u i)) = c}
  rw [← tendsto_comap'_iff (i := ((↑) : T → ι)) (by rwa [Subtype.range_coe])]
  obtain ⟨σ, hσ, hlim⟩ := hX.exists_tendsto_flow_of_tendsto hw hbc hca (hu.comp tendsto_comap)
    (s := fun i : T ↦ Flow.levelCrossingTime hX.flow f c (u i))
    fun i ↦ Flow.apply_flow_levelCrossingTime i.property
  rw [hX.levelPoint_eq hab hw hσ]
  exact hlim

/-- **Reversing the pseudo-gradient.** On a trajectory between distinct critical points crossing
the level `c` of `f`, the level point for `-X` on the level `-c` of `-f` is the level point for
`X` on the level `c`. -/
theorem levelPoint_neg (hf : IsMorse 𝓘(ℝ, E) f) {a b x : M} (hab : a ≠ b)
    (hx : x ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ}
    (hex : ∃ t, f (hX.flow t x) = c) :
    (hX.neg hf).levelPoint (-c) x = hX.levelPoint c x := by
  obtain ⟨t, ht⟩ := hex
  have hx' : x ∈ (hX.neg hf).flow.unstableSet b ∩ (hX.neg hf).flow.stableSet a := by
    rw [← hX.stableSet_eq_unstableSet_neg hf, ← hX.unstableSet_eq_stableSet_neg hf]
    exact ⟨hx.2, hx.1⟩
  have hneg (s : ℝ) : (hX.neg hf).flow s x = hX.flow (-s) x := by
    rw [hX.neg_flow hf, Flow.reverse_apply]
  rw [hX.levelPoint_eq hab hx ht, (hX.neg hf).levelPoint_eq hab.symm hx' (t := -t)
    (by rw [hneg, neg_neg, Pi.neg_apply, ht]), hneg, neg_neg]

/-- The point of the orbit of `x` on the level `max (f x) c`: the point `x` itself when
`c ≤ f x`, and otherwise the point where the orbit of `x` comes down from the level `c`. -/
noncomputable def upperLevelPoint (c : ℝ) (x : M) : M :=
  if c ≤ f x then x else hX.levelPoint c x

/-- The point of the orbit of `x` on the level `min (f x) c`: the point `x` itself when
`f x ≤ c`, and otherwise the point where the orbit of `x` descends to the level `c`. -/
noncomputable def lowerLevelPoint (c : ℝ) (x : M) : M :=
  if f x ≤ c then x else hX.levelPoint c x

/-- At or above the level, the upper level point is the point itself. -/
theorem upperLevelPoint_of_le {c : ℝ} {x : M} (h : c ≤ f x) : hX.upperLevelPoint c x = x :=
  ite_eq_left h

/-- Below the level, the upper level point is the level point. -/
theorem upperLevelPoint_of_lt {c : ℝ} {x : M} (h : f x < c) :
    hX.upperLevelPoint c x = hX.levelPoint c x :=
  ite_eq_right h.not_ge

/-- At or below the level, the lower level point is the point itself. -/
theorem lowerLevelPoint_of_le {c : ℝ} {x : M} (h : f x ≤ c) : hX.lowerLevelPoint c x = x :=
  ite_eq_left h

/-- Above the level, the lower level point is the level point. -/
theorem lowerLevelPoint_of_lt {c : ℝ} {x : M} (h : c < f x) :
    hX.lowerLevelPoint c x = hX.levelPoint c x :=
  ite_eq_right h.not_ge

/-- On `W^u(p)`, for `c < f p`, the upper level point on the level `c` is the lower level point
for `-X` on the level `-c` of `-f`. -/
theorem upperLevelPoint_eq_lowerLevelPoint_neg (hf : IsMorse 𝓘(ℝ, E) f) {p x : M}
    (hx : x ∈ hX.flow.unstableSet p) {c : ℝ} (hcp : c < f p) :
    hX.upperLevelPoint c x = (hX.neg hf).lowerLevelPoint (-c) x := by
  rcases le_or_gt c (f x) with hcx | hxc
  · rw [hX.upperLevelPoint_of_le hcx, (hX.neg hf).lowerLevelPoint_of_le (neg_le_neg hcx)]
  · obtain ⟨a, hpa, hxa⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_unstableSet hf hx
      (ne_of_apply_ne f (hxc.trans hcp).ne)
    rw [hX.upperLevelPoint_of_lt hxc, (hX.neg hf).lowerLevelPoint_of_lt (neg_lt_neg hxc),
      hX.levelPoint_neg hf hpa hxa (hX.exists_flow_eq_of_mem_unstableSet hf hx hcp hxc)]

/-- On `W^s(r)`, for `f r < c`, the lower level point on the level `c` is the upper level point
for `-X` on the level `-c` of `-f`. -/
theorem lowerLevelPoint_eq_upperLevelPoint_neg (hf : IsMorse 𝓘(ℝ, E) f) {r x : M}
    (hx : x ∈ hX.flow.stableSet r) {c : ℝ} (hrc : f r < c) :
    hX.lowerLevelPoint c x = (hX.neg hf).upperLevelPoint (-c) x := by
  rcases le_or_gt (f x) c with hxc | hcx
  · rw [hX.lowerLevelPoint_of_le hxc, (hX.neg hf).upperLevelPoint_of_le (neg_le_neg hxc)]
  · obtain ⟨b, hbr, hxb⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet hf hx
      (ne_of_apply_ne f (hrc.trans hcx).ne')
    rw [hX.lowerLevelPoint_of_lt hcx, (hX.neg hf).upperLevelPoint_of_lt (neg_lt_neg hcx),
      hX.levelPoint_neg hf hbr hxb (hX.exists_flow_eq_of_mem_stableSet hf hx hrc hcx)]

/-- **The upper level point is continuous on an unstable manifold.** For `c < f p`, the point of
the orbit of `x` on the level `max (f x) c` depends continuously on the point `x` of `W^u(p)`. -/
theorem continuousOn_upperLevelPoint (hf : IsMorse 𝓘(ℝ, E) f) {p : M} {c : ℝ}
    (hcp : c < f p) : ContinuousOn (hX.upperLevelPoint c) (hX.flow.unstableSet p) := by
  intro y hy
  have hcont : Continuous f := hX.mdifferentiable.continuous
  have hsplit : hX.flow.unstableSet p =
      (hX.flow.unstableSet p ∩ {x | c ≤ f x}) ∪ (hX.flow.unstableSet p ∩ {x | f x < c}) := by
    rw [← inter_union_distrib_left, ← ofPred_or]
    simp only [le_or_gt, ofPred_true, inter_univ]
  rw [hsplit]
  refine ContinuousWithinAt.union ?_ ?_
  · -- Above the level, the upper level point is the point itself.
    by_cases hyc : c ≤ f y
    · exact continuousWithinAt_id.congr (fun x hx ↦ hX.upperLevelPoint_of_le hx.2)
        (hX.upperLevelPoint_of_le hyc)
    · exact continuousWithinAt_of_notMem_closure fun hcl ↦ hyc
        (closure_minimal inter_subset_right (isClosed_le continuous_const hcont) hcl)
  · -- Below the level, it is the level point, which converges along the trajectory through `y`.
    by_cases hcl : y ∈ closure (hX.flow.unstableSet p ∩ {x | f x < c})
    · have hcy : f y ≤ c :=
        closure_lt_subset_le hcont continuous_const (closure_mono inter_subset_right hcl)
      obtain ⟨a, hpa, hya⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_unstableSet hf hy
        (ne_of_apply_ne f (hcy.trans_lt hcp).ne)
      have hfy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa hya
      have hlim := hX.tendsto_levelPoint hya (hfy.1.trans_le hcy) hcp (u := id)
        (l := 𝓝[hX.flow.unstableSet p ∩ {x | f x < c}] y) nhdsWithin_le_nhds
        (eventually_nhdsWithin_of_forall fun x hx ↦
          hX.exists_flow_eq_of_mem_unstableSet hf hx.1 hcp hx.2)
      have hy' : hX.upperLevelPoint c y = hX.levelPoint c y := by
        rcases hcy.lt_or_eq with hcy | hcy
        · exact hX.upperLevelPoint_of_lt hcy
        · rw [hX.upperLevelPoint_of_le hcy.ge,
            hX.levelPoint_eq hpa hya (t := 0) (by rw [Flow.map_zero_apply, hcy]),
            Flow.map_zero_apply]
      rw [ContinuousWithinAt, hy']
      exact hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
        (hX.upperLevelPoint_of_lt hx.2).symm)
    · exact continuousWithinAt_of_notMem_closure hcl

/-- **The lower level point is continuous on a stable manifold.** For `f r < c`, the point of
the orbit of `x` on the level `min (f x) c` depends continuously on the point `x` of `W^s(r)`. -/
theorem continuousOn_lowerLevelPoint (hf : IsMorse 𝓘(ℝ, E) f) {r : M} {c : ℝ}
    (hrc : f r < c) : ContinuousOn (hX.lowerLevelPoint c) (hX.flow.stableSet r) := by
  -- Reversing the pseudo-gradient, it is an upper level point on an unstable manifold.
  rw [hX.stableSet_eq_unstableSet_neg hf]
  refine ((hX.neg hf).continuousOn_upperLevelPoint hf.neg (neg_lt_neg hrc)).congr fun x hx ↦ ?_
  rw [← hX.stableSet_eq_unstableSet_neg hf] at hx
  exact hX.lowerLevelPoint_eq_upperLevelPoint_neg hf hx hrc

end LevelPoint

end IsAdaptedPseudoGradient

end TauCeti

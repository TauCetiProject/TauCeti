/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Points with unique values on the horizontal slices of a map on `ℝ × ℝ`

Let `u : ℝ × ℝ → X` be a continuous map into a Hausdorff space such that `u(s, t)` tends to
`xm(t₀)` as `s → -∞` and `t → t₀` together, and to `xp(t₀)` as `s → +∞` and `t → t₀` together.
If `z₀ = (s₀, t₀)` is the only point of its slice with value `u(z₀)`, away from the limits, and
`(s, t) ↦ (u(s, t), t)` is injective near `z₀`, then every nearby point is the only point of its
slice with its value (`TauCeti.eventually_forall_slice_eq_imp_eq_of_tendsto`). The limits confine
the competitors to a compact interval, and a compactness argument separates them uniformly
nearby. Without the local injectivity, such a point `z₀` is an injective point of
`(s, t) ↦ (t, u(s, t))`: the points `z` with `(z.2, u z)` close to `(t₀, u z₀)` are close to `z₀`
(`TauCeti.comap_nhds_le_nhds_of_tendsto`). The limits confine these points to a compact box, on
which `z₀` is their only cluster point.

A *partner* of `z` on its slice is a point `(s, z.2)` with `u(s, z.2) = u z`. For a compact set
`D`, the points with a partner in `D` at distance at least `ε` form a closed set
(`TauCeti.isClosed_setOf_exists_slice_eq`). If moreover `(s, t) ↦ (u(s, t), t)` is injective
on `D`, a choice of partners in `D` on an open set is continuous
(`TauCeti.continuousAt_of_forall_slice_eq`).

This is the topological part of the openness and density of the regular points of Floer
trajectories.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℝ × ℝ → X} {xm xp : ℝ → X}

/-- **Points with a unique value on their slice persist nearby.** Let `u : ℝ × ℝ → X` be
continuous, with values in a Hausdorff space, and suppose that `u(s, t)` tends to `xm(t₀)` and
`xp(t₀)` as `s → -∞` and `s → +∞` and `t → t₀`. Let `z₀ = (s₀, t₀)` be a point near which
`(s, t) ↦ (u(s, t), t)` is injective, with `u(z₀) ≠ xm(t₀)`, `u(z₀) ≠ xp(t₀)` and
`u(s, t₀) ≠ u(z₀)` for all `s ≠ s₀`. Then every point `(s, t)` near `z₀` has the last property:
`u(s', t) ≠ u(s, t)` for all `s' ≠ s`. -/
theorem eventually_forall_slice_eq_imp_eq_of_tendsto {z₀ : ℝ × ℝ} (hu : Continuous u)
    (hm : Tendsto u (atBot ×ˢ 𝓝 z₀.2) (𝓝 (xm z₀.2)))
    (hp : Tendsto u (atTop ×ˢ 𝓝 z₀.2) (𝓝 (xp z₀.2)))
    (hinj : ∃ U ∈ 𝓝 z₀, InjOn (fun z ↦ (u z, z.2)) U)
    (hm₀ : u z₀ ≠ xm z₀.2) (hp₀ : u z₀ ≠ xp z₀.2) (h₀ : ∀ s, u (s, z₀.2) = u z₀ → s = z₀.1) :
    ∀ᶠ z in 𝓝 z₀, ∀ s, u (s, z.2) = u z → s = z.1 := by
  obtain ⟨s₀, t₀⟩ := z₀
  obtain ⟨U, hU, hinj⟩ := hinj
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  -- Along an end, `u` stays near the asymptotic value, away from a neighbourhood of `u z₀`.
  have hend {l : Filter ℝ} {x : ℝ → X} (h : Tendsto u (l ×ˢ 𝓝 t₀) (𝓝 (x t₀)))
      (hne : u (s₀, t₀) ≠ x t₀) :
      ∃ p : ℝ → Prop, (∀ᶠ s in l, p s) ∧ ∀ᶠ z in 𝓝 (s₀, t₀), ∀ s, p s → u (s, z.2) ≠ u z := by
    obtain ⟨A, B, hA, hB, hAx, hBx, hAB⟩ := t2_separation hne
    obtain ⟨p, hp, q, hq, hpq⟩ := eventually_prod_iff.1 (h (hB.mem_nhds hBx))
    refine ⟨p, hp, ?_⟩
    filter_upwards [hu.continuousAt.preimage_mem_nhds (hA.mem_nhds hAx),
      continuousAt_snd.preimage_mem_nhds hq] with z hzA hzq s hs heq
    exact disjoint_left.1 hAB hzA (heq ▸ hpq hs hzq)
  obtain ⟨pm, hpm, hevm⟩ := hend hm hm₀
  obtain ⟨pp, hpp, hevp⟩ := hend hp hp₀
  obtain ⟨Sm, hSm⟩ := eventually_atBot.1 hpm
  obtain ⟨Sp, hSp⟩ := eventually_atTop.1 hpp
  -- On the compact rest of the slice, `u` is separated from `u z₀` uniformly nearby.
  have hmid : ∀ᶠ z in 𝓝 (s₀, t₀), ∀ s ∈ Icc Sm Sp \ ball s₀ δ, u (s, z.2) ≠ u z := by
    refine (isCompact_Icc.diff isOpen_ball).eventually_forall_of_forall_eventually
      (P := fun z s ↦ u (s, z.2) ≠ u z) fun s hs ↦ ?_
    have hne : u (s, t₀) ≠ u (s₀, t₀) := fun h ↦
      hs.2 (h₀ s h ▸ mem_ball_self hδ)
    exact ((hu.comp (by fun_prop)).continuousAt.ne_iff_eventually_ne
      (hu.comp continuous_fst).continuousAt).1 hne
  filter_upwards [hevm, hevp, hmid, ball_mem_nhds _ hδ] with z h₁ h₂ h₃ hz s hs
  by_cases hsδ : s ∈ ball s₀ δ
  · -- Near `s₀` the slice is injective.
    rw [← ball_prod_same] at hz
    have hsz : (s, z.2) ∈ U := hδU (by rw [← ball_prod_same]; exact ⟨hsδ, hz.2⟩)
    have hzU : z ∈ U := hδU (by rw [← ball_prod_same]; exact hz)
    exact congrArg Prod.fst (hinj hsz hzU (Prod.ext hs rfl))
  · -- Otherwise `s` lies far along an end or in the compact rest of the slice.
    exfalso
    rcases le_or_gt s Sm with hle | hlt
    · exact h₁ s (hSm s hle) hs
    rcases le_or_gt Sp s with hle' | hlt'
    · exact h₂ s (hSp s hle') hs
    · exact h₃ s ⟨⟨hlt.le, hlt'.le⟩, hsδ⟩ hs

/-- **Points with a unique value on their slice are injective points of `(s, t) ↦ (t, u(s, t))`.**
Let `u : ℝ × ℝ → X` be continuous, with values in a Hausdorff space, and suppose that `u(s, t)`
tends to `xm(t₀)` and `xp(t₀)` as `s → -∞` and `s → +∞` and `t → t₀`. Let `z₀ = (s₀, t₀)` be a
point with `u(z₀) ≠ xm(t₀)`, `u(z₀) ≠ xp(t₀)` and `u(s, t₀) ≠ u(z₀)` for all `s ≠ s₀`. Then the
points `z` at which `(z.2, u z)` is close to `(t₀, u z₀)` are close to `z₀`. -/
theorem comap_nhds_le_nhds_of_tendsto {z₀ : ℝ × ℝ} (hu : Continuous u)
    (hm : Tendsto u (atBot ×ˢ 𝓝 z₀.2) (𝓝 (xm z₀.2)))
    (hp : Tendsto u (atTop ×ˢ 𝓝 z₀.2) (𝓝 (xp z₀.2)))
    (hm₀ : u z₀ ≠ xm z₀.2) (hp₀ : u z₀ ≠ xp z₀.2) (h₀ : ∀ s, u (s, z₀.2) = u z₀ → s = z₀.1) :
    (𝓝 (z₀.2, u z₀)).comap (fun z ↦ (z.2, u z)) ≤ 𝓝 z₀ := by
  obtain ⟨s₀, t₀⟩ := z₀
  set l := (𝓝 (t₀, u (s₀, t₀))).comap (fun z : ℝ × ℝ ↦ (z.2, u z))
  have hl : Tendsto (fun z : ℝ × ℝ ↦ (z.2, u z)) l (𝓝 (t₀, u (s₀, t₀))) := tendsto_comap
  have ht : Tendsto Prod.snd l (𝓝 t₀) := (continuous_fst.tendsto _).comp hl
  have hul : Tendsto u l (𝓝 (u (s₀, t₀))) := (continuous_snd.tendsto _).comp hl
  -- Along an end, `u` stays near the asymptotic value, away from a neighbourhood of `u z₀`.
  have hend {f : Filter ℝ} {x : ℝ → X} (h : Tendsto u (f ×ˢ 𝓝 t₀) (𝓝 (x t₀)))
      (hne : u (s₀, t₀) ≠ x t₀) : ∃ p : ℝ → Prop, (∀ᶠ s in f, p s) ∧ ∀ᶠ z in l, ¬p z.1 := by
    obtain ⟨A, B, hA, hB, hAx, hBx, hAB⟩ := t2_separation hne
    obtain ⟨p, hp, q, hq, hpq⟩ := eventually_prod_iff.1 (h (hB.mem_nhds hBx))
    refine ⟨p, hp, ?_⟩
    filter_upwards [hul (hA.mem_nhds hAx), ht hq] with z hzA hzq hpz
    exact disjoint_left.1 hAB hzA (hpq hpz hzq)
  obtain ⟨pm, hpm, hevm⟩ := hend hm hm₀
  obtain ⟨pp, hpp, hevp⟩ := hend hp hp₀
  obtain ⟨Sm, hSm⟩ := eventually_atBot.1 hpm
  obtain ⟨Sp, hSp⟩ := eventually_atTop.1 hpp
  -- So `l` lives on a compact box, and its only cluster point there is `z₀`.
  refine (isCompact_Icc.prod isCompact_Icc).le_nhds_of_unique_clusterPt
    (s := Icc Sm Sp ×ˢ Icc (t₀ - 1) (t₀ + 1)) ?_ fun w _ hw ↦ ?_
  · filter_upwards [hevm, hevp, ht (Icc_mem_nhds (sub_one_lt t₀) (lt_add_one t₀))] with z h₁ h₂ h₃
    exact ⟨⟨(not_le.1 fun h ↦ h₁ (hSm _ h)).le, (not_le.1 fun h ↦ h₂ (hSp _ h)).le⟩, h₃⟩
  · obtain ⟨h₂, h₁⟩ := Prod.mk.inj (eq_of_nhds_neBot
      (hw.map (f := fun z : ℝ × ℝ ↦ (z.2, u z)) (continuous_snd.prodMk hu).continuousAt hl))
    exact Prod.ext (h₀ w.1 (by rw [← h₁, ← h₂])) h₂

/-! ### Partners on a slice -/

/-- The set of pairs `(z, s)` such that `(s, z.2)` lies in `D`, at distance at least `ε` from `z`
on its slice, with the same value `u(s, z.2) = u z`, is closed. -/
theorem isClosed_setOf_slice_eq (hu : Continuous u) {D : Set (ℝ × ℝ)}
    (hD : IsClosed D) (ε : ℝ) :
    IsClosed {q : (ℝ × ℝ) × ℝ | (q.2, q.1.2) ∈ D ∧ ε ≤ |q.2 - q.1.1| ∧ u (q.2, q.1.2) = u q.1} := by
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ ↦ (q.2, q.1.2) := by fun_prop
  exact (hD.preimage hc).inter ((isClosed_le continuous_const
    (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ ↦ |q.2 - q.1.1|)).inter
    (isClosed_eq (hu.comp hc) (hu.comp continuous_fst)))

/-- For a compact set `D`, the points `z` with a partner `s` on their slice, `(s, z.2) ∈ D`, at
distance at least `ε` from `z` and with `u(s, z.2) = u z`, form a closed set. -/
theorem isClosed_setOf_exists_slice_eq (hu : Continuous u) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (ε : ℝ) :
    IsClosed {z : ℝ × ℝ | ∃ s, (s, z.2) ∈ D ∧ ε ≤ |s - z.1| ∧ u (s, z.2) = u z} := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz ↦ ?_)
  have h := (hD.image continuous_fst).eventually_forall_of_forall_eventually (x₀ := z)
    (P := fun z' s ↦ ¬((s, z'.2) ∈ D ∧ ε ≤ |s - z'.1| ∧ u (s, z'.2) = u z')) fun s _ ↦
      (isClosed_setOf_slice_eq hu hD.isClosed ε).isOpen_compl.mem_nhds fun hq ↦ hz ⟨s, hq⟩
  filter_upwards [h] with z' hz' ⟨s, hs⟩
  exact hz' s ⟨_, hs.1, rfl⟩ hs

/-- **Continuity of a unique slice partner.** Let `D` be compact with `(s, t) ↦ (u(s, t), t)`
injective on `D`, and let `φ` pick for every `z` of an open set `U` a partner on its slice,
`(φ z, z.2) ∈ D` with `u(φ z, z.2) = u z`. Then `φ` is continuous on `U`. -/
theorem continuousAt_of_forall_slice_eq (hu : Continuous u) {D U : Set (ℝ × ℝ)}
    {φ : ℝ × ℝ → ℝ} (hD : IsCompact D) (hinj : InjOn (fun w ↦ (u w, w.2)) D)
    (hU : IsOpen U) (hφ : ∀ z ∈ U, (φ z, z.2) ∈ D ∧ u (φ z, z.2) = u z)
    {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ U) : ContinuousAt φ z₀ := by
  have hmem : ∀ᶠ z in 𝓝 z₀, φ z ∈ Prod.fst '' D :=
    eventually_of_mem (hU.mem_nhds hz₀) fun z hz ↦ ⟨(φ z, z.2), (hφ z hz).1, rfl⟩
  refine (hD.image continuous_fst).tendsto_nhds_of_unique_mapClusterPt hmem fun s _ hs ↦ ?_
  -- A cluster value of `φ` at `z₀` is a partner of `z₀`, since the partner condition is closed.
  have hs₀ : (s, z₀.2) ∈ D ∧ u (s, z₀.2) = u z₀ := by
    by_contra hns
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.1
      ((isClosed_setOf_slice_eq hu hD.isClosed 0).isOpen_compl.mem_nhds
        (Set.mem_compl fun h ↦ hns ⟨h.1, h.2.2⟩))
    obtain ⟨z, hzB, hzA, hzU⟩ := ((mapClusterPt_iff_frequently.1 hs B hB).and_eventually
      (inter_mem hA (hU.mem_nhds hz₀))).exists
    exact hAB (Set.mk_mem_prod hzA hzB) ⟨(hφ z hzU).1, abs_nonneg _, (hφ z hzU).2⟩
  -- The partner in `D` is unique.
  exact congrArg Prod.fst (hinj hs₀.1 (hφ z₀ hz₀).1
    (Prod.ext (hs₀.2.trans (hφ z₀ hz₀).2.symm) rfl))

end TauCeti

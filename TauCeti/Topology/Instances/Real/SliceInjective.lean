/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import TauCeti.Topology.Baire.Lemmas
import TauCeti.Topology.Constructions.SumProd

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
(`TauCeti.comap_nhds_le_nhds_of_forall_slice_eq_imp_eq`). The limits confine these points to a
compact box, on which `z₀` is their only cluster point.

A *partner* of `z` on its slice is a point `(s, z.2)` with `u(s, z.2) = u z`. For a compact set
`D`, the points with a partner in `D` at distance at least `ε` form a closed set
(`TauCeti.isClosed_setOf_exists_slice_eq`). If moreover `(s, t) ↦ (u(s, t), t)` is injective
on `D`, a choice of partners in `D` on an open set is continuous
(`TauCeti.continuousAt_of_forall_slice_eq`), and such a choice exists as soon as every point has a
partner in `D` (`TauCeti.exists_continuousOn_slice_eq_of_injOn`).

Conversely to openness, suppose that every point of a nonempty open set `U` has a partner on its
slice other than itself, lying in a set `S`. If `(s, t) ↦ (u(s, t), t)` is locally injective on an
open set `G` containing all but countably many points of `S`, then on a smaller nonempty open set
the partners can be chosen in `G` and continuously
(`TauCeti.exists_continuousOn_slice_eq_of_forall_exists_ne`). The proof covers `U` by countably
many closed sets, those of points with a partner at distance at least `1 / (m + 1)` in one of
countably many compact balls in `G` on which `(s, t) ↦ (u(s, t), t)` is injective, together with
the horizontal lines through the points of `S` outside `G`, and applies Baire's theorem
(`IsOpen.exists_inter_interior_nonempty_of_subset_iUnion`). Inside one such ball the partner is
unique, so it varies continuously.

This is the topological part of the openness and density of the regular points of Floer
trajectories.
-/

public section

open Filter Function Metric Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [T2Space X] {u : ℝ × ℝ → X} {xm xp : ℝ → X}

/-- If `u(s, t)` tends to `x` along `f ×ˢ 𝓝 t₀` and `y ≠ x`, then eventually along `f` and for `t`
near `t₀`, `u(s, t)` stays out of a neighbourhood of `y`. -/
private theorem exists_forall_notMem_of_tendsto {f : Filter ℝ} {t₀ : ℝ} {x y : X}
    (h : Tendsto u (f ×ˢ 𝓝 t₀) (𝓝 x)) (hne : y ≠ x) :
    ∃ p : ℝ → Prop, (∀ᶠ s in f, p s) ∧ ∃ A ∈ 𝓝 y, ∃ q ∈ 𝓝 t₀,
      ∀ s, p s → ∀ t ∈ q, u (s, t) ∉ A := by
  obtain ⟨A, B, hA, hB, hAy, hBx, hAB⟩ := t2_separation hne
  obtain ⟨p, hp, q, hq, hpq⟩ := eventually_prod_iff.1 (h (hB.mem_nhds hBx))
  exact ⟨p, hp, A, hA.mem_nhds hAy, {t | q t}, hq, fun s hs t ht hA' ↦
    disjoint_left.1 hAB hA' (hpq hs ht)⟩

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
    obtain ⟨p, hp, A, hA, q, hq, hpq⟩ := exists_forall_notMem_of_tendsto h hne
    refine ⟨p, hp, ?_⟩
    filter_upwards [hu.continuousAt.preimage_mem_nhds hA,
      continuousAt_snd.preimage_mem_nhds hq] with z hzA hzq s hs heq
    exact hpq s hs _ hzq (heq ▸ hzA)
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
theorem comap_nhds_le_nhds_of_forall_slice_eq_imp_eq {z₀ : ℝ × ℝ} (hu : Continuous u)
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
  obtain ⟨pm, hpm, Am, hAm, qm, hqm, hevm⟩ := exists_forall_notMem_of_tendsto hm hm₀
  obtain ⟨pp, hpp, Ap, hAp, qp, hqp, hevp⟩ := exists_forall_notMem_of_tendsto hp hp₀
  obtain ⟨Sm, hSm⟩ := eventually_atBot.1 hpm
  obtain ⟨Sp, hSp⟩ := eventually_atTop.1 hpp
  -- So `l` lives on a compact box, and its only cluster point there is `z₀`.
  refine (isCompact_Icc.prod isCompact_Icc).le_nhds_of_unique_clusterPt
    (s := Icc Sm Sp ×ˢ Icc (t₀ - 1) (t₀ + 1)) ?_ fun w _ hw ↦ ?_
  · filter_upwards [hul hAm, hul hAp, ht hqm, ht hqp,
      ht (Icc_mem_nhds (sub_one_lt t₀) (lt_add_one t₀))] with z hzm hzp hqm hqp h₃
    exact ⟨⟨(not_le.1 fun h ↦ hevm _ (hSm _ h) _ hqm hzm).le,
      (not_le.1 fun h ↦ hevp _ (hSp _ h) _ hqp hzp).le⟩, h₃⟩
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

/-- **Partners in a compact set on which `(s, t) ↦ (u(s, t), t)` is injective can be chosen
continuously.** Let `u` be continuous and `K` compact with `(s, t) ↦ (u(s, t), t)` injective on
`K`. If every point `z` of an open set `W` has a partner `(s, z.2) ∈ K` on its slice, with
`u(s, z.2) = u(z)`, then there is `φ`, continuous on `W`, with `(φ(z), z.2) ∈ K` and
`u(φ(z), z.2) = u(z)` for every `z ∈ W`. -/
theorem exists_continuousOn_slice_eq_of_injOn {K W : Set (ℝ × ℝ)} (hu : Continuous u)
    (hK : IsCompact K) (hinj : InjOn (fun z ↦ (u z, z.2)) K) (hW : IsOpen W)
    (h : ∀ z ∈ W, ∃ s, (s, z.2) ∈ K ∧ u (s, z.2) = u z) :
    ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ W ∧ ∀ z ∈ W, (φ z, z.2) ∈ K ∧ u (φ z, z.2) = u z := by
  choose! φ hφ using h
  exact ⟨φ, fun z hz ↦ (continuousAt_of_forall_slice_eq hu hK hinj hW hφ hz).continuousWithinAt,
    hφ⟩

omit [TopologicalSpace X] [T2Space X] in
/-- An open set `G`, near each point of which `(s, t) ↦ (u(s, t), t)` is injective, is covered by
countably many closed balls contained in `G` on which this map is injective. -/
private theorem exists_countable_closedBall_cover_injOn {G : Set (ℝ × ℝ)} (hG : IsOpen G)
    (hGinj : ∀ p ∈ G, ∃ N ∈ 𝓝 p, InjOn (fun z ↦ (u z, z.2)) N) :
    ∃ T : Set (ℝ × ℝ), T.Countable ∧ ∃ r : ℝ × ℝ → ℝ, G ⊆ ⋃ p ∈ T, closedBall p (r p) ∧
      (∀ p ∈ T, closedBall p (r p) ⊆ G) ∧
      ∀ p ∈ T, InjOn (fun z ↦ (u z, z.2)) (closedBall p (r p)) := by
  have hK (p) (hp : p ∈ G) : ∃ r > 0, closedBall p r ⊆ G ∧
      InjOn (fun z ↦ (u z, z.2)) (closedBall p r) := by
    obtain ⟨N, hN, hinj⟩ := hGinj p hp
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 (inter_mem (hG.mem_nhds hp) hN)
    have hsub := (closedBall_subset_ball (half_lt_self hε)).trans hεs
    exact ⟨ε / 2, half_pos hε, fun q hq ↦ (hsub hq).1, hinj.mono fun q hq ↦ (hsub hq).2⟩
  choose! r hr hrG hrinj using hK
  obtain ⟨T, hTG, hTc, hGT⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := G)
    (f := fun p ↦ closedBall p (r p)) fun p hp ↦
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds p (hr p hp))
  exact ⟨T, hTc, r, hGT, fun p hp ↦ hrG p (hTG hp), fun p hp ↦ hrinj p (hTG hp)⟩

/-- **The Baire step.** Let `u : ℝ × ℝ → X` be continuous, let `G` be a set covered by the closed
balls of a countable family indexed by `T`, containing all but countably many points of a set
`S`, and suppose that every point `(s, t)` of a nonempty open set `U` has a partner `s' ≠ s` on
its slice, with `(s', t) ∈ S` and `u(s', t) = u(s, t)`. Then for some `p ∈ T` and `m : ℕ`, the set
of points with a partner in the ball of `p` at distance at least `1 / (m + 1)` has interior points
in `U`. -/
private theorem exists_nonempty_inter_interior_setOf_slice_eq {G S U T : Set (ℝ × ℝ)}
    {r : ℝ × ℝ → ℝ} (hu : Continuous u) (hGc : (S \ G).Countable) (hTc : T.Countable)
    (hGT : G ⊆ ⋃ p ∈ T, closedBall p (r p)) (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, ∃ s ≠ z.1, (s, z.2) ∈ S ∧ u (s, z.2) = u z) :
    ∃ p ∈ T, ∃ m : ℕ, (U ∩ interior {z | ∃ s, (s, z.2) ∈ closedBall p (r p) ∧
      1 / ((m : ℝ) + 1) ≤ |s - z.1| ∧ u (s, z.2) = u z}).Nonempty := by
  -- The closed sets of points with a partner in the ball of `p ∈ T` at distance at least
  -- `1 / (m + 1)` and the horizontal lines through the countably many points of `S` outside `G`
  -- cover `U`.
  have := hTc.to_subtype
  have := hGc.to_subtype
  let f : (T × ℕ) ⊕ (S \ G : Set (ℝ × ℝ)) → Set (ℝ × ℝ)
    | .inl i => {z | ∃ s, (s, z.2) ∈ closedBall (i.1 : ℝ × ℝ) (r i.1) ∧
        1 / ((i.2 : ℝ) + 1) ≤ |s - z.1| ∧ u (s, z.2) = u z}
    | .inr q => Prod.snd ⁻¹' {(q : ℝ × ℝ).2}
  have hf (i) : IsClosed (f i) := by
    rcases i with i | q
    exacts [isClosed_setOf_exists_slice_eq hu (isCompact_closedBall _ _) _,
      isClosed_singleton.preimage continuous_snd]
  have hcover : U ⊆ ⋃ i, f i := fun z hzU ↦ by
    obtain ⟨s, hs, hsS, hsu⟩ := h z hzU
    refine mem_iUnion.2 ?_
    by_cases hq : (s, z.2) ∈ G
    · obtain ⟨p, hp, hpq⟩ := mem_iUnion₂.1 (hGT hq)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hs))
      exact ⟨.inl (⟨p, hp⟩, m), s, hpq, hm.le, hsu⟩
    · exact ⟨.inr ⟨(s, z.2), hsS, hq⟩, rfl⟩
  -- By Baire's theorem one of these sets has interior points in `U`; only the first kind can,
  -- since lines have empty interior.
  obtain ⟨i, z, hzU, hz⟩ := hU.exists_inter_interior_nonempty_of_subset_iUnion hUne hf hcover
  rcases i with i | q
  · exact ⟨i.1, i.1.property, i.2, z, hzU, hz⟩
  · exact absurd hz (by
      simp only [f, interior_preimage_snd_singleton, notMem_empty, not_false_eq_true])

/-- **Continuous choice of partners on an open set, by Baire's theorem.** Let
`u : ℝ × ℝ → X` be continuous, with values in a Hausdorff space, and let `G` be an open set, near
each point of which `(s, t) ↦ (u(s, t), t)` is injective, containing all but countably many points
of a set `S`. If every point `(s, t)` of a nonempty open set `U` has a partner `s' ≠ s` on its
slice, with `(s', t) ∈ S` and `u(s', t) = u(s, t)`, then on some nonempty open `W ⊆ U` these
partners can be chosen continuously and in `G`: there is `φ`, continuous on `W`, with
`φ(z) ≠ z.1`, `u(φ(z), z.2) = u(z)` and `(φ(z), z.2) ∈ G` for every `z ∈ W`. For `S = univ`,
`G` has countable complement. -/
theorem exists_continuousOn_slice_eq_of_forall_exists_ne {G S U : Set (ℝ × ℝ)}
    (hu : Continuous u) (hG : IsOpen G)
    (hGinj : ∀ p ∈ G, ∃ N ∈ 𝓝 p, InjOn (fun z ↦ (u z, z.2)) N) (hGc : (S \ G).Countable)
    (hU : IsOpen U) (hUne : U.Nonempty) (h : ∀ z ∈ U, ∃ s ≠ z.1, (s, z.2) ∈ S ∧ u (s, z.2) = u z) :
    ∃ W ⊆ U, IsOpen W ∧ W.Nonempty ∧ ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ W ∧
      ∀ z ∈ W, φ z ≠ z.1 ∧ u (φ z, z.2) = u z ∧ (φ z, z.2) ∈ G := by
  obtain ⟨T, hTc, r, hGT, hrG, hrinj⟩ := exists_countable_closedBall_cover_injOn hG hGinj
  -- Some set `A` of points with a partner in the ball of `p ∈ T` at distance at least
  -- `1 / (m + 1)` has interior points in `U`.
  obtain ⟨p, hp, m, hne⟩ := exists_nonempty_inter_interior_setOf_slice_eq hu hGc hTc hGT hU hUne h
  let A : Set (ℝ × ℝ) := {z | ∃ s, (s, z.2) ∈ closedBall p (r p) ∧
    1 / ((m : ℝ) + 1) ≤ |s - z.1| ∧ u (s, z.2) = u z}
  -- On `U ∩ interior A`, the partner in the ball is unique, hence continuous.
  have hinj := hrinj p hp
  have hA (w) (hw : w ∈ U ∩ interior A) : ∃ s, (s, w.2) ∈ closedBall p (r p) ∧
      1 / ((m : ℝ) + 1) ≤ |s - w.1| ∧ u (s, w.2) = u w :=
    interior_subset hw.2
  obtain ⟨φ, hφc, hφ⟩ := exists_continuousOn_slice_eq_of_injOn hu (isCompact_closedBall _ _) hinj
    (hU.inter isOpen_interior) fun w hw ↦ by
      obtain ⟨s, hs, -, hsu⟩ := hA w hw
      exact ⟨s, hs, hsu⟩
  refine ⟨U ∩ interior A, inter_subset_left, hU.inter isOpen_interior, hne, φ, hφc,
    fun w hw ↦ ⟨fun he ↦ ?_, (hφ w hw).2, hrG p hp (hφ w hw).1⟩⟩
  obtain ⟨s, hs, hd, hsu⟩ := hA w hw
  have hsφ : s = φ w :=
    congrArg Prod.fst (hinj hs (hφ w hw).1 (by simp only [hsu, (hφ w hw).2]))
  rw [hsφ, he, sub_self, abs_zero] at hd
  exact (one_div_pos.2 (by positivity)).not_ge hd

end TauCeti

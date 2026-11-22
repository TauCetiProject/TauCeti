/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Points with unique values on the horizontal slices of a map on `ℝ × ℝ`

Let `u : ℝ × ℝ → X` be a continuous map into a Hausdorff space such that `u(s, t)` tends to
`xm(t₀)` as `s → -∞` and `t → t₀` together, and to `xp(t₀)` as `s → +∞` and `t → t₀` together.
If `z₀ = (s₀, t₀)` is the only point of its slice with value `u(z₀)`, away from the limits, and
`(s, t) ↦ (u(s, t), t)` is injective near `z₀`, then every nearby point is the only point of its
slice with its value (`TauCeti.eventually_forall_slice_eq_imp_eq_of_tendsto`). The limits confine
the competitors to a compact interval, and a compactness argument separates them uniformly
nearby.

This is the topological part of the openness of the regular points of Floer trajectories.

Conversely, suppose that every point of a nonempty open set `U` has a competitor on its slice: a
point `(s', t) ≠ (s, t)` with `u(s', t) = u(s, t)`. If `(s, t) ↦ (u(s, t), t)` is locally
injective on an open set `G` with countable complement, then on a smaller nonempty open set the
competitors can be chosen in `G` and continuously
(`TauCeti.exists_continuousOn_slice_eq_of_forall_exists_ne`). The proof covers `U` by countably
many closed sets, those of points with a competitor at distance at least `1 / (m + 1)` in one of
countably many compact balls in `G` on which `(s, t) ↦ (u(s, t), t)` is injective, together with
the horizontal lines through the points outside `G`, and applies Baire's theorem. Inside one such
ball the competitor is unique, so it varies continuously
(`TauCeti.exists_continuousOn_slice_eq_of_injOn`). This is the topological part of the density
of the regular points of Floer trajectories.
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

/-- **Competitors in a compact set on which `(s, t) ↦ (u(s, t), t)` is injective can be chosen
continuously.** Let `u` be continuous and `K` compact with `(s, t) ↦ (u(s, t), t)` injective on
`K`. If every point `z` of an open set `W` has a point `q ∈ K` on its slice, `q.2 = z.2`, with
`u(q) = u(z)`, then there is `φ`, continuous on `W`, with `(φ(z), z.2) ∈ K` and
`u(φ(z), z.2) = u(z)` for every `z ∈ W`. -/
theorem exists_continuousOn_slice_eq_of_injOn {K W : Set (ℝ × ℝ)} (hu : Continuous u)
    (hK : IsCompact K) (hinj : InjOn (fun z ↦ (u z, z.2)) K) (hW : IsOpen W)
    (h : ∀ z ∈ W, ∃ q ∈ K, q.2 = z.2 ∧ u q = u z) :
    ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ W ∧ ∀ z ∈ W, (φ z, z.2) ∈ K ∧ u (φ z, z.2) = u z := by
  classical
  let φ : ℝ × ℝ → ℝ := fun z ↦ if hz : z ∈ W then (h z hz).choose.1 else 0
  have hφ (z) (hz : z ∈ W) : (φ z, z.2) ∈ K ∧ u (φ z, z.2) = u z := by
    obtain ⟨hq, hq2, hqu⟩ := (h z hz).choose_spec
    have he : (φ z, z.2) = (h z hz).choose := by
      simp only [φ, hz, ↓reduceDIte]
      exact Prod.ext rfl hq2.symm
    exact ⟨he ▸ hq, he ▸ hqu⟩
  refine ⟨φ, fun w hw ↦ ?_, hφ⟩
  have hev : ∀ᶠ v in 𝓝 w, v ∈ W := hW.mem_nhds hw
  have hΦ : Continuous fun z : ℝ × ℝ ↦ (u z, z.2) := hu.prodMk continuous_snd
  -- The points `(φ v, v.2)` stay in `K`, and each of their cluster points as `v → w` has the
  -- image `(u w, w.2)` of `(φ w, w.2)` under the map `(s, t) ↦ (u(s, t), t)`, injective on `K`.
  have hlim : Tendsto (fun v ↦ (φ v, v.2)) (𝓝 w) (𝓝 (φ w, w.2)) := by
    refine hK.tendsto_nhds_of_unique_mapClusterPt (hev.mono fun v hv ↦ (hφ v hv).1)
      fun q hq hcl ↦ hinj hq (hφ w hw).1 ?_
    have hlim' : Tendsto (fun v ↦ (u (φ v, v.2), (φ v, v.2).2)) (𝓝 w) (𝓝 (u w, w.2)) :=
      (hΦ.tendsto w).congr' (hev.mono fun v hv ↦ by simp only [(hφ v hv).2])
    simp only [eq_of_nhds_neBot (ClusterPt.mono (hcl.continuousAt_comp hΦ.continuousAt) hlim'),
      (hφ w hw).2]
  exact ContinuousAt.continuousWithinAt ((continuous_fst.tendsto _).comp hlim)

/-- The points `z` with a competitor `q` in a compact set `K`, on the slice of `z`, with
`u(q) = u(z)` and `|q.1 - z.1| ≥ δ`, form a closed set: it is the projection of a closed set
along the compact factor `K`. -/
private theorem isClosed_setOf_exists_slice_eq {K : Set (ℝ × ℝ)} (hu : Continuous u)
    (hK : IsCompact K) (δ : ℝ) :
    IsClosed {z : ℝ × ℝ | ∃ q ∈ K, q.2 = z.2 ∧ u q = u z ∧ δ ≤ |q.1 - z.1|} := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hq : Continuous fun x : (ℝ × ℝ) × K ↦ (x.2 : ℝ × ℝ) :=
    continuous_subtypeVal.comp continuous_snd
  have hS : IsClosed {x : (ℝ × ℝ) × K | (x.2 : ℝ × ℝ).2 = x.1.2 ∧ u x.2 = u x.1 ∧
      δ ≤ |(x.2 : ℝ × ℝ).1 - x.1.1|} :=
    (isClosed_eq (continuous_snd.comp hq) (continuous_snd.comp continuous_fst)).inter
      ((isClosed_eq (hu.comp hq) (hu.comp continuous_fst)).inter (isClosed_le continuous_const
        ((continuous_fst.comp hq).sub (continuous_fst.comp continuous_fst)).abs))
  convert isClosedMap_fst_of_compactSpace _ hS using 1
  ext z
  constructor
  · rintro ⟨q, hq, hq'⟩
    exact ⟨(z, ⟨q, hq⟩), hq', rfl⟩
  · rintro ⟨⟨w, q, hq⟩, hq', rfl⟩
    exact ⟨q, hq, hq'⟩

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

/-- **Continuous choice of competitors on an open set, by Baire's theorem.** Let
`u : ℝ × ℝ → X` be continuous, with values in a Hausdorff space, and let `G` be an open set whose
complement is countable, near each point of which `(s, t) ↦ (u(s, t), t)` is injective. If every
point `(s, t)` of a nonempty open set `U` has a competitor `s' ≠ s` on its slice, with
`u(s', t) = u(s, t)`, then on some nonempty open `W ⊆ U` these competitors can be chosen
continuously and in `G`: there is `φ`, continuous on `W`, with `φ(z) ≠ z.1`,
`u(φ(z), z.2) = u(z)` and `(φ(z), z.2) ∈ G` for every `z ∈ W`. -/
theorem exists_continuousOn_slice_eq_of_forall_exists_ne {G U : Set (ℝ × ℝ)} (hu : Continuous u)
    (hG : IsOpen G) (hGinj : ∀ p ∈ G, ∃ N ∈ 𝓝 p, InjOn (fun z ↦ (u z, z.2)) N)
    (hGc : Gᶜ.Countable) (hU : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, ∃ s ≠ z.1, u (s, z.2) = u z) :
    ∃ W ⊆ U, IsOpen W ∧ W.Nonempty ∧ ∃ φ : ℝ × ℝ → ℝ, ContinuousOn φ W ∧
      ∀ z ∈ W, φ z ≠ z.1 ∧ u (φ z, z.2) = u z ∧ (φ z, z.2) ∈ G := by
  classical
  obtain ⟨T, hTc, r, hGT, hrG, hrinj⟩ := exists_countable_closedBall_cover_injOn hG hGinj
  -- The closed sets of points with a competitor in the ball of `p ∈ T` at distance at least
  -- `1 / (m + 1)`, the complement of `U` and the horizontal lines through the countably many
  -- points outside `G` cover the plane.
  let A : T × ℕ → Set (ℝ × ℝ) := fun i ↦ {z | ∃ q ∈ closedBall (i.1 : ℝ × ℝ) (r i.1),
    q.2 = z.2 ∧ u q = u z ∧ 1 / ((i.2 : ℝ) + 1) ≤ |q.1 - z.1|}
  have := hTc.to_subtype
  have := hGc.to_subtype
  let f : Option ((T × ℕ) ⊕ (Gᶜ : Set (ℝ × ℝ))) → Set (ℝ × ℝ)
    | none => Uᶜ
    | some (.inl i) => A i
    | some (.inr q) => Prod.snd ⁻¹' {(q : ℝ × ℝ).2}
  have hf (i) : IsClosed (f i) := by
    rcases i with _ | i | q
    exacts [hU.isClosed_compl, isClosed_setOf_exists_slice_eq hu (isCompact_closedBall _ _) _,
      isClosed_singleton.preimage continuous_snd]
  have hcover : ⋃ i, f i = univ := by
    refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    by_cases hzU : z ∈ U
    · obtain ⟨s, hs, hsu⟩ := h z hzU
      by_cases hq : (s, z.2) ∈ G
      · obtain ⟨p, hp, hpq⟩ := mem_iUnion₂.1 (hGT hq)
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hs))
        exact ⟨some (.inl (⟨p, hp⟩, m)), (s, z.2), hpq, rfl, hsu, hm.le⟩
      · exact ⟨some (.inr ⟨(s, z.2), hq⟩), rfl⟩
    · exact ⟨none, hzU⟩
  -- By Baire's theorem one of these sets has interior points in `U`; only the `A i` can, since
  -- lines have empty interior.
  obtain ⟨z, hzU, hz⟩ := (dense_iUnion_interior_of_closed hf hcover).inter_open_nonempty U hU hUne
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  rcases i with _ | i | q
  · exact absurd hzU (interior_subset hi)
  swap
  · have hint : interior (Prod.snd ⁻¹' {(q : ℝ × ℝ).2} : Set (ℝ × ℝ)) = ∅ := by
      rw [← isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd, interior_singleton,
        preimage_empty]
    exact absurd hi (by simp only [f, hint, notMem_empty, not_false_eq_true])
  -- On `U ∩ interior (A i)`, the competitor in the ball is unique, hence continuous.
  have hinj := hrinj i.1 i.1.property
  have hA (w) (hw : w ∈ U ∩ interior (A i)) : ∃ q ∈ closedBall (i.1 : ℝ × ℝ) (r i.1),
      q.2 = w.2 ∧ u q = u w ∧ 1 / ((i.2 : ℝ) + 1) ≤ |q.1 - w.1| :=
    interior_subset hw.2
  obtain ⟨φ, hφc, hφ⟩ := exists_continuousOn_slice_eq_of_injOn hu (isCompact_closedBall _ _) hinj
    (hU.inter isOpen_interior) fun w hw ↦ by
      obtain ⟨q, hq, hq2, hqu, -⟩ := hA w hw
      exact ⟨q, hq, hq2, hqu⟩
  refine ⟨U ∩ interior (A i), inter_subset_left, hU.inter isOpen_interior, ⟨z, hzU, hi⟩, φ, hφc,
    fun w hw ↦ ⟨fun he ↦ ?_, (hφ w hw).2, hrG i.1 i.1.property (hφ w hw).1⟩⟩
  obtain ⟨q, hq, hq2, hqu, hd⟩ := hA w hw
  have hqφ : q = (φ w, w.2) := hinj hq (hφ w hw).1 (by simp only [hq2, hqu, (hφ w hw).2])
  rw [hqφ, he, sub_self, abs_zero] at hd
  exact (one_div_pos.2 (by positivity)).not_ge hd

end TauCeti

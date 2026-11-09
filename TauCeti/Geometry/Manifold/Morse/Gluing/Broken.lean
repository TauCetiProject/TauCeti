/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.BoxCrossing
public import TauCeti.Geometry.Manifold.Morse.Stable.Gluing
public import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Dynamics.Flow.LevelCrossing

/-!
# Gluing at a broken index-two trajectory

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `q`, `r` critical points with
`ind p = ind q + 1 = ind r + 2`. Record the trajectories from `p` to `r` by their points on two
levels: for a point `a₁` of a trajectory from `p` to `q` and a point `a₂` of a trajectory from `q`
to `r`, the unbroken trajectories give the pairs `(w₁, w₂)` of points of one trajectory from `p` to
`r` with `f w₁ = f a₁` and `f w₂ = f a₂`, and the broken trajectory through `a₁` and `a₂` gives
the pair `(a₁, a₂)`. The main theorem shows that `(a₁, a₂)` has a neighbourhood among these pairs
homeomorphic to a half-open interval `[0, δ)`. These are the local half-open models that
`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico` needs at the broken pairs, once the
compactified space of index-two trajectories is assembled from them and the charts at unbroken
pairs.

The proof transports the gluing in the split model of a Morse box at `q`
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`), which
describes the pairs of a model entrance point and a model exit point joined by the passage map as
a half-open arc whose closure adds only the broken pair, to the two levels:

* a trajectory near the broken one crosses the box once, so its model entrance and exit points
  form one of these pairs
  (`TauCeti.IsAdaptedPseudoGradient.splitPassage_splitEntryTime_eq_splitExitTime`);
* following the flow to the two levels is continuous at both broken and unbroken trajectories,
  since the level points depend continuously on the orbit along connecting trajectories.

So the level points of the gluing arc form a continuous injective arc in `M × M` from `(a₁, a₂)`,
which contains every unbroken pair near `(a₁, a₂)`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`: a broken trajectory has
  a neighbourhood homeomorphic to `[0, δ)` among the unbroken trajectories recorded on two levels.
* `IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet`: every broken trajectory is a
  limit of unbroken ones.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- A gluing parameter small enough for the passage to be unique: for `ε > 0`, `r₀ > 0` and
`n ≥ 0`, some `r₁ ∈ (0, min r₀ 1]` makes `n u² < ε²` for all `u ∈ [0, r₁ ε]`. -/
private theorem exists_pos_forall_mul_sq_lt {r₀ ε n : ℝ} (hr₀ : 0 < r₀) (hε : 0 < ε)
    (hn : 0 ≤ n) :
    ∃ r₁, 0 < r₁ ∧ r₁ ≤ r₀ ∧ r₁ ≤ 1 ∧ ∀ u, 0 ≤ u → u ≤ r₁ * ε → n * u ^ 2 < ε ^ 2 := by
  set r₁ := min r₀ (1 / (n + 1))
  have hr₁ : 0 < r₁ := lt_min hr₀ (by positivity)
  have hr₁n : n * (r₁ * ε) ^ 2 < ε ^ 2 := by
    have h₁ : r₁ * (n + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
    have h₂ : 0 < r₁ * ε := mul_pos hr₁ hε
    have h₃ : r₁ * ε * (n + 1) ≤ ε := by nlinarith
    have h₄ : (r₁ * ε * (n + 1)) ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (by positivity) h₃ 2
    nlinarith [mul_pos h₂ h₂]
  exact ⟨r₁, hr₁, min_le_left _ _,
    (min_le_right _ _).trans ((div_le_one (by positivity)).2 (by linarith)), fun u hu hu' ↦
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hu' 2) hn) hr₁n⟩

/-- A map on `[0, δ]` is injective if it is injective away from `0` and takes its value at `0`
nowhere else. -/
private theorem injective_of_forall_ne_zero {α : Type*} {δ : ℝ} (hδ : 0 ≤ δ)
    {F : Icc (0 : ℝ) δ → α}
    (h₀ : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ≠ F ⟨0, left_mem_Icc.2 hδ⟩)
    (h : ∀ s s' : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (s' : ℝ) ≠ 0 → F s = F s' → s = s') :
    Injective F := by
  intro s s' hss'
  by_cases hs : (s : ℝ) = 0 <;> by_cases hs' : (s' : ℝ) = 0
  · exact Subtype.ext (hs.trans hs'.symm)
  · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ⟩ := Subtype.ext hs
    exact absurd hss'.symm (h₀ s' hs')
  · obtain rfl : s' = ⟨0, left_mem_Icc.2 hδ⟩ := Subtype.ext hs'
    exact absurd hss' (h₀ s hs)
  · exact h s s' hs hs' hss'

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- A model entrance point of the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` that the passage map sends to the exit
face, and its image, read in a Morse chart whose coordinate cube of radius `ε` lies in the chart,
are points of the chart. -/
private theorem MorseChart.coord_symm_splitCoord_symm_mem_target_of_mem_splitPassage_source
    {x : M} {φ : MorseChart E f x} {ε : ℝ}
    (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ (splitPassage ε).source) :
    φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm (splitPassage ε z)) ∈ φ.toChart.target := by
  have htgt := mem_splitPassage_target.1 ((splitPassage ε).map_source hz)
  exact ⟨MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε
      (mem_splitPassage_source.1 hz).1.le (mem_splitPassage_source.1 hz).2.2,
    MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε htgt.2.2 htgt.1.le⟩

namespace IsAdaptedPseudoGradient

/-- **A Morse box at the middle of a broken trajectory.** For a trajectory from `p` to `q` through
`a₁` and one from `q` to `r` through `a₂`, there are a Morse chart `φ` at `q` in which `X` is
linear and a radius `ε` such that the cube of radius `2 ε` lies in the chart, the stable and
unstable sets of `q` are the coordinate planes on a cube of radius larger than `2 ε`, and the two
trajectories cross the entrance and exit faces of the box at points `y₁` and `y₂` of the
coordinate planes. -/
private theorem exists_morseBox_of_broken (hX : IsAdaptedPseudoGradient f X)
    (hf : IsMorse 𝓘(ℝ, E) f) {p q r a₁ a₂ : M} (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hpq : p ≠ q) (hqr : q ≠ r) (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (φ : MorseChart E f q) (ε ρ T₁ T₂ : ℝ) (y₁ y₂ : M),
      (∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      0 < ε ∧ 2 * ε < ρ ∧ (∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target) ∧
      (∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < ρ →
        (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
        (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)) ∧
      hX.flow T₁ a₁ = y₁ ∧ hX.flow T₂ a₂ = y₂ ∧ y₁ ∈ φ.toChart.source ∧ y₂ ∈ φ.toChart.source ∧
      (φ.splitCoord (φ.coord (φ.toChart y₁))).snd = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₁))).fst‖ = ε ∧
      (φ.splitCoord (φ.coord (φ.toChart y₂))).fst = 0 ∧
      ‖(φ.splitCoord (φ.coord (φ.toChart y₂))).snd‖ = ε := by
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  have hφ' := φ.coord_mfderiv_neg hφ hnd
  have hfd' : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) (-f) := hf.neg.contMDiff.mdifferentiable (by simp)
  -- The local descriptions of the stable and unstable sets, and of the flow on them.
  obtain ⟨ρs, hρs, hs⟩ := hX.exists_forall_mem_stableSet_iff φ hφ hfd
  obtain ⟨ρu, hρu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd) hφ' hfd'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hu
  obtain ⟨ρc, hρc, hc⟩ := hX.exists_forall_coord_flow_eq_exp_smul φ hφ hfd
  obtain ⟨ρc', hρc', hc'⟩ := (hX.neg hf).exists_forall_coord_flow_eq_exp_smul (φ.neg hnd) hφ' hfd'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, hX.neg_flow hf, Flow.stableSet_reverse,
    Flow.reverse_apply] at hc'
  obtain ⟨rT, hrT, hT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  have hsplit : ∀ w ∈ φ.toChart.source, ‖φ.coord (φ.toChart w)‖ < min ρs ρu →
      (w ∈ hX.flow.stableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
      (w ∈ hX.flow.unstableSet q ↔ (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) :=
    fun w hw hwρ ↦ ⟨(hs w hw (hwρ.trans_le (min_le_left _ _))).trans
      (by simp [funext_iff, φ.weight_ne_one_iff]),
      (hu w hw (hwρ.trans_le (min_le_right _ _))).trans (by simp [funext_iff, φ.weight_eq_one_iff])⟩
  set δ := min (min (min ρs ρu / 2) ρc) (min ρc' (rT / 4)) with hδdef
  have hδ : 0 < δ := by positivity
  -- Points of the two trajectories in the cube of radius `δ`.
  have hN : {w | w ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart w)‖ < δ} ∈ 𝓝 q := by
    have hcont : ContinuousAt (fun w ↦ ‖φ.coord (φ.toChart w)‖) q :=
      (φ.continuous_coord.norm.continuousAt).comp (φ.toChart.continuousAt φ.mem_source)
    filter_upwards [φ.toChart.open_source.mem_nhds φ.mem_source,
      hcont.eventually (gt_mem_nhds (by simpa using hδ))] with w hw hwδ using ⟨hw, hwδ⟩
  obtain ⟨t₁, hb₁, hb₁δ⟩ := ((Flow.mem_stableSet.1 ha₁.2).eventually hN).exists
  obtain ⟨t₂, hb₂, hb₂δ⟩ := ((Flow.mem_unstableSet.1 ha₂.1).eventually hN).exists
  set b₁ := hX.flow t₁ a₁
  set b₂ := hX.flow t₂ a₂
  have hb₁m : b₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q t₁ ha₁
  have hb₂m : b₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hX.flow.isInvariant_unstableSet_inter_stableSet q r t₂ ha₂
  -- Their coordinates are nonzero, since they are not the critical point.
  have hz₁ : 0 < ‖φ.coord (φ.toChart b₁)‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have hb := (φ.toChart_eq_zero_iff hb₁).1 (by simpa using h)
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq hb₁m
    rw [hb] at this
    exact this.1.ne rfl
  have hz₂ : 0 < ‖φ.coord (φ.toChart b₂)‖ := by
    refine norm_pos_iff.2 fun h ↦ ?_
    have hb := (φ.toChart_eq_zero_iff hb₂).1 (by simpa using h)
    have := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqr hb₂m
    rw [hb] at this
    exact this.2.ne rfl
  set ε := min ‖φ.coord (φ.toChart b₁)‖ ‖φ.coord (φ.toChart b₂)‖ with hεdef
  have hε : 0 < ε := lt_min hz₁ hz₂
  have hεδ : ε < δ := (min_le_left _ _).trans_lt hb₁δ
  -- Flow the two points to the faces of the box of radius `ε`.
  set s₁ := Real.log (‖φ.coord (φ.toChart b₁)‖ / ε)
  set s₂ := Real.log (‖φ.coord (φ.toChart b₂)‖ / ε)
  have hs₁ : 0 ≤ s₁ := Real.log_nonneg ((one_le_div hε).2 (min_le_left _ _))
  have hs₂ : 0 ≤ s₂ := Real.log_nonneg ((one_le_div hε).2 (min_le_right _ _))
  obtain ⟨hy₁, hy₁c⟩ := hc b₁ hb₁m.2 hb₁ (hb₁δ.trans_le (by simp [hδdef])) s₁ hs₁
  obtain ⟨hy₂, hy₂c⟩ := hc' b₂ hb₂m.1 hb₂ (hb₂δ.trans_le (by simp [hδdef])) s₂ hs₂
  have he₁ : Real.exp (-s₁) * ‖φ.coord (φ.toChart b₁)‖ = ε := by
    rw [Real.exp_neg, Real.exp_log (div_pos hz₁ hε)]; field_simp
  have he₂ : Real.exp (-s₂) * ‖φ.coord (φ.toChart b₂)‖ = ε := by
    rw [Real.exp_neg, Real.exp_log (div_pos hz₂ hε)]; field_simp
  have hδρ : δ ≤ min ρs ρu / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδT : δ ≤ rT / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hb₁s := ((hsplit b₁ hb₁ (by linarith [hb₁δ])).1.1 hb₁m.2)
  have hb₂u := ((hsplit b₂ hb₂ (by linarith [hb₂δ])).2.1 hb₂m.1)
  refine ⟨φ, ε, min ρs ρu, s₁ + t₁, -s₂ + t₂, hX.flow s₁ b₁, hX.flow (-s₂) b₂, hφ, hε,
    by linarith, fun z hz ↦ hT z (by linarith), hsplit, Flow.map_add _ _ _ _,
    Flow.map_add _ _ _ _, hy₁, hy₂, ?_, ?_, ?_, ?_⟩
  · rw [hy₁c, map_smul, WithLp.smul_snd, hb₁s, smul_zero]
  · have h := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow s₁ b₁)))
    rw [hy₁c, map_smul, WithLp.smul_snd, hb₁s, smul_zero, norm_zero, ← map_smul, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, he₁] at h
    rwa [max_eq_left (norm_nonneg _), ← hy₁c] at h
  · rw [hy₂c, map_smul, WithLp.smul_fst, hb₂u, smul_zero]
  · have h := φ.max_norm_fst_norm_snd_splitCoord (φ.coord (φ.toChart (hX.flow (-s₂) b₂)))
    rw [hy₂c, map_smul, WithLp.smul_fst, hb₂u, smul_zero, norm_zero, ← map_smul, norm_smul,
      Real.norm_of_nonneg (Real.exp_pos _).le, he₂] at h
    rwa [max_eq_right (norm_nonneg _), ← hy₂c] at h


/-- **A model passage through the box joins `p` to `r`.** Let `X` be linear in the Morse chart
`φ`, whose coordinate cube of radius `ε` lies in the chart, and let `z` be a model entrance point
that the passage map sends to the exit face. If the point with split coordinates `z` is on the
orbit of a point of `W^u(p)`, and the point with split coordinates `splitPassage ε z` on the orbit
of a point of `W^s(r)`, then the first lies on a trajectory from `p` to `r`, and the flow carries
it to the second at the model exit time. -/
private theorem mem_unstableSet_inter_stableSet_of_mem_splitPassage_source
    (hX : IsAdaptedPseudoGradient f X) {x : M} (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ (splitPassage ε).source) {p r w₁ w₂ : M} {t₁ t₂ : ℝ}
    (hw₁ : w₁ ∈ hX.flow.unstableSet p) (hw₂ : w₂ ∈ hX.flow.stableSet r)
    (h₁ : hX.flow t₁ w₁ = φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))
    (h₂ : hX.flow t₂ w₂ = φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitPassage ε z)))) :
    φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) ∈
        hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      hX.flow (splitExitTime ε z) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitPassage ε z))) := by
  have h₃ := hX.flow_splitExitTime φ hφ hε hz
  refine ⟨⟨h₁ ▸ (Flow.apply_mem_unstableSet_iff _ _).2 hw₁, ?_⟩, h₃⟩
  have h₄ := h₂ ▸ (Flow.apply_mem_stableSet_iff _ _).2 hw₂
  rw [← h₃] at h₄
  exact (Flow.apply_mem_stableSet_iff _ _).1 h₄

/-- **The model gluing arc at a broken trajectory, on the manifold.** For a trajectory from `p`
through `a₁` to `q` and one from `q` through `a₂` to `r`, of consecutive indices, there are points
`flow T₁ a₁` and `flow T₂ a₂` of the two trajectories and a continuous arc `B` in `M × M`, starting
at this pair, along which `B s` is, for `s ≠ 0`, a pair of points of one trajectory from `p` to
`r`, different `s` giving different trajectories. Every pair of points of one trajectory from `p`
to `r` on the levels of `flow T₁ a₁` and `flow T₂ a₂` near this pair lies on the trajectories of
some `B s` with `s` below the end of the arc. -/
private theorem IsMorseSmale.exists_gluingArc {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q r a₁ a₂ : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (T₁ T₂ δ : ℝ) (hδ : 0 < δ) (B : Icc (0 : ℝ) δ → M × M), Continuous B ∧
      B ⟨0, left_mem_Icc.2 hδ.le⟩ = (hX.flow T₁ a₁, hX.flow T₂ a₂) ∧
      (∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 →
        (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ ∃ t, hX.flow t (B s).1 = (B s).2) ∧
      (∀ s s' : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → (s' : ℝ) ≠ 0 → ∀ t,
        hX.flow t (B s).1 = (B s').1 → s = s') ∧
      ∀ᶠ w : M × M in 𝓝 (hX.flow T₁ a₁, hX.flow T₂ a₂),
        w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r → f w.1 = f (hX.flow T₁ a₁) →
        f w.2 = f (hX.flow T₂ a₂) → (∃ t, hX.flow t w.1 = w.2) →
        ∃ s : Icc (0 : ℝ) δ, (s : ℝ) < δ ∧ (∃ t, hX.flow t w.1 = (B s).1) ∧
          ∃ t, hX.flow t w.2 = (B s).2 := by
  -- Plan: choose a Morse box at `q` with entrance point `y₁` and exit point `y₂`
  -- (`exists_morseBox_of_broken`), apply the model gluing theorem there, and take as `B` the points
  -- with the coordinates of the gluing pairs of small parameter. Uniqueness of the passage gives
  -- the injectivity clause, and `splitPassage_splitEntryTime_eq_splitExitTime` the last clause.
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hpr' : p ≠ r := by rintro rfl; omega
  obtain ⟨φ, ε, ρ, T₁, T₂, y₁, y₂, hφ, hε, hερ, hε₂, hloc, hT₁, hT₂, hy₁φ, hy₂φ, hy₁s, hy₁ε,
    hy₂u, hy₂ε⟩ := hX.exists_morseBox_of_broken hf hq hpq' hqr' ha₁ ha₂
  set Φ : M → WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
    fun w ↦ φ.splitCoord (φ.coord (φ.toChart w)) with hΦdef
  set Ψ : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) → M :=
    fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) with hΨdef
  have hΨΦ : ∀ w ∈ φ.toChart.source, Ψ (Φ w) = w := fun w hw ↦ by
    simp only [hΨdef, hΦdef, LinearEquiv.symm_apply_apply, φ.toChart.left_inv hw]
  have hΦc : ∀ w ∈ φ.toChart.source, ContinuousAt Φ w := fun w hw ↦
    (φ.splitCoordL.continuous.continuousAt.comp (φ.toChart.continuousAt hw)).congr
      (.of_forall fun _ ↦ φ.splitCoordL_apply _)
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦
    hε₂ z (by linarith)
  have hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hT₁ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : y₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hT₂ ▸ hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ha₂
  have hcoord : ∀ w, ‖φ.coord (φ.toChart w)‖ = max ‖(Φ w).fst‖ ‖(Φ w).snd‖ := fun w ↦
    (φ.max_norm_fst_norm_snd_splitCoord _).symm
  -- The norms of the split coordinates near the entrance and exit points.
  have hfst : ∀ w ∈ φ.toChart.source, ContinuousAt (fun w ↦ ‖(Φ w).fst‖) w := fun w hw ↦
    ((WithLp.continuous_fst 2 _ _).norm.continuousAt (x := Φ w)).comp (hΦc w hw)
  have hsnd : ∀ w ∈ φ.toChart.source, ContinuousAt (fun w ↦ ‖(Φ w).snd‖) w := fun w hw ↦
    ((WithLp.continuous_snd 2 _ _).norm.continuousAt (x := Φ w)).comp (hΦc w hw)
  have hy₁fst : Tendsto (fun w ↦ ‖(Φ w).fst‖) (𝓝 y₁) (𝓝 ε) := by
    have h := (hfst y₁ hy₁φ).tendsto
    rwa [hy₁ε] at h
  have hy₁snd : Tendsto (fun w ↦ ‖(Φ w).snd‖) (𝓝 y₁) (𝓝 0) := by
    have h := (hsnd y₁ hy₁φ).tendsto
    rwa [hy₁s, norm_zero] at h
  have hy₂snd : Tendsto (fun w ↦ ‖(Φ w).snd‖) (𝓝 y₂) (𝓝 ε) := by
    have h := (hsnd y₂ hy₂φ).tendsto
    rwa [hy₂ε] at h
  have hy₂fst : Tendsto (fun w ↦ ‖(Φ w).fst‖) (𝓝 y₂) (𝓝 0) := by
    have h := (hfst y₂ hy₂φ).tendsto
    rwa [hy₂u, norm_zero] at h
  have hA₁ : ∀ᶠ w in 𝓝 y₁, w ∈ φ.toChart.source ∧ 0 < ‖(Φ w).fst‖ ∧ ‖(Φ w).fst‖ < 2 * ε ∧
      ‖(Φ w).snd‖ < ε := by
    filter_upwards [φ.toChart.open_source.mem_nhds hy₁φ, hy₁fst.eventually (lt_mem_nhds hε),
      hy₁fst.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
      hy₁snd.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄ using ⟨h₁, h₂, h₃, h₄⟩
  have hA₂ : ∀ᶠ w in 𝓝 y₂, w ∈ φ.toChart.source ∧ 0 < ‖(Φ w).snd‖ ∧ ‖(Φ w).snd‖ < 2 * ε ∧
      ‖(Φ w).fst‖ < ε := by
    filter_upwards [φ.toChart.open_source.mem_nhds hy₂φ, hy₂snd.eventually (lt_mem_nhds hε),
      hy₂snd.eventually (gt_mem_nhds (by linarith : ε < 2 * ε)),
      hy₂fst.eventually (gt_mem_nhds hε)] with w h₁ h₂ h₃ h₄ using ⟨h₁, h₂, h₃, h₄⟩
  have hloc₁ : ∀ᶠ w in 𝓝 y₁, w ∈ hX.flow.stableSet q → (Φ w).snd = 0 := by
    filter_upwards [hA₁] with w hw'
    obtain ⟨hw, -, h₁, h₂⟩ := hw'
    exact (hloc w hw (by rw [hcoord]; exact max_lt (by linarith) (by linarith))).1.1
  have hloc₂ : ∀ᶠ w in 𝓝 y₂, w ∈ hX.flow.unstableSet q → (Φ w).fst = 0 := by
    filter_upwards [hA₂] with w hw'
    obtain ⟨hw, -, h₁, h₂⟩ := hw'
    exact (hloc w hw (by rw [hcoord]; exact max_lt (by linarith) (by linarith))).2.1
  set U := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < 2 * ε ∧ ‖(Φ w).snd‖ < ε}
  set V := {w | w ∈ φ.toChart.source ∧ ‖(Φ w).fst‖ < ε ∧ ‖(Φ w).snd‖ < 2 * ε}
  have hU : U ∈ 𝓝 y₁ := hA₁.mono fun w ⟨h₁, _, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩
  have hV : V ∈ 𝓝 y₂ := hA₂.mono fun w ⟨h₁, _, h₂, h₃⟩ ↦ ⟨h₁, h₃, h₂⟩
  obtain ⟨r₀, hr₀, g, k, ⟨e, he, he₀⟩, hcl, hpairs, hexh⟩ :=
    h.exists_homeomorph_closure_splitGluingPairs hf hp hq hr hpq hqr φ hy₁ hy₁φ hy₂ hy₂φ hloc₁
      hloc₂ hε hy₁ε hy₂ε hU hV
  -- The orbits through the points of the gluing pairs run from `p` to `r`.
  have hP : ∀ z ∈ splitGluingPairs ε r₀ g k,
      Ψ z.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        hX.flow (splitExitTime ε z.1) (Ψ z.1) = Ψ z.2 := by
    intro z hz
    obtain ⟨⟨w, ⟨hw, hwf, hws⟩, hwu, -, hwz⟩, w', ⟨hw', hw'f, hw's⟩, hw'r, -, hw'z⟩ :=
      hpairs z hz
    obtain ⟨hsrc, -, -, hpass, -⟩ := mem_splitGluingPairs.1 hz
    rw [hpass] at hw'z ⊢
    exact hX.mem_unstableSet_inter_stableSet_of_mem_splitPassage_source φ hφ hε₁ hsrc hwu hw'r
      (hwz ▸ hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw hwf hws)
      (hw'z ▸ hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw' hw'f hw's)
  have hbox₀ : ∀ w ∈ φ.toChart.source,
      φ.coord.symm (φ.splitCoord.symm (Φ w)) ∈ φ.toChart.target := fun w hw ↦ by
    simpa [hΦdef] using φ.toChart.map_source hw
  have hΨc : ∀ z, φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target → ContinuousAt Ψ z :=
    fun z hz ↦ (φ.toChart.continuousAt_symm hz).comp
      (f := fun z ↦ φ.coord.symm (φ.splitCoord.symm z))
      ((φ.splitCoordL.symm.continuous.continuousAt (x := z)).congr
        (.of_forall fun _ ↦ φ.splitCoordL_symm_apply _))
  -- Restrict to gluing parameters small enough for the passage to be unique.
  obtain ⟨r₁, hr₁, hr₁r₀, hr₁1, hsmall⟩ :=
    exists_pos_forall_mul_sq_lt hr₀ hε (Nat.cast_nonneg (Module.finrank ℝ E))
  have hr₁ε : r₁ * ε ≤ ε := mul_le_of_le_one_left hε.le hr₁1
  -- The points of the arc with nonzero parameter are unbroken pairs.
  have hz₀ : (Φ y₁, Φ y₂) ∈ closure (splitGluingPairs ε r₀ g k) := hcl ▸ mem_insert _ _
  have he₀' : e ⟨0, left_mem_Icc.2 hr₀.le⟩ = ⟨_, hz₀⟩ := Subtype.ext he₀
  have hepair : ∀ s : Icc (0 : ℝ) r₀, (s : ℝ) ≠ 0 →
      (e s).val ∈ splitGluingPairs ε r₀ g k ∧ ‖(e s).val.1.snd‖ = s * ε := by
    intro s hs
    have hsn : ‖(e s).val.1.snd‖ = s * ε := by
      have := he (e s)
      rw [e.symm_apply_apply] at this
      rw [this, div_mul_cancel₀ _ hε.ne']
    refine ⟨?_, hsn⟩
    have hmem : (e s).val ∈ insert (Φ y₁, Φ y₂) (splitGluingPairs ε r₀ g k) := hcl ▸ (e s).2
    refine hmem.resolve_left fun h0 ↦ hs ?_
    have : e s = e ⟨0, left_mem_Icc.2 hr₀.le⟩ := by rw [he₀']; exact Subtype.ext h0
    exact congrArg Subtype.val (e.injective this)
  have hboxC : ∀ z ∈ closure (splitGluingPairs ε r₀ g k),
      φ.coord.symm (φ.splitCoord.symm z.1) ∈ φ.toChart.target ∧
      φ.coord.symm (φ.splitCoord.symm z.2) ∈ φ.toChart.target := by
    intro z hz
    rw [hcl] at hz
    rcases hz with rfl | hz
    · exact ⟨hbox₀ y₁ hy₁φ, hbox₀ y₂ hy₂φ⟩
    · obtain ⟨hsrc, -, -, hpass, -⟩ := mem_splitGluingPairs.1 hz
      rw [hpass]
      exact MorseChart.coord_symm_splitCoord_symm_mem_target_of_mem_splitPassage_source hε₁ hsrc
  -- The arc: the points with the coordinates of the gluing pairs.
  set B : Icc (0 : ℝ) r₁ → M × M := fun s ↦
    (Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.1,
      Ψ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.2) with hBdef
  refine ⟨T₁, T₂, r₁, hr₁, B, ?_, ?_, fun s hs ↦ ?_, fun s s' hs hs' t hss' ↦ ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun s ↦ ?_
    obtain ⟨hb₁, hb₂⟩ := hboxC _ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).2
    have hc : Continuous fun s : Icc (0 : ℝ) r₁ ↦
        (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val :=
      continuous_subtype_val.comp (e.continuous.comp (continuous_inclusion _))
    exact ((hΨc _ hb₁).comp (f := fun s ↦ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.1)
      (continuous_fst.comp hc).continuousAt).prodMk
      ((hΨc _ hb₂).comp (f := fun s ↦ (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val.2)
        (continuous_snd.comp hc).continuousAt)
  · simp only [hBdef]
    rw [inclusion_mk, he₀', hΨΦ y₁ hy₁φ, hΨΦ y₂ hy₂φ, hT₁, hT₂]
  · obtain ⟨hpz, hflow⟩ := hP _ (hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs).1
    exact ⟨hpz, _, hflow⟩
  · -- Two unbroken pairs whose entrance points lie on one orbit are equal.
    set z := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s)).val
    set z' := (e (inclusion (Icc_subset_Icc_right hr₁r₀) s')).val
    obtain ⟨hz, hzn⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s) hs
    obtain ⟨hz', hzn'⟩ := hepair (inclusion (Icc_subset_Icc_right hr₁r₀) s') hs'
    have hle : ∀ u : Icc (0 : ℝ) r₁, (u : ℝ) * ε ≤ r₁ * ε := fun u ↦
      mul_le_mul_of_nonneg_right u.2.2 hε.le
    have h1 := hX.eq_of_flow_eq_of_mem_splitPassage_source φ hφ hε₁ (mem_splitGluingPairs.1 hz).1
      (mem_splitGluingPairs.1 hz').1
      (hsmall _ (norm_nonneg _) (hzn ▸ hle s)) (hsmall _ (norm_nonneg _) (hzn' ▸ hle s'))
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' (hP z hz).1) hss'
    have hzz : z = z' := Prod.ext h1 (by
      rw [(mem_splitGluingPairs.1 hz).2.2.2.1, (mem_splitGluingPairs.1 hz').2.2.2.1, h1])
    exact inclusion_injective _ (e.injective (Subtype.ext hzz))
  · -- A trajectory near the broken one crosses the box once; its entrance and exit points form a
    -- gluing pair of small parameter.
    have hκ₁ : ∀ᶠ w in 𝓝 y₁, ‖(Φ w).fst‖ * ‖(Φ w).snd‖ / ε < r₁ * ε := by
      have h := (hy₁fst.mul hy₁snd).div_const ε
      rw [mul_zero, zero_div] at h
      exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
    have hκ₂ : ∀ᶠ w in 𝓝 y₂, ‖(Φ w).fst‖ * ‖(Φ w).snd‖ / ε < r₁ * ε := by
      have h := (hy₂fst.mul hy₂snd).div_const ε
      rw [zero_mul, zero_div] at h
      exact h.eventually (gt_mem_nhds (mul_pos hr₁ hε))
    rw [hT₁, hT₂]
    filter_upwards [(hA₁.and hκ₁).prod_nhds (hA₂.and hκ₂), hexh] with w hw hpairw hw1 hw1f hw2f hwt
    obtain ⟨⟨⟨hw₁src, hw₁f0, hw₁f, hw₁s⟩, hκw₁⟩, ⟨⟨hw₂src, hw₂s0, hw₂s, hw₂f⟩, hκw₂⟩⟩ := hw
    obtain ⟨t, ht⟩ := hwt
    have hw2 : w.2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r :=
      ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hw1
    -- Off the broken trajectory, the coordinate that vanishes on it does not vanish.
    have hsnd₁ : (Φ w.1).snd ≠ 0 := fun h0 ↦ (Flow.disjoint_stableSet hqr').ne_of_mem
      ((hloc w.1 hw₁src (by rw [hcoord]; exact max_lt (by linarith) (by linarith))).1.2 h0)
      hw1.2 rfl
    have hfst₂ : (Φ w.2).fst ≠ 0 := fun h0 ↦ (Flow.disjoint_unstableSet hpq').ne_of_mem hw2.1
      ((hloc w.2 hw₂src (by rw [hcoord]; exact max_lt (by linarith) (by linarith))).2.2 h0) rfl
    obtain ⟨hE, hEQ'⟩ := hX.splitPassage_splitEntryTime_eq_splitExitTime φ hφ hε hε₂ hw₁src
      (norm_pos_iff.1 hw₁f0) hw₁f hsnd₁ hw₁s hw₂src (norm_pos_iff.1 hw₂s0) hw₂s hfst₂ hw₂f
      (by linarith) (hsmall _ (by positivity) hκw₁.le) (by linarith)
      (hsmall _ (by positivity) hκw₂.le)
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw1) ht
    have hEQ := hpairw hw1.1 hw1f hw2.2 hw2f (mem_splitPassage_source.1 hE).2.1 hEQ'
    -- The pair is a point of the arc of small parameter.
    set s₀ := e.symm ⟨_, subset_closure hEQ⟩ with hs₀def
    have hs₀r₁ : (s₀ : ℝ) < r₁ := by
      rw [hs₀def, he, div_lt_iff₀ hε, norm_snd_splitQuadraticFlow_splitEntryTime hε
        (norm_pos_iff.1 hw₁f0)]
      exact hκw₁
    have hes : e (inclusion (Icc_subset_Icc_right hr₁r₀) ⟨(s₀ : ℝ), s₀.2.1, hs₀r₁.le⟩) =
        ⟨_, subset_closure hEQ⟩ := by
      rw [← e.apply_symm_apply ⟨_, subset_closure hEQ⟩, ← hs₀def]
    refine ⟨⟨s₀, s₀.2.1, hs₀r₁.le⟩, hs₀r₁, ⟨splitEntryTime ε (Φ w.1), ?_⟩,
      ⟨splitExitTime ε (Φ w.2), ?_⟩⟩
    · simp only [hBdef, hes]
      exact hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁src hw₁f hw₁s
    · simp only [hBdef, hes]
      exact hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw₂src hw₂f hw₂s

/-- **Gluing at a broken trajectory.** Let `X` be a Morse–Smale adapted pseudo-gradient for a
Morse function `f` on a compact manifold, and `p`, `q`, `r` critical points of consecutive indices
`ind p = ind q + 1 = ind r + 2`. Record trajectories from `p` to `r` by their points on two levels:
take a point `a₁` of a trajectory from `p` to `q` and a point `a₂` of a trajectory from `q` to `r`,
and let `S` be the set of pairs `(w₁, w₂)` of points of one trajectory from `p` to `r` with
`f w₁ = f a₁` and `f w₂ = f a₂`. Then the broken trajectory `(a₁, a₂)` has a neighbourhood `N` in
`S ∪ {(a₁, a₂)}` homeomorphic to a half-open interval `[0, δ)`, with `(a₁, a₂)` corresponding to
`0`.

So `(a₁, a₂)` is the endpoint of a half-open arc of unbroken pairs, and in particular a limit of
unbroken pairs (`IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet`). -/
theorem IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    ∃ (N : Set (M × M)) (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
      (e ⟨0, left_mem_Ico.2 hδ⟩ : M × M) = (a₁, a₂) ∧
      N ⊆ insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} ∧
      N ∈ 𝓝[insert (a₁, a₂) {w | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
        f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2}] (a₁, a₂) := by
  -- Plan: follow the arc `B` of `exists_gluingArc` to the two levels. The resulting map `F` is
  -- continuous and injective on a closed interval, hence an embedding, and every unbroken pair
  -- near `(a₁, a₂)` is a value of `F` at a parameter below the end of the interval.
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hpr' : p ≠ r := by rintro rfl; omega
  obtain ⟨T₁, T₂, δ, hδ, B, hBc, hB₀, hBS, hBinj, hBfwd⟩ :=
    h.exists_gluingArc hf hp hq hr hpq hqr ha₁ ha₂
  set S := {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
    f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} with hSdef
  have hfa₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq' ha₁
  have hfa₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqr' ha₂
  have hy₁ : hX.flow T₁ a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p q T₁ ha₁
  have hy₂ : hX.flow T₂ a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r :=
    hX.flow.isInvariant_unstableSet_inter_stableSet q r T₂ ha₂
  -- Along the arc, the first points run from `p`, and the second points run to `r`.
  have hB : ∀ s, (∃ b, p ≠ b ∧ (B s).1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet b ∧
      f b < f a₁) ∧ ∃ a, a ≠ r ∧ (B s).2 ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet r ∧
      f a₂ < f a := by
    intro s
    by_cases hs : (s : ℝ) = 0
    · obtain rfl : s = ⟨0, left_mem_Icc.2 hδ.le⟩ := Subtype.ext hs
      rw [hB₀]
      exact ⟨⟨q, hpq', hy₁, hfa₁.1⟩, ⟨q, hqr', hy₂, hfa₂.2⟩⟩
    · obtain ⟨hs₁, t, ht⟩ := hBS s hs
      exact ⟨⟨r, hpr', hs₁, by linarith [hfa₁.1, hfa₂.1, hfa₂.2]⟩,
        ⟨p, hpr', ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hs₁,
          by linarith [hfa₁.1, hfa₁.2, hfa₂.2]⟩⟩
  -- The level points along the arc.
  set F : Icc (0 : ℝ) δ → M × M := fun s ↦
    (hX.flow (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1) (B s).1,
      hX.flow (Flow.levelCrossingTime hX.flow f (f a₂) (B s).2) (B s).2) with hFdef
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun s ↦ ?_
    obtain ⟨⟨b, hpb, hb, hfb⟩, ⟨a, har, ha, hfa⟩⟩ := hB s
    -- Every point of the arc crosses the two levels, since it runs from above `f a₁` to below
    -- `f a₂`.
    have hc₁ : ∀ s', f (hX.flow (Flow.levelCrossingTime hX.flow f (f a₁) (B s').1) (B s').1) =
        f a₁ := fun s' ↦ by
      obtain ⟨⟨b', hpb', hb', hfb'⟩, -⟩ := hB s'
      exact Flow.apply_flow_levelCrossingTime
        (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpb' hb' hfb' hfa₁.2).exists
    have hc₂ : ∀ s', f (hX.flow (Flow.levelCrossingTime hX.flow f (f a₂) (B s').2) (B s').2) =
        f a₂ := fun s' ↦ by
      obtain ⟨-, ⟨a', ha'r, ha', hfa'⟩⟩ := hB s'
      exact Flow.apply_flow_levelCrossingTime
        (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd ha'r ha' hfa₂.1 hfa').exists
    obtain ⟨σ₁, hσ₁, h₁⟩ := hX.exists_tendsto_flow_of_tendsto hfd hb hfb hfa₁.2
      ((continuous_fst.comp hBc).tendsto s) (.of_forall hc₁)
    obtain ⟨σ₂, hσ₂, h₂⟩ := hX.exists_tendsto_flow_of_tendsto hfd ha hfa₂.1 hfa
      ((continuous_snd.comp hBc).tendsto s) (.of_forall hc₂)
    rw [← Flow.flow_levelCrossingTime
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpb hb) hσ₁] at h₁
    rw [← Flow.flow_levelCrossingTime
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet har ha) hσ₂] at h₂
    exact h₁.prodMk_nhds h₂
  have hF₀ : F ⟨0, left_mem_Icc.2 hδ.le⟩ = (a₁, a₂) := by
    have e₁ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpq' ha₁)
      (by rw [Flow.map_zero_apply] : f (hX.flow 0 a₁) = f a₁) T₁
    have e₂ := Flow.flow_levelCrossingTime_flow
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hqr' ha₂)
      (by rw [Flow.map_zero_apply] : f (hX.flow 0 a₂) = f a₂) T₂
    rw [Flow.map_zero_apply] at e₁ e₂
    simp only [hFdef, hB₀, e₁, e₂]
  -- Away from `0`, the level points are an unbroken trajectory.
  have hFS : ∀ s : Icc (0 : ℝ) δ, (s : ℝ) ≠ 0 → F s ∈ S := by
    intro s hs
    obtain ⟨hs₁, t, ht⟩ := hBS s hs
    have hs₂ : (B s).2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r :=
      ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hs₁
    obtain ⟨σ₁, hσ₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr' hs₁
      (by linarith [hfa₁.1, hfa₂.1, hfa₂.2]) hfa₁.2
    obtain ⟨σ₂, hσ₂, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr' hs₂
      hfa₂.1 (by linarith [hfa₁.1, hfa₁.2, hfa₂.2])
    simp only [hFdef, hSdef, mem_ofPred_eq, Flow.flow_levelCrossingTime
      (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hs₁) hσ₁,
      Flow.flow_levelCrossingTime
        (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hs₂) hσ₂]
    refine ⟨hX.flow.isInvariant_unstableSet_inter_stableSet p r _ hs₁, hσ₁, hσ₂, σ₂ + t - σ₁, ?_⟩
    rw [← Flow.map_add, sub_add_cancel, Flow.map_add, ht]
  have hFinj : Injective F := by
    refine injective_of_forall_ne_zero hδ.le (fun s hs h ↦ (Flow.disjoint_stableSet
      hqr'.symm).ne_of_mem (hFS s hs).1.2 ((h.trans hF₀) ▸ ha₁.2) rfl) fun s s' hs hs' hss' ↦ ?_
    -- Equal first level points put the first points of `B s` and `B s'` on one orbit.
    refine hBinj s s' hs hs' (Flow.levelCrossingTime hX.flow f (f a₁) (B s).1 -
      Flow.levelCrossingTime hX.flow f (f a₁) (B s').1) ?_
    have h₁ := congrArg Prod.fst hss'
    simp only [hFdef] at h₁
    rw [sub_eq_add_neg, add_comm, Flow.map_add, h₁, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  -- Every unbroken trajectory near the broken one is a level point of the arc.
  have hfwd : ∀ᶠ w in 𝓝[S] (a₁, a₂),
      ∃ s : Ico (0 : ℝ) δ, F (inclusion Ico_subset_Icc_self s) = w := by
    have hSmem : ∀ᶠ w in 𝓝[S] (a₁, a₂), w ∈ S := self_mem_nhdsWithin
    have hw₂m : ∀ w ∈ S, w.2 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r := fun w hw ↦ by
      obtain ⟨t, ht⟩ := hw.2.2.2
      exact ht ▸ hX.flow.isInvariant_unstableSet_inter_stableSet p r t hw.1
    have hfy₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hpq' hy₁
    have hfy₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hfd hqr' hy₂
    -- The trajectories of `S` cross the levels of the arc's start.
    have hc₁ : ∀ w ∈ S, f (hX.flow (Flow.levelCrossingTime hX.flow f (f (hX.flow T₁ a₁)) w.1)
        w.1) = f (hX.flow T₁ a₁) := fun w hw ↦ Flow.apply_flow_levelCrossingTime
      (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr' hw.1
        (by linarith [hfy₁.1, hfa₂.1, hfa₂.2]) hfy₁.2).exists
    have hc₂ : ∀ w ∈ S, f (hX.flow (Flow.levelCrossingTime hX.flow f (f (hX.flow T₂ a₂)) w.2)
        w.2) = f (hX.flow T₂ a₂) := fun w hw ↦ Flow.apply_flow_levelCrossingTime
      (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hfd hpr' (hw₂m w hw) hfy₂.1
        (by linarith [hfy₂.2, hfa₁.1, hfa₁.2])).exists
    -- The points where they cross these levels tend to the arc's start.
    obtain ⟨σ₁, hσ₁, hm₁⟩ := hX.exists_tendsto_flow_of_tendsto hfd ha₁ hfy₁.1 hfy₁.2
      ((continuous_fst.tendsto _).mono_left nhdsWithin_le_nhds) (hSmem.mono hc₁)
    obtain ⟨σ₂, hσ₂, hm₂⟩ := hX.exists_tendsto_flow_of_tendsto hfd ha₂ hfy₂.1 hfy₂.2
      ((continuous_snd.tendsto _).mono_left nhdsWithin_le_nhds) (hSmem.mono hc₂)
    rw [(hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpq' ha₁).injective hσ₁] at hm₁
    rw [(hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hqr' ha₂).injective hσ₂] at hm₂
    filter_upwards [hSmem, (hm₁.prodMk_nhds hm₂).eventually hBfwd] with w hw hfw
    have hw2 := hw₂m w hw
    obtain ⟨s, hs, ⟨t₁, ht₁⟩, ⟨t₂, ht₂⟩⟩ := hfw
      (hX.flow.isInvariant_unstableSet_inter_stableSet p r _ hw.1) (hc₁ w hw) (hc₂ w hw)
      ⟨Flow.levelCrossingTime hX.flow f (f (hX.flow T₂ a₂)) w.2 + hw.2.2.2.choose -
          Flow.levelCrossingTime hX.flow f (f (hX.flow T₁ a₁)) w.1,
        by rw [← Flow.map_add, sub_add_cancel, Flow.map_add, hw.2.2.2.choose_spec]⟩
    obtain ⟨hw1, hw1f, hw2f, -⟩ := hw
    have hanti₁ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw1
    have hanti₂ := hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hpr' hw2
    set τ₁ := Flow.levelCrossingTime hX.flow f (f (hX.flow T₁ a₁)) w.1
    set τ₂ := Flow.levelCrossingTime hX.flow f (f (hX.flow T₂ a₂)) w.2
    refine ⟨⟨s, s.2.1, hs⟩, ?_⟩
    have e₁ := Flow.flow_levelCrossingTime_flow hanti₁
      (by rw [Flow.map_zero_apply]; exact hw1f : f (hX.flow 0 w.1) = f a₁) (t₁ + τ₁)
    have e₂ := Flow.flow_levelCrossingTime_flow hanti₂
      (by rw [Flow.map_zero_apply]; exact hw2f : f (hX.flow 0 w.2) = f a₂) (t₂ + τ₂)
    rw [Flow.map_zero_apply, Flow.map_add] at e₁ e₂
    rw [ht₁] at e₁
    rw [ht₂] at e₂
    exact Prod.ext e₁ e₂
  have hemb : IsEmbedding (F ∘ inclusion (Ico_subset_Icc_self : Ico (0 : ℝ) δ ⊆ Icc 0 δ)) :=
    (hFc.isClosedEmbedding hFinj).isEmbedding.comp (IsEmbedding.inclusion Ico_subset_Icc_self)
  refine ⟨range (F ∘ inclusion Ico_subset_Icc_self), δ, hδ, hemb.toHomeomorph, hF₀, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    by_cases hs : (s : ℝ) = 0
    · left
      rw [← hF₀]
      exact congrArg F (Subtype.ext hs)
    · exact Or.inr (hFS _ hs)
  · rw [mem_nhdsWithin_insert]
    refine ⟨⟨⟨0, left_mem_Ico.2 hδ⟩, hF₀⟩, ?_⟩
    filter_upwards [hfwd] with w ⟨s, hs⟩ using ⟨s, hs⟩

/-- **Every broken trajectory is a limit of unbroken ones.** With the notation of
`IsMorseSmale.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet`, the pair `(a₁, a₂)`
recording a trajectory broken at `q` lies in the closure of the pairs recording the unbroken
trajectories from `p` to `r` on the same two levels. -/
theorem IsMorseSmale.mem_closure_of_mem_unstableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q r a₁ a₂ : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (ha₁ : a₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (ha₂ : a₂ ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) :
    (a₁, a₂) ∈ closure {w : M × M | w.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧
      f w.1 = f a₁ ∧ f w.2 = f a₂ ∧ ∃ t, hX.flow t w.1 = w.2} := by
  obtain ⟨N, δ, hδ, e, he₀, hN, -⟩ :=
    h.exists_homeomorph_Ico_of_mem_unstableSet_inter_stableSet hf hp hq hr hpq hqr ha₁ ha₂
  -- The points of the half-open interval `δ / (n + 2)` tend to `0`, and their images are unbroken.
  set u : ℕ → Ico (0 : ℝ) δ := fun n ↦ ⟨δ / (n + 2), by positivity,
    (div_lt_self hδ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))⟩ with hudef
  have hu : Tendsto u atTop (𝓝 ⟨0, left_mem_Ico.2 hδ⟩) := by
    refine tendsto_subtype_rng.2 ?_
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  refine mem_closure_of_tendsto (he₀ ▸ (continuous_subtype_val.tendsto _).comp
    ((e.continuous.tendsto _).comp hu)) (.of_forall fun n ↦ ?_)
  refine (hN (e (u n)).2).resolve_left fun h0 ↦ ?_
  have : e (u n) = e ⟨0, left_mem_Ico.2 hδ⟩ := Subtype.ext (h0.trans he₀.symm)
  have hpos : (0 : ℝ) < δ / (n + 2) := by positivity
  exact hpos.ne' (congrArg Subtype.val (e.injective this))

end IsAdaptedPseudoGradient

end TauCeti

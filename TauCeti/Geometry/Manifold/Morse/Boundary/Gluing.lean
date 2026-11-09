/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Compactification
public import TauCeti.Geometry.Manifold.Morse.Stable.Gluing
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Existence
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Passage
import TauCeti.Geometry.Manifold.Morse.PseudoGradient.UniformConvergence

/-!
# Broken index-two trajectories are limits of unbroken ones

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. Record trajectories from `p` to `r` by their points on two levels `c₁` and
`c₂`, as in `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`. The compactified space of
these trajectories is the closure of the unbroken pairs in `M × M`, and
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryPairs_subset` shows that it
adds only broken pairs. This file proves the converse: every trajectory broken once, at a
critical point `q` of intermediate index, is a limit of unbroken trajectories. So the points the
compactification adds are exactly the broken trajectories.

The proof transports the gluing theorem in a Morse box at `q`,
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`, to the
two levels. Choose a Morse chart at `q` in which `X` is linear, and a box radius `ε` small enough.
The first component of the broken trajectory enters the box at a point `a` of the entrance face,
and the second leaves it at a point `b` of the exit face
(`TauCeti.IsAdaptedPseudoGradient.exists_forall_exists_norm_coord_flow_eq`). The gluing theorem
gives a glued trajectory through the box which starts on the level cut of `W^u(p)` through `a` and
ends on the level cut of `W^s(r)` through `b`, as close to `a` and `b` as we like. Near the faces
the flow is the split hyperbolic flow, so this is an actual trajectory from `p` to `r`. Since
level crossings depend continuously on the orbit
(`TauCeti.IsAdaptedPseudoGradient.eventually_forall_flow_mem_of_mem_unstableSet_inter_stableSet`),
its points on the levels `c₁` and `c₂` are close to the two points of the broken trajectory.

It remains to show that every broken trajectory has a neighbourhood in the compactified space
homeomorphic to a half-open interval; this local uniqueness of the gluing is not proved here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`:

* `morseBrokenTrajectoryPairs_subset_closure`: every broken pair is a limit of unbroken pairs.
* `closure_morseTrajectoryPairs`: the compactified space is the union of the unbroken and the
  broken pairs.
* `closure_diff_morseTrajectoryPairs`: the points the compactification adds are exactly the
  broken pairs.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- A real number between `1 / 2` and `2` has a logarithm of absolute value at most `log 2`, so
the split hyperbolic flow during a time of that size scales each coordinate by at most `2`. -/
private theorem exp_abs_log_le_two {x : ℝ} (h₁ : 1 / 2 < x) (h₂ : x < 2) :
    Real.exp |Real.log x| ≤ 2 := by
  have hx : 0 < x := by linarith
  calc Real.exp |Real.log x| ≤ Real.exp (Real.log 2) := by
        refine Real.exp_le_exp.2 (abs_le.2 ⟨?_, Real.log_le_log hx h₂.le⟩)
        rw [← Real.log_inv]
        exact Real.log_le_log (by norm_num) (by linarith)
    _ = 2 := Real.exp_log two_pos

omit [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The norms of the two factors of the split coordinates of a Morse chart are continuous on its
source. -/
private theorem continuousAt_norm_splitCoord {q : M} (φ : MorseChart E f q) {z : M}
    (hz : z ∈ φ.toChart.source) :
    ContinuousAt (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖) z ∧
      ContinuousAt (fun w ↦ ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖) z := by
  have hc : ContinuousAt (fun w ↦ φ.splitCoordL (φ.toChart w)) z :=
    φ.splitCoordL.continuous.continuousAt.comp (φ.toChart.continuousAt hz)
  simp only [MorseChart.splitCoordL_apply] at hc
  exact ⟨((WithLp.fstL 2 ℝ _ _).continuous.continuousAt.comp hc).norm,
    ((WithLp.sndL 2 ℝ _ _).continuous.continuousAt.comp hc).norm⟩

/-- **Entrance and exit points of a broken trajectory in a Morse box.** Let `y₁ ≠ q` lie on the
stable set and `y₂ ≠ q` on the unstable set of a critical point `q`. There is a Morse chart at `q`
in which `X` is linear, and a radius `ε` with the cube of radius `4 ε` in the chart, such that the
orbit of `y₁` passes through a point `a` of the entrance face `‖u‖ = ε, v = 0` near which the
stable set of `q` is `v = 0`, and the orbit of `y₂` through a point `b` of the exit face
`u = 0, ‖v‖ = ε` near which the unstable set of `q` is `u = 0`. -/
private theorem exists_morseChart_entrance_exit (hf : IsMorse 𝓘(ℝ, E) f) {q y₁ y₂ : M}
    (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0) (hy₁ : y₁ ∈ hX.flow.stableSet q) (hy₁q : y₁ ≠ q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet q) (hy₂q : y₂ ≠ q) :
    ∃ φ : MorseChart E f q, (∀ y ∈ φ.toChart.source,
      φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
        fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i)) ∧
      ∃ ε > 0, (∀ z, ‖z‖ ≤ 4 * ε → φ.coord.symm z ∈ φ.toChart.target) ∧ ∃ t₁ t₂ : ℝ,
        (hX.flow t₁ y₁ ∈ φ.toChart.source ∧
          (φ.splitCoord (φ.coord (φ.toChart (hX.flow t₁ y₁)))).snd = 0 ∧
          ‖(φ.splitCoord (φ.coord (φ.toChart (hX.flow t₁ y₁)))).fst‖ = ε ∧
          ∀ᶠ w in 𝓝 (hX.flow t₁ y₁), w ∈ hX.flow.stableSet q →
            (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0) ∧
        (hX.flow t₂ y₂ ∈ φ.toChart.source ∧
          (φ.splitCoord (φ.coord (φ.toChart (hX.flow t₂ y₂)))).fst = 0 ∧
          ‖(φ.splitCoord (φ.coord (φ.toChart (hX.flow t₂ y₂)))).snd‖ = ε ∧
          ∀ᶠ w in 𝓝 (hX.flow t₂ y₂), w ∈ hX.flow.unstableSet q →
            (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  obtain ⟨φ, hφ⟩ := hX.exists_morseChart q hq
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero hq
  -- The radii of the chart target and of the cubes on which `W^s(q)` and `W^u(q)` are flat.
  obtain ⟨R, hR, hRT⟩ := φ.exists_pos_forall_norm_lt_mem_target
  obtain ⟨εs, hεs, hεss⟩ := hX.exists_forall_mem_stableSet_iff φ hφ hdf
  obtain ⟨εu, hεu, hεuu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd)
    (φ.coord_mfderiv_neg hφ hnd) (hf.neg.contMDiff.mdifferentiable (by simp))
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hεuu
  obtain ⟨m₁, hm₁, hent⟩ := hX.exists_forall_exists_norm_coord_flow_eq φ hφ hdf hy₁ hy₁q
  obtain ⟨m₂, hm₂, hext⟩ :=
    hX.exists_forall_exists_norm_coord_flow_eq_of_unstableSet hf φ hφ hy₂ hy₂q
  set ε := min (min m₁ m₂) (min (R / 8) (min (εs / 2) (εu / 2)))
  have hε : 0 < ε := by positivity
  have hεR : ε ≤ R / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hεεs : ε ≤ εs / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεεu : ε ≤ εu / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨t₁, ha, ha0, haε⟩ := hent ε hε ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨t₂, hb, hb0, hbε⟩ := hext ε hε ((min_le_left _ _).trans (min_le_right _ _))
  rw [← φ.splitCoord_snd_eq_zero_iff] at ha0
  rw [← φ.splitCoord_fst_eq_zero_iff] at hb0
  have hcn : ∀ z ∈ φ.toChart.source, ContinuousAt (fun w ↦ ‖φ.coord (φ.toChart w)‖) z :=
    fun z hz ↦ (φ.continuous_coord.continuousAt.comp (φ.toChart.continuousAt hz)).norm
  refine ⟨φ, hφ, ε, hε, fun z hz ↦ hRT z (by linarith), t₁, t₂,
    ⟨ha, ha0, (φ.norm_fst_splitCoord_of_snd_eq_zero ha0).trans haε, ?_⟩,
    ⟨hb, hb0, (φ.norm_snd_splitCoord_of_fst_eq_zero hb0).trans hbε, ?_⟩⟩
  · filter_upwards [φ.toChart.open_source.mem_nhds ha, (hcn _ ha).eventually_lt
      continuousAt_const (show ‖φ.coord (φ.toChart _)‖ < εs by rw [haε]; linarith)]
      with w hw hwε hws
    exact φ.splitCoord_snd_eq_zero_iff _ |>.2 ((hεss w hw hwε).1 hws)
  · filter_upwards [φ.toChart.open_source.mem_nhds hb, (hcn _ hb).eventually_lt
      continuousAt_const (show ‖φ.coord (φ.toChart _)‖ < εu by rw [hbε]; linarith)]
      with w hw hwε hwu
    exact φ.splitCoord_fst_eq_zero_iff _ |>.2 ((hεuu w hw hwε).1 hwu)

include h hf in
/-- **A glued trajectory through a Morse box.** Let `p`, `q`, `r` be critical points with
`ind p = ind q + 1 = ind r + 2`, `φ` a Morse chart at `q` in which `X` is linear, with the cube of
radius `4 ε` in the chart. Let `a ∈ W^u(p) ∩ W^s(q)` lie on the entrance face `‖u‖ = ε, v = 0` and
`b ∈ W^u(q) ∩ W^s(r)` on the exit face `u = 0, ‖v‖ = ε`, with `W^s(q)` flat near `a` and `W^u(q)`
flat near `b`. Then every neighbourhood of `a` contains a point on a trajectory from `p` to `r`
whose orbit also meets any given neighbourhood of `b`. -/
private theorem exists_mem_unstableSet_inter_stableSet_flow_mem {p q r a b : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (hqr : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (φ : MorseChart E f q)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hbox : ∀ z, ‖z‖ ≤ 4 * ε → φ.coord.symm z ∈ φ.toChart.target)
    (haW : a ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (ha : a ∈ φ.toChart.source)
    (haΦ : (φ.splitCoord (φ.coord (φ.toChart a))).snd = 0)
    (haε : ‖(φ.splitCoord (φ.coord (φ.toChart a))).fst‖ = ε)
    (hloc₁ : ∀ᶠ w in 𝓝 a, w ∈ hX.flow.stableSet q →
      (φ.splitCoord (φ.coord (φ.toChart w))).snd = 0)
    (hbW : b ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r) (hb : b ∈ φ.toChart.source)
    (hbΦ : (φ.splitCoord (φ.coord (φ.toChart b))).fst = 0)
    (hbε : ‖(φ.splitCoord (φ.coord (φ.toChart b))).snd‖ = ε)
    (hloc₂ : ∀ᶠ w in 𝓝 b, w ∈ hX.flow.unstableSet q →
      (φ.splitCoord (φ.coord (φ.toChart w))).fst = 0)
    {U V : Set M} (hU : U ∈ 𝓝 a) (hV : V ∈ 𝓝 b) :
    ∃ z₁ ∈ U, z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ ∃ τ, hX.flow τ z₁ ∈ V := by
  -- Near `a` and `b` the flow is the split hyperbolic flow for times of size at most `log 2`.
  have hbox₂ : ∀ {A B : ℝ}, A ≤ 2 → 0 ≤ B → B ≤ 2 * ε → A * B ≤ 4 * ε := fun hA hB hB' ↦ by
    nlinarith
  obtain ⟨hfa, hsa⟩ := continuousAt_norm_splitCoord φ ha
  obtain ⟨hfb, hsb⟩ := continuousAt_norm_splitCoord φ hb
  have hUbox := (φ.toChart.open_source.eventually_mem ha).and <|
    (continuousAt_const.eventually_lt hfa (by rw [haε]; linarith : ε / 2 < _)).and <|
      (hfa.eventually_lt continuousAt_const (by rw [haε]; linarith : _ < 2 * ε)).and
        (hsa.eventually_lt continuousAt_const (by rw [haΦ, norm_zero]; exact hε : _ < ε))
  have hVbox := (φ.toChart.open_source.eventually_mem hb).and <|
    (continuousAt_const.eventually_lt hsb (by rw [hbε]; linarith : ε / 2 < _)).and <|
      (hsb.eventually_lt continuousAt_const (by rw [hbε]; linarith : _ < 2 * ε)).and
        (hfb.eventually_lt continuousAt_const (by rw [hbΦ, norm_zero]; exact hε : _ < ε))
  -- The gluing theorem in the box provides a glued trajectory with ends in these neighbourhoods.
  obtain ⟨r₀, hr₀, g, k, ⟨e, -, -⟩, hpairs, -⟩ :=
    h.exists_homeomorph_closure_splitGluingPairs hf hp hq hr hpq hqr φ haW ha hbW hb hloc₁ hloc₂
      hε haε hbε (hUbox.and hU) (hVbox.and hV)
  obtain ⟨Q, hQ⟩ := closure_nonempty_iff.1 ⟨_, (e ⟨0, left_mem_Icc.2 hr₀.le⟩).2⟩
  obtain ⟨⟨z₁, ⟨⟨hz₁, hz₁l, hz₁r, hz₁v⟩, hz₁U⟩, hz₁u, -, hz₁Q⟩,
    z₂, ⟨⟨hz₂, hz₂l, hz₂r, hz₂u⟩, hz₂V⟩, hz₂s, -, hz₂Q⟩ := hpairs Q hQ
  obtain ⟨hQs, -, -, hQ₂, -⟩ := mem_splitGluingPairs.1 hQ
  -- On the manifold, `z₁` flows to the entrance point of `Q`, which flows to its exit point, to
  -- which `z₂` also flows.
  have hl₁ := exp_abs_log_le_two (x := ‖(φ.splitCoord (φ.coord (φ.toChart z₁))).fst‖ / ε)
    (by rw [lt_div_iff₀ hε]; linarith) (by rw [div_lt_iff₀ hε]; linarith)
  have hl₂ := exp_abs_log_le_two (x := ε / ‖(φ.splitCoord (φ.coord (φ.toChart z₂))).snd‖)
    (by rw [lt_div_iff₀ (by linarith)]; linarith) (by rw [div_lt_iff₀ (by linarith)]; linarith)
  rw [← splitEntryTime_def] at hl₁
  rw [← splitExitTime_def] at hl₂
  have h₁ := hX.flow_toChart_symm_splitCoord_symm_of_exp_abs_mul_le φ hφ hbox
    (w := φ.splitCoord (φ.coord (φ.toChart z₁))) (t := splitEntryTime ε _)
    (hbox₂ hl₁ (norm_nonneg _) hz₁r.le) (hbox₂ hl₁ (norm_nonneg _) (by linarith))
  rw [hz₁Q, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    φ.toChart.left_inv hz₁] at h₁
  have h₂ := hX.flow_splitExitTime φ hφ (fun z hz ↦ hbox z (by linarith)) hQs
  rw [← hQ₂] at h₂
  have h₃ := hX.flow_toChart_symm_splitCoord_symm_of_exp_abs_mul_le φ hφ hbox
    (w := φ.splitCoord (φ.coord (φ.toChart z₂))) (t := splitExitTime ε _)
    (hbox₂ hl₂ (norm_nonneg _) (by linarith)) (hbox₂ hl₂ (norm_nonneg _) hz₂r.le)
  rw [hz₂Q, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    φ.toChart.left_inv hz₂] at h₃
  -- So `z₂` lies on the orbit of `z₁`, which therefore runs from `p` to `r`.
  set τ := -splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart z₂))) +
    (splitExitTime ε Q.1 + splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart z₁))))
  have hz₁₂ : hX.flow τ z₁ = z₂ := by
    rw [Flow.map_add, Flow.map_add, h₁, h₂, ← h₃, ← Flow.map_add, neg_add_cancel,
      Flow.map_zero_apply]
  exact ⟨z₁, hz₁U, ⟨hz₁u, (Flow.apply_mem_stableSet_iff _ τ).1 (by rwa [hz₁₂])⟩, τ,
    hz₁₂ ▸ hz₂V⟩

include h hf in
/-- **Broken trajectories are limits of unbroken ones.** Let `p` and `r` be critical points whose
Morse indices differ by two. Every pair of points on the levels `c₁` and `c₂` of a trajectory from
`p` to `r` broken once, at a critical point of intermediate index, is a limit of pairs of points
on these levels of unbroken trajectories from `p` to `r`. -/
theorem morseBrokenTrajectoryPairs_subset_closure (p r : M) (c₁ c₂ : ℝ) :
    hX.morseBrokenTrajectoryPairs p r c₁ c₂ ⊆ closure (hX.morseTrajectoryPairs p r c₁ c₂) := by
  rintro ⟨y₁, y₂⟩ hw
  simp only [mem_morseBrokenTrajectoryPairs] at hw
  obtain ⟨q, hq, hpq, hqr, hy₁, rfl, hy₂, rfl⟩ := hw
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hpr' : p ≠ r := by rintro rfl; omega
  have hI₁ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hy₁
  have hI₂ := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hy₂
  -- The broken trajectory enters a Morse box at `q` at `a` and leaves it at `b`.
  obtain ⟨φ, hφ, ε, hε, hbox, t₁, t₂, ⟨ha, haΦ, haε, hloc₁⟩, ⟨hb, hbΦ, hbε, hloc₂⟩⟩ :=
    exists_morseChart_entrance_exit hf hq hy₁.2 (by rintro rfl; exact hI₁.1.false) hy₂.1
      (by rintro rfl; exact hI₂.2.false)
  have hflow_neg (t : ℝ) (y : M) : hX.flow (-t) (hX.flow t y) = y := by
    rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  -- It suffices to find unbroken pairs in every product neighbourhood `W₁ ×ˢ W₂` of `(y₁, y₂)`.
  refine mem_closure_iff_nhds.2 fun W hW ↦ ?_
  obtain ⟨W₁, hW₁, W₂, hW₂, hW₁₂⟩ := mem_nhds_prod_iff.1 hW
  -- Orbits near `a` cross the level `f y₁` in `W₁`, and orbits near `b` cross `f y₂` in `W₂`.
  have hU := hX.eventually_forall_flow_mem_of_mem_unstableSet_inter_stableSet hdf hpq'
    (hX.flow.isInvariant_unstableSet_inter_stableSet p q t₁ hy₁) (σ := -t₁) (c := f y₁)
    (by rw [hflow_neg]) (W := W₁) (by rwa [hflow_neg])
  have hV := hX.eventually_forall_flow_mem_of_mem_unstableSet_inter_stableSet hdf hqr'
    (hX.flow.isInvariant_unstableSet_inter_stableSet q r t₂ hy₂) (σ := -t₂) (c := f y₂)
    (by rw [hflow_neg]) (W := W₂) (by rwa [hflow_neg])
  obtain ⟨z, hzU, hzW, τ, hzV⟩ := exists_mem_unstableSet_inter_stableSet_flow_mem h hf
    (hX.mfderiv_eq_zero_of_forall_eq (hdf p) fun t ↦ by rw [Flow.fixed_of_mem_unstableSet hy₁.1 t])
    hq (hX.mfderiv_eq_zero_of_forall_eq (hdf r) fun t ↦ by rw [Flow.fixed_of_mem_stableSet hy₂.2 t])
    hpq hqr φ hφ hε hbox (hX.flow.isInvariant_unstableSet_inter_stableSet p q t₁ hy₁) ha haΦ haε
    hloc₁ (hX.flow.isInvariant_unstableSet_inter_stableSet q r t₂ hy₂) hb hbΦ hbε hloc₂ hU hV
  -- The points of the glued trajectory on the two levels are the required unbroken pair.
  obtain ⟨s₁, hs₁, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hpr' hzW
    ((hI₂.1.trans hI₂.2).trans hI₁.1) hI₁.2
  obtain ⟨s₂, hs₂, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hpr' hzW
    hI₂.1 ((hI₂.2.trans hI₁.1).trans hI₁.2)
  have hs₂' : hX.flow s₂ z = hX.flow (s₂ - τ) (hX.flow τ z) := by
    rw [← Flow.map_add, sub_add_cancel]
  refine ⟨(hX.flow s₁ z, hX.flow s₂ z), hW₁₂ ⟨hzU s₁ hs₁, hs₂' ▸ hzV _ (hs₂' ▸ hs₂)⟩,
    hX.mem_morseTrajectoryPairs.2
      ⟨hX.flow.isInvariant_unstableSet_inter_stableSet p r s₁ hzW, hs₁, hs₂, s₂ - s₁, ?_⟩⟩
  rw [← Flow.map_add, sub_add_cancel]

include h hf in
/-- **The compactified space of index-two trajectories.** Let `p` and `r` be critical points with
`ind p = ind r + 2`, and let the levels `f r < c₂ < c₁ < f p` separate every critical value
strictly between `f r` and `f p` from `f r` and `f p`. The closure of the pairs of points on these
levels of trajectories from `p` to `r` consists of these pairs together with the pairs of points
of trajectories broken once, at a critical point of intermediate index. -/
theorem closure_morseTrajectoryPairs {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    closure (hX.morseTrajectoryPairs p r c₁ c₂) =
      hX.morseTrajectoryPairs p r c₁ c₂ ∪ hX.morseBrokenTrajectoryPairs p r c₁ c₂ :=
  (h.closure_morseTrajectoryPairs_subset hf hp hr hind hr₂ h₂₁ h₁p hgap).antisymm
    (union_subset subset_closure (h.morseBrokenTrajectoryPairs_subset_closure hf p r c₁ c₂))

include h hf in
/-- **The compactification adds exactly the broken trajectories.** Under the hypotheses of
`closure_morseTrajectoryPairs`, the points of the closure of the unbroken trajectory pairs that are
not unbroken pairs are the broken trajectory pairs. -/
theorem closure_diff_morseTrajectoryPairs {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {c₁ c₂ : ℝ}
    (hr₂ : f r < c₂) (h₂₁ : c₂ < c₁) (h₁p : c₁ < f p)
    (hgap : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x ∈ Ioo (f r) (f p) → f x ∈ Ioo c₂ c₁) :
    closure (hX.morseTrajectoryPairs p r c₁ c₂) \ hX.morseTrajectoryPairs p r c₁ c₂ =
      hX.morseBrokenTrajectoryPairs p r c₁ c₂ := by
  rw [h.closure_morseTrajectoryPairs hf hp hr hind hr₂ h₂₁ h₁p hgap, union_sdiff_left,
    (hX.disjoint_morseTrajectoryPairs_morseBrokenTrajectoryPairs p r c₁ c₂).symm.sdiff_eq_left]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

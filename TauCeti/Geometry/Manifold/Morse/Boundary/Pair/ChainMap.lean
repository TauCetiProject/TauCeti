/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Gluing.Pair
public import TauCeti.Geometry.Manifold.Morse.Boundary.Pair.Commutation
import TauCeti.Geometry.Manifold.Boundary.LocalModels
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.Lyapunov

/-!
# The mod-two pair map is a chain map

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with Morse–Smale
pseudo-gradients `X₀` and `X₁` adapted to them, forming a Morse–Smale pair
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`). The pair map counts the points of the rigid
intersections `W^u_{X₀}(p) ∩ W^s_{X₁}(q)`; for the pair transported by the transition
diffeomorphism of a transverse continuation these are the continuation trajectories
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage_mpullback`). By
`IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_eq_iff`, the pair map commutes with the
Morse boundaries modulo two exactly when, between a critical point `p` of `f₀` and a critical
point `r` of `f₁`, the configurations broken at the source
(`TauCeti.IsAdaptedPseudoGradient.morseSourceBrokenPairSet`) and at the target
(`TauCeti.IsAdaptedPseudoGradient.morseTargetBrokenPairSet`) are evenly many in total. This file
proves that they are
(`IsMorseSmalePair.even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet`), so the
pair map with coefficients in `ZMod 2` is a chain map
(`IsMorseSmalePair.signedMorseBoundary_comp_signedPairMap_zmod_two`).

When `ind p = ind r + 1`, the broken configurations are the endpoints of the compactified
one-dimensional intersection `S = W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and the count is that of the
boundary of a compact one-manifold (`TauCeti.even_ncard_of_forall_exists_homeomorph_Ico`). The
compactification is built inside `M × M × M`. Choose a level `c₀` below `f₀ p` and above every
critical value of `f₀` below `f₀ p`, and a level `c₁` above `f₁ r` and below every critical value
of `f₁` above `f₁ r`. A point `x` of `S` is recorded by the triple of

* the point of its `X₀`-orbit on the level `max (f₀ x) c₀`,
* the point `x` itself, and
* the point of its `X₁`-orbit on the level `min (f₁ x) c₁`.

Truncating the levels at `f₀ x` and `f₁ x` makes both outer points depend continuously on `x`,
also at the critical points `p` and `r`, which may lie on `S`. The records of the points of `S`
form a copy of `S`, hence a one-manifold. Their limits break at most once: at the source, along a
trajectory of `X₀` from `p` to a critical point `a`, whose point on the level `c₀` is the limit of
the first components; or at the target, along a trajectory of `X₁` from a critical point `b` to
`r`, whose point on the level `c₁` is the limit of the third components. The records of the broken
configurations are in bijection with the configurations themselves, so they are finitely many.
Near each of them, the half-open gluing charts of
`TauCeti.Geometry.Manifold.Morse.Gluing.Pair`, which record a point by a single orbit, transfer
to the triple records (`TauCeti.exists_homeomorph_Ico_closure_of_homeomorph_Ico`), since the
remaining component is a continuous function of the middle one.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient.IsMorseSmalePair`:

* `even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet`: between any two
  critical points, the configurations broken at the source and at the target are evenly many in
  total.
* `signedMorseBoundary_comp_signedPairMap_zmod_two`: the pair map with coefficients in `ZMod 2`
  commutes with the Morse boundaries.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map is a chain map, by counting the
  ends of the one-dimensional moduli spaces of continuation trajectories).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness and gluing of trajectories) and Chapter 6 (invariance of Morse homology
  by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-! ### Levels separating a critical value -/

section Levels

omit [FiniteDimensional ℝ E] [T2Space M]

/-- Some level `c < f p` lies above every critical value below `f p`. -/
private theorem IsMorse.exists_lt_forall_lt (hf : IsMorse 𝓘(ℝ, E) f) (p : M) :
    ∃ c < f p, ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f x < f p → f x < c := by
  have h : ∀ᶠ c in 𝓝[<] (f p), ∀ x ∈ {x ∈ criticalPoints 𝓘(ℝ, E) f | f x < f p}, f x < c :=
    (hf.finite_criticalPoints.subset (sep_subset _ _)).eventually_all.2 fun _ hx ↦
      nhdsWithin_le_nhds (lt_mem_nhds hx.2)
  obtain ⟨c, hc, hcp⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨c, hcp, fun x hx hxp ↦ hc x ⟨hx, hxp⟩⟩

/-- Some level `c > f r` lies below every critical value above `f r`. -/
private theorem IsMorse.exists_gt_forall_gt (hf : IsMorse 𝓘(ℝ, E) f) (r : M) :
    ∃ c > f r, ∀ x ∈ criticalPoints 𝓘(ℝ, E) f, f r < f x → c < f x := by
  have h : ∀ᶠ c in 𝓝[>] (f r), ∀ x ∈ {x ∈ criticalPoints 𝓘(ℝ, E) f | f r < f x}, c < f x :=
    (hf.finite_criticalPoints.subset (sep_subset _ _)).eventually_all.2 fun _ hx ↦
      nhdsWithin_le_nhds (gt_mem_nhds hx.2)
  obtain ⟨c, hc, hrc⟩ := (h.and self_mem_nhdsWithin).exists
  exact ⟨c, hrc, fun x hx hrx ↦ hc x ⟨hx, hrx⟩⟩

end Levels

namespace IsAdaptedPseudoGradient

/-! ### Points of an orbit on a level -/

section LevelPoint

variable (hX : IsAdaptedPseudoGradient f X)

/-- The point of the orbit of `x` on the level `c`, at the crossing time
`Flow.levelCrossingTime`, when the orbit meets that level, and `x` otherwise. -/
private noncomputable def levelPoint (c : ℝ) (x : M) : M :=
  hX.flow (Flow.levelCrossingTime hX.flow f c x) x

/-- When the orbit of `x` meets the level `c`, its level point lies on that level and on that
orbit. -/
private theorem levelPoint_spec {c : ℝ} {x : M} (h : ∃ t, f (hX.flow t x) = c) :
    f (hX.levelPoint c x) = c ∧ ∃ t, hX.flow t x = hX.levelPoint c x :=
  ⟨Flow.apply_flow_levelCrossingTime h, _, rfl⟩

/-- Along a trajectory between distinct critical points, the level point is the unique point of
the orbit on the level. -/
private theorem levelPoint_eq {a b x : M} (hab : a ≠ b)
    (hx : x ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {t c : ℝ}
    (ht : f (hX.flow t x) = c) : hX.levelPoint c x = hX.flow t x :=
  congrArg (hX.flow · x) ((Flow.eq_levelCrossingTime_iff
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hx) ⟨t, ht⟩).2 ht).symm

/-- **Level points converge.** If points `u i` whose orbits meet the level `c` converge to a point
`w` of a trajectory from `a` to `b` crossing that level, then their level points converge to that
of `w`. -/
private theorem tendsto_levelPoint {a b w : M}
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

/-- A point of `W^s(r)` other than `r` lies on a trajectory from a critical point `b ≠ r` to `r`. -/
private theorem exists_mem_unstableSet_inter_stableSet_of_mem_stableSet
    (hf : IsMorse 𝓘(ℝ, E) f) {r x : M} (hx : x ∈ hX.flow.stableSet r) (hxr : x ≠ r) :
    ∃ b, b ≠ r ∧ x ∈ hX.flow.unstableSet b ∩ hX.flow.stableSet r := by
  obtain ⟨b, -, hb⟩ := hX.exists_tendsto_atBot hf x
  refine ⟨b, ?_, Flow.mem_unstableSet.2 hb, hx⟩
  rintro rfl
  exact hxr (hX.eq_of_mem_unstableSet_inter_stableSet ⟨Flow.mem_unstableSet.2 hb, hx⟩)

/-- The orbit of a point of `W^s(r)` above the level `c > f r` meets that level. -/
private theorem exists_flow_eq_of_mem_stableSet (hf : IsMorse 𝓘(ℝ, E) f) {r x : M}
    (hx : x ∈ hX.flow.stableSet r) {c : ℝ} (hrc : f r < c) (hcx : c < f x) :
    ∃ t, f (hX.flow t x) = c := by
  obtain ⟨b, hbr, hxb⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet hf hx
    (by rintro rfl; exact (hrc.trans hcx).false)
  exact (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hbr hxb hrc
    (hcx.trans (hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr hxb).2)).exists

/-- The orbit of a point of `W^u(p)` below the level `c < f p` meets that level. -/
private theorem exists_flow_eq_of_mem_unstableSet (hf : IsMorse 𝓘(ℝ, E) f) {p x : M}
    (hx : x ∈ hX.flow.unstableSet p) {c : ℝ} (hcp : c < f p) (hxc : f x < c) :
    ∃ t, f (hX.flow t x) = c := by
  obtain ⟨a, hpa, hxa, hac⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hf hx
    (t := 0) (by rwa [Flow.map_zero_apply]) hcp.le
  exact (hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpa hxa hac hcp).exists

/-- The point of the orbit of `x` on the level `min (f x) c`: the point `x` itself when
`f x ≤ c`, and otherwise the point where the orbit of `x` descends to the level `c`. -/
private noncomputable def lowerLevelPoint (c : ℝ) (x : M) : M :=
  if f x ≤ c then x else hX.levelPoint c x

/-- The point of the orbit of `x` on the level `max (f x) c`: the point `x` itself when
`c ≤ f x`, and otherwise the point where the orbit of `x` comes down from the level `c`. -/
private noncomputable def upperLevelPoint (c : ℝ) (x : M) : M :=
  if c ≤ f x then x else hX.levelPoint c x

/-- **The lower level point is continuous on a stable manifold.** For `f r < c`, the point of
the orbit of `x` on the level `min (f x) c` depends continuously on the point `x` of `W^s(r)`. -/
private theorem continuousOn_lowerLevelPoint (hf : IsMorse 𝓘(ℝ, E) f) {r : M} {c : ℝ}
    (hrc : f r < c) : ContinuousOn (hX.lowerLevelPoint c) (hX.flow.stableSet r) := by
  intro y hy
  have hcont : Continuous f := hX.mdifferentiable.continuous
  have hsplit : hX.flow.stableSet r =
      (hX.flow.stableSet r ∩ {x | f x ≤ c}) ∪ (hX.flow.stableSet r ∩ {x | c < f x}) := by
    rw [← inter_union_distrib_left, ← ofPred_or]
    simp only [le_or_gt, ofPred_true, inter_univ]
  rw [hsplit]
  refine ContinuousWithinAt.union ?_ ?_
  · -- Below the level, the lower level point is the point itself.
    by_cases hyc : f y ≤ c
    · exact continuousWithinAt_id.congr (fun x hx ↦ ite_eq_left hx.2) (ite_eq_left hyc)
    · exact continuousWithinAt_of_notMem_closure fun hcl ↦ hyc
        (closure_minimal inter_subset_right (isClosed_le hcont continuous_const) hcl)
  · -- Above the level, it is the level point, which converges along the trajectory through `y`.
    by_cases hcl : y ∈ closure (hX.flow.stableSet r ∩ {x | c < f x})
    · have hcy : c ≤ f y :=
        closure_lt_subset_le continuous_const hcont (closure_mono inter_subset_right hcl)
      obtain ⟨b, hbr, hyb⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet hf hy
        (by rintro rfl; linarith)
      have hfy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr hyb
      have hlim := hX.tendsto_levelPoint hyb hrc (hcy.trans_lt hfy.2) (u := id)
        (l := 𝓝[hX.flow.stableSet r ∩ {x | c < f x}] y) nhdsWithin_le_nhds
        (eventually_nhdsWithin_of_forall fun x hx ↦
          hX.exists_flow_eq_of_mem_stableSet hf hx.1 hrc hx.2)
      have hy' : hX.lowerLevelPoint c y = hX.levelPoint c y := by
        rcases hcy.lt_or_eq with hcy | hcy
        · exact ite_eq_right (not_le.2 hcy)
        · rw [lowerLevelPoint, ite_eq_left hcy.ge,
            hX.levelPoint_eq hbr hyb (t := 0) (by rw [Flow.map_zero_apply, hcy]),
            Flow.map_zero_apply]
      rw [ContinuousWithinAt, hy']
      exact hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
        (ite_eq_right (not_le.2 hx.2)).symm)
    · exact continuousWithinAt_of_notMem_closure hcl

/-- **The upper level point is continuous on an unstable manifold.** For `c < f p`, the point of
the orbit of `x` on the level `max (f x) c` depends continuously on the point `x` of `W^u(p)`. -/
private theorem continuousOn_upperLevelPoint (hf : IsMorse 𝓘(ℝ, E) f) {p : M} {c : ℝ}
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
    · exact continuousWithinAt_id.congr (fun x hx ↦ ite_eq_left hx.2) (ite_eq_left hyc)
    · exact continuousWithinAt_of_notMem_closure fun hcl ↦ hyc
        (closure_minimal inter_subset_right (isClosed_le continuous_const hcont) hcl)
  · -- Below the level, it is the level point, which converges along the trajectory through `y`.
    by_cases hcl : y ∈ closure (hX.flow.unstableSet p ∩ {x | f x < c})
    · have hcy : f y ≤ c :=
        closure_lt_subset_le hcont continuous_const (closure_mono inter_subset_right hcl)
      obtain ⟨a, hpa, hya, -⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hf hy
        (t := 0) (by rw [Flow.map_zero_apply]; linarith) le_rfl
      have hfy := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa hya
      have hlim := hX.tendsto_levelPoint hya (hfy.1.trans_le hcy) hcp (u := id)
        (l := 𝓝[hX.flow.unstableSet p ∩ {x | f x < c}] y) nhdsWithin_le_nhds
        (eventually_nhdsWithin_of_forall fun x hx ↦
          hX.exists_flow_eq_of_mem_unstableSet hf hx.1 hcp hx.2)
      have hy' : hX.upperLevelPoint c y = hX.levelPoint c y := by
        rcases hcy.lt_or_eq with hcy | hcy
        · exact ite_eq_right (not_le.2 hcy)
        · rw [upperLevelPoint, ite_eq_left hcy.ge,
            hX.levelPoint_eq hpa hya (t := 0) (by rw [Flow.map_zero_apply, hcy]),
            Flow.map_zero_apply]
      rw [ContinuousWithinAt, hy']
      exact hlim.congr' (eventually_nhdsWithin_of_forall fun x hx ↦
        (ite_eq_right (not_le.2 hx.2)).symm)
    · exact continuousWithinAt_of_notMem_closure hcl

/-- Moving a point of a trajectory between distinct critical points along its orbit does not move
its level point, when the orbit crosses the level. -/
private theorem levelPoint_flow {a b x : M} (hab : a ≠ b)
    (hx : x ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ}
    (hex : ∃ t, f (hX.flow t x) = c) (t : ℝ) :
    hX.levelPoint c (hX.flow t x) = hX.levelPoint c x := by
  obtain ⟨s, hs⟩ := hex
  exact (Flow.flow_levelCrossingTime_flow
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hab hx) hs t).trans
      (hX.levelPoint_eq hab hx hs).symm

/-- On a trajectory between distinct critical points crossing the level `c`, the level point is a
point of the orbit, on the trajectory and on the level. -/
private theorem exists_levelPoint_eq {a b z : M} (hab : a ≠ b)
    (hz : z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {c : ℝ} (hbc : f b < c)
    (hca : c < f a) :
    ∃ s, hX.levelPoint c z = hX.flow s z ∧
      hX.levelPoint c z ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b ∧
        f (hX.levelPoint c z) = c := by
  obtain ⟨s, hs, -⟩ := hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hab hz hbc hca
  rw [hX.levelPoint_eq hab hz hs]
  exact ⟨s, rfl, hX.flow.isInvariant_unstableSet_inter_stableSet a b s hz, hs⟩

end LevelPoint

/-! ### Level points near a broken trajectory -/

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
include h hf

/-- **Level points of a sequence breaking at the source.** Let `u n` be points of `W^u(p)`
converging to a point `y` of `W^u(a)`, where `ind p = ind a + 1`. If the points of their orbits on
the levels `max (f (u n)) c`, for `f a < c < f p`, converge to `w`, then `w` lies on a trajectory
from `p` to `a`, on the level `c`: the orbits of the `u n` break at `a`, and their level points
follow the first component. -/
private theorem mem_of_tendsto_upperLevelPoint_of_mem_unstableSet {p a y w : M} (hpa : p ≠ a)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f a + 1)
    (hy : y ∈ hX.flow.unstableSet a) {c : ℝ} (hac : f a < c) (hcp : c < f p) {u : ℕ → M}
    (hu : ∀ n, u n ∈ hX.flow.unstableSet p) (hlim : Tendsto u atTop (𝓝 y))
    (hw : Tendsto (fun n ↦ hX.upperLevelPoint c (u n)) atTop (𝓝 w)) :
    w ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet a ∧ f w = c := by
  have hcont : Continuous f := hX.mdifferentiable.continuous
  -- Flowing backward, the `u n` accumulate at a point `z ≠ a` of `W^s(a)`.
  obtain ⟨z, hz, hza, n, t, hn, -, hzlim⟩ :=
    hX.exists_tendsto_mem_stableSet_of_tendsto_mem_unstableSet hf hy hlim
      (Frequently.of_forall fun k ↦ (Flow.disjoint_unstableSet hpa).notMem_of_mem_left (hu k))
  -- The backward limit of `z` is `p`, as no index fits strictly between those of `a` and `p`.
  obtain ⟨p', -, hp'⟩ := hX.exists_tendsto_atBot hf z
  have hzp' : z ∈ hX.flow.unstableSet p' := Flow.mem_unstableSet.2 hp'
  have hzcl : z ∈ closure (hX.flow.unstableSet p) := mem_closure_of_tendsto hzlim
    (.of_forall fun k ↦ (Flow.apply_mem_unstableSet_iff _ _).2 (hu _))
  have hp'a : p' ≠ a := by
    rintro rfl
    exact hza (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hzp', hz⟩)
  have hlt := h.manifoldMorseIndex_lt hf hp'a ⟨z, hzp', hz⟩
  obtain rfl : p = p' := by
    by_contra hne
    have := h.manifoldMorseIndex_lt_of_reflTransGen hf
      (reflTransGen_of_mem_closure_unstableSet hf hzcl hzp') (Ne.symm hne)
    omega
  -- Eventually the `u n` lie below the level `c`, so their orbits cross it.
  have hya : f y ≤ f a :=
    Flow.le_of_mem_unstableSet_of_antitone hy hcont.continuousAt (hX.antitone_flow y)
  have hbelow₀ := (hcont.tendsto y).comp hlim |>.eventually (gt_mem_nhds (hya.trans_lt hac))
  have hw' : Tendsto (fun m ↦ hX.levelPoint c (u m)) atTop (𝓝 w) :=
    hw.congr' (hbelow₀.mono fun m hm ↦ ite_eq_right (not_le.2 hm))
  have hbelow : ∀ᶠ k in atTop, f (u (n k)) < c := hn.eventually hbelow₀
  have hex : ∀ᶠ k in atTop, ∃ s, f (hX.flow s (u (n k))) = c :=
    hbelow.mono fun k hk ↦ hX.exists_flow_eq_of_mem_unstableSet hf (hu _) hcp hk
  -- The level points of the shifted points converge to the level point of `z`.
  have h1 := hX.tendsto_levelPoint ⟨hzp', hz⟩ hac hcp hzlim (hex.mono fun k ⟨s, hs⟩ ↦
    ⟨s - t k, by rwa [← Flow.map_add, sub_add_cancel]⟩)
  have h2 : ∀ᶠ k in atTop,
      hX.levelPoint c (hX.flow (t k) (u (n k))) = hX.levelPoint c (u (n k)) := by
    filter_upwards [hbelow, hex] with k hk hk'
    obtain ⟨a', hpa', hxa', -⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt hf
      (hu (n k)) (t := 0) (by rwa [Flow.map_zero_apply]) hcp.le
    exact hX.levelPoint_flow hpa' hxa' hk' _
  obtain ⟨-, -, hmem, hc⟩ := hX.exists_levelPoint_eq hpa ⟨hzp', hz⟩ hac hcp
  exact tendsto_nhds_unique (hw'.comp hn) (h1.congr' h2) ▸ ⟨hmem, hc⟩

/-- **Level points of a sequence breaking at the target.** Let `u n` be points of `W^s(r)`
converging to a point `y` of `W^s(b)`, where `ind b = ind r + 1`. If the points of their orbits on
the levels `min (f (u n)) c`, for `f r < c < f b`, converge to `w`, then `w` lies on a trajectory
from `b` to `r`, on the level `c`: the orbits of the `u n` break at `b`, and their level points
follow the last component. -/
private theorem mem_of_tendsto_lowerLevelPoint_of_mem_stableSet {b r y w : M} (hbr : b ≠ r)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f b = manifoldMorseIndex 𝓘(ℝ, E) f r + 1)
    (hy : y ∈ hX.flow.stableSet b) {c : ℝ} (hrc : f r < c) (hcb : c < f b) {u : ℕ → M}
    (hu : ∀ n, u n ∈ hX.flow.stableSet r) (hlim : Tendsto u atTop (𝓝 y))
    (hw : Tendsto (fun n ↦ hX.lowerLevelPoint c (u n)) atTop (𝓝 w)) :
    w ∈ hX.flow.unstableSet b ∩ hX.flow.stableSet r ∧ f w = c := by
  have hcont : Continuous f := hX.mdifferentiable.continuous
  -- Flowing forward, the `u n` accumulate at a point `z ≠ b` of `W^u(b)`.
  obtain ⟨z, hz, hzb, n, t, hn, -, hzlim⟩ :=
    hX.exists_tendsto_mem_unstableSet_of_tendsto_mem_stableSet hf hy hlim
      (Frequently.of_forall fun k ↦ (Flow.disjoint_stableSet hbr).notMem_of_mem_right (hu k))
  -- The forward limit of `z` is `r`, as no index fits strictly between those of `r` and `b`.
  obtain ⟨r', -, hr'⟩ := hX.exists_tendsto_atTop hf z
  have hzr' : z ∈ hX.flow.stableSet r' := Flow.mem_stableSet.2 hr'
  have hzcl : z ∈ closure (hX.flow.stableSet r) := mem_closure_of_tendsto hzlim
    (.of_forall fun k ↦ (Flow.apply_mem_stableSet_iff _ _).2 (hu _))
  have hbr' : b ≠ r' := by
    rintro rfl
    exact hzb (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hz, hzr'⟩)
  have hlt := h.manifoldMorseIndex_lt hf hbr' ⟨z, hz, hzr'⟩
  obtain rfl : r = r' := by
    by_contra hne
    have := h.manifoldMorseIndex_lt_of_reflTransGen hf
      (reflTransGen_of_mem_closure_stableSet hf hzcl hzr') hne
    omega
  -- Eventually the `u n` lie above the level `c`, so their orbits cross it.
  have hyb : f b ≤ f y :=
    Flow.le_of_mem_stableSet_of_antitone hy hcont.continuousAt (hX.antitone_flow y)
  have habove₀ := (hcont.tendsto y).comp hlim |>.eventually (lt_mem_nhds (hcb.trans_le hyb))
  have hw' : Tendsto (fun m ↦ hX.levelPoint c (u m)) atTop (𝓝 w) :=
    hw.congr' (habove₀.mono fun m hm ↦ ite_eq_right (not_le.2 hm))
  have habove : ∀ᶠ k in atTop, c < f (u (n k)) := hn.eventually habove₀
  have hex : ∀ᶠ k in atTop, ∃ s, f (hX.flow s (u (n k))) = c :=
    habove.mono fun k hk ↦ hX.exists_flow_eq_of_mem_stableSet hf (hu _) hrc hk
  -- The level points of the shifted points converge to the level point of `z`.
  have h1 := hX.tendsto_levelPoint ⟨hz, hzr'⟩ hrc hcb hzlim (hex.mono fun k ⟨s, hs⟩ ↦
    ⟨s - t k, by rwa [← Flow.map_add, sub_add_cancel]⟩)
  have h2 : ∀ᶠ k in atTop,
      hX.levelPoint c (hX.flow (t k) (u (n k))) = hX.levelPoint c (u (n k)) := by
    filter_upwards [habove, hex] with k hk hk'
    obtain ⟨b', hb'r, hxb'⟩ := hX.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet hf
      (hu (n k)) (by rintro h; rw [h] at hk; exact (hrc.trans hk).false)
    exact hX.levelPoint_flow hb'r hxb' hk' _
  obtain ⟨-, -, hmem, hc⟩ := hX.exists_levelPoint_eq hbr ⟨hz, hzr'⟩ hrc hcb
  exact tendsto_nhds_unique (hw'.comp hn) (h1.congr' h2) ▸ ⟨hmem, hc⟩

end IsMorseSmale


/-! ### The compactified intersection of a Morse–Smale pair -/

section Pair

variable {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hX₀ : IsAdaptedPseudoGradient f₀ X₀) (hX₁ : IsAdaptedPseudoGradient f₁ X₁)

/-- The record of a point `x` of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`: the point of its `X₀`-orbit on the
level `max (f₀ x) c₀`, the point itself, and the point of its `X₁`-orbit on the level
`min (f₁ x) c₁`. -/
private noncomputable def pairRecord (c₀ c₁ : ℝ) (x : M) : M × M × M :=
  (hX₀.upperLevelPoint c₀ x, x, hX₁.lowerLevelPoint c₁ x)

/-- The records of the configurations broken at the source: a point of a trajectory of `X₀` from
`p` to a critical point `a` on the level `c₀`, a point `y` of `W^u_{X₀}(a) ∩ W^s_{X₁}(r)`, and the
point of the `X₁`-orbit of `y` on the level `min (f₁ y) c₁`. -/
private def sourceBrokenRecords (p r : M) (c₀ c₁ : ℝ) : Set (M × M × M) :=
  {w | ∃ a, manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₀ a + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₀ a = manifoldMorseIndex 𝓘(ℝ, E) f₁ r ∧
    w.1 ∈ hX₀.flow.unstableSet p ∩ hX₀.flow.stableSet a ∧ f₀ w.1 = c₀ ∧
    w.2.1 ∈ hX₀.flow.unstableSet a ∩ hX₁.flow.stableSet r ∧
    w.2.2 = hX₁.lowerLevelPoint c₁ w.2.1}

/-- The records of the configurations broken at the target: the point of the `X₀`-orbit of a
point `y` of `W^u_{X₀}(p) ∩ W^s_{X₁}(b)` on the level `max (f₀ y) c₀`, the point `y`, and a point
of a trajectory of `X₁` from `b` to `r` on the level `c₁`. -/
private def targetBrokenRecords (p r : M) (c₀ c₁ : ℝ) : Set (M × M × M) :=
  {w | ∃ b, manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ b ∧
    manifoldMorseIndex 𝓘(ℝ, E) f₁ b = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1 ∧
    w.2.1 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet b ∧
    w.1 = hX₀.upperLevelPoint c₀ w.2.1 ∧
    w.2.2 ∈ hX₁.flow.unstableSet b ∩ hX₁.flow.stableSet r ∧ f₁ w.2.2 = c₁}

/-- No configuration breaks both at the source and at the target. -/
private theorem disjoint_sourceBrokenRecords_targetBrokenRecords (p r : M) (c₀ c₁ : ℝ) :
    Disjoint (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) (hX₀.targetBrokenRecords hX₁ p r c₀ c₁) := by
  refine disjoint_left.2 ?_
  rintro w ⟨a, hpa, -, -, -, hy, -⟩ ⟨b, -, -, hy', -⟩
  exact (Flow.disjoint_unstableSet (x := p) (y := a) (by rintro rfl; omega)).notMem_of_mem_left
    hy'.1 hy.1

variable {p r : M} {c₀ c₁ : ℝ}

/-- The records of the configurations broken at the source are the images of the configurations
of `morseSourceBrokenPairSet`, moving the point of the trajectory from `p` to the level `c₀`. -/
private theorem sourceBrokenRecords_eq_image (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦
        (hX₀.levelPoint c₀ x.2.1, x.2.2, hX₁.lowerLevelPoint c₁ x.2.2)) ''
        hX₀.morseSourceBrokenPairSet hX₁ p r := by
  ext w
  constructor
  · rintro ⟨a, hpa, har, hw₁, hw₁c, hy, hw₃⟩
    have ha := mem_criticalPoints_iff_mfderiv_eq_zero.2 (hX₀.mfderiv_eq_zero_of_mem_stableSet hw₁.2)
    have hpa' : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' hw₁
    -- Move the point of the trajectory to its middle level.
    obtain ⟨t, ht, -⟩ := hX₀.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hpa' hw₁
      (c := (f₀ p + f₀ a) / 2) (by linarith [hfa.1, hfa.2]) (by linarith [hfa.1, hfa.2])
    have hz := hX₀.flow.isInvariant_unstableSet_inter_stableSet p a t hw₁
    refine ⟨(⟨a, ha⟩, hX₀.flow t w.1, w.2.1), (hX₀.mem_morseSourceBrokenPairSet hX₁).2
      ⟨hpa, har, (hX₀.mem_morseTrajectorySlice).2 ⟨hz.1, hz.2, ht⟩, hy⟩, ?_⟩
    have hlev : hX₀.levelPoint c₀ (hX₀.flow t w.1) = w.1 := by
      rw [hX₀.levelPoint_eq hpa' hz (t := -t) (by rw [← Flow.map_add, neg_add_cancel,
        Flow.map_zero_apply, hw₁c]), ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    exact Prod.ext hlev (Prod.ext rfl hw₃.symm)
  · rintro ⟨⟨a, z, y⟩, hx, rfl⟩
    obtain ⟨hpa, har, hz, hy⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
    dsimp only at hpa har hz hy
    rw [mem_morseTrajectorySlice] at hz
    have hpa' : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ⟨hz.1, hz.2.1⟩
    obtain ⟨-, -, hmem, hc⟩ := hX₀.exists_levelPoint_eq hpa' ⟨hz.1, hz.2.1⟩
      (hgap₀ a a.property (hfa.1.trans hfa.2)) hc₀
    exact ⟨a, hpa, har, hmem, hc, hy, rfl⟩

/-- Distinct configurations broken at the source have distinct records. -/
private theorem injOn_sourceBrokenRecords (hc₀ : c₀ < f₀ p)
    (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₀ × M × M ↦
        (hX₀.levelPoint c₀ x.2.1, x.2.2, hX₁.lowerLevelPoint c₁ x.2.2))
      (hX₀.morseSourceBrokenPairSet hX₁ p r) := by
  rintro ⟨a, z, y⟩ hx ⟨a', z', y'⟩ hx' heq
  obtain ⟨hpa, -, hz, -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
  obtain ⟨hpa₂, -, hz', -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx'
  dsimp only at hpa hz hpa₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨heq, rfl, -⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  have hpa' : p ≠ a := by rintro rfl; omega
  have hpa₂' : p ≠ a' := by rintro rfl; omega
  have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ⟨hz.1, hz.2.1⟩
  have hfa' := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa₂' ⟨hz'.1, hz'.2.1⟩
  obtain ⟨s, hs, hmem, -⟩ := hX₀.exists_levelPoint_eq hpa' ⟨hz.1, hz.2.1⟩
    (hgap₀ a a.property (hfa.1.trans hfa.2)) hc₀
  obtain ⟨s', hs', hmem', -⟩ := hX₀.exists_levelPoint_eq hpa₂' ⟨hz'.1, hz'.2.1⟩
    (hgap₀ a' a'.property (hfa'.1.trans hfa'.2)) hc₀
  -- The common level point lies on the stable sets of `a` and `a'`, so `a = a'`.
  obtain rfl : a = a' := Subtype.ext <| by
    by_contra hne
    exact (Flow.disjoint_stableSet hne).notMem_of_mem_left hmem.2 (heq ▸ hmem'.2)
  -- The points `z` and `z'` lie on one orbit, on the same middle level.
  have hzz : z = z' := hX₀.eq_of_flow_eq_of_value_eq hpa' ⟨hz.1, hz.2.1⟩
    (hs.symm.trans (heq.trans hs')) (hz.2.2.trans hz'.2.2.symm)
  rw [hzz]

/-- The records of the configurations broken at the target are the images of the configurations
of `morseTargetBrokenPairSet`, moving the point of the trajectory to `r` to the level `c₁`. -/
private theorem targetBrokenRecords_eq_image (hc₁ : f₁ r < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x) :
    hX₀.targetBrokenRecords hX₁ p r c₀ c₁ =
      (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦
        (hX₀.upperLevelPoint c₀ x.2.1, x.2.1, hX₁.levelPoint c₁ x.2.2)) ''
        hX₀.morseTargetBrokenPairSet hX₁ p r := by
  ext w
  constructor
  · rintro ⟨b, hpb, hbr, hy, hw₁, hw₃, hw₃c⟩
    have hb := mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₁.mfderiv_eq_zero_of_mem_unstableSet hw₃.1)
    have hbr' : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' hw₃
    -- Move the point of the trajectory to its middle level.
    obtain ⟨t, ht, -⟩ := hX₁.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hbr' hw₃
      (c := (f₁ b + f₁ r) / 2) (by linarith [hfb.1, hfb.2]) (by linarith [hfb.1, hfb.2])
    have hz := hX₁.flow.isInvariant_unstableSet_inter_stableSet b r t hw₃
    refine ⟨(⟨b, hb⟩, w.2.1, hX₁.flow t w.2.2), (hX₀.mem_morseTargetBrokenPairSet hX₁).2
      ⟨hpb, hbr, hy, (hX₁.mem_morseTrajectorySlice).2 ⟨hz.1, hz.2, ht⟩⟩, ?_⟩
    have hlev : hX₁.levelPoint c₁ (hX₁.flow t w.2.2) = w.2.2 := by
      rw [hX₁.levelPoint_eq hbr' hz (t := -t) (by rw [← Flow.map_add, neg_add_cancel,
        Flow.map_zero_apply, hw₃c]), ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    exact Prod.ext hw₁.symm (Prod.ext rfl hlev)
  · rintro ⟨⟨b, y, z⟩, hx, rfl⟩
    obtain ⟨hpb, hbr, hy, hz⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
    dsimp only at hpb hbr hy hz
    rw [mem_morseTrajectorySlice] at hz
    have hbr' : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' ⟨hz.1, hz.2.1⟩
    obtain ⟨-, -, hmem, hc⟩ := hX₁.exists_levelPoint_eq hbr' ⟨hz.1, hz.2.1⟩ hc₁
      (hgap₁ b b.property (hfb.1.trans hfb.2))
    exact ⟨b, hpb, hbr, hy, rfl, hmem, hc⟩

/-- Distinct configurations broken at the target have distinct records. -/
private theorem injOn_targetBrokenRecords (hc₁ : f₁ r < c₁)
    (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x) :
    InjOn (fun x : criticalPoints 𝓘(ℝ, E) f₁ × M × M ↦
        (hX₀.upperLevelPoint c₀ x.2.1, x.2.1, hX₁.levelPoint c₁ x.2.2))
      (hX₀.morseTargetBrokenPairSet hX₁ p r) := by
  rintro ⟨b, y, z⟩ hx ⟨b', y', z'⟩ hx' heq
  obtain ⟨-, hbr, -, hz⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
  obtain ⟨-, hbr₂, -, hz'⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx'
  dsimp only at hbr hz hbr₂ hz'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl, heq⟩ := heq
  rw [mem_morseTrajectorySlice] at hz hz'
  have hbr' : b ≠ r := by rintro rfl; omega
  have hbr₂' : b' ≠ r := by rintro rfl; omega
  have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' ⟨hz.1, hz.2.1⟩
  have hfb' := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr₂' ⟨hz'.1, hz'.2.1⟩
  obtain ⟨s, hs, hmem, -⟩ := hX₁.exists_levelPoint_eq hbr' ⟨hz.1, hz.2.1⟩ hc₁
    (hgap₁ b b.property (hfb.1.trans hfb.2))
  obtain ⟨s', hs', hmem', -⟩ := hX₁.exists_levelPoint_eq hbr₂' ⟨hz'.1, hz'.2.1⟩ hc₁
    (hgap₁ b' b'.property (hfb'.1.trans hfb'.2))
  -- The common level point lies on the unstable sets of `b` and `b'`, so `b = b'`.
  obtain rfl : b = b' := Subtype.ext <| by
    by_contra hne
    exact (Flow.disjoint_unstableSet hne).notMem_of_mem_left hmem.1 (heq ▸ hmem'.1)
  -- The points `z` and `z'` lie on one orbit, on the same middle level.
  have hzz : z = z' := hX₁.eq_of_flow_eq_of_value_eq hbr' ⟨hz.1, hz.2.1⟩
    (hs.symm.trans (heq.trans hs')) (hz.2.2.trans hz'.2.2.symm)
  rw [hzz]


namespace IsMorseSmalePair

variable {hX₀ hX₁} (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
  (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
  (hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1)
  (hc₀ : c₀ < f₀ p) (hgap₀ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₀, f₀ x < f₀ p → f₀ x < c₀)
  (hc₁ : f₁ r < c₁) (hgap₁ : ∀ x ∈ criticalPoints 𝓘(ℝ, E) f₁, f₁ r < f₁ x → c₁ < f₁ x)

include h h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁

/-- **The limits of records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`**, for `ind p = ind r + 1`, are records
of its points or of configurations broken at the source or at the target. -/
private theorem closure_pairRecords_subset :
    closure (hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)) ⊆
      hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) ∪
        (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) := by
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  set S := hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r
  intro q hq
  obtain ⟨v, hvP, hvq⟩ := mem_closure_iff_seq_limit.1 hq
  choose x hxS hxv using hvP
  obtain rfl : (fun n ↦ hX₀.pairRecord hX₁ c₀ c₁ (x n)) = v := funext hxv
  set y := q.2.1
  have hx : Tendsto x atTop (𝓝 y) := ((continuous_fst.comp continuous_snd).tendsto q).comp hvq
  have h₁q : Tendsto (fun n ↦ hX₀.upperLevelPoint c₀ (x n)) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hvq
  have h₃q : Tendsto (fun n ↦ hX₁.lowerLevelPoint c₁ (x n)) atTop (𝓝 q.2.2) :=
    ((continuous_snd.comp continuous_snd).tendsto q).comp hvq
  have hxS' : Tendsto x atTop (𝓝[S] y) := tendsto_nhdsWithin_iff.2 ⟨hx, .of_forall hxS⟩
  -- Where the limit lies on `W^u_{X₀}(p)`, resp. `W^s_{X₁}(r)`, its records are the limits.
  have hup (hy : y ∈ hX₀.flow.unstableSet p) : q.1 = hX₀.upperLevelPoint c₀ y :=
    tendsto_nhds_unique h₁q ((hX₀.continuousOn_upperLevelPoint hf₀ hc₀ y hy).tendsto.comp
      (tendsto_nhdsWithin_mono_right inter_subset_left hxS'))
  have hlow (hy : y ∈ hX₁.flow.stableSet r) : q.2.2 = hX₁.lowerLevelPoint c₁ y :=
    tendsto_nhds_unique h₃q ((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁ y hy).tendsto.comp
      (tendsto_nhdsWithin_mono_right inter_subset_right hxS'))
  rcases h.closure_unstableSet_inter_stableSet_subset h₀ h₁ hf₀ hf₁ hind
    (mem_closure_of_tendsto hx (.of_forall hxS)) with (hy | hy) | hy
  · exact Or.inl ⟨y, hy, Prod.ext (hup hy.1).symm (Prod.ext rfl (hlow hy.2).symm)⟩
  · -- Breaking at the source, at a critical point `a` below the level `c₀`.
    obtain ⟨a, ⟨har, z, hz⟩, hya⟩ := mem_iUnion₂.1 hy
    have hpa : p ≠ a := by rintro rfl; omega
    have hfa := hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa hz
    have hac : f₀ a < c₀ := hgap₀ a (mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₀.mfderiv_eq_zero_of_mem_unstableSet hya.1)) (hfa.1.trans hfa.2)
    obtain ⟨hq₁, hq₁c⟩ := h₀.mem_of_tendsto_upperLevelPoint_of_mem_unstableSet hf₀ hpa
      (by omega) hya.1 hac hc₀ (fun n ↦ (hxS n).1) hx h₁q
    exact Or.inr (Or.inl ⟨a, by omega, har, hq₁, hq₁c, hya, hlow hya.2⟩)
  · -- Breaking at the target, at a critical point `b` above the level `c₁`.
    obtain ⟨b, ⟨hbp, z, hz⟩, hyb⟩ := mem_iUnion₂.1 hy
    have hbr : b ≠ r := by rintro rfl; omega
    have hfb := hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr hz
    have hcb : c₁ < f₁ b := hgap₁ b (mem_criticalPoints_iff_mfderiv_eq_zero.2
      (hX₁.mfderiv_eq_zero_of_mem_stableSet hyb.2)) (hfb.1.trans hfb.2)
    obtain ⟨hq₃, hq₃c⟩ := h₁.mem_of_tendsto_lowerLevelPoint_of_mem_stableSet hf₁ hbr
      (by omega) hyb.2 hc₁ hcb (fun n ↦ (hxS n).2) hx h₃q
    exact Or.inr (Or.inr ⟨b, by omega, by omega, hyb, hup hyb.1, hq₃, hq₃c⟩)


omit hind in
/-- There are finitely many records of broken configurations. -/
private theorem finite_brokenRecords :
    (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁).Finite := by
  rw [hX₀.sourceBrokenRecords_eq_image hX₁ (r := r) (c₁ := c₁) hc₀ hgap₀,
    hX₀.targetBrokenRecords_eq_image hX₁ (p := p) (c₀ := c₀) hc₁ hgap₁]
  exact ((h.finite_morseSourceBrokenPairSet h₀ h₁ hf₀ hf₁ p r).image _).union
    ((h.finite_morseTargetBrokenPairSet h₀ h₁ hf₀ hf₁ p r).image _)

/-- Near any of its points `w`, the compactified space contains only `w` and records of points of
the intersection: it adds finitely many records of broken configurations. -/
private theorem eventually_eq_or_mem_pairRecords (w : M × M × M) :
    ∀ᶠ q in 𝓝[closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))] w,
      q = w ∨ q ∈ hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r) := by
  have hfar : ((hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) \
      {w})ᶜ ∈ 𝓝 w :=
    (h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁).sdiff.isClosed.isOpen_compl.mem_nhds
      (by simp)
  filter_upwards [nhdsWithin_le_nhds hfar, self_mem_nhdsWithin] with q hq hqcl
  rcases h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hqcl with hqP | hqB
  · exact Or.inr hqP
  · exact Or.inl (not_not.1 fun hne ↦ hq ⟨hqB, hne⟩)

/-- **The compactified intersection is one-dimensional at unbroken records.** Every record of a
point of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)` has a neighbourhood in the closure of the records
homeomorphic to an open subset of `ℝ`. -/
private theorem exists_nhds_homeomorph_of_mem_pairRecords {q : M × M × M}
    (hq : q ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
      (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)))
    (hqP : q ∈ hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)) :
    ∃ N ∈ 𝓝 (⟨q, hq⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
      ∃ V : Set ℝ, IsOpen V ∧ Nonempty (V ≃ₜ N) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hqP
  set S := hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r
  set P := hX₀.pairRecord hX₁ c₀ c₁ '' S
  have hx₀P : hX₀.pairRecord hX₁ c₀ c₁ x₀ ∈ P := mem_image_of_mem _ hx₀
  have hcont : ContinuousOn (hX₀.pairRecord hX₁ c₀ c₁) S :=
    ((hX₀.continuousOn_upperLevelPoint hf₀ hc₀).mono inter_subset_left).prodMk
      (continuousOn_id.prodMk ((hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).mono inter_subset_right))
  -- The records of the points of `S` form a copy of `S`.
  have hmemS (w : P) : (w : M × M × M).2.1 ∈ S := by
    obtain ⟨_, x, hx, rfl⟩ := w
    exact hx
  let Φ : P ≃ₜ S :=
    { toFun w := ⟨(w : M × M × M).2.1, hmemS w⟩
      invFun x := ⟨hX₀.pairRecord hX₁ c₀ c₁ x, mem_image_of_mem _ x.property⟩
      left_inv := by rintro ⟨_, ⟨x, hx, rfl⟩⟩; rfl
      right_inv _ := rfl
      continuous_toFun :=
        ((continuous_fst.comp continuous_snd).comp continuous_subtypeVal).subtype_mk hmemS
      continuous_invFun :=
        (hcont.comp_continuous continuous_subtypeVal fun x ↦ x.property).subtype_mk _ }
  -- `S` is a manifold modelled on a line `L`.
  obtain ⟨L, hL, C, -, -⟩ := h.exists_unstableSet_inter_stableSet_isManifold hf₀ ⟨x₀, hx₀⟩
  let _ := C
  have hL1 : Module.finrank ℝ L = Module.finrank ℝ ℝ := by rw [Module.finrank_self]; omega
  -- The unbroken records sit openly in the compactified space.
  let ι : P → closure P := fun x ↦ ⟨x.val, subset_closure x.property⟩
  have hι : IsOpenEmbedding ι := by
    refine ⟨(IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).1 IsEmbedding.subtypeVal, ?_⟩
    have hc : IsClosed ((↑) ⁻¹' (closure P \ P) : Set (closure P)) :=
      ((h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁).subset fun w hw ↦
        ((h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
          (mem_of_mem_sdiff hw)).resolve_left (notMem_of_mem_sdiff hw))).isClosed.preimage
          continuous_subtypeVal
    convert hc.isOpen_compl using 1
    ext x
    simp only [mem_range, mem_compl_iff, mem_preimage, Set.mem_sdiff, Subtype.coe_prop, true_and,
      not_not]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.property, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have : Nonempty P := ⟨⟨_, hx₀P⟩⟩
  let G := ((hι.toOpenPartialHomeomorph ι).symm.trans Φ.toOpenPartialHomeomorph).trans
    ((chartAt L (Φ ⟨_, hx₀P⟩)).trans
      (ContinuousLinearEquiv.ofFinrankEq hL1).toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨G.source, G.open_source.mem_nhds ?_, G.target, G.open_target,
    ⟨G.toHomeomorphSourceTarget.symm⟩⟩
  have hιw : ι ⟨_, hx₀P⟩ = ⟨_, hq⟩ := rfl
  simp [G, ← hιw, hι.toOpenPartialHomeomorph_left_inv]

/-- **A configuration broken at the source is an endpoint.** The record of a configuration broken
at the source lies in the closure of the records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and has a
neighbourhood there homeomorphic to a half-open interval `[0, δ)`, by a homeomorphism sending `0`
to it. -/
private theorem exists_homeomorph_Ico_of_mem_sourceBrokenRecords {w : M × M × M}
    (hw : w ∈ hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) :
    ∃ hb : w ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
          (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
            (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))) = ⟨w, hb⟩ := by
  have hcont₀ : Continuous f₀ := hX₀.mdifferentiable.continuous
  have hnear := h.eventually_eq_or_mem_pairRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ w
  obtain ⟨a₁, y, w₃⟩ := w
  obtain ⟨a, hpa, har, ha₁, ha₁c, hy, hw₃⟩ := hw
  dsimp only at ha₁ ha₁c hy hw₃
  subst hw₃
  have hpa' : p ≠ a := by rintro rfl; omega
  have hyc : f₀ y < c₀ := (Flow.le_of_mem_unstableSet_of_antitone hy.1
    hcont₀.continuousAt (hX₀.antitone_flow y)).trans_lt
      (ha₁c ▸ (hX₀.mem_Ioo_of_mem_unstableSet_inter_stableSet hpa' ha₁).1)
  obtain ⟨N, δ, hδ, e, he, hNsub, hN⟩ := h.exists_homeomorph_Ico_of_source h₀ hf₀ hpa har ha₁ hy
  -- The gluing chart records a point by its `X₀`-orbit on the level `c₀`; the third component of
  -- the records is a continuous function of the second.
  have hlow : ContinuousOn (fun v : M × M ↦ hX₁.lowerLevelPoint c₁ v.2) (insert (a₁, y)
      {v | v.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧ f₀ v.1 = f₀ a₁ ∧
        ∃ t, hX₀.flow t v.1 = v.2}) :=
    (hX₁.continuousOn_lowerLevelPoint hf₁ hc₁).comp continuous_snd.continuousOn fun v hv ↦ by
      rcases hv with rfl | hv
      exacts [hy.2, hv.1.2]
  refine exists_homeomorph_Ico_closure_of_homeomorph_Ico (fun q ↦ (q.1, q.2.1))
    (fun v ↦ (v.1, v.2, hX₁.lowerLevelPoint c₁ v.2)) (by fun_prop)
    (continuousOn_fst.prodMk (continuousOn_snd.prodMk hlow)) (fun _ _ ↦ rfl) rfl ?_ ?_ hδ e he
    hNsub hN
  · -- Near `(a₁, y)`, the points of the chart lie below the level `c₀`, so they are records.
    have hev : ∀ᶠ v in 𝓝 (a₁, y), f₀ v.2 < c₀ :=
      ((hcont₀.comp continuous_snd).tendsto (a₁, y)).eventually (gt_mem_nhds hyc)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvR
    obtain ⟨hvS, hv₁, t, ht⟩ := hvR.1.resolve_left hvR.2
    refine ⟨v.2, hvS, Prod.ext ?_ rfl⟩
    obtain ⟨a', hpa'', hva', -⟩ := hX₀.exists_mem_unstableSet_inter_stableSet_of_apply_flow_lt
      hf₀ hvS.1 (t := 0) (by rwa [Flow.map_zero_apply]) hc₀.le
    change hX₀.upperLevelPoint c₀ v.2 = v.1
    rw [upperLevelPoint, ite_eq_right (not_le.2 hv), hX₀.levelPoint_eq hpa'' hva' (t := -t)
      (by rw [← ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply, hv₁, ha₁c]), ← ht,
      ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · -- Near the broken record, the records lie below the level `c₀` and come from the chart.
    have hev : ∀ᶠ q in 𝓝 (a₁, y, hX₁.lowerLevelPoint c₁ y), f₀ q.2.1 < c₀ :=
      (((hcont₀.comp continuous_fst).comp continuous_snd).tendsto _).eventually (gt_mem_nhds hyc)
    filter_upwards [hnear, nhdsWithin_le_nhds hev] with q hq hqc
    rcases hq with rfl | ⟨x, hxS, rfl⟩
    · exact ⟨mem_insert _ _, rfl⟩
    · have hxc : f₀ x < c₀ := hqc
      obtain ⟨hlc, t, ht⟩ :=
        hX₀.levelPoint_spec (hX₀.exists_flow_eq_of_mem_unstableSet hf₀ hxS.1 hc₀ hxc)
      have hup : hX₀.upperLevelPoint c₀ x = hX₀.levelPoint c₀ x := ite_eq_right (not_le.2 hxc)
      refine ⟨Or.inr ⟨hxS, ?_, -t, ?_⟩, rfl⟩
      · change f₀ (hX₀.upperLevelPoint c₀ x) = f₀ a₁
        rw [hup, hlc, ha₁c]
      · change hX₀.flow (-t) (hX₀.upperLevelPoint c₀ x) = x
        rw [hup, ← ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

/-- **A configuration broken at the target is an endpoint.** The record of a configuration broken
at the target lies in the closure of the records of `W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and has a
neighbourhood there homeomorphic to a half-open interval `[0, δ)`, by a homeomorphism sending `0`
to it. -/
private theorem exists_homeomorph_Ico_of_mem_targetBrokenRecords {w : M × M × M}
    (hw : w ∈ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) :
    ∃ hb : w ∈ closure (hX₀.pairRecord hX₁ c₀ c₁ ''
        (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)),
      ∃ N ∈ 𝓝 (⟨w, hb⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
          (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))),
        ∃ (δ : ℝ) (hδ : 0 < δ) (e : Ico (0 : ℝ) δ ≃ₜ N),
          (e ⟨0, left_mem_Ico.2 hδ⟩ : closure (hX₀.pairRecord hX₁ c₀ c₁ ''
            (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r))) = ⟨w, hb⟩ := by
  have hcont₁ : Continuous f₁ := hX₁.mdifferentiable.continuous
  have hnear := h.eventually_eq_or_mem_pairRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ w
  obtain ⟨w₁, y, a₂⟩ := w
  obtain ⟨b, hpb, hbr, hy, hw₁, ha₂, ha₂c⟩ := hw
  dsimp only at ha₂ ha₂c hy hw₁
  subst hw₁
  have hbr' : b ≠ r := by rintro rfl; omega
  have hyc : c₁ < f₁ y :=
    (ha₂c ▸ (hX₁.mem_Ioo_of_mem_unstableSet_inter_stableSet hbr' ha₂).2).trans_le
    (Flow.le_of_mem_stableSet_of_antitone hy.2 hcont₁.continuousAt (hX₁.antitone_flow y))
  obtain ⟨N, δ, hδ, e, he, hNsub, hN⟩ :=
    h.exists_homeomorph_Ico_of_target h₁ hf₀ hf₁ hbr hpb ha₂ hy
  -- The gluing chart records a point by its `X₁`-orbit on the level `c₁`; the first component of
  -- the records is a continuous function of the second.
  have hup : ContinuousOn (fun v : M × M ↦ hX₀.upperLevelPoint c₀ v.2) (insert (a₂, y)
      {v | v.2 ∈ hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r ∧ f₁ v.1 = f₁ a₂ ∧
        ∃ t, hX₁.flow t v.1 = v.2}) :=
    (hX₀.continuousOn_upperLevelPoint hf₀ hc₀).comp continuous_snd.continuousOn fun v hv ↦ by
      rcases hv with rfl | hv
      exacts [hy.1, hv.1.1]
  refine exists_homeomorph_Ico_closure_of_homeomorph_Ico (fun q ↦ (q.2.2, q.2.1))
    (fun v ↦ (hX₀.upperLevelPoint c₀ v.2, v.2, v.1)) (by fun_prop)
    (hup.prodMk (continuousOn_snd.prodMk continuousOn_fst)) (fun _ _ ↦ rfl) rfl ?_ ?_ hδ e he
    hNsub hN
  · -- Near `(a₂, y)`, the points of the chart lie above the level `c₁`, so they are records.
    have hev : ∀ᶠ v in 𝓝 (a₂, y), c₁ < f₁ v.2 :=
      ((hcont₁.comp continuous_snd).tendsto (a₂, y)).eventually (lt_mem_nhds hyc)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with v hv hvR
    obtain ⟨hvS, hv₁, t, ht⟩ := hvR.1.resolve_left hvR.2
    refine ⟨v.2, hvS, Prod.ext rfl (Prod.ext rfl ?_)⟩
    obtain ⟨b', hb'r, hvb'⟩ := hX₁.exists_mem_unstableSet_inter_stableSet_of_mem_stableSet
      hf₁ hvS.2 (by rintro h; rw [h] at hv; exact (hc₁.trans hv).false)
    change hX₁.lowerLevelPoint c₁ v.2 = v.1
    rw [lowerLevelPoint, ite_eq_right (not_le.2 hv), hX₁.levelPoint_eq hb'r hvb' (t := -t)
      (by rw [← ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply, hv₁, ha₂c]), ← ht,
      ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · -- Near the broken record, the records lie above the level `c₁` and come from the chart.
    have hev : ∀ᶠ q in 𝓝 (hX₀.upperLevelPoint c₀ y, y, a₂), c₁ < f₁ q.2.1 :=
      (((hcont₁.comp continuous_fst).comp continuous_snd).tendsto _).eventually (lt_mem_nhds hyc)
    filter_upwards [hnear, nhdsWithin_le_nhds hev] with q hq hqc
    rcases hq with rfl | ⟨x, hxS, rfl⟩
    · exact ⟨mem_insert _ _, rfl⟩
    · have hxc : c₁ < f₁ x := hqc
      obtain ⟨hlc, t, ht⟩ :=
        hX₁.levelPoint_spec (hX₁.exists_flow_eq_of_mem_stableSet hf₁ hxS.2 hc₁ hxc)
      have hlow : hX₁.lowerLevelPoint c₁ x = hX₁.levelPoint c₁ x := ite_eq_right (not_le.2 hxc)
      refine ⟨Or.inr ⟨hxS, ?_, -t, ?_⟩, rfl⟩
      · change f₁ (hX₁.lowerLevelPoint c₁ x) = f₁ a₂
        rw [hlow, hlc, ha₂c]
      · change hX₁.flow (-t) (hX₁.lowerLevelPoint c₁ x) = x
        rw [hlow, ← ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]

end IsMorseSmalePair


namespace IsMorseSmalePair

variable {hX₀ hX₁} (h : IsMorseSmalePair hX₀ hX₁) (h₀ : hX₀.IsMorseSmale)
  (h₁ : hX₁.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)
include h h₀ h₁ hf₀ hf₁

/-- **Broken configurations of a Morse–Smale pair come in pairs.** Let `(X₀, X₁)` be a Morse–Smale
pair of Morse–Smale pseudo-gradients adapted to Morse functions `f₀` and `f₁` on a compact
boundaryless manifold. Between any critical point `p` of `f₀` and any critical point `r` of `f₁`,
the configurations broken at the source and those broken at the target are evenly many in total:
when `ind p = ind r + 1` they are the endpoints of the compactified one-dimensional intersection
`W^u_{X₀}(p) ∩ W^s_{X₁}(r)`, and otherwise there are none. -/
theorem even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet
    (p : criticalPoints 𝓘(ℝ, E) f₀) (r : criticalPoints 𝓘(ℝ, E) f₁) :
    Even ((hX₀.morseSourceBrokenPairSet hX₁ p r).ncard +
      (hX₀.morseTargetBrokenPairSet hX₁ p r).ncard) := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ r + 1
  swap
  · -- Without an index drop by one, no configuration breaks.
    have hs : hX₀.morseSourceBrokenPairSet hX₁ p r = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
      obtain ⟨h₁, h₂, -⟩ := (hX₀.mem_morseSourceBrokenPairSet hX₁).1 hx
      omega
    have ht : hX₀.morseTargetBrokenPairSet hX₁ p r = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
      obtain ⟨h₁, h₂, -⟩ := (hX₀.mem_morseTargetBrokenPairSet hX₁).1 hx
      omega
    simp [hs, ht]
  -- Record the points of the intersection on levels `c₀` below `p` and `c₁` above `r`.
  obtain ⟨c₀, hc₀, hgap₀⟩ := hf₀.exists_lt_forall_lt (p : M)
  obtain ⟨c₁, hc₁, hgap₁⟩ := hf₁.exists_gt_forall_gt (r : M)
  set P := hX₀.pairRecord hX₁ c₀ c₁ '' (hX₀.flow.unstableSet p ∩ hX₁.flow.stableSet r)
  have hcl := h.closure_pairRecords_subset h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
  have hs (w : M × M × M) (hw : w ∈ hX₀.sourceBrokenRecords hX₁ p r c₀ c₁) :=
    h.exists_homeomorph_Ico_of_mem_sourceBrokenRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hw
  have ht (w : M × M × M) (hw : w ∈ hX₀.targetBrokenRecords hX₁ p r c₀ c₁) :=
    h.exists_homeomorph_Ico_of_mem_targetBrokenRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁ hw
  have hfin := h.finite_brokenRecords h₀ h₁ hf₀ hf₁ hc₀ hgap₀ hc₁ hgap₁
  -- The closure of the records is a compact space locally modelled on the half-line, whose
  -- endpoints are the records of broken configurations.
  have : CompactSpace (closure P) := isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have hE : Even (((↑) : closure P → M × M × M) ⁻¹'
      (hX₀.sourceBrokenRecords hX₁ p r c₀ c₁ ∪ hX₀.targetBrokenRecords hX₁ p r c₀ c₁)).ncard := by
    refine even_ncard_of_forall_exists_homeomorph_Ico (F := ℝ) (Module.finrank_self ℝ)
      (fun q hq ↦ ?_) fun q hq ↦ ?_
    · rcases hq with hq | hq
      · obtain ⟨_, N, hN, δ, hδ, e, he⟩ := hs _ hq
        exact ⟨N, hN, δ, hδ, e, he⟩
      · obtain ⟨_, N, hN, δ, hδ, e, he⟩ := ht _ hq
        exact ⟨N, hN, δ, hδ, e, he⟩
    · exact h.exists_nhds_homeomorph_of_mem_pairRecords h₀ h₁ hf₀ hf₁ hind hc₀ hgap₀ hc₁ hgap₁
        q.property ((hcl q.property).resolve_right hq)
  -- Count the endpoints through the records of the broken configurations.
  rw [ncard_preimage_of_injective_subset_range Subtype.val_injective (by
      rw [Subtype.range_coe]
      exact union_subset (fun w hw ↦ (hs w hw).1) fun w hw ↦ (ht w hw).1),
    ncard_union_eq (hX₀.disjoint_sourceBrokenRecords_targetBrokenRecords hX₁ p r c₀ c₁)
      (hfin.subset subset_union_left) (hfin.subset subset_union_right),
    hX₀.sourceBrokenRecords_eq_image hX₁ hc₀ hgap₀, hX₀.targetBrokenRecords_eq_image hX₁ hc₁ hgap₁,
    (hX₀.injOn_sourceBrokenRecords hX₁ hc₀ hgap₀).ncard_image,
    (hX₀.injOn_targetBrokenRecords hX₁ hc₁ hgap₁).ncard_image] at hE
  exact hE

/-- **The mod-two pair map is a chain map.** For a Morse–Smale pair `(X₀, X₁)` of Morse–Smale
pseudo-gradients adapted to Morse functions on a compact boundaryless manifold, and any choice of
orientations, the pair map with coefficients in `ZMod 2` commutes with the Morse boundaries:
`∂₁ ∘ Φ = Φ ∘ ∂₀`. -/
theorem signedMorseBoundary_comp_signedPairMap_zmod_two {𝔬₀ : MorseOrientation f₀ X₀}
    {𝔬₁ : MorseOrientation f₁ X₁} :
    hX₁.signedMorseBoundary 𝔬₁ hf₁ (ZMod 2) ∘ₗ hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ (ZMod 2) =
      hX₀.signedPairMap hX₁ 𝔬₀ 𝔬₁ hf₁ (ZMod 2) ∘ₗ hX₀.signedMorseBoundary 𝔬₀ hf₀ (ZMod 2) := by
  refine (h.signedMorseBoundary_comp_signedPairMap_eq_iff h₀ h₁ hf₀ hf₁).2 fun p r ↦ ?_
  -- Modulo two, the signed counts are the numbers of broken configurations, whose sum is even.
  rw [h.intCast_finsum_mem_targetBrokenPairSign h₀ h₁ hf₀ hf₁,
    h.intCast_finsum_mem_sourceBrokenPairSign h₀ h₁ hf₀ hf₁, ← CharTwo.add_eq_zero,
    ← Nat.cast_add, add_comm, ZMod.natCast_eq_zero_iff_even]
  exact h.even_ncard_morseSourceBrokenPairSet_add_ncard_morseTargetBrokenPairSet h₀ h₁ hf₀ hf₁ p r

end IsMorseSmalePair

end Pair

end IsAdaptedPseudoGradient

end TauCeti

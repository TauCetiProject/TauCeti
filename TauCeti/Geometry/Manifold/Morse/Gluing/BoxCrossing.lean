/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Passage

/-!
# Orbits near a broken trajectory cross a Morse box once

Let `x` be a critical point of a Morse function `f` on a compact boundaryless manifold, and `X` a
pseudo-gradient adapted to `f`, linear in a Morse chart `φ` at `x`. In the split coordinates
`(u, v)` of `φ` (contracting and expanding), the flow of `X` on the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` is the
split hyperbolic flow, and the model passage map `TauCeti.splitPassage` sends a point of the
entrance face `‖u‖ = ε` off the stable plane to the point where its orbit leaves the box. This file
shows that the passage map describes the actual crossing of trajectories near a broken one.

In the Morse chart `f = f x + (Σᵢ uᵢ² - Σⱼ vⱼ²) / 2`. Hence `f` exceeds `f x` on the entrance face
near the stable plane `v = 0` and is below `f x` on the exit face near the unstable plane `u = 0`
(`TauCeti.MorseChart.lt_apply_of_norm_fst_eq` and `TauCeti.MorseChart.apply_lt_of_norm_snd_eq`).
Since `f` strictly decreases along non-stationary orbits, an orbit that enters the box near the
stable plane, and so leaves it near the unstable plane, cannot enter it there again: an orbit meets
the part of the entrance face near the stable plane at most once. So if a point `w₁` near the
entrance face and a point `w₂` of its orbit near the exit face both pass close to `x`, the passage
map sends the model entrance point of `w₁` to the model exit point of `w₂`. This is the step that
identifies, near a broken trajectory, the trajectories of `X` with the pairs of the model gluing
theorem `TauCeti.exists_homeomorph_closure_splitGluingPairs`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_norm_fst_eq`: an orbit meets the entrance face
  near the stable plane at most once.
* `TauCeti.IsAdaptedPseudoGradient.splitPassage_splitEntryTime_eq_splitExitTime`: the passage map
  sends the model entrance point of a trajectory near a broken one to its model exit point.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing of broken trajectories, using a pseudo-gradient that is linear near the
  critical points).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {x : M}

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- An orbit through the entrance face of a Morse box near the stable plane does not meet the
entrance face near the stable plane again at a positive time: while it stays in the box its
contracting coordinate has norm less than `ε`, and once it has left the box `f` is below `f x`. -/
private theorem flow_ne_of_norm_fst_eq (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z z' : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : ‖z.fst‖ = ε) (hzs : ‖z.snd‖ ≤ ε) (hz' : ‖z'.fst‖ = ε) (hz's : ‖z'.snd‖ ≤ ε)
    (hzn : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2)
    (hzn' : Module.finrank ℝ E * ‖z'.snd‖ ^ 2 < ε ^ 2)
    (hanti : StrictAnti fun t ↦ f (hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))))
    {t : ℝ} (ht₀ : 0 < t) :
    hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) ≠
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z')) := by
  intro h
  have hε₀ : 0 < ε := by
    rcases (hz ▸ norm_nonneg z.fst : 0 ≤ ε).eq_or_lt with h0 | h0
    · rw [← h0] at hzn'
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E)) (sq_nonneg ‖z'.snd‖)]
    · exact h0
  have hmem' : φ.coord.symm (φ.splitCoord.symm z') ∈ φ.toChart.target :=
    MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε hz'.le hz's
  -- While the model orbit of `z` stays in the box, the flow reads it, but at the time `t > 0` its
  -- contracting coordinate has norm `e^{-t} ε < ε`.
  have hbox_ne : (∀ s ∈ uIcc 0 t,
      ‖(splitQuadraticFlow s z).fst‖ ≤ ε ∧ ‖(splitQuadraticFlow s z).snd‖ ≤ ε) → False := by
    intro hbox
    rw [hX.flow_toChart_symm_splitCoord_symm φ hφ hε hbox] at h
    obtain ⟨h₁, h₂⟩ := hbox t right_mem_uIcc
    have hzz := φ.injOn_toChart_symm_coord_symm_splitCoord_symm
      (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε h₁ h₂) hmem' h
    have hnorm := congrArg (fun w ↦ ‖w.fst‖) hzz
    simp only [norm_fst_splitQuadraticFlow, hz, hz'] at hnorm
    have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    nlinarith
  by_cases hs : z.snd = 0
  · -- On the stable plane the model orbit stays in the box.
    refine hbox_ne fun s hs' ↦ norm_fst_le_and_norm_snd_le_splitQuadraticFlow hz.le
      (by rw [norm_snd_splitQuadraticFlow, hs, norm_zero, mul_zero]; exact hε₀.le)
      (by rwa [uIcc_of_le ht₀.le] at hs')
  have hsrc : z ∈ (splitPassage ε).source := mem_splitPassage_source.2 ⟨hz, hs, hzs⟩
  by_cases htT : t ≤ splitExitTime ε z
  · refine hbox_ne fun s hs' ↦ ?_
    rw [uIcc_of_le ht₀.le] at hs'
    exact (norm_fst_le_and_norm_snd_le_iff_of_mem_splitPassage_source hsrc).2
      ⟨hs'.1, hs'.2.trans htT⟩
  · -- After leaving the box the orbit is below `f x`, while `f` exceeds `f x` at `z'`.
    have htgt := mem_splitPassage_target.1 ((splitPassage ε).map_source hsrc)
    have hout : f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitPassage ε z)))) <
        f x :=
      MorseChart.apply_lt_of_norm_snd_eq
        (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε htgt.2.2 htgt.1.le)
        htgt.1 (by rwa [norm_fst_splitPassage hsrc])
    have hin : f x < f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z'))) :=
      MorseChart.lt_apply_of_norm_fst_eq hmem' hz' hzn'
    have hlt := hanti (not_le.1 htT)
    simp only [h, hX.flow_splitExitTime φ hφ hε hsrc] at hlt
    linarith

/-- **An orbit meets the entrance face of a Morse box near the stable plane at most once.** Let
`X` be linear in the Morse chart `φ` at `x`, whose coordinate cube of radius `ε` lies in the
chart. Two points `z`, `z'` of the entrance face `‖u‖ = ε, ‖v‖ ≤ ε` whose expanding coordinates
are small enough that `f` exceeds `f x` there, and which lie on one orbit along which `f` strictly
decreases, are equal. The points may lie on the stable plane `v = 0`. -/
theorem eq_of_flow_eq_of_norm_fst_eq (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z z' : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : ‖z.fst‖ = ε) (hzs : ‖z.snd‖ ≤ ε) (hz' : ‖z'.fst‖ = ε) (hz's : ‖z'.snd‖ ≤ ε)
    (hzn : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2)
    (hzn' : Module.finrank ℝ E * ‖z'.snd‖ ^ 2 < ε ^ 2)
    (hanti : StrictAnti fun t ↦ f (hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))))
    {t : ℝ} (ht : hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z'))) :
    z = z' := by
  rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
  · -- Run the orbit backwards from `z'`.
    have ht' : hX.flow (-t) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z'))) =
        φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) := by
      rw [← ht, Flow.map_neg_apply_map]
    have hanti' : StrictAnti fun s ↦
        f (hX.flow s (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z')))) := fun a b hab ↦ by
      simpa only [← ht, ← Flow.map_add] using hanti (by linarith : a + t < b + t)
    exact absurd ht' (flow_ne_of_norm_fst_eq hX φ hφ hε hz' hz's hz hzs hzn' hzn hanti'
      (neg_pos.2 ht₀))
  · rw [Flow.map_zero_apply] at ht
    exact φ.injOn_toChart_symm_coord_symm_splitCoord_symm
      (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε hz.le hzs)
      (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε hz'.le hz's) ht
  · exact absurd ht (flow_ne_of_norm_fst_eq hX φ hφ hε hz hzs hz' hz's hzn hzn' hanti ht₀)


/-- **A trajectory near a broken one crosses the Morse box once.** Let `X` be linear in the Morse
chart `φ` at `x`, whose coordinate cube of radius `2 ε` lies in the chart. Let `w₁` be a point near
the entrance face, off the stable set of the model, and `w₂` a point of its orbit near the exit
face, off the unstable set of the model, such that both model orbits pass close to `x`. Then the
model entrance point of `w₁` lies on the entrance face off the stable set, and the passage map
sends it to the model exit point of `w₂`. -/
theorem splitPassage_splitEntryTime_eq_splitExitTime (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {w₁ w₂ : M} (hw₁ : w₁ ∈ φ.toChart.source)
    (hw₁f : (φ.splitCoord (φ.coord (φ.toChart w₁))).fst ≠ 0)
    (hw₁f' : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ < 2 * ε)
    (hw₁s : (φ.splitCoord (φ.coord (φ.toChart w₁))).snd ≠ 0)
    (hw₁s' : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ < ε)
    (hw₂ : w₂ ∈ φ.toChart.source)
    (hw₂s : (φ.splitCoord (φ.coord (φ.toChart w₂))).snd ≠ 0)
    (hw₂s' : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ < 2 * ε)
    (hw₂f : (φ.splitCoord (φ.coord (φ.toChart w₂))).fst ≠ 0)
    (hw₂f' : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ < ε)
    (hκ₁ : ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ / ε ≤ ε)
    (hn₁ : Module.finrank ℝ E * (‖(φ.splitCoord (φ.coord (φ.toChart w₁))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₁))).snd‖ / ε) ^ 2 < ε ^ 2)
    (hκ₂ : ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ / ε ≤ ε)
    (hn₂ : Module.finrank ℝ E * (‖(φ.splitCoord (φ.coord (φ.toChart w₂))).fst‖ *
      ‖(φ.splitCoord (φ.coord (φ.toChart w₂))).snd‖ / ε) ^ 2 < ε ^ 2)
    (hanti : StrictAnti fun t ↦ f (hX.flow t w₁)) {t : ℝ} (ht : hX.flow t w₁ = w₂) :
    splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁))) ∈ (splitPassage ε).source ∧
      splitPassage ε (splitQuadraticFlow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w₁))))
        (φ.splitCoord (φ.coord (φ.toChart w₁)))) =
      splitQuadraticFlow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w₂))))
        (φ.splitCoord (φ.coord (φ.toChart w₂))) := by
  set z₁ := φ.splitCoord (φ.coord (φ.toChart w₁))
  set z₂ := φ.splitCoord (φ.coord (φ.toChart w₂))
  set E₁ := splitQuadraticFlow (splitEntryTime ε z₁) z₁
  set Q := splitQuadraticFlow (splitExitTime ε z₂) z₂
  have hε₁ : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target := fun z hz ↦ hε₂ z (by linarith)
  have hEsnd : ‖E₁.snd‖ = ‖z₁.fst‖ * ‖z₁.snd‖ / ε :=
    norm_snd_splitQuadraticFlow_splitEntryTime hε hw₁f
  have hQfst : ‖Q.fst‖ = ‖z₂.fst‖ * ‖z₂.snd‖ / ε :=
    norm_fst_splitQuadraticFlow_splitExitTime hε hw₂s
  have hE : E₁ ∈ (splitPassage ε).source := by
    refine mem_splitPassage_source.2 ⟨norm_fst_splitQuadraticFlow_splitEntryTime hε hw₁f, ?_,
      hEsnd ▸ hκ₁⟩
    rw [← norm_pos_iff, hEsnd]
    have := norm_pos_iff.2 hw₁f
    have := norm_pos_iff.2 hw₁s
    positivity
  have hQ : Q ∈ (splitPassage ε).target := by
    refine mem_splitPassage_target.2 ⟨norm_snd_splitQuadraticFlow_splitExitTime hε hw₂s, ?_,
      hQfst ▸ hκ₂⟩
    rw [← norm_pos_iff, hQfst]
    have := norm_pos_iff.2 hw₂f
    have := norm_pos_iff.2 hw₂s
    positivity
  -- Both model points lie on the orbit of `w₁`, so the orbit crossing the box is unique.
  have hΨE : φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm E₁)) =
      hX.flow (splitEntryTime ε z₁) w₁ :=
    (hX.flow_splitEntryTime_of_norm_lt φ hφ hε hε₂ hw₁ hw₁f' hw₁s').symm
  have hΨQ : φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm Q)) =
      hX.flow (splitExitTime ε z₂) w₂ :=
    (hX.flow_splitExitTime_of_norm_lt φ hφ hε hε₂ hw₂ hw₂f' hw₂s').symm
  have hantiE : StrictAnti fun s ↦ f (hX.flow s
      (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm E₁)))) := fun a b hab ↦ by
    simpa only [hΨE, ← Flow.map_add] using
      hanti (by linarith : a + splitEntryTime ε z₁ < b + splitEntryTime ε z₁)
  have horb : hX.flow (splitEntryTime ε Q + splitExitTime ε z₂ + t - splitEntryTime ε z₁)
      (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm E₁))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm ((splitPassage ε).symm Q))) := by
    rw [← hX.flow_splitEntryTime φ hφ hε₁ hQ, hΨQ, hΨE, ← ht]
    simp only [← Flow.map_add]
    congr 1
    ring
  have hE' := mem_splitPassage_source.1 ((splitPassage ε).map_target hQ)
  have hEz : E₁ = (splitPassage ε).symm Q :=
    hX.eq_of_flow_eq_of_norm_fst_eq φ hφ hε₁ (mem_splitPassage_source.1 hE).1
      (mem_splitPassage_source.1 hE).2.2 hE'.1 hE'.2.2 (by rwa [hEsnd])
      (by rwa [norm_snd_splitPassage_symm hQ, hQfst]) hantiE horb
  exact ⟨hE, by rw [hEz, (splitPassage ε).right_inv hQ]⟩

end IsAdaptedPseudoGradient

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Passage
import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Orbits near a broken trajectory cross a Morse box once

Let `x` be a critical point of a Morse function `f` on a compact boundaryless manifold, and `X` a
pseudo-gradient adapted to `f`, linear in a Morse chart `φ` at `x`. In the split coordinates
`(u, v)` of `φ` (contracting and expanding), the flow of `X` on the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` is the
split hyperbolic flow, and the model passage map `TauCeti.splitPassage` sends a point of the
entrance face `‖u‖ = ε` off the stable plane to the point where its orbit leaves the box. This file
shows that the passage map describes the actual crossing of trajectories near a broken one.

In the Morse chart `f = f x + (Σᵢ uᵢ² - Σⱼ vⱼ²) / 2`. Hence `f` exceeds `f x` on the entrance
face near the stable plane `v = 0` and is below `f x` on the exit face near the unstable plane
`u = 0`. Since `f` strictly decreases along non-stationary orbits, an orbit that enters the box
near the stable plane, and so leaves it near the unstable plane, cannot enter it there again:
an orbit meets the part of the entrance face near the stable plane at most once. So if a point
`w₁` near the entrance face and a point `w₂` of its orbit near the exit face both pass close to
`x`, the passage map sends the model entrance point of `w₁` to the model exit point of `w₂`. This
is the step that identifies, near a broken trajectory, the trajectories of `X` with the pairs of
the model gluing theorem `TauCeti.exists_homeomorph_closure_splitGluingPairs`.

## Main results

* `TauCeti.MorseChart.apply_toChart_symm_coord_symm_splitCoord_symm`: the Morse normal form in
  split coordinates.
* `TauCeti.MorseChart.lt_apply_of_norm_fst_eq`, `TauCeti.MorseChart.apply_lt_of_norm_snd_eq`: `f`
  is above `f x` on the entrance face near the stable plane and below it on the exit face near the
  unstable plane.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitEntryTime_of_norm_lt` and
  `TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime_of_norm_lt`: near the entrance and exit
  faces, the flow at the model entry and exit times is the split hyperbolic flow.
* `TauCeti.IsAdaptedPseudoGradient.eq_of_flow_eq_of_mem_splitPassage_source`: an orbit meets the
  entrance face near the stable plane at most once.
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

namespace MorseChart

variable (φ : MorseChart E f x)

/-- **The Morse normal form in split coordinates.** At the point with split coordinates `(u, v)`,
`f = f x + (Σᵢ uᵢ² - Σⱼ vⱼ²) / 2`. -/
theorem apply_toChart_symm_coord_symm_splitCoord_symm
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) :
    f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) =
      f x + 2⁻¹ * (∑ i, z.fst i ^ 2 - ∑ i, z.snd i ^ 2) := by
  rw [φ.eq_quadratic _ (φ.toChart.map_target hz), φ.toChart.right_inv hz,
    LinearEquiv.apply_symm_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun i ↦ φ.weight i = 1), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 2
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [i.2]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [(φ.weight_eq_neg_one_or_eq_one i).resolve_right i.2]
    norm_num


variable {φ}

/-- On the box, the split coordinates read a point of the chart. -/
theorem coord_symm_splitCoord_symm_mem_target_of_norm_le {ε : ℝ}
    (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hfst : ‖z.fst‖ ≤ ε) (hsnd : ‖z.snd‖ ≤ ε) :
    φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target :=
  hε _ <| by
    rw [← φ.max_norm_fst_norm_snd_splitCoord, LinearEquiv.apply_symm_apply]
    exact max_le hfst hsnd

variable (φ) in
/-- The point with given split coordinates determines them. -/
theorem injOn_toChart_symm_coord_symm_splitCoord_symm :
    InjOn (fun z ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))
      {z | φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target} := fun z hz z' hz' h ↦
  φ.splitCoord.symm.injective (φ.coord.symm.injective
    (φ.toChart.symm.injOn (by simpa using hz) (by simpa using hz') h))

/-- **Above the critical value on the entrance face.** At a point of the chart whose contracting
split coordinate has norm `ε` and whose expanding one is small, `f` exceeds `f x`. -/
theorem lt_apply_of_norm_fst_eq {ε : ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) (hfst : ‖z.fst‖ = ε)
    (hsnd : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2) :
    f x < f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) := by
  rw [φ.apply_toChart_symm_coord_symm_splitCoord_symm hz]
  -- Compare the sup norms of the split coordinates with their `L²` norms.
  have h₁ : ‖z.fst‖ ^ 2 ≤ ∑ i, z.fst i ^ 2 := by
    have h := PiLp.dist_ofLp_le (WithLp.toLp 2 z.fst) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have h₂ : ∑ i, z.snd i ^ 2 ≤ Fintype.card {i // ¬φ.weight i = 1} * ‖z.snd‖ ^ 2 := by
    have h := PiLp.dist_le_sqrt_card_mul_dist_ofLp (WithLp.toLp 2 z.snd) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcard : (Fintype.card {i // ¬φ.weight i = 1} : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le
  rw [hfst] at h₁
  nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg ‖z.snd‖)]

/-- **Below the critical value on the exit face.** At a point of the chart whose expanding split
coordinate has norm `ε` and whose contracting one is small, `f` is less than `f x`. -/
theorem apply_lt_of_norm_snd_eq {ε : ℝ}
    {z : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : φ.coord.symm (φ.splitCoord.symm z) ∈ φ.toChart.target) (hsnd : ‖z.snd‖ = ε)
    (hfst : Module.finrank ℝ E * ‖z.fst‖ ^ 2 < ε ^ 2) :
    f (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) < f x := by
  rw [φ.apply_toChart_symm_coord_symm_splitCoord_symm hz]
  -- Compare the sup norms of the split coordinates with their `L²` norms.
  have h₁ : ‖z.snd‖ ^ 2 ≤ ∑ i, z.snd i ^ 2 := by
    have h := PiLp.dist_ofLp_le (WithLp.toLp 2 z.snd) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have h₂ : ∑ i, z.fst i ^ 2 ≤ Fintype.card {i // φ.weight i = 1} * ‖z.fst‖ ^ 2 := by
    have h := PiLp.dist_le_sqrt_card_mul_dist_ofLp (WithLp.toLp 2 z.fst) 0
    rw [dist_zero_right, WithLp.ofLp_toLp, WithLp.ofLp_zero, dist_zero_right] at h
    simpa [PiLp.norm_sq_eq_of_L2, mul_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hcard : (Fintype.card {i // φ.weight i = 1} : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast (Fintype.card_subtype_le _).trans (Fintype.card_fin _).le
  rw [hsnd] at h₁
  nlinarith [mul_le_mul_of_nonneg_right hcard (sq_nonneg ‖z.fst‖)]

end MorseChart

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Entering the Morse box.** Let `X` be linear in the Morse chart `φ`, whose coordinate cube of
radius `2 ε` lies in the chart. Near the entrance face, at a point `w` whose contracting split
coordinate has norm less than `2 ε` and whose expanding one has norm less than `ε`, the flow of `X`
at the model entry time is the split hyperbolic flow. -/
theorem flow_splitEntryTime_of_norm_lt (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {w : M} (hw : w ∈ φ.toChart.source)
    (hfst : ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < 2 * ε)
    (hsnd : ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < ε) :
    hX.flow (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w)))) w =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitQuadraticFlow
        (splitEntryTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
        (φ.splitCoord (φ.coord (φ.toChart w)))))) := by
  set z := φ.splitCoord (φ.coord (φ.toChart w))
  have hwz : φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) = w := by
    rw [LinearEquiv.symm_apply_apply, φ.toChart_symm_coord_symm_coord hw]
  conv_lhs => rw [← hwz]
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε₂ fun s hs ↦ ?_
  -- Bound `exp s` and `exp (-s)` on the time interval between `0` and `t`.
  have hs₁ := (Real.exp_monotone.image_uIcc_subset (mem_image_of_mem _ hs)).2
  have hs₂ := ((Real.exp_monotone.comp_antitone fun _ _ h ↦ neg_le_neg h).image_uIcc_subset
    (mem_image_of_mem _ hs)).2
  simp only [comp_apply, neg_zero, Real.exp_zero] at hs₁ hs₂
  rw [norm_fst_splitQuadraticFlow, norm_snd_splitQuadraticFlow]
  rcases (norm_nonneg z.fst).eq_or_lt with h0 | h0
  · have : s = 0 := by simpa [splitEntryTime_def, ← h0] using hs
    subst this
    simp only [neg_zero, Real.exp_zero, one_mul]
    constructor <;> linarith
  have hexp : Real.exp (splitEntryTime ε z) = ‖z.fst‖ / ε := by
    rw [splitEntryTime_def]; exact Real.exp_log (by positivity)
  rw [hexp] at hs₁
  rw [Real.exp_neg (splitEntryTime ε z), hexp, inv_div] at hs₂
  constructor
  · calc Real.exp (-s) * ‖z.fst‖ ≤ max 1 (ε / ‖z.fst‖) * ‖z.fst‖ := by gcongr
      _ ≤ 2 * ε := by
        rcases le_total 1 (ε / ‖z.fst‖) with h | h
        · rw [max_eq_right h, div_mul_cancel₀ _ h0.ne']; linarith
        · rw [max_eq_left h]; linarith
  · calc Real.exp s * ‖z.snd‖ ≤ max 1 (‖z.fst‖ / ε) * ‖z.snd‖ := by gcongr
      _ ≤ 2 * ε := by
        have : max 1 (‖z.fst‖ / ε) ≤ 2 :=
          max_le one_le_two ((div_le_iff₀ hε).2 (by linarith))
        nlinarith [norm_nonneg z.snd]


/-- **Leaving the Morse box.** Let `X` be linear in the Morse chart `φ`, whose coordinate cube of
radius `2 ε` lies in the chart. Near the exit face, at a point `w` whose expanding split
coordinate has norm less than `2 ε` and whose contracting one has norm less than `ε`, the flow of
`X` at the model exit time is the split hyperbolic flow. -/
theorem flow_splitExitTime_of_norm_lt (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : 0 < ε) (hε₂ : ∀ z, ‖z‖ ≤ 2 * ε → φ.coord.symm z ∈ φ.toChart.target)
    {w : M} (hw : w ∈ φ.toChart.source)
    (hfst : ‖(φ.splitCoord (φ.coord (φ.toChart w))).fst‖ < ε)
    (hsnd : ‖(φ.splitCoord (φ.coord (φ.toChart w))).snd‖ < 2 * ε) :
    hX.flow (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w)))) w =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitQuadraticFlow
        (splitExitTime ε (φ.splitCoord (φ.coord (φ.toChart w))))
        (φ.splitCoord (φ.coord (φ.toChart w)))))) := by
  set z := φ.splitCoord (φ.coord (φ.toChart w))
  have hwz : φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)) = w := by
    rw [LinearEquiv.symm_apply_apply, φ.toChart_symm_coord_symm_coord hw]
  conv_lhs => rw [← hwz]
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε₂ fun s hs ↦ ?_
  -- Bound `exp s` and `exp (-s)` on the time interval between `0` and `t`.
  have hs₁ := (Real.exp_monotone.image_uIcc_subset (mem_image_of_mem _ hs)).2
  have hs₂ := ((Real.exp_monotone.comp_antitone fun _ _ h ↦ neg_le_neg h).image_uIcc_subset
    (mem_image_of_mem _ hs)).2
  simp only [comp_apply, neg_zero, Real.exp_zero] at hs₁ hs₂
  rw [norm_fst_splitQuadraticFlow, norm_snd_splitQuadraticFlow]
  rcases (norm_nonneg z.snd).eq_or_lt with h0 | h0
  · have : s = 0 := by simpa [splitExitTime_def, ← h0] using hs
    subst this
    simp only [neg_zero, Real.exp_zero, one_mul]
    constructor <;> linarith
  have hexp : Real.exp (splitExitTime ε z) = ε / ‖z.snd‖ := by
    rw [splitExitTime_def]; exact Real.exp_log (by positivity)
  rw [hexp] at hs₁
  rw [Real.exp_neg (splitExitTime ε z), hexp, inv_div] at hs₂
  constructor
  · calc Real.exp (-s) * ‖z.fst‖ ≤ max 1 (‖z.snd‖ / ε) * ‖z.fst‖ := by gcongr
      _ ≤ 2 * ε := by
        have : max 1 (‖z.snd‖ / ε) ≤ 2 :=
          max_le one_le_two ((div_le_iff₀ hε).2 (by linarith))
        nlinarith [norm_nonneg z.fst]
  · calc Real.exp s * ‖z.snd‖ ≤ max 1 (ε / ‖z.snd‖) * ‖z.snd‖ := by gcongr
      _ ≤ 2 * ε := by
        rcases le_total 1 (ε / ‖z.snd‖) with h | h
        · rw [max_eq_right h, div_mul_cancel₀ _ h0.ne']; linarith
        · rw [max_eq_left h]; linarith

/-- An orbit through the entrance face of a Morse box does not meet the entrance face again
before it leaves the box. -/
private theorem flow_ne_of_mem_splitPassage_source (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z z' : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ (splitPassage ε).source) (hz' : z' ∈ (splitPassage ε).source) {t : ℝ}
    (ht₀ : 0 < t) (htT : t ≤ splitExitTime ε z) :
    hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) ≠
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z')) := by
  intro h
  have hbox : ∀ s ∈ uIcc 0 t,
      ‖(splitQuadraticFlow s z).fst‖ ≤ ε ∧ ‖(splitQuadraticFlow s z).snd‖ ≤ ε := fun s hs ↦ by
    rw [uIcc_of_le ht₀.le] at hs
    exact (norm_fst_le_and_norm_snd_le_iff_of_mem_splitPassage_source hz).2
      ⟨hs.1, hs.2.trans htT⟩
  rw [hX.flow_toChart_symm_splitCoord_symm φ hφ hε hbox] at h
  obtain ⟨h₁, h₂⟩ := hbox t (right_mem_uIcc)
  have hzz := φ.injOn_toChart_symm_coord_symm_splitCoord_symm
    (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε h₁ h₂)
    (MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε
      (mem_splitPassage_source.1 hz').1.le (mem_splitPassage_source.1 hz').2.2) h
  have hnorm := congrArg (fun w ↦ ‖w.fst‖) hzz
  simp only [norm_fst_splitQuadraticFlow, (mem_splitPassage_source.1 hz).1,
    (mem_splitPassage_source.1 hz').1] at hnorm
  have hε0 := pos_of_mem_splitPassage_source hz
  have : Real.exp (-t) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  nlinarith

/-- **An orbit crosses a Morse box at most once near the broken trajectories.** Let `X` be linear
in the Morse chart `φ` at `x`, whose coordinate cube of radius `ε` lies in the chart. Two points
`z`, `z'` of the entrance face whose expanding coordinates are small enough that `f` exceeds `f x`
there and is less than `f x` where their orbits leave the box, and which lie on one orbit along
which `f` strictly decreases, are equal. -/
theorem eq_of_flow_eq_of_mem_splitPassage_source (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {z z' : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hz : z ∈ (splitPassage ε).source) (hz' : z' ∈ (splitPassage ε).source)
    (hzs : Module.finrank ℝ E * ‖z.snd‖ ^ 2 < ε ^ 2)
    (hzs' : Module.finrank ℝ E * ‖z'.snd‖ ^ 2 < ε ^ 2)
    (hanti : StrictAnti fun t ↦ f (hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z)))))
    {t : ℝ} (ht : hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm z'))) :
    z = z' := by
  set Ψ := fun w ↦ φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm w))
  have hmem : ∀ w ∈ (splitPassage ε).source,
      φ.coord.symm (φ.splitCoord.symm w) ∈ φ.toChart.target := fun w hw ↦
    MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε
      (mem_splitPassage_source.1 hw).1.le (mem_splitPassage_source.1 hw).2.2
  have hmem' : ∀ w ∈ (splitPassage ε).source,
      φ.coord.symm (φ.splitCoord.symm (splitPassage ε w)) ∈ φ.toChart.target := fun w hw ↦
    have h := (splitPassage ε).map_source hw
    MorseChart.coord_symm_splitCoord_symm_mem_target_of_norm_le hε
      (mem_splitPassage_target.1 h).2.2 (mem_splitPassage_target.1 h).1.le
  -- `f` is above `f x` at the entrance points and below it at the exit points.
  have hin : ∀ w ∈ (splitPassage ε).source, Module.finrank ℝ E * ‖w.snd‖ ^ 2 < ε ^ 2 →
      f x < f (Ψ w) := fun w hw hws ↦
    MorseChart.lt_apply_of_norm_fst_eq (hmem w hw) (mem_splitPassage_source.1 hw).1 hws
  have hout : ∀ w ∈ (splitPassage ε).source, Module.finrank ℝ E * ‖w.snd‖ ^ 2 < ε ^ 2 →
      f (Ψ (splitPassage ε w)) < f x := fun w hw hws ↦
    MorseChart.apply_lt_of_norm_snd_eq (hmem' w hw)
      (mem_splitPassage_target.1 ((splitPassage ε).map_source hw)).1
      (by rwa [norm_fst_splitPassage hw])
  have hpass : ∀ w ∈ (splitPassage ε).source,
      hX.flow (splitExitTime ε w) (Ψ w) = Ψ (splitPassage ε w) := fun w hw ↦
    hX.flow_splitExitTime φ hφ (fun z hz ↦ hε z hz) hw
  -- The orbit meets `z'` before it leaves the box through the exit point of `z`, and conversely.
  have h₁ : t < splitExitTime ε z := by
    refine hanti.lt_iff_gt.1 ?_
    rw [ht, hpass z hz]
    exact (hout z hz hzs).trans (hin z' hz' hzs')
  have h₂ : -t < splitExitTime ε z' := by
    have h : hX.flow (splitExitTime ε z' + t) (Ψ z) = Ψ (splitPassage ε z') := by
      rw [Flow.map_add, ht, hpass z' hz']
    have : 0 < splitExitTime ε z' + t := by
      refine hanti.lt_iff_gt.1 ?_
      rw [h, Flow.map_zero_apply]
      exact (hout z' hz' hzs').trans (hin z hz hzs)
    linarith
  rcases lt_trichotomy t 0 with ht₀ | rfl | ht₀
  · refine absurd ?_ (flow_ne_of_mem_splitPassage_source hX φ hφ hε hz' hz (neg_pos.2 ht₀) h₂.le)
    rw [← ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
  · rw [Flow.map_zero_apply] at ht
    exact φ.injOn_toChart_symm_coord_symm_splitCoord_symm (hmem z hz) (hmem z' hz') ht
  · exact absurd ht (flow_ne_of_mem_splitPassage_source hX φ hφ hε hz hz' ht₀ h₁.le)


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
  have hEz : E₁ = (splitPassage ε).symm Q :=
    hX.eq_of_flow_eq_of_mem_splitPassage_source φ hφ hε₁ hE ((splitPassage ε).map_target hQ)
      (by rwa [hEsnd]) (by rwa [norm_snd_splitPassage_symm hQ, hQfst]) hantiE horb
  exact ⟨hE, by rw [hEz, (splitPassage ε).right_inv hQ]⟩

end IsAdaptedPseudoGradient

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local

/-!
# The passage of an adapted pseudo-gradient through a Morse box

Near a critical point `x` of `f`, an adapted pseudo-gradient `X` reads in a Morse chart `φ` as the
linear field `z ↦ (-wᵢ zᵢ)ᵢ` with weights `wᵢ = ±1`. Splitting the coordinates into those of
positive weight, on which the linear flow contracts, and those of negative weight, on which it
expands (`TauCeti.MorseChart.splitCoord`), turns the linear flow into the split hyperbolic flow
`φ t (u, v) = (e^{-t} u, e^t v)` (`TauCeti.splitQuadraticFlow`). Each factor carries the sup norm,
so the coordinate cube `‖z‖ ≤ ε` is the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of
`TauCeti.Analysis.Calculus.Morse.Passage`.

When the box lies in the chart, the flow of `X` is the split hyperbolic flow for as long as the
model orbit stays in the box. In particular, at the model exit time, the flow carries a point of
the entrance face `‖u‖ = ε` off the stable set to the point of the exit face `‖v‖ = ε` given by the
model passage map `TauCeti.splitPassage`. This identification is what lets
the local analysis of broken and glued trajectories in the split model (breaking, the linear
λ-lemma, and the gluing of transverse discs in `TauCeti.Analysis.Calculus.Morse.Gluing.Basic`) be
applied to the flow of an adapted pseudo-gradient on a compact manifold.

## Main declarations

* `TauCeti.MorseChart.splitCoord_linearFlow`: the split coordinates conjugate the linear flow to
  the split hyperbolic flow.
* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_splitCoord_symm`: while the model orbit stays
  in a box contained in the chart, the flow of `X` is the split hyperbolic flow.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime`: the flow carries a point of the entrance
  face to its image under the passage map, at the exit time.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitEntryTime`: backward in time, the flow carries a point
  of the exit face to its image under the inverse passage map, at the entry time.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitEntryTime_of_norm_lt` and
  `TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime_of_norm_lt`: near the entrance and exit
  faces, the flow at the model entry and exit times is the split hyperbolic flow.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness and gluing of trajectories, using a pseudo-gradient that is linear near
  the critical points).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ : MorseChart E f x)

/-- **The split coordinates conjugate the linear flow to the split hyperbolic flow.** -/
theorem splitCoord_linearFlow (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.splitCoord (φ.linearFlow t z) = splitQuadraticFlow t (φ.splitCoord z) := by
  apply WithLp.ofLp_injective
  ext i
  · simp [splitQuadraticFlow_apply, i.2]
  · simp [splitQuadraticFlow_apply, (φ.weight_eq_neg_one_or_eq_one i).resolve_right i.2]

end MorseChart

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- **In a Morse box the flow is the split hyperbolic flow.** Let `X` be the linear field
`z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart `φ`, and let the coordinate cube of radius `ε` lie in the chart.
If the split hyperbolic orbit of `w` stays in the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` for all times between `0`
and `t`, then at time `t` the flow of `X` from the point with split coordinates `w` is the point
with split coordinates `(e^{-t} u, e^t v)`. -/
theorem flow_toChart_symm_splitCoord_symm (hX : IsAdaptedPseudoGradient f X)
    (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))} {t : ℝ}
    (hw : ∀ s ∈ uIcc 0 t,
      ‖(splitQuadraticFlow s w).fst‖ ≤ ε ∧ ‖(splitQuadraticFlow s w).snd‖ ≤ ε) :
    hX.flow t (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm w))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitQuadraticFlow t w))) := by
  have hlin (s : ℝ) :
      φ.linearFlow s (φ.splitCoord.symm w) = φ.splitCoord.symm (splitQuadraticFlow s w) := by
    rw [LinearEquiv.eq_symm_apply, φ.splitCoord_linearFlow, LinearEquiv.apply_symm_apply]
  rw [← hlin]
  refine hX.flow_toChart_symm_of_forall_mem_uIcc φ hφ fun s hs ↦ hε _ ?_
  rw [hlin, ← φ.max_norm_fst_norm_snd_splitCoord, LinearEquiv.apply_symm_apply, max_le_iff]
  exact hw s hs

/-- **Passage through a Morse box.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the Morse chart
`φ`, and let the coordinate cube of radius `ε` lie in the chart. At the exit time
`TauCeti.splitExitTime`, the flow of `X` carries a point of the entrance face
`‖u‖ = ε, 0 < ‖v‖ ≤ ε` to its image under the passage map `TauCeti.splitPassage`, on the exit
face. -/
theorem flow_splitExitTime (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hw : w ∈ (splitPassage ε).source) :
    hX.flow (splitExitTime ε w) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm w))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm (splitPassage ε w))) := by
  rw [splitPassage_apply]
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε fun s hs ↦ ?_
  obtain ⟨-, hy, hyε⟩ := mem_splitPassage_source.1 hw
  rw [uIcc_of_le (splitExitTime_nonneg hy hyε)] at hs
  exact (norm_fst_le_and_norm_snd_le_iff_of_mem_splitPassage_source hw).2 hs

/-- **Backward passage through a Morse box.** Let `X` be the linear field `z ↦ (-wᵢ zᵢ)ᵢ` in the
Morse chart `φ`, and let the coordinate cube of radius `ε` lie in the chart. At the nonpositive
entry time `TauCeti.splitEntryTime`, the flow of `X` carries a point of the exit face
`‖v‖ = ε, 0 < ‖u‖ ≤ ε` to its image under the inverse passage map, on the entrance face. -/
theorem flow_splitEntryTime (hX : IsAdaptedPseudoGradient f X) (φ : MorseChart E f x)
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {ε : ℝ} (hε : ∀ z, ‖z‖ ≤ ε → φ.coord.symm z ∈ φ.toChart.target)
    {w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ))}
    (hw : w ∈ (splitPassage ε).target) :
    hX.flow (splitEntryTime ε w) (φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm w))) =
      φ.toChart.symm (φ.coord.symm (φ.splitCoord.symm ((splitPassage ε).symm w))) := by
  rw [splitPassage_symm_apply]
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε fun s hs ↦ ?_
  obtain ⟨-, -, hxε⟩ := mem_splitPassage_target.1 hw
  rw [uIcc_of_ge (splitEntryTime_nonpos hxε)] at hs
  exact (norm_fst_le_and_norm_snd_le_iff_of_mem_splitPassage_target hw).2 hs

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
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε₂ fun s hs ↦
    norm_splitQuadraticFlow_le_of_mem_uIcc hs ⟨hfst.le, by linarith⟩ ?_
  -- At the entry time the contracting factor has norm `ε`, and the expanding one has grown by the
  -- factor `‖z.fst‖ / ε < 2`.
  rcases eq_or_ne z.fst 0 with h0 | h0
  · simp only [norm_fst_splitQuadraticFlow, norm_snd_splitQuadraticFlow, splitEntryTime_def, h0,
      norm_zero, zero_div, Real.log_zero, neg_zero, Real.exp_zero, one_mul, mul_zero]
    exact ⟨by linarith, by linarith⟩
  rw [norm_fst_splitQuadraticFlow_splitEntryTime hε h0,
    norm_snd_splitQuadraticFlow_splitEntryTime hε h0, div_le_iff₀ hε]
  exact ⟨by linarith, by nlinarith [norm_nonneg z.fst, norm_nonneg z.snd]⟩

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
  refine hX.flow_toChart_symm_splitCoord_symm φ hφ hε₂ fun s hs ↦
    norm_splitQuadraticFlow_le_of_mem_uIcc hs ⟨by linarith, hsnd.le⟩ ?_
  -- At the exit time the expanding factor has norm `ε`, and the contracting one has shrunk by the
  -- factor `ε / ‖z.snd‖ > 1 / 2`.
  rcases eq_or_ne z.snd 0 with h0 | h0
  · simp only [norm_fst_splitQuadraticFlow, norm_snd_splitQuadraticFlow, splitExitTime_def, h0,
      norm_zero, div_zero, Real.log_zero, neg_zero, Real.exp_zero, one_mul, mul_zero]
    exact ⟨by linarith, by linarith⟩
  rw [norm_fst_splitQuadraticFlow_splitExitTime hε h0,
    norm_snd_splitQuadraticFlow_splitExitTime hε h0, div_le_iff₀ hε]
  exact ⟨by nlinarith [norm_nonneg z.fst, norm_nonneg z.snd], by linarith⟩

end IsAdaptedPseudoGradient

end TauCeti

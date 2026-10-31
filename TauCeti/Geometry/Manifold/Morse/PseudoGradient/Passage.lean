/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Local
public import TauCeti.LinearAlgebra.Pi

/-!
# The passage of an adapted pseudo-gradient through a Morse box

Near a critical point `x` of `f`, an adapted pseudo-gradient `X` reads in a Morse chart `φ` as the
linear field `z ↦ (-wᵢ zᵢ)ᵢ` with weights `wᵢ = ±1`. Splitting the coordinates into those of
positive weight, on which the linear flow contracts, and those of negative weight, on which it
expands, turns the linear flow into the split hyperbolic flow
`φ t (u, v) = (e^{-t} u, e^t v)` (`TauCeti.splitQuadraticFlow`). Each factor carries the sup norm,
so the coordinate cube `‖z‖ ≤ ε` is the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of
`TauCeti.Analysis.Calculus.Morse.Passage`.

When the box lies in the chart, the flow of `X` is the split hyperbolic flow for as long as the
model orbit stays in the box. In particular an orbit entering the box through the entrance face
`‖u‖ = ε` off the stable set leaves it through the exit face `‖v‖ = ε` at the point given by the
model passage map `TauCeti.splitPassage`, at the model exit time. This identification is what lets
the local analysis of broken and glued trajectories in the split model (breaking, the linear
λ-lemma, and the gluing of transverse discs in `TauCeti.Analysis.Calculus.Morse.Gluing.Basic`) be
applied to the flow of an adapted pseudo-gradient on a compact manifold.

## Main declarations

* `TauCeti.MorseChart.splitCoord`: the coordinates of a Morse chart, split by the sign of the
  weight.
* `TauCeti.MorseChart.splitCoord_linearFlow`: the split coordinates conjugate the linear flow to
  the split hyperbolic flow.
* `TauCeti.MorseChart.max_norm_fst_norm_snd_splitCoord`: the sup norm of the coordinates is the
  larger of the norms of the two factors.
* `TauCeti.IsAdaptedPseudoGradient.flow_toChart_symm_splitCoord_symm`: while the model orbit stays
  in a box contained in the chart, the flow of `X` is the split hyperbolic flow.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitExitTime`: the flow carries a point of the entrance
  face to its image under the passage map, at the exit time.
* `TauCeti.IsAdaptedPseudoGradient.flow_splitEntryTime`: backward in time, the flow carries a point
  of the exit face to its image under the inverse passage map, at the entry time.

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

/-- The **split coordinates** of a Morse chart: the pair formed by the coordinates of positive
weight, on which the linear flow contracts, and the remaining coordinates, of weight `-1`, on which
it expands. Each factor carries the sup norm. -/
noncomputable def splitCoord :
    (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ]
      WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)) :=
  (LinearEquiv.piEquivPiSubtypeProd ℝ (fun i ↦ φ.weight i = 1) fun _ ↦ ℝ).trans
    (WithLp.linearEquiv 2 ℝ _).symm

/-- The contracting factor of the split coordinates consists of the coordinates of positive
weight. -/
@[simp]
theorem splitCoord_fst_apply (z : Fin (Module.finrank ℝ E) → ℝ) (i : {i // φ.weight i = 1}) :
    (φ.splitCoord z).fst i = z i := by
  simp [splitCoord]

/-- The expanding factor of the split coordinates consists of the coordinates of negative
weight. -/
@[simp]
theorem splitCoord_snd_apply (z : Fin (Module.finrank ℝ E) → ℝ) (i : {i // ¬φ.weight i = 1}) :
    (φ.splitCoord z).snd i = z i := by
  simp [splitCoord]

/-- The coordinates of a point given in split coordinates. -/
@[simp]
theorem splitCoord_symm_apply
    (w : WithLp 2 (({i // φ.weight i = 1} → ℝ) × ({i // ¬φ.weight i = 1} → ℝ)))
    (i : Fin (Module.finrank ℝ E)) :
    φ.splitCoord.symm w i = if h : φ.weight i = 1 then w.fst ⟨i, h⟩ else w.snd ⟨i, h⟩ := by
  simp [splitCoord]

/-- **The split coordinates conjugate the linear flow to the split hyperbolic flow.** -/
theorem splitCoord_linearFlow (t : ℝ) (z : Fin (Module.finrank ℝ E) → ℝ) :
    φ.splitCoord (φ.linearFlow t z) = splitQuadraticFlow t (φ.splitCoord z) := by
  apply WithLp.ofLp_injective
  ext i
  · simp [splitQuadraticFlow_apply, i.2]
  · simp [splitQuadraticFlow_apply, (φ.weight_eq_neg_one_or_eq_one i).resolve_right i.2]

/-- The sup norm of the coordinates of a Morse chart is the larger of the norms of the two factors
of the split coordinates. So the coordinate cube `‖z‖ ≤ ε` is the box `‖u‖ ≤ ε, ‖v‖ ≤ ε` of the
split model. -/
theorem max_norm_fst_norm_snd_splitCoord (z : Fin (Module.finrank ℝ E) → ℝ) :
    max ‖(φ.splitCoord z).fst‖ ‖(φ.splitCoord z).snd‖ = ‖z‖ := by
  refine le_antisymm (max_le ?_ ?_) ?_
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i ↦ by
      simpa using norm_le_pi_norm z i
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i ↦ by
      simpa using norm_le_pi_norm z i
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i ↦ ?_
    by_cases hi : φ.weight i = 1
    · exact le_max_of_le_left (by simpa using norm_le_pi_norm (φ.splitCoord z).fst ⟨i, hi⟩)
    · exact le_max_of_le_right (by simpa using norm_le_pi_norm (φ.splitCoord z).snd ⟨i, hi⟩)

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
`φ`, and let the coordinate cube of radius `ε` lie in the chart. The orbit of a point of the
entrance face `‖u‖ = ε, 0 < ‖v‖ ≤ ε` stays in the box until the exit time
`TauCeti.splitExitTime`, and at that time it reaches the image of the point under the passage map
`TauCeti.splitPassage`, on the exit face. -/
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
Morse chart `φ`, and let the coordinate cube of radius `ε` lie in the chart. Followed backward in
time, the orbit of a point of the exit face `‖v‖ = ε, 0 < ‖u‖ ≤ ε` stays in the box until the
entry time `TauCeti.splitEntryTime`, and at that time it reaches the image of the point under the
inverse passage map, on the entrance face. -/
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

end IsAdaptedPseudoGradient

end TauCeti

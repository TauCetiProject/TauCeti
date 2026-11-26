/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Naturality of the integral Morse boundary under diffeomorphisms

Let `σ : M → M'` be a diffeomorphism between compact boundaryless manifolds, `f` and `f'` Morse
functions with `f' ∘ σ = f`, and `X`, `X'` pseudo-gradients adapted to `f` and `f'` which `σ`
intertwines: `dσ (X y) = X' (σ y)`. Then `σ` carries every object of the integral Morse complex of
`(f, X)` to the corresponding object of `(f', X')`, and this file proves that it does so
compatibly with the signs.

* **Flows.** `σ` conjugates the flows, `Φ'_t ∘ σ = σ ∘ Φ_t`
  (`TauCeti.IsAdaptedPseudoGradient.flow_apply_diffeomorph`, in
  `TauCeti/Geometry/Manifold/Morse/PseudoGradient/Diffeomorph.lean`), so it carries stable and
  unstable manifolds and the middle-level slices of trajectories to those of `(f', X')`.
* **Morse charts.** A Morse chart `φ` for `f'` at `σ x` pulls back to the Morse chart `φ ∘ σ` for
  `f` at `x`, with the same coordinates and weights (`TauCeti.MorseChart.pullback`, in
  `TauCeti/Geometry/Manifold/Morse/Diffeomorph.lean`); if `X'` is linear in `φ`, then `X` is linear
  in `φ ∘ σ`. The Morse indices of `f` at `x` and of `f'` at `σ x` agree.
* **Frames and signs.** In the pulled-back charts, the unstable frames, the normal coordinates of
  the stable manifolds and the comparison maps of `(f, X)` at `y` are those of `(f', X')` at
  `σ y`, read through `dσ`. Hence the sign of the trajectory through `y`, for orientations
  transported along the pulled-back charts, is the sign of the trajectory through `σ y`
  (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_pullback`), and the signed counts agree.
* **The boundary.** Orientation data `𝔬'` for `(f', X')` pull back to orientation data for
  `(f, X)` (`TauCeti.MorseOrientation.pullback`), and the bijection between the critical points
  of `f` and of `f'` induced by `σ` (`TauCeti.criticalPointsEquivOfComp`) intertwines the two
  integral Morse boundaries, over every ring of coefficients
  (`TauCeti.IsAdaptedPseudoGradient.domLCongr_comp_signedMorseBoundary_pullback`).

Taking `M' = M`, this applies to a symmetry `σ` of `(f, X)` fixing two critical points `p` and
`q`: it permutes the trajectories from `p` to `q`, and a trajectory and its image have the same
sign once the orientations are transported along `σ`. Comparing the transported orientations with
the original ones in the same charts
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_map_negativeChange`) then relates the signs of
two trajectories exchanged by `σ` through the effect of `σ` on the orientations of the unstable
manifolds at `p` and at `q`, read off from the action of its derivative on the unstable frames at
`p` and at `q` (`TauCeti.IsAdaptedPseudoGradient.trajectorySign_apply_eq_mul_mul_trajectorySign`).
For instance, on the real projective plane with its moment function,
the reflection negating the coordinate of the saddle fixes the three critical points, and for a
pseudo-gradient invariant under it, it exchanges the two trajectories from the maximum to the
saddle and the two from the saddle to the minimum.

## Main definitions

* `TauCeti.MorseOrientation.pullback`: the pullback of orientation data along a diffeomorphism
  intertwining the pseudo-gradients.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `preimage_morseTrajectorySlice_diffeomorph`: the diffeomorphism carries the slices of
  trajectories to those of `(f', X')`.
* `trajectoryComparison_pullback`: the comparison maps agree.
* `trajectorySign_pullback`, `signedTrajectoryCount_pullback`: so do the signs of the trajectories
  and their signed counts.
* `signedMorseBoundaryCoeff_pullback`, `domLCongr_comp_signedMorseBoundary_pullback`: the
  diffeomorphism intertwines the integral Morse boundaries.
* `trajectorySign_apply_eq_mul_mul_trajectorySign`: a symmetry fixing `p` and `q`, acting on the
  orientations of the unstable manifolds at `p` and `q` by signs `up` and `uq`, multiplies the
  sign of each trajectory from `p` to `q` by `up * uq`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds and the signs
  of flow lines).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M']
  {f : M → ℝ} {f' : M' → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {X' : (x : M') → TangentSpace 𝓘(ℝ, E) x} {σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M'}
  [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, E) ∞ M']

variable (hf : f' ∘ σ = f)

namespace MorseChart

variable {x : M} (φ : MorseChart E f' (σ x))

/-- The pullback keeps the coordinates of negative weight. -/
@[simp]
theorem pullback_negativeCoord : (φ.pullback hf).negativeCoord = φ.negativeCoord := by
  ext v i
  exact (negativeCoord_apply _ v i).trans (negativeCoord_apply φ v i).symm

/-- The pullback keeps the extension by zero of the coordinates of negative weight. -/
@[simp]
theorem pullback_negativeExtend : (φ.pullback hf).negativeExtend = φ.negativeExtend := by
  refine LinearMap.ext fun c ↦ φ.coord.injective (funext fun i ↦ ?_)
  by_cases hi : φ.weight i < 0
  · exact (coord_negativeExtend_of_weight_neg (φ.pullback hf) c ⟨i, hi⟩).trans
      (coord_negativeExtend_of_weight_neg φ c ⟨i, hi⟩).symm
  · exact (coord_negativeExtend_of_not_weight_neg (φ.pullback hf) c hi).trans
      (coord_negativeExtend_of_not_weight_neg φ c hi).symm

/-- **The target orientation pulls back.** Transporting the orientation `oq` of the coordinates of
negative weight of `φ` to the pullback, by recasting its index type, recasts the target orientation
of the trajectories ending at the centre. -/
theorem trajectoryTargetOrientation_pullback {p : M}
    (oq : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f' (σ x))))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x + 1)
    (hpq' : manifoldMorseIndex 𝓘(ℝ, E) f' (σ p) = manifoldMorseIndex 𝓘(ℝ, E) f' (σ x) + 1)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f' (σ p) = manifoldMorseIndex 𝓘(ℝ, E) f p) :
    (φ.pullback hf).trajectoryTargetOrientation
        (Orientation.reindex ℝ _ (finCongr (φ.manifoldMorseIndex_eq_of_comp hf).symm) oq) hpq =
      Orientation.reindex ℝ _ (finCongr hp) (φ.trajectoryTargetOrientation oq hpq') := by
  rw [trajectoryTargetOrientation_def, trajectoryTargetOrientation_def,
    Orientation.prod_reindex_finCongr_right, Orientation.reindex_finCongr_reindex_finCongr,
    Orientation.reindex_finCongr_reindex_finCongr]

end MorseChart

namespace MorseOrientation

variable (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y))

/-- **The pullback of orientation data along a diffeomorphism.** If `f' ∘ σ = f` and `σ` carries
`X` to `X'`, orientation data `𝔬'` for `(f', X')` give orientation data for `(f, X)`: at a critical
point `p` of `f`, the pullback of the Morse chart of `𝔬'` at `σ p`, with the orientation of `𝔬'`
at `σ p`, its index type recast along the equality of the Morse indices. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `pullback_orientation` needs `(𝔬'.pullback hf hσX).chart` to reduce to the pulled-back charts.
@[expose]
noncomputable def pullback (𝔬' : MorseOrientation f' X') : MorseOrientation f X where
  chart p := (𝔬'.chart (criticalPointsEquivOfComp hf p)).pullback hf
  coord_mfderiv_chart p :=
    MorseChart.coord_mfderiv_pullback hf hσX
      (𝔬'.coord_mfderiv_chart (criticalPointsEquivOfComp hf p))
  orientation p := Orientation.reindex ℝ _
    (finCongr ((𝔬'.chart (criticalPointsEquivOfComp hf p)).manifoldMorseIndex_eq_of_comp hf).symm)
    (𝔬'.orientation (criticalPointsEquivOfComp hf p))

variable (𝔬' : MorseOrientation f' X')

/-- The Morse charts of the pullback are the pullbacks of the Morse charts. -/
@[simp]
theorem pullback_chart (p : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬'.pullback hf hσX).chart p = (𝔬'.chart (criticalPointsEquivOfComp hf p)).pullback hf :=
  rfl

/-- The orientations of the pullback are those of `𝔬'`, with their index types recast. -/
@[simp]
theorem pullback_orientation (p : criticalPoints 𝓘(ℝ, E) f) :
    (𝔬'.pullback hf hσX).orientation p = Orientation.reindex ℝ _
      (finCongr ((𝔬'.chart (criticalPointsEquivOfComp hf p)).manifoldMorseIndex_eq_of_comp hf).symm)
      (𝔬'.orientation (criticalPointsEquivOfComp hf p)) :=
  rfl

open scoped Classical in
/-- **Reversing orientations commutes with the pullback**: pulling back the orientations of `𝔬'`
reversed at the critical points of `S` gives the pulled-back orientations reversed at the critical
points that `σ` carries into `S`. -/
theorem pullback_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f')) [DecidablePred (· ∈ S)] :
    (𝔬'.reverse S).pullback hf hσX =
      (𝔬'.pullback hf hσX).reverse (criticalPointsEquivOfComp hf ⁻¹' S) := by
  ext p
  · simp
  · refine heq_of_eq (funext fun p ↦ ?_)
    simp only [pullback_orientation, reverse_orientation, Set.mem_preimage]
    by_cases hp : criticalPointsEquivOfComp hf p ∈ S <;> simp only [hp, ↓reduceIte]
    · exact Orientation.reindex_neg (R := ℝ) _ _
    · congr 1

end MorseOrientation

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] [CompactSpace M'] [T2Space M']
  (hX : IsAdaptedPseudoGradient f X) (hX' : IsAdaptedPseudoGradient f' X')
  (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X' (σ y))

include hσX

/-! ### Trajectories -/

include hf in
/-- **`σ` carries trajectories to trajectories**: the middle-level slice of the trajectories of `X`
from `p` to `q` is the preimage of the slice of the trajectories of `X'` from `σ p` to `σ q`. -/
theorem preimage_morseTrajectorySlice_diffeomorph (p q : M) :
    σ ⁻¹' hX'.morseTrajectorySlice (σ p) (σ q) = hX.morseTrajectorySlice p q := by
  ext y
  rw [mem_preimage, mem_morseTrajectorySlice, mem_morseTrajectorySlice,
    ← preimage_unstableSet_diffeomorph hX hX' hσX, ← preimage_stableSet_diffeomorph hX hX' hσX]
  simp only [mem_preimage, ← hf, comp_apply]

include hf in
/-- The middle-level slice of the trajectories of `X'` from `σ p` to `σ q` is the image under `σ`
of that of `X` from `p` to `q`. -/
theorem image_morseTrajectorySlice_diffeomorph (p q : M) :
    σ '' hX.morseTrajectorySlice p q = hX'.morseTrajectorySlice (σ p) (σ q) := by
  rw [← preimage_morseTrajectorySlice_diffeomorph hf hX hX' hσX]
  exact σ.surjective.image_preimage _

/-! ### Frames and comparison maps -/

variable {x : M} {φ : MorseChart E f' (σ x)}

include hf in
/-- The times of linear forward flow of `y` in the pullback of `φ` are those of `σ y` in `φ`. -/
theorem linearForwardTimes_pullback (y : M) :
    hX.linearForwardTimes (φ.pullback hf) y = hX'.linearForwardTimes φ (σ y) := by
  ext T
  rw [mem_linearForwardTimes, mem_linearForwardTimes, MorseChart.pullback_source,
    MorseChart.pullback_target, MorseChart.coe_pullback_toChart, MorseChart.pullback_coord,
    MorseChart.pullback_linearFlow]
  simp only [flow_apply_diffeomorph hX hX' hσX, comp_apply, mem_preimage]

include hf in
/-- The times of linear backward flow of `y` in the pullback of `φ` are those of `σ y` in `φ`. -/
theorem linearBackwardTimes_pullback (y : M) :
    hX.linearBackwardTimes (φ.pullback hf) y = hX'.linearBackwardTimes φ (σ y) := by
  ext T
  rw [mem_linearBackwardTimes, mem_linearBackwardTimes, MorseChart.pullback_source,
    MorseChart.pullback_target, MorseChart.coe_pullback_toChart, MorseChart.pullback_coord,
    MorseChart.pullback_linearFlow]
  simp only [flow_apply_diffeomorph hX hX' hσX, comp_apply, mem_preimage]

/-- In the pullback of a chart, the chart composed with the time-`t` map of the flow of `X` is the
chart composed with the time-`t` map of the flow of `X'`, composed with `σ`. -/
private theorem toChart_comp_flow_pullback (t : ℝ) :
    (φ.pullback hf).toChart ∘ hX.flow t = (φ.toChart ∘ hX'.flow t) ∘ σ := by
  ext y
  simp [flow_apply_diffeomorph hX hX' hσX]

include hf in
/-- In the pullback of a chart, the differential at `y` of the chart composed with the time-`t` map
of the flow of `X` is the differential at `σ y` of the chart composed with the time-`t` map of the
flow of `X'`, read through `dσ`. -/
private theorem mfderiv_toChart_comp_flow_pullback_apply (t : ℝ) (y : M)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((φ.pullback hf).toChart ∘ hX.flow t) y w =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX'.flow t) (σ y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y w) := by
  rw [toChart_comp_flow_pullback hf hX hX' hσX, σ.mfderiv_comp_diffeomorph (by simp),
    ContinuousLinearMap.comp_apply]

variable (hφ : ∀ y ∈ φ.toChart.source,
  φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X' y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- **The normal coordinates pull back.** At a point `y` of `W^s(x)`, the normal coordinates of
the stable manifold in the pullback of `φ` are those of `W'^s(σ x)` at `σ y` in `φ`, read through
`dσ`. -/
theorem stableNormal_pullback_apply {y : M} (hy : y ∈ hX.flow.stableSet x)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal (φ.pullback hf) y w =
      hX'.stableNormal φ (σ y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y w) := by
  have hy' : σ y ∈ hX'.flow.stableSet (σ x) := by
    rwa [← preimage_stableSet_diffeomorph hX hX' hσX] at hy
  obtain ⟨T, hT⟩ := (hX'.eventually_mem_linearForwardTimes hφ hy').exists
  have hT' : T ∈ hX.linearForwardTimes (φ.pullback hf) y := by
    rwa [linearForwardTimes_pullback hf hX hX' hσX]
  rw [stableNormal_apply (MorseChart.coord_mfderiv_pullback hf hσX hφ) hT',
    mfderiv_toChart_comp_flow_pullback_apply hf hX hX' hσX,
    MorseChart.pullback_negativeCoord, stableNormal_apply hφ hT]

/-- **The unstable frame pulls back.** At a point `y` of `W^u(x)`, `dσ` carries the unstable frame
of `W^u(x)` in the pullback of `φ` to that of `W'^u(σ x)` at `σ y` in `φ`. -/
theorem mfderiv_unstableFrame_pullback (hf' : IsMorse 𝓘(ℝ, E) f') {y : M}
    (hy : y ∈ hX.flow.unstableSet x) (c : {i // φ.weight i < 0} → ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (hX.unstableFrame (φ.pullback hf) y c) =
      hX'.unstableFrame φ (σ y) c := by
  have hy' : σ y ∈ hX'.flow.unstableSet (σ x) := by
    rwa [← preimage_unstableSet_diffeomorph hX hX' hσX] at hy
  obtain ⟨T, hT⟩ := (hX'.eventually_mem_linearBackwardTimes hφ hf' hy').exists
  have hT' : T ∈ hX.linearBackwardTimes (φ.pullback hf) y := by
    rwa [linearBackwardTimes_pullback hf hX hX' hσX]
  -- Both sides have the same image under the invertible derivative of `φ ∘ Φ'_{-T}` at `σ y`.
  refine (isInvertible_mfderiv_toChart_comp_flow ((mem_linearBackwardTimes hX' φ).1 hT).1).injective
    ?_
  have h := mfderiv_unstableFrame (MorseChart.coord_mfderiv_pullback hf hσX hφ) hT' c
  rw [mfderiv_toChart_comp_flow_pullback_apply hf hX hX' hσX,
    MorseChart.pullback_negativeExtend] at h
  exact h.trans (mfderiv_unstableFrame hφ hT c).symm

omit hφ

/-- **The comparison maps pull back.** At a point `y` of a trajectory of `X` from `p` to `q`, the
comparison map in the pullbacks of Morse charts `φp` at `σ p` and `φq` at `σ q` is the comparison
map of `X'` in `φp` and `φq` at `σ y`. -/
theorem trajectoryComparison_pullback (hf' : IsMorse 𝓘(ℝ, E) f') {p q : M}
    {φp : MorseChart E f' (σ p)} {φq : MorseChart E f' (σ q)}
    (hφp : ∀ y ∈ φp.toChart.source,
      φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X' y)) =
        fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source,
      φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X' y)) =
        fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.trajectoryComparison (φp.pullback hf) (φq.pullback hf) y =
      hX'.trajectoryComparison φp φq (σ y) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hd (w : TangentSpace 𝓘(ℝ, E) y) :
      mvfderiv 𝓘(ℝ, E) f y w = mvfderiv 𝓘(ℝ, E) f' (σ y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y w) := by
    rw [← hf, σ.mvfderiv_comp_diffeomorph (by simp), ContinuousLinearMap.comp_apply]
  rw [trajectoryComparison_apply, trajectoryComparison_apply, hd,
    stableNormal_pullback_apply hf hX hX' hσX hφq hy.2,
    mfderiv_unstableFrame_pullback hf hX hX' hσX hφp hf' hy.1]

/-! ### Signs of trajectories and signed counts -/

variable {p q : M} {φp : MorseChart E f' (σ p)} {φq : MorseChart E f' (σ q)}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X' y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X' y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f' (σ p))))
  (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f' (σ q))))
  (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)

include hφp hφq

/-- **Signs of trajectories pull back.** The sign of the trajectory of `X` through `y`, for the
pullbacks of the Morse charts `φp` and `φq` and the orientations `op` and `oq` transported to them,
is the sign of the trajectory of `X'` through `σ y`. -/
theorem trajectorySign_pullback (hf' : IsMorse 𝓘(ℝ, E) f') {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.trajectorySign (φp.pullback hf) (φq.pullback hf)
        (Orientation.reindex ℝ _ (finCongr (φp.manifoldMorseIndex_eq_of_comp hf).symm) op)
        (Orientation.reindex ℝ _ (finCongr (φq.manifoldMorseIndex_eq_of_comp hf).symm) oq) hpq y =
      hX'.trajectorySign φp φq op oq
        (MorseChart.manifoldMorseIndex_eq_add_one_of_comp hf φp φq hpq) (σ y) := by
  have hC := trajectoryComparison_pullback hf hX hX' hσX hf' hφp hφq hy
  by_cases hb : Bijective (hX'.trajectoryComparison φp φq (σ y))
  · have hb' : Bijective (hX.trajectoryComparison (φp.pullback hf) (φq.pullback hf) y) := by
      rwa [hC]
    have he : LinearEquiv.ofBijective
          (hX.trajectoryComparison (φp.pullback hf) (φq.pullback hf) y).toLinearMap hb' =
        LinearEquiv.ofBijective (hX'.trajectoryComparison φp φq (σ y)).toLinearMap hb :=
      LinearEquiv.ext fun v ↦ by simp [hC]
    rw [trajectorySign_of_bijective hb', trajectorySign_of_bijective hb, he,
      Orientation.map_reindex, MorseChart.trajectoryTargetOrientation_pullback hf φq oq hpq
        (MorseChart.manifoldMorseIndex_eq_add_one_of_comp hf φp φq hpq)
        (φp.manifoldMorseIndex_eq_of_comp hf).symm,
      (Orientation.reindex ℝ _ _).injective.eq_iff]
  · have hb' : ¬Bijective (hX.trajectoryComparison (φp.pullback hf) (φq.pullback hf) y) := by
      rwa [hC]
    rw [trajectorySign_of_not_bijective hb', trajectorySign_of_not_bijective hb]

/-- **Signed counts pull back.** The number of trajectories of `X` from `p` to `q` counted with
their signs, in the pullbacks of the Morse charts `φp` and `φq` and for the orientations `op` and
`oq` transported to them, is the signed count of the trajectories of `X'` from `σ p` to `σ q`. -/
theorem signedTrajectoryCount_pullback (hf' : IsMorse 𝓘(ℝ, E) f') :
    hX.signedTrajectoryCount (φp.pullback hf) (φq.pullback hf)
        (Orientation.reindex ℝ _ (finCongr (φp.manifoldMorseIndex_eq_of_comp hf).symm) op)
        (Orientation.reindex ℝ _ (finCongr (φq.manifoldMorseIndex_eq_of_comp hf).symm) oq) hpq =
      hX'.signedTrajectoryCount φp φq op oq
        (MorseChart.manifoldMorseIndex_eq_add_one_of_comp hf φp φq hpq) := by
  rw [signedTrajectoryCount_def, signedTrajectoryCount_def,
    ← image_morseTrajectorySlice_diffeomorph hf hX hX' hσX,
    finsum_mem_image (g := ⇑σ) σ.injective.injOn]
  refine finsum_mem_congr rfl fun y hy ↦ ?_
  rw [mem_morseTrajectorySlice] at hy
  exact trajectorySign_pullback hf hX hX' hσX hφp hφq op oq hpq hf' ⟨hy.1, hy.2.1⟩

omit hφp hφq op oq hpq

/-! ### The integral Morse boundary -/

variable (𝔬' : MorseOrientation f' X') (hf' : IsMorse 𝓘(ℝ, E) f')
include hf'

/-- **The boundary coefficients pull back.** The coefficient of `q` in the integral Morse boundary
of `p`, for the orientation data pulled back from `𝔬'`, is the coefficient of `σ q` in the
boundary of `σ p` for `𝔬'`. -/
theorem signedMorseBoundaryCoeff_pullback (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseBoundaryCoeff (𝔬'.pullback hf hσX) p q =
      hX'.signedMorseBoundaryCoeff 𝔬' (criticalPointsEquivOfComp hf p)
        (criticalPointsEquivOfComp hf q) := by
  -- The Morse charts of `𝔬'` at `σ p` and `σ q`.
  let φp : MorseChart E f' (σ p) := 𝔬'.chart (criticalPointsEquivOfComp hf p)
  let φq : MorseChart E f' (σ q) := 𝔬'.chart (criticalPointsEquivOfComp hf q)
  have hp := φp.manifoldMorseIndex_eq_of_comp hf
  have hq := φq.manifoldMorseIndex_eq_of_comp hf
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one
        (MorseChart.manifoldMorseIndex_eq_add_one_of_comp hf φp φq hpq)]
    exact signedTrajectoryCount_pullback hf hX hX' hσX (𝔬'.coord_mfderiv_chart _)
      (𝔬'.coord_mfderiv_chart _) _ _ hpq hf'
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq,
      signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one]
    simpa [← hp, ← hq] using hpq

/-- **Naturality of the integral Morse boundary.** The bijection between the critical points of
`f` and of `f'` given by `σ` intertwines the Morse boundary of `(f, X)`, for the orientation data
pulled back from `𝔬'`, with the Morse boundary of `(f', X')` for `𝔬'`, over every ring of
coefficients. -/
theorem domLCongr_comp_signedMorseBoundary_pullback (R : Type*) [Ring R] :
    (Finsupp.domLCongr (criticalPointsEquivOfComp hf)).toLinearMap ∘ₗ
        hX.signedMorseBoundary (𝔬'.pullback hf hσX)
          (hf ▸ hf'.comp_isLocalDiffeomorph σ.isLocalDiffeomorph) R =
      hX'.signedMorseBoundary 𝔬' hf' R ∘ₗ
        (Finsupp.domLCongr (criticalPointsEquivOfComp hf)).toLinearMap := by
  refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun q ↦ ?_
  obtain ⟨q, rfl⟩ := (criticalPointsEquivOfComp hf).surjective q
  simp [Finsupp.domLCongr_apply, signedMorseBoundaryCoeff_pullback hf hX hX' hσX 𝔬' hf']

end IsAdaptedPseudoGradient

/-! ### Symmetries fixing two critical points -/

namespace IsAdaptedPseudoGradient

section Symmetry

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

/-- At a critical point `p`, a change of negative coordinates `N` from the chart of `𝔬` at `p` to
the chart of `𝔬` at `c = p` which agrees with `L` through the unstable frames transports the
orientation of `𝔬` at `p` as `L` does. -/
private theorem map_orientation_eq_units_smul_reindex (hX : IsAdaptedPseudoGradient f X)
    (hf' : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X) {p c : criticalPoints 𝓘(ℝ, E) f}
    (hc : c = p)
    (N : ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart c).weight i < 0} → ℝ))
    (L : ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart p).weight i < 0} → ℝ))
    (hN : ∀ v, hX.unstableFrame (𝔬.chart c) c (N v) = hX.unstableFrame (𝔬.chart p) p (L v))
    {u : ℤˣ} (hu : Orientation.map _ L (𝔬.orientation p) =
      Units.map (Int.castRingHom ℝ).toMonoidHom u • 𝔬.orientation p)
    (h : manifoldMorseIndex 𝓘(ℝ, E) f c = manifoldMorseIndex 𝓘(ℝ, E) f p) :
    Orientation.map _ N (𝔬.orientation p) =
      Units.map (Int.castRingHom ℝ).toMonoidHom u •
        Orientation.reindex ℝ _ (finCongr h) (𝔬.orientation c) := by
  subst hc
  -- At the critical point itself, the unstable frame is injective, so `N = L`.
  have hc : (c : M) ∈ hX.flow.unstableSet c :=
    (hX.mem_unstableSet_inter_stableSet_self
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 c.property)).1
  have hNL : N = L := LinearEquiv.ext fun v ↦
    hX.injective_unstableFrame_of_mem (𝔬.coord_mfderiv_chart c) hf' hc (hN v)
  rw [hNL, hu, finCongr_refl, Orientation.reindex_refl, Equiv.refl_apply]

/-- **Signs of trajectories under a symmetry.** Let `σ` be a diffeomorphism of `M` preserving `f`
and `X` and fixing the critical points `p` and `q`, where `ind p = ind q + 1`. Suppose that the
derivative of `σ` acts on the unstable frames of the orientation data `𝔬` at `p` and at `q` through
linear isomorphisms `Lp` and `Lq` of the coordinates of negative weight, which multiply the
orientations of `𝔬` at `p` and at `q` by the signs `up` and `uq`. Then the sign of the image under
`σ` of a trajectory from `p` to `q` is `up * uq` times the sign of the trajectory. -/
theorem trajectorySign_apply_eq_mul_mul_trajectorySign (hX : IsAdaptedPseudoGradient f X)
    (hf' : IsMorse 𝓘(ℝ, E) f) (σ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (hσf : f ∘ σ = f)
    (hσX : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ y (X y) = X (σ y)) (𝔬 : MorseOrientation f X)
    {p q : criticalPoints 𝓘(ℝ, E) f} (hp : σ p = p) (hq : σ q = q)
    (Lp : ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart p).weight i < 0} → ℝ))
    (Lq : ({i // (𝔬.chart q).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart q).weight i < 0} → ℝ))
    (hLp : ∀ v, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ p (hX.unstableFrame (𝔬.chart p) p v) =
      hX.unstableFrame (𝔬.chart p) p (Lp v))
    (hLq : ∀ v, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) σ q (hX.unstableFrame (𝔬.chart q) q v) =
      hX.unstableFrame (𝔬.chart q) q (Lq v))
    {up uq : ℤˣ}
    (hup : Orientation.map _ Lp (𝔬.orientation p) =
      Units.map (Int.castRingHom ℝ).toMonoidHom up • 𝔬.orientation p)
    (huq : Orientation.map _ Lq (𝔬.orientation q) =
      Units.map (Int.castRingHom ℝ).toMonoidHom uq • 𝔬.orientation q)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq (σ y) =
      up * uq *
        hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq y := by
  set e := criticalPointsEquivOfComp hσf
  -- The charts of `𝔬` at `σ p` and `σ q`, which pull back along `σ` to Morse charts at `p` and `q`.
  set φp : MorseChart E f (σ p) := 𝔬.chart (e p)
  set φq : MorseChart E f (σ q) := 𝔬.chart (e q)
  have hφp' := MorseChart.coord_mfderiv_pullback hσf hσX (𝔬.coord_mfderiv_chart (e p))
  have hφq' := MorseChart.coord_mfderiv_pullback hσf hσX (𝔬.coord_mfderiv_chart (e q))
  have hmem (r : criticalPoints 𝓘(ℝ, E) f) : (r : M) ∈ hX.flow.unstableSet r :=
    (hX.mem_unstableSet_inter_stableSet_self
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 r.property)).1
  -- Through the unstable frames, the changes of negative coordinates to the pulled-back charts
  -- are `Lp` and `Lq`; so they transport the orientations of `𝔬` by `up` and `uq`.
  have hop := map_orientation_eq_units_smul_reindex hX hf' 𝔬 (c := e p) (Subtype.ext hp)
    ((𝔬.chart p).negativeChange (φp.pullback hσf)) Lp (fun v ↦ by
      rw [← hLp, ← unstableFrame_negativeChange (𝔬.coord_mfderiv_chart p) hφp' hf' (hmem p) v]
      exact (mfderiv_unstableFrame_pullback hσf hX hX hσX (𝔬.coord_mfderiv_chart (e p)) hf'
        (hmem p) _).symm) hup (φp.manifoldMorseIndex_eq_of_comp hσf).symm
  have hoq := map_orientation_eq_units_smul_reindex hX hf' 𝔬 (c := e q) (Subtype.ext hq)
    ((𝔬.chart q).negativeChange (φq.pullback hσf)) Lq (fun v ↦ by
      rw [← hLq, ← unstableFrame_negativeChange (𝔬.coord_mfderiv_chart q) hφq' hf' (hmem q) v]
      exact (mfderiv_unstableFrame_pullback hσf hX hX hσX (𝔬.coord_mfderiv_chart (e q)) hf'
        (hmem q) _).symm) huq (φq.manifoldMorseIndex_eq_of_comp hσf).symm
  -- The sign at `σ y` in the charts of `𝔬` at `σ p = p` and `σ q = q` is the sign at `y` in the
  -- pulled-back charts, and changing to the charts of `𝔬` multiplies it by `up * uq`.
  have key : ∀ (c d : criticalPoints 𝓘(ℝ, E) f) (_ : c = p) (_ : d = q)
      (h : manifoldMorseIndex 𝓘(ℝ, E) f c = manifoldMorseIndex 𝓘(ℝ, E) f d + 1),
      hX.trajectorySign (𝔬.chart c) (𝔬.chart d) (𝔬.orientation c) (𝔬.orientation d) h (σ y) =
        hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq
          (σ y) := by
    rintro c d rfl rfl h
    rfl
  rw [← key (e p) (e q) (Subtype.ext hp) (Subtype.ext hq)
      (MorseChart.manifoldMorseIndex_eq_add_one_of_comp hσf φp φq hpq)]
  -- The critical point `e p` is `σ p` as a point of `M`, so the pullback statement applies.
  refine (trajectorySign_pullback hσf hX hX hσX (𝔬.coord_mfderiv_chart (e p))
    (𝔬.coord_mfderiv_chart (e q)) _ _ hpq hf' hy).symm.trans ?_
  rw [← trajectorySign_map_negativeChange (𝔬.coord_mfderiv_chart p) hφp'
    (𝔬.coord_mfderiv_chart q) hφq' hf' (𝔬.orientation p) (𝔬.orientation q) hpq hy, hop, hoq,
    Orientation.intCast_units_smul_eq_ite, Orientation.intCast_units_smul_eq_ite]
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  -- After `simp only`, the two sides of each case differ only in the base points of the charts in
  -- the implicit types of the `Orientation.reindex` coercions: `σ p` on one side and `(e p : M)`
  -- on the other. These agree by definition (`coe_criticalPointsEquivOfComp_apply` is `rfl`), but
  -- `simp` and `rw` cannot reach into these dependent implicit types, so `rfl` closes the goals.
  rcases Int.units_eq_one_or up with rfl | rfl <;> rcases Int.units_eq_one_or uq with rfl | rfl <;>
    simp only [↓reduceIte, hne, trajectorySign_neg_left, trajectorySign_neg_right, Units.val_one,
      Units.val_neg, one_mul, neg_mul, neg_neg] <;> rfl

end Symmetry

end IsAdaptedPseudoGradient

end TauCeti

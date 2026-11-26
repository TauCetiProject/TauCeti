/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.Morse.Boundary.OneDimensional
import TauCeti.Geometry.Manifold.Morse.Stable.Orientation
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The fundamental chain of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
Morse–Smale pseudo-gradient adapted to `f`, `𝔬` orientation data for the integral Morse boundary
(`TauCeti.MorseOrientation`), and `oM` an orientation of `M`. At a critical point `p` of index
`n` the unstable manifold `W^u(p)` is an open subset of `M`, which `𝔬` orients through the unstable
frame at `p`. The **fundamental sign** of `p`
(`TauCeti.IsAdaptedPseudoGradient.fundamentalSign`) is `1` if this is the orientation `oM`, `-1`
if it is the opposite one, and `0` at the critical points of index less than `n`. The
**fundamental chain** (`TauCeti.IsAdaptedPseudoGradient.signedMorseFundamentalChain`) is the sum
of the critical points of index `n`, weighted by their fundamental signs.

The main theorem is that the fundamental chain is a cycle of the integral Morse complex,
`∂ [M] = 0`, with coefficients in any ring. With coefficients in `ZMod 2` it is the mod-two
fundamental chain `TauCeti.morseFundamentalChain`, whatever the orientations. It is dual to the
vanishing of the augmentation on boundaries, `ε ∘ ∂ = 0`
(`TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation`), with the trajectories reaching a
critical point of index `n - 1` in place of those leaving a critical point of index `1`; unlike the
augmentation, it needs the orientation of `M`.

The proof has two steps.

* **The orientation of `M` along `W^u(p)`.** The flow preserves every orientation of `M`
  (`TauCeti.IsAdaptedPseudoGradient.isOrientationPreservingAt_flow`), and in a Morse chart at `p`
  the unstable frames at a point `y` of `W^u(p)` flowed back close to `p` and at `p` itself are the
  same map up to a positive factor. So the unstable frame compares `𝔬` with `oM` in the same way at
  every point of `W^u(p)`
  (`TauCeti.IsAdaptedPseudoGradient.map_unstableFrame_eq_orientationAt_iff`). Along a trajectory
  from `p` to a critical point `q`, the sign of the trajectory times the fundamental sign of `p`
  therefore compares `oM` with the map `v ↦ (df v, N_q v)` formed by the differential of `f` and
  the normal coordinates of `W^s(q)`.
* **The two sides of a critical point of index `n - 1`.** The stable manifold of such a `q` is `q`
  together with two trajectories, coming from critical points of index `n`. In a Morse chart at
  `q`, close to `q`, they have a single nonzero coordinate, of positive weight, and its signs on
  the two trajectories are opposite. There `df` is that coordinate times the coordinate function,
  while `oM` is constant in the chart, so the two maps `v ↦ (df v, N_q v)` carry `oM` to opposite
  orientations, and the two trajectories cancel in the boundary of the fundamental chain.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `unstableOrientation`: the orientation of the tangent space at a critical point of top index
  carried by the unstable frame from the orientation of its coordinates of negative weight.
* `fundamentalSign`: the sign comparing the orientation of the unstable manifold of a critical
  point of top index with the orientation of `M`, and `0` at the other critical points.
* `signedMorseFundamentalChain`: the sum of the critical points of top index, weighted by their
  fundamental signs, with coefficients in a ring `R`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `map_unstableFrame_eq_orientationAt_iff`: the unstable frame of a critical point of top index
  compares orientations in the same way at every point of its unstable manifold.
* `bijective_mvfderiv_prod_stableNormal`, `fundamentalSign_mul_trajectorySign`: along a trajectory
  from a critical point of top index to one of index `n - 1`, the map `v ↦ (df v, N_q v)` is an
  isomorphism, and the sign of the trajectory times the fundamental sign of its source compares,
  through this map, the orientation of `M` with the standard orientation of `ℝ` followed by the
  orientation of the unstable manifold of `q`.
* `fundamentalSign_mul_trajectorySign_of_finrank_eq_one`: on an oriented manifold of dimension
  `1`, the sign of a trajectory from a critical point of index `1` to one of index `0`, weighted by
  the fundamental sign of its source and the augmentation sign of its end, is the sign of the
  derivative of `f` in the positive direction at any of its points.
* `IsMorseSmale.finsum_fundamentalSign_mul_signedMorseBoundaryCoeff`: the boundary coefficients of
  a critical point, weighted by the fundamental signs of their sources, add up to zero.
* `IsMorseSmale.signedMorseBoundary_signedMorseFundamentalChain`: `∂ [M] = 0`.
* `signedMorseFundamentalChain_eq_morseFundamentalChain`: modulo two, the fundamental chain is the
  mod-two fundamental chain.
* `signedMorseFundamentalChain_neg`, `signedMorseFundamentalChain_reverse`: reversing the
  orientation of `M`, or of unstable manifolds, changes the signs accordingly.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Function Module Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X}

/-- The unstable frame at a critical point of top index is bijective. -/
theorem bijective_unstableFrame_self (𝔬 : MorseOrientation f X) {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    Bijective (hX.unstableFrame (𝔬.chart p) p) :=
  bijective_unstableFrame (𝔬.coord_mfderiv_chart p) hp
    (mem_linearBackwardTimes_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) 0)

variable (hX) in
/-- The **unstable orientation** of a critical point `p` of Morse index `n = dim M`: the
orientation `𝔬.orientation p` of the coordinates of negative weight, carried by the unstable frame
at `p` to an orientation of the tangent space `T_p M`. -/
noncomputable def unstableOrientation (𝔬 : MorseOrientation f X) {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, E) (p : M)) (Fin (finrank ℝ E)) :=
  Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) p).toLinearMap
    (bijective_unstableFrame_self 𝔬 hp)) ((𝔬.orientation p).reindex ℝ _ (finCongr hp))

/-- The defining formula of the unstable orientation. -/
theorem unstableOrientation_def (𝔬 : MorseOrientation f X) {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.unstableOrientation 𝔬 hp =
      Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) p).toLinearMap
        (bijective_unstableFrame_self 𝔬 hp)) ((𝔬.orientation p).reindex ℝ _ (finCongr hp)) :=
  (rfl)

/-- **Reversing orientations reverses the unstable orientations** at the critical points of the
reversed set. -/
theorem unstableOrientation_reverse (𝔬 : MorseOrientation f X)
    (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)] {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.unstableOrientation (𝔬.reverse S) hp =
      if p ∈ S then -hX.unstableOrientation 𝔬 hp else hX.unstableOrientation 𝔬 hp := by
  rw [unstableOrientation_def, unstableOrientation_def, MorseOrientation.reverse_orientation]
  split_ifs
  · exact (congrArg _ (Orientation.reindex_neg _ _)).trans (Orientation.map_neg _ _)
  -- The reversed data has the same charts by definition (`reverse_chart`), so the two unstable
  -- frames agree.
  · rfl

variable (hX) in
open scoped Classical in
/-- The **fundamental sign** of a critical point `p` for an orientation `oM` of `M`. When `p` has
Morse index `n = dim M`, the sign is `1` if the unstable orientation of `p` is the orientation `oM`
of `M` at `p`, and `-1` otherwise. At the critical points of index less than `n` the sign is
`0`. -/
noncomputable def fundamentalSign (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) (p : criticalPoints 𝓘(ℝ, E) f) :
    ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E then
    if hX.unstableOrientation 𝔬 h = oM.orientationAt p then 1 else -1
  else 0

variable {𝔬 : MorseOrientation f X} {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}

open scoped Classical in
/-- At a critical point of top index, the fundamental sign compares the unstable orientation with
the orientation of `M`. -/
theorem fundamentalSign_of_morseIndex_eq {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.fundamentalSign 𝔬 oM p =
      if hX.unstableOrientation 𝔬 hp = oM.orientationAt p then 1 else -1 :=
  dite_eq_left hp

/-- The fundamental sign vanishes at the critical points of index less than `dim M`. -/
@[simp]
theorem fundamentalSign_of_morseIndex_ne {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ finrank ℝ E) : hX.fundamentalSign 𝔬 oM p = 0 :=
  dite_eq_right hp

/-- At a critical point of top index the fundamental sign is `±1`. -/
theorem fundamentalSign_eq_one_or_eq_neg_one {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.fundamentalSign 𝔬 oM p = 1 ∨ hX.fundamentalSign 𝔬 oM p = -1 := by
  rw [fundamentalSign_of_morseIndex_eq hp]
  split_ifs <;> simp

/-- Modulo two, the fundamental sign is `1` at the critical points of top index and `0`
elsewhere, whatever the orientations. -/
theorem intCast_fundamentalSign (p : criticalPoints 𝓘(ℝ, E) f) :
    (hX.fundamentalSign 𝔬 oM p : ZMod 2) =
      if manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E then 1 else 0 := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [ite_eq_left hp]
    rcases fundamentalSign_eq_one_or_eq_neg_one (𝔬 := 𝔬) (oM := oM) hp with h | h <;>
      rw [h] <;> decide
  · rw [ite_eq_right hp, fundamentalSign_of_morseIndex_ne hp, Int.cast_zero]

/-- **Reversing the orientation of `M` reverses the fundamental signs.** -/
@[simp]
theorem fundamentalSign_neg (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.fundamentalSign 𝔬 (-oM) p = -hX.fundamentalSign 𝔬 oM p := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [fundamentalSign_of_morseIndex_eq hp, fundamentalSign_of_morseIndex_eq hp,
      Manifold.Orientation.orientationAt_neg]
    exact Orientation.ite_eq_neg_eq_neg_ite (Fintype.card_fin _)
  · simp [hp]

/-- **Reversing orientations changes the fundamental signs** at the critical points of the
reversed set. -/
theorem fundamentalSign_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)]
    (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.fundamentalSign (𝔬.reverse S) oM p =
      (if p ∈ S then -1 else 1) * hX.fundamentalSign 𝔬 oM p := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [fundamentalSign_of_morseIndex_eq hp, fundamentalSign_of_morseIndex_eq hp,
      unstableOrientation_reverse]
    by_cases hS : p ∈ S
    · rw [ite_eq_left hS, ite_eq_left hS, neg_one_mul]
      exact Orientation.ite_neg_eq_eq_neg_ite (Fintype.card_fin _)
    · rw [ite_eq_right hS, ite_eq_right hS, one_mul]
  · simp [hp]

/-- **The orientation of `M` along an unstable manifold.** Let `p` be a critical point and `op` an
orientation of the coordinates of negative weight of a Morse chart at `p` in which `X` is linear.
At every point `y` of `W^u(p)` where the unstable frame is an isomorphism, as it is when `p` has
index `n`, the unstable frame carries `op` to the orientation of `M` exactly when it does so at
`p`. -/
theorem map_unstableFrame_eq_orientationAt_iff (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    {φ : MorseChart E f p}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (finrank ℝ E))) {y : M}
    (hy : y ∈ hX.flow.unstableSet p) (hby : Bijective (hX.unstableFrame φ y))
    (hbp : Bijective (hX.unstableFrame φ p)) :
    Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φ y).toLinearMap hby) op =
        oM.orientationAt y ↔
      Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φ p).toLinearMap hbp) op =
        oM.orientationAt p := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ hf hy).exists
  obtain ⟨eDy, heDy⟩ := isInvertible_mfderiv_toChart_comp_flow (hX := hX) (φ := φ)
    ((hX.mem_linearBackwardTimes φ).1 hT).1
  obtain ⟨eDp, heDp⟩ := isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source
  let Ly : TangentSpace 𝓘(ℝ, E) y ≃ₗ[ℝ] E := eDy.toLinearEquiv
  let Lp : TangentSpace 𝓘(ℝ, E) p ≃ₗ[ℝ] E := eDp.toLinearEquiv
  -- Read both tangent spaces in the model space `E`, through `φ ∘ Φ_{-T}` and `φ`: there `oM`
  -- gives the same orientation at `y` and at `p`.
  refine Orientation.eq_iff_eq_of_map_eq Ly Lp ?_
    (map_orientationAt_eq_of_mem_linearBackwardTimes hφ oM hy hT eDy heDy eDp heDp)
  -- So do the frames, since there the frame at `y` is `e^{-T}` times the frame at `p`.
  have hL : (LinearEquiv.ofBijective (hX.unstableFrame φ y).toLinearMap hby).trans Ly =
      ((LinearEquiv.smulOfNeZero ℝ _ (Real.exp (-T)) (Real.exp_pos _).ne').trans
        (LinearEquiv.ofBijective (hX.unstableFrame φ p).toLinearMap hbp)).trans Lp := by
    ext c
    have h := mfderiv_unstableFrame_eq_exp_smul_self hφ hp hT c
    rw [← heDy, ← heDp, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe] at h
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.smulOfNeZero_apply, map_smul, map_smul]
    exact h
  rw [← Orientation.map_trans, hL, Orientation.map_trans, Orientation.map_trans,
    Orientation.map_smulOfNeZero_of_pos _ (Real.exp_pos _)]

/-! ### The two trajectories into a critical point of index `n - 1` -/

/-- **Normal form of a point of the stable manifold near a critical point of index `n - 1`.**
Flowing a point `y ≠ q` of `W^s(q)` forward for a long time brings it to a point `z` with linear
forward flow at time `0`, satisfying any property `P` that holds near `q`, whose only nonzero
coordinate in the Morse chart is the coordinate `b` of positive weight. -/
private theorem exists_flow_eq_smul_single {q : M}
    {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hneg : ∀ i, i ≠ j → φ.weight i < 0) {y : M}
    (hy : y ∈ hX.flow.stableSet q) (hyq : y ≠ q) {P : M → Prop} (hP : ∀ᶠ z in 𝓝 q, P z) :
    ∃ T b : ℝ, 0 ∈ hX.linearForwardTimes φ (hX.flow T y) ∧ P (hX.flow T y) ∧ b ≠ 0 ∧
      φ.coord (φ.toChart (hX.flow T y)) = b • Pi.single j 1 := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  have hnear : ∀ᶠ z in 𝓝 q, P z ∧ z ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart z)‖ < ε :=
    hP.and (φ.eventually_mem_source_norm_coord_lt hε)
  obtain ⟨T, hT, hPT, hsrc, hsmall⟩ := ((hX.eventually_mem_linearForwardTimes hφ hy).and
    ((Flow.mem_stableSet.1 hy).eventually hnear)).exists
  have hzs : hX.flow T y ∈ hX.flow.stableSet q := (Flow.apply_mem_stableSet_iff _ T).2 hy
  have hzero := (hloc _ hsrc hsmall).1 hzs
  set b := φ.coord (φ.toChart (hX.flow T y)) j
  have hcoord : φ.coord (φ.toChart (hX.flow T y)) = b • Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [b]
    · simp [hi, hzero i (hneg i hi)]
  refine ⟨T, b, (mem_linearForwardTimes_flow (hX := hX)).2 (by rwa [zero_add]), hPT,
    fun hb ↦ hyq ?_, hcoord⟩
  -- A vanishing coordinate `b` puts the point at the centre `q` of the chart.
  rw [hb, zero_smul, ← map_zero φ.coord] at hcoord
  have hq := (φ.toChart_eq_zero_iff hsrc).1 (φ.coord.injective hcoord)
  calc y = hX.flow (-T) (hX.flow T y) := by rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    _ = hX.flow (-T) q := by rw [hq]
    _ = q := hX.flow_apply_of_mfderiv_eq_zero (hX.mfderiv_eq_zero_of_mem_stableSet hy) (-T)

/-- Two points of the stable manifold with linear forward flow at time `0`, whose only nonzero
coordinates are coordinates `b₁`, `b₂` of positive weight with `0 < b₂ / b₁ ≤ 1`, lie on one
orbit: the flow for the time `-log (b₂ / b₁)` takes the first to the second. -/
private theorem flow_eq_of_coord_eq_smul_single {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hpos : 0 < b₂ / b₁)
    (hle : b₂ / b₁ ≤ 1) : hX.flow (-Real.log (b₂ / b₁)) z₁ = z₂ := by
  have hb₁0 : b₁ ≠ 0 := fun h ↦ by simp [h] at hpos
  obtain ⟨hs, hcoord⟩ := add_mem_linearForwardTimes hφ h₁
    (neg_nonneg.2 (Real.log_nonpos hpos.le hle))
  rw [add_zero] at hs hcoord
  -- The flow for the time `-log (b₂ / b₁)` rescales the coordinate `b₁` to `b₂`.
  have hscale : b₁ * Real.exp (-(-Real.log (b₂ / b₁))) = b₂ := by
    simp [Real.exp_log hpos, mul_div_cancel₀ _ hb₁0]
  rw [Flow.map_zero_apply, hb₁, φ.linearFlow_smul, φ.linearFlow_single_of_weight_eq_one hj,
    smul_smul, hscale, ← hb₂] at hcoord
  have h₂src : z₂ ∈ φ.toChart.source := by
    simpa using ((mem_linearForwardTimes hX φ).1 h₂).1
  exact φ.toChart.injOn ((mem_linearForwardTimes hX φ).1 hs).1 h₂src
    (φ.coord.injective hcoord)

/-- **The two trajectories into a critical point of index `n - 1` arrive from opposite sides.**
Two points of the stable manifold on different orbits, with linear forward flow at time `0` and
whose only nonzero coordinates are coordinates `b₁`, `b₂` of positive weight, have `b₁ b₂ < 0`. -/
private theorem mul_neg_of_notMem_orbit {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁0 : b₁ ≠ 0) (hb₂0 : b₂ ≠ 0) (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hne : z₂ ∉ hX.flow.orbit z₁) :
    b₁ * b₂ < 0 := by
  by_contra hle
  have hpos : 0 < b₁ * b₂ := lt_of_le_of_ne (not_lt.1 hle) (mul_ne_zero hb₁0 hb₂0).symm
  have h₂₁ : 0 < b₂ / b₁ := by
    rw [show b₂ / b₁ = b₁ * b₂ / (b₁ * b₁) by field_simp]
    exact div_pos hpos (mul_self_pos.2 hb₁0)
  rcases le_total (b₂ / b₁) 1 with hle₁ | hle₁
  · exact hne ((hX.flow.mem_orbit_iff).2
      ⟨_, flow_eq_of_coord_eq_smul_single hφ hj h₁ h₂ hb₁ hb₂ h₂₁ hle₁⟩)
  · -- Otherwise the flow takes `z₂` to `z₁`.
    have h₁₂ : b₁ / b₂ = (b₂ / b₁)⁻¹ := (inv_div b₂ b₁).symm
    have h := flow_eq_of_coord_eq_smul_single hφ hj h₂ h₁ hb₂ hb₁ (h₁₂ ▸ inv_pos.2 h₂₁)
      (h₁₂ ▸ inv_le_one_of_one_le₀ hle₁)
    refine hne ((hX.flow.mem_orbit_iff).2 ⟨Real.log (b₁ / b₂), ?_⟩)
    rw [← h, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- At a point of a Morse chart whose only nonzero coordinate is a coordinate `b` of weight `1`,
the linear field `X` is `-b` times the corresponding coordinate vector. -/
private theorem mfderiv_toChart_apply_eq_smul {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z : M} (hz : z ∈ φ.toChart.source) {b : ℝ}
    (hb : φ.coord (φ.toChart z) = b • Pi.single j 1) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (X z) = -b • φ.coord.symm (Pi.single j 1) := by
  refine φ.coord.injective ?_
  rw [hφ z hz, hb, map_smul, LinearEquiv.apply_symm_apply]
  funext i
  by_cases hi : i = j
  · subst hi
    simp [hj]
  · simp [hi]

/-- **The stable comparison map near a critical point of index `n - 1`.** Let `z` be a point of
the Morse chart at `q` with linear forward flow at time `0` whose only nonzero coordinate is a
coordinate `b` of weight `1`, at which the chart preserves the orientations `oM` and `oE`. The map
`v ↦ (df_z v, N_q v)`, read through the chart, is an isomorphism `Ψ` of `E` with `ℝ × V_q` whose
second component is the coordinates of negative weight, and which sends the coordinate vector of
weight `1` to `(a, 0)` with `a` of the sign of `b`. -/
private theorem exists_linearEquiv_stableComparison {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1)
    {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    {oE₀ : Orientation ℝ E (Fin (finrank ℝ E))} (hoE : ∀ x, oE.orientationAt x = oE₀) {z : M}
    (hz : 0 ∈ hX.linearForwardTimes φ z) {b : ℝ} (hb : φ.coord (φ.toChart z) = b • Pi.single j 1)
    (hb0 : b ≠ 0) (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z ≠ 0)
    (hpres : oM.IsOrientationPreservingAt oE φ.toChart z)
    (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z))) :
    ∃ Ψ : E ≃ₗ[ℝ] ℝ × ({i // φ.weight i < 0} → ℝ),
      Orientation.map _
          (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z)).toLinearMap
            hA) (oM.orientationAt z) = Orientation.map _ Ψ oE₀ ∧
      (∀ u, (Ψ u).2 = φ.negativeCoord u) ∧
      ∃ a, Ψ (φ.coord.symm (Pi.single j 1)) = (a, 0) ∧ 0 < a * b := by
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 hpres
  have hsrc : z ∈ φ.toChart.source := by simpa using ((mem_linearForwardTimes hX φ).1 hz).1
  set 𝒜 :=
    LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z)).toLinearMap hA
  have he' (v : TangentSpace 𝓘(ℝ, E) z) : e v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v := by
    rw [← he, ContinuousLinearEquiv.coe_coe]
  set Ψ : E ≃ₗ[ℝ] ℝ × ({i // φ.weight i < 0} → ℝ) := e.symm.toLinearEquiv.trans 𝒜
  -- The two components of `Ψ` are `df` and the normal coordinates, after `e⁻¹`.
  have hΨ (u : E) : (Ψ u).1 = mvfderiv 𝓘(ℝ, E) f z (e.symm u) ∧
      (Ψ u).2 = hX.stableNormal φ z (e.symm u) := by
    -- `Ψ u` is `𝒜 (e⁻¹ u)`, reading `u : E` as a tangent vector of the model space `E` at `φ z`.
    change (𝒜 (e.symm u)).1 = _ ∧ (𝒜 (e.symm u)).2 = _
    simp only [𝒜, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.prod_apply, and_self]
  refine ⟨Ψ, ?_, fun u ↦ ?_, ?_⟩
  · -- Transport the orientation of `M` at `z` to that of `E` through the chart.
    have h1 : Orientation.map _ 𝒜 (oM.orientationAt z) = Orientation.map _
        (e.symm.toLinearEquiv.trans 𝒜) (oE.orientationAt (φ.toChart z)) := by
      rw [← hmap, ← Orientation.map_trans]
      congr 2
      refine LinearEquiv.ext fun v ↦ ?_
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      exact congrArg 𝒜 (e.symm_apply_apply v).symm
    -- `Ψ` is this transport, read on the tangent space `T_{φ z} E = E`.
    exact h1.trans (congrArg _ (hoE _))
  · rw [(hΨ u).2, stableNormal_apply_of_zero_mem hφ hz, ← he']
    exact congrArg φ.negativeCoord (e.apply_symm_apply u)
  · -- The coordinate vector of weight `1` is read back as `-1 / b` times the velocity.
    have hX' : e.symm (φ.coord.symm (Pi.single j 1)) = (-b⁻¹) • X z := by
      have h : e (X z) = -b • φ.coord.symm (Pi.single j 1) :=
        (he' _).trans (mfderiv_toChart_apply_eq_smul hφ hj hsrc hb)
      have h' : e ((-b⁻¹) • X z) = φ.coord.symm (Pi.single j 1) := by
        rw [map_smul, h]
        exact (smul_smul _ _ _).trans (by rw [neg_mul_neg, inv_mul_cancel₀ hb0]; exact one_smul _ _)
      rw [← h', e.symm_apply_apply]
    refine ⟨-b⁻¹ * mvfderiv 𝓘(ℝ, E) f z (X z), Prod.ext ?_ ?_, ?_⟩
    · rw [(hΨ _).1, hX', map_smul, smul_eq_mul]
    · rw [(hΨ _).2, stableNormal_apply_of_zero_mem hφ hz, ← he']
      -- `dsimp` reads the second component of `(a, 0)` as `0`.
      refine (congrArg φ.negativeCoord (e.apply_symm_apply _)).trans ?_
      dsimp only
      funext i
      rw [MorseChart.negativeCoord_apply, LinearEquiv.apply_symm_apply,
        Pi.single_eq_of_ne (fun h ↦ (lt_irrefl (0 : ℝ)) (by
          have := i.property
          rw [h, hj] at this
          linarith)), Pi.zero_apply]
    · have hdf := hX.mvfderiv_apply_lt_zero z hcrit
      rw [mul_comm, ← mul_assoc, mul_neg, mul_inv_cancel₀ hb0]
      linarith

/-- **The stable comparison maps on the two sides of a critical point of index `n - 1`.** At two
points `z₁`, `z₂` as in `exists_linearEquiv_stableComparison`, on opposite sides (`b₁ b₂ < 0`), the
maps `v ↦ (df_z v, N_q v)` carry the orientation of `M` to opposite orientations of `ℝ × V_q`. -/
private theorem map_stableComparison_eq_neg {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E)
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1)
    {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    {oE₀ : Orientation ℝ E (Fin (finrank ℝ E))} (hoE : ∀ x, oE.orientationAt x = oE₀) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hb : b₁ * b₂ < 0)
    (hcrit₁ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z₁ ≠ 0) (hcrit₂ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z₂ ≠ 0)
    (hpres₁ : oM.IsOrientationPreservingAt oE φ.toChart z₁)
    (hpres₂ : oM.IsOrientationPreservingAt oE φ.toChart z₂)
    (hA₁ : Bijective ((mvfderiv 𝓘(ℝ, E) f z₁).prod (hX.stableNormal φ z₁)))
    (hA₂ : Bijective ((mvfderiv 𝓘(ℝ, E) f z₂).prod (hX.stableNormal φ z₂))) :
    Orientation.map _
        (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z₂).prod (hX.stableNormal φ z₂)).toLinearMap
          hA₂) (oM.orientationAt z₂) =
      -Orientation.map _
        (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z₁).prod (hX.stableNormal φ z₁)).toLinearMap
          hA₁) (oM.orientationAt z₁) := by
  obtain ⟨Ψ₁, hΨ₁, hs₁, a₁, ha₁, hab₁⟩ := exists_linearEquiv_stableComparison hφ hj hoE h₁ hb₁
    (left_ne_zero_of_mul hb.ne) hcrit₁ hpres₁ hA₁
  obtain ⟨Ψ₂, hΨ₂, hs₂, a₂, ha₂, hab₂⟩ := exists_linearEquiv_stableComparison hφ hj hoE h₂ hb₂
    (right_ne_zero_of_mul hb.ne) hcrit₂ hpres₂ hA₂
  rw [hΨ₁, hΨ₂]
  -- `Ψ₂ = B ∘ Ψ₁`, where `B` fixes the second component and has determinant `a₂ / a₁ < 0`.
  set B := Ψ₁.symm.trans Ψ₂
  have hΨ : Ψ₂ = Ψ₁.trans B := LinearEquiv.ext fun u ↦ by simp [B]
  have hB (v : ℝ × ({i // φ.weight i < 0} → ℝ)) : (B v).2 = v.2 := by
    simp only [B, LinearEquiv.trans_apply]
    rw [hs₂, ← hs₁, Ψ₁.apply_symm_apply]
  have ha₁0 : a₁ ≠ 0 := left_ne_zero_of_mul hab₁.ne'
  have hB₁ : B (1, 0) = a₁⁻¹ • (a₂, 0) := by
    have hsymm : Ψ₁.symm (1, 0) = a₁⁻¹ • φ.coord.symm (Pi.single j 1) := by
      rw [LinearEquiv.symm_apply_eq, map_smul, ha₁, Prod.smul_mk, smul_eq_mul,
        inv_mul_cancel₀ ha₁0, smul_zero]
    simp only [B, LinearEquiv.trans_apply]
    rw [hsymm, map_smul, ha₂]
  have hdet : LinearMap.det B.toLinearMap < 0 := by
    rw [LinearMap.det_eq_fst_of_snd_eq _ hB, LinearEquiv.coe_coe, hB₁, Prod.smul_fst,
      smul_eq_mul]
    have : a₁ * a₂ < 0 := by nlinarith [mul_pos hab₁ hab₂]
    rw [show a₁⁻¹ * a₂ = a₁ * a₂ / (a₁ * a₁) by field_simp]
    exact div_neg_of_neg_of_pos this (mul_self_pos.2 ha₁0)
  rw [hΨ, Orientation.map_trans, Orientation.map_eq_neg_iff_det_neg _ _ ?_]
  · exact hdet
  · rw [Fintype.card_fin, φ.finrank_prod_negativeWeight_fun]
    omega

/-- **The stable comparison map along a trajectory from a critical point of top index.** At a
point `z` of a trajectory from a critical point `p` of index `n` to a critical point `q` of index
`n - 1`, the map `v ↦ (df_z v, N_q v)` is an isomorphism: it is the comparison map after the
inverse of the unstable frame of `p`. -/
theorem bijective_mvfderiv_prod_stableNormal (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source, φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source, φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)) := by
  obtain ⟨S, hS⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hz.1).exists
  refine (Bijective.of_comp_iff _ (bijective_unstableFrame hφp hp hS)).1 ?_
  convert bijective_trajectoryComparison hφp hφq hMS hf hpq hz using 1
  funext c
  rw [comp_apply, trajectoryComparison_apply, ContinuousLinearMap.prod_apply]

open scoped Classical in
/-- **A trajectory into a critical point of index `n - 1`, read against the orientation of `M`.**
Let `p` have index `n` and `q` index `n - 1`, and let `z` lie on a trajectory from `p` to `q`. The
sign of the trajectory, multiplied by the fundamental sign of `p`, is `1` exactly when the map
`v ↦ (df_z v, N_q v)` carries the orientation of `M` at `z` to the standard orientation of `ℝ`
followed by the orientation of the unstable manifold of `q`. -/
theorem fundamentalSign_mul_trajectorySign (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) {p q : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z))) :
    hX.fundamentalSign 𝔬 oM p * hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p)
        (𝔬.orientation q) hpq z =
      if Orientation.map _ (LinearEquiv.ofBijective
          ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z)).toLinearMap hA)
          (oM.orientationAt z) =
        ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod (𝔬.orientation q)
          (Module.finrank_self ℝ) (𝔬.chart q).finrank_negativeWeight_fun).reindex ℝ _
          (finCongr (by omega)) then 1 else -1 := by
  rw [fundamentalSign_of_morseIndex_eq hp, unstableOrientation_def]
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes (𝔬.coord_mfderiv_chart p) hf hz.1).exists
  have hF := bijective_unstableFrame (𝔬.coord_mfderiv_chart p) hp hT
  have hC := bijective_trajectoryComparison (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q)
    hMS hf hpq hz
  set 𝒜 := LinearEquiv.ofBijective
    ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z)).toLinearMap hA
  set 𝓕 := LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) z).toLinearMap hF
  -- The comparison map is the stable comparison map after the unstable frame.
  have hC𝓕 : LinearEquiv.ofBijective
      (hX.trajectoryComparison (𝔬.chart p) (𝔬.chart q) z).toLinearMap hC = 𝓕.trans 𝒜 :=
    LinearEquiv.ext fun c ↦ by
      simp [𝓕, 𝒜]
  -- Index all orientations by `Fin n`.
  set op := (𝔬.orientation p).reindex ℝ _ (finCongr hp)
  set τ := ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod (𝔬.orientation q)
    (Module.finrank_self ℝ) (𝔬.chart q).finrank_negativeWeight_fun).reindex ℝ _
    (finCongr (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f q = finrank ℝ E))
  have hτ : Orientation.map _ (LinearEquiv.ofBijective
      (hX.trajectoryComparison (𝔬.chart p) (𝔬.chart q) z).toLinearMap hC) (𝔬.orientation p) =
        (𝔬.chart q).trajectoryTargetOrientation (𝔬.orientation q) hpq ↔
      Orientation.map _ (𝓕.trans 𝒜) op = τ := by
    have hτp : τ = ((𝔬.chart q).trajectoryTargetOrientation (𝔬.orientation q) hpq).reindex ℝ _
        (finCongr hp) := by
      rw [MorseChart.trajectoryTargetOrientation_def, Orientation.reindex_finCongr_reindex_finCongr]
    rw [← hC𝓕, Orientation.map_reindex, hτp]
    exact (Orientation.reindex ℝ _ (finCongr hp)).injective.eq_iff.symm
  rw [trajectorySign_of_bijective hC,
    ← map_unstableFrame_eq_orientationAt_iff hf (𝔬.coord_mfderiv_chart p)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property) oM op hz.1 hF, if_congr hτ rfl rfl]
  refine Orientation.ite_map_mul_ite_map_trans 𝓕 𝒜 op (Fintype.card_fin _) ?_
  rw [Fintype.card_fin, (𝔬.chart q).finrank_prod_negativeWeight_fun]
  omega

/-! ### Trajectories on an oriented one-dimensional manifold -/

omit [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M] in
/-- On a manifold of dimension `1`, at a point `z` where `df_z` does not vanish, `df_z` does not
vanish on the vector of a basis of `T_z M`: it does not vanish on `X z`, a multiple of it. -/
private theorem mvfderiv_apply_ne_zero_of_finrank_eq_one (hX : IsAdaptedPseudoGradient f X)
    (hE : finrank ℝ E = 1) {z : M}
    (hz : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z ≠ 0)
    (b : Module.Basis (Fin (finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) z)) (k : Fin (finrank ℝ E)) :
    mvfderiv 𝓘(ℝ, E) f z (b k) ≠ 0 := by
  have : Unique (Fin (finrank ℝ E)) := by rw [hE]; infer_instance
  have hlt := hX.mvfderiv_apply_lt_zero z hz
  intro h0
  rw [← b.sum_repr (X z), Fintype.sum_unique, map_smul, Subsingleton.elim default k, h0,
    smul_zero] at hlt
  exact lt_irrefl 0 hlt

/-- On a manifold of dimension `1`, let `q` have index `0`, let the stable comparison map
`v ↦ (df_z v, N_q v)` at `z` be bijective, and let `B₀` be a basis of `ℝ × V`, for `V = 0` the
space of coordinates of negative weight at `q`, whose vectors have first coordinate `1`. Then the
stable comparison map carries the orientation of a basis `b` of `T_z M` to that of `B₀`, scaled by
the inverse of `d = df_z (b k)`. -/
private theorem map_orientation_stableComparison_eq (hE : finrank ℝ E = 1) {q : M}
    (φq : MorseChart E f q) (hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0) {z : M}
    (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)))
    (b : Module.Basis (Fin (finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) z)) (k : Fin (finrank ℝ E))
    (hd : mvfderiv 𝓘(ℝ, E) f z (b k) ≠ 0)
    (B₀ : Module.Basis (Fin (finrank ℝ E)) ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)))
    (hB₀ : ∀ j, (B₀ j).1 = 1) :
    Orientation.map _ (LinearEquiv.ofBijective
        ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)).toLinearMap hA) b.orientation =
      (Units.mk0 _ hd)⁻¹ • B₀.orientation := by
  have : Unique (Fin (finrank ℝ E)) := by rw [hE]; infer_instance
  have hsub : Subsingleton ({i // φq.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (φq.finrank_negativeWeight_fun.trans hq)
  -- The stable comparison map sends `b` to `d` times `B₀`.
  have hmap : b.map (LinearEquiv.ofBijective
      ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)).toLinearMap hA) =
      B₀.unitsSMul fun _ ↦ Units.mk0 _ hd := by
    refine Module.Basis.eq_of_apply_eq fun i ↦ Prod.ext ?_ (Subsingleton.elim _ _)
    obtain rfl : i = k := Subsingleton.elim _ _
    rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.prod_apply, Module.Basis.unitsSMul_apply, Units.smul_def,
      Units.val_mk0, Prod.smul_fst, hB₀, smul_eq_mul, mul_one]
  rw [← Module.Basis.orientation_map, hmap, Module.Basis.orientation_unitsSMul,
    Fintype.prod_unique]

/-- **The sign of a trajectory on an oriented one-dimensional manifold.** Let `M` have dimension
`1`, let `p` and `q` be critical points with `ind p = ind q + 1`, so of index `1` and `0`, and let
`z` lie on a trajectory from `p` to `q`. For a positive basis `b` of `T_z M`, the sign of the
trajectory, multiplied by the fundamental sign of `p`, is the augmentation sign of `q` times the
sign of `df_z (b k)`. So when `W^u(p)` is oriented like `M` and `q` positively, the trajectory
counts positively exactly when it runs against the orientation of `M`, along which `f` then
increases. -/
theorem fundamentalSign_mul_trajectorySign_of_finrank_eq_one (hf : IsMorse 𝓘(ℝ, E) f)
    (hE : finrank ℝ E = 1) (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (b : Module.Basis (Fin (finrank ℝ E)) ℝ (TangentSpace 𝓘(ℝ, E) z))
    (hb : b.orientation = oM.orientationAt z) (k : Fin (finrank ℝ E)) :
    hX.fundamentalSign 𝔬 oM p * hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p)
        (𝔬.orientation q) hpq z =
      𝔬.augmentationSign q * (SignType.sign (mvfderiv 𝓘(ℝ, E) f z (b k)) : ℤ) := by
  classical
  have hMS := hX.isMorseSmale_of_finrank_eq_one hf hE
  -- In dimension `1`, the source has index `1` and the target index `0`.
  have hp₁ : manifoldMorseIndex 𝓘(ℝ, E) f p ≤ finrank ℝ E := manifoldMorseIndex_le_finrank
  have hq : manifoldMorseIndex 𝓘(ℝ, E) f q = 0 := by omega
  have hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E := by omega
  have hA := bijective_mvfderiv_prod_stableNormal hMS hf (𝔬.coord_mfderiv_chart p)
    (𝔬.coord_mfderiv_chart q) hp hpq hz
  rw [fundamentalSign_mul_trajectorySign hMS hf 𝔬 oM hp hpq hz hA,
    𝔬.augmentationSign_of_morseIndex_eq_zero hq]
  have hd := mvfderiv_apply_ne_zero_of_finrank_eq_one hX hE
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet
      (fun he ↦ by rw [Subtype.ext he] at hpq; omega) hz) b k
  set d := mvfderiv 𝓘(ℝ, E) f z (b k)
  -- The target orientation is that of a basis `B₀` whose vectors are `(1, 0)`, or its reverse.
  obtain ⟨B₀, hB₀, hT⟩ := (𝔬.chart q).exists_basis_fst_eq_one_orientation_eq hq
    (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f q = finrank ℝ E)
  set b₀ := Module.finBasisOfFinrankEq ℝ _ (𝔬.chart q).finrank_negativeWeight_fun
  rw [← hb, map_orientation_stableComparison_eq hE (𝔬.chart q) hq hA b k hd B₀ hB₀]
  -- Compare the two orientations according to the signs of `d` and of the orientation at `q`.
  have hne := Module.Ray.ne_neg_self B₀.orientation
  rcases hd.lt_or_gt with hneg | hpos
  · rw [Module.Ray.units_smul_of_neg _ (by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact inv_lt_zero.2 hneg), sign_neg hneg]
    rcases b₀.orientation_eq_or_eq_neg (𝔬.orientation q) with ho | ho <;> rw [ho]
    · rw [hT]
      simp [hne.symm]
    · rw [Orientation.prod_neg_right, Orientation.reindex_neg, hT]
      simp
  · rw [Module.Ray.units_smul_of_pos _ (by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact inv_pos.2 hpos), sign_pos hpos]
    rcases b₀.orientation_eq_or_eq_neg (𝔬.orientation q) with ho | ho <;> rw [ho]
    · rw [hT]
      simp
    · rw [Orientation.prod_neg_right, Orientation.reindex_neg, hT]
      simp [hne]

/-! ### The fundamental chain is a cycle -/

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
include h hf

/-- **The two trajectories into a critical point of index `n - 1` cancel.** Let `q` have index
`n - 1`, and let `w 0`, `w 1` be points on two different trajectories into `q`, coming from
critical points `a 0`, `a 1` of index `n`. Weighted by the fundamental signs of their sources, the
two trajectories carry opposite signs. -/
private theorem fundamentalSign_mul_trajectorySign_eq_neg {q : criticalPoints 𝓘(ℝ, E) f}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E) {a : Fin 2 → criticalPoints 𝓘(ℝ, E) f}
    {w : Fin 2 → M}
    (hw : ∀ i, w i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q)
    (hw1 : w 1 ∉ hX.flow.orbit (w 0))
    (hpq : ∀ i, manifoldMorseIndex 𝓘(ℝ, E) f (a i) = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.fundamentalSign 𝔬 oM (a 1) * hX.trajectorySign (𝔬.chart (a 1)) (𝔬.chart q)
        (𝔬.orientation (a 1)) (𝔬.orientation q) (hpq 1) (w 1) =
      -(hX.fundamentalSign 𝔬 oM (a 0) * hX.trajectorySign (𝔬.chart (a 0)) (𝔬.chart q)
        (𝔬.orientation (a 0)) (𝔬.orientation q) (hpq 0) (w 0)) := by
  have ha (i : Fin 2) : manifoldMorseIndex 𝓘(ℝ, E) f (a i) = finrank ℝ E := (hpq i).trans hq
  set φ := 𝔬.chart q
  have hφ := 𝔬.coord_mfderiv_chart q
  obtain ⟨j, hj, hneg⟩ := φ.exists_weight_eq_one_of_add_one_eq_finrank hq
  -- An orientation of the model space for which the chart preserves orientations near `q`.
  obtain ⟨oE, hU⟩ := Manifold.Orientation.exists_eventually_isOrientationPreservingAt
    (contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one φ.mem_source)
    (isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source) oM
  have hoE (x : E) : oE.orientationAt x = oE.orientationAt 0 :=
    Manifold.Orientation.orientationAt_eq_orientationAt oE x 0
  have hne (i : Fin 2) : (a i : M) ≠ q := fun he ↦ by
    have := ha i
    rw [Subtype.coe_injective he] at this
    omega
  have hcrit (i : Fin 2) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (w i) ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hne i) (hw i)
  have hwq (i : Fin 2) : w i ≠ q := fun he ↦ hcrit i
    (he ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property)
  -- Flow both points close to `q`, into the normal form of the chart.
  choose T b h0 hpres hb0 hb using fun i ↦
    exists_flow_eq_smul_single hφ hneg (hw i).2 (hwq i) hU
  set z : Fin 2 → M := fun i ↦ hX.flow (T i) (w i)
  have hz (i : Fin 2) : z i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ _).2 (hw i).1, (Flow.apply_mem_stableSet_iff _ _).2 (hw i).2⟩
  have hcritz (i : Fin 2) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (z i) ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hne i) (hz i)
  have hA (i : Fin 2) :=
    bijective_mvfderiv_prod_stableNormal h hf (𝔬.coord_mfderiv_chart (a i)) hφ (ha i) (hpq i) (hz i)
  -- The two points are on opposite sides of `q`.
  have hz1 : z 1 ∉ hX.flow.orbit (z 0) := fun hmem ↦ hw1 (by
    obtain ⟨t, ht⟩ := (hX.flow.mem_orbit_iff).1 hmem
    refine (hX.flow.mem_orbit_iff).2 ⟨-T 1 + (t + T 0), ?_⟩
    simp only [z] at ht
    rw [Flow.map_add, Flow.map_add, ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply])
  have hbb := mul_neg_of_notMem_orbit hφ hj (h0 0) (h0 1) (hb0 0) (hb0 1) (hb 0) (hb 1) hz1
  have hflip := map_stableComparison_eq_neg hφ hq hj hoE (h0 0) (h0 1) (hb 0) (hb 1) hbb
    (hcritz 0) (hcritz 1) (hpres 0) (hpres 1) (hA 0) (hA 1)
  -- Each weighted sign compares the orientation of `M` with the same orientation of `ℝ × V_q`.
  rw [← trajectorySign_flow (𝔬.coord_mfderiv_chart (a 1)) hφ h hf (hw 1) (T 1),
    ← trajectorySign_flow (𝔬.coord_mfderiv_chart (a 0)) hφ h hf (hw 0) (T 0),
    fundamentalSign_mul_trajectorySign h hf 𝔬 oM (ha 1) (hpq 1) (hz 1) (hA 1),
    fundamentalSign_mul_trajectorySign h hf 𝔬 oM (ha 0) (hpq 0) (hz 0) (hA 0)]
  rw [hflip]
  refine Orientation.ite_neg_eq_eq_neg_ite ?_
  rw [Fintype.card_fin, φ.finrank_prod_negativeWeight_fun]
  omega


/-- **The boundary coefficients into a critical point, weighted by the fundamental signs, add up
to zero.** For every critical point `q`, the coefficients of `q` in the integral boundaries of the
critical points `p`, weighted by the fundamental signs of `p`, add up to zero. -/
theorem finsum_fundamentalSign_mul_signedMorseBoundaryCoeff (q : criticalPoints 𝓘(ℝ, E) f) :
    ∑ᶠ p, hX.fundamentalSign 𝔬 oM p * hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  rw [finsum_eq_sum_of_fintype]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E
  swap
  · -- Away from index `n - 1`, no critical point of index `n` reaches `q`.
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), mul_zero]
    · rw [fundamentalSign_of_morseIndex_ne hp, zero_mul]
  -- The two trajectories into `q` cross the middle levels at `w i` and start at `ac i`.
  obtain ⟨w, a, ha, hwmem, hw1, hwinj, hslice⟩ :=
    h.exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank hf
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hq
  set ac : Fin 2 → criticalPoints 𝓘(ℝ, E) f :=
    fun i ↦ ⟨a i, mem_criticalPoints_iff_mfderiv_eq_zero.2 (ha i).1⟩
  have hpq (i : Fin 2) : manifoldMorseIndex 𝓘(ℝ, E) f (ac i) =
      manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := (ha i).2.trans hq.symm
  set s : Fin 2 → ℤ := fun i ↦ hX.fundamentalSign 𝔬 oM (ac i) * hX.trajectorySign
    (𝔬.chart (ac i)) (𝔬.chart q) (𝔬.orientation (ac i)) (𝔬.orientation q) (hpq i) (w i)
  have hs : s 1 = -s 0 :=
    fundamentalSign_mul_trajectorySign_eq_neg h hf 𝔬 oM hq hwmem hw1 hpq
  -- The weighted coefficient of `q` in the boundary of `p` is the sum of the signs of the
  -- trajectories starting at `p`.
  have hp (p : criticalPoints 𝓘(ℝ, E) f) :
      hX.fundamentalSign 𝔬 oM p * hX.signedMorseBoundaryCoeff 𝔬 p q =
        ∑ i ∈ Finset.univ.filter (fun i ↦ ac i = p), s i := by
    by_cases hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
    swap
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpi, mul_zero, eq_comm]
      exact Finset.sum_eq_zero fun i hi ↦ absurd ((Finset.mem_filter.1 hi).2 ▸ hpq i) hpi
    have hne : (p : M) ≠ q := fun he ↦ by
      rw [Subtype.coe_injective he] at hpi
      omega
    rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpi, signedTrajectoryCount_def,
      hslice p hne, finsum_mem_image hwinj.injOn,
      finsum_mem_eq_finite_toFinset_sum _ (toFinite _), Finset.mul_sum]
    refine Finset.sum_congr (by ext; simp [ac, Subtype.ext_iff]) fun i hi ↦ ?_
    obtain rfl : ac i = p := by simpa [ac, Subtype.ext_iff] using hi
    rfl
  rw [Finset.sum_congr rfl fun p _ ↦ hp p, Finset.sum_fiberwise, Fin.sum_univ_two, hs,
    add_neg_cancel]

end IsMorseSmale

variable (hX) in
/-- The **fundamental chain** of the integral Morse complex with coefficients in a ring `R`, for
an orientation `oM` of `M`: the sum of the critical points of index `n = dim M`, each weighted by
its fundamental sign. -/
noncomputable def signedMorseFundamentalChain (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) (hf : IsMorse 𝓘(ℝ, E) f)
    (R : Type*) [Ring R] : criticalPoints 𝓘(ℝ, E) f →₀ R :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.ofSupportFinite (fun p ↦ (hX.fundamentalSign 𝔬 oM p : R)) (toFinite _)

variable (hf : IsMorse 𝓘(ℝ, E) f) {R : Type*} [Ring R]

/-- The coefficient of a critical point in the fundamental chain is its fundamental sign. -/
@[simp]
theorem signedMorseFundamentalChain_apply (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseFundamentalChain 𝔬 oM hf R p = hX.fundamentalSign 𝔬 oM p := by
  rw [signedMorseFundamentalChain, Finsupp.ofSupportFinite_coe]

/-- **Reversing the orientation of `M` negates the fundamental chain.** -/
@[simp]
theorem signedMorseFundamentalChain_neg :
    hX.signedMorseFundamentalChain 𝔬 (-oM) hf R = -hX.signedMorseFundamentalChain 𝔬 oM hf R := by
  ext p
  simp

/-- **Reversing orientations changes the fundamental chain by the sign reversal** of the chains on
the reversed set. -/
theorem signedMorseFundamentalChain_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] :
    hX.signedMorseFundamentalChain (𝔬.reverse S) oM hf R =
      Finsupp.signReversal R S (hX.signedMorseFundamentalChain 𝔬 oM hf R) := by
  ext p
  rw [signedMorseFundamentalChain_apply, Finsupp.signReversal_apply,
    signedMorseFundamentalChain_apply, fundamentalSign_reverse]
  by_cases hS : p ∈ S <;> simp [hS]

/-- **Change of coefficients.** A ring homomorphism `g : R → R'` sends the fundamental chain with
coefficients in `R` to that with coefficients in `R'`. -/
theorem mapRange_signedMorseFundamentalChain {R' F : Type*} [Ring R'] [FunLike F R R']
    [RingHomClass F R R'] (g : F) :
    Finsupp.mapRange g (map_zero g) (hX.signedMorseFundamentalChain 𝔬 oM hf R) =
      hX.signedMorseFundamentalChain 𝔬 oM hf R' := by
  ext p
  simp

/-- **With coefficients in `ZMod 2`, the fundamental chain is the mod-two fundamental chain**, the
sum of the critical points of top index, whatever the orientations. -/
theorem signedMorseFundamentalChain_eq_morseFundamentalChain :
    hX.signedMorseFundamentalChain 𝔬 oM hf (ZMod 2) = morseFundamentalChain hf := by
  ext p
  rw [signedMorseFundamentalChain_apply, intCast_fundamentalSign, morseFundamentalChain_apply]

/-- **The fundamental chain is a cycle.** For a Morse–Smale pseudo-gradient on a compact oriented
manifold, the integral Morse boundary of the sum of the critical points of top index, weighted by
their fundamental signs, is zero: `∂ [M] = 0`, with coefficients in any ring. -/
@[simp]
theorem IsMorseSmale.signedMorseBoundary_signedMorseFundamentalChain (h : hX.IsMorseSmale) :
    hX.signedMorseBoundary 𝔬 hf R (hX.signedMorseFundamentalChain 𝔬 oM hf R) = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  ext q
  have hsum := h.finsum_fundamentalSign_mul_signedMorseBoundaryCoeff hf 𝔬 oM q
  rw [finsum_eq_sum_of_fintype] at hsum
  rw [signedMorseBoundary_apply, Finsupp.zero_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [signedMorseFundamentalChain_apply]
  rw [← Int.cast_zero, ← hsum]
  push_cast
  -- The two sums differ only in the instance paths to multiplication and `Int.cast` in `R`.
  congr 1

end IsAdaptedPseudoGradient

end TauCeti

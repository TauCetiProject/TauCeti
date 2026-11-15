/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
import TauCeti.Dynamics.Flow.Basic
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import TauCeti.Geometry.Manifold.Morse.Stable.OneDimensional
import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import TauCeti.LinearAlgebra.Determinant.Prod
import TauCeti.LinearAlgebra.Ray

/-!
# The integral Morse boundary of a critical point of index one

Let `f` be a Morse function on a compact boundaryless manifold, `X` a Morse–Smale pseudo-gradient
adapted to `f`, and `p` a critical point of index `1`. The unstable manifold `W^u(p)` is a line
through `p`, and `W^u(p) - {p}` consists of two trajectories, leaving `p` in opposite directions.
This file shows that, for any orientation of `W^u(p)`, these two trajectories carry opposite signs
in the integral Morse boundary when they end at the same critical point `q` of index `0`
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_eq_neg_of_notMem_orbit`), so that they cancel:
the coefficient of `q` in the integral boundary of `p` is zero
(`TauCeti.IsAdaptedPseudoGradient.signedTrajectoryCount_eq_zero_of_unstableSet_diff_subset`).
This is the integral refinement of the mod-two count of two trajectories, which only gives a
coefficient divisible by two.

In particular, if `f` has a single critical point `m` of index `0`, then `m` has coefficient zero in
the integral boundary of every chain (in the namespace
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`,
`signedMorseBoundary_apply_eq_zero_of_unique_index_zero`): every critical point of index `1` is
an integral cycle. For the sphere with two maxima, one saddle and one minimum, this is the
vanishing of the boundary of the saddle; for the moment function on the real projective plane it
is the vanishing of the differential from degree `1` to degree `0`.

The orientation of the trajectory through a point `y` compares an orientation of the line
`T_y W^u(p)`, transported from `p` by the unstable frame, with the direction `-X y` in which `f`
increases. Near `p` the frame is read in a Morse chart `φ` in which `X` is linear: the velocity
`X y` is the unstable frame on the coordinates of negative weight of `y`
(`TauCeti.IsAdaptedPseudoGradient.unstableFrame_negativeCoord_toChart`). The two trajectories
leaving `p` are the two half-lines of the coordinate line of negative weight, on which this
coordinate has opposite signs, so the velocities of the two trajectories correspond to opposite
vectors of the frame. Since the signs do not change along the flow, they are opposite everywhere.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `unstableFrame_negativeCoord_toChart`: near the critical point, the velocity is the unstable
  frame on the coordinates of negative weight.
* `trajectorySign_eq_neg_of_notMem_orbit`: two distinct trajectories from a critical point of index
  `1` to a critical point of index `0` have opposite signs.
* `signedTrajectoryCount_eq_zero_of_unstableSet_diff_subset`: if both trajectories leaving a
  critical point `p` of index `1` end at `q`, the signed count of the trajectories from `p` to `q`
  is `0`.
* `IsMorseSmale.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero` and
  `IsMorseSmale.signedMorseBoundary_apply_eq_zero_of_unique_index_zero`: the only critical point
  of index `0` has coefficient zero in every integral boundary.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (signs of flow lines, and the Morse complex of the sphere
  with two maxima).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients and its homology in degree `0`).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

/-! ### The unstable manifold near the critical point -/

section Local

variable {hX : IsAdaptedPseudoGradient f X} {x : M} {φ : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
include hφ

/-- **The velocity in the unstable frame.** At a point `y` of `W^u(x)` whose backward orbit stays
in the linear part of the Morse chart `φ` from the time `0` on, the unstable frame of `φ` sends the
coordinates of negative weight of `y` to the velocity `X y`. -/
theorem unstableFrame_negativeCoord_toChart (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) (h₀ : 0 ∈ hX.linearBackwardTimes φ y) :
    hX.unstableFrame φ y (φ.negativeCoord (φ.toChart y)) = X y := by
  -- The velocity, read as a vector `w` of the model space `E`, is tangent to `W^u(x)`, so it is
  -- the frame on some coordinates `c`.
  obtain ⟨w, hw⟩ : ∃ w : E, X y = w := ⟨_, rfl⟩
  have hXy : w ∈ Submodule.span ℝ (mtangentConeAt 𝓘(ℝ, E) (hX.flow.unstableSet x) y) :=
    hw ▸ Submodule.subset_span
      (hX.mem_mtangentConeAt_of_isInvariant (hX.flow.isInvariant_unstableSet x) hy)
  obtain ⟨c, hc⟩ := (Set.ext_iff.1 (hX.range_unstableFrame hφ hf hy) w).2 hXy
  rw [← hw] at hc
  -- Reading both sides in the chart, `c` are the coordinates of negative weight of `y`.
  have hd := hX.mfderiv_unstableFrame hφ h₀ c
  rw [neg_zero, Flow.map_zero, comp_id, Real.exp_zero, one_smul, hc] at hd
  have hsrc : y ∈ φ.toChart.source := by
    simpa using ((hX.mem_linearBackwardTimes φ).1 h₀).1
  suffices φ.negativeCoord (φ.toChart y) = c by rw [this, hc]
  funext i
  have hi : φ.weight i = -1 :=
    (φ.weight_eq_neg_one_or_eq_one i).resolve_right fun h ↦ by linarith [i.2]
  have h := congrFun (hφ y hsrc) i
  rw [hd, φ.coord_negativeExtend_of_weight_neg, hi] at h
  rw [MorseChart.negativeCoord_apply, h]
  ring

/-- Close to `x`, two points of `W^u(x)` whose coordinates of negative weight are positive multiples
of each other lie on a common orbit: the coordinates of positive weight vanish on `W^u(x)` near `x`,
and the backward flow there multiplies the coordinates by `e^{-t}`. -/
private theorem exists_forall_mem_orbit_of_negativeCoord_eq_smul (hf : IsMorse 𝓘(ℝ, E) f) :
    ∃ ρ > 0, ∀ y₁ ∈ hX.flow.unstableSet x, ∀ y₂ ∈ hX.flow.unstableSet x,
      y₁ ∈ φ.toChart.source → y₂ ∈ φ.toChart.source →
      ‖φ.coord (φ.toChart y₁)‖ < ρ → ‖φ.coord (φ.toChart y₂)‖ < ρ → ∀ a : ℝ, 0 < a →
      φ.negativeCoord (φ.toChart y₂) = a • φ.negativeCoord (φ.toChart y₁) →
      y₂ ∈ hX.flow.orbit y₁ := by
  -- The local description of `W^u(x)` and of the backward flow on it, from the reversed flow.
  have hnd := hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl)
  have hφ' := φ.coord_mfderiv_neg hφ hnd
  obtain ⟨ρu, hρu, hu⟩ := (hX.neg hf).exists_forall_mem_stableSet_iff (φ.neg hnd) hφ'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, MorseChart.neg_weight, Pi.neg_apply,
    Left.neg_neg_iff, ← hX.unstableSet_eq_stableSet_neg hf] at hu
  obtain ⟨ρc, hρc, hc⟩ := (hX.neg hf).exists_forall_coord_flow_eq_exp_smul (φ.neg hnd) hφ'
  simp only [MorseChart.neg_toChart, MorseChart.neg_coord, hX.neg_flow hf, Flow.stableSet_reverse,
    Flow.reverse_apply] at hc
  set ρ := min ρu ρc
  -- Near `x`, a point of `W^u(x)` is determined by its coordinates of negative weight.
  have hcoord {y : M} (hy : y ∈ hX.flow.unstableSet x) (hys : y ∈ φ.toChart.source)
      (hyρ : ‖φ.coord (φ.toChart y)‖ < ρ) :
      φ.negativeExtend (φ.negativeCoord (φ.toChart y)) = φ.toChart y :=
    φ.negativeExtend_negativeCoord fun i hi ↦ (hu y hys (hyρ.trans_le (min_le_left _ _))).1 hy i
      (by
        rcases φ.weight_eq_neg_one_or_eq_one i with h | h
        · rw [h] at hi
          norm_num at hi
        · rw [h]
          exact one_pos)
  -- For a factor `a ≤ 1`, flowing `y₁` backwards for the time `-log a` reaches `y₂`.
  have key {y₁ y₂ : M} (hy₁ : y₁ ∈ hX.flow.unstableSet x) (hy₂ : y₂ ∈ hX.flow.unstableSet x)
      (hys₁ : y₁ ∈ φ.toChart.source) (hys₂ : y₂ ∈ φ.toChart.source)
      (hρ₁ : ‖φ.coord (φ.toChart y₁)‖ < ρ) (hρ₂ : ‖φ.coord (φ.toChart y₂)‖ < ρ) {a : ℝ}
      (ha : 0 < a) (ha1 : a ≤ 1)
      (h12 : φ.negativeCoord (φ.toChart y₂) = a • φ.negativeCoord (φ.toChart y₁)) :
      hX.flow (Real.log a) y₁ = y₂ := by
    obtain ⟨hsrc, hflow⟩ := hc y₁ hy₁ hys₁ (hρ₁.trans_le (min_le_right _ _)) (-Real.log a)
      (neg_nonneg.2 (Real.log_nonpos ha.le ha1))
    rw [neg_neg] at hsrc
    rw [neg_neg, Real.exp_log ha] at hflow
    refine φ.toChart.injOn hsrc hys₂ (φ.coord.injective ?_)
    rw [hflow, ← hcoord hy₂ hys₂ hρ₂, h12, map_smul, map_smul, hcoord hy₁ hys₁ hρ₁]
  refine ⟨ρ, lt_min hρu hρc, fun y₁ hy₁ y₂ hy₂ hys₁ hys₂ hρ₁ hρ₂ a ha h12 ↦ ?_⟩
  rcases le_total a 1 with ha1 | ha1
  · exact hX.flow.mem_orbit_iff.2 ⟨_, key hy₁ hy₂ hys₁ hys₂ hρ₁ hρ₂ ha ha1 h12⟩
  · have h21 : φ.negativeCoord (φ.toChart y₁) = a⁻¹ • φ.negativeCoord (φ.toChart y₂) := by
      rw [h12, smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    have h := key hy₂ hy₁ hys₂ hys₁ hρ₂ hρ₁ (inv_pos.2 ha) (inv_le_one_of_one_le₀ ha1) h21
    exact hX.flow.mem_orbit_iff.2
      ⟨-Real.log a⁻¹, by rw [← h, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]⟩

end Local

/-! ### Opposite signs of the two trajectories leaving a critical point of index one -/

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp : MorseChart E f p}
  {φq : MorseChart E f q}
  {op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p))}
  {oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q))}
  {hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
include hφp hφq

/-- From a critical point of index `1` to one of index `0`, if the velocities at two points of
trajectories are the unstable frame on opposite vectors `c₁` and `c₂ = a • c₁`, `a < 0`, then the
two signs are opposite: the comparison maps at the two points differ by a map of the line `ℝ` of
negative determinant. -/
private theorem trajectorySign_eq_neg_of_unstableFrame_eq_smul (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) {c₁ c₂ : {i // φp.weight i < 0} → ℝ}
    (hc₁ : hX.unstableFrame φp y₁ c₁ = X y₁) (hc₂ : hX.unstableFrame φp y₂ c₂ = X y₂) {a : ℝ}
    (ha : a < 0) (h12 : c₂ = a • c₁) :
    hX.trajectorySign φp φq op oq hpq y₂ = -hX.trajectorySign φp φq op oq hpq y₁ := by
  have hne : p ≠ q := by rintro rfl; omega
  -- The space of coordinates of negative weight at `q` is zero-dimensional.
  have : Subsingleton ({i // φq.weight i < 0} → ℝ) :=
    Module.finrank_zero_iff.1 (by rw [φq.finrank_negativeWeight_fun]; omega)
  have hC₁ := bijective_trajectoryComparison hφp hφq hMS hf hpq hy₁
  have hC₂ := bijective_trajectoryComparison hφp hφq hMS hf hpq hy₂
  rw [trajectorySign_of_bijective hC₁, trajectorySign_of_bijective hC₂]
  set e₁ := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y₁).toLinearMap hC₁
  set e₂ := LinearEquiv.ofBijective (hX.trajectoryComparison φp φq y₂).toLinearMap hC₂
  -- The comparison maps send `c₁` and `c₂` to `(d₁, 0)` and `(d₂, 0)` with `dᵢ = df(X yᵢ) < 0`.
  set d₁ := mvfderiv 𝓘(ℝ, E) f y₁ (X y₁)
  set d₂ := mvfderiv 𝓘(ℝ, E) f y₂ (X y₂)
  have hd₁ : d₁ < 0 := hX.mvfderiv_apply_lt_zero y₁
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy₁)
  have hd₂ : d₂ < 0 := hX.mvfderiv_apply_lt_zero y₂
    (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hy₂)
  have he₁ : e₁ c₁ = (d₁, 0) := by
    rw [LinearEquiv.ofBijective_apply]
    exact Prod.ext (by simp [hc₁, d₁]) (Subsingleton.elim _ _)
  have he₂ : (e₂ c₁).1 = a⁻¹ * d₂ := by
    have hc : c₁ = a⁻¹ • c₂ := by rw [h12, smul_smul, inv_mul_cancel₀ ha.ne, one_smul]
    rw [LinearEquiv.ofBijective_apply, hc, map_smul, Prod.smul_fst, ContinuousLinearMap.coe_coe,
      trajectoryComparison_apply, hc₂, smul_eq_mul]
  -- So `e₂ = e₁ ∘ B` for an automorphism `B` of `ℝ × 0` of negative determinant.
  set B := e₁.symm.trans e₂
  have hB : LinearMap.det (B : (ℝ × ({i // φq.weight i < 0} → ℝ)) →ₗ[ℝ]
      ℝ × ({i // φq.weight i < 0} → ℝ)) < 0 := by
    rw [LinearMap.det_eq_fst_of_snd_eq _ fun _ ↦ Subsingleton.elim _ _]
    have h10 : ((1 : ℝ), (0 : {i // φq.weight i < 0} → ℝ)) = d₁⁻¹ • e₁ c₁ := by
      rw [he₁]
      exact Prod.ext (by simp [hd₁.ne]) (Subsingleton.elim _ _)
    rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, h10, map_smul, e₁.symm_apply_apply,
      map_smul, Prod.smul_fst, he₂, smul_eq_mul]
    have : 0 < d₁⁻¹ * a⁻¹ := mul_pos_of_neg_of_neg (inv_lt_zero.2 hd₁) (inv_lt_zero.2 ha)
    nlinarith
  have hcard : Fintype.card (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)) =
      Module.finrank ℝ (ℝ × ({i // φq.weight i < 0} → ℝ)) := by
    rw [Fintype.card_fin, Module.finrank_prod, Module.finrank_self, φq.finrank_negativeWeight_fun]
    omega
  have hmap : Orientation.map _ e₂ op = -Orientation.map _ e₁ op := by
    have hee : e₂ = e₁.trans B := LinearEquiv.ext fun v ↦ by
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, e₁.symm_apply_apply]
    rw [hee, Orientation.map_trans]
    exact ((Orientation.map _ e₁ op).map_eq_neg_iff_det_neg B hcard).2 hB
  rw [hmap]
  generalize Orientation.map _ e₁ op = o
  rcases φq.eq_or_eq_neg_trajectoryTargetOrientation (oq := oq) (hpq := hpq) o with rfl | rfl
  · simp [(Module.Ray.ne_neg_self _).symm]
  · simp [(Module.Ray.ne_neg_self _).symm, Module.Ray.neg_neg]

/-- **Two trajectories leaving a critical point of index one have opposite signs.** Let `p` be a
critical point of index `1` and `q` one of index `0`. If `y₁` and `y₂` lie on trajectories from `p`
to `q`, and `y₂` is not on the trajectory through `y₁`, then the trajectories through `y₁` and `y₂`
have opposite signs, for any orientations of the unstable manifolds. They are the two halves of
`W^u(p) - {p}`, leaving `p` in opposite directions. -/
theorem trajectorySign_eq_neg_of_notMem_orbit (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1) {y₁ y₂ : M}
    (hy₁ : y₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hy₂ : y₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) (h12 : y₂ ∉ hX.flow.orbit y₁) :
    hX.trajectorySign φp φq op oq hpq y₂ = -hX.trajectorySign φp φq op oq hpq y₁ := by
  have hne : p ≠ q := by rintro rfl; omega
  obtain ⟨ρ, hρ, horbit⟩ := exists_forall_mem_orbit_of_negativeCoord_eq_smul hφp hf
  -- Move both points backwards by a common time `T`, close to `p`, in the linear part of `φp`.
  have hnear : ∀ᶠ z in 𝓝 p, z ∈ φp.toChart.source ∧ ‖φp.coord (φp.toChart z)‖ < ρ := by
    have hc : ContinuousAt (fun z ↦ ‖φp.coord (φp.toChart z)‖) p :=
      (φp.continuous_coord.continuousAt.comp (φp.toChart.continuousAt φp.mem_source)).norm
    exact (φp.toChart.open_source.eventually_mem φp.mem_source).and
      (hc.eventually_lt continuousAt_const (by simpa using hρ))
  have hev (y : M) (hy : y ∈ hX.flow.unstableSet p) : ∀ᶠ T in atTop,
      T ∈ hX.linearBackwardTimes φp y ∧ hX.flow (-T) y ∈ φp.toChart.source ∧
        ‖φp.coord (φp.toChart (hX.flow (-T) y))‖ < ρ :=
    (hX.eventually_mem_linearBackwardTimes hφp hf hy).and
      (((Flow.mem_unstableSet.1 hy).comp tendsto_neg_atTop_atBot).eventually
        hnear)
  obtain ⟨T, ⟨hT₁, hs₁, hρ₁⟩, hT₂, hs₂, hρ₂⟩ := ((hev y₁ hy₁.1).and (hev y₂ hy₂.1)).exists
  set u₁ := hX.flow (-T) y₁
  set u₂ := hX.flow (-T) y₂
  have hu (y : M) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
      hX.flow (-T) y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hy.1, (Flow.apply_mem_stableSet_iff _ _).2 hy.2⟩
  have h0 {y : M} (hT : T ∈ hX.linearBackwardTimes φp y) :
      0 ∈ hX.linearBackwardTimes φp (hX.flow (-T) y) :=
    mem_linearBackwardTimes_flow.2 (by rwa [zero_sub, neg_neg])
  -- At `uᵢ`, the velocity is the unstable frame on the coordinates `cᵢ` of negative weight.
  set c₁ := φp.negativeCoord (φp.toChart u₁)
  set c₂ := φp.negativeCoord (φp.toChart u₂)
  have hc₁ : hX.unstableFrame φp u₁ c₁ = X u₁ :=
    unstableFrame_negativeCoord_toChart hφp hf (hu y₁ hy₁).1 (h0 hT₁)
  have hc₂ : hX.unstableFrame φp u₂ c₂ = X u₂ :=
    unstableFrame_negativeCoord_toChart hφp hf (hu y₂ hy₂).1 (h0 hT₂)
  have hX0 {u : M} (hu : u ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) : X u ≠ 0 :=
    hX.ne_zero_of_mfderiv_ne_zero (hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet hne hu)
  have hc₁0 : c₁ ≠ 0 := fun h ↦ hX0 (hu y₁ hy₁) (by rw [← hc₁, h, map_zero])
  have hc₂0 : c₂ ≠ 0 := fun h ↦ hX0 (hu y₂ hy₂) (by rw [← hc₂, h, map_zero])
  -- These coordinates lie on a line, so `c₂ = a • c₁`, and `a > 0` would put `u₂` on the orbit of
  -- `u₁`.
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_ne_zero' c₁ hc₁0).1
    (by rw [φp.finrank_negativeWeight_fun, hp]) c₂
  have ha0 : a < 0 := by
    refine lt_of_le_of_ne (not_lt.1 fun ha0 ↦ h12 ?_) fun h ↦ hc₂0 (by rw [← ha, h, zero_smul])
    have h := horbit u₁ (hu y₁ hy₁).1 u₂ (hu y₂ hy₂).1 hs₁ hs₂ hρ₁ hρ₂ a ha0 ha.symm
    rw [Flow.orbit_apply] at h
    simpa [u₂] using hX.flow.mem_orbit_of_mem_orbit T h
  rw [← trajectorySign_flow hφp hφq hMS hf hy₁ (-T), ← trajectorySign_flow hφp hφq hMS hf hy₂ (-T)]
  exact trajectorySign_eq_neg_of_unstableFrame_eq_smul hφp hφq hMS hf hp (hu y₁ hy₁) (hu y₂ hy₂)
    hc₁ hc₂ ha0 ha.symm

/-- **The two trajectories leaving a critical point of index one cancel at a common end.** Let `p`
be a critical point of index `1` and `q` one of index `0`. If every point of `W^u(p)` other than `p`
flows to `q`, then the two trajectories from `p` to `q` have opposite signs, so their signed count
is `0`, for any orientations of the unstable manifolds. -/
theorem signedTrajectoryCount_eq_zero_of_unstableSet_diff_subset (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = 1)
    (hW : hX.flow.unstableSet p \ {p} ⊆ hX.flow.stableSet q) :
    hX.signedTrajectoryCount φp φq op oq hpq = 0 := by
  have hne : p ≠ q := by rintro rfl; omega
  -- `W^u(p) - {p}` consists of the orbits of two points `y₁` and `y₂`.
  obtain ⟨y₁, y₂, hy₁p, hy₂p, hdisj, hWu⟩ := hX.exists_unstableSet_eq_insert_union_orbit hf
    ((φp.mfderiv_eq_zero_iff φp.mem_source).2 rfl) hp
  have hmem {y : M} (hyp : y ≠ p) (hy : y ∈ hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) :
      y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    have hyu : y ∈ hX.flow.unstableSet p := hWu ▸ mem_insert_of_mem _ hy
    ⟨hyu, hW ⟨hyu, hyp⟩⟩
  have hy₁ := hmem hy₁p (Or.inl (Flow.mem_orbit_self _ _))
  have hy₂ := hmem hy₂p (Or.inr (Flow.mem_orbit_self _ _))
  have hval := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hne hy₁
  -- Each orbit crosses the middle level exactly once, at `zᵢ`.
  obtain ⟨τ₁, hτ₁, hτ₁u⟩ :=
    hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hne hy₁
  obtain ⟨τ₂, hτ₂, hτ₂u⟩ :=
    hX.existsUnique_flow_eq_midpoint_of_mem_unstableSet_inter_stableSet hne hy₂
  set z₁ := hX.flow τ₁ y₁
  set z₂ := hX.flow τ₂ y₂
  have hz₁ : z₁ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hy₁.1, (Flow.apply_mem_stableSet_iff _ _).2 hy₁.2⟩
  have hz₂ : z₂ ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ _).2 hy₂.1, (Flow.apply_mem_stableSet_iff _ _).2 hy₂.2⟩
  have hz₂₁ : z₂ ∉ hX.flow.orbit z₁ := by
    rw [Flow.orbit_apply]
    exact disjoint_right.1 hdisj (Flow.mem_orbit _ _ _)
  have hslice : hX.morseTrajectorySlice p q = {z₁, z₂} := by
    ext w
    simp only [mem_morseTrajectorySlice, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun hw ↦ ?_, ?_⟩
    · obtain ⟨hwu, -, hwc⟩ := hw
      have hwp : w ≠ p := by rintro rfl; linarith [hval.1, hval.2]
      rcases (by simpa [hWu, hwp] using hwu : w ∈ hX.flow.orbit y₁ ∪ hX.flow.orbit y₂) with
        hw | hw
      · obtain ⟨t, rfl⟩ := hX.flow.mem_orbit_iff.1 hw
        exact Or.inl (by rw [hτ₁u t hwc])
      · obtain ⟨t, rfl⟩ := hX.flow.mem_orbit_iff.1 hw
        exact Or.inr (by rw [hτ₂u t hwc])
    · rintro (rfl | rfl)
      exacts [⟨hz₁.1, hz₁.2, hτ₁⟩, ⟨hz₂.1, hz₂.2, hτ₂⟩]
  have hz : z₁ ≠ z₂ := fun h ↦ hz₂₁ (h ▸ Flow.mem_orbit_self _ _)
  rw [signedTrajectoryCount_def, hslice, finsum_mem_pair hz,
    trajectorySign_eq_neg_of_notMem_orbit hφp hφq hMS hf hp hz₁ hz₂ hz₂₁, add_neg_cancel]

omit hφp hφq

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
include h hf

/-- **No integral boundary reaches a unique critical point of index zero.** If `m` is the only
critical point of index `0`, then its coefficient in the integral Morse boundary of every critical
point vanishes, for any orientation data: both trajectories leaving a critical point of index `1`
end at `m`, with opposite signs. -/
theorem signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero {m : criticalPoints 𝓘(ℝ, E) f}
    (hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (q : criticalPoints 𝓘(ℝ, E) f) : hX.signedMorseBoundaryCoeff 𝔬 q m = 0 := by
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f m + 1
  · rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hind]
    refine signedTrajectoryCount_eq_zero_of_unstableSet_diff_subset (𝔬.coord_mfderiv_chart q)
      (𝔬.coord_mfderiv_chart m) h hf (by omega) fun y ⟨hyu, hyq⟩ ↦ ?_
    -- Every trajectory out of `q` goes to a critical point of index `0`, hence to `m`.
    obtain ⟨m', hm', hym'⟩ := mem_iUnion₂.1 ((hX.iUnion_stableSet hf).symm ▸ mem_univ y :
      y ∈ ⋃ x ∈ {x : M | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0}, hX.flow.stableSet x)
    have hqm' : (q : M) ≠ m' := by
      rintro rfl
      exact hyq (hX.eq_of_mem_unstableSet_inter_stableSet ⟨hyu, hym'⟩)
    have hlt := h.manifoldMorseIndex_lt hf hqm' ⟨y, hyu, hym'⟩
    rwa [← huniq m' hm' (by omega)]
  · exact signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hind

/-- **A unique critical point of index zero is not hit by the integral boundary.** If `m` is the
only critical point of index `0`, then the coefficient of `m` in the Morse boundary of every chain
with coefficients in a ring `R` vanishes, for any orientation data. -/
theorem signedMorseBoundary_apply_eq_zero_of_unique_index_zero {R : Type*} [Ring R]
    {m : criticalPoints 𝓘(ℝ, E) f} (hm : manifoldMorseIndex 𝓘(ℝ, E) f m = 0)
    (huniq : ∀ y, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f y = 0 → manifoldMorseIndex 𝓘(ℝ, E) f y = 0 → y = m)
    (c : criticalPoints 𝓘(ℝ, E) f →₀ R) : hX.signedMorseBoundary 𝔬 hf R c m = 0 := by
  simp [signedMorseBoundary_apply,
    h.signedMorseBoundaryCoeff_eq_zero_of_unique_index_zero hf 𝔬 hm huniq]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti

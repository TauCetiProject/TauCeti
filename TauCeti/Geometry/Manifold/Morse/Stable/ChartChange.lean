/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Changing the Morse chart of the unstable frame and the normal coordinates

Let `X` be a pseudo-gradient adapted to `f` on a compact manifold, and `φ`, `φ'` two Morse charts at
the same critical point `x` in both of which `X` is the linear field `z ↦ (-wᵢ zᵢ)ᵢ`. Write `V` and
`V'` for their spaces of coordinates of negative weight. Each chart gives an unstable frame
`hX.unstableFrame φ y : V → T_y M` of `W^u(x)` and normal coordinates
`hX.stableNormal φ y : T_y M → V` of `W^s(x)`
(`TauCeti.Geometry.Manifold.Morse.Stable.Frame`). This file shows that the two charts give the same
frames and normal coordinates up to one fixed linear isomorphism `V → V'`, the **change of negative
coordinates** `φ.negativeChange φ'`: a vector with coordinates `c` of negative weight and `0` of
positive weight in `φ` is carried by the derivative at `0` of the transition map `φ' ∘ φ⁻¹`, and
`φ.negativeChange φ' c` are the coordinates of negative weight of the result in `φ'`. This map is
defined for any two Morse charts at `x`, and it is an isomorphism because the derivative of the
transition map preserves the Hessian of `f`.

* `hX.unstableFrame φ' y (φ.negativeChange φ' c) = hX.unstableFrame φ y c` for `y ∈ W^u(x)`;
* `φ.negativeChange φ' (hX.stableNormal φ y v) = hX.stableNormal φ' y v` for `y ∈ W^s(x)`.

So an orientation of `V` and its image under `φ.negativeChange φ'` orient the tangent spaces of
`W^u(x)` and the normal spaces of `W^s(x)` in the same way at every point: the orientations
built from Morse charts depend only on the orientation of the tangent space of `W^u(x)` at `x`
which the chart induces. For three Morse charts in which `X` is linear, the changes of negative
coordinates compose. The signs of the trajectories counted by the integral Morse differential are
therefore independent of the choice of the Morse charts
(`TauCeti.IsAdaptedPseudoGradient.trajectorySign_map_negativeChange`).

Near `x`, where the flow is linear in both charts, the frame of `φ` is the inverse of the derivative
of `φ` on the vectors of negative weight, and similarly for `φ'`. There, comparing the two frames
or the two normal coordinates is reading the derivative of the transition map `φ' ∘ φ⁻¹` at the
image of the point, on the vectors of negative weight. Along the flow both frames, and both normal
coordinates, are rescaled by the same factors (`TauCeti.IsAdaptedPseudoGradient.unstableFrame_flow`
and `TauCeti.IsAdaptedPseudoGradient.stableNormal_mfderiv_flow`), so for every point of `W^u(x)`,
respectively `W^s(x)`, the comparison at the points of its backward, respectively forward, orbit is
the same for all large times. These points converge to `x`, and the derivative of the transition
map is continuous, so this comparison is the one at `x`, which is `φ.negativeChange φ'`.

## Main definitions

* `TauCeti.MorseChart.negativeChange`: the change of negative coordinates between two Morse charts
  at the same point, a linear isomorphism.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `unstableFrame_negativeChange`: the unstable frames of two Morse charts differ by the change of
  negative coordinates.
* `negativeChange_stableNormal`: so do the normal coordinates of the stable manifold.
* `negativeChange_trans_negativeChange`: for three Morse charts in which `X` is linear, the changes
  of negative coordinates compose.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (orientations of the unstable manifolds and the Morse complex with integer
  coefficients).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace MorseChart

variable (φ φ' : MorseChart E f x)

/-- The change of negative coordinates read at the image of a point `z` instead of at `0`: the
coordinates of negative weight in `φ'` of the image of a vector of negative weight in `φ` under the
derivative of the transition map `φ' ∘ φ⁻¹` at `φ z`. -/
private noncomputable def negativeChangeAt (z : M) :
    ({i // φ.weight i < 0} → ℝ) →L[ℝ] ({i // φ'.weight i < 0} → ℝ) :=
  (LinearMap.toContinuousLinearMap φ'.negativeCoord).comp
    ((fderiv ℝ (φ.toChart.symm.trans φ'.toChart) (φ.toChart z)).comp
      (LinearMap.toContinuousLinearMap φ.negativeExtend))

private theorem negativeChangeAt_apply (z : M) (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeChangeAt φ' z c = φ'.negativeCoord
      (fderiv ℝ (φ.toChart.symm.trans φ'.toChart) (φ.toChart z) (φ.negativeExtend c)) :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- The centre `0` of `φ` lies in the source of the transition map `φ' ∘ φ⁻¹`. -/
private theorem zero_mem_transition_source :
    (0 : E) ∈ (φ.toChart.symm.trans φ'.toChart).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact ⟨by simpa using φ.toChart.map_source φ.mem_source, by simp⟩

omit [FiniteDimensional ℝ E] in
/-- Near `0`, the transition map `φ' ∘ φ⁻¹` carries the quadratic normal form of `φ'` to that
of `φ`: both read `f` in the charts. -/
private theorem quadratic_comp_transition :
    φ'.quadratic ∘ (φ.toChart.symm.trans φ'.toChart) =ᶠ[𝓝 0] φ.quadratic := by
  filter_upwards [(φ.toChart.symm.trans φ'.toChart).open_source.mem_nhds
    (φ.zero_mem_transition_source φ')] with z hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  have h₁ := φ'.eq_quadratic _ hz.2
  have h₂ := φ.eq_quadratic _ (φ.toChart.map_target hz.1)
  rw [φ.toChart.right_inv hz.1] at h₂
  simp only [comp_apply, OpenPartialHomeomorph.coe_trans, quadratic_apply]
  linarith

omit [FiniteDimensional ℝ E] in
/-- The derivative at `0` of the transition map `φ' ∘ φ⁻¹` preserves the Hessian of the quadratic
normal forms: `Σᵢ w'ᵢ (L' (D v))ᵢ² = Σᵢ wᵢ (L v)ᵢ²`. -/
private theorem sum_weight_mul_coord_fderiv_transition_sq (v : E) :
    ∑ i, φ'.weight i * φ'.coord (fderiv ℝ (φ.toChart.symm.trans φ'.toChart) 0 v) i ^ 2 =
      ∑ i, φ.weight i * φ.coord v i ^ 2 := by
  set τ := φ.toChart.symm.trans φ'.toChart
  have hτ0 : τ 0 = 0 := by simp [τ]
  have hτ : ContDiffAt ℝ 2 τ 0 := contDiffAt_symm_trans_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ.mem_maximalAtlas)
    (IsManifold.maximalAtlas_subset_of_le (by simp) φ'.mem_maximalAtlas)
    (φ.zero_mem_transition_source φ')
  have hcomp := hessianQuadraticForm_comp (φ'.contDiff_quadratic.contDiffAt.of_le (by simp)) hτ
    (by rw [hτ0, fderiv_quadratic_eq_zero_iff])
  have hH : hessianQuadraticForm (φ'.quadratic ∘ τ) 0 = hessianQuadraticForm φ.quadratic 0 := by
    rw [hessianQuadraticForm_def, hessianQuadraticForm_def,
      (quadratic_comp_transition φ φ').fderiv.fderiv_eq]
  have h := congrArg (fun Q : QuadraticForm ℝ E ↦ Q v) (hcomp.symm.trans hH)
  simpa only [QuadraticMap.comp_apply, ContinuousLinearMap.coe_coe, hτ0,
    hessianQuadraticForm_quadratic] using h

/-- The change of negative coordinates is injective, hence bijective: a nonzero vector of negative
weight in `φ` is negative for the Hessian, so its image cannot have vanishing coordinates of
negative weight in `φ'`. -/
private theorem bijective_negativeChangeAt : Bijective (φ.negativeChangeAt φ' x) := by
  have hinj : Injective (φ.negativeChangeAt φ' x) := by
    refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
    rw [negativeChangeAt_apply, φ.apply_self] at hc
    have h := sum_weight_mul_coord_fderiv_transition_sq φ φ' (φ.negativeExtend c)
    -- The left side is nonnegative, since the coordinates of negative weight vanish.
    have hl : 0 ≤ ∑ i, φ'.weight i *
        φ'.coord (fderiv ℝ (φ.toChart.symm.trans φ'.toChart) 0 (φ.negativeExtend c)) i ^ 2 := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      by_cases hi : φ'.weight i < 0
      · have := congrFun hc ⟨i, hi⟩
        rw [negativeCoord_apply, Pi.zero_apply] at this
        rw [this]
        simp
      · exact mul_nonneg (not_lt.1 hi) (sq_nonneg _)
    -- Every term on the right side is nonpositive, and it is `-(c i)²` at a negative weight.
    have hr (i : Fin (Module.finrank ℝ E)) :
        φ.weight i * φ.coord (φ.negativeExtend c) i ^ 2 ≤ 0 := by
      by_cases hi : φ.weight i < 0
      · exact mul_nonpos_of_nonpos_of_nonneg hi.le (sq_nonneg _)
      · rw [φ.coord_negativeExtend_of_not_weight_neg c hi]
        simp
    have hzero := (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hr i).1
      (le_antisymm (Finset.sum_nonpos fun i _ ↦ hr i) (h ▸ hl))
    funext i
    have hi := hzero i (Finset.mem_univ _)
    rw [φ.coord_negativeExtend_of_weight_neg c i] at hi
    simpa [i.property.ne] using hi
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (φ.negativeChangeAt φ' x).toLinearMap) ?_).1 hinj⟩
  rw [φ.finrank_negativeWeight_fun, φ'.finrank_negativeWeight_fun]

/-- The **change of negative coordinates** from the Morse chart `φ` to the Morse chart `φ'` at the
same point `x`: the vector with coordinates `c` of negative weight and `0` of positive weight in
`φ` is carried by the derivative at `0` of the transition map `φ' ∘ φ⁻¹`, and
`φ.negativeChange φ' c` are the coordinates of negative weight of the result in `φ'`
(`TauCeti.MorseChart.negativeChange_apply`). It is an isomorphism, since the derivative of the
transition map preserves the Hessian of `f`, which is negative definite on the vectors of negative
weight of either chart. -/
noncomputable def negativeChange :
    ({i // φ.weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // φ'.weight i < 0} → ℝ) :=
  LinearEquiv.ofBijective (φ.negativeChangeAt φ' x).toLinearMap (φ.bijective_negativeChangeAt φ')

/-- The defining formula of the change of negative coordinates. -/
theorem negativeChange_apply (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeChange φ' c =
      φ'.negativeCoord (fderiv ℝ (φ.toChart.symm.trans φ'.toChart) 0 (φ.negativeExtend c)) := by
  rw [negativeChange, LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe,
    negativeChangeAt_apply, φ.apply_self]

private theorem negativeChangeAt_self_apply (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeChangeAt φ' x c = φ.negativeChange φ' c := by
  rw [negativeChange_apply, negativeChangeAt_apply, φ.apply_self]

/-- The change of negative coordinates from a Morse chart to itself is the identity. -/
@[simp]
theorem negativeChange_self : φ.negativeChange φ = LinearEquiv.refl ℝ _ := by
  -- Near `0`, the transition map from `φ` to itself is the identity.
  have h : fderiv ℝ (φ.toChart.symm.trans φ.toChart) 0 = ContinuousLinearMap.id ℝ E := by
    refine (Filter.EventuallyEq.fderiv_eq ?_).trans fderiv_id
    have h0 : (0 : E) ∈ φ.toChart.target := by
      simpa using φ.toChart.map_source φ.mem_source
    filter_upwards [φ.toChart.open_target.mem_nhds h0] with z hz
    simp [φ.toChart.right_inv hz]
  ext c : 1
  rw [negativeChange_apply, h, ContinuousLinearMap.id_apply, negativeCoord_negativeExtend,
    LinearEquiv.refl_apply]

omit [FiniteDimensional ℝ E] in
/-- On the source of `φ`, the derivative of `φ'` is the derivative of the transition map
`φ' ∘ φ⁻¹` after the derivative of `φ`. -/
private theorem mfderiv_eq_fderiv_comp {z : M} (hz : z ∈ φ.toChart.source)
    (v : TangentSpace 𝓘(ℝ, E) z) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ'.toChart z v =
      fderiv ℝ (φ.toChart.symm.trans φ'.toChart) (φ.toChart z)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v) := by
  rw [mfderiv_eq_fderiv_comp_of_eqOn φ.mem_maximalAtlas_one
    (h := φ.toChart.symm.trans φ'.toChart) (fun w hw ↦ by simp [φ.toChart.left_inv hw]) hz]
  rfl

/-- The change of negative coordinates read at `z` is continuous at the centre. -/
private theorem tendsto_negativeChangeAt :
    Tendsto (φ.negativeChangeAt φ') (𝓝 x) (𝓝 (φ.negativeChangeAt φ' x)) := by
  set τ := φ.toChart.symm.trans φ'.toChart
  have hx : φ.toChart x ∈ τ.source := φ.apply_self ▸ φ.zero_mem_transition_source φ'
  -- The derivative of the transition map is continuous on its open source.
  have hτ : ContinuousAt (fderiv ℝ τ) (φ.toChart x) :=
    ((contDiffOn_symm_trans_of_mem_maximalAtlas φ.mem_maximalAtlas_one
      φ'.mem_maximalAtlas_one).continuousOn_fderiv_of_isOpen τ.open_source le_rfl).continuousAt
      (τ.open_source.mem_nhds hx)
  exact continuousAt_const.clm_comp
    ((hτ.comp (φ.toChart.continuousAt φ.mem_source)).clm_comp continuousAt_const)

end MorseChart

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {φ φ' : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  (hφ' : ∀ y ∈ φ'.toChart.source, φ'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ'.toChart y (X y)) =
    fun i ↦ -(φ'.weight i * φ'.coord (φ'.toChart y) i))

/-! ### The unstable frame -/

include hφ in
/-- At a point whose backward orbit stays in the linear part of `φ` from the time `0` on, the
derivative of `φ` sends the unstable frame on `c` to the vector with coordinates `c` of negative
weight and `0` of positive weight. -/
private theorem mfderiv_unstableFrame_of_zero_mem {z : M}
    (hz : 0 ∈ hX.linearBackwardTimes φ z) (c : {i // φ.weight i < 0} → ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (hX.unstableFrame φ z c) = φ.negativeExtend c := by
  have h := hX.mfderiv_unstableFrame hφ hz c
  rwa [neg_zero, Flow.map_zero, comp_id, Real.exp_zero, one_smul] at h

/-- A point whose backward orbit stays in the linear part of `φ` from the time `0` on lies in the
source of `φ`. -/
private theorem mem_source_of_zero_mem_linearBackwardTimes {z : M}
    (hz : 0 ∈ hX.linearBackwardTimes φ z) : z ∈ φ.toChart.source := by
  simpa using ((hX.mem_linearBackwardTimes φ).1 hz).1

include hφ hφ' in
/-- Near `x`, where the backward flow is linear in both charts, the unstable frames of `φ` and
`φ'` differ by the change of negative coordinates read at the point. -/
private theorem unstableFrame_negativeChangeAt (hf : IsMorse 𝓘(ℝ, E) f) {z : M}
    (hz : z ∈ hX.flow.unstableSet x) (h₀ : 0 ∈ hX.linearBackwardTimes φ z)
    (h₀' : 0 ∈ hX.linearBackwardTimes φ' z) (c : {i // φ.weight i < 0} → ℝ) :
    hX.unstableFrame φ' z (φ.negativeChangeAt φ' z c) = hX.unstableFrame φ z c := by
  -- The frames of both charts span the tangent space of `W^u(x)`.
  obtain ⟨c', hc'⟩ : hX.unstableFrame φ z c ∈ range (hX.unstableFrame φ' z) := by
    rw [hX.range_unstableFrame hφ' hf hz, ← hX.range_unstableFrame hφ hf hz]
    exact mem_range_self c
  have hc : φ.negativeChangeAt φ' z c = c' := by
    rw [MorseChart.negativeChangeAt_apply, ← mfderiv_unstableFrame_of_zero_mem hφ h₀,
      ← MorseChart.mfderiv_eq_fderiv_comp φ φ' (mem_source_of_zero_mem_linearBackwardTimes h₀),
      ← hc', mfderiv_unstableFrame_of_zero_mem hφ' h₀', MorseChart.negativeCoord_negativeExtend]
  rw [hc, hc']

include hφ hφ' in
/-- **The unstable frames of two Morse charts.** At every point `y` of `W^u(x)`, the unstable frame
of `φ'` on the change of negative coordinates of `c` is the unstable frame of `φ` on `c`. -/
theorem unstableFrame_negativeChange (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) (c : {i // φ.weight i < 0} → ℝ) :
    hX.unstableFrame φ' y (φ.negativeChange φ' c) = hX.unstableFrame φ y c := by
  -- For all large `T`, the point `z = Φ_{-T} y` is in the linear part of both charts, where the
  -- frames differ by the change of negative coordinates read at `z`; moving forward by `T`
  -- rescales both frames by the same factor.
  have hev : ∀ᶠ T in atTop,
      hX.unstableFrame φ' y (φ.negativeChangeAt φ' (hX.flow (-T) y) c) =
        hX.unstableFrame φ y c := by
    filter_upwards [hX.eventually_mem_linearBackwardTimes hφ hf hy,
      hX.eventually_mem_linearBackwardTimes hφ' hf hy] with T hT hT'
    have h₀ : 0 ∈ hX.linearBackwardTimes φ (hX.flow (-T) y) :=
      mem_linearBackwardTimes_flow.2 (by rwa [zero_sub, neg_neg])
    have h₀' : 0 ∈ hX.linearBackwardTimes φ' (hX.flow (-T) y) :=
      mem_linearBackwardTimes_flow.2 (by rwa [zero_sub, neg_neg])
    have hz := (Flow.apply_mem_unstableSet_iff hX.flow (-T)).2 hy
    have key := congrArg (fun v ↦ Real.exp (-T) • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) _ v)
      (unstableFrame_negativeChangeAt hφ hφ' hf hz h₀ h₀' c)
    rwa [← hX.unstableFrame_flow hφ' h₀', ← hX.unstableFrame_flow hφ h₀, ← Flow.map_add,
      add_neg_cancel, Flow.map_zero_apply] at key
  -- As `T → ∞`, the point `Φ_{-T} y` tends to `x`, where the comparison is the change of
  -- negative coordinates.
  have hlim : Tendsto (fun T ↦ hX.unstableFrame φ' y (φ.negativeChangeAt φ' (hX.flow (-T) y) c))
      atTop (𝓝 (hX.unstableFrame φ' y (φ.negativeChange φ' c))) := by
    have hz : Tendsto (fun T ↦ hX.flow (-T) y) atTop (𝓝 x) :=
      (Flow.mem_unstableSet.1 hy).comp tendsto_neg_atTop_atBot
    rw [← MorseChart.negativeChangeAt_self_apply]
    exact ((hX.unstableFrame φ' y).continuous.tendsto _).comp
      (((ContinuousLinearMap.apply ℝ _ c).continuous.tendsto _).comp
        ((φ.tendsto_negativeChangeAt φ').comp hz))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h ↦ h.symm))

/-! ### The normal coordinates of the stable manifold -/

include hφ in
/-- At a point whose forward orbit stays in the linear part of `φ` from the time `0` on, the normal
coordinates are the coordinates of negative weight of the derivative of `φ`. -/
private theorem stableNormal_eq_negativeCoord {z : M} (hz : 0 ∈ hX.linearForwardTimes φ z)
    (v : TangentSpace 𝓘(ℝ, E) z) :
    hX.stableNormal φ z v = φ.negativeCoord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v) := by
  rw [hX.stableNormal_apply hφ hz v, Flow.map_zero, comp_id, neg_zero, Real.exp_zero, one_smul]

include hφ hφ' in
/-- Near `x`, where the forward flow is linear in both charts, the normal coordinates of `φ` and
`φ'` differ by the change of negative coordinates read at the point. -/
private theorem negativeChangeAt_stableNormal {z : M} (hz : z ∈ hX.flow.stableSet x)
    (h₀ : 0 ∈ hX.linearForwardTimes φ z) (h₀' : 0 ∈ hX.linearForwardTimes φ' z)
    (v : TangentSpace 𝓘(ℝ, E) z) :
    φ.negativeChangeAt φ' z (hX.stableNormal φ z v) = hX.stableNormal φ' z v := by
  have hsrc : z ∈ φ.toChart.source := by simpa using ((hX.mem_linearForwardTimes φ).1 h₀).1
  -- A vector `v₀` with the same normal coordinates as `v` for `φ`, and with vanishing coordinates
  -- of positive weight in `φ`.
  obtain ⟨v₀, hv₀⟩ := (isInvertible_mfderiv_chart φ.mem_maximalAtlas_one hsrc).surjective
    (φ.negativeExtend (hX.stableNormal φ z v) : TangentSpace 𝓘(ℝ, E) (φ.toChart z))
  have hN : hX.stableNormal φ z v₀ = hX.stableNormal φ z v := by
    rw [stableNormal_eq_negativeCoord hφ h₀ v₀, hv₀, MorseChart.negativeCoord_negativeExtend]
  -- `v - v₀` is tangent to `W^s(x)`, where the normal coordinates of both charts vanish.
  have hker : hX.stableNormal φ' z (v - v₀) = 0 :=
    (hX.stableNormal_eq_zero_iff hφ' hz _).2
      ((hX.stableNormal_eq_zero_iff hφ hz _).1 (by rw [map_sub, hN, sub_self]))
  rw [map_sub, sub_eq_zero] at hker
  rw [hker, stableNormal_eq_negativeCoord hφ' h₀', MorseChart.mfderiv_eq_fderiv_comp φ φ' hsrc,
    hv₀, MorseChart.negativeChangeAt_apply]

include hφ hφ' in
/-- **The normal coordinates of two Morse charts.** At every point `y` of `W^s(x)`, the change of
negative coordinates carries the normal coordinates of `φ` to those of `φ'`. -/
theorem negativeChange_stableNormal {y : M} (hy : y ∈ hX.flow.stableSet x)
    (v : TangentSpace 𝓘(ℝ, E) y) :
    φ.negativeChange φ' (hX.stableNormal φ y v) = hX.stableNormal φ' y v := by
  -- For all large `T`, the point `z = Φ_T y` is in the linear part of both charts, where the
  -- normal coordinates differ by the change of negative coordinates read at `z`; moving forward
  -- by `T` rescales both normal coordinates by the same factor.
  have hev : ∀ᶠ T in atTop,
      φ.negativeChangeAt φ' (hX.flow T y) (hX.stableNormal φ y v) = hX.stableNormal φ' y v := by
    filter_upwards [hX.eventually_mem_linearForwardTimes hφ hy,
      hX.eventually_mem_linearForwardTimes hφ' hy] with T hT hT'
    have h₀ : 0 ∈ hX.linearForwardTimes φ (hX.flow T y) :=
      mem_linearForwardTimes_flow.2 (by rwa [zero_add])
    have h₀' : 0 ∈ hX.linearForwardTimes φ' (hX.flow T y) :=
      mem_linearForwardTimes_flow.2 (by rwa [zero_add])
    have hz := (Flow.apply_mem_stableSet_iff hX.flow T).2 hy
    have key := negativeChangeAt_stableNormal hφ hφ' hz h₀ h₀'
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y v)
    rw [hX.stableNormal_mfderiv_flow hφ hT, hX.stableNormal_mfderiv_flow hφ' hT', map_smul] at key
    exact smul_right_injective _ (Real.exp_ne_zero T) key
  -- As `T → ∞`, the point `Φ_T y` tends to `x`, where the comparison is the change of negative
  -- coordinates.
  have hlim : Tendsto (fun T ↦ φ.negativeChangeAt φ' (hX.flow T y) (hX.stableNormal φ y v))
      atTop (𝓝 (φ.negativeChange φ' (hX.stableNormal φ y v))) := by
    rw [← MorseChart.negativeChangeAt_self_apply]
    exact ((ContinuousLinearMap.apply ℝ _ _).continuous.tendsto _).comp
      ((φ.tendsto_negativeChangeAt φ').comp (Flow.mem_stableSet.1 hy))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h ↦ h.symm))

variable (hX) in
include hX hφ hφ' in
/-- **The changes of negative coordinates compose** for three Morse charts at a critical point in
which the pseudo-gradient is linear: both sides carry the unstable frame of `φ''` at `x` to that
of `φ`. -/
theorem negativeChange_trans_negativeChange (hf : IsMorse 𝓘(ℝ, E) f) {φ'' : MorseChart E f x}
    (hφ'' : ∀ y ∈ φ''.toChart.source, φ''.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ''.toChart y (X y)) =
      fun i ↦ -(φ''.weight i * φ''.coord (φ''.toChart y) i)) :
    (φ.negativeChange φ').trans (φ'.negativeChange φ'') = φ.negativeChange φ'' := by
  -- `x` is a rest point, so it lies in its own unstable manifold.
  have hx : x ∈ hX.flow.unstableSet x := Flow.self_mem_unstableSet_iff.2
    (hX.flow_apply_of_mfderiv_eq_zero ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl))
  ext c : 1
  refine hX.injective_unstableFrame_of_mem hφ'' hf hx ?_
  rw [LinearEquiv.trans_apply, unstableFrame_negativeChange hφ' hφ'' hf hx,
    unstableFrame_negativeChange hφ hφ' hf hx, unstableFrame_negativeChange hφ hφ'' hf hx]

end IsAdaptedPseudoGradient

end TauCeti

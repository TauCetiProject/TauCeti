/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Frame
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Changing the Morse chart of the unstable frame and the normal coordinates

Let `φ` and `φ'` be two Morse charts of `f` at the same critical point `x`, with spaces
`V = {i // wᵢ < 0} → ℝ` and `V'` of coordinates of negative weight. The unstable frame
`hX.unstableFrame φ y : V → T_y M` of `W^u(x)` and the normal coordinates
`hX.stableNormal φ y : T_y M → V` of `W^s(x)` are built from the chart `φ`
(`TauCeti.Geometry.Manifold.Morse.Stable.Frame`). This file compares them with those built from
`φ'`, so that orientations of the unstable manifolds, and the signs built from them, can be moved
from one Morse chart to another.

The comparison map is the **transition of negative coordinates**
`TauCeti.MorseChart.negativeTransition φ φ' : V → V'`: the derivative at `0` of the chart
transition `φ' ∘ φ⁻¹`, applied to vectors of `V` (extended by zero coordinates of positive weight)
and followed by the coordinates of negative weight of `φ'`. It is an isomorphism
(`TauCeti.MorseChart.bijective_negativeTransition`): the derivative of the transition carries the
quadratic form `Σᵢ wᵢ (L z)ᵢ²` of `φ` to that of `φ'`, since both express `f`, so it carries the
negative definite space `V` of `φ` to a subspace on which the form of `φ'` is negative definite,
which meets the vectors of `φ'` with no coordinates of negative weight only in `0`.

When the pseudo-gradient `X` is linear in both charts, the two frames and the two normal
coordinates differ exactly by this map `A`:

* `Fφ'(y) ∘ A = Fφ(y)` at every point `y` of `W^u(x)`
  (`TauCeti.IsAdaptedPseudoGradient.unstableFrame_negativeTransition`);
* `Nφ'(y) = A ∘ Nφ(y)` at every point `y` of `W^s(x)`
  (`TauCeti.IsAdaptedPseudoGradient.stableNormal_eq_negativeTransition`).

Both are read off the flow. At a time `T` at which the orbit of `y` lies in the parts of both charts
where the flow is linear, the derivative of `φ' ∘ Φ_T` is the derivative of the transition at
`φ (Φ_T y)` composed with that of `φ ∘ Φ_T`, so the two frames, respectively normal coordinates,
differ by the transition of negative coordinates read at `φ (Φ_T y)` instead of at `0`. This does
not depend on `T`, and as `T` tends to infinity (backwards along `W^u(x)`, forwards along
`W^s(x)`) the orbit tends to `x`, so the derivative of the transition tends to its value at `0`.

In particular the transitions compose along three charts in which `X` is linear
(`TauCeti.MorseChart.negativeTransition_comp_negativeTransition`), and the transition from a chart
to itself is the identity (`TauCeti.MorseChart.negativeTransition_self`), so transporting
orientations of the spaces of coordinates of negative weight along them is consistent.

## Main definitions

In the namespace `TauCeti.MorseChart`:

* `negativeTransition φ φ'`: the transition of negative coordinates from `φ` to `φ'`.
* `negativeTransitionEquiv φ φ'`: the same map, as a linear equivalence.

## Main results

* `MorseChart.bijective_negativeTransition`: the transition of negative coordinates is bijective.
* `MorseChart.negativeTransition_self`, `MorseChart.negativeTransitionEquiv_self`: the transition
  from a chart to itself is the identity.
* `IsAdaptedPseudoGradient.unstableFrame_negativeTransition`: the unstable frames of two Morse
  charts in which `X` is linear differ by the transition.
* `IsAdaptedPseudoGradient.stableNormal_eq_negativeTransition`: so do the normal coordinates.
* `MorseChart.negativeTransition_comp_negativeTransition` and
  `MorseChart.negativeTransitionEquiv_trans`: the transitions between three Morse charts in which
  `X` is linear compose.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations of the descending manifolds).
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {x : M}

namespace MorseChart

variable (φ φ' : MorseChart E f x)

/-- The chart transition `φ' ∘ φ⁻¹` is smooth at every point of its domain. -/
private theorem contDiffAt_transition {z : E} (hz : z ∈ φ.toChart.target)
    (hz' : φ.toChart.symm z ∈ φ'.toChart.source) :
    ContDiffAt ℝ ∞ (φ'.toChart ∘ φ.toChart.symm) z := by
  rw [← OpenPartialHomeomorph.coe_trans]
  exact contDiffAt_symm_trans_of_mem_maximalAtlas φ.mem_maximalAtlas φ'.mem_maximalAtlas
    (by simpa using ⟨hz, hz'⟩)

/-- The centre of the chart, `0`, lies in the target. -/
private theorem zero_mem_target : (0 : E) ∈ φ.toChart.target :=
  φ.apply_self ▸ φ.toChart.map_source φ.mem_source

/-- The chart transition `φ' ∘ φ⁻¹` is smooth at `0`. -/
private theorem contDiffAt_transition_zero : ContDiffAt ℝ ∞ (φ'.toChart ∘ φ.toChart.symm) 0 :=
  φ.contDiffAt_transition φ' φ.zero_mem_target (by simp)

variable [FiniteDimensional ℝ E]

/-- The **transition of negative coordinates** from the Morse chart `φ` to the Morse chart `φ'` at
the same point: a vector of coordinates of negative weight of `φ`, extended by zero coordinates of
positive weight, is moved by the derivative at `0` of the chart transition `φ' ∘ φ⁻¹`, and its
coordinates of negative weight of `φ'` are read off. -/
noncomputable def negativeTransition :
    ({i // φ.weight i < 0} → ℝ) →L[ℝ] ({i // φ'.weight i < 0} → ℝ) :=
  (LinearMap.toContinuousLinearMap φ'.negativeCoord).comp
    ((fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) 0).comp
      (LinearMap.toContinuousLinearMap φ.negativeExtend))

/-- The defining formula of the transition of negative coordinates. -/
theorem negativeTransition_apply (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeTransition φ' c =
      φ'.negativeCoord (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) 0 (φ.negativeExtend c)) :=
  (rfl)

/-- **The transition from a chart to itself is the identity.** -/
@[simp]
theorem negativeTransition_self : φ.negativeTransition φ = ContinuousLinearMap.id ℝ _ := by
  have h : (φ.toChart ∘ φ.toChart.symm : E → E) =ᶠ[𝓝 0] id := by
    filter_upwards [φ.toChart.open_target.mem_nhds φ.zero_mem_target] with z hz
    exact φ.toChart.right_inv hz
  ext c : 1
  rw [negativeTransition_apply, h.fderiv_eq, fderiv_id, ContinuousLinearMap.id_apply,
    negativeCoord_negativeExtend, ContinuousLinearMap.id_apply]

/-- The coordinate functional of index `i` of a Morse chart. -/
private noncomputable def coordFunctional (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj i).comp (φ.coord : E →ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ)))

/-- The diagonal bilinear form `(u, v) ↦ Σᵢ wᵢ (L u)ᵢ (L v)ᵢ` of a Morse chart, whose quadratic
form expresses `f` in the chart. -/
private noncomputable def weightForm : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, φ.weight i •
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp (φ.coordFunctional i) (φ.coordFunctional i)

private theorem weightForm_apply_self (v : E) :
    φ.weightForm v v = ∑ i, φ.weight i * φ.coord v i ^ 2 := by
  simp [weightForm, coordFunctional, sq]

/-- The derivative of the chart transition carries the quadratic form of `φ` to that of `φ'`. -/
private theorem weightForm_fderiv_transition (v : E) :
    φ'.weightForm (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) 0 v)
        (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) 0 v) =
      φ.weightForm v v := by
  have hdiff := (φ.contDiffAt_transition_zero φ').differentiableAt (by simp)
  have h0 : (φ'.toChart ∘ φ.toChart.symm) 0 = 0 := by simp
  refine ContinuousLinearMap.apply_self_fderiv_eq_of_eventuallyEq _ _ hdiff h0 ?_ v
  -- Near `0`, both quadratic forms express `f` read through `φ⁻¹`.
  have hsrc : ∀ᶠ z in 𝓝 (0 : E), φ.toChart.symm z ∈ φ'.toChart.source :=
    φ.toChart.continuousAt_symm φ.zero_mem_target
      (by simpa using φ'.toChart.open_source.mem_nhds φ'.mem_source)
  filter_upwards [φ.toChart.open_target.mem_nhds φ.zero_mem_target, hsrc] with z hz hz'
  have h := φ.eq_quadratic _ (φ.toChart.map_target hz)
  have h' := φ'.eq_quadratic _ hz'
  rw [φ.toChart.right_inv hz] at h
  simp only [comp_apply, weightForm_apply_self]
  linarith

/-- **The transition of negative coordinates is injective.** -/
theorem injective_negativeTransition : Injective (φ.negativeTransition φ') := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  set v := φ.negativeExtend c
  set u := fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) 0 v
  have hQ := φ.weightForm_fderiv_transition φ' v
  rw [weightForm_apply_self, weightForm_apply_self] at hQ
  -- `u` has no coordinates of negative weight, so the form of `φ'` is nonnegative on it.
  have hu : ∀ i, φ'.weight i < 0 → φ'.coord u i = 0 := fun i hi ↦ by
    simpa [negativeTransition_apply] using congrFun hc ⟨i, hi⟩
  have hpos : 0 ≤ ∑ i, φ'.weight i * φ'.coord u i ^ 2 := Finset.sum_nonneg fun i _ ↦ by
    rcases φ'.weight_eq_neg_one_or_eq_one i with hi | hi
    · simp [hu i (by rw [hi]; norm_num)]
    · rw [hi, one_mul]
      exact sq_nonneg _
  -- `v` has only coordinates of negative weight, so the form of `φ` is negative on it unless
  -- `c = 0`.
  by_contra hc0
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hc0
  have hneg : ∑ i, φ.weight i * φ.coord v i ^ 2 < ∑ _i : Fin (Module.finrank ℝ E), (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨j, Finset.mem_univ _, ?_⟩
    · by_cases hi : φ.weight i < 0
      · exact mul_nonpos_of_nonpos_of_nonneg hi.le (sq_nonneg _)
      · simp [v, φ.coord_negativeExtend_of_not_weight_neg c hi]
    · have hw : φ.weight j = -1 :=
        (φ.weight_eq_neg_one_or_eq_one j).resolve_right ((φ.weight_ne_one_iff j).2 j.2)
      rw [hw, show φ.coord v j = c j from φ.coord_negativeExtend_of_weight_neg c j]
      have : 0 < c j ^ 2 := by simpa using sq_pos_of_ne_zero hj
      linarith
  rw [Finset.sum_const_zero] at hneg
  linarith

/-- **The transition of negative coordinates is bijective.** -/
theorem bijective_negativeTransition : Bijective (φ.negativeTransition φ') := by
  have hinj : Injective (φ.negativeTransition φ').toLinearMap := φ.injective_negativeTransition φ'
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [φ.finrank_negativeWeight_fun, φ'.finrank_negativeWeight_fun]

/-- The transition of negative coordinates from `φ` to `φ'`, as a linear equivalence. -/
noncomputable def negativeTransitionEquiv :
    ({i // φ.weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // φ'.weight i < 0} → ℝ) :=
  LinearEquiv.ofBijective (φ.negativeTransition φ').toLinearMap (φ.bijective_negativeTransition φ')

/-- The linear equivalence `negativeTransitionEquiv` applies the transition of negative
coordinates. -/
@[simp]
theorem negativeTransitionEquiv_apply (c : {i // φ.weight i < 0} → ℝ) :
    φ.negativeTransitionEquiv φ' c = φ.negativeTransition φ' c :=
  LinearEquiv.ofBijective_apply _ c

/-- The transition equivalence from a chart to itself is the identity. -/
@[simp]
theorem negativeTransitionEquiv_self : φ.negativeTransitionEquiv φ = LinearEquiv.refl ℝ _ :=
  LinearEquiv.ext fun c ↦ by simp

/-- Along a family of points tending to the centre, the transition of negative coordinates read at
their images in the chart tends to the transition read at `0`. -/
private theorem tendsto_negativeCoord_fderiv_transition {α : Type*} {l : Filter α} {γ : α → M}
    (hγ : Tendsto γ l (𝓝 x)) (c : {i // φ.weight i < 0} → ℝ) :
    Tendsto (fun a ↦ φ'.negativeCoord
      (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) (φ.toChart (γ a)) (φ.negativeExtend c))) l
      (𝓝 (φ.negativeTransition φ' c)) := by
  have hchart : Tendsto (fun a ↦ φ.toChart (γ a)) l (𝓝 0) :=
    φ.apply_self ▸ (φ.toChart.continuousAt φ.mem_source).tendsto.comp hγ
  have hD := ((φ.contDiffAt_transition_zero φ').continuousAt_fderiv (by simp)).tendsto.comp hchart
  have hcoord : Continuous φ'.negativeCoord := LinearMap.continuous_of_finiteDimensional _
  exact (hcoord.tendsto _).comp
    (((ContinuousLinearMap.apply ℝ E (φ.negativeExtend c)).continuous.tendsto _).comp hD)

end MorseChart

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable {hX : IsAdaptedPseudoGradient f X} {φ φ' : MorseChart E f x}

/-- **The chain rule through the chart transition.** At a point whose orbit lies in both charts at
time `T`, the derivative of `φ' ∘ Φ_T` is the derivative of the transition `φ' ∘ φ⁻¹` at
`φ (Φ_T y)` composed with that of `φ ∘ Φ_T`. -/
private theorem mfderiv_toChart_comp_flow_eq_fderiv_transition {y : M} {T : ℝ}
    (hT : hX.flow T y ∈ φ.toChart.source) (hT' : hX.flow T y ∈ φ'.toChart.source)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ'.toChart ∘ hX.flow T) y w =
      fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) (φ.toChart (hX.flow T y))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y w) := by
  have hflow : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (hX.flow T) y :=
    (hX.contMDiff_flow_apply T).mdifferentiable (by simp) y
  have hev : (φ'.toChart ∘ hX.flow T : M → E) =ᶠ[𝓝 y]
      (φ'.toChart ∘ φ.toChart.symm) ∘ (φ.toChart ∘ hX.flow T) := by
    filter_upwards [hflow.continuousAt.preimage_mem_nhds (φ.toChart.open_source.mem_nhds hT)]
      with z hz
    simp [φ.toChart.left_inv hz]
  have hτ : DifferentiableAt ℝ (φ'.toChart ∘ φ.toChart.symm) (φ.toChart (hX.flow T y)) :=
    (φ.contDiffAt_transition φ' (φ.toChart.map_source hT) (by rwa [φ.toChart.left_inv hT])
      ).differentiableAt (by simp)
  rw [hev.mfderiv_eq, mfderiv_comp y hτ.mdifferentiableAt
    ((φ.mdifferentiableAt_toChart hT).comp y hflow), mfderiv_eq_fderiv]
  rfl

variable (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  (hφ' : ∀ y ∈ φ'.toChart.source, φ'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ'.toChart y (X y)) =
    fun i ↦ -(φ'.weight i * φ'.coord (φ'.toChart y) i))
include hφ hφ'

/-- **The unstable frames of two Morse charts differ by the transition of negative coordinates.**
If `X` is linear in the Morse charts `φ` and `φ'` at `x`, then at every point `y` of `W^u(x)` the
unstable frame of `φ'` on the transition of `c` is the unstable frame of `φ` on `c`. -/
theorem unstableFrame_negativeTransition (hf : IsMorse 𝓘(ℝ, E) f) {y : M}
    (hy : y ∈ hX.flow.unstableSet x) (c : {i // φ.weight i < 0} → ℝ) :
    hX.unstableFrame φ' y (φ.negativeTransition φ' c) = hX.unstableFrame φ y c := by
  -- At a time `T` of linear backward flow in both charts, the two frames differ by the transition
  -- read at `φ (Φ_{-T} y)`.
  have hev : ∀ᶠ T in atTop, hX.unstableFrame φ' y (φ'.negativeCoord
      (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) (φ.toChart (hX.flow (-T) y))
        (φ.negativeExtend c))) = hX.unstableFrame φ y c := by
    filter_upwards [hX.eventually_mem_linearBackwardTimes hφ hf hy,
      hX.eventually_mem_linearBackwardTimes hφ' hf hy] with T hT hT'
    have hsrc := ((mem_linearBackwardTimes _ _).1 hT).1
    have hsrc' := ((mem_linearBackwardTimes _ _).1 hT').1
    -- The frame of `φ` on `c` is tangent to `W^u(x)`, hence the frame of `φ'` on some `c'`.
    obtain ⟨c', hc'⟩ : hX.unstableFrame φ y c ∈ range (hX.unstableFrame φ' y) := by
      rw [range_unstableFrame hφ' hf hy, ← range_unstableFrame hφ hf hy]
      exact mem_range_self c
    have h := mfderiv_unstableFrame hφ' hT' c'
    rw [hc', mfderiv_toChart_comp_flow_eq_fderiv_transition hsrc hsrc',
      mfderiv_unstableFrame hφ hT, map_smul] at h
    rw [smul_right_injective E (Real.exp_ne_zero _) h, MorseChart.negativeCoord_negativeExtend,
      hc']
  have hlim := φ.tendsto_negativeCoord_fderiv_transition φ'
    ((Flow.mem_unstableSet.1 hy).comp tendsto_neg_atTop_atBot) c
  exact tendsto_nhds_unique (((hX.unstableFrame φ' y).continuous.tendsto _).comp hlim)
    (tendsto_const_nhds.congr' (hev.mono fun _ h ↦ h.symm))

/-- **The normal coordinates of two Morse charts differ by the transition of negative
coordinates.** If `X` is linear in the Morse charts `φ` and `φ'` at `x`, then at every point `y`
of `W^s(x)` the normal coordinates of `φ'` are the transition of those of `φ`. -/
theorem stableNormal_eq_negativeTransition {y : M} (hy : y ∈ hX.flow.stableSet x)
    (w : TangentSpace 𝓘(ℝ, E) y) :
    hX.stableNormal φ' y w = φ.negativeTransition φ' (hX.stableNormal φ y w) := by
  -- At a time `T` of linear forward flow in both charts, the two normal coordinates differ by the
  -- transition read at `φ (Φ_T y)`.
  have hev : ∀ᶠ T in atTop, hX.stableNormal φ' y w = φ'.negativeCoord
      (fderiv ℝ (φ'.toChart ∘ φ.toChart.symm) (φ.toChart (hX.flow T y))
        (φ.negativeExtend (hX.stableNormal φ y w))) := by
    filter_upwards [hX.eventually_mem_linearForwardTimes hφ hy,
      hX.eventually_mem_linearForwardTimes hφ' hy] with T hT hT'
    have hsrc := ((mem_linearForwardTimes _ _).1 hT).1
    have hsrc' := ((mem_linearForwardTimes _ _).1 hT').1
    -- The vector `w₀` sent by the derivative of `φ ∘ Φ_T` to a vector of negative weight has the
    -- same normal coordinates as `w`, for both charts.
    set w₀ := (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y).inverse
      (Real.exp T • φ.negativeExtend (hX.stableNormal φ y w))
    have hw₀ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (φ.toChart ∘ hX.flow T) y w₀ =
        Real.exp T • φ.negativeExtend (hX.stableNormal φ y w) :=
      (isInvertible_mfderiv_toChart_comp_flow hsrc).self_apply_inverse _
    have hN : hX.stableNormal φ y (w - w₀) = 0 := by
      rw [map_sub, stableNormal_apply hφ hT w₀, hw₀, map_smul,
        MorseChart.negativeCoord_negativeExtend, smul_smul, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, one_smul, sub_self]
    have hN' := (stableNormal_eq_zero_iff hφ' hy _).2 ((stableNormal_eq_zero_iff hφ hy _).1 hN)
    rw [map_sub, sub_eq_zero] at hN'
    rw [hN', stableNormal_apply hφ' hT', mfderiv_toChart_comp_flow_eq_fderiv_transition hsrc hsrc',
      hw₀, map_smul, map_smul, smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun _ h ↦ h))
    (φ.tendsto_negativeCoord_fderiv_transition φ' (Flow.mem_stableSet.1 hy) _)

end IsAdaptedPseudoGradient

namespace MorseChart

variable {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {φ φ' φ'' : MorseChart E f x}
  (hX : IsAdaptedPseudoGradient f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
    fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
  (hφ' : ∀ y ∈ φ'.toChart.source, φ'.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ'.toChart y (X y)) =
    fun i ↦ -(φ'.weight i * φ'.coord (φ'.toChart y) i))
  (hφ'' : ∀ y ∈ φ''.toChart.source, φ''.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ''.toChart y (X y)) =
    fun i ↦ -(φ''.weight i * φ''.coord (φ''.toChart y) i))
include hX hf hφ hφ' hφ''

/-- **The transitions of negative coordinates compose.** If a pseudo-gradient `X` adapted to the
Morse function `f` is linear in the three Morse charts `φ`, `φ'` and `φ''` at `x`, the transition
from `φ` to `φ''` is the transition from `φ` to `φ'` followed by the transition from `φ'` to
`φ''`. -/
theorem negativeTransition_comp_negativeTransition :
    (φ'.negativeTransition φ'').comp (φ.negativeTransition φ') = φ.negativeTransition φ'' := by
  -- Compare the three unstable frames at the critical point `x`, a rest point of the flow.
  have hx : x ∈ hX.flow.unstableSet x := Flow.self_mem_unstableSet_iff.2
    (hX.flow_apply_of_mfderiv_eq_zero ((φ.mfderiv_eq_zero_iff φ.mem_source).2 rfl))
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes hφ'' hf hx).exists
  ext c : 1
  refine hX.injective_unstableFrame hφ'' hT ?_
  rw [ContinuousLinearMap.comp_apply,
    IsAdaptedPseudoGradient.unstableFrame_negativeTransition hφ' hφ'' hf hx,
    IsAdaptedPseudoGradient.unstableFrame_negativeTransition hφ hφ' hf hx,
    IsAdaptedPseudoGradient.unstableFrame_negativeTransition hφ hφ'' hf hx]

/-- The transition equivalences between three Morse charts in which `X` is linear compose, so
transporting an orientation from `φ` to `φ'` and then to `φ''` transports it from `φ` to `φ''`. -/
theorem negativeTransitionEquiv_trans :
    (φ.negativeTransitionEquiv φ').trans (φ'.negativeTransitionEquiv φ'') =
      φ.negativeTransitionEquiv φ'' :=
  LinearEquiv.ext fun c ↦ by
    simpa using DFunLike.congr_fun
      (negativeTransition_comp_negativeTransition hX hf hφ hφ' hφ'') c

end MorseChart

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Basic
public import TauCeti.Geometry.Manifold.Flow.TimeDependent

/-!
# Continuation trajectories through the transition diffeomorphisms of the slab

Let `V` be a continuation field on `M × ℝ` from a pseudo-gradient `X₀` to a pseudo-gradient `X₁`
at rate `C > 0` (`TauCeti.IsContinuationField`), on a compact boundaryless manifold `M`. In the
open slab `M × (0, 1)` the time component of `V` is `C t (1 - t²)`, so along every trajectory
through the slab the time component is a translate of the base trajectory
`β = TauCeti.intervalBaseOrbit C`. Reading the space component of `V` along `β` gives a
time-dependent vector field on `M`,

`Y s x = (V (x, β s)).1` (`TauCeti.continuationSpaceField`),

and the trajectories of `V` through the slab are exactly the curves `s ↦ (φ_{τ, s} x, β s)`, up to
translation of time, where `φ_{s, t}` is the time-dependent flow of `Y`
(`TauCeti.timeDependentFlowOf`). This is the time-dependent formulation of a continuation used by
Hutchings: a trajectory from `(p, 0)` to `(q, 1)` is a solution of `x' = Y_s(x)` which tends to
`p` at `-∞` and to `q` at `+∞`. On a compact manifold the time-dependent flow of `Y` is defined at
all times, and each of its time maps is a diffeomorphism of `M`
(`TauCeti.timeDependentFlowDiffeomorph`).

Since `V` agrees with `X₀` near `t = 0` and with `X₁` near `t = 1`, the field `Y` is `X₀` for very
negative times and `X₁` for very positive times. There the time-dependent flow is the flow of `X₀`
and of `X₁` (`TauCeti.IsAdaptedPseudoGradient.eqOn_timeDependentFlowOf_flow_of_lt`,
`TauCeti.IsAdaptedPseudoGradient.eqOn_timeDependentFlowOf_flow_of_gt`), which preserves their
unstable and stable manifolds. So a solution tends to `p` at `-∞` exactly when its value at one very
negative time `a` lies in the unstable manifold `W^u(p)` of `X₀`, and to `q` at `+∞` exactly when
its value at one very positive time `b` lies in the stable manifold `W^s(q)` of `X₁`. Reading
trajectories on the middle level `t = 1 / 2`, at the time `σ` with `β σ = 1 / 2`, this identifies
the slices of the continuation map
(`TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage`):

`TauCeti.morseContinuationSlice V p q = φ_{σ, a}⁻¹ (W^u(p)) ∩ φ_{σ, b}⁻¹ (W^s(q))`.

Since `φ_{σ, b} = φ_{a, b} ∘ φ_{σ, a}` and `φ_{σ, a}` is a bijection, the slice of `(p, q)` is in
bijection with the intersection `W^u(p) ∩ Φ⁻¹ (W^s(q))` for the single transition map
`Φ = φ_{a, b}` of the slab, a diffeomorphism of `M` carrying the very negative level of the slab to
the very positive one; the same `Φ` serves all pairs of critical points
(`TauCeti.IsContinuationField.eventually_ncard_morseContinuationSlice_eq`). So the coefficients
of the mod-two continuation map are intersection counts of the unstable manifolds of `X₀` with the
preimages under `Φ` of the stable manifolds of `X₁`
(`TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_inter_preimage`). In
this form the transversality condition for continuations is the transversality of `W^u(p)` and
`Φ⁻¹ (W^s(q))`, which is the stable manifold of `Φ⁻¹ q` for the pullback of `X₁` by `Φ`.

## Main declarations

* `TauCeti.continuationSpaceField`: the space component of a field on `M × ℝ` along the base
  trajectory, a time-dependent vector field on `M`.
* `TauCeti.contMDiff_continuationSpaceField`: it is as smooth as the field.
* `TauCeti.isMIntegralCurve_timeDependentFlowOf_continuationSpaceField`: the curves
  `s ↦ (φ_{τ, s} x, β s)` are trajectories of `V`.
* `TauCeti.exists_eq_timeDependentFlowOf_continuationSpaceField`: every trajectory of `V` through
  the slab is such a curve, up to translation of time.
* `TauCeti.IsAdaptedPseudoGradient.eqOn_timeDependentFlowOf_flow_of_lt`,
  `TauCeti.IsAdaptedPseudoGradient.eqOn_timeDependentFlowOf_flow_of_gt`: a time-dependent flow
  follows the flow of an adapted pseudo-gradient on the times where its field is that
  pseudo-gradient.
* `TauCeti.IsAdaptedPseudoGradient.tendsto_atBot_iff_timeDependentFlowOf_mem_unstableSet`,
  `TauCeti.IsAdaptedPseudoGradient.tendsto_atTop_iff_timeDependentFlowOf_mem_stableSet`: a
  time-dependent flow line `s ↦ φ_{τ, s} x` tends to a point `p` at `-∞`, resp. `+∞`,
  exactly when its value at one very negative, resp. very positive, time lies in the unstable,
  resp. stable, manifold of `p`.
* `TauCeti.IsContinuationField.eventually_atBot_continuationSpaceField_eq`,
  `TauCeti.IsContinuationField.eventually_atTop_continuationSpaceField_eq`: the space component
  along the base trajectory is `X₀` at very negative times and `X₁` at very positive times.
* `TauCeti.IsContinuationField.morseContinuationSlice_eq_preimage`,
  `TauCeti.IsContinuationField.eventually_morseContinuationSlice_eq_preimage`: the slices of the
  continuation map are preimages of unstable and stable manifolds under the transition maps, for
  times `a` and `b` beyond given windows on which the space component is `X₀` and `X₁`, and so
  for all sufficiently negative `a` and sufficiently positive `b`.
* `TauCeti.IsContinuationField.eventually_ncard_morseContinuationSlice_eq`: the slices have as
  many points as `W^u(p) ∩ φ_{a, b}⁻¹ (W^s(q))`.
* `TauCeti.IsContinuationField.eventually_morseContinuationCoeff_eq_ncard_inter_preimage`: the
  continuation coefficients count the points of `W^u(p) ∩ φ_{a, b}⁻¹ (W^s(q))` modulo two.
* `TauCeti.continuationTransition`: the transition map `φ_{a, b}` of a smooth field on `M × ℝ`,
  as a smooth diffeomorphism of `M`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1 (the continuation map, defined by a time-dependent
  pseudo-gradient interpolating between the two ends).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-! ### The space component along the base trajectory -/

/-- The **space component of a field `V` on `M × ℝ` along the base trajectory**: the
time-dependent vector field on `M` whose value at time `s` is the space component of `V` on the
level `t = β s` of the base trajectory `β = TauCeti.intervalBaseOrbit C`. When the time component
of `V` in the open slab is `C t (1 - t²)`, the trajectories of `V` through the slab are the curves
`s ↦ (x s, β (s + τ))` with `x' = Y (s + τ) x`. -/
noncomputable def continuationSpaceField (C : ℝ)
    (V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) (s : ℝ) (x : M) :
    TangentSpace 𝓘(ℝ, E) x :=
  (V (x, intervalBaseOrbit C s) : E × ℝ).1

variable {C : ℝ} {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

/-- The value of the space component along the base trajectory. -/
@[simp]
theorem continuationSpaceField_apply (s : ℝ) (x : M) :
    continuationSpaceField C V s x = (V (x, intervalBaseOrbit C s) : E × ℝ).1 :=
  (rfl)

/-- **The space component along the base trajectory is as smooth as the field**: for a `C^n`
vector field `V` on `M × ℝ`, the time-dependent field `continuationSpaceField C V` is jointly
`C^n` in the time and the point. -/
theorem contMDiff_continuationSpaceField [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ∞ω}
    (hV : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent n
      fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ))) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent n
      fun p : ℝ × M ↦ (⟨p.2, continuationSpaceField C V p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M) := by
  have hq : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ) n (intervalBaseOrbit C) :=
    contMDiff_iff_contDiff.2 (contDiff_intervalBaseOrbit C)
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, E).prod 𝓘(ℝ)) n
      fun p : ℝ × M ↦ (p.2, intervalBaseOrbit C p.1) :=
    contMDiff_snd.prodMk (hq.comp contMDiff_fst)
  -- The tangent bundle of `M × ℝ` splits as a product, and the first factor of the split
  -- section is the space component.
  exact contMDiff_fst.comp (contMDiff_equivTangentBundleProd.comp (hV.comp hg))

/-! ### Trajectories through the slab -/

section Trajectory

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) 1 M] [CompactSpace M] [T2Space M]
  (hsnd : ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 → (V z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2))
  (hV : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent 1
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

include hsnd hV in
/-- **The time-dependent flow along the base trajectory gives trajectories of `V`.** If the time
component of a `C¹` field `V` on `M × ℝ` is `C t (1 - t²)` in the open slab, then for every point
`x` of the compact manifold `M` and every time `τ`, the curve `s ↦ (φ_{τ, s} x, β s)` is an
integral curve of `V`, where `φ` is the time-dependent flow of `continuationSpaceField C V`. -/
theorem isMIntegralCurve_timeDependentFlowOf_continuationSpaceField (τ : ℝ) (x : M) :
    IsMIntegralCurve
      (fun s ↦ (timeDependentFlowOf (continuationSpaceField C V) τ s x, intervalBaseOrbit C s))
      V := by
  have hY := contMDiff_continuationSpaceField (C := C) hV
  intro s
  have h₁ := hasMFDerivAt_timeDependentFlowOf_of_compactSpace hY (s := τ) (t := s) (x := x)
  have h₂ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ) (intervalBaseOrbit C) s ((1 : ℝ →L[ℝ] ℝ).smulRight
      (C * intervalBaseOrbit C s * (1 - intervalBaseOrbit C s ^ 2))) :=
    hasMFDerivAt_iff_hasFDerivAt.2 (hasDerivAt_intervalBaseOrbit C s).hasFDerivAt
  have hV₂ : (V (timeDependentFlowOf (continuationSpaceField C V) τ s x, intervalBaseOrbit C s) :
      E × ℝ).2 = C * intervalBaseOrbit C s * (1 - intervalBaseOrbit C s ^ 2) :=
    hsnd _ (intervalBaseOrbit_mem_Ioo C s)
  -- Both derivatives send `r` to `(r • Y s (φ_{τ, s} x), r • C β s (1 - (β s)²))`, read in
  -- `E × ℝ`; the time component of `V` on the curve is `C β s (1 - (β s)²)`.
  exact (h₁.prodMk h₂).congr_mfderiv
    (ContinuousLinearMap.ext fun r ↦ Prod.ext rfl (congrArg (HSMul.hSMul (α := ℝ) r) hV₂.symm))

omit [FiniteDimensional ℝ E] [CompactSpace M] in
include hsnd hV in
/-- **Every trajectory of `V` through the slab comes from the time-dependent flow.** If the time
component of a `C¹` field `V` on `M × ℝ` is `C t (1 - t²)` in the open slab, with `C ≠ 0`, then
an integral curve `γ` of `V` which meets the open slab at time `0` is
`s ↦ (φ_{τ, s + τ} (γ 0).1, β (s + τ))` for some shift `τ`, where `φ` is the time-dependent flow
of `continuationSpaceField C V`. -/
theorem exists_eq_timeDependentFlowOf_continuationSpaceField (hC : C ≠ 0) {γ : ℝ → M × ℝ}
    (hγ : IsMIntegralCurve γ V) (h₀ : (γ 0).2 ∈ Ioo 0 1) :
    ∃ τ, ∀ s, γ s = (timeDependentFlowOf (continuationSpaceField C V) τ (s + τ) (γ 0).1,
      intervalBaseOrbit C (s + τ)) := by
  have hY := contMDiff_continuationSpaceField (C := C) hV
  obtain ⟨τ, hτ'⟩ := exists_snd_eq_intervalBaseOrbit hsnd hγ h₀ hC
  -- In the absolute time `u = s + τ`, the space component solves `x' = Y u x`.
  set δ : ℝ → M := fun u ↦ (γ (u - τ)).1 with hδ_def
  have hδ (u : ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) δ u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (continuationSpaceField C V u (δ u))) := by
    have hsub : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun u : ℝ ↦ u - τ) u (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id u).sub_const τ)
    have hpt : γ (u - τ) = (δ u, intervalBaseOrbit C u) :=
      Prod.ext rfl (by rw [hτ', sub_add_cancel])
    -- Both derivatives send `r` to `r • (V (δ u, q u)).1`, read in `E`.
    have hfst : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Prod.fst ∘ γ) (u - τ)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V (γ (u - τ)) : E × ℝ).1) :=
      (hγ (u - τ)).fst_curve
    refine (hfst.comp u hsub).congr_mfderiv (ContinuousLinearMap.ext fun r ↦ ?_)
    exact congrArg (fun z : M × ℝ ↦ HSMul.hSMul (α := ℝ) r (V z : E × ℝ).1) hpt
  refine ⟨τ, fun s ↦ Prod.ext ?_ (hτ' s)⟩
  have heq := timeDependentFlowOf_eq_of_hasMFDerivAt hY (γ := δ) (s := τ) (t := s + τ)
    (a := min τ (s + τ) - 1) (b := max τ (s + τ) + 1) (fun u _ ↦ hδ u)
    ⟨by linarith [min_le_left τ (s + τ)], by linarith [le_max_left τ (s + τ)]⟩
    ⟨by linarith [min_le_right τ (s + τ)], by linarith [le_max_right τ (s + τ)]⟩
  simp only [hδ_def, sub_self, add_sub_cancel_right] at heq
  exact heq.symm

end Trajectory

/-! ### Time-dependent flows which agree with a pseudo-gradient -/

section Ends

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} (hX : IsAdaptedPseudoGradient f X)
  {Y : ℝ → (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hY : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E).tangent 1
    fun p : ℝ × M ↦ (⟨p.2, Y p.1 p.2⟩ : TangentBundle 𝓘(ℝ, E) M))
  {τ a b : ℝ} {x p : M}

namespace IsAdaptedPseudoGradient

include hX hY

/-- **Before a time `b` up to which a time-dependent field is `X`, its flow follows the flow of
`X`.** If the `C¹` time-dependent field `Y` is the adapted pseudo-gradient `X` at all times
before `b`, then for `a < b` the curve `u ↦ φ_{τ, u} x` of its time-dependent flow is, up to time
`a`, the orbit of `φ_{τ, a} x` under the flow of `X`, shifted by `a`. -/
theorem eqOn_timeDependentFlowOf_flow_of_lt (hYX : ∀ u < b, Y u = X) (hab : a < b) :
    EqOn (fun u ↦ timeDependentFlowOf Y τ u x)
      (fun u ↦ hX.flow (u - a) (timeDependentFlowOf Y τ a x)) (Iic a) :=
  hX.eqOn_flow_of_isMIntegralCurveOn_Iio (isMIntegralCurveOn_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY) hY (T := Iio b) hYX) hab

/-- **After a time `a` from which on a time-dependent field is `X`, its flow follows the flow of
`X`.** If the `C¹` time-dependent field `Y` is the adapted pseudo-gradient `X` at all times after
`a`, then for `a < b` the curve `u ↦ φ_{τ, u} x` of its time-dependent flow is, from time `b` on,
the orbit of `φ_{τ, b} x` under the flow of `X`, shifted by `b`. -/
theorem eqOn_timeDependentFlowOf_flow_of_gt (hYX : ∀ u > a, Y u = X) (hab : a < b) :
    EqOn (fun u ↦ timeDependentFlowOf Y τ u x)
      (fun u ↦ hX.flow (u - b) (timeDependentFlowOf Y τ b x)) (Ici b) :=
  hX.eqOn_flow_of_isMIntegralCurveOn_Ioi (isMIntegralCurveOn_timeDependentFlowOf
    (isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY) hY (T := Ioi a) hYX) hab

/-- **A time-dependent flow line tends to a point at `-∞` along its unstable manifold.** If the
`C¹` time-dependent field `Y` is the adapted pseudo-gradient `X` at all times before `b`, and
`a < b`, then the curve `s ↦ φ_{τ, s} x` of its time-dependent flow tends to `p` at `-∞` exactly
when `φ_{τ, a} x` lies in the unstable manifold of `p` for `X`. -/
theorem tendsto_atBot_iff_timeDependentFlowOf_mem_unstableSet (hYX : ∀ u < b, Y u = X)
    (hab : a < b) :
    Tendsto (fun s ↦ timeDependentFlowOf Y τ s x) atBot (𝓝 p) ↔
      timeDependentFlowOf Y τ a x ∈ hX.flow.unstableSet p :=
  Flow.tendsto_atBot_iff_mem_unstableSet_of_eqOn (hX.eqOn_timeDependentFlowOf_flow_of_lt hY hYX hab)

/-- **A time-dependent flow line tends to a point at `+∞` along its stable manifold.** If the
`C¹` time-dependent field `Y` is the adapted pseudo-gradient `X` at all times after `a`, and
`a < b`, then the curve `s ↦ φ_{τ, s} x` of its time-dependent flow tends to `p` at `+∞` exactly
when `φ_{τ, b} x` lies in the stable manifold of `p` for `X`. -/
theorem tendsto_atTop_iff_timeDependentFlowOf_mem_stableSet (hYX : ∀ u > a, Y u = X)
    (hab : a < b) :
    Tendsto (fun s ↦ timeDependentFlowOf Y τ s x) atTop (𝓝 p) ↔
      timeDependentFlowOf Y τ b x ∈ hX.flow.stableSet p :=
  Flow.tendsto_atTop_iff_mem_stableSet_of_eqOn (hX.eqOn_timeDependentFlowOf_flow_of_gt hY hYX hab)

end IsAdaptedPseudoGradient

end Ends

/-! ### The slices of the continuation map -/

namespace IsContinuationField

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  (hV : IsContinuationField X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C)
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent 1
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
include hV hC in
/-- For `C > 0`, the space component of a continuation field from `X₀` along the base trajectory
is `X₀` at all sufficiently negative times. -/
theorem eventually_atBot_continuationSpaceField_eq :
    ∀ᶠ s in atBot, continuationSpaceField C V s = X₀ := by
  filter_upwards [(tendsto_intervalBaseOrbit_atBot_nhdsGT hC).eventually hV.eventually_fst_eq_left]
    with s hs
  exact funext fun x ↦ hs x

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
include hV hC in
/-- For `C > 0`, the space component of a continuation field to `X₁` along the base trajectory
is `X₁` at all sufficiently positive times. -/
theorem eventually_atTop_continuationSpaceField_eq :
    ∀ᶠ s in atTop, continuationSpaceField C V s = X₁ := by
  filter_upwards [(tendsto_intervalBaseOrbit_atTop_nhdsLT hC).eventually hV.eventually_fst_eq_right]
    with s hs
  exact funext fun x ↦ hs x

include hV hX₀ hX₁ hC hVs in
/-- **The slices of the continuation map through given transition maps of the slab.** Let `V` be
a `C¹` continuation field from `X₀` to `X₁` at rate `C > 0`, let `φ` be the time-dependent flow of
its space component `continuationSpaceField C V` along the base trajectory `β`, and let `σ` be
the time at which `β σ = 1 / 2`. If the space component is `X₀` at all times before `a₀` and `X₁`
at all times after `b₀`, then for `a < a₀` and `b₀ < b` the points on the middle level of the
trajectories from `(p, 0)` to `(q, 1)` are the points `x` with `φ_{σ, a} x` in the unstable
manifold of `p` for `X₀` and `φ_{σ, b} x` in the stable manifold of `q` for `X₁`. -/
theorem morseContinuationSlice_eq_preimage {σ : ℝ} (hσ : intervalBaseOrbit C σ = 1 / 2)
    {a₀ b₀ a b : ℝ} (ha₀ : ∀ s < a₀, continuationSpaceField C V s = X₀)
    (hb₀ : ∀ s > b₀, continuationSpaceField C V s = X₁) (ha : a < a₀) (hb : b₀ < b) (p q : M) :
    morseContinuationSlice V p q =
      timeDependentFlowOf (continuationSpaceField C V) σ a ⁻¹' hX₀.flow.unstableSet p ∩
        timeDependentFlowOf (continuationSpaceField C V) σ b ⁻¹' hX₁.flow.stableSet q := by
  have hY := contMDiff_continuationSpaceField (C := C) hVs
  have hsnd := hV.snd_eq
  -- The trajectory through `(x, 1 / 2)` at time `0`, in the time of the base trajectory.
  set Γ : M → ℝ → M × ℝ := fun x s ↦
    (timeDependentFlowOf (continuationSpaceField C V) σ (s + σ) x, intervalBaseOrbit C (s + σ))
  have hΓ (x : M) : IsMIntegralCurve (Γ x) V :=
    (isMIntegralCurve_timeDependentFlowOf_continuationSpaceField hsnd hVs σ x).comp_add σ
  -- Its limits at the two ends are read off the transition maps to the times `a` and `b`.
  -- The time component tends to `0` and `1`, and the shift by `σ` does not change the limits.
  have hbot (x : M) : Tendsto (Γ x) atBot (𝓝 (p, 0)) ↔
      timeDependentFlowOf (continuationSpaceField C V) σ a x ∈ hX₀.flow.unstableSet p := by
    have hβ : Tendsto (fun s ↦ (Γ x s).2) atBot (𝓝 0) :=
      (tendsto_intervalBaseOrbit_atBot hC).comp (tendsto_atBot_add_const_right _ σ tendsto_id)
    rw [nhds_prod_eq, tendsto_prod_iff', and_iff_left hβ,
      ← hX₀.tendsto_atBot_iff_timeDependentFlowOf_mem_unstableSet hY ha₀ ha]
    exact ⟨fun h ↦ (h.comp (tendsto_atBot_add_const_right _ (-σ) tendsto_id)).congr
      fun u ↦ by simp [Γ], fun h ↦ h.comp (tendsto_atBot_add_const_right _ σ tendsto_id)⟩
  have htop (x : M) : Tendsto (Γ x) atTop (𝓝 (q, 1)) ↔
      timeDependentFlowOf (continuationSpaceField C V) σ b x ∈ hX₁.flow.stableSet q := by
    have hβ : Tendsto (fun s ↦ (Γ x s).2) atTop (𝓝 1) :=
      (tendsto_intervalBaseOrbit_atTop hC).comp (tendsto_atTop_add_const_right _ σ tendsto_id)
    rw [nhds_prod_eq, tendsto_prod_iff', and_iff_left hβ,
      ← hX₁.tendsto_atTop_iff_timeDependentFlowOf_mem_stableSet hY hb₀ hb]
    exact ⟨fun h ↦ (h.comp (tendsto_atTop_add_const_right _ (-σ) tendsto_id)).congr
      fun u ↦ by simp [Γ], fun h ↦ h.comp (tendsto_atTop_add_const_right _ σ tendsto_id)⟩
  ext x
  simp only [mem_morseContinuationSlice, mem_inter_iff, mem_preimage]
  refine ⟨fun ⟨γ, hγ, hγ0, hp, hq⟩ ↦ ?_, fun ⟨hp, hq⟩ ↦
    ⟨Γ x, hΓ x, by simp [Γ, hσ, timeDependentFlowOf_self], (hbot x).2 hp, (htop x).2 hq⟩⟩
  -- Every trajectory through `(x, 1 / 2)` is `Γ x`: its shift is the time `σ` of the level.
  have h₀ : (γ 0).2 ∈ Ioo 0 1 := by rw [hγ0]; norm_num
  obtain ⟨τ, hτ⟩ := exists_eq_timeDependentFlowOf_continuationSpaceField hsnd hVs hC.ne' hγ h₀
  have hτσ : τ = σ := by
    have h := congrArg Prod.snd (hτ 0)
    simp only [hγ0, zero_add] at h
    exact intervalBaseOrbit_injective hC.ne' (h.symm.trans hσ.symm)
  have hγΓ : γ = Γ x := funext fun s ↦ by rw [hτ s, hγ0, hτσ]
  rw [hγΓ] at hp hq
  exact ⟨(hbot x).1 hp, (htop x).1 hq⟩

include hV hX₀ hX₁ hC hVs in
/-- **The slices of the continuation map through the transition maps of the slab.** Let `V` be a
`C¹` continuation field from `X₀` to `X₁` at rate `C > 0`, let `φ` be the time-dependent flow of
its space component `continuationSpaceField C V` along the base trajectory `β`, and let `σ` be
the time at which `β σ = 1 / 2`. Then for every sufficiently negative time `a` and every
sufficiently positive time `b`, the points on the middle level of the trajectories from `(p, 0)`
to `(q, 1)` are the points `x` with `φ_{σ, a} x` in the unstable manifold of `p` for `X₀` and
`φ_{σ, b} x` in the stable manifold of `q` for `X₁`, for all `p` and `q` at once. -/
theorem eventually_morseContinuationSlice_eq_preimage {σ : ℝ}
    (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M, morseContinuationSlice V p q =
      timeDependentFlowOf (continuationSpaceField C V) σ a ⁻¹' hX₀.flow.unstableSet p ∩
        timeDependentFlowOf (continuationSpaceField C V) σ b ⁻¹' hX₁.flow.stableSet q := by
  obtain ⟨a₀, ha₀⟩ := eventually_atBot.1 (hV.eventually_atBot_continuationSpaceField_eq hC)
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hV.eventually_atTop_continuationSpaceField_eq hC)
  filter_upwards [eventually_lt_atBot a₀] with a ha
  filter_upwards [eventually_gt_atTop b₀] with b hb
  exact hV.morseContinuationSlice_eq_preimage hX₀ hX₁ hC hVs hσ (fun s hs ↦ ha₀ s hs.le)
    (fun s hs ↦ hb₀ s hs.le) ha hb

include hV hX₀ hX₁ hC hVs in
/-- **The continuation slices count the intersections through the transition maps.** Let `V` be a
`C¹` continuation field from `X₀` to `X₁` at rate `C > 0`, and let `φ` be the time-dependent flow
of its space component `continuationSpaceField C V` along the base trajectory. Then for every
sufficiently negative time `a` and every sufficiently positive time `b`, the continuation
trajectories from `(p, 0)` to `(q, 1)` are as many as the points of the unstable manifold of `p`
for `X₀` which the transition map `φ_{a, b}` of the slab carries into the stable manifold of `q`
for `X₁`, for all `p` and `q` at once. -/
theorem eventually_ncard_morseContinuationSlice_eq :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M, (morseContinuationSlice V p q).ncard =
      (hX₀.flow.unstableSet p ∩
        timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q).ncard := by
  have hY := contMDiff_continuationSpaceField (C := C) hVs
  have hcomp := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_morseContinuationSlice_eq_preimage hX₀ hX₁ hC hVs hσ] with a ha
  filter_upwards [ha] with b hb p q
  set φ := timeDependentFlowOf (continuationSpaceField C V)
  -- The slice is the preimage of `W^u(p) ∩ φ_{a, b}⁻¹ (W^s(q))` under the diffeomorphism
  -- `φ_{σ, a}`.
  have hpre : φ σ a ⁻¹' hX₀.flow.unstableSet p ∩ φ σ b ⁻¹' hX₁.flow.stableSet q =
      φ σ a ⁻¹' (hX₀.flow.unstableSet p ∩ φ a b ⁻¹' hX₁.flow.stableSet q) := by
    ext x
    simp [φ, timeDependentFlowOf_trans hcomp hY]
  set Φ := (timeDependentFlowDiffeomorph hcomp le_rfl hY σ a).toEquiv
  have hΦ : ⇑Φ = φ σ a := funext (timeDependentFlowDiffeomorph_apply hcomp le_rfl hY σ a)
  rw [hb, hpre, ← hΦ,
    Set.ncard_preimage_of_injective_subset_range Φ.injective fun y _ ↦ Φ.surjective y]

include hV hX₀ hX₁ hC hVs in
/-- **The continuation coefficients are intersection counts.** Let `V` be a `C¹` continuation
field from `X₀` to `X₁` at rate `C > 0`, between pseudo-gradients adapted to Morse functions `f₀`
and `f₁`, and let `φ` be the time-dependent flow of its space component
`continuationSpaceField C V` along the base trajectory. Then for every sufficiently negative time
`a` and every sufficiently positive time `b`, and all critical points `p` of `f₀` and `q` of `f₁`
of equal index, the coefficient of `q` in the continuation of `p` is the number, modulo two, of
points of the unstable manifold of `p` for `X₀` which the transition map `φ_{a, b}` of the slab
carries into the stable manifold of `q` for `X₁`. -/
theorem eventually_morseContinuationCoeff_eq_ncard_inter_preimage :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ (p : criticalPoints 𝓘(ℝ, E) f₀)
      (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
        morseContinuationCoeff f₀ f₁ V p q = ((hX₀.flow.unstableSet p ∩
          timeDependentFlowOf (continuationSpaceField C V) a b ⁻¹' hX₁.flow.stableSet q).ncard :
            ZMod 2) := by
  filter_upwards [hV.eventually_ncard_morseContinuationSlice_eq hX₀ hX₁ hC hVs] with a ha
  filter_upwards [ha] with b hb p q hind
  rw [TauCeti.morseContinuationCoeff_eq_ncard hind, hb]

end IsContinuationField

/-! ### The transition diffeomorphism -/

section TransitionDiffeomorph

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  (hVs : ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent ∞
    fun z ↦ (⟨z, V z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

variable (C) in
/-- The **transition diffeomorphism** from time `a` to time `b` of a smooth field `V` on `M × ℝ`:
the time-dependent flow `φ_{a, b}` of the space component of `V` along the base trajectory
`TauCeti.intervalBaseOrbit C` (`TauCeti.continuationSpaceField`), a smooth diffeomorphism of the
compact manifold `M`. For a continuation field, very negative `a` and very positive `b`, it
carries the level of the slab where `V` is `X₀` to the level where `V` is `X₁`. -/
noncomputable def continuationTransition (a b : ℝ) : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  timeDependentFlowDiffeomorph
    (isCompleteVectorField_timeDependentSuspensionField_of_compactSpace
      ((contMDiff_continuationSpaceField (C := C) hVs).of_le (by simp)))
    (n := ⊤) le_top (contMDiff_continuationSpaceField (C := C) hVs) a b

/-- The transition diffeomorphism is the time-dependent flow of the space component. -/
@[simp]
theorem coe_continuationTransition (a b : ℝ) :
    ⇑(continuationTransition C hVs a b) = timeDependentFlowOf (continuationSpaceField C V) a b :=
  funext (timeDependentFlowDiffeomorph_apply _ _ _ a b)

/-- The inverse of the transition diffeomorphism from `a` to `b` is the time-dependent flow of the
space component from `b` to `a`. -/
@[simp]
theorem continuationTransition_symm_apply (a b : ℝ) (x : M) :
    (continuationTransition C hVs a b).symm x =
      timeDependentFlowOf (continuationSpaceField C V) b a x :=
  timeDependentFlowDiffeomorph_symm_apply _ _ _ a b x

end TransitionDiffeomorph

end TauCeti

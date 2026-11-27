/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle.Tangent
public import TauCeti.Geometry.Manifold.Morse.Circle
public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transition
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Diffeomorph
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Continuation fields along paths of rotations of the circle

On the circle `S¹ = ℝ ⧸ 2πℤ` the functions `f_r(θ) = δ cos (2 (θ - r))`
(`TauCeti.circleCosTwo δ r`) are the rotations of `f_0` by the angle `r`. This file builds
continuation data along a path of angles `t ↦ r t` from adapted pseudo-gradients, and shows that
for large rates the transition diffeomorphism of the slab is the composite of the two end flows and
of a map moving every angle as little as we like. The rotations of vector fields, the rotating
continuation field and the drift estimate make sense on a circle `ℝ ⧸ pℤ` of any period.

**Rotated pseudo-gradients.** Let `X` be a pseudo-gradient adapted to `f_0`. Its rotation
`θ ↦ X (θ - r)` (`TauCeti.circleRotatedField X r`) is the pullback of `X` along the rotation
`θ ↦ θ - r`, which carries `f_0` to `f_r`, so it is a pseudo-gradient adapted to `f_r`
(`TauCeti.IsAdaptedPseudoGradient.circleRotatedField`).

**The rotating continuation field.** For a smooth path `r` and a rate `C`, the field
`C t (1 - t²) ∂_t + X (θ - r t)` on the cylinder `S¹ × ℝ`
(`TauCeti.circleRotatingContinuationField X r C`) is smooth
(`TauCeti.contMDiff_circleRotatingContinuationField`). If `r = r₀` for `t ≤ t₀` and `r = r₁` for
`t ≥ t₁`, it is a continuation field at rate `C` from the rotation of `X` by `r₀` to its rotation by
`r₁` (`TauCeti.isContinuationField_circleRotatingContinuationField`).

**The window.** Along the base trajectory of rate `C > 0` the level `t ∈ (0, 1)` is reached at the
time `U(t) / C`, where `U(t) = log t - (1 / 2) log (1 - t²)`
(`TauCeti.intervalBaseTimeCoordinate`). So the space component of the rotating field along the base
trajectory is the rotation of `X` by `r₀` before the time `U(t₀) / C` and its rotation by `r₁` after
the time `U(t₁) / C`. For window times `s₀ < U(t₀) / C` and `s₁ > U(t₁) / C`, the transition
diffeomorphism from a time `a ≤ s₀` to a time `b ≥ s₁` is therefore the flow of the rotation by
`r₀` for the time `s₀ - a`, then the time-dependent flow across the window from `s₀` to `s₁`, then
the flow of the rotation by `r₁` for the time `b - s₁`; its inverse decomposes in the same way
(`TauCeti.continuationTransition_circleRotatingContinuationField_apply`,
`TauCeti.continuationTransition_circleRotatingContinuationField_symm_apply`).

**The drift estimate.** If `|X| ≤ L`, the time-dependent flow of the space component moves each
angle by at most `L |t - s|` from the time `s` to the time `t`
(`TauCeti.dist_timeDependentFlowOf_circleRotatingContinuationField_le`). The window times
`s₀ = (U(t₀) - 1) / C` and `s₁ = (U(t₁) + 1) / C` are `(U(t₁) - U(t₀) + 2) / C` apart, so for every
`ε > 0` and all large rates `C` the flow across the window, forwards and backwards, moves every
angle by less than `ε`
(`TauCeti.eventually_dist_timeDependentFlowOf_circleRotatingContinuationField_lt`).
This is the estimate of the circle continuation examples that the transition diffeomorphism across
the window moves every lifted angle by less than `π / 12`, forwards and backwards. There it is
obtained for the gradient field of `f_r` by taking the amplitude `δ` small; an adapted
pseudo-gradient is linear in Morse charts with weights `±1`, so it cannot be scaled down, and the
rate `C` is made large instead, which is the same after rescaling time.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.circleRotatedField`: rotating an adapted pseudo-gradient of
  `f_0` by `r` gives one of `f_r`.
* `TauCeti.isContinuationField_circleRotatingContinuationField`,
  `TauCeti.contMDiff_circleRotatingContinuationField`: the rotating field is a smooth continuation
  field.
* `TauCeti.continuationTransition_circleRotatingContinuationField_apply`,
  `TauCeti.continuationTransition_circleRotatingContinuationField_symm_apply`: the transition
  diffeomorphism and its inverse through the window.
* `TauCeti.dist_timeDependentFlowOf_circleRotatingContinuationField_le`,
  `TauCeti.eventually_dist_timeDependentFlowOf_circleRotatingContinuationField_lt`: the drift
  estimate, and the window drift is small for large rates.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.1–4.2 (continuation maps).
-/

public section

open Filter Function Module Set
open scoped ContDiff Manifold Real Topology

namespace TauCeti

variable {p : ℝ} [Fact (0 < p)] {X : (θ : AddCircle p) → TangentSpace 𝓘(ℝ) θ}

/-! ### Rotated fields and the rotating continuation field -/

/-- **The rotation of a vector field on the circle** by the angle `r`: the field `θ ↦ X (θ - r)`,
read in the common tangent line `ℝ` of the circle. -/
noncomputable def circleRotatedField (X : (θ : AddCircle p) → TangentSpace 𝓘(ℝ) θ) (r : ℝ)
    (θ : AddCircle p) : TangentSpace 𝓘(ℝ) θ :=
  X (θ - r)

@[simp]
theorem circleRotatedField_apply (r : ℝ) (θ : AddCircle p) :
    circleRotatedField X r θ = X (θ - r) :=
  (rfl)

/-- **The rotating continuation field** of a vector field `X` on the circle along a path of angles
`r`, at rate `C`: the field `C t (1 - t²) ∂_t + X (θ - r t)` on the cylinder `S¹ × ℝ`, whose space
component at the level `t` is the rotation of `X` by `r t`. -/
noncomputable def circleRotatingContinuationField
    (X : (θ : AddCircle p) → TangentSpace 𝓘(ℝ) θ) (r : ℝ → ℝ) (C : ℝ)
    (z : AddCircle p × ℝ) : TangentSpace (𝓘(ℝ).prod 𝓘(ℝ)) z :=
  ((X (z.1 - r z.2) : ℝ), C * z.2 * (1 - z.2 ^ 2))

@[simp]
theorem circleRotatingContinuationField_apply (r : ℝ → ℝ) (C : ℝ) (z : AddCircle p × ℝ) :
    circleRotatingContinuationField X r C z = ((X (z.1 - r z.2) : ℝ), C * z.2 * (1 - z.2 ^ 2)) :=
  (rfl)

/-- **The rotating continuation field is smooth** when `X` and the path `r` are. -/
theorem contMDiff_circleRotatingContinuationField
    (hX : ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent ∞
      fun θ ↦ (⟨θ, X θ⟩ : TangentBundle 𝓘(ℝ) (AddCircle p)))
    {r : ℝ → ℝ} (hr : ContDiff ℝ ∞ r) (C : ℝ) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)).tangent ∞ fun z ↦
      (⟨z, circleRotatingContinuationField X r C z⟩ :
        TangentBundle (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × ℝ)) := by
  have hXr : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ fun θ : AddCircle p ↦ (X θ : ℝ) :=
    (AddCircle.contMDiff_totalSpace_mk_iff.1 hX).2
  have hsub : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      fun z : AddCircle p × ℝ ↦ z.1 - (r z.2 : AddCircle p) :=
    contMDiff_fst.sub (((AddCircle.contMDiff_coe _ _).comp hr.contMDiff).comp contMDiff_snd)
  have h₁ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ).tangent ∞ fun z : AddCircle p × ℝ ↦
      (⟨z.1, X (z.1 - r z.2)⟩ : TangentBundle 𝓘(ℝ) (AddCircle p)) :=
    AddCircle.contMDiff_totalSpace_mk_iff.2 ⟨contMDiff_fst, hXr.comp hsub⟩
  have h₂ : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ).tangent ∞ fun z : AddCircle p × ℝ ↦
      (⟨z.2, C * z.2 * (1 - z.2 ^ 2)⟩ : TangentBundle 𝓘(ℝ) ℝ) := by
    have hg : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
        fun z : AddCircle p × ℝ ↦ C * z.2 * (1 - z.2 ^ 2) :=
      (by fun_prop : ContDiff ℝ ∞ fun t : ℝ ↦ C * t * (1 - t ^ 2)).contMDiff.comp contMDiff_snd
    -- The trivializations of the tangent bundle of the model space `ℝ` are the identity.
    refine fun z ↦ Bundle.contMDiffAt_totalSpace_iff.2 ⟨contMDiff_snd.contMDiffAt, ?_⟩
    simp only [trivializationAt_model_space_apply]
    exact hg.contMDiffAt
  exact contMDiff_equivTangentBundleProd_symm.comp (h₁.prodMk h₂)

/-- **The rotating continuation field is a continuation field.** If the path `r` is `r₀` for
`t ≤ t₀` and `r₁` for `t ≥ t₁`, where `0 < t₀` and `t₁ < 1`, the rotating continuation field at
rate `C` is a continuation field from the rotation of `X` by `r₀` to its rotation by `r₁`. -/
theorem isContinuationField_circleRotatingContinuationField {r : ℝ → ℝ} {r₀ r₁ t₀ t₁ : ℝ}
    (ht₀ : 0 < t₀) (ht₁ : t₁ < 1) (hr₀ : ∀ t ≤ t₀, r t = r₀) (hr₁ : ∀ t ≥ t₁, r t = r₁) (C : ℝ) :
    IsContinuationField (circleRotatedField X r₀) (circleRotatedField X r₁) C
      (circleRotatingContinuationField X r C) where
  snd_eq _ _ := rfl
  eventually_fst_eq_left := by
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht x
    simp only [circleRotatingContinuationField_apply, circleRotatedField_apply]
    rw [hr₀ t ht.2.le]
  eventually_fst_eq_right := by
    filter_upwards [Ioo_mem_nhdsLT ht₁] with t ht x
    simp only [circleRotatingContinuationField_apply, circleRotatedField_apply]
    rw [hr₁ t ht.1.le]

/-! ### The window -/

section Window

variable {r : ℝ → ℝ} {r₀ r₁ t₀ t₁ C : ℝ}

/-- **The space component before the window.** Before the time `U(t₀) / C` at which the base
trajectory of rate `C > 0` reaches the level `t₀ ∈ (0, 1)`, the space component of the rotating
field is the rotation of `X` by `r₀`, if `r = r₀` up to `t₀`. -/
theorem continuationSpaceField_circleRotatingContinuationField_of_lt (hC : 0 < C)
    (ht₀ : t₀ ∈ Ioo 0 1) (hr₀ : ∀ t ≤ t₀, r t = r₀) {s : ℝ}
    (hs : s < intervalBaseTimeCoordinate t₀ / C) :
    continuationSpaceField C (circleRotatingContinuationField X r C) s =
      circleRotatedField X r₀ := by
  have hβ : intervalBaseOrbit C s < t₀ := by
    refine (strictMonoOn_intervalBaseTimeCoordinate.lt_iff_lt (intervalBaseOrbit_mem_Ioo C s)
      ht₀).1 ?_
    rw [intervalBaseTimeCoordinate_intervalBaseOrbit]
    rwa [lt_div_iff₀ hC, mul_comm] at hs
  funext θ
  simp only [continuationSpaceField_apply, circleRotatingContinuationField_apply,
    circleRotatedField_apply]
  rw [hr₀ _ hβ.le]

/-- **The space component after the window.** After the time `U(t₁) / C` at which the base
trajectory of rate `C > 0` reaches the level `t₁ ∈ (0, 1)`, the space component of the rotating
field is the rotation of `X` by `r₁`, if `r = r₁` from `t₁` on. -/
theorem continuationSpaceField_circleRotatingContinuationField_of_gt (hC : 0 < C)
    (ht₁ : t₁ ∈ Ioo 0 1) (hr₁ : ∀ t ≥ t₁, r t = r₁) {s : ℝ}
    (hs : intervalBaseTimeCoordinate t₁ / C < s) :
    continuationSpaceField C (circleRotatingContinuationField X r C) s =
      circleRotatedField X r₁ := by
  have hβ : t₁ < intervalBaseOrbit C s := by
    refine (strictMonoOn_intervalBaseTimeCoordinate.lt_iff_lt ht₁
      (intervalBaseOrbit_mem_Ioo C s)).1 ?_
    rw [intervalBaseTimeCoordinate_intervalBaseOrbit]
    rwa [div_lt_iff₀ hC, mul_comm] at hs
  funext θ
  simp only [continuationSpaceField_apply, circleRotatingContinuationField_apply,
    circleRotatedField_apply]
  rw [hr₁ _ hβ.le]

variable (hXs : ContMDiff 𝓘(ℝ) 𝓘(ℝ).tangent ∞
    fun θ ↦ (⟨θ, X θ⟩ : TangentBundle 𝓘(ℝ) (AddCircle p))) (hr : ContDiff ℝ ∞ r)
include hXs hr

/-- The space component of the rotating field is jointly `C¹` in the time and the angle. -/
private theorem contMDiff_continuationSpaceField_circleRotating :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ)) 𝓘(ℝ).tangent 1 fun z : ℝ × AddCircle p ↦
      (⟨z.2, continuationSpaceField C (circleRotatingContinuationField X r C) z.1 z.2⟩ :
        TangentBundle 𝓘(ℝ) (AddCircle p)) :=
  contMDiff_continuationSpaceField
    ((contMDiff_circleRotatingContinuationField hXs hr C).of_le (by simp))

/-- **The drift estimate.** If `|X| ≤ L`, the time-dependent flow of the space component of the
rotating field moves each angle by at most `L |t - s|` from the time `s` to the time `t`. -/
theorem dist_timeDependentFlowOf_circleRotatingContinuationField_le {L : ℝ}
    (hL : ∀ θ, abs (α := ℝ) (X θ) ≤ L) (s t : ℝ) (θ : AddCircle p) :
    dist (timeDependentFlowOf (continuationSpaceField C (circleRotatingContinuationField X r C))
      s t θ) θ ≤ L * |t - s| := by
  have hY := contMDiff_continuationSpaceField_circleRotating (C := C) hXs hr
  have h := AddCircle.dist_le_mul_of_hasMFDerivAt (s := s) (t := t) (L := L)
    (fun u ↦ hasMFDerivAt_timeDependentFlowOf_of_compactSpace hY (s := s) (t := u) (x := θ))
    (fun u _ ↦ by
      simp only [continuationSpaceField_apply, circleRotatingContinuationField_apply]
      exact hL _)
  rwa [timeDependentFlowOf_self] at h

/-- **The window drift is small for large rates.** For every `ε > 0` and all large rates `C`, the
time-dependent flow of the space component of the rotating field across the window from
`s₀ = (U(t₀) - 1) / C` to `s₁ = (U(t₁) + 1) / C`, forwards and backwards, moves every angle by less
than `ε`. -/
theorem eventually_dist_timeDependentFlowOf_circleRotatingContinuationField_lt (t₀ t₁ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ C in atTop, ∀ θ : AddCircle p,
      dist (timeDependentFlowOf (continuationSpaceField C (circleRotatingContinuationField X r C))
        ((intervalBaseTimeCoordinate t₀ - 1) / C) ((intervalBaseTimeCoordinate t₁ + 1) / C) θ)
          θ < ε ∧
      dist (timeDependentFlowOf (continuationSpaceField C (circleRotatingContinuationField X r C))
        ((intervalBaseTimeCoordinate t₁ + 1) / C) ((intervalBaseTimeCoordinate t₀ - 1) / C) θ)
          θ < ε := by
  -- A bound `L ≥ 0` for `|X|`, by compactness of the circle.
  obtain ⟨L, hL⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun θ : AddCircle p ↦ (X θ : ℝ))
    (AddCircle.contMDiff_totalSpace_mk_iff.1 hXs).2.continuous.continuousOn
  have hL' (θ : AddCircle p) : abs (α := ℝ) (X θ) ≤ max L 0 :=
    (hL θ (mem_univ θ)).trans (le_max_left L 0)
  set K := |intervalBaseTimeCoordinate t₁ + 1 - (intervalBaseTimeCoordinate t₀ - 1)|
  filter_upwards [eventually_gt_atTop 0, eventually_gt_atTop (max L 0 * K / ε)] with C hC hCL θ
  -- The window has length `K / C`, and `max L 0 * K / C < ε`.
  have hdrift : max L 0 * |(intervalBaseTimeCoordinate t₁ + 1) / C -
      (intervalBaseTimeCoordinate t₀ - 1) / C| < ε := by
    rw [← sub_div, abs_div, abs_of_pos hC, mul_div_assoc', div_lt_iff₀ hC]
    have h := (div_lt_iff₀ hε).1 hCL
    linarith
  refine ⟨(dist_timeDependentFlowOf_circleRotatingContinuationField_le hXs hr hL' _ _ _).trans_lt
    hdrift, (dist_timeDependentFlowOf_circleRotatingContinuationField_le hXs hr hL' _ _ _).trans_lt
    (by rwa [abs_sub_comm])⟩

end Window

/-! ### Rotated adapted pseudo-gradients of `δ cos (2 θ)` -/

section Adapted

local instance circleRotatingTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

variable {δ : ℝ} {X : (θ : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) θ}

/-- **Rotated adapted pseudo-gradients.** If `X` is a pseudo-gradient adapted to `δ cos (2 θ)`, its
rotation by `r` is a pseudo-gradient adapted to `δ cos (2 (θ - r))`: it is the pullback of `X`
along the rotation `θ ↦ θ - r`, a diffeomorphism of the circle whose differential is the
identity. -/
protected theorem IsAdaptedPseudoGradient.circleRotatedField
    (hX : IsAdaptedPseudoGradient (circleCosTwo δ 0) X) (r : ℝ) :
    IsAdaptedPseudoGradient (circleCosTwo δ r) (circleRotatedField X r) := by
  set σ := Lie.addZSMulDiffeomorph 𝓘(ℝ) ∞ (-(r : AddCircle (2 * π))) 1 (by norm_num)
  have hσ : ⇑σ = (· + (-(r : AddCircle (2 * π)))) := funext fun θ ↦ by
    simp only [σ, Lie.addZSMulDiffeomorph_apply, one_zsmul, add_comm]
  have h := hX.mpullback σ
  have hσθ (θ : AddCircle (2 * π)) : σ θ = θ - r := by rw [hσ, sub_eq_add_neg]
  have hf : circleCosTwo δ 0 ∘ σ = circleCosTwo δ r := funext fun θ ↦ by
    rw [comp_apply, hσθ, circleCosTwo_zero_apply_sub]
  -- The differential of the rotation is the identity, so the pullback of `X` is `X ∘ σ`.
  have hV : VectorField.mpullback 𝓘(ℝ) 𝓘(ℝ) σ X = circleRotatedField X r := funext fun θ ↦ by
    have hd : mfderiv 𝓘(ℝ) 𝓘(ℝ) σ θ = ContinuousLinearMap.id ℝ ℝ := by
      rw [hσ]
      exact AddCircle.mfderiv_add_right (2 * π) (-(r : AddCircle (2 * π))) θ
    have h₁ := σ.mfderiv_apply_mpullback (by simp) X θ
    rw [hd] at h₁
    rw [circleRotatedField_apply, ← hσθ]
    -- `h₁` applies the identity of the tangent line `ℝ` to the left-hand side.
    exact h₁
  rwa [hf, hV] at h

variable {r : ℝ → ℝ} {r₀ r₁ t₀ t₁ C : ℝ} (hX : IsAdaptedPseudoGradient (circleCosTwo δ 0) X)
  (hr : ContDiff ℝ ∞ r) (ht₀ : t₀ ∈ Ioo 0 1) (ht₁ : t₁ ∈ Ioo 0 1) (hr₀ : ∀ t ≤ t₀, r t = r₀)
  (hr₁ : ∀ t ≥ t₁, r t = r₁) (hC : 0 < C) {s₀ s₁ a b : ℝ}
  (hs₀ : s₀ < intervalBaseTimeCoordinate t₀ / C) (hs₁ : intervalBaseTimeCoordinate t₁ / C < s₁)
  (ha : a ≤ s₀) (hb : s₁ ≤ b)
include hX hr ht₀ ht₁ hr₀ hr₁ hC hs₀ hs₁ ha hb

/-- **The transition diffeomorphism through the window.** For window times `s₀ < U(t₀) / C` and
`s₁ > U(t₁) / C`, the transition diffeomorphism of the rotating field from a time `a ≤ s₀` to a
time `b ≥ s₁` is the flow of the rotation of `X` by `r₀` for the time `s₀ - a`, then the
time-dependent flow across the window from `s₀` to `s₁`, then the flow of the rotation of `X` by
`r₁` for the time `b - s₁`. -/
theorem continuationTransition_circleRotatingContinuationField_apply (θ : AddCircle (2 * π)) :
    continuationTransition C (contMDiff_circleRotatingContinuationField hX.contMDiff hr C) a b θ =
      (hX.circleRotatedField r₁).flow (b - s₁)
        (timeDependentFlowOf (continuationSpaceField C (circleRotatingContinuationField X r C))
          s₀ s₁ ((hX.circleRotatedField r₀).flow (s₀ - a) θ)) := by
  rw [coe_continuationTransition]
  exact timeDependentFlowOf_eq_flow_timeDependentFlowOf_flow (hX.circleRotatedField r₀)
    (hX.circleRotatedField r₁) (contMDiff_continuationSpaceField_circleRotating hX.contMDiff hr)
    (fun u hu ↦ continuationSpaceField_circleRotatingContinuationField_of_lt hC ht₀ hr₀ hu)
    (fun u hu ↦ continuationSpaceField_circleRotatingContinuationField_of_gt hC ht₁ hr₁ hu)
    hs₀ hs₁ ha hb θ

/-- **The inverse transition diffeomorphism through the window.** For window times
`s₀ < U(t₀) / C` and `s₁ > U(t₁) / C`, the inverse of the transition diffeomorphism of the rotating
field from a time `a ≤ s₀` to a time `b ≥ s₁` is the flow of the rotation of `X` by `r₁` for the
time `s₁ - b`, then the time-dependent flow back across the window from `s₁` to `s₀`, then the flow
of the rotation of `X` by `r₀` for the time `a - s₀`. -/
theorem continuationTransition_circleRotatingContinuationField_symm_apply
    (θ : AddCircle (2 * π)) :
    (continuationTransition C (contMDiff_circleRotatingContinuationField hX.contMDiff hr C)
        a b).symm θ =
      (hX.circleRotatedField r₀).flow (a - s₀)
        (timeDependentFlowOf (continuationSpaceField C (circleRotatingContinuationField X r C))
          s₁ s₀ ((hX.circleRotatedField r₁).flow (s₁ - b) θ)) := by
  rw [continuationTransition_symm_apply]
  exact timeDependentFlowOf_eq_flow_timeDependentFlowOf_flow_symm (hX.circleRotatedField r₀)
    (hX.circleRotatedField r₁) (contMDiff_continuationSpaceField_circleRotating hX.contMDiff hr)
    (fun u hu ↦ continuationSpaceField_circleRotatingContinuationField_of_lt hC ht₀ hr₀ hu)
    (fun u hu ↦ continuationSpaceField_circleRotatingContinuationField_of_gt hC ht₁ hr₁ hu)
    hs₀ hs₁ ha hb θ

end Adapted

end TauCeti

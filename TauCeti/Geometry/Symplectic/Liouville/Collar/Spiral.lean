/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import TauCeti.Analysis.Complex.Circle.PolarCurve
public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import Mathlib.Order.Monotone.Union
import TauCeti.Geometry.Manifold.Flow.NormedSpace
import TauCeti.Geometry.Symplectic.Liouville.ContactType

/-!
# A spiral with no Liouville collar of uniform width

A hypersurface `Y` transverse to the Liouville field `Z` of a primitive `α`, `ι_Z dα = α`, has a
collar: the local flow map `Φ(t, y) = φₜ(y)` is a diffeomorphism from a neighbourhood
`{(t, y) | |t| < ε y}` of `{0} × Y` onto a neighbourhood of `Y`
(`TauCeti.exists_continuous_pos_injOn_flowOf_comp`). When `Y` is compact the width can be taken
constant (`TauCeti.exists_pos_injOn_flowOf_comp`). This file shows that compactness cannot be
dropped there, even for a closed embedded hypersurface and a complete Liouville field.

In the plane `ℂ` with its radial primitive `λₓ(v) = σ(x, v) / 2` of a linear symplectic form `σ`,
the Liouville field is `Z(u) = u / 2`, whose flow is the dilation `u ↦ e^(t/2) u`. Let
`Y` be the **polar curve** `r = ρ(θ)`, the image of `θ ↦ ρ(θ) e^(iθ)` (`TauCeti.polarCurve`, whose
basic analysis is in `TauCeti.Analysis.Complex.Circle.PolarCurve`).

* If `ρ` never vanishes, every nonzero multiple of the position field is transverse to the curve
  (`TauCeti.isTransverseAlong_smul_polarCurve`), and for smooth `ρ` the curve is an immersion
  (`TauCeti.injective_mfderiv_polarCurve`) on which `λ` restricts to a contact form
  (`TauCeti.isContactForm_mpullback_polarCurve_radialPrimitive`).
* If `ρ` is continuous, strictly increasing and positive, the curve is a topological embedding
  (`TauCeti.isEmbedding_polarCurve`). If moreover `ρ → 0` as `θ → -∞` and `ρ → ∞` as `θ → ∞`,
  its closure only adds the origin (`TauCeti.closure_range_polarCurve`): the curve is a closed
  embedded curve in `ℂ ∖ {0}`.
* If `ρ(θ + 2π) / ρ(θ) → 1` as `θ → ∞`, then on no strip `(-ε, ε) × ℝ` is the flow map
  `(t, θ) ↦ e^(t/2) ρ(θ) e^(iθ)` injective (`TauCeti.not_injOn_flowOf_polarCurve`): the points
  at angles `θ` and `θ + 2π` lie on one ray, and the flow joins them in the time
  `2 log (ρ(θ + 2π) / ρ(θ))`, which tends to `0`.

The radius `TauCeti.spiralRadius` is a smooth, strictly increasing function with
`spiralRadius θ = e^(θ - 2)` for `θ ≤ 2` and `spiralRadius θ = θ` for `θ ≥ 3`. It satisfies all
these hypotheses (`TauCeti.strictMono_spiralRadius`, `TauCeti.tendsto_spiralRadius_atBot`,
`TauCeti.tendsto_spiralRadius_atTop`, `TauCeti.tendsto_spiralRadius_add_two_pi_div`), so its
spiral is a closed embedded curve in `ℂ ∖ {0}`, transverse to the complete Liouville field `u / 2`
and of contact type. By `TauCeti.exists_continuous_pos_injOn_flowOf_comp` it has a Liouville
collar of variable width, but by `TauCeti.not_injOn_flowOf_polarCurve` none of uniform width.

## Main definitions

* `TauCeti.spiralRadius`: a smooth increasing radius, equal to `e^(θ - 2)` for `θ ≤ 2` and to `θ`
  for `θ ≥ 3`.

## Main results

* `TauCeti.isTransverseAlong_smul_polarCurve`: transversality to the position field.
* `TauCeti.isContactForm_mpullback_polarCurve_radialPrimitive`: the radial primitive restricts to a
  contact form on the polar curve.
* `TauCeti.injective_mfderiv_polarCurve`: a polar curve is an immersion.
* `TauCeti.not_injOn_flowOf_polarCurve`: the flow map of `u / 2` out of the polar curve is
  injective on no strip `(-ε, ε) × ℝ`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their collars).
-/

public section

noncomputable section

open Complex Filter Function Set Topology
open scoped Manifold Real ContDiff

namespace TauCeti

/-! ### Polar curves and the Liouville field -/

variable {ρ : ℝ → ℝ}

/-- No multiple `u (ρ' + i ρ) e^(iθ)` of the velocity of a polar curve with `ρ(θ) ≠ 0` is a
nonzero multiple `c ρ(θ) e^(iθ)` of its position: the angular components are `u ρ(θ)` and `0`. -/
private theorem smul_velocity_ne_smul_polarCurve {c θ ρ' : ℝ} (hc : c ≠ 0) (hρ : ρ θ ≠ 0)
    (u : ℝ) : u • ((((ρ' : ℝ) : ℂ) + ((ρ θ : ℝ) : ℂ) * I) * exp ((θ : ℂ) * I)) ≠
      c • polarCurve ρ θ := by
  intro h
  -- Cancelling `e^(iθ)` gives `u (ρ' + i ρ) = c ρ`.
  have h' : ((u : ℂ) * (ρ' + ρ θ * I)) * exp ((θ : ℂ) * I) =
      ((c * ρ θ : ℝ) : ℂ) * exp ((θ : ℂ) * I) := by
    rw [polarCurve_apply, circleMap_zero, real_smul, real_smul] at h
    push_cast
    linear_combination h
  have h2 := mul_right_cancel₀ (exp_ne_zero _) h'
  have him := congrArg Complex.im h2
  have hre := congrArg Complex.re h2
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, add_re, add_im, I_re, I_im] at him hre
  have hu : u = 0 := by simpa [hρ] using him
  subst hu
  simp_all

/-- **The position field is transverse to a polar curve.** If the radius `ρ` never vanishes, then
for every `c ≠ 0` the vector field `u ↦ c u` is transverse along the polar curve `r = ρ(θ)`: the
velocity `(ρ' + i ρ) e^(iθ)` has a nonzero angular component. No differentiability of `ρ` is
needed, since where the curve is not differentiable its differential vanishes. -/
theorem isTransverseAlong_smul_polarCurve {c : ℝ} (hc : c ≠ 0) (hρ : ∀ θ, ρ θ ≠ 0) :
    IsTransverseAlong (I := 𝓘(ℝ, ℂ)) 𝓘(ℝ) (fun x : ℂ ↦ c • x) (polarCurve ρ) := by
  refine isTransverseAlong_iff.2 fun θ ⟨v, hv⟩ ↦ ?_
  rw [mfderiv_eq_fderiv] at hv
  by_cases hd : DifferentiableAt ℝ (polarCurve ρ) θ
  · -- On model spaces the tangent identifications are the identity.
    exact smul_velocity_ne_smul_polarCurve hc (hρ θ) v
      ((fderiv_polarCurve_apply (differentiableAt_polarCurve_iff.1 hd) v).symm.trans
        (hv : fderiv ℝ (polarCurve ρ) θ v = c • polarCurve ρ θ))
  · rw [fderiv_zero_of_not_differentiableAt hd] at hv
    exact smul_ne_zero hc (polarCurve_apply ρ θ ▸ circleMap_ne_center (hρ θ))
      (hv : (0 : ℂ) = c • polarCurve ρ θ).symm

/-- **A polar curve is an immersion** where its radius is differentiable and nonzero. -/
theorem injective_mfderiv_polarCurve {θ : ℝ} (hd : DifferentiableAt ℝ ρ θ) (hρ : ρ θ ≠ 0) :
    Injective (mfderiv 𝓘(ℝ) 𝓘(ℝ, ℂ) (polarCurve ρ) θ) := by
  intro v w h
  rw [mfderiv_eq_fderiv] at h
  -- On model spaces the tangent identifications are the identity.
  have h' := (fderiv_polarCurve_apply hd v).symm.trans
    ((h : fderiv ℝ (polarCurve ρ) θ v = fderiv ℝ (polarCurve ρ) θ w).trans
      (fderiv_polarCurve_apply hd w))
  refine smul_left_injective ℝ (mul_ne_zero (fun h0 ↦ hρ ?_) (exp_ne_zero _)) h'
  simpa using congrArg Complex.im h0

/-- **A polar curve is of contact type.** For a smooth nowhere-vanishing radius `ρ` and a linear
symplectic form `σ` on `ℂ`, the radial primitive `λₓ(v) = σ(x, v) / 2`, whose Liouville field is
`u / 2`, restricts to a contact form on the polar curve `r = ρ(θ)`. -/
theorem isContactForm_mpullback_polarCurve_radialPrimitive (σ : SymplecticForm ℂ)
    (hc : ContDiff ℝ ∞ ρ) (hρ : ∀ θ, ρ θ ≠ 0) :
    (SmoothForm.mpullback (polarCurve ρ) (contDiff_polarCurve hc).contMDiff
      σ.radialPrimitive).IsContactForm := by
  have hrc : IsRestrictedContactType 𝓘(ℝ) σ.constSmooth.val σ.radialPrimitive.val
      (polarCurve ρ) :=
    isRestrictedContactType_iff.2 ⟨σ.mextDeriv_radialPrimitive, fun x ↦ (2⁻¹ : ℝ) • x,
      contMDiff_vectorSpace_iff_contDiff.2 (contDiff_id.const_smul (2⁻¹ : ℝ)),
      σ.constSmooth_interior_two_inv_smul, isTransverseAlong_smul_polarCurve (by norm_num) hρ⟩
  refine hrc.isContactType.isContactForm_mpullback σ.isNondegenerate_constSmooth _
    (fun θ ↦ injective_mfderiv_polarCurve ((hc.differentiable (by simp)) θ) (hρ θ)) ?_
  simp

/-- **The flow out of a polar curve is injective on no strip.** Let the radius satisfy
`ρ(θ + 2π) / ρ(θ) → 1` as `θ → ∞`, as the spiral `ρ(θ) = θ` does. Then for every `ε > 0` the flow
map `(t, θ) ↦ φₜ(ρ(θ) e^(iθ)) = e^(t/2) ρ(θ) e^(iθ)` of the Liouville field `u / 2` is not
injective on `(-ε, ε) × ℝ`: the flow joins the points at the angles `θ` and `θ + 2π` of the
curve in the time `2 log (ρ(θ + 2π) / ρ(θ))`, which is eventually smaller than `ε`. -/
theorem not_injOn_flowOf_polarCurve
    (hρ : Tendsto (fun θ ↦ ρ (θ + 2 * π) / ρ θ) atTop (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ¬ InjOn (fun q : ℝ × ℝ ↦
        flowOf (I := 𝓘(ℝ, ℂ)) (fun x : ℂ ↦ (2⁻¹ : ℝ) • x) q.1 (polarCurve ρ q.2))
      (Ioo (-ε) ε ×ˢ univ) := by
  have hlog : Tendsto (fun θ ↦ 2 * Real.log (ρ (θ + 2 * π) / ρ θ)) atTop (𝓝 0) := by
    simpa using ((Real.continuousAt_log one_ne_zero).tendsto.comp hρ).const_mul 2
  obtain ⟨θ, hθε, hk⟩ := ((hlog.eventually (Ioo_mem_nhds (neg_neg_of_pos hε) hε)).and
    (hρ.eventually (lt_mem_nhds one_pos))).exists
  have hρθ : ρ θ ≠ 0 := fun h ↦ by simp [h] at hk
  intro hinj
  have heq := hinj (x₁ := (2 * Real.log (ρ (θ + 2 * π) / ρ θ), θ)) (mem_prod.2 ⟨hθε, mem_univ _⟩)
    (x₂ := (0, θ + 2 * π)) (mem_prod.2 ⟨⟨neg_neg_of_pos hε, hε⟩, mem_univ _⟩) ?_
  · have := congrArg Prod.snd heq
    simp only at this
    linarith [Real.pi_pos]
  · -- Both points lie on the ray of angle `θ`, and the flow rescales one onto the other.
    have hexp : Real.exp (2⁻¹ * (2 * Real.log (ρ (θ + 2 * π) / ρ θ))) = ρ (θ + 2 * π) / ρ θ := by
      rw [inv_mul_cancel_left₀ two_ne_zero, Real.exp_log hk]
    simp only [flowOf_dilation, hexp, polarCurve_apply,
      periodic_circleMap 0 (ρ (θ + 2 * π)) θ]
    simp [circleMap_zero, ← mul_assoc, div_mul_cancel₀ _ (ofReal_ne_zero.2 hρθ)]

/-! ### The spiral radius -/

/-- A smooth increasing **spiral radius**: `e^(θ - 2)` for `θ ≤ 2`, blending through a smooth
transition into `θ` for `θ ≥ 3`. -/
def spiralRadius (θ : ℝ) : ℝ :=
  Real.exp (θ - 2) + Real.smoothTransition (θ - 2) * (θ - Real.exp (θ - 2))

/-- Below `θ = 2` the spiral radius is `e^(θ - 2)`. -/
theorem spiralRadius_of_le_two {θ : ℝ} (h : θ ≤ 2) : spiralRadius θ = Real.exp (θ - 2) := by
  simp [spiralRadius, Real.smoothTransition.zero_of_nonpos (by linarith : θ - 2 ≤ 0)]

/-- From `θ = 3` on the spiral radius is `θ`, so the spiral is the Archimedean spiral `r = θ`. -/
theorem spiralRadius_of_three_le {θ : ℝ} (h : 3 ≤ θ) : spiralRadius θ = θ := by
  simp [spiralRadius, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ θ - 2)]

/-- The spiral radius is smooth. -/
theorem contDiff_spiralRadius {n : ℕ∞} : ContDiff ℝ n spiralRadius := by
  have he : ContDiff ℝ n fun θ : ℝ ↦ Real.exp (θ - 2) :=
    Real.contDiff_exp.comp (contDiff_id.sub contDiff_const)
  exact he.add ((Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (contDiff_id.sub he))

/-- On `[2, 3]`, where the spiral radius blends `e^(θ - 2)` into `θ`, the first lies below the
second. -/
private theorem exp_sub_two_le_self {θ : ℝ} (h2 : 2 ≤ θ) (h3 : θ ≤ 3) : Real.exp (θ - 2) ≤ θ := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := θ - 2) (by rw [abs_le]; constructor <;> linarith)
  nlinarith [(abs_le.1 h).2]

/-- The spiral radius is strictly increasing. -/
theorem strictMono_spiralRadius : StrictMono spiralRadius := by
  refine StrictMonoOn.Iic_union_Ici (a := 2) (fun a ha b hb hab ↦ ?_) fun a ha b _ hab ↦ ?_
  · rw [spiralRadius_of_le_two ha, spiralRadius_of_le_two hb]
    exact Real.exp_lt_exp.2 (by linarith)
  rcases le_or_gt 3 a with h3 | h3
  · rw [spiralRadius_of_three_le h3, spiralRadius_of_three_le (h3.trans hab.le)]
    exact hab
  -- With `h` the transition and `e = exp (· - 2)`, `ρ = (1 - h) e + h id`, so
  -- `ρ b - ρ a = (1 - h b) (e b - e a) + h b (b - a) + (h b - h a) (a - e a)`.
  set ha' := Real.smoothTransition (a - 2)
  set hb' := Real.smoothTransition (b - 2)
  have hid : spiralRadius b - spiralRadius a = (1 - hb') * (Real.exp (b - 2) - Real.exp (a - 2)) +
      hb' * (b - a) + (hb' - ha') * (a - Real.exp (a - 2)) := by
    simp only [spiralRadius, ha', hb']
    ring
  have hhab : ha' ≤ hb' := Real.smoothTransition.monotone (by linarith)
  have he : Real.exp (a - 2) < Real.exp (b - 2) := Real.exp_lt_exp.2 (by linarith)
  have hea := exp_sub_two_le_self ha h3.le
  have hb0 : 0 ≤ hb' := Real.smoothTransition.nonneg _
  have hb1 : hb' ≤ 1 := Real.smoothTransition.le_one _
  have hpos : 0 < (1 - hb') * (Real.exp (b - 2) - Real.exp (a - 2)) + hb' * (b - a) := by
    rcases hb1.lt_or_eq with h | h
    · nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 he)]
    · rw [h]
      linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hhab) (sub_nonneg.2 hea)]

/-- The spiral radius tends to `0` as `θ → -∞`. -/
theorem tendsto_spiralRadius_atBot : Tendsto spiralRadius atBot (𝓝 0) := by
  have h : Tendsto (fun θ : ℝ ↦ Real.exp (θ - 2)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_right _ (-2) tendsto_id)
  exact h.congr' ((eventually_le_atBot 2).mono fun θ hθ ↦ (spiralRadius_of_le_two hθ).symm)

/-- The spiral radius tends to `∞` as `θ → ∞`. -/
theorem tendsto_spiralRadius_atTop : Tendsto spiralRadius atTop atTop :=
  tendsto_id.congr' ((eventually_ge_atTop 3).mono fun _ hθ ↦ (spiralRadius_of_three_le hθ).symm)

/-- The spiral radius is positive. -/
theorem spiralRadius_pos (θ : ℝ) : 0 < spiralRadius θ :=
  (strictMono_spiralRadius.monotone.le_of_tendsto tendsto_spiralRadius_atBot (θ - 1)).trans_lt
    (strictMono_spiralRadius (by linarith))

/-- Consecutive turns of the spiral have asymptotically equal radii:
`spiralRadius (θ + 2π) / spiralRadius θ → 1`. -/
theorem tendsto_spiralRadius_add_two_pi_div :
    Tendsto (fun θ ↦ spiralRadius (θ + 2 * π) / spiralRadius θ) atTop (𝓝 1) := by
  have h : Tendsto (fun θ : ℝ ↦ 1 + 2 * π / θ) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := 2 * π)).div_atTop (tendsto_id (α := ℝ)))
  refine h.congr' ((eventually_ge_atTop 3).mono fun θ hθ ↦ ?_)
  dsimp only
  rw [spiralRadius_of_three_le hθ, spiralRadius_of_three_le (by linarith [Real.pi_pos])]
  field_simp

end TauCeti

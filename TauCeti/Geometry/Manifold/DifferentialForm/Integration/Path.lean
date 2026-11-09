/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Curve
public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Interval.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Integration of one-forms along curves

The integral of a `1`-form `φ` on a manifold `M` along a curve `γ : ℝ → M` over the oriented
interval `a..b` is the interval integral of `φ` evaluated on the velocity of `γ`,

`∫_γ φ = ∫ t in a..b, φ (γ t) (γ' t)`,

where the velocity `TauCeti.Manifold.curveVelocity I γ t` is the manifold derivative of `γ` on
the unit vector. Equivalently, it is the interval integral of the pullback `γ^* φ`, a `1`-form on
`ℝ`, evaluated on the unit vector (`TauCeti.pathIntegral_eq_integral_mpullback`). For a
real-valued form and `a < b`, it is the canonical oriented integral over `[a, b]` of the pullback
of `φ` along `γ` (`TauCeti.integralTopForm_mpullback_Icc_eq_pathIntegral`).

Line integrals are the basic tool for detecting de Rham cohomology classes in degree one. The
integral of the differential of a `C¹` function is its endpoint difference
(`TauCeti.pathIntegral_mextDeriv_ofFunction`, `TauCeti.pathIntegral_mextDeriv`), so exact forms
integrate to zero around closed curves (`TauCeti.pathIntegral_eq_zero_of_mem_exactForms`). The
integral is invariant under `C¹` reparametrization (`TauCeti.pathIntegral_comp`), changes sign
when the curve is reversed (`TauCeti.pathIntegral_comp_sub_left`), is additive under
concatenation of curves (`TauCeti.pathIntegral_curveConcat`), is natural under pullback
(`TauCeti.pathIntegral_mpullback`), and only depends on the values of the form along the curve
(`TauCeti.pathIntegral_congr`) and on the curve away from the endpoints
(`TauCeti.pathIntegral_congr_of_eqOn_uIoo`).

## Main declarations

* `TauCeti.pathIntegral φ γ a b`: the integral of the `1`-form `φ` along `γ` from `a` to `b`.
* `TauCeti.IsSmoothForm.continuous_apply_curveVelocity`: the integrand of a continuous form
  along a `C¹` curve is continuous.
* `TauCeti.pathIntegral_mextDeriv_ofFunction` and `TauCeti.pathIntegral_mextDeriv`: the
  fundamental theorem of calculus for line integrals.
* `TauCeti.pathIntegral_eq_zero_of_mem_exactForms`: exact `1`-forms integrate to zero around
  closed `C¹` curves.
* `TauCeti.pathIntegral_comp`: invariance under `C¹` reparametrization.
* `TauCeti.pathIntegral_curveConcat`: additivity under concatenation of curves.
* `TauCeti.exists_contMDiff_loop_pathIntegral_eq_sub`: two smooth curves with common endpoints
  form a smooth loop whose line integral is the difference of theirs.
* `TauCeti.pathIntegral_mpullback`: naturality under pullback.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11, section
  *Line Integrals*.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The integral of a `1`-form `φ` along a curve `γ : ℝ → M` over the oriented interval `a..b`:
the interval integral of `φ` evaluated on the velocity of `γ`. -/
def pathIntegral (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) : F :=
  ∫ t in a..b, φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t

/-- The line integral is the interval integral of the form on the velocity of the curve. -/
theorem pathIntegral_def (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) :
    pathIntegral φ γ a b = ∫ t in a..b, φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t :=
  (rfl)

/-- The line integral is the interval integral of the pullback of the form to the parameter
line, evaluated on the unit vector. -/
theorem pathIntegral_eq_integral_mpullback (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) :
    pathIntegral φ γ a b = ∫ t in a..b, mpullback 𝓘(ℝ, ℝ) I γ φ t fun _ ↦ 1 := by
  rw [pathIntegral_def]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [Manifold.curveVelocity_apply]
  -- the unit tangent vector of the parameter line is the real number `1`
  exact (mpullback_apply γ φ t _).symm

/-- Line integrals only depend on the values of the form along the curve. -/
theorem pathIntegral_congr {φ ψ : RoughForm I M F 1} {γ : ℝ → M} {a b : ℝ}
    (h : ∀ t ∈ uIcc a b, φ (γ t) = ψ (γ t)) : pathIntegral φ γ a b = pathIntegral ψ γ a b := by
  simp only [pathIntegral_def]
  exact intervalIntegral.integral_congr fun t ht ↦ by simp only [h t ht]

/-- Line integrals along two curves agree when the curves agree on the open interval between the
endpoints: the velocities then agree there, and the endpoints are a null set. -/
theorem pathIntegral_congr_of_eqOn_uIoo {φ : RoughForm I M F 1} {γ γ' : ℝ → M} {a b : ℝ}
    (h : EqOn γ γ' (uIoo a b)) : pathIntegral φ γ a b = pathIntegral φ γ' a b := by
  simp only [pathIntegral_def]
  refine intervalIntegral.integral_congr_uIoo fun t ht ↦ ?_
  have hev : γ =ᶠ[𝓝 t] γ' := h.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
  simp only [Manifold.curveVelocity_apply, hev.mfderiv_eq]
  -- `tangentSpaceCast` identifies two tangent spaces at the same point, both of which are `E`.
  have key (p q : M) (hpq : p = q) (v : TangentSpace I q) :
      φ p (fun _ ↦ tangentSpaceCast I q p v) = φ q fun _ ↦ v := by
    subst hpq; rfl
  exact key _ _ hev.eq_of_nhds _

/-! ### The interval of integration -/

/-- The line integral over a degenerate interval vanishes. -/
@[simp]
theorem pathIntegral_same (φ : RoughForm I M F 1) (γ : ℝ → M) (a : ℝ) :
    pathIntegral φ γ a a = 0 :=
  intervalIntegral.integral_same

/-- Reversing the interval of integration changes the sign of the line integral. -/
theorem pathIntegral_symm (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) :
    pathIntegral φ γ b a = -pathIntegral φ γ a b :=
  intervalIntegral.integral_symm a b

/-- Line integrals over adjacent intervals add up, as soon as the form evaluated on the velocity
is interval integrable on both intervals. For a continuous form along a `C¹` curve this is
`TauCeti.IsSmoothForm.intervalIntegrable_apply_curveVelocity`. -/
theorem pathIntegral_add_adjacent {φ : RoughForm I M F 1} {γ : ℝ → M} {a b c : ℝ}
    (hab : IntervalIntegrable (fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b)
    (hbc : IntervalIntegrable (fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume b c) :
    pathIntegral φ γ a b + pathIntegral φ γ b c = pathIntegral φ γ a c :=
  intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The line integral along a constant curve vanishes. -/
@[simp]
theorem pathIntegral_const_curve (φ : RoughForm I M F 1) (x : M) (a b : ℝ) :
    pathIntegral φ (fun _ ↦ x) a b = 0 := by
  simp only [pathIntegral_def, Manifold.curveVelocity_const]
  exact (intervalIntegral.integral_congr fun _ _ ↦ (φ x).map_zero).trans
    intervalIntegral.integral_zero

/-! ### Linearity in the form -/

/-- The line integral of the zero form vanishes. -/
@[simp]
theorem pathIntegral_zero (γ : ℝ → M) (a b : ℝ) :
    pathIntegral (0 : RoughForm I M F 1) γ a b = 0 := by
  simp [pathIntegral_def]

/-- The line integral commutes with negation of the form. -/
@[simp]
theorem pathIntegral_neg (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) :
    pathIntegral (-φ) γ a b = -pathIntegral φ γ a b := by
  simp [pathIntegral_def, intervalIntegral.integral_neg]

/-- The line integral commutes with scalar multiplication of the form. -/
@[simp]
theorem pathIntegral_smul (c : ℝ) (φ : RoughForm I M F 1) (γ : ℝ → M) (a b : ℝ) :
    pathIntegral (c • φ) γ a b = c • pathIntegral φ γ a b := by
  simp [pathIntegral_def, intervalIntegral.integral_smul]

/-- The line integral of a sum of forms is the sum of the line integrals, as soon as both forms
evaluated on the velocity are interval integrable. For continuous forms along a `C¹` curve this
is `TauCeti.IsSmoothForm.intervalIntegrable_apply_curveVelocity`. -/
theorem pathIntegral_add {φ ψ : RoughForm I M F 1} {γ : ℝ → M} {a b : ℝ}
    (hφ : IntervalIntegrable (fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b)
    (hψ : IntervalIntegrable (fun t ↦ ψ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b) :
    pathIntegral (φ + ψ) γ a b = pathIntegral φ γ a b + pathIntegral ψ γ a b := by
  simp only [pathIntegral_def, Pi.add_apply, ContinuousAlternatingMap.add_apply]
  exact intervalIntegral.integral_add hφ hψ

/-- The line integral of a difference of forms is the difference of the line integrals, as soon
as both forms evaluated on the velocity are interval integrable. For continuous forms along a
`C¹` curve this is `TauCeti.IsSmoothForm.intervalIntegrable_apply_curveVelocity`. -/
theorem pathIntegral_sub {φ ψ : RoughForm I M F 1} {γ : ℝ → M} {a b : ℝ}
    (hφ : IntervalIntegrable (fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b)
    (hψ : IntervalIntegrable (fun t ↦ ψ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b) :
    pathIntegral (φ - ψ) γ a b = pathIntegral φ γ a b - pathIntegral ψ γ a b := by
  simp only [pathIntegral_def, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
  exact intervalIntegral.integral_sub hφ hψ

section Continuous

variable [IsManifold I 1 M]

/-- Along a `C¹` curve, a continuous `1`-form evaluated on the velocity is a continuous function
of the parameter. -/
theorem IsSmoothForm.continuous_apply_curveVelocity {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t := by
  have h := isSmoothForm_modelSpace_iff.mp (hφ.mpullback (by simpa using hγ))
  refine ((ContinuousAlternatingMap.apply ℝ ℝ F fun _ ↦ (1 : ℝ)).continuous.comp
    h.continuous).congr fun t ↦ ?_
  rw [Manifold.curveVelocity_apply]
  -- the unit tangent vector of the parameter line is the real number `1`
  exact mpullback_apply γ φ t _

/-- A continuous `1`-form is interval integrable along a `C¹` curve. -/
theorem IsSmoothForm.intervalIntegrable_apply_curveVelocity {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t) volume a b :=
  (hφ.continuous_apply_curveVelocity hγ).intervalIntegrable a b

/-- **Reparametrization invariance.** The line integral of a continuous form along `γ ∘ σ`, for
a `C¹` change of parameter `σ`, is the line integral along `γ` between the image endpoints. The
change of parameter need not be monotone. -/
theorem pathIntegral_comp {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {σ σ' : ℝ → ℝ} {a b : ℝ}
    (hσ : ∀ t ∈ uIcc a b, HasDerivAt σ (σ' t) t) (hσ' : ContinuousOn σ' (uIcc a b)) :
    pathIntegral φ (γ ∘ σ) a b = pathIntegral φ γ (σ a) (σ b) := by
  rw [pathIntegral_def, pathIntegral_def,
    ← intervalIntegral.integral_deriv_smul_comp hσ hσ' (hφ.continuous_apply_curveVelocity hγ)]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [Function.comp_apply, Manifold.curveVelocity_comp (hσ t ht)
    ((hγ (σ t)).mdifferentiableAt one_ne_zero)]
  simpa using (φ (γ (σ t))).map_smul_univ (fun _ ↦ σ' t) fun _ ↦ Manifold.curveVelocity I γ (σ t)

/-- The line integral along an affine reparametrization `t ↦ γ (c * t + d)` is the line integral
along `γ` between the image endpoints. -/
theorem pathIntegral_comp_mul_add {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (c d a b : ℝ) :
    pathIntegral φ (fun t ↦ γ (c * t + d)) a b = pathIntegral φ γ (c * a + d) (c * b + d) :=
  pathIntegral_comp hφ hγ (σ := fun t ↦ c * t + d) (σ' := fun _ ↦ c)
    (fun t _ ↦ by simpa using ((hasDerivAt_id t).const_mul c).add_const d) continuousOn_const

/-- The line integral along the reversed curve `t ↦ γ (d - t)` is the negative of the line integral
along `γ` between the image endpoints. -/
theorem pathIntegral_comp_sub_left {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (d a b : ℝ) :
    pathIntegral φ (fun t ↦ γ (d - t)) a b = -pathIntegral φ γ (d - b) (d - a) := by
  have h := pathIntegral_comp_mul_add hφ hγ (-1) d a b
  simp only [neg_one_mul, neg_add_eq_sub] at h
  rw [h, pathIntegral_symm]

/-- The line integral along a concatenation of two `C¹` curves, constant near the junction point,
is the sum of the line integrals. -/
theorem pathIntegral_curveConcat {φ : RoughForm I M F 1} (hφ : IsSmoothForm I 0 φ)
    {γ₁ γ₂ : ℝ → M} {y : M} (hγ₁ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ₁)
    (hγ₂ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ₂) (h₁ : ∀ t, 1 ≤ t → γ₁ t = y) (h₂ : ∀ t ≤ 0, γ₂ t = y) :
    pathIntegral φ (curveConcat γ₁ γ₂) 0 1 = pathIntegral φ γ₁ 0 1 + pathIntegral φ γ₂ 0 1 := by
  have hi := hφ.intervalIntegrable_apply_curveVelocity
    (ContMDiff.curveConcat (n := 1) hγ₁ hγ₂ h₁ h₂)
  rw [← pathIntegral_add_adjacent (hi 0 (1 / 3)) (hi (1 / 3) 1),
    ← pathIntegral_add_adjacent (hi (1 / 3) (2 / 3)) (hi (2 / 3) 1)]
  -- The concatenation runs through `γ₁` on `[0, 1/3]`, rests on `[1/3, 2/3]`, and runs through
  -- `γ₂` on `[2/3, 1]`.
  have hl : pathIntegral φ (curveConcat γ₁ γ₂) 0 (1 / 3) = pathIntegral φ γ₁ 0 1 := by
    rw [pathIntegral_congr_of_eqOn_uIoo (γ' := fun t ↦ γ₁ (3 * t + 0)) fun t ht ↦ by
        rw [uIoo_of_le (by norm_num)] at ht
        simpa using eqOn_curveConcat_left h₁ h₂ (lt_trans ht.2 (by norm_num)),
      pathIntegral_comp_mul_add hφ hγ₁]
    norm_num
  have hm : pathIntegral φ (curveConcat γ₁ γ₂) (1 / 3) (2 / 3) = 0 := by
    rw [pathIntegral_congr_of_eqOn_uIoo (γ' := fun _ ↦ y) fun t ht ↦
        curveConcat_eq_of_mem_Icc h₁ h₂ (by
          rw [uIoo_of_le (by norm_num)] at ht; exact Ioo_subset_Icc_self ht),
      pathIntegral_const_curve]
  have hr : pathIntegral φ (curveConcat γ₁ γ₂) (2 / 3) 1 = pathIntegral φ γ₂ 0 1 := by
    rw [pathIntegral_congr_of_eqOn_uIoo (γ' := fun t ↦ γ₂ (3 * t + -2)) fun t ht ↦ by
        rw [uIoo_of_le (by norm_num)] at ht
        simpa [sub_eq_add_neg] using eqOn_curveConcat_right h₁ h₂ (lt_trans (by norm_num) ht.1),
      pathIntegral_comp_mul_add hφ hγ₂]
    norm_num
  rw [hl, hm, hr, zero_add]

/-- Two smooth curves from `x₀` to `y`, constant on `(-∞, 0]` and on `[1, ∞)`, form a smooth loop
at `x₀`, the first followed by the reversed second. The line integral of a continuous form along
this loop is the difference of the line integrals along the two curves. -/
theorem exists_contMDiff_loop_pathIntegral_eq_sub {φ : RoughForm I M F 1}
    (hφ : IsSmoothForm I 0 φ) {x₀ y : M} {γ γ' : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hγ₀ : ∀ t ≤ 0, γ t = x₀) (hγ₁ : ∀ t, 1 ≤ t → γ t = y) (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (hγ'₀ : ∀ t ≤ 0, γ' t = x₀) (hγ'₁ : ∀ t, 1 ≤ t → γ' t = y) :
    ∃ ℓ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I ∞ ℓ ∧ ℓ 0 = x₀ ∧ ℓ 1 = x₀ ∧
      pathIntegral φ ℓ 0 1 = pathIntegral φ γ 0 1 - pathIntegral φ γ' 0 1 := by
  have hrev : ContMDiff 𝓘(ℝ, ℝ) I ∞ fun t ↦ γ' (1 - t) :=
    hγ'.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ ↦ 1 - t).contMDiff
  have h₂ : ∀ t ≤ 0, γ' (1 - t) = y := fun t ht ↦ hγ'₁ _ (by linarith)
  refine ⟨_, hγ.curveConcat hrev hγ₁ h₂,
    by rw [curveConcat_of_le (by norm_num), hγ₀ _ (by norm_num)],
    by rw [curveConcat_of_lt (by norm_num)]; exact hγ'₀ _ (by norm_num), ?_⟩
  rw [pathIntegral_curveConcat hφ (hγ.of_le (by simp)) (hrev.of_le (by simp)) hγ₁ h₂,
    pathIntegral_comp_sub_left hφ (hγ'.of_le (by simp)), sub_self, sub_zero, sub_eq_add_neg]

end Continuous

/-! ### Naturality -/

section Pullback

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Naturality of line integrals.** The line integral of the pullback `f^* φ` along `γ` is the
line integral of `φ` along `f ∘ γ`, as soon as `f` and `γ` are differentiable along the interval
of integration. -/
theorem pathIntegral_mpullback {f : M → M'} (φ : RoughForm I' M' F 1) {γ : ℝ → M} {a b : ℝ}
    (hf : ∀ t ∈ uIcc a b, MDifferentiableAt I I' f (γ t))
    (hγ : ∀ t ∈ uIcc a b, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    pathIntegral (mpullback I I' f φ) γ a b = pathIntegral φ (f ∘ γ) a b := by
  simp only [pathIntegral_def, mpullback_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have hv : Manifold.curveVelocity I' (f ∘ γ) t =
      mfderiv I I' f (γ t) (Manifold.curveVelocity I γ t) := by
    simpa only [Manifold.curveVelocityWithin_univ] using
      Manifold.curveVelocityWithin_map (s := univ) (hf t ht) uniqueDiffWithinAt_univ
        (hγ t ht).mdifferentiableWithinAt
  simp only [Function.comp_apply, hv]

/-- The line integral of a one-form along the curve `t ↦ u (x, t)` is the integral of the pullback
of the form along `u` on the second coordinate vector. -/
theorem pathIntegral_apply_snd {α : RoughForm I M F 1} {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (x a b : ℝ) :
    pathIntegral α (fun t ↦ u (x, t)) a b =
      ∫ t in a..b, mpullback 𝓘(ℝ, ℝ × ℝ) I u α (x, t) fun _ ↦ (0, 1) := by
  rw [pathIntegral_eq_integral_mpullback]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hL : HasFDerivAt (fun t : ℝ ↦ (x, t)) ((0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ))
      t := (hasFDerivAt_const x t).prodMk (hasFDerivAt_id t)
  have := mpullback_comp_apply_of_hasFDerivAt hL ((hu _).mdifferentiableAt one_ne_zero) α
  simp only [Function.comp_def] at this
  rw [this]
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans ?_
  congr 1

/-- The line integral of a one-form along the curve `s ↦ u (s, y)` is the integral of the pullback
of the form along `u` on the first coordinate vector. -/
theorem pathIntegral_apply_fst {α : RoughForm I M F 1} {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) (y a b : ℝ) :
    pathIntegral α (fun s ↦ u (s, y)) a b =
      ∫ s in a..b, mpullback 𝓘(ℝ, ℝ × ℝ) I u α (s, y) fun _ ↦ (1, 0) := by
  rw [pathIntegral_eq_integral_mpullback]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  have hL : HasFDerivAt (fun s : ℝ ↦ (s, y)) ((ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ))
      s := (hasFDerivAt_id s).prodMk (hasFDerivAt_const y s)
  have := mpullback_comp_apply_of_hasFDerivAt hL ((hu _).mdifferentiableAt one_ne_zero) α
  simp only [Function.comp_def] at this
  rw [this]
  refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans ?_
  congr 1

end Pullback

/-! ### The fundamental theorem of calculus -/

section FTC

variable [CompleteSpace F]

/-- **The fundamental theorem of calculus for line integrals.** The line integral of the
differential of a `C¹` function along a `C¹` curve is the difference of the values of the
function at the endpoints. -/
theorem pathIntegral_mextDeriv_ofFunction {f : M → F} (hf : ContMDiff I 𝓘(ℝ, F) 1 f)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathIntegral (mextDeriv (RoughForm.ofFunction I f)) γ a b = f (γ b) - f (γ a) := by
  have hfγ : ContDiff ℝ 1 (f ∘ γ) := contMDiff_iff_contDiff.mp (hf.comp hγ)
  have hd (t : ℝ) : HasDerivAt (f ∘ γ) (mextDeriv (RoughForm.ofFunction I f) (γ t)
      fun _ ↦ Manifold.curveVelocity I γ t) t := by
    rw [mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply]
    exact Manifold.hasDerivAt_comp_curve ((hf (γ t)).mdifferentiableAt one_ne_zero)
      (Manifold.hasMFDerivAt_curveVelocity ((hγ t).mdifferentiableAt one_ne_zero))
  have hderiv : deriv (f ∘ γ) = fun t ↦ mextDeriv (RoughForm.ofFunction I f) (γ t)
      fun _ ↦ Manifold.curveVelocity I γ t := funext fun t ↦ (hd t).deriv
  rw [pathIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) ?_
  rw [← hderiv]
  exact hfγ.continuous_deriv_one.intervalIntegrable a b

/-- **The fundamental theorem of calculus for line integrals**, for a `C¹` form `ψ` of degree
zero: the line integral of `dψ` along a `C¹` curve is the difference of the values of `ψ` at the
endpoints. -/
theorem pathIntegral_mextDeriv [IsManifold I 1 M] {ψ : RoughForm I M F 0}
    (hψ : IsSmoothForm I 1 ψ) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathIntegral (mextDeriv ψ) γ a b = ψ (γ b) 0 - ψ (γ a) 0 := by
  rw [RoughForm.eq_ofFunction ψ, isSmoothForm_ofFunction_iff] at hψ
  have h := pathIntegral_mextDeriv_ofFunction hψ hγ a b
  rwa [← RoughForm.eq_ofFunction] at h

/-- **The fundamental theorem of calculus along a map with an exact pullback.** If a
differentiable map `i : N → M` pulls the one-form `φ` back to the differential of a `C¹` function
`f` on `N`, then the line integral of `φ` along `i ∘ c`, for a `C¹` curve `c` in `N`, is the
difference of the values of `f` at the endpoints of `c`. For instance, `i` may be an exact
Lagrangian map and `f` its primitive. -/
theorem pathIntegral_comp_eq_sub_of_mpullback_eq {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {φ : RoughForm I M F 1} {i : N → M} {f : N → F}
    (hi : MDifferentiable J I i) (hf : ContMDiff J 𝓘(ℝ, F) 1 f)
    (hφ : mpullback J I i φ = mextDeriv (RoughForm.ofFunction J f)) {c : ℝ → N}
    (hc : ContMDiff 𝓘(ℝ, ℝ) J 1 c) (a b : ℝ) :
    pathIntegral φ (i ∘ c) a b = f (c b) - f (c a) := by
  rw [← pathIntegral_mpullback φ (fun t _ ↦ hi (c t))
    (fun t _ ↦ (hc t).mdifferentiableAt one_ne_zero), hφ, pathIntegral_mextDeriv_ofFunction hf hc]

end FTC

/-- Exact smooth `1`-forms integrate to zero around closed `C¹` curves. -/
theorem pathIntegral_eq_zero_of_mem_exactForms [IsManifold I 2 M] {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ exactForms I M 1) {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) {a b : ℝ}
    (hab : γ a = γ b) : pathIntegral (φ : RoughForm I M ℝ 1) γ a b = 0 := by
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨g, rfl⟩ := hφ
  have hg : IsSmoothForm I 1 g.1 :=
    g.isSmoothForm.of_le (by exact_mod_cast le_top)
  rw [mextDerivₗ_apply, pathIntegral_mextDeriv hg hγ, hab, sub_self]

/-! ### Comparison with oriented interval integration -/

/-- For `a < b`, the line integral of a continuous real `1`-form along a `C¹` curve is the
canonical oriented integral over `[a, b]` of the pullback of the form along the curve. -/
theorem integralTopForm_mpullback_Icc_eq_pathIntegral [IsManifold I 1 M] {a b : ℝ}
    [Fact (a < b)] {φ : RoughForm I M ℝ 1} (hφ : IsSmoothForm I 0 φ) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    integralTopForm (Manifold.Orientation.interval a b)
      (mpullback (𝓡∂ 1) I (fun t : Icc a b ↦ γ t) φ) = pathIntegral φ γ a b := by
  have hc : mpullback (𝓡∂ 1) I (fun t : Icc a b ↦ γ t) φ =
      mpullback (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Icc a b → ℝ) (mpullback 𝓘(ℝ, ℝ) I γ φ) :=
    mpullback_comp ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).mdifferentiable
      one_ne_zero) (hγ.mdifferentiable one_ne_zero) φ
  have he : (fun t ↦ mpullback 𝓘(ℝ, ℝ) I γ φ t fun _ ↦ 1) =
      fun t ↦ φ (γ t) fun _ ↦ Manifold.curveVelocity I γ t := funext fun t ↦ by
    rw [Manifold.curveVelocity_apply]
    -- the unit tangent vector of the parameter line is the real number `1`
    exact mpullback_apply γ φ t _
  have hi : IntervalIntegrable (fun t ↦ mpullback 𝓘(ℝ, ℝ) I γ φ t fun _ ↦ 1) volume a b := by
    rw [he]
    exact hφ.intervalIntegrable_apply_curveVelocity hγ a b
  rw [hc, (integralTopForm_mpullback_subtypeVal_Icc _ hi).2,
    pathIntegral_eq_integral_mpullback]

end TauCeti

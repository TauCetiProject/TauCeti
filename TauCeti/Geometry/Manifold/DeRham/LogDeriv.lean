/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.DeRham.Period
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.Topology

/-!
# Logarithmic derivatives of circle-valued maps

For a differentiable map `u : M → S¹` to the unit circle `S¹ ⊆ ℂ`, the pullback
`θ_u = u^* dθ` of the angular form `dθ` (`TauCeti.circleAngularForm`) is a real `1`-form, and
the logarithmic derivative of `u` is the imaginary `1`-form

`u⁻¹ du = i θ_u`,

that is `du = u · i θ_u` (`TauCeti.mvfderiv_coe_apply_eq_mul_mpullback_circleAngularForm`).
Pointwise `θ_u(v) = Im (conj (u x) du(v))`
(`TauCeti.mpullback_circleAngularForm_apply`); the real part of `conj (u x) du(v)` vanishes
because `|u|² = 1`. The form `θ_u` is the logarithmic derivative written as a real form, and
`u ↦ θ_u` turns products into sums and inverses into negatives. On a connected manifold its
kernel consists of the constant maps, so a map to the circle is determined by `θ_u` and its value
at one point.

The values of a circle-valued map are recovered from `θ_u` by integration: along a homotopy class
`γ` of paths from `x` to `y`, `u x · exp (i ∫_γ θ_u) = u y`. Hence every period of `θ_u` lies in
`2πℤ`, that is, `u⁻¹ du` has periods in `2πiℤ`. Conversely, a closed `C^r` real `1`-form `φ`
(`1 ≤ r`) on a connected manifold whose periods lie in `2πℤ` is `θ_u` for a `C^r` map
`u : M → S¹` with `u x₀ = 1`: one puts `u y = exp (i ∫_γ φ)` along any path `γ` from `x₀` to `y`.
These maps are the gauge transformations of a complex line bundle with a Hermitian metric, and
`θ_u` measures how a gauge transformation moves a unitary connection; the integrality of its
periods is what makes the components of the gauge group discrete.

## Main results

* `TauCeti.mpullback_circleAngularForm_apply`: `θ_u(v) = Im (conj (u x) du(v))`.
* `TauCeti.mvfderiv_coe_apply_eq_mul_mpullback_circleAngularForm`: `du = u · i θ_u`.
* `TauCeti.mpullback_const_circleAngularForm`, `TauCeti.mpullback_mul_circleAngularForm`,
  `TauCeti.mpullback_inv_circleAngularForm`: `θ` vanishes on constants and turns products into
  sums and inverses into negatives.
* `TauCeti.mpullback_circleAngularForm_eq_zero_iff`: on a connected manifold, `θ_u = 0` exactly
  when `u` is constant, and `TauCeti.eq_of_mpullback_circleAngularForm_eq`: `u` is determined by
  `θ_u` and one value.
* `TauCeti.mpullback_circleExp_circleAngularForm`: `dθ` pulls back to `dt` along `t ↦ exp (t i)`.
* `TauCeti.mextDeriv_mpullback_circleAngularForm`: `θ_u` is closed.
* `TauCeti.mul_circleExp_pathClassIntegral_mpullback_circleAngularForm`:
  `u x · exp (i ∫_γ θ_u) = u y` for a path class `γ` from `x` to `y`.
* `TauCeti.periodHom_mpullback_circleAngularForm_mem_zmultiples`: the periods of `θ_u` lie in
  `2πℤ`.
* `TauCeti.exists_contMDiff_mpullback_circleAngularForm_eq`: a closed `C^r` form with periods in
  `2πℤ` on a connected manifold is `θ_u` for a `C^r` map `u` to the circle with `u x₀ = 1`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 11 (line integrals, closed and
  exact covector fields) and Chapter 17.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996 (the gauge group of a
  `Spinᶜ` structure).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff ComplexConjugate Real Topology

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The logarithmic derivative -/

/-- The coordinate of a circle-valued map is differentiable where the map is. -/
private theorem mdifferentiableAt_coe {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) :
    MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) x :=
  ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero).comp x hu

/-- Products of differentiable circle-valued maps are differentiable. -/
private theorem mdifferentiableAt_mul {u v : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) (hv : MDifferentiableAt I (𝓡 1) v x) :
    MDifferentiableAt I (𝓡 1) (u * v) x :=
  ((contMDiff_mul (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x (hu.prodMk hv)

/-- Inverses of differentiable circle-valued maps are differentiable. -/
private theorem mdifferentiableAt_inv {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) : MDifferentiableAt I (𝓡 1) u⁻¹ x :=
  ((contMDiff_inv (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x hu

/-- **The logarithmic derivative of a circle-valued map.** The pullback `θ_u = u^* dθ` of the
angular form along `u : M → S¹` is `θ_u(v) = Im (conj (u x) du(v))`. -/
theorem mpullback_circleAngularForm_apply {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) (v : Fin 1 → TangentSpace I x) :
    mpullback I (𝓡 1) u circleAngularForm x v =
      (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x (v 0)).im := by
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) (u x) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  rw [mpullback_apply, circleAngularForm_def, mpullback_apply,
    ← Function.comp_def (fun z : Circle ↦ (z : ℂ)) u, mvfderiv_comp_apply x hcoe hu]
  refine (planeAngularForm_apply _ _).trans ?_
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  rw [mvfderiv_apply_eq_mfderiv_apply]
  ring

/-- The derivative of a circle-valued map is tangent to the circle: `Re (conj (u x) du(v)) = 0`,
since `|u|² = 1`. -/
theorem re_conj_mul_mvfderiv_coe_eq_zero {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) (w : TangentSpace I x) :
    (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x w).re = 0 := by
  have hsq : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun z : ℂ ↦ ‖z‖ ^ 2) (u x : ℂ) :=
    (hasStrictFDerivAt_norm_sq (u x : ℂ)).differentiableAt.mdifferentiableAt
  -- differentiate `‖u‖² = 1`
  have h := mvfderiv_comp_apply x hsq (mdifferentiableAt_coe hu) w
  have hone : ((fun z : ℂ ↦ ‖z‖ ^ 2) ∘ fun y ↦ (u y : ℂ)) = fun _ ↦ (1 : ℝ) := by
    funext y
    simp
  rw [hone, mvfderiv_const, mvfderiv_eq_fderiv,
    (hasStrictFDerivAt_norm_sq (u x : ℂ)).hasFDerivAt.fderiv] at h
  simp [mvfderiv, Complex.inner] at h ⊢
  linarith

/-- **The logarithmic derivative is imaginary**: `du = u · i θ_u`, that is
`u⁻¹ du = i θ_u` with `θ_u = u^* dθ`. -/
theorem mvfderiv_coe_apply_eq_mul_mpullback_circleAngularForm {u : M → Circle} {x : M}
    (hu : MDifferentiableAt I (𝓡 1) u x) (w : TangentSpace I x) :
    mvfderiv I (fun y ↦ (u y : ℂ)) x w =
      u x * (mpullback I (𝓡 1) u circleAngularForm x (fun _ ↦ w) * Complex.I) := by
  rw [mpullback_circleAngularForm_apply hu]
  have hre := re_conj_mul_mvfderiv_coe_eq_zero hu w
  set D := mvfderiv I (fun y ↦ (u y : ℂ)) x w
  have hD : D = u x * (conj (u x : ℂ) * D) := by
    rw [← mul_assoc, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one, one_mul]
  conv_lhs => rw [hD]
  congr 1
  apply Complex.ext
  · simpa using hre
  · simp

/-- The logarithmic derivative of a constant map vanishes. -/
@[simp]
theorem mpullback_const_circleAngularForm (c : Circle) :
    mpullback I (𝓡 1) (fun _ : M ↦ c) circleAngularForm = 0 := by
  funext x
  ext v
  rw [mpullback_circleAngularForm_apply mdifferentiableAt_const, mvfderiv_const]
  simp

/-- **The logarithmic derivative of a product** is the sum of the logarithmic derivatives:
`θ_{uv} = θ_u + θ_v`. -/
theorem mpullback_mul_circleAngularForm {u v : M → Circle} (hu : MDifferentiable I (𝓡 1) u)
    (hv : MDifferentiable I (𝓡 1) v) :
    mpullback I (𝓡 1) (u * v) circleAngularForm =
      mpullback I (𝓡 1) u circleAngularForm + mpullback I (𝓡 1) v circleAngularForm := by
  funext x
  refine ContinuousAlternatingMap.ext fun w ↦ ?_
  -- the product rule `d(uv) = u dv + v du` for the coordinates in `ℂ`
  have hD : mvfderiv I (fun y ↦ ((u * v) y : ℂ)) x (w 0) =
      u x * mvfderiv I (fun y ↦ (v y : ℂ)) x (w 0) +
        v x * mvfderiv I (fun y ↦ (u y : ℂ)) x (w 0) := by
    have hprod : (fun y ↦ ((u * v) y : ℂ)) = (fun y ↦ (u y : ℂ)) * fun y ↦ (v y : ℂ) := by
      funext y
      simp
    rw [hprod, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply,
      mvfderiv_apply_eq_mfderiv_apply, (((mdifferentiableAt_coe (hu x)).hasMFDerivAt).mul
        (mdifferentiableAt_coe (hv x)).hasMFDerivAt).mfderiv]
    -- the tangent spaces of `ℂ` are `ℂ`, where the scalar action is multiplication
    rfl
  have hu₁ : conj (u x : ℂ) * u x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
  have hv₁ : conj (v x : ℂ) * v x = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, Complex.ofReal_one]
  rw [Pi.add_apply, ContinuousAlternatingMap.add_apply,
    mpullback_circleAngularForm_apply (mdifferentiableAt_mul (hu x) (hv x)),
    mpullback_circleAngularForm_apply (hu x), mpullback_circleAngularForm_apply (hv x), hD,
    ← Complex.add_im, Pi.mul_apply, Circle.coe_mul, map_mul]
  congr 1
  linear_combination (conj (v x : ℂ) * mvfderiv I (fun y ↦ (v y : ℂ)) x (w 0)) * hu₁ +
    (conj (u x : ℂ) * mvfderiv I (fun y ↦ (u y : ℂ)) x (w 0)) * hv₁

/-- The logarithmic derivative of the pointwise inverse is the negative: `θ_{u⁻¹} = -θ_u`. -/
theorem mpullback_inv_circleAngularForm {u : M → Circle} (hu : MDifferentiable I (𝓡 1) u) :
    mpullback I (𝓡 1) u⁻¹ circleAngularForm = -mpullback I (𝓡 1) u circleAngularForm := by
  have h := mpullback_mul_circleAngularForm hu fun x ↦ mdifferentiableAt_inv (hu x)
  have h₁ : mpullback I (𝓡 1) (1 : M → Circle) circleAngularForm = 0 :=
    mpullback_const_circleAngularForm 1
  rw [mul_inv_cancel, h₁] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- **Constants are the kernel of the logarithmic derivative.** On a connected manifold, a
differentiable map to the circle has `θ_u = 0` exactly when it is constant. -/
theorem mpullback_circleAngularForm_eq_zero_iff [IsManifold I 1 M] [PreconnectedSpace M]
    {u : M → Circle} (hu : MDifferentiable I (𝓡 1) u) :
    mpullback I (𝓡 1) u circleAngularForm = 0 ↔ ∃ c : Circle, u = fun _ ↦ c := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc⟩ ↦ hc ▸ mpullback_const_circleAngularForm c⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨1, funext fun x ↦ hM.elim x⟩
  -- the coordinate of `u` in `ℂ` has zero derivative, `du = u · i θ_u = 0`
  have hzero (x : M) : mfderiv I 𝓘(ℝ, ℂ) (fun y ↦ (u y : ℂ)) x = 0 := by
    ext w
    have hw := mvfderiv_coe_apply_eq_mul_mpullback_circleAngularForm (hu x) w
    rw [h, mvfderiv_apply_eq_mfderiv_apply] at hw
    simp only [Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Complex.ofReal_zero, zero_mul,
      mul_zero] at hw
    -- `hw` is an equation in `ℂ`, the tangent space `TangentSpace 𝓘(ℝ, ℂ) _`
    exact hw
  refine ⟨u x₀, funext fun x ↦ Circle.ext ?_⟩
  exact MDifferentiable.apply_eq_of_mfderiv_eq_zero (fun y ↦ mdifferentiableAt_coe (hu y))
    hzero x x₀

/-- **A circle-valued map is determined by its logarithmic derivative and one value**, on a
connected manifold. -/
theorem eq_of_mpullback_circleAngularForm_eq [IsManifold I 1 M] [PreconnectedSpace M]
    {u v : M → Circle} (hu : MDifferentiable I (𝓡 1) u) (hv : MDifferentiable I (𝓡 1) v)
    (h : mpullback I (𝓡 1) u circleAngularForm = mpullback I (𝓡 1) v circleAngularForm)
    {x₀ : M} (h₀ : u x₀ = v x₀) : u = v := by
  have hv' : MDifferentiable I (𝓡 1) v⁻¹ := fun x ↦ mdifferentiableAt_inv (hv x)
  -- `u v⁻¹` has zero logarithmic derivative, so it is constant, equal to its value `1` at `x₀`
  obtain ⟨c, hc⟩ := (mpullback_circleAngularForm_eq_zero_iff fun x ↦
    mdifferentiableAt_mul (hu x) (hv' x)).mp (by
      rw [mpullback_mul_circleAngularForm hu hv', mpullback_inv_circleAngularForm hv, h,
        add_neg_cancel])
  have hc₀ := congrFun hc x₀
  simp only [Pi.mul_apply, Pi.inv_apply, h₀, mul_inv_cancel] at hc₀
  funext x
  have hcx := congrFun hc x
  rwa [← hc₀, Pi.mul_apply, Pi.inv_apply, mul_inv_eq_one] at hcx

/-- The angular form pulls back to `dt` along the parametrization `t ↦ exp (t i)` of the
circle. -/
theorem mpullback_circleExp_circleAngularForm :
    mpullback 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp circleAngularForm =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, ℝ) id) := by
  funext t
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hd : HasDerivAt (fun s : ℝ ↦ (Circle.exp s : ℂ))
      (Complex.exp (t * Complex.I) * Complex.I) t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).cexp
  rw [mpullback_circleAngularForm_apply
      ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero),
    mvfderiv_eq_fderiv, hd.hasFDerivAt.fderiv, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_eq_fderiv, fderiv_id]
  have he : conj (Circle.exp t : ℂ) * Complex.exp (t * Complex.I) = 1 := by
    rw [← Circle.coe_exp, ← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe,
      Complex.ofReal_one]
  have key (a : ℝ) :
      (conj (Circle.exp t : ℂ) * (a • (Complex.exp (t * Complex.I) * Complex.I))).im = a := by
    have h : conj (Circle.exp t : ℂ) * (a * (Complex.exp (t * Complex.I) * Complex.I)) =
        a * Complex.I := by
      linear_combination (a * Complex.I) * he
    rw [Complex.real_smul, h]
    simp
  exact key _

/-- **The logarithmic derivative is closed**: `d θ_u = 0` for a `C²` map `u : M → S¹`. -/
theorem mextDeriv_mpullback_circleAngularForm [IsManifold I 2 M] {u : M → Circle}
    (hu : ContMDiff I (𝓡 1) 2 u) :
    mextDeriv (mpullback I (𝓡 1) u circleAngularForm) = 0 := by
  rw [← mpullback_mextDeriv hu ((isSmoothBundleForm_def _ _).mpr
    (isSmoothForm_circleAngularForm.of_le (by simp)).contMDiff), mextDeriv_circleAngularForm,
    mpullback_zero]

/-! ### Integrals along paths and periods -/

variable [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]

/-- **Integrating the angular form along a path in the circle** recovers the endpoint:
`z · exp (i ∫_γ dθ) = w` for a path class `γ` from `z` to `w`. -/
theorem mul_circleExp_pathClassIntegral_circleAngularForm {z w : Circle}
    (γ : Path.Homotopic.Quotient z w) :
    z * Circle.exp (pathClassIntegral circleAngularForm γ) = w := by
  induction γ with | mk p =>
  -- lift the path through the covering `t ↦ exp (t i)`, where `dθ` becomes `dt`
  obtain ⟨t₀, rfl⟩ := Circle.exp_surjective z
  obtain ⟨Γ, hΓ, hΓ₀⟩ :=
    Circle.isCoveringMap_exp.exists_path_lifts p.toContinuousMap t₀ (by simp)
  have hw : Circle.exp (Γ 1) = w := by
    simpa using congrFun hΓ 1
  subst hw
  let q : Path t₀ (Γ 1) := ⟨Γ, hΓ₀, rfl⟩
  have hpq : p = q.map Circle.exp.continuous :=
    Path.ext (funext fun t ↦ (congrFun hΓ t).symm)
  have h : pathClassIntegral (mpullback 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp circleAngularForm) (.mk q) =
      pathClassIntegral circleAngularForm ((Path.Homotopic.Quotient.mk q).map Circle.exp) :=
    pathClassIntegral_mpullback contMDiff_circleExp
      (isSmoothForm_circleAngularForm.of_le (by simp)) mextDeriv_circleAngularForm _
  rw [hpq, Path.Homotopic.Quotient.mk_map q Circle.exp, ← h,
    mpullback_circleExp_circleAngularForm, pathClassIntegral_mextDeriv_ofFunction contMDiff_id,
    ← Circle.exp_add, id, id, add_sub_cancel]

/-- **Integrating the logarithmic derivative** of a `C²` map `u : M → S¹` along a path class `γ`
from `x` to `y` recovers `u`: `u x · exp (i ∫_γ θ_u) = u y`. -/
theorem mul_circleExp_pathClassIntegral_mpullback_circleAngularForm {u : M → Circle}
    (hu : ContMDiff I (𝓡 1) 2 u) {x y : M} (γ : Path.Homotopic.Quotient x y) :
    u x * Circle.exp (pathClassIntegral (mpullback I (𝓡 1) u circleAngularForm) γ) = u y := by
  rw [pathClassIntegral_mpullback hu (isSmoothForm_circleAngularForm.of_le (by simp))
    mextDeriv_circleAngularForm]
  exact mul_circleExp_pathClassIntegral_circleAngularForm _

/-- **The periods of a logarithmic derivative are integral**: every period of `θ_u = u^* dθ`, for
a `C²` map `u : M → S¹`, lies in `2πℤ`. -/
theorem periodHom_mpullback_circleAngularForm_mem_zmultiples {u : M → Circle}
    (hu : ContMDiff I (𝓡 1) 2 u) (x : M) (γ : Additive (FundamentalGroup M x)) :
    periodHom (mpullback I (𝓡 1) u circleAngularForm) x γ ∈ AddSubgroup.zmultiples (2 * π) := by
  have h := mul_circleExp_pathClassIntegral_mpullback_circleAngularForm hu
    (Additive.toMul γ).toPath
  rw [mul_eq_left, Circle.exp_eq_one] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [periodHom_apply, hn]; exact zsmul_eq_mul _ _⟩

/-- **Closed forms with integral periods are logarithmic derivatives.** On a connected manifold,
a closed `C^r` real `1`-form `φ` (`1 ≤ r`) whose periods at `x₀` lie in `2πℤ` is the logarithmic
derivative `θ_u = u^* dθ` of a `C^r` map `u : M → S¹` with `u x₀ = 1`, namely
`u y = exp (i ∫_γ φ)` for any path `γ` from `x₀` to `y`. -/
theorem exists_contMDiff_mpullback_circleAngularForm_eq [PreconnectedSpace M] {r : ℕ∞}
    (hr : 1 ≤ r) {φ : RoughForm I M ℝ 1} (hφ : IsSmoothForm I r φ) (hclosed : mextDeriv φ = 0)
    (x₀ : M) (hper : ∀ γ, periodHom φ x₀ γ ∈ AddSubgroup.zmultiples (2 * π)) :
    ∃ u : M → Circle, ContMDiff I (𝓡 1) r u ∧ u x₀ = 1 ∧
      mpullback I (𝓡 1) u circleAngularForm = φ := by
  have := I.locallyPathConnectedSpace
  have := ChartedSpace.locallyPathConnectedSpace H M
  have : ConnectedSpace M := { toNonempty := ⟨x₀⟩ }
  have : PathConnectedSpace M := pathConnectedSpace_iff_connectedSpace.mpr ‹_›
  -- `u y` is `exp (i ∫ φ)` along a chosen path from `x₀` to `y`
  let u (y : M) : Circle :=
    Circle.exp (pathClassIntegral φ (.mk (PathConnectedSpace.somePath x₀ y)))
  -- it does not depend on the path, because the periods of `φ` lie in `2πℤ`
  have hu_eq {y : M} (γ : Path.Homotopic.Quotient x₀ y) :
      u y = Circle.exp (pathClassIntegral φ γ) := by
    obtain ⟨n, hn⟩ := hper (Additive.ofMul (FundamentalGroup.fromPath
      ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ y)).trans γ.symm)))
    rw [periodHom_apply, toMul_ofMul, pathClassIntegral_trans, pathClassIntegral_symm] at hn
    refine Circle.exp_eq_exp.mpr ⟨n, ?_⟩
    simp only [zsmul_eq_mul] at hn
    linarith
  have hu_trans {x y : M} (δ : Path.Homotopic.Quotient x y) :
      u y = u x * Circle.exp (pathClassIntegral φ δ) := by
    rw [hu_eq ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)).trans δ),
      pathClassIntegral_trans, Circle.exp_add]
  -- near each point, `u` is a constant times `exp (i g)` for a local primitive `g` of `φ`
  have hloc (x : M) : ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) r g ∧
      mextDeriv (RoughForm.ofFunction I g) x = φ x ∧
      u =ᶠ[𝓝 x] fun y ↦ u x * Circle.exp (-g x) * Circle.exp (g y) := by
    obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn hr hφ hclosed x
    obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ :=
      (path_connected_basis x).mem_iff.mp (hgU.isOpen.mem_nhds hxU)
    refine ⟨g, hg, hgU.mextDeriv_eq x hxU, ?_⟩
    filter_upwards [hV] with y hy
    -- along a path inside `V`, the integral of `φ` is the change of `g`
    have hxy := hVc.joinedIn x (mem_of_mem_nhds hV) y hy
    have hδ := pathClassIntegral_mk_eq_sub (hφ.of_le (by exact_mod_cast hr)) hclosed
      ((PrimitiveSpace.continuousOn_graph hgU).comp_continuous hxy.somePath.continuous
        fun t ↦ hVU (hxy.somePath_mem t)) (fun t ↦ PrimitiveSpace.proj_graph _)
    simp only [Function.comp_apply, PrimitiveSpace.value_graph, Path.source, Path.target] at hδ
    rw [hu_trans (.mk hxy.somePath), hδ, mul_assoc]
    congr 1
    rw [← Circle.exp_add, neg_add_eq_sub]
  refine ⟨u, fun x ↦ ?_, ?_, funext fun x ↦ ?_⟩
  · obtain ⟨g, hg, -, hug⟩ := hloc x
    exact ((contMDiff_mul_left.comp (contMDiff_circleExp.comp hg)) x).congr_of_eventuallyEq hug
  · rw [hu_eq (.refl x₀), pathClassIntegral_refl, Circle.exp_zero]
  · obtain ⟨g, hg, hdg, hug⟩ := hloc x
    have hg₁ : MDifferentiable I 𝓘(ℝ, ℝ) g :=
      hg.mdifferentiable (by simpa using (zero_lt_one.trans_le hr).ne')
    have hexp : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp :=
      (contMDiff_circleExp (m := 1)).mdifferentiable one_ne_zero
    have hprod : (fun y ↦ u x * Circle.exp (-g x) * Circle.exp (g y)) =
        (fun _ ↦ u x * Circle.exp (-g x)) * (Circle.exp ∘ g) :=
      rfl
    -- `θ_u = θ_c + θ_{exp ∘ g} = g^* dt = dg` near `x`
    rw [hug.mpullback_eq, hprod, mpullback_mul_circleAngularForm (fun _ ↦ mdifferentiableAt_const)
      (hexp.comp hg₁), mpullback_const_circleAngularForm, zero_add, mpullback_comp hg₁ hexp,
      mpullback_circleExp_circleAngularForm, ← hdg,
      mpullback_mextDeriv_ofFunction_apply (hg₁ x) mdifferentiableAt_id, Function.id_comp]

end TauCeti

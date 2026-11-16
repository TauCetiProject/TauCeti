/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.Degree.Continuous
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
-- Private: smooth integer powers on Lie groups, global degree integration, top-form orientation
-- criteria, and connectedness of spheres are used only inside proofs.
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Geometry.Manifold.Orientation.TopForm
import TauCeti.Geometry.Sphere.Connected

/-!
# The mapping degree on the circle and reconciliation with `Circle.degree`

On the unit circle `S¹ = Circle` of `ℂ`, the angular `1`-form `dθ` (`TauCeti.circleAngularForm`) is
nowhere vanishing, integrates to `2π` over the counterclockwise orientation
`TauCeti.circleOrientation` (`TauCeti.integralTopForm_circleOrientation_circleAngularForm`), and
selects the same orientation as the outward-normal orientation
`Complex.orientation.sphereOrientation` of `S¹ ⊆ ℂ`
(`TauCeti.circleOrientation_eq_sphereOrientation`).

For a differentiable circle-valued map `f : M → Circle`, the pulled-back angular form `f^* dθ` is
the imaginary part of the logarithmic derivative `dlog f`
(`TauCeti.mpullback_circleAngularForm_apply_eq_im_mlogDeriv`). Because `dlog` turns pointwise
products into sums, pullback of `dθ` is additive under pointwise multiplication
(`TauCeti.mpullback_mul_circleAngularForm`), negates under inversion
(`TauCeti.mpullback_inv_circleAngularForm`), and scales by `k` under the `k`-th integer power
(`TauCeti.mpullback_zpow_circleAngularForm`). In particular, on `Circle` itself,

`((· ^ k)^* dθ) = k • dθ` (`TauCeti.mpullback_zpow_id_circleAngularForm`).

Combining this identity with the top-form degree formula `∫_{S¹} f^* dθ = deg(f) · 2π`
(`TauCeti.integralTopForm_circleOrientation_mpullback_circleAngularForm`) and the top-form
orientation criteria gives the complete smooth and continuous degree calculus on `S¹`:

* `z ↦ z ^ k` (`k : ℤ`) preserves orientation when `0 < k`, reverses orientation when `k < 0`, has
  every point of `S¹` as a regular value when `k ≠ 0`, and has smooth and continuous mapping degree
  `k` (`TauCeti.degree_zpow_circle`, `TauCeti.continuousDegree_zpow_id_circle`);
* inversion `z ↦ z⁻¹` on `Circle` and complex conjugation `TauCeti.conjSphere` on
  `sphere (0 : ℂ) 1` have smooth and continuous mapping degree `-1`
  (`TauCeti.degree_inv_circle`, `TauCeti.degree_conjSphere`, `TauCeti.continuousDegree_conjSphere`);
* pointwise multiplication, inversion, division, and powers of maps into `Circle` act on the
  mapping degree as addition, negation, subtraction, and scalar multiplication
  (`TauCeti.degree_mul_circle`, `TauCeti.continuousDegree_mul_circle`,
  `TauCeti.continuousDegree_zpow_circle`).

Finally, lifting `f.toBasedLoop` along the universal covering `Circle.exp : ℝ → Circle` writes any
continuous map `f : C(Circle, Circle)` as `f z = exp (i Ψ z) · z ^ k` for a continuous real-valued
phase `Ψ : C(Circle, ℝ)` and `k = Circle.degree f.toBasedLoop`
(`ContinuousMap.exists_exp_mul_zpow_eq`). Scaling `Ψ` linearly to `0` homotopes `f` to `z ↦ z ^ k`
(`ContinuousMap.homotopic_zpow`), reconciling the differential-geometric mapping degree with the
covering-space winding number `Circle.degree`:

* `TauCeti.continuousDegree_circle_eq_circleDegree`:
  `continuousDegree o o f = Circle.degree f.toBasedLoop` for every orientation `o` of `S¹`;
* `TauCeti.continuousDegree_toCircle`: `continuousDegree o o γ.toCircle = Circle.degree γ` for
  every loop `γ` in `S¹`;
* `TauCeti.degree_circle_eq_circleDegree`: `degree o o f` agrees with `Circle.degree` on smooth
  maps `S¹ → S¹`;
* `TauCeti.homotopic_circle_iff_continuousDegree_eq` and
  `ContinuousMap.homotopic_iff_degree_toBasedLoop_eq`: two maps in `C(Circle, Circle)` are
  homotopic if and only if they have the same mapping degree.

## Main results

* `TauCeti.circleOrientation_eq_sphereOrientation`: `circleOrientation` equals
  `Complex.orientation.sphereOrientation`.
* `TauCeti.mpullback_circleAngularForm_apply_eq_im_mlogDeriv`,
  `TauCeti.mpullback_mul_circleAngularForm`, `TauCeti.mpullback_inv_circleAngularForm`,
  `TauCeti.mpullback_zpow_circleAngularForm`, `TauCeti.mpullback_zpow_id_circleAngularForm`:
  pullback calculus of `dθ` under group operations and integer powers.
* `TauCeti.integralTopForm_circleOrientation_mpullback_circleAngularForm`:
  `∫_{S¹} f^* dθ = deg(f) · 2π`.
* `TauCeti.isOrientationPreservingAt_zpow_circle`, `TauCeti.isOrientationReversingAt_zpow_circle`,
  `TauCeti.isRegularValue_zpow_circle`, `TauCeti.degreeAtRegularValue_zpow_circle`: local and
  regular-value calculus of `z ↦ z ^ k`.
* `TauCeti.degree_zpow_circle`, `TauCeti.degree_pow_circle`, `TauCeti.degree_inv_circle`,
  `TauCeti.degree_conjSphere`, `TauCeti.degree_mul_circle`, `TauCeti.degree_fun_zpow_circle`:
  smooth mapping degrees on `S¹`.
* `TauCeti.continuousDegree_one_circle`, `TauCeti.continuousDegree_mul_circle`,
  `TauCeti.continuousDegree_inv_circle`, `TauCeti.continuousDegree_div_circle`,
  `TauCeti.continuousDegree_pow_circle`, `TauCeti.continuousDegree_zpow_circle`,
  `TauCeti.continuousDegree_zpow_id_circle`, `TauCeti.continuousDegree_conjSphere`: continuous
  mapping degrees on `S¹`.
* `ContinuousMap.exists_exp_mul_zpow_eq`, `ContinuousMap.homotopic_zpow`: phase factorization and
  homotopy to `z ↦ z ^ k`.
* `TauCeti.continuousDegree_circle_eq_circleDegree`, `TauCeti.continuousDegree_toCircle`,
  `TauCeti.degree_circle_eq_circleDegree`, `TauCeti.homotopic_circle_iff_continuousDegree_eq`,
  `ContinuousMap.homotopic_iff_degree_toBasedLoop_eq`: reconciliation with `Circle.degree` and
  homotopy classification of maps `S¹ → S¹`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory (Example 17.36 and Problem 17-13).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open ContinuousMap Function Metric Module Set
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-! ### Orientation of the circle and pullbacks of the angular form -/

/-- Evaluation of the angular form `dθ` on `Circle` in terms of the ambient derivative in `ℂ`. -/
@[simp]
theorem circleAngularForm_apply (z : Circle) (v : Fin 1 → TangentSpace (𝓡 1) z) :
    circleAngularForm z v =
      (z : ℂ).re * (mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) z (v 0)).im -
        (z : ℂ).im * (mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) z (v 0)).re := by
  rw [circleAngularForm_def, mpullback_apply]
  exact planeAngularForm_apply _ _

/-- The counterclockwise orientation `TauCeti.circleOrientation` defined by the angular form `dθ`
coincides with the outward-normal orientation `Complex.orientation.sphereOrientation` of the unit
circle in `ℂ`. -/
theorem circleOrientation_eq_sphereOrientation :
    circleOrientation = Complex.orientation.sphereOrientation := by
  ext z
  let b : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z) := circleTangentBasis z
  have hb_sph : b.orientation = Complex.orientation.sphereOrientation.orientationAt z :=
    orientation_circleTangentBasis z
  have hb_pos := (Complex.orientation_eq_orientationAt_sphereOrientation_iff b).1 hb_sph
  have hb_cir : b.orientation = circleOrientation.orientationAt z := by
    rw [orientation_eq_orientationAt_circleOrientation_iff, circleAngularForm_apply]
    exact hb_pos
  exact hb_cir.symm.trans hb_sph

section PullbackAngularForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- For a map `f : M → Circle` differentiable at `x`, the pulled-back angular form `f^* dθ` at `x`
is the imaginary part of the logarithmic derivative `dlog f`. -/
theorem mpullback_circleAngularForm_apply_eq_im_mlogDeriv {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (v : Fin 1 → TangentSpace I x) :
    mpullback I (𝓡 1) f circleAngularForm x v =
      (mlogDeriv I (fun y ↦ (f y : ℂ)) x v).im := by
  have hcoe : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun w : Circle ↦ (w : ℂ)) (f x) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hd : mvfderiv (𝓡 1) (fun w : Circle ↦ (w : ℂ)) (f x) (mfderiv I (𝓡 1) f x (v 0)) =
      mvfderiv I (fun y ↦ (f y : ℂ)) x (v 0) :=
    (mvfderiv_comp_apply x hcoe hf (v 0)).symm
  rw [mpullback_apply, circleAngularForm_apply, hd, mlogDeriv_apply, ← Circle.coe_inv,
    Circle.coe_inv_eq_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Pulling back the angular form along a constant map into `Circle` gives `0`. -/
@[simp]
theorem mpullback_const_circleAngularForm (z₀ : Circle) :
    mpullback I (𝓡 1) (fun _ : M ↦ z₀) circleAngularForm = 0 := by
  ext x v
  rw [mpullback_circleAngularForm_apply_eq_im_mlogDeriv mdifferentiableAt_const]
  simp [mlogDeriv_const]

/-- **Pullback of `dθ` turns products into sums.** If `f, g : M → Circle` are differentiable at `x`,
then `(f * g)^* dθ = f^* dθ + g^* dθ` at `x`. -/
theorem mpullback_mul_circleAngularForm_apply {f g : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (hg : MDifferentiableAt I (𝓡 1) g x) :
    mpullback I (𝓡 1) (fun y ↦ f y * g y) circleAngularForm x =
      mpullback I (𝓡 1) f circleAngularForm x + mpullback I (𝓡 1) g circleAngularForm x := by
  have hfg : MDifferentiableAt I (𝓡 1) (fun y ↦ f y * g y) x :=
    ((contMDiff_mul (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x (hf.prodMk hg)
  have hcoe (w : Circle) : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle ↦ (z : ℂ)) w :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have huf : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (f y : ℂ)) x := (hcoe (f x)).comp x hf
  have hug : MDifferentiableAt I 𝓘(ℝ, ℂ) (fun y ↦ (g y : ℂ)) x := (hcoe (g x)).comp x hg
  ext v
  rw [mpullback_circleAngularForm_apply_eq_im_mlogDeriv hfg, ContinuousAlternatingMap.add_apply,
    mpullback_circleAngularForm_apply_eq_im_mlogDeriv hf,
    mpullback_circleAngularForm_apply_eq_im_mlogDeriv hg]
  have hmul := mlogDeriv_mul huf hug (Circle.coe_ne_zero (f x)) (Circle.coe_ne_zero (g x))
  simpa only [Pi.mul_def, Circle.coe_mul, ContinuousAlternatingMap.add_apply,
    Complex.add_im] using congrArg (fun η ↦ (η v).im) hmul

/-- For differentiable maps `f, g : M → Circle`, `(f * g)^* dθ = f^* dθ + g^* dθ`. -/
theorem mpullback_mul_circleAngularForm {f g : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (hg : MDifferentiable I (𝓡 1) g) :
    mpullback I (𝓡 1) (fun y ↦ f y * g y) circleAngularForm =
      mpullback I (𝓡 1) f circleAngularForm + mpullback I (𝓡 1) g circleAngularForm :=
  funext fun x ↦ mpullback_mul_circleAngularForm_apply (hf x) (hg x)

/-- If `f : M → Circle` is differentiable at `x`, then `(f⁻¹)^* dθ = - f^* dθ` at `x`. -/
theorem mpullback_inv_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) :
    mpullback I (𝓡 1) (fun y ↦ (f y)⁻¹) circleAngularForm x =
      -mpullback I (𝓡 1) f circleAngularForm x := by
  have hinv : MDifferentiableAt I (𝓡 1) (fun y ↦ (f y)⁻¹) x :=
    ((contMDiff_inv (𝓡 1) 1).mdifferentiableAt one_ne_zero).comp x hf
  have h := mpullback_mul_circleAngularForm_apply hf hinv
  simp only [mul_inv_cancel, mpullback_const_circleAngularForm, Pi.zero_apply] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- For a differentiable map `f : M → Circle`, `(f⁻¹)^* dθ = - f^* dθ`. -/
theorem mpullback_inv_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f) :
    mpullback I (𝓡 1) (fun y ↦ (f y)⁻¹) circleAngularForm =
      -mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_inv_circleAngularForm_apply (hf x)

/-- If `f : M → Circle` is differentiable at `x`, then `(f ^ n)^* dθ = n • f^* dθ` at `x` for every
`n : ℕ`. -/
theorem mpullback_pow_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (n : ℕ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ n) circleAngularForm x =
      (n : ℝ) • mpullback I (𝓡 1) f circleAngularForm x := by
  induction n with
  | zero =>
    simp [mpullback_const_circleAngularForm]
  | succ n ih =>
    have hpow : MDifferentiableAt I (𝓡 1) (fun y ↦ f y ^ n) x :=
      (((contMDiff_pow n : ContMDiff (𝓡 1) (𝓡 1) 1 _)).mdifferentiableAt one_ne_zero).comp x hf
    simp only [pow_succ]
    rw [mpullback_mul_circleAngularForm_apply hpow hf, ih, Nat.cast_add, Nat.cast_one, add_smul,
      one_smul]

/-- For a differentiable map `f : M → Circle` and `n : ℕ`, `(f ^ n)^* dθ = n • f^* dθ`. -/
theorem mpullback_pow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (n : ℕ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ n) circleAngularForm =
      (n : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_pow_circleAngularForm_apply (hf x) n

/-- If `f : M → Circle` is differentiable at `x`, then `(f ^ k)^* dθ = k • f^* dθ` at `x` for every
`k : ℤ`. -/
theorem mpullback_zpow_circleAngularForm_apply {f : M → Circle} {x : M}
    (hf : MDifferentiableAt I (𝓡 1) f x) (k : ℤ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ k) circleAngularForm x =
      (k : ℝ) • mpullback I (𝓡 1) f circleAngularForm x := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast, Int.cast_natCast] using mpullback_pow_circleAngularForm_apply hf n
  · have hpow : MDifferentiableAt I (𝓡 1) (fun y ↦ f y ^ n) x :=
      (((contMDiff_pow n : ContMDiff (𝓡 1) (𝓡 1) 1 _)).mdifferentiableAt one_ne_zero).comp x hf
    simp only [zpow_neg, zpow_natCast, Int.cast_neg, Int.cast_natCast]
    rw [mpullback_inv_circleAngularForm_apply hpow, mpullback_pow_circleAngularForm_apply hf n]
    ext v
    simp

/-- For a differentiable map `f : M → Circle` and `k : ℤ`, `(f ^ k)^* dθ = k • f^* dθ`. -/
theorem mpullback_zpow_circleAngularForm {f : M → Circle} (hf : MDifferentiable I (𝓡 1) f)
    (k : ℤ) :
    mpullback I (𝓡 1) (fun y ↦ f y ^ k) circleAngularForm =
      (k : ℝ) • mpullback I (𝓡 1) f circleAngularForm :=
  funext fun x ↦ mpullback_zpow_circleAngularForm_apply (hf x) k

end PullbackAngularForm

/-- Left multiplication on `Circle` preserves the angular form `dθ`. -/
@[simp]
theorem mpullback_mul_left_circleAngularForm (z₀ : Circle) :
    mpullback (𝓡 1) (𝓡 1) (z₀ * ·) circleAngularForm = circleAngularForm := by
  simpa only [id_eq, mpullback_const_circleAngularForm, zero_add, mpullback_id] using
    mpullback_mul_circleAngularForm (I := 𝓡 1) (mdifferentiable_const (c := z₀)) mdifferentiable_id

/-- Right multiplication on `Circle` preserves the angular form `dθ`. -/
@[simp]
theorem mpullback_mul_right_circleAngularForm (z₀ : Circle) :
    mpullback (𝓡 1) (𝓡 1) (· * z₀) circleAngularForm = circleAngularForm := by
  simpa only [id_eq, mpullback_const_circleAngularForm, add_zero, mpullback_id] using
    mpullback_mul_circleAngularForm (I := 𝓡 1) mdifferentiable_id (mdifferentiable_const (c := z₀))

/-- Inversion on `Circle` negates the angular form `dθ`. -/
@[simp]
theorem mpullback_inv_id_circleAngularForm :
    mpullback (𝓡 1) (𝓡 1) (·⁻¹ : Circle → Circle) circleAngularForm = -circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_inv_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id

/-- The natural power map `z ↦ z ^ n` on `Circle` pulls `dθ` back to `n • dθ`. -/
@[simp]
theorem mpullback_pow_id_circleAngularForm (n : ℕ) :
    mpullback (𝓡 1) (𝓡 1) (fun z : Circle ↦ z ^ n) circleAngularForm =
      (n : ℝ) • circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_pow_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id n

/-- **Pullback of `dθ` by `z ↦ z ^ k`.** For every integer `k : ℤ`, the power map `z ↦ z ^ k` on
`Circle` pulls the angular form `dθ` back to `k • dθ`. -/
@[simp]
theorem mpullback_zpow_id_circleAngularForm (k : ℤ) :
    mpullback (𝓡 1) (𝓡 1) (fun z : Circle ↦ z ^ k) circleAngularForm =
      (k : ℝ) • circleAngularForm := by
  simpa only [id_eq, mpullback_id] using mpullback_zpow_circleAngularForm (I := 𝓡 1)
    mdifferentiable_id k

/-! ### Integral formula, local orientation signs, and smooth degrees on `Circle` -/

/-- For a self-map `f : Circle → Circle`, `degree o o f` is the same for both orientations `o` of
`Circle`. -/
theorem degree_circle_eq_circleOrientation (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : Circle → Circle) :
    degree o o f = degree circleOrientation circleOrientation f := by
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · rfl
  · rw [degree_neg_left, degree_neg_right, neg_neg]

/-- For a continuous self-map `f : C(Circle, Circle)`, `continuousDegree o o f` is the same for
both orientations `o` of `Circle`. -/
theorem continuousDegree_circle_eq_circleOrientation
    (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(Circle, Circle)) :
    continuousDegree o o f = continuousDegree circleOrientation circleOrientation f := by
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · rfl
  · rw [continuousDegree_neg_left, continuousDegree_neg_right, neg_neg]

/-- **Integral formula for the mapping degree on `S¹`.** For every smooth map `f : Circle → Circle`
and every orientation `o` of `Circle`, the counterclockwise integral of `f^* dθ` is `deg(f) · 2π`.
-/
theorem integralTopForm_circleOrientation_mpullback_circleAngularForm
    (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f : Circle → Circle}
    (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) :
    integralTopForm circleOrientation (mpullback (𝓡 1) (𝓡 1) f circleAngularForm) =
      degree o o f * (2 * Real.pi) := by
  rw [degree_circle_eq_circleOrientation o f,
    integralTopForm_mpullback_eq_degree_mul circleOrientation circleOrientation hf
      isSmoothForm_circleAngularForm (isClosed_tsupport _).isCompact,
    integralTopForm_circleOrientation_circleAngularForm]

/-- **Pointwise multiplication of smooth maps `S¹ → S¹` adds their degrees.** -/
theorem degree_mul_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f g : Circle → Circle}
    (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) (hg : ContMDiff (𝓡 1) (𝓡 1) ∞ g) :
    degree o o (fun z ↦ f z * g z) = degree o o f + degree o o g := by
  have hfg := integralTopForm_circleOrientation_mpullback_circleAngularForm o
    (f := fun z ↦ f z * g z) (hf.mul hg)
  have hf_int := integralTopForm_circleOrientation_mpullback_circleAngularForm o hf
  have hg_int := integralTopForm_circleOrientation_mpullback_circleAngularForm o hg
  have hadd : integralTopForm circleOrientation
        (mpullback (𝓡 1) (𝓡 1) (fun z ↦ f z * g z) circleAngularForm) =
      integralTopForm circleOrientation (mpullback (𝓡 1) (𝓡 1) f circleAngularForm) +
        integralTopForm circleOrientation (mpullback (𝓡 1) (𝓡 1) g circleAngularForm) := by
    rw [mpullback_mul_circleAngularForm (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp))]
    exact integralTopForm_add_of_compactSpace circleOrientation
      ((isSmoothForm_circleAngularForm.mpullback hf).of_le zero_le)
      ((isSmoothForm_circleAngularForm.mpullback hg).of_le zero_le)
  rw [hfg, hf_int, hg_int, ← add_mul, ← Int.cast_add] at hadd
  exact_mod_cast mul_right_cancel₀ Real.two_pi_pos.ne' hadd

/-- **Degree of integer power maps on `S¹`.** For every orientation `o` of `Circle` and every
`k : ℤ`, the map `z ↦ z ^ k` has smooth mapping degree `k`. -/
@[simp]
theorem degree_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (k : ℤ) :
    degree o o (fun z : Circle ↦ z ^ k) = k := by
  have h := integralTopForm_circleOrientation_mpullback_circleAngularForm o (contMDiff_zpow k)
  simp only [mpullback_zpow_id_circleAngularForm, integralTopForm_smul,
    integralTopForm_circleOrientation_circleAngularForm] at h
  exact_mod_cast mul_right_cancel₀ Real.two_pi_pos.ne' h.symm

/-- **Degree of natural power maps on `S¹`.** For every orientation `o` of `Circle` and every
`n : ℕ`, the map `z ↦ z ^ n` has smooth mapping degree `n`. -/
@[simp]
theorem degree_pow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (n : ℕ) :
    degree o o (fun z : Circle ↦ z ^ n) = n := by
  simpa only [zpow_natCast] using degree_zpow_circle o (n : ℤ)

/-- **Degree of inversion on `S¹`.** Inversion `z ↦ z⁻¹` (which equals complex conjugation
`z ↦ conj z` on `Circle`) has smooth mapping degree `-1`. -/
@[simp]
theorem degree_inv_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    degree o o (·⁻¹ : Circle → Circle) = -1 := by
  simpa only [zpow_neg, zpow_one] using degree_zpow_circle o (-1)

/-- Raising a smooth map `f : Circle → Circle` pointwise to the `k`-th integer power multiplies its
degree by `k`. -/
theorem degree_fun_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) (k : ℤ) :
    degree o o (fun z ↦ f z ^ k) = k * degree o o f := by
  simpa only [Function.comp_def, degree_zpow_circle] using
    degree_comp o o o hf (contMDiff_zpow k)

/-- Raising a smooth map `f : Circle → Circle` pointwise to the `n`-th natural power multiplies its
degree by `n`. -/
theorem degree_fun_pow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) (n : ℕ) :
    degree o o (fun z ↦ f z ^ n) = n * degree o o f := by
  simpa only [zpow_natCast] using degree_fun_zpow_circle o hf (n : ℤ)

/-- Pointwise inversion of a smooth map `f : Circle → Circle` negates its degree. -/
theorem degree_fun_inv_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) :
    degree o o (fun z ↦ (f z)⁻¹) = -degree o o f := by
  simpa only [zpow_neg, zpow_one, neg_one_mul] using degree_fun_zpow_circle o hf (-1)

/-- Left rotation `z ↦ z₀ * z` on `Circle` has smooth mapping degree `1`. -/
@[simp]
theorem degree_mul_left_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (z₀ : Circle) :
    degree o o (z₀ * ·) = 1 := by
  have h := degree_mul_circle o (contMDiff_const (c := z₀)) contMDiff_id
  simpa [degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)))] using h

/-- Right rotation `z ↦ z * z₀` on `Circle` has smooth mapping degree `1`. -/
@[simp]
theorem degree_mul_right_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (z₀ : Circle) :
    degree o o (· * z₀) = 1 := by
  have h := degree_mul_circle o contMDiff_id (contMDiff_const (c := z₀))
  simpa [degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)))] using h

/-- `circleOrientation` equals the `ofTopForm` orientation attached to `circleAngularForm`. -/
private theorem circleOrientation_eq_ofTopForm :
    circleOrientation =
      Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin circleAngularForm
        (isSmoothForm_circleAngularForm.of_le zero_le) circleAngularForm_ne_zero := by
  ext z
  let b : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z) := circleTangentBasis z
  have hb : b.orientation = circleOrientation.orientationAt z := by
    rw [circleOrientation_eq_sphereOrientation]
    exact orientation_circleTangentBasis z
  have hpos : 0 < circleAngularForm z b :=
    (orientation_eq_orientationAt_circleOrientation_iff b).1 hb
  exact hb.symm.trans
    ((Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff _ _ _ b).2 hpos)

/-- For `0 < k`, the integer power map `z ↦ z ^ k` preserves every orientation `o` of `Circle` at
every point `z`. -/
theorem isOrientationPreservingAt_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : 0 < k) (z : Circle) :
    Manifold.Orientation.IsOrientationPreservingAt o o (fun w : Circle ↦ w ^ k) z := by
  have hcir : Manifold.Orientation.IsOrientationPreservingAt circleOrientation circleOrientation
      (fun w : Circle ↦ w ^ k) z := by
    rw [circleOrientation_eq_ofTopForm]
    exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
      (Int.cast_pos.2 hk) (congrFun (mpullback_zpow_id_circleAngularForm k) z)
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · exact hcir
  · simpa only [Manifold.Orientation.isOrientationPreservingAt_neg_left,
      Manifold.Orientation.isOrientationReversingAt_neg_right] using hcir

/-- For `k < 0`, the integer power map `z ↦ z ^ k` reverses every orientation `o` of `Circle` at
every point `z`. -/
theorem isOrientationReversingAt_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : k < 0) (z : Circle) :
    Manifold.Orientation.IsOrientationReversingAt o o (fun w : Circle ↦ w ^ k) z := by
  have hcir : Manifold.Orientation.IsOrientationReversingAt circleOrientation circleOrientation
      (fun w : Circle ↦ w ^ k) z := by
    rw [circleOrientation_eq_ofTopForm]
    exact Manifold.Orientation.isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
      (Int.cast_lt_zero.2 hk) (congrFun (mpullback_zpow_id_circleAngularForm k) z)
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · exact hcir
  · simpa only [Manifold.Orientation.isOrientationReversingAt_neg_left,
      Manifold.Orientation.isOrientationPreservingAt_neg_right] using hcir

/-- For `0 < k`, `z ↦ z ^ k` has orientation sign `1` at every point of `Circle`. -/
theorem orientationSign_zpow_circle_of_pos (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : 0 < k) (z : Circle) :
    Manifold.Orientation.orientationSign o o (fun w : Circle ↦ w ^ k) z = 1 :=
  Manifold.Orientation.orientationSign_of_isOrientationPreservingAt
    (isOrientationPreservingAt_zpow_circle o hk z)

/-- For `k < 0`, `z ↦ z ^ k` has orientation sign `-1` at every point of `Circle`. -/
theorem orientationSign_zpow_circle_of_neg (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : k < 0) (z : Circle) :
    Manifold.Orientation.orientationSign o o (fun w : Circle ↦ w ^ k) z = -1 :=
  Manifold.Orientation.orientationSign_of_isOrientationReversingAt
    (isOrientationReversingAt_zpow_circle o hk z)

/-- For `k ≠ 0`, every point `y : Circle` is a regular value of `z ↦ z ^ k`. -/
theorem isRegularValue_zpow_circle {k : ℤ} (hk : k ≠ 0) (y : Circle) :
    IsRegularValue (𝓡 1) (𝓡 1) (fun z : Circle ↦ z ^ k) y := by
  refine isRegularValue_iff.2 fun z _ ↦ (isRegularPoint_iff_isInvertible_mfderiv rfl).2 ?_
  refine not_not.1 (Manifold.Orientation.orientationSign_eq_zero_iff (o := circleOrientation)
    (o' := circleOrientation).not.1 ?_)
  rcases hk.lt_or_gt with hlt | hgt
  · rw [orientationSign_zpow_circle_of_neg circleOrientation hlt z]
    decide
  · rw [orientationSign_zpow_circle_of_pos circleOrientation hgt z]
    decide

/-- For `k ≠ 0`, the signed count of the fibre of `z ↦ z ^ k` over every point `y : Circle` is `k`.
-/
theorem degreeAtRegularValue_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : k ≠ 0) (y : Circle) :
    degreeAtRegularValue o o (fun z : Circle ↦ z ^ k) y = k := by
  rw [← degree_eq_degreeAtRegularValue o o (contMDiff_zpow k) (isRegularValue_zpow_circle hk y),
    degree_zpow_circle]

/-- Inversion `z ↦ z⁻¹` on `Circle` has signed fibre count `-1` at every point. -/
@[simp]
theorem degreeAtRegularValue_inv_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (y : Circle) :
    degreeAtRegularValue o o (·⁻¹ : Circle → Circle) y = -1 := by
  simpa only [zpow_neg, zpow_one] using
    degreeAtRegularValue_zpow_circle o (by decide : (-1 : ℤ) ≠ 0) y

/-- Complex conjugation `conjSphere` on `sphere (0 : ℂ) 1` has orientation sign `-1` at every
point, for either orientation `o` of the circle. -/
@[simp]
theorem orientationSign_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.orientationSign o o conjSphere z = -1 := by
  have := connectedSpace_sphere (E := ℂ) 1
  have hstd : Manifold.Orientation.orientationSign Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation conjSphere z = -1 :=
    Manifold.Orientation.orientationSign_of_isOrientationReversingAt
      (isOrientationReversingAt_conjSphere z)
  rcases o.eq_or_eq_neg Complex.orientation.sphereOrientation with rfl | rfl
  · exact hstd
  · rw [Manifold.Orientation.orientationSign_neg_left,
      Manifold.Orientation.orientationSign_neg_right, neg_neg, hstd]

/-- Complex conjugation `conjSphere` on `sphere (0 : ℂ) 1` has degree `-1` at every value. -/
@[simp]
theorem degreeAtRegularValue_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (y : sphere (0 : ℂ) 1) :
    degreeAtRegularValue o o conjSphere y = -1 := by
  rw [degreeAtRegularValue_eq_sum (s := {conjSphere y}) fun x ↦ by
    rw [Finset.mem_singleton]
    exact ⟨fun h ↦ by rw [h, conjSphere_conjSphere],
      fun h ↦ by rw [← h, conjSphere_conjSphere]⟩,
    Finset.sum_singleton, orientationSign_conjSphere]

/-- **Degree of complex conjugation on `S¹`.** On `sphere (0 : ℂ) 1`, complex conjugation
`z ↦ conj z` has smooth mapping degree `-1` for every orientation `o`. -/
@[simp]
theorem degree_conjSphere (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) :
    degree o o conjSphere = -1 := by
  have hreg (y : sphere (0 : ℂ) 1) : IsRegularValue (𝓡 1) (𝓡 1) conjSphere y :=
    isRegularValue_iff.2 fun z _ ↦ (isRegularPoint_iff_isInvertible_mfderiv rfl).2 <|
      not_not.1 <| Manifold.Orientation.orientationSign_eq_zero_iff (o := o) (o' := o).not.1 <|
        (orientationSign_conjSphere o z).trans_ne (by decide)
  rw [degree_eq_degreeAtRegularValue_choose ⟨⟨1, by simp⟩, hreg _⟩, degreeAtRegularValue_conjSphere]

/-! ### Continuous degree on `Circle` and reconciliation with `Circle.degree` -/

/-- **Continuous degree of integer power maps on `S¹`.** -/
@[simp]
theorem continuousDegree_zpow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (k : ℤ)
    {hc : Continuous fun z : Circle ↦ z ^ k} :
    continuousDegree o o ⟨(· ^ k), hc⟩ = k :=
  (continuousDegree_eq_degree o o (f := ⟨(· ^ k), hc⟩) (contMDiff_zpow k)).trans
    (degree_zpow_circle o k)

/-- **Continuous degree of natural power maps on `S¹`.** -/
@[simp]
theorem continuousDegree_pow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (n : ℕ)
    {hc : Continuous fun z : Circle ↦ z ^ n} :
    continuousDegree o o ⟨(· ^ n), hc⟩ = n := by
  simpa only [zpow_natCast] using continuousDegree_zpow_id_circle o (n : ℤ) (hc := hc)

/-- **Continuous degree of complex conjugation on `S¹`.** -/
@[simp]
theorem continuousDegree_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) {hc : Continuous conjSphere} :
    continuousDegree o o ⟨conjSphere, hc⟩ = -1 := by
  have := connectedSpace_sphere (E := ℂ) 1
  exact (continuousDegree_eq_degree o o (f := ⟨conjSphere, hc⟩) contMDiff_conjSphere).trans
    (degree_conjSphere o)

/-- The constant map `1 : C(Circle, Circle)` has continuous degree `0`. -/
@[simp]
theorem continuousDegree_one_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    continuousDegree o o 1 = 0 := by
  rw [← ContinuousMap.const_one]
  exact continuousDegree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))) o o 1

/-- **Pointwise multiplication in `C(Circle, Circle)` adds continuous degrees.** -/
@[simp]
theorem continuousDegree_mul_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f g : C(Circle, Circle)) :
    continuousDegree o o (f * g) = continuousDegree o o f + continuousDegree o o g := by
  obtain ⟨f₀, hf₀, hff₀, hdf⟩ := exists_contMDiff_homotopic_and_continuousDegree_eq o o f
  obtain ⟨g₀, hg₀, hgg₀, hdg⟩ := exists_contMDiff_homotopic_and_continuousDegree_eq o o g
  have hmul : (f * g).Homotopic (f₀ * g₀) := by
    obtain ⟨Hf⟩ := hff₀
    obtain ⟨Hg⟩ := hgg₀
    exact ⟨{
      toFun p := Hf p * Hg p
      continuous_toFun := Hf.continuous.mul Hg.continuous
      map_zero_left z := by simp
      map_one_left z := by simp }⟩
  rw [hdf, hdg, continuousDegree_eq_of_homotopic_contMDiff o o (hf₀.mul hg₀) hmul]
  exact degree_mul_circle o hf₀ hg₀

/-- **Pointwise inversion in `C(Circle, Circle)` negates the continuous degree.** -/
@[simp]
theorem continuousDegree_inv_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : C(Circle, Circle)) :
    continuousDegree o o f⁻¹ = -continuousDegree o o f := by
  have h := continuousDegree_mul_circle o f f⁻¹
  rw [mul_inv_cancel, continuousDegree_one_circle] at h
  omega

/-- Pointwise division in `C(Circle, Circle)` subtracts continuous degrees. -/
@[simp]
theorem continuousDegree_div_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f g : C(Circle, Circle)) :
    continuousDegree o o (f / g) = continuousDegree o o f - continuousDegree o o g := by
  rw [div_eq_mul_inv, continuousDegree_mul_circle, continuousDegree_inv_circle, sub_eq_add_neg]

/-- Raising `f : C(Circle, Circle)` to the `k`-th integer power multiplies its continuous degree by
`k`. -/
@[simp]
theorem continuousDegree_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : C(Circle, Circle)) (k : ℤ) :
    continuousDegree o o (f ^ k) = k * continuousDegree o o f := by
  have hcomp : (⟨(· ^ k), continuous_zpow k⟩ : C(Circle, Circle)).comp f = f ^ k :=
    ContinuousMap.ext fun _ ↦ rfl
  rw [← hcomp, continuousDegree_comp o o o, continuousDegree_zpow_id_circle]

/-- Raising `f : C(Circle, Circle)` to the `n`-th natural power multiplies its continuous degree by
`n`. -/
@[simp]
theorem continuousDegree_pow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : C(Circle, Circle)) (n : ℕ) :
    continuousDegree o o (f ^ n) = n * continuousDegree o o f := by
  simpa only [zpow_natCast] using continuousDegree_zpow_circle o f (n : ℤ)

end TauCeti

namespace ContinuousMap

/-- **Logarithmic phase factorization on `S¹`.** Every continuous map `f : C(Circle, Circle)` can
be written as `f z = Circle.exp (Ψ z) * z ^ (Circle.degree f.toBasedLoop)` for a continuous
real-valued phase function `Ψ : C(Circle, ℝ)`. -/
theorem exists_exp_mul_zpow_eq (f : C(Circle, Circle)) :
    ∃ Ψ : C(Circle, ℝ),
      ∀ z : Circle, f z = Circle.exp (Ψ z) * z ^ Circle.degree f.toBasedLoop := by
  set k : ℤ := Circle.degree f.toBasedLoop
  obtain ⟨θ, hθ⟩ := Circle.exists_lift f.toBasedLoop
  have hsub : θ 1 - θ 0 = k * (2 * Real.pi) :=
    Circle.sub_eq_degree_mul f.toBasedLoop θ.continuous hθ
  -- Subtracting the linear winding `k * (2π t)` closes `θ` into a loop `ψ` in `ℝ` at `θ 0`,
  -- which descends to `Ψ = ψ.toCircle : C(Circle, ℝ)`.
  let ψ : Path (θ 0) (θ 0) :=
    { toFun t := θ t - k * (2 * Real.pi * t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp; linarith }
  refine ⟨ψ.toCircle, fun z ↦ ?_⟩
  obtain ⟨t, rfl⟩ := TauCeti.unitToCircle_surjective z
  have hθt : θ t = ψ.toCircle (TauCeti.unitToCircle t) + k * (2 * Real.pi * t) := by
    rw [ψ.toCircle_unitToCircle]
    simp [ψ]
  rw [← f.toBasedLoop_apply, ← hθ t, hθt, Circle.exp_add, Circle.exp_intCast_mul,
    TauCeti.unitToCircle_apply]

/-- **Every continuous map `f : C(Circle, Circle)` is homotopic to `z ↦ z ^ k`**, where
`k = Circle.degree f.toBasedLoop` is the winding number of `f`. -/
theorem homotopic_zpow (f : C(Circle, Circle)) :
    f.Homotopic ⟨(· ^ Circle.degree f.toBasedLoop), continuous_zpow _⟩ := by
  obtain ⟨Ψ, hΨ⟩ := f.exists_exp_mul_zpow_eq
  exact ⟨{
    toFun p := Circle.exp ((1 - (p.1 : ℝ)) * Ψ p.2) * p.2 ^ Circle.degree f.toBasedLoop
    continuous_toFun := by fun_prop
    map_zero_left z := by simp [← hΨ z]
    map_one_left z := by simp }⟩

end ContinuousMap

namespace TauCeti

/-- **Reconciliation of the continuous mapping degree on `S¹` with `Circle.degree`.** For every
orientation `o` of `Circle` and every continuous map `f : C(Circle, Circle)`, the smooth-manifold
continuous mapping degree `TauCeti.continuousDegree o o f` equals the covering-space winding number
`Circle.degree f.toBasedLoop`. -/
theorem continuousDegree_circle_eq_circleDegree (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : C(Circle, Circle)) :
    continuousDegree o o f = Circle.degree f.toBasedLoop :=
  (continuousDegree_eq_of_homotopic o o f.homotopic_zpow).trans
    (continuousDegree_zpow_id_circle o _)

/-- **Reconciliation on based loops.** Reading a loop `γ : Path x x` in `Circle` as a map
`γ.toCircle : C(Circle, Circle)` gives a continuous mapping degree equal to `Circle.degree γ`. -/
@[simp]
theorem continuousDegree_toCircle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {x : Circle}
    (γ : Path x x) :
    continuousDegree o o γ.toCircle = Circle.degree γ := by
  rw [continuousDegree_circle_eq_circleDegree]
  exact Circle.degree_congr _ _ fun t ↦ by
    rw [ContinuousMap.toBasedLoop_apply, γ.toCircle_unitToCircle]

/-- **Reconciliation of the smooth mapping degree on `S¹` with `Circle.degree`.** For every smooth
map `f : Circle → Circle` and every orientation `o` of `Circle`, `TauCeti.degree o o f` equals
`Circle.degree` of its loop `t ↦ f(e^{2π i t})`. -/
theorem degree_circle_eq_circleDegree (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) :
    degree o o f = Circle.degree (⟨f, hf.continuous⟩ : C(Circle, Circle)).toBasedLoop :=
  (continuousDegree_eq_degree o o (f := ⟨f, hf.continuous⟩) hf).symm.trans
    (continuousDegree_circle_eq_circleDegree o _)

/-- **Hopf's degree theorem in dimension `1`.** Two continuous maps `f, g : C(Circle, Circle)` are
homotopic if and only if they have the same mapping degree. -/
theorem homotopic_circle_iff_continuousDegree_eq (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f g : C(Circle, Circle)} :
    f.Homotopic g ↔ continuousDegree o o f = continuousDegree o o g := by
  refine ⟨continuousDegree_eq_of_homotopic o o, fun h ↦ ?_⟩
  rw [continuousDegree_circle_eq_circleDegree, continuousDegree_circle_eq_circleDegree] at h
  exact f.homotopic_zpow.trans (h ▸ g.homotopic_zpow.symm)

end TauCeti

namespace ContinuousMap

/-- Two continuous maps `f, g : C(Circle, Circle)` are homotopic if and only if their loops
`f.toBasedLoop` and `g.toBasedLoop` have the same `Circle.degree`. -/
theorem homotopic_iff_degree_toBasedLoop_eq {f g : C(Circle, Circle)} :
    f.Homotopic g ↔ Circle.degree f.toBasedLoop = Circle.degree g.toBasedLoop := by
  rw [TauCeti.homotopic_circle_iff_continuousDegree_eq TauCeti.circleOrientation,
    TauCeti.continuousDegree_circle_eq_circleDegree,
    TauCeti.continuousDegree_circle_eq_circleDegree]

end ContinuousMap

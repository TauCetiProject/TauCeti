/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import TauCeti.Geometry.Manifold.DeRham.Circle
public import TauCeti.Geometry.Manifold.Degree.Continuous
public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Topology.Circle.Degree
public import TauCeti.Topology.Circle.Loop
-- Private: free-loop classification, smooth integer powers on Lie groups, global degree
-- integration, connectedness of spheres, and the homotopy/path bridge are used only inside proofs.
import TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic
import TauCeti.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Topology.Homotopy.Homotopic.With

/-!
# The mapping degree on the circle and reconciliation with `Circle.degree`

On the unit circle `S¹ = Circle` of `ℂ`, the angular `1`-form `dθ` (`TauCeti.circleAngularForm`) is
nowhere vanishing, integrates to `2π` over the counterclockwise orientation
`TauCeti.circleOrientation` (`TauCeti.integralTopForm_circleOrientation_circleAngularForm`), and
selects the same orientation as the outward-normal orientation
`Complex.orientation.sphereOrientation` of `S¹ ⊆ ℂ`
(`TauCeti.circleOrientation_eq_sphereOrientation`).

Combining the pullback calculus of `dθ` in `TauCeti.Geometry.Manifold.DeRham.Circle` with the
top-form degree formula `∫_M f^* dθ = deg(f) · 2π`
(`TauCeti.integralTopForm_mpullback_circleAngularForm`, for any compact Hausdorff boundaryless
oriented smooth `1`-manifold `M`) and the top-form orientation criteria gives the smooth and
continuous degree calculus for `Circle`-valued maps and self-maps of `S¹`:

* pointwise `1`, multiplication, inversion, division, negation, and natural/integer powers of smooth
  maps `M → Circle` and continuous maps `C(M, Circle)` act on the mapping degree as `0`, addition,
  negation, subtraction, the identity, and scalar multiplication (`TauCeti.degree_one_circle`,
  `TauCeti.degree_mul_circle`, `TauCeti.degree_inv_circle`, `TauCeti.degree_div_circle`,
  `TauCeti.degree_neg_circle`, `TauCeti.degree_pow_circle`, `TauCeti.degree_zpow_circle`, and their
  `TauCeti.continuousDegree_*_circle` counterparts);
* on `Circle` itself, `z ↦ z ^ k` (`k : ℤ`) preserves orientation when `0 < k`, reverses orientation
  when `k < 0`, has every point of `S¹` as a regular value when `k ≠ 0`, and has smooth and
  continuous mapping degree `k` (`TauCeti.degree_zpow_id_circle`,
  `TauCeti.continuousDegree_zpow_id_circle`);
* inversion `z ↦ z⁻¹` on `Circle` and complex conjugation `TauCeti.conjSphere` on
  `sphere (0 : ℂ) 1` have degree `-1`, while negation `z ↦ -z` and rotations `z₀ * ·`, `· * z₀`
  have degree `1` (`TauCeti.degree_inv_id_circle`, `TauCeti.continuousDegree_inv_id_circle`,
  `TauCeti.degree_neg_id_circle`, `TauCeti.continuousDegree_neg_id_circle`,
  `TauCeti.continuousDegree_conjSphere`).

Finally, combining path-component invariance (`TauCeti.continuousDegree_eq_of_joined`) with the
covering-space classification of free loops on `S¹` (`Circle.joined_iff_circleDegree_eq` in
`TauCeti.AlgebraicTopology.UniversalCover.Circle.FreeLoop.Basic`) reconciles the
differential-geometric mapping degree with the winding number `Circle.degree`:

* `TauCeti.continuousDegree_eq_circleDegree_toBasedLoop`:
  `continuousDegree o o f = Circle.degree f.toBasedLoop` for every orientation `o` of `S¹`;
* `TauCeti.continuousDegree_toCircle`: `continuousDegree o o γ.toCircle = Circle.degree γ` for
  every loop `γ` in `S¹`;
* `TauCeti.degree_eq_circleDegree_toBasedLoop`: `degree o o f` agrees with `Circle.degree` on
  smooth maps `S¹ → S¹`;
* `TauCeti.homotopic_circle_iff_continuousDegree_eq`: two maps in `C(Circle, Circle)` are homotopic
  if and only if they have the same mapping degree (Hopf's degree theorem in dimension `1`).

## Main results

* `TauCeti.circleOrientation_eq_sphereOrientation`: `circleOrientation` equals
  `Complex.orientation.sphereOrientation`.
* `TauCeti.degree_eq_degree_circleOrientation`,
  `TauCeti.continuousDegree_eq_continuousDegree_circleOrientation`: self-map degrees on `Circle` are
  independent of the choice of orientation.
* `TauCeti.integralTopForm_mpullback_circleAngularForm`: `∫_M f^* dθ = deg(f) · 2π`.
* `TauCeti.degree_one_circle`, `TauCeti.degree_mul_circle`, `TauCeti.degree_inv_circle`,
  `TauCeti.degree_div_circle`, `TauCeti.degree_neg_circle`, `TauCeti.degree_pow_circle`,
  `TauCeti.degree_zpow_circle`: smooth degree calculus for maps `M → Circle`.
* `TauCeti.degree_zpow_id_circle`, `TauCeti.degree_pow_id_circle`, `TauCeti.degree_inv_id_circle`,
  `TauCeti.degree_neg_id_circle`, `TauCeti.degree_mul_left_circle`,
  `TauCeti.degree_mul_right_circle`: smooth degrees of standard self-maps of `Circle`.
* `TauCeti.isOrientationPreservingAt_zpow_circle`, `TauCeti.isOrientationReversingAt_zpow_circle`,
  `TauCeti.isRegularValue_zpow_circle`, `TauCeti.degreeAtRegularValue_zpow_circle`: local and
  regular-value calculus of `z ↦ z ^ k`.
* `TauCeti.continuousDegree_one_circle`, `TauCeti.continuousDegree_mul_circle`,
  `TauCeti.continuousDegree_inv_circle`, `TauCeti.continuousDegree_div_circle`,
  `TauCeti.continuousDegree_neg_circle`, `TauCeti.continuousDegree_pow_circle`,
  `TauCeti.continuousDegree_zpow_circle`: continuous degree calculus for maps `C(M, Circle)`.
* `TauCeti.continuousDegree_zpow_id_circle`, `TauCeti.continuousDegree_pow_id_circle`,
  `TauCeti.continuousDegree_inv_id_circle`, `TauCeti.continuousDegree_neg_id_circle`,
  `TauCeti.continuousDegree_conjSphere`: continuous degrees of standard self-maps of `Circle`.
* `TauCeti.continuousDegree_eq_circleDegree_toBasedLoop`, `TauCeti.continuousDegree_toCircle`,
  `TauCeti.degree_eq_circleDegree_toBasedLoop`, `TauCeti.homotopic_circle_iff_continuousDegree_eq`:
  reconciliation with `Circle.degree` and homotopy classification of maps `S¹ → S¹`.

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

/-! ### Orientation of the circle -/

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

/-- For a self-map `f : Circle → Circle`, `degree o o f` is the same for both orientations `o` of
`Circle`. -/
theorem degree_eq_degree_circleOrientation (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (f : Circle → Circle) :
    degree o o f = degree circleOrientation circleOrientation f := by
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · rfl
  · rw [degree_neg_left, degree_neg_right, neg_neg]

/-- For a continuous self-map `f : C(Circle, Circle)`, `continuousDegree o o f` is the same for
both orientations `o` of `Circle`. -/
theorem continuousDegree_eq_continuousDegree_circleOrientation
    (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(Circle, Circle)) :
    continuousDegree o o f = continuousDegree circleOrientation circleOrientation f := by
  rcases o.eq_or_eq_neg circleOrientation with rfl | rfl
  · rfl
  · rw [continuousDegree_neg_left, continuousDegree_neg_right, neg_neg]

/-! ### Smooth degree calculus for maps into `Circle` -/

section CircleValuedSmooth

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- **Integral formula for the mapping degree into `S¹`.** For every smooth map `f : M → Circle`
from a compact Hausdorff boundaryless oriented `1`-manifold `M`, the integral of `f^* dθ` over `M`
is `deg(f) · 2π` (with respect to `circleOrientation` on the target). -/
theorem integralTopForm_mpullback_circleAngularForm (o : Manifold.Orientation I M (Fin 1))
    {f : M → Circle} (hf : ContMDiff I (𝓡 1) ∞ f) :
    integralTopForm o (mpullback I (𝓡 1) f circleAngularForm) =
      degree o circleOrientation f * (2 * Real.pi) := by
  rw [integralTopForm_mpullback_eq_degree_mul o circleOrientation hf hf.continuous.isProperMap
      isSmoothForm_circleAngularForm (isClosed_tsupport _).isCompact,
    integralTopForm_circleOrientation_circleAngularForm]

omit [BoundarylessManifold I M] [T2Space M] [CompactSpace M] in
/-- The constant map `1 : M → Circle` has smooth mapping degree `0`. -/
@[simp]
theorem degree_one_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    degree o o' (1 : M → Circle) = 0 :=
  degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))) (1 : Circle)

/-- **Pointwise multiplication of smooth maps `M → Circle` adds their degrees.** -/
@[to_fun degree_fun_mul_circle]
theorem degree_mul_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f g : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) (hg : ContMDiff I (𝓡 1) ∞ g) :
    degree o o' (f * g) = degree o o' f + degree o o' g := by
  suffices hstd : degree o circleOrientation (f * g) =
      degree o circleOrientation f + degree o circleOrientation g by
    rcases o'.eq_or_eq_neg circleOrientation with rfl | rfl
    · exact hstd
    · simp only [degree_neg_right, hstd, neg_add]
  have hfg := integralTopForm_mpullback_circleAngularForm o (f := f * g) (hf.mul hg)
  have hf_int := integralTopForm_mpullback_circleAngularForm o hf
  have hg_int := integralTopForm_mpullback_circleAngularForm o hg
  have hadd : integralTopForm o (mpullback I (𝓡 1) (f * g) circleAngularForm) =
      integralTopForm o (mpullback I (𝓡 1) f circleAngularForm) +
        integralTopForm o (mpullback I (𝓡 1) g circleAngularForm) := by
    rw [mpullback_mul_circleAngularForm (hf.mdifferentiable (by simp))
      (hg.mdifferentiable (by simp))]
    exact integralTopForm_add_of_compactSpace o
      ((isSmoothForm_circleAngularForm.mpullback hf).of_le zero_le)
      ((isSmoothForm_circleAngularForm.mpullback hg).of_le zero_le)
  rw [hfg, hf_int, hg_int, ← add_mul, ← Int.cast_add] at hadd
  exact_mod_cast mul_right_cancel₀ Real.two_pi_pos.ne' hadd

/-- Pointwise inversion of a smooth map `f : M → Circle` negates its degree. -/
@[to_fun degree_fun_inv_circle]
theorem degree_inv_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) :
    degree o o' f⁻¹ = -degree o o' f := by
  have hinv : ContMDiff I (𝓡 1) ∞ f⁻¹ := hf.inv
  have h := degree_mul_circle o o' hf hinv
  rw [mul_inv_cancel, degree_one_circle] at h
  omega

/-- Pointwise division of smooth maps `M → Circle` subtracts their degrees. -/
@[to_fun degree_fun_div_circle]
theorem degree_div_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f g : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) (hg : ContMDiff I (𝓡 1) ∞ g) :
    degree o o' (f / g) = degree o o' f - degree o o' g := by
  have hinv : ContMDiff I (𝓡 1) ∞ g⁻¹ := hg.inv
  rw [div_eq_mul_inv, degree_mul_circle o o' hf hinv, degree_inv_circle o o' hg, sub_eq_add_neg]

/-- Pointwise negation of a smooth map `f : M → Circle` preserves its degree. -/
@[to_fun degree_fun_neg_circle]
theorem degree_neg_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) :
    degree o o' (-f) = degree o o' f := by
  have hneg : -f = (fun _ : M ↦ (-1 : Circle)) * f := funext fun y ↦ (neg_one_mul (f y)).symm
  rw [hneg, degree_mul_circle o o' contMDiff_const hf,
    degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))), zero_add]

/-- Raising a smooth map `f : M → Circle` pointwise to the `n`-th natural power multiplies its
degree by `n`. -/
@[to_fun degree_fun_pow_circle]
theorem degree_pow_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) (n : ℕ) :
    degree o o' (f ^ n) = n * degree o o' f := by
  induction n with
  | zero =>
    simp [pow_zero]
  | succ n ih =>
    have hpow : ContMDiff I (𝓡 1) ∞ (f ^ n) := hf.pow n
    rw [pow_succ, degree_mul_circle o o' hpow hf, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Raising a smooth map `f : M → Circle` pointwise to the `k`-th integer power multiplies its
degree by `k`. -/
@[to_fun degree_fun_zpow_circle]
theorem degree_zpow_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {f : M → Circle}
    (hf : ContMDiff I (𝓡 1) ∞ f) (k : ℤ) :
    degree o o' (f ^ k) = k * degree o o' f := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast] using degree_pow_circle o o' hf n
  · have hpow : ContMDiff I (𝓡 1) ∞ (f ^ n) := hf.pow n
    rw [zpow_neg, zpow_natCast, degree_inv_circle o o' hpow, degree_pow_circle o o' hf n, neg_mul]

end CircleValuedSmooth

/-! ### Standard self-maps of `Circle`: smooth degrees and local orientation signs -/

/-- **Degree of integer power maps on `S¹`.** For every orientation `o` of `Circle` and every
`k : ℤ`, the map `z ↦ z ^ k` has smooth mapping degree `k`. -/
@[simp]
theorem degree_zpow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (k : ℤ) :
    degree o o (fun z : Circle ↦ z ^ k) = k := by
  simpa only [id_eq, degree_id, mul_one] using degree_fun_zpow_circle o o contMDiff_id k

/-- **Degree of natural power maps on `S¹`.** For every orientation `o` of `Circle` and every
`n : ℕ`, the map `z ↦ z ^ n` has smooth mapping degree `n`. -/
@[simp]
theorem degree_pow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (n : ℕ) :
    degree o o (fun z : Circle ↦ z ^ n) = n := by
  simpa only [zpow_natCast] using degree_zpow_id_circle o (n : ℤ)

/-- **Degree of inversion on `S¹`.** Inversion `z ↦ z⁻¹` (which equals complex conjugation
`z ↦ conj z` on `Circle`) has smooth mapping degree `-1`. -/
@[simp]
theorem degree_inv_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    degree o o (·⁻¹ : Circle → Circle) = -1 := by
  simpa only [zpow_neg, zpow_one] using degree_zpow_id_circle o (-1)

/-- **Degree of negation on `S¹`.** Negation `z ↦ -z` on `Circle` (rotation by `π`) has smooth
mapping degree `1`. -/
@[simp]
theorem degree_neg_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    degree o o (fun z : Circle ↦ -z) = 1 := by
  simpa only [id_eq, degree_id] using degree_fun_neg_circle o o contMDiff_id

/-- Left rotation `z ↦ z₀ * z` on `Circle` has smooth mapping degree `1`. -/
@[simp]
theorem degree_mul_left_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (z₀ : Circle) :
    degree o o (z₀ * ·) = 1 := by
  have h := degree_fun_mul_circle o o (contMDiff_const (c := z₀)) contMDiff_id
  simpa [degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)))] using h

/-- Right rotation `z ↦ z * z₀` on `Circle` has smooth mapping degree `1`. -/
@[simp]
theorem degree_mul_right_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (z₀ : Circle) :
    degree o o (· * z₀) = 1 := by
  have h := degree_fun_mul_circle o o contMDiff_id (contMDiff_const (c := z₀))
  simpa [degree_const (by simp : 0 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)))] using h

/-- For `0 < k`, the integer power map `z ↦ z ^ k` preserves every orientation `o` of `Circle` at
every point `z`. -/
theorem isOrientationPreservingAt_zpow_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {k : ℤ} (hk : 0 < k) (z : Circle) :
    Manifold.Orientation.IsOrientationPreservingAt o o (fun w : Circle ↦ w ^ k) z := by
  have hcir : Manifold.Orientation.IsOrientationPreservingAt circleOrientation circleOrientation
      (fun w : Circle ↦ w ^ k) z := by
    rw [circleOrientation_def]
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
    rw [circleOrientation_def]
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
  have hf : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle ↦ z ^ k) := contMDiff_zpow k
  rw [← degree_eq_degreeAtRegularValue o o hf hf.continuous.isProperMap
      (isRegularValue_zpow_circle hk y),
    degree_zpow_id_circle]

/-- Inversion `z ↦ z⁻¹` on `Circle` has signed fibre count `-1` at every point. -/
@[simp]
theorem degreeAtRegularValue_inv_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    (y : Circle) :
    degreeAtRegularValue o o (·⁻¹ : Circle → Circle) y = -1 := by
  simpa only [zpow_neg, zpow_one] using
    degreeAtRegularValue_zpow_circle o (by decide : (-1 : ℤ) ≠ 0) y

/-! ### Continuous degree calculus for maps into `Circle` -/

section CircleValuedContinuous

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

/-- The constant map `1 : C(M, Circle)` has continuous degree `0`. -/
@[simp]
theorem continuousDegree_one_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) :
    continuousDegree o o' (1 : C(M, Circle)) = 0 := by
  rw [← ContinuousMap.const_one]
  exact continuousDegree_const o o' 1

/-- **Pointwise multiplication in `C(M, Circle)` adds continuous degrees.** -/
@[simp]
theorem continuousDegree_mul_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f g : C(M, Circle)) :
    continuousDegree o o' (f * g) = continuousDegree o o' f + continuousDegree o o' g := by
  obtain ⟨f₀, hf₀, hff₀, hdf⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o o' f
  obtain ⟨g₀, hg₀, hgg₀, hdg⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o o' g
  have hmul : (f * g).Homotopic (f₀ * g₀) := by
    obtain ⟨Hf⟩ := hff₀
    obtain ⟨Hg⟩ := hgg₀
    exact ⟨{
      toFun p := Hf p * Hg p
      continuous_toFun := Hf.continuous.mul Hg.continuous
      map_zero_left z := by simp
      map_one_left z := by simp }⟩
  rw [hdf, hdg, continuousDegree_eq_degree_of_homotopic o o' (hf₀.mul hg₀) hmul]
  exact degree_mul_circle o o' hf₀ hg₀

/-- **Pointwise inversion in `C(M, Circle)` negates the continuous degree.** -/
@[simp]
theorem continuousDegree_inv_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(M, Circle)) :
    continuousDegree o o' f⁻¹ = -continuousDegree o o' f := by
  have h := continuousDegree_mul_circle o o' f f⁻¹
  rw [mul_inv_cancel, continuousDegree_one_circle] at h
  omega

/-- Pointwise division in `C(M, Circle)` subtracts continuous degrees. -/
@[simp]
theorem continuousDegree_div_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f g : C(M, Circle)) :
    continuousDegree o o' (f / g) = continuousDegree o o' f - continuousDegree o o' g := by
  rw [div_eq_mul_inv, continuousDegree_mul_circle, continuousDegree_inv_circle, sub_eq_add_neg]

/-- Pointwise negation in `C(M, Circle)` preserves the continuous degree. -/
@[simp]
theorem continuousDegree_neg_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(M, Circle)) :
    continuousDegree o o' (-f) = continuousDegree o o' f := by
  have hneg : -f = ContinuousMap.const M (-1 : Circle) * f :=
    ContinuousMap.ext fun y ↦ (neg_one_mul (f y)).symm
  rw [hneg, continuousDegree_mul_circle, continuousDegree_const, zero_add]

/-- Raising `f : C(M, Circle)` to the `n`-th natural power multiplies its continuous degree by `n`.
-/
@[simp]
theorem continuousDegree_pow_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(M, Circle)) (n : ℕ) :
    continuousDegree o o' (f ^ n) = n * continuousDegree o o' f := by
  induction n with
  | zero =>
    simp [pow_zero]
  | succ n ih =>
    rw [pow_succ, continuousDegree_mul_circle, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

/-- Raising `f : C(M, Circle)` to the `k`-th integer power multiplies its continuous degree by `k`.
-/
@[simp]
theorem continuousDegree_zpow_circle (o : Manifold.Orientation I M (Fin 1))
    (o' : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(M, Circle)) (k : ℤ) :
    continuousDegree o o' (f ^ k) = k * continuousDegree o o' f := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [zpow_natCast] using continuousDegree_pow_circle o o' f n
  · rw [zpow_neg, zpow_natCast, continuousDegree_inv_circle, continuousDegree_pow_circle, neg_mul]

end CircleValuedContinuous

/-! ### Standard continuous self-maps of `Circle` and reconciliation with `Circle.degree` -/

/-- **Continuous degree of integer power maps on `S¹`.** -/
@[simp]
theorem continuousDegree_zpow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (k : ℤ)
    {hc : Continuous fun z : Circle ↦ z ^ k} :
    continuousDegree o o ⟨(· ^ k), hc⟩ = k :=
  (continuousDegree_eq_degree o o (f := ⟨(· ^ k), hc⟩) (contMDiff_zpow k)).trans
    (degree_zpow_id_circle o k)

/-- **Continuous degree of natural power maps on `S¹`.** -/
@[simp]
theorem continuousDegree_pow_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (n : ℕ)
    {hc : Continuous fun z : Circle ↦ z ^ n} :
    continuousDegree o o ⟨(· ^ n), hc⟩ = n := by
  simpa only [zpow_natCast] using continuousDegree_zpow_id_circle o (n : ℤ) (hc := hc)

/-- **Continuous degree of inversion on `S¹`.** -/
@[simp]
theorem continuousDegree_inv_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {hc : Continuous (·⁻¹ : Circle → Circle)} :
    continuousDegree o o ⟨(·⁻¹), hc⟩ = -1 :=
  (continuousDegree_eq_degree o o (f := ⟨(·⁻¹), hc⟩) (contMDiff_inv (𝓡 1) ∞)).trans
    (degree_inv_id_circle o)

/-- **Continuous degree of negation on `S¹`.** -/
@[simp]
theorem continuousDegree_neg_id_circle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {hc : Continuous fun z : Circle ↦ -z} :
    continuousDegree o o ⟨(-·), hc⟩ = 1 :=
  (continuousDegree_eq_degree o o (f := ⟨(-·), hc⟩) contMDiff_neg_sphere).trans
    (degree_neg_id_circle o)

/-- **Continuous degree of complex conjugation on `S¹`.** -/
@[simp]
theorem continuousDegree_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) {hc : Continuous conjSphere} :
    continuousDegree o o ⟨conjSphere, hc⟩ = -1 := by
  have := connectedSpace_sphere (E := ℂ) 1
  exact (continuousDegree_eq_degree o o (f := ⟨conjSphere, hc⟩) contMDiff_conjSphere).trans
    (degree_conjSphere o)

/-- **Reconciliation of the continuous mapping degree on `S¹` with `Circle.degree`.** For every
orientation `o` of `Circle` and every continuous map `f : C(Circle, Circle)`, the smooth-manifold
continuous mapping degree `TauCeti.continuousDegree o o f` equals the covering-space winding number
`Circle.degree f.toBasedLoop`. -/
theorem continuousDegree_eq_circleDegree_toBasedLoop
    (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) (f : C(Circle, Circle)) :
    continuousDegree o o f = Circle.degree f.toBasedLoop := by
  rw [Circle.degree_toBasedLoop]
  exact (continuousDegree_eq_of_joined o o <|
    Circle.joined_iff_circleDegree_eq.2 (ContinuousMap.circleDegree_zpow _).symm).trans
    (continuousDegree_zpow_id_circle o _)

/-- **Reconciliation on based loops.** Reading a loop `γ : Path x x` in `Circle` as a map
`γ.toCircle : C(Circle, Circle)` gives a continuous mapping degree equal to `Circle.degree γ`. -/
@[simp]
theorem continuousDegree_toCircle (o : Manifold.Orientation (𝓡 1) Circle (Fin 1)) {x : Circle}
    (γ : Path x x) :
    continuousDegree o o γ.toCircle = Circle.degree γ := by
  rw [continuousDegree_eq_circleDegree_toBasedLoop, Circle.degree_toBasedLoop,
    ContinuousMap.circleDegree_toCircle]

/-- **Reconciliation of the smooth mapping degree on `S¹` with `Circle.degree`.** For every smooth
map `f : Circle → Circle` and every orientation `o` of `Circle`, `TauCeti.degree o o f` equals
`Circle.degree` of its loop `t ↦ f(e^{2π i t})`. -/
theorem degree_eq_circleDegree_toBasedLoop (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f : Circle → Circle} (hf : ContMDiff (𝓡 1) (𝓡 1) ∞ f) :
    degree o o f = Circle.degree (⟨f, hf.continuous⟩ : C(Circle, Circle)).toBasedLoop :=
  (continuousDegree_eq_degree o o (f := ⟨f, hf.continuous⟩) hf).symm.trans
    (continuousDegree_eq_circleDegree_toBasedLoop o _)

/-- **Hopf's degree theorem in dimension `1`.** Two continuous maps `f, g : C(Circle, Circle)` are
homotopic if and only if they have the same mapping degree. -/
theorem homotopic_circle_iff_continuousDegree_eq (o : Manifold.Orientation (𝓡 1) Circle (Fin 1))
    {f g : C(Circle, Circle)} :
    f.Homotopic g ↔ continuousDegree o o f = continuousDegree o o g := by
  rw [ContinuousMap.homotopic_iff_joined, Circle.joined_iff_circleDegree_eq,
    continuousDegree_eq_circleDegree_toBasedLoop, continuousDegree_eq_circleDegree_toBasedLoop,
    Circle.degree_toBasedLoop, Circle.degree_toBasedLoop]

end TauCeti

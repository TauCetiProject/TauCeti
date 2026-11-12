/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.Analysis.InnerProductSpace.Sphere.Stereographic

/-!
# The area of the two-sphere

Let `E` be an oriented real inner product space of dimension three. The volume form
`vol(u, ·, ·)` of its unit sphere `S²` (`Orientation.sphereVolumeForm`) is a symplectic form. This
file proves that its total area is `4π`: the measure `|vol|` of the volume form, which is also its
Liouville measure, gives `S²` measure `4π`
(`Orientation.measure_sphereVolumeForm_univ`, `Orientation.liouvilleMeasure_sphereVolumeForm_univ`).

The computation transports the area form to the Riemann sphere `OnePoint ℂ` along the inverse
stereographic projection `Φ = OnePoint.diffeomorphSphere v ι` from a point `v`. The round metric
pulls back to `4π` times the Fubini–Study metric (`OnePoint.inner_mfderiv_diffeomorphSphere`). On a
surface the area of a parallelogram is determined by the metric: for tangent vectors `a`, `b` at a
point `u` of the sphere, `|vol(u, a, b)| = √(|a|² |b|² - ⟪a, b⟫²)`, as `u` is a unit normal
(`Orientation.abs_volumeForm_cons_eq_sqrt_det_gram`). With Lagrange's identity
`|a|² |b|² - (Re (conj a * b))² = (Im (conj a * b))²` this gives

`|Φ^* vol| = 4π |ω_FS|`

pointwise (`Orientation.abs_mpullback_diffeomorphSphere_sphereVolumeForm_apply`), where `ω_FS` is
the Fubini–Study form, normalized to total area one (`OnePoint.measure_fubiniStudyForm_univ`). No
orientation of the Riemann sphere is compared: the measure of a top form only depends on its
absolute value.

For the unit sphere of `ℝ³`, the area form `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`)
rescaled by `r` has area `4π |r|` (`TauCeti.liouvilleMeasure_smul_sphereAreaForm_univ`). By
`TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`, on the infinitesimal rotations, which span
every tangent plane, `r σ` is the Kirillov–Kostant–Souriau form of the coadjoint orbit of `SO(3)` of
radius `r`, carried to `S²` along `x ↦ r x`. So this is the KKS area `4π r` of that orbit.

## Main results

* `Orientation.abs_mpullback_diffeomorphSphere_sphereVolumeForm_apply`: the volume form of `S²`
  pulls back to the Riemann sphere with absolute value `4π |ω_FS|`.
* `Orientation.measure_sphereVolumeForm_univ`: the volume form of `S²` has total measure `4π`.
* `Orientation.liouvilleMeasure_sphereVolumeForm_univ`: the Liouville measure of `S²` is `4π`.
* `TauCeti.liouvilleMeasure_smul_sphereAreaForm_univ`: the area form of the unit sphere of `ℝ³`
  scaled by `r` has Liouville measure `4π |r|`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2 (the coadjoint orbits of `SO(3)`).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (stereographic coordinates on the round sphere).
-/

public section

noncomputable section

open Metric Module Set MeasureTheory ComplexConjugate
open scoped Manifold InnerProductSpace TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- **The volume form of `S²` on the Riemann sphere.** Along the inverse stereographic projection
`Φ = OnePoint.diffeomorphSphere v ι`, the volume form of the unit sphere pulls back to a form with
the absolute values of `4π ω_FS`, where `ω_FS` is the Fubini–Study form. -/
theorem _root_.Orientation.abs_mpullback_diffeomorphSphere_sphereVolumeForm_apply
    (o : Orientation ℝ E (Fin (2 + 1))) (v : sphere (0 : E) 1) (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ)
    (x : OnePoint ℂ) (u : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) x) :
    |mpullback 𝓘(ℝ, ℂ) (𝓡 2) (OnePoint.diffeomorphSphere v ι) o.sphereVolumeForm.1 x u| =
      |4 * Real.pi * OnePoint.fubiniStudyForm.1 x u| := by
  -- The round metric pulls back to `4π` times the Fubini–Study metric.
  have hinner (p q : ℂ) :
      ⟪mvfderiv (𝓡 2) ((↑) : sphere (0 : E) 1 → E) (OnePoint.diffeomorphSphere v ι x)
          (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (OnePoint.diffeomorphSphere v ι) x p),
        mvfderiv (𝓡 2) ((↑) : sphere (0 : E) 1 → E) (OnePoint.diffeomorphSphere v ι x)
          (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (OnePoint.diffeomorphSphere v ι) x q)⟫_ℝ =
        4 * Real.pi * OnePoint.fubiniStudyDensity (chartAt ℂ x x) * (conj p * q).re := by
    rw [← inner_tangentSpace_sphere, OnePoint.inner_mfderiv_diffeomorphSphere,
      OnePoint.eval₂_fubiniStudyForm_I_mul]
    ring
  have hω : OnePoint.fubiniStudyForm.1 x u =
      SmoothBundleForm.eval₂ OnePoint.fubiniStudyForm x (u 0) (u 1) :=
    ((SmoothBundleForm.eval₂_apply _ _ _ _).trans
      (congrArg _ (funext fun i ↦ by fin_cases i <;> rfl))).symm
  -- The point is a unit normal to the tangent vectors, so only their Gram determinant remains.
  rw [mpullback_apply, Orientation.sphereVolumeForm_apply,
    o.abs_volumeForm_cons_eq_sqrt_det_gram (norm_eq_of_mem_sphere _)
      fun i ↦ inner_coe_mvfderiv_subtypeVal_sphere _ _, Matrix.det_fin_two, hω]
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℂ, u = ![a, b] :=
    ⟨u 0, u 1, funext fun i ↦ by fin_cases i <;> rfl⟩
  simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hinner,
    OnePoint.eval₂_fubiniStudyForm]
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  -- Lagrange's identity `|a|² |b|² - (Re (conj a * b))² = (Im (conj a * b))²`.
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

section Measure

variable [MeasurableSpace E] [BorelSpace E]

attribute [local instance] finrank_euclideanSpace_fin_succ_fact Complex.finrank_real_complex_fact

/-- A space of dimension `2 + 1` is finite dimensional, so its unit sphere is compact. -/
local instance finiteDimensional_of_finrank_eq_two_add_one : FiniteDimensional ℝ E :=
  .of_fact_finrank_eq_succ 2

/-- **The area of the two-sphere is `4π`.** The measure `|vol|` of the volume form of the unit
sphere of an oriented three-dimensional inner product space gives the whole sphere measure `4π`. -/
theorem _root_.Orientation.measure_sphereVolumeForm_univ (o : Orientation ℝ E (Fin (2 + 1))) :
    RoughForm.measure o.sphereVolumeForm.1 (univ : Set (sphere (0 : E) 1)) =
      ENNReal.ofReal (4 * Real.pi) := by
  -- Transport along inverse stereographic projection from a point `v` of the sphere.
  have : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [Fact.out (p := finrank ℝ E = 2 + 1)]; norm_num)
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have : Fact (finrank ℝ E = 3) := ⟨Fact.out (p := finrank ℝ E = 2 + 1)⟩
  set v : sphere (0 : E) 1 := ⟨‖w‖⁻¹ • w, by simp [norm_smul, hw]⟩
  set Φ := OnePoint.diffeomorphSphere v
    (complexIsometryOrthogonalSpanSingleton (ne_zero_of_mem_unit_sphere v))
  let _ : MeasurableSpace (OnePoint ℂ) := borel _
  have : BorelSpace (OnePoint ℂ) := ⟨rfl⟩
  have hΦ := Φ.toHomeomorph.measurePreserving_measure_mpullback (Φ.mdifferentiable (by simp))
    o.sphereVolumeForm.1
  have habs (x : OnePoint ℂ) (u : Fin 2 → TangentSpace 𝓘(ℝ, ℂ) x) :
      |mpullback 𝓘(ℝ, ℂ) (𝓡 2) Φ.toHomeomorph o.sphereVolumeForm.1 x u| =
        |((4 * Real.pi) • OnePoint.fubiniStudyForm.1) x u| :=
    o.abs_mpullback_diffeomorphSphere_sphereVolumeForm_apply v _ x u
  rw [← hΦ.map_eq, Measure.map_apply hΦ.measurable MeasurableSet.univ, preimage_univ,
    RoughForm.measure_eq_of_forall_abs_apply_eq habs, RoughForm.measure_smul, FunLike.coe_smul,
    Pi.smul_apply, OnePoint.measure_fubiniStudyForm_univ, smul_eq_mul, mul_one,
    abs_of_pos (by positivity)]

/-- **The Liouville measure of the two-sphere is `4π`.** The volume form of the unit sphere of an
oriented three-dimensional inner product space, regarded as a symplectic form, has total Liouville
measure `4π`. -/
theorem _root_.Orientation.liouvilleMeasure_sphereVolumeForm_univ
    (o : Orientation ℝ E (Fin (2 + 1))) :
    SmoothTwoForm.liouvilleMeasure 1 o.sphereVolumeForm (univ : Set (sphere (0 : E) 1)) =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [SmoothTwoForm.liouvilleMeasure_one]
  exact o.measure_sphereVolumeForm_univ

end Measure

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- **The KKS area of the coadjoint spheres of `SO(3)`.** The area form `σ` of the unit sphere of
`ℝ³`, rescaled by `r`, has total Liouville measure `4π |r|`. On the infinitesimal rotations, which
span every tangent plane, `r σ` is the Kirillov–Kostant–Souriau form of the coadjoint orbit of
`SO(3)` of radius `r`, carried to the unit sphere along `x ↦ r x`
(`TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`). So for `r > 0` that orbit has KKS area
`4π r`. -/
theorem liouvilleMeasure_smul_sphereAreaForm_univ (r : ℝ) :
    (r • sphereAreaForm).liouvilleMeasure 1
        (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      ENNReal.ofReal (4 * Real.pi * |r|) := by
  rw [SmoothTwoForm.liouvilleMeasure_one, Submodule.coe_smul, RoughForm.measure_smul,
    FunLike.coe_smul, Pi.smul_apply, sphereAreaForm_def, Orientation.measure_sphereVolumeForm_univ,
    smul_eq_mul, ← ENNReal.ofReal_mul (abs_nonneg r), mul_comm]

end TauCeti

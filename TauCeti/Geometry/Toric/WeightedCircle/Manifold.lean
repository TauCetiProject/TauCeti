/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.Fredholm.LevelSet.Inclusion
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Toric.WeightedCircle.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Fredholm.Basic

/-!
# The weighted ellipsoid as a smooth manifold, and its diffeomorphism with the three-sphere

Let `a` and `b` be natural numbers. The circle acts on `ℂ²` by the weighted rotations
`u • (z₁, z₂) = (u ^ a z₁, u ^ b z₂)` (`TauCeti.Toric.weightedRotation`), with moment map
`(a |z₁|² + b |z₂|²) / 2`, whose level `ε` is the ellipsoid

`E = {z ∈ ℂ² | a |z₁|² + b |z₂|² = 2 ε}` (`TauCeti.Toric.weightedEllipsoid a b ε`).

This file makes `E` a smooth manifold and identifies it, equivariantly, with the unit sphere
`S³ ⊆ ℂ²`.

* **The smooth structure.** The function `F(z) = a |z₁|² + b |z₂|²` is a homogeneous quadratic
  form, so its derivative at `z` sends `z` to `2 F(z)` (Euler's identity). On `E` this is
  `4 ε`, so for `ε ≠ 0` the derivative is a nonzero functional, hence surjective, at every point of
  `E`, and `2 ε` is a regular value of `F`. The implicit-function atlas of the regular level set
  (`TauCeti.levelSetChartedSpace`) therefore makes `E` a smooth, indeed analytic, manifold of
  dimension `4 - 1 = 3`, modelled on `Fin 3 → ℝ`
  (`TauCeti.Toric.weightedEllipsoidChartedSpace`, `TauCeti.Toric.isManifold_weightedEllipsoid`).
  No positivity of the weights is needed: for `a = 0` the level is the cylinder over a circle.
  For this atlas the inclusion of `E` into `ℂ²` is smooth
  (`TauCeti.Toric.contMDiff_coe_weightedEllipsoid`), a map into `E` is smooth as soon as it is
  smooth into `ℂ²` (`ContMDiff.codRestrict_weightedEllipsoid`), and in particular
  every element of the circle acts on `E` by a smooth map
  (`TauCeti.Toric.contMDiff_smul_weightedEllipsoid`).
* **The diffeomorphism with the sphere.** For positive weights and `ε > 0`, the diagonal scaling
  `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)` carries `E` onto the unit sphere `S³` of the
  Euclidean space `ℂ²`, with inverse `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. Both are
  restrictions of linear maps, so they are smooth for the atlas above and for Mathlib's
  stereographic atlas of the sphere (`EuclideanSpace.instChartedSpaceSphere`), and together they
  form a diffeomorphism `E ≃ S³` (`TauCeti.Toric.weightedEllipsoidDiffeomorphSphere`). The
  scaling commutes with the weighted rotations, so the diffeomorphism intertwines the action on
  `E` with the action `(w₁, w₂) ↦ (u ^ a w₁, u ^ b w₂)` on `S³`
  (`TauCeti.Toric.coe_weightedEllipsoidDiffeomorphSphere_smul`). For `a = b = 1` this is the Hopf
  action of the circle on the round sphere.

## Main definitions

* `TauCeti.Toric.weightedEllipsoidChartedSpace`: the implicit-function atlas of the ellipsoid,
  modelled on `Fin 3 → ℝ`.
* `TauCeti.Toric.weightedEllipsoidDiffeomorphSphere`: the equivariant diffeomorphism of the
  ellipsoid with the unit sphere `S³ ⊆ ℂ²`.

## Main results

* `TauCeti.Toric.isManifold_weightedEllipsoid`: the ellipsoid is a smooth manifold of dimension
  three.
* `TauCeti.Toric.contMDiff_coe_weightedEllipsoid`,
  `ContMDiff.codRestrict_weightedEllipsoid`: smooth maps out of and into the
  ellipsoid.
* `TauCeti.Toric.contMDiff_smul_weightedEllipsoid`: the circle acts by smooth maps.
* `TauCeti.Toric.coe_weightedEllipsoidDiffeomorphSphere_apply`,
  `TauCeti.Toric.coe_weightedEllipsoidDiffeomorphSphere_symm_apply`: the diffeomorphism and its
  inverse are the diagonal scalings.
* `TauCeti.Toric.coe_weightedEllipsoidDiffeomorphSphere_smul`: the diffeomorphism is equivariant.

## References

* Eugene Lerman and Susan Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric
  varieties*, Trans. Amer. Math. Soc. 349 (1997), 4201–4230, Section 1 (weighted projective
  spaces as quotients of the weighted ellipsoid).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Corollary 5.14
  (regular level sets are embedded submanifolds).
-/

public section

noncomputable section

open Set Manifold
open scoped ContDiff

namespace TauCeti.Toric

variable {a b : ℕ} {ε : ℝ}

/-! ### The ellipsoid as a regular level set -/

variable (a b) in
/-- The quadratic form `a |z₁|² + b |z₂|²`, twice the moment map of the weighted circle action.
The ellipsoid `weightedEllipsoid a b ε` is its level `2 ε`. -/
private def weightedNormSq (z : ℂ × ℂ) : ℝ :=
  a * ‖z.1‖ ^ 2 + b * ‖z.2‖ ^ 2

private theorem contDiff_weightedNormSq {m : ℕ∞ω} : ContDiff ℝ m (weightedNormSq a b) :=
  (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_fst)).add
    (contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd))

private theorem hasStrictFDerivAt_weightedNormSq (z : ℂ × ℂ) :
    HasStrictFDerivAt (weightedNormSq a b) (fderiv ℝ (weightedNormSq a b) z) z :=
  (contDiff_weightedNormSq (m := 1)).contDiffAt.hasStrictFDerivAt
    ((contDiff_weightedNormSq (m := 1)).differentiable one_ne_zero z).hasFDerivAt one_ne_zero

/-- Euler's identity for the homogeneous quadratic form: its derivative at `z` sends `z` to twice
its value. -/
private theorem fderiv_weightedNormSq_apply_self (z : ℂ × ℂ) :
    fderiv ℝ (weightedNormSq a b) z z = 2 * weightedNormSq a b z := by
  have h : HasFDerivAt (weightedNormSq a b)
      ((a : ℝ) • 2 • (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ ℂ ℂ) +
        (b : ℝ) • 2 • (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) z :=
    ((hasFDerivAt_fst.norm_sq).const_mul (a : ℝ)).add ((hasFDerivAt_snd.norm_sq).const_mul (b : ℝ))
  rw [h.fderiv]
  simp [weightedNormSq]
  ring

/-- At every point of a nonzero level of the quadratic form its derivative is surjective, since
it is a functional which does not vanish on the point itself. -/
private theorem surjective_fderiv_weightedNormSq (hε : ε ≠ 0) {z : ℂ × ℂ}
    (hz : z ∈ weightedEllipsoid a b ε) :
    Function.Surjective (fderiv ℝ (weightedNormSq a b) z) := by
  have hz' : fderiv ℝ (weightedNormSq a b) z z ≠ 0 := by
    rw [fderiv_weightedNormSq_apply_self, weightedNormSq, mem_weightedEllipsoid.1 hz]
    simpa using hε
  refine fun r ↦ ⟨(r / fderiv ℝ (weightedNormSq a b) z z) • z, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz']

/-- The derivative of the quadratic form on `ℂ²` has index `4 - 1 = 3`. -/
private theorem index_fderiv_weightedNormSq (z : ℂ × ℂ) :
    ContinuousLinearMap.index (𝕜 := ℝ) (fderiv ℝ (weightedNormSq a b) z) = (3 : ℕ) := by
  rw [ContinuousLinearMap.index_eq_of_finiteDimensional, Module.finrank_prod,
    Complex.finrank_real_complex, Module.finrank_self]
  norm_num

variable (a b) in
/-- The atlas of the ellipsoid `a |z₁|² + b |z₂|² = 2 ε`, for `ε ≠ 0`, by the implicit-function
charts of the regular level set `TauCeti.levelSetChartedSpace`. It is modelled on `Fin 3 → ℝ`. -/
@[instance_reducible]
def weightedEllipsoidChartedSpace (hε : ε ≠ 0) :
    ChartedSpace (Fin 3 → ℝ) (weightedEllipsoid a b ε) :=
  levelSetChartedSpace (f := weightedNormSq a b) (c := 2 * ε)
    (fun z _ ↦ hasStrictFDerivAt_weightedNormSq z)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun _ hz ↦ surjective_fderiv_weightedNormSq hε hz)
    (fun z _ ↦ index_fderiv_weightedNormSq z)

/-- **The ellipsoid is a smooth manifold** of dimension three, indeed a `C^m` manifold for every
`m`, including the analytic case `m = ω`, for the atlas
`TauCeti.Toric.weightedEllipsoidChartedSpace`. -/
theorem isManifold_weightedEllipsoid (hε : ε ≠ 0) (m : ℕ∞ω) :
    letI := weightedEllipsoidChartedSpace a b hε
    IsManifold 𝓘(ℝ, Fin 3 → ℝ) m (weightedEllipsoid a b ε) :=
  isManifold_levelSet _ _ _ _ fun _ _ ↦ contDiff_weightedNormSq.contDiffAt

/-- The inclusion of the ellipsoid into `ℂ²` is smooth for the atlas
`TauCeti.Toric.weightedEllipsoidChartedSpace`. -/
theorem contMDiff_coe_weightedEllipsoid (hε : ε ≠ 0) {m : ℕ∞ω} :
    letI := weightedEllipsoidChartedSpace a b hε
    ContMDiff 𝓘(ℝ, Fin 3 → ℝ) 𝓘(ℝ, ℂ × ℂ) m ((↑) : weightedEllipsoid a b ε → ℂ × ℂ) :=
  contMDiff_coe_levelSet _ _ _ _ fun _ _ ↦ contDiff_weightedNormSq.contDiffAt

section CodRestrict

variable {E' H : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E' H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {g : M → ℂ × ℂ} {m : ℕ∞ω}

/-- **Smooth maps into the ellipsoid.** For the atlas
`TauCeti.Toric.weightedEllipsoidChartedSpace`, a smooth map into `ℂ²` with values in the ellipsoid
is smooth as a map into the ellipsoid. -/
theorem _root_.ContMDiff.codRestrict_weightedEllipsoid (hε : ε ≠ 0)
    (hg : ContMDiff I 𝓘(ℝ, ℂ × ℂ) m g) (hg' : ∀ y, g y ∈ weightedEllipsoid a b ε) :
    letI := weightedEllipsoidChartedSpace a b hε
    ContMDiff I 𝓘(ℝ, Fin 3 → ℝ) m (codRestrict g (weightedEllipsoid a b ε) hg') :=
  ContMDiff.codRestrict_levelSet (f := weightedNormSq a b) (c := 2 * ε) _ _ _ _ hg hg'

end CodRestrict

/-- Each element of the circle acts on the ellipsoid by a smooth map, for the atlas
`TauCeti.Toric.weightedEllipsoidChartedSpace`. -/
theorem contMDiff_smul_weightedEllipsoid (hε : ε ≠ 0) (u : Circle) {m : ℕ∞ω} :
    letI := weightedEllipsoidChartedSpace a b hε
    ContMDiff 𝓘(ℝ, Fin 3 → ℝ) 𝓘(ℝ, Fin 3 → ℝ) m
      (fun z : weightedEllipsoid a b ε ↦ u • z) := by
  let := weightedEllipsoidChartedSpace a b hε
  have hrot_eq : weightedRotation a b u = fun z ↦ ((u : ℂ) ^ a * z.1, (u : ℂ) ^ b * z.2) :=
    funext fun z ↦ Prod.ext (weightedRotation_fst u z) (weightedRotation_snd u z)
  have hrot : ContDiff ℝ m (weightedRotation a b u) := by
    rw [hrot_eq]
    exact (contDiff_const.mul contDiff_fst).prodMk (contDiff_const.mul contDiff_snd)
  exact ContMDiff.codRestrict_weightedEllipsoid hε
    (hrot.comp_contMDiff (contMDiff_coe_weightedEllipsoid hε))
    fun z ↦ weightedRotation_mem_weightedEllipsoid_iff.2 z.2

/-! ### The diffeomorphism with the three-sphere -/

/-- The diagonal scaling `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)` from `ℂ²` to the
Euclidean space `ℂ²`, which carries the ellipsoid onto the unit sphere. -/
private def toSphereScaling (a b : ℕ) (ε : ℝ) (z : ℂ × ℂ) : EuclideanSpace ℂ (Fin 2) :=
  !₂[√(a / (2 * ε)) • z.1, √(b / (2 * ε)) • z.2]

/-- The diagonal scaling `(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)` from the Euclidean space
`ℂ²` to `ℂ²`, which carries the unit sphere onto the ellipsoid. -/
private def ofSphereScaling (a b : ℕ) (ε : ℝ) (w : EuclideanSpace ℂ (Fin 2)) : ℂ × ℂ :=
  (√(2 * ε / a) • w 0, √(2 * ε / b) • w 1)

private theorem contDiff_toSphereScaling {m : ℕ∞ω} : ContDiff ℝ m (toSphereScaling a b ε) := by
  refine contDiff_piLp' 2 fun i ↦ ?_
  fin_cases i
  · simp only [toSphereScaling, Fin.zero_eta, PiLp.toLp_apply, Matrix.cons_val_zero]
    exact contDiff_fst.const_smul _
  · simp only [toSphereScaling, Fin.mk_one, PiLp.toLp_apply, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact contDiff_snd.const_smul _

private theorem contDiff_ofSphereScaling {m : ℕ∞ω} : ContDiff ℝ m (ofSphereScaling a b ε) := by
  unfold ofSphereScaling
  exact ((contDiff_piLp_apply 2 (𝕜 := ℝ) (E := fun _ : Fin 2 ↦ ℂ) (i := 0)).const_smul _).prodMk
    ((contDiff_piLp_apply 2 (𝕜 := ℝ) (E := fun _ : Fin 2 ↦ ℂ) (i := 1)).const_smul _)

/-- The product of the two scaling factors of one coordinate is `1`. -/
private theorem sqrt_mul_sqrt_inv {c : ℕ} (hc : 0 < c) (hε : 0 < ε) :
    √(2 * ε / c) * √(c / (2 * ε)) = 1 := by
  rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (2 * ε),
    div_self (by positivity), Real.sqrt_one]

private theorem toSphereScaling_mem_sphere (hε : 0 < ε) (z : weightedEllipsoid a b ε) :
    toSphereScaling a b ε z ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
  have hz := mem_weightedEllipsoid.1 z.2
  have hsq : ‖toSphereScaling a b ε z‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp only [toSphereScaling, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (show (0 : ℝ) ≤ a / (2 * ε) by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ b / (2 * ε) by positivity)]
    field_simp
    linarith
  rw [mem_sphere_zero_iff_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [hsq, one_pow])

private theorem ofSphereScaling_mem_weightedEllipsoid (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (w : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    ofSphereScaling a b ε w ∈ weightedEllipsoid a b ε := by
  have hw : ‖(w : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 + ‖(w : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 =
      1 := by
    rw [← Fin.sum_univ_two (fun i ↦ ‖(w : EuclideanSpace ℂ (Fin 2)) i‖ ^ 2),
      ← EuclideanSpace.norm_sq_eq, norm_eq_of_mem_sphere w, one_pow]
  rw [mem_weightedEllipsoid]
  simp only [ofSphereScaling, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 * ε / a by positivity),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 * ε / b by positivity)]
  have ha' : (a : ℝ) ≠ 0 := by positivity
  have hb' : (b : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination hw

variable (a b) in
/-- **The weighted ellipsoid is diffeomorphic to the three-sphere.** For positive weights and
`ε > 0`, the diagonal scaling `(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)` is a `C^n`
diffeomorphism, for every `n`, from the ellipsoid `a |z₁|² + b |z₂|² = 2 ε`, with the atlas
`TauCeti.Toric.weightedEllipsoidChartedSpace`, onto the unit sphere `S³` of the Euclidean space
`ℂ²`, with Mathlib's stereographic atlas. Its inverse is the scaling
`(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. -/
def weightedEllipsoidDiffeomorphSphere (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) (n : ℕ∞ω) :
    letI := weightedEllipsoidChartedSpace a b hε.ne'
    weightedEllipsoid a b ε ≃ₘ^n⟮𝓘(ℝ, Fin 3 → ℝ), 𝓡 3⟯
      Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 :=
  letI := weightedEllipsoidChartedSpace a b hε.ne'
  haveI := isManifold_weightedEllipsoid (a := a) (b := b) hε.ne' n
  { toFun z := ⟨toSphereScaling a b ε z, toSphereScaling_mem_sphere hε z⟩
    invFun w := ⟨ofSphereScaling a b ε w, ofSphereScaling_mem_weightedEllipsoid ha hb hε w⟩
    left_inv z := by
      ext
      · simp only [toSphereScaling, ofSphereScaling, PiLp.toLp_apply, Matrix.cons_val_zero,
          smul_smul, sqrt_mul_sqrt_inv ha hε, one_smul]
      · simp only [toSphereScaling, ofSphereScaling, PiLp.toLp_apply, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, smul_smul, sqrt_mul_sqrt_inv hb hε, one_smul]
    right_inv w := by
      ext i
      fin_cases i
      · simp only [toSphereScaling, ofSphereScaling, Fin.zero_eta, PiLp.toLp_apply,
          Matrix.cons_val_zero, smul_smul, mul_comm √(a / (2 * ε)), sqrt_mul_sqrt_inv ha hε,
          one_smul]
      · simp only [toSphereScaling, ofSphereScaling, Fin.mk_one, PiLp.toLp_apply,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_smul, mul_comm √(b / (2 * ε)),
          sqrt_mul_sqrt_inv hb hε, one_smul]
    contMDiff_toFun :=
      ((contDiff_toSphereScaling (a := a) (b := b) (ε := ε)).comp_contMDiff
        (contMDiff_coe_weightedEllipsoid hε.ne')).codRestrict_sphere _
    contMDiff_invFun :=
      ContMDiff.codRestrict_weightedEllipsoid hε.ne'
        ((contDiff_ofSphereScaling (a := a) (b := b) (ε := ε)).comp_contMDiff
          contMDiff_coe_sphere) _ }

/-- The diffeomorphism of the ellipsoid with the sphere is the diagonal scaling
`(z₁, z₂) ↦ (√(a / (2 ε)) z₁, √(b / (2 ε)) z₂)`. -/
@[simp]
theorem coe_weightedEllipsoidDiffeomorphSphere_apply (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (n : ℕ∞ω) (z : weightedEllipsoid a b ε) :
    (weightedEllipsoidDiffeomorphSphere a b ha hb hε n z : EuclideanSpace ℂ (Fin 2)) =
      !₂[√(a / (2 * ε)) • (z : ℂ × ℂ).1, √(b / (2 * ε)) • (z : ℂ × ℂ).2] :=
  (rfl)

/-- The inverse of the diffeomorphism of the ellipsoid with the sphere is the diagonal scaling
`(w₁, w₂) ↦ (√(2 ε / a) w₁, √(2 ε / b) w₂)`. -/
@[simp]
theorem coe_weightedEllipsoidDiffeomorphSphere_symm_apply (ha : 0 < a) (hb : 0 < b)
    (hε : 0 < ε) (n : ℕ∞ω) (w : Metric.sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    letI := weightedEllipsoidChartedSpace a b hε.ne'
    ((weightedEllipsoidDiffeomorphSphere a b ha hb hε n).symm w : ℂ × ℂ) =
      (√(2 * ε / a) • (w : EuclideanSpace ℂ (Fin 2)) 0,
        √(2 * ε / b) • (w : EuclideanSpace ℂ (Fin 2)) 1) :=
  (rfl)

/-- **The diffeomorphism with the sphere is equivariant.** It carries the weighted rotation by a
circle element `u` on the ellipsoid to the rotation `(w₁, w₂) ↦ (u ^ a w₁, u ^ b w₂)` of the
sphere. -/
theorem coe_weightedEllipsoidDiffeomorphSphere_smul (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (n : ℕ∞ω) (u : Circle) (z : weightedEllipsoid a b ε) :
    (weightedEllipsoidDiffeomorphSphere a b ha hb hε n (u • z) : EuclideanSpace ℂ (Fin 2)) =
      !₂[(u : ℂ) ^ a * (weightedEllipsoidDiffeomorphSphere a b ha hb hε n z :
          EuclideanSpace ℂ (Fin 2)) 0,
        (u : ℂ) ^ b * (weightedEllipsoidDiffeomorphSphere a b ha hb hε n z :
          EuclideanSpace ℂ (Fin 2)) 1] := by
  simp only [coe_weightedEllipsoidDiffeomorphSphere_apply, coe_smul_weightedEllipsoid,
    weightedRotation_fst, weightedRotation_snd, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_smul_comm]

end TauCeti.Toric

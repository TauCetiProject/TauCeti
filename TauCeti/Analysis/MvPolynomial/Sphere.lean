/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.Algebra
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Polynomial restriction to the Euclidean unit sphere

Evaluation on the unit sphere is an algebra homomorphism from real multivariate polynomials
to continuous functions. Although not injective on all polynomials, it is injective on each
fixed homogeneous degree: radial homogeneity recovers the values away from the origin, and
homogeneity also recovers the value at the origin.

In particular, restriction embeds harmonic homogeneous polynomials into the continuous
functions on the actual Euclidean unit sphere, without changing their dimension. These are
finite-dimensional polynomial images; no identification with a full Laplace eigenspace or
spectral completeness is asserted here.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137
  (2001), Chapter 5 (homogeneous harmonic polynomials and spherical restriction).
-/

public section

noncomputable section

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

private def sphereCoord (i : σ) : C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, ℝ) :=
  ⟨fun x ↦ x.val i, (EuclideanSpace.proj i).continuous.comp continuous_subtype_val⟩

@[simp]
private theorem sphereCoord_apply (i : σ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) : sphereCoord i x = x.val i := (rfl)

/-- Restriction of a real polynomial to the Euclidean unit sphere, as a continuous function. -/
def sphereEval : MvPolynomial σ ℝ →ₐ[ℝ] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, ℝ) :=
  aeval sphereCoord

@[simp]
theorem sphereEval_apply (p : MvPolynomial σ ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval p x = eval (fun i ↦ x.val i) p := by
  rw [sphereEval, ← ContinuousMap.evalAlgHom_apply ℝ ℝ x, comp_aeval_apply]
  simp only [ContinuousMap.evalAlgHom_apply, sphereCoord_apply, aeval_eq_eval]

/-- The squared-norm polynomial restricts to the constant function one. -/
@[simp]
theorem sphereEval_normSq : sphereEval (normSq σ ℝ) = 1 := by
  ext x
  rw [sphereEval_apply, eval_normSq, ← EuclideanSpace.real_norm_sq_eq]
  simp [(mem_sphere_zero_iff_norm).1 x.property]

/-- Radial homogeneity reconstructs a homogeneous polynomial from its unit-sphere values
at every nonzero vector. -/
theorem IsHomogeneous.eval_eq_norm_pow_mul_sphereEval {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    eval (fun i ↦ x i) p = ‖x‖ ^ d * sphereEval p
      ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hx)⟩ := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hscale := hp.eval_smul (fun i ↦ (‖x‖⁻¹ • x) i) ‖x‖
  simpa only [sphereEval_apply, Pi.smul_def, PiLp.smul_apply, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hnorm, one_mul] using hscale

variable [Nonempty σ]

/-- A homogeneous polynomial vanishing on the unit sphere is zero, including in degree zero.
The nonempty variable type ensures that the unit sphere is nonempty. -/
theorem IsHomogeneous.eq_zero_of_sphereEval_eq_zero {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : sphereEval p = 0) : p = 0 := by
  apply hp.eq_zero_of_forall_eval_eq_zero
  intro x
  by_cases hx : x = 0
  · obtain ⟨u, hu⟩ := exists_norm_eq (E := EuclideanSpace ℝ σ) (by norm_num : (0 : ℝ) ≤ 1)
    have hz : eval (fun i ↦ u i) p = 0 := by
      simpa only [sphereEval_apply, ContinuousMap.zero_apply] using
        congrArg (fun f ↦ f ⟨u, mem_sphere_zero_iff_norm.2 hu⟩) h
    have hscale := hp.eval_smul (fun i ↦ u i) 0
    simpa [hx, hz] using hscale
  · have hnonzero : (WithLp.toLp 2 x : EuclideanSpace ℝ σ) ≠ 0 := by
      simpa using hx
    have hcoord : (fun i ↦ (WithLp.toLp 2 x : EuclideanSpace ℝ σ) i) = x := by
      ext i
      exact PiLp.toLp_apply 2 (fun _ : σ ↦ ℝ) x i
    have hrad := hp.eval_eq_norm_pow_mul_sphereEval hnonzero
    rw [hcoord] at hrad
    rw [hrad, h]
    simp

/-- Polynomials of the same homogeneous degree are determined by their restrictions to the
unit sphere. No harmonicity assumption is needed. -/
theorem IsHomogeneous.sphereEval_inj {p q : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    sphereEval p = sphereEval q ↔ p = q := by
  constructor
  · intro h
    apply sub_eq_zero.1
    exact (hp.sub hq).eq_zero_of_sphereEval_eq_zero (by simp [h])
  · rintro rfl
    rfl

/-- The linear restriction of harmonic homogeneous polynomials to the Euclidean unit sphere. -/
def harmonicSphereRestriction (σ : Type*) [Fintype σ] (d : ℕ) :
    harmonicSubmodule σ ℝ d →ₗ[ℝ] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, ℝ) :=
  sphereEval.toLinearMap.comp (harmonicSubmodule σ ℝ d).subtype

omit [Nonempty σ] in
/-- Harmonic restriction agrees with polynomial evaluation as a continuous function. -/
@[simp]
theorem harmonicSphereRestriction_coe (d : ℕ) (p : harmonicSubmodule σ ℝ d) :
    harmonicSphereRestriction σ d p = sphereEval (p : MvPolynomial σ ℝ) := (rfl)

/-- Restriction loses no harmonic homogeneous polynomial, in any degree. -/
theorem harmonicSphereRestriction_injective (d : ℕ) :
    Function.Injective (harmonicSphereRestriction σ d) := by
  intro p q h
  apply Subtype.ext
  exact ((mem_harmonicSubmodule_iff.1 p.property).1.sphereEval_inj
    (mem_harmonicSubmodule_iff.1 q.property).1).1
    (by simpa only [harmonicSphereRestriction_coe] using h)

/-- The spherical image has the same dimension as the harmonic polynomial space. -/
theorem finrank_range_harmonicSphereRestriction (d : ℕ) :
    Module.finrank ℝ (LinearMap.range (harmonicSphereRestriction σ d)) =
      Module.finrank ℝ (harmonicSubmodule σ ℝ d) :=
  LinearMap.finrank_range_of_inj (harmonicSphereRestriction_injective d)

/-- The dimension of the restricted harmonic polynomials of degree `e + 2` in `n` variables
is `n.multichoose (e + 2) - n.multichoose e`. -/
theorem finrank_range_harmonicSphereRestriction_add_two (e : ℕ) :
    Module.finrank ℝ (LinearMap.range (harmonicSphereRestriction σ (e + 2))) =
      (Fintype.card σ).multichoose (e + 2) - (Fintype.card σ).multichoose e := by
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_add_two]

/-- Constants and linear polynomials retain their full homogeneous dimension on the sphere. -/
theorem finrank_range_harmonicSphereRestriction_of_le_one {d : ℕ} (hd : d ≤ 1) :
    Module.finrank ℝ (LinearMap.range (harmonicSphereRestriction σ d)) =
      (Fintype.card σ).multichoose d := by
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_of_le_one hd]

end MvPolynomial

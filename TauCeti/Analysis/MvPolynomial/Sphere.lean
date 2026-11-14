/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Orthogonal
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# Polynomial restriction to the Euclidean unit sphere and uniform spherical-harmonic density

Evaluation at the real coordinates of a unit vector defines an `R`-algebra homomorphism
`MvPolynomial.sphereEval` from multivariate polynomials over a topological `ℝ`-algebra `R` to
`C(S, R)`, where `S = Metric.sphere (0 : EuclideanSpace ℝ σ) 1`.

Although `sphereEval` is not injective on all polynomials (`r² - 1` vanishes identically on `S`), it
is injective on each homogeneous degree `d` over any commutative topological `ℝ`-algebra: radial
homogeneity recovers values on `ℝ^σ \ {0}` and `0` from values on `S` when `R = ℝ`, and linear
functionals `R →ₗ[ℝ] ℝ` reduce the general case to `ℝ`. Restricting `sphereEval` to the harmonic
homogeneous polynomials `harmonicSubmodule σ R d` therefore embeds `H_d` injectively into `C(S, R)`
(`MvPolynomial.harmonicSphereRestriction`) without loss of dimension.

Under the orthogonal group `Matrix.orthogonalGroup σ ℝ`, spherical restriction intertwines the
algebraic representation `MvPolynomial.harmonicRep` with the geometric pullback `x ↦ g⁻¹ • x` on
the unit sphere (`MvPolynomial.harmonicSphereRestriction_harmonicRep_apply`).

Combining the iterated Fischer decomposition
(`MvPolynomial.homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow`) with
`sphereEval (normSq σ K) = 1` shows that every polynomial function on `S` is a finite sum of
spherical harmonics (`MvPolynomial.range_sphereEval_eq_iSup_range_harmonicSphereRestriction`). Over
`𝕜` with `[RCLike 𝕜]`, the range of `sphereEval` is closed under pointwise conjugation and separates
points of `S`, so the Stone–Weierstrass theorem proves that finite sums of spherical harmonics are
uniformly dense in `C(S, 𝕜)`
(`MvPolynomial.topologicalClosure_iSup_range_harmonicSphereRestriction`).

## Main definitions

* `MvPolynomial.sphereEval`: restriction `MvPolynomial σ R →ₐ[R] C(S, R)` of polynomials to the
  Euclidean unit sphere `S`.
* `MvPolynomial.harmonicSphereRestriction`: linear restriction
  `harmonicSubmodule σ R d →ₗ[R] C(S, R)` of harmonic homogeneous polynomials of degree `d` to `S`.

## Main results

* `MvPolynomial.sphereEval_normSq`: `sphereEval (normSq σ R) = 1`.
* `MvPolynomial.harmonicSphereRestriction_harmonicRep_apply`: `O(σ)`-equivariance of spherical
  harmonics under `Matrix.UnitaryGroup.toLinearIsometryEquiv`.
* `MvPolynomial.IsHomogeneous.eq_zero_of_sphereEval_eq_zero`,
  `MvPolynomial.harmonicSphereRestriction_injective`: injectivity of spherical restriction in a
  fixed homogeneous degree (over any commutative topological `ℝ`-algebra, when `σ` is nonempty).
* `MvPolynomial.finrank_range_harmonicSphereRestriction`,
  `MvPolynomial.finrank_range_harmonicSphereRestriction_eq_choose_sub`: dimension of the space of
  degree-`d` spherical harmonics.
* `MvPolynomial.range_sphereEval_eq_iSup_range_harmonicSphereRestriction`: polynomial functions on
  `S` coincide with the span of spherical harmonics of all degrees.
* `MvPolynomial.topologicalClosure_range_sphereEval`,
  `MvPolynomial.topologicalClosure_iSup_range_harmonicSphereRestriction`: uniform density of
  spherical harmonics in `C(S, 𝕜)` for `[RCLike 𝕜]`.

## References

* S. Axler, P. Bourdon and W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137
  (2001), Chapter 5 (homogeneous harmonic polynomials, spherical harmonics, and uniform density).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Princeton
  University Press (1971), Chapter IV, Section 2.
-/

public section

noncomputable section

namespace MvPolynomial

section CommSemiring

variable {σ R : Type*} [Fintype σ] [CommSemiring R] [Algebra ℝ R]
  [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousSMul ℝ R]

private def sphereCoord (i : σ) : C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, R) :=
  ⟨fun x ↦ algebraMap ℝ R (x.val i),
    ((continuous_id.smul (continuous_const (y := (1 : R)))).congr
      fun r ↦ (Algebra.algebraMap_eq_smul_one r).symm).comp
      ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val)⟩

omit [IsTopologicalSemiring R] in
@[simp]
private theorem sphereCoord_apply (i : σ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereCoord (R := R) i x = algebraMap ℝ R (x.val i) := (rfl)

/-- Restriction of a polynomial over an `ℝ`-algebra `R` to the Euclidean unit sphere, as an
`R`-valued continuous function. -/
def sphereEval : MvPolynomial σ R →ₐ[R] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, R) :=
  aeval sphereCoord

@[simp]
theorem sphereEval_apply (p : MvPolynomial σ R)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval p x = eval (fun i ↦ algebraMap ℝ R (x.val i)) p := by
  rw [sphereEval, ← ContinuousMap.evalAlgHom_apply R R x, comp_aeval_apply]
  simp only [ContinuousMap.evalAlgHom_apply, sphereCoord_apply, aeval_eq_eval]

theorem sphereEval_X (i : σ) (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (X i : MvPolynomial σ R) x = algebraMap ℝ R (x.val i) := by
  simp

theorem sphereEval_C (r : R) (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (C r : MvPolynomial σ R) x = r := by
  simp

/-- Restricting a real polynomial after extending scalars to `R` agrees with applying
`algebraMap ℝ R` to its real restriction. -/
theorem sphereEval_map_algebraMap (p : MvPolynomial σ ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (map (algebraMap ℝ R) p) x = algebraMap ℝ R (sphereEval p x) := by
  simp only [sphereEval_apply, Algebra.algebraMap_self, RingHom.id_apply, map_eval]
  rfl

/-- The squared-norm polynomial `∑ᵢ Xᵢ²` restricts to the constant function `1` on the unit
sphere. -/
@[simp]
theorem sphereEval_normSq : sphereEval (normSq σ R) = 1 := by
  ext x
  rw [← map_normSq (σ := σ) (algebraMap ℝ R), sphereEval_map_algebraMap, sphereEval_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, eval_normSq,
    ← EuclideanSpace.real_norm_sq_eq, mem_sphere_zero_iff_norm.1 x.property, one_pow, map_one,
    ContinuousMap.one_apply]

/-- Radial homogeneity reconstructs the value of a degree-`d` homogeneous polynomial on `ℝ^σ \ {0}`
from its restriction to the unit sphere. -/
theorem IsHomogeneous.eval_algebraMap_eq_norm_pow_smul_sphereEval {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    eval (fun i ↦ algebraMap ℝ R (x i)) p = ‖x‖ ^ d • sphereEval p
      ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hx)⟩ := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hscale := hp.eval_smul (algebraMap ℝ R ‖x‖)
    (fun i ↦ algebraMap ℝ R ((‖x‖⁻¹ • x) i))
  rw [sphereEval_apply, Algebra.smul_def, map_pow]
  refine (congrArg (eval · p) (_root_.funext fun i ↦ ?_)).trans hscale
  simp [← map_mul, ← mul_assoc, mul_inv_cancel₀ hnorm]

/-- Radial homogeneity reconstructs a real homogeneous polynomial from its unit-sphere values at
every nonzero vector. -/
theorem IsHomogeneous.eval_eq_norm_pow_mul_sphereEval {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    eval (fun i ↦ x i) p = ‖x‖ ^ d * sphereEval p
      ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm hx)⟩ := by
  simpa using hp.eval_algebraMap_eq_norm_pow_smul_sphereEval hx

/-- The linear restriction of harmonic homogeneous polynomials of degree `d` over `R` to continuous
functions on the Euclidean unit sphere. -/
def harmonicSphereRestriction (σ : Type*) [Fintype σ] {R : Type*} [CommSemiring R] [Algebra ℝ R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousSMul ℝ R] (d : ℕ) :
    harmonicSubmodule σ R d →ₗ[R] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, R) :=
  sphereEval.toLinearMap.comp (harmonicSubmodule σ R d).subtype

/-- Harmonic restriction agrees with polynomial evaluation as a continuous function. -/
@[simp]
theorem harmonicSphereRestriction_coe (d : ℕ) (p : harmonicSubmodule σ R d) :
    harmonicSphereRestriction σ d p = sphereEval (p : MvPolynomial σ R) := (rfl)

theorem harmonicSphereRestriction_apply (d : ℕ) (p : harmonicSubmodule σ R d)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    harmonicSphereRestriction σ d p x =
      eval (fun i ↦ algebraMap ℝ R (x.val i)) (p : MvPolynomial σ R) :=
  sphereEval_apply (p : MvPolynomial σ R) x

end CommSemiring

section OrthogonalEquivariance

open Matrix

variable {σ R : Type*} [Fintype σ] [DecidableEq σ]

/-- Substituting the transpose of an orthogonal matrix `g ∈ O(σ)` before restricting to the unit
sphere pulls back along the Euclidean isometry of `g⁻¹`. -/
theorem sphereEval_linearSubst_transpose_orthogonal_apply [CommSemiring R] [Algebra ℝ R]
    [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousSMul ℝ R]
    (g : Matrix.orthogonalGroup σ ℝ) (p : MvPolynomial σ R)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (linearSubst ((g : Matrix σ σ ℝ)ᵀ.map (algebraMap ℝ R)) p) x =
      sphereEval p (Matrix.UnitaryGroup.toLinearIsometryEquiv g⁻¹ • x) := by
  rw [sphereEval_apply, eval_linearSubst, sphereEval_apply]
  refine congrArg (eval · p) (funext fun i ↦ ?_)
  have hinv : ((g⁻¹ : Matrix.orthogonalGroup σ ℝ) : Matrix σ σ ℝ) = (g : Matrix σ σ ℝ)ᵀ := by
    rw [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [LinearIsometryEquiv.coe_smul_unitSphere, UnitaryGroup.toLinearIsometryEquiv_apply, hinv]
  simp [Matrix.mulVec, dotProduct]

/-- **Orthogonal equivariance of spherical harmonics**: the algebraic `O(σ)`-action
`MvPolynomial.harmonicRep` on `harmonicSubmodule σ ℝ d` intertwines under
`harmonicSphereRestriction` with the geometric pullback `x ↦ g⁻¹ • x` on the unit sphere. -/
theorem harmonicSphereRestriction_harmonicRep_apply {d : ℕ} (g : Matrix.orthogonalGroup σ ℝ)
    (p : harmonicSubmodule σ ℝ d) (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    harmonicSphereRestriction σ d (harmonicRep σ ℝ d g p) x =
      harmonicSphereRestriction σ d p (Matrix.UnitaryGroup.toLinearIsometryEquiv g⁻¹ • x) := by
  simpa [harmonicSphereRestriction_coe, coe_harmonicRep_apply] using
    sphereEval_linearSubst_transpose_orthogonal_apply (R := ℝ) g (p : MvPolynomial σ ℝ) x

end OrthogonalEquivariance

section Injective

variable {σ R : Type*} [Fintype σ] [Nonempty σ]

private theorem eq_zero_of_sphereEval_eq_zero_real {p : MvPolynomial σ ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : sphereEval p = 0) : p = 0 := by
  apply hp.eq_zero_of_forall_eval_eq_zero
  intro x
  by_cases hx : x = 0
  · obtain ⟨u, hu⟩ := exists_norm_eq (E := EuclideanSpace ℝ σ) (by norm_num : (0 : ℝ) ≤ 1)
    have hz : eval (fun i ↦ u i) p = 0 := by
      simpa only [sphereEval_apply, Algebra.algebraMap_self, RingHom.id_apply,
        ContinuousMap.zero_apply] using
        congrArg (fun f ↦ f ⟨u, mem_sphere_zero_iff_norm.2 hu⟩) h
    have hscale := hp.eval_smul 0 (fun i ↦ u i)
    simpa [hx, hz] using hscale
  · have hnonzero : (WithLp.toLp 2 x : EuclideanSpace ℝ σ) ≠ 0 := by simpa using hx
    have hcoord : (fun i ↦ (WithLp.toLp 2 x : EuclideanSpace ℝ σ) i) = x := by
      ext i
      exact PiLp.toLp_apply 2 (fun _ : σ ↦ ℝ) x i
    have hrad := hp.eval_eq_norm_pow_mul_sphereEval hnonzero
    rw [hcoord] at hrad
    rw [hrad, h]
    simp

variable [CommRing R] [Algebra ℝ R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousSMul ℝ R]

/-- A homogeneous polynomial over a commutative topological `ℝ`-algebra that vanishes on the unit
sphere is zero, including in degree zero. The nonempty variable type ensures that the unit sphere
is nonempty. -/
theorem IsHomogeneous.eq_zero_of_sphereEval_eq_zero {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : sphereEval p = 0) : p = 0 := by
  classical
  ext m
  change p.coeff m = 0
  rw [← Module.forall_dual_apply_eq_zero_iff ℝ]
  intro φ
  let q : MvPolynomial σ ℝ := .ofCoeff (Finsupp.mapRange.linearMap φ p.coeff)
  have hq_coeff (n : σ →₀ ℕ) : q.coeff n = φ (p.coeff n) := rfl
  have hq_hom : q.IsHomogeneous d := fun n hn ↦ hp fun h0 ↦ hn (by simp [hq_coeff, h0])
  have hq_eval : sphereEval q = 0 := by
    ext x
    have hx : φ (sphereEval p x) = 0 := by simp [h]
    rw [ContinuousMap.zero_apply, ← hx, sphereEval_apply, sphereEval_apply, ← aeval_eq_eval,
      ← aeval_eq_eval, hq_hom.aeval_eq_sum_finsuppAntidiag, hp.aeval_eq_sum_finsuppAntidiag,
      map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have hprod : ∏ i, algebraMap ℝ R (x.val i) ^ s i = algebraMap ℝ R (∏ i, x.val i ^ s i) := by
      simp
    simp only [Algebra.algebraMap_self, RingHom.id_apply, hq_coeff, hprod]
    rw [mul_comm (p.coeff s), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  simpa [hq_coeff] using congrArg (fun f : MvPolynomial σ ℝ ↦ f.coeff m)
    (eq_zero_of_sphereEval_eq_zero_real hq_hom hq_eval)

/-- Homogeneous polynomials of the same degree over a commutative topological `ℝ`-algebra are
determined by their restrictions to the unit sphere. No harmonicity assumption is needed. -/
theorem IsHomogeneous.sphereEval_inj {p q : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    sphereEval p = sphereEval q ↔ p = q := by
  refine ⟨fun h ↦ sub_eq_zero.1 <| (hp.sub hq).eq_zero_of_sphereEval_eq_zero ?_, fun h ↦ h ▸ rfl⟩
  rw [map_sub, h, sub_self]

/-- Restriction to the unit sphere is injective on harmonic homogeneous polynomials of any
degree. -/
theorem harmonicSphereRestriction_injective (d : ℕ) :
    Function.Injective (harmonicSphereRestriction (R := R) σ d) := by
  intro p q h
  apply Subtype.ext
  exact ((mem_harmonicSubmodule_iff.1 p.property).1.sphereEval_inj
    (mem_harmonicSubmodule_iff.1 q.property).1).1
    (by simpa only [harmonicSphereRestriction_coe] using h)

/-- The space of degree-`d` spherical harmonics has the same dimension as the space of degree-`d`
harmonic homogeneous polynomials. -/
theorem finrank_range_harmonicSphereRestriction (d : ℕ) :
    Module.finrank R (LinearMap.range (harmonicSphereRestriction (R := R) σ d)) =
      Module.finrank R (harmonicSubmodule σ R d) :=
  LinearMap.finrank_range_of_inj (harmonicSphereRestriction_injective d)

/-- Constants and linear polynomials retain their full homogeneous dimension on the sphere. -/
theorem finrank_range_harmonicSphereRestriction_of_le_one [StrongRankCondition R] {d : ℕ}
    (hd : d ≤ 1) :
    Module.finrank R (LinearMap.range (harmonicSphereRestriction (R := R) σ d)) =
      (Fintype.card σ).multichoose d := by
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_of_le_one hd]

end Injective

section FischerAndDensity

variable {σ : Type*} [Fintype σ]

section Field

variable {K : Type*} [Field K] [CharZero K] [Algebra ℝ K] [TopologicalSpace K]
  [IsTopologicalRing K] [ContinuousSMul ℝ K]

/-- The dimension of the space of spherical harmonics of degree `e + 2` in `n` variables (`n ≥ 1`)
is `n.multichoose (e + 2) - n.multichoose e`. -/
theorem finrank_range_harmonicSphereRestriction_add_two [Nonempty σ] (e : ℕ) :
    Module.finrank K (LinearMap.range (harmonicSphereRestriction (R := K) σ (e + 2))) =
      (Fintype.card σ).multichoose (e + 2) - (Fintype.card σ).multichoose e := by
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_add_two]

/-- **Dimension of spherical harmonics on `S^m ⊂ ℝ^(m+1)`**: when `|σ| = m + 1`, the space of
spherical harmonics of degree `d` has dimension `C(m + d, d) - C(m + d - 2, d - 2)`, where the
subtracted term is `0` for `d < 2`. -/
theorem finrank_range_harmonicSphereRestriction_eq_choose_sub {m : ℕ}
    (hσ : Fintype.card σ = m + 1) (d : ℕ) :
    Module.finrank K (LinearMap.range (harmonicSphereRestriction (R := K) σ d)) =
      (m + d).choose d - if 2 ≤ d then (m + d - 2).choose (d - 2) else 0 := by
  have : Nonempty σ := Fintype.card_pos_iff.1 (by omega)
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_eq_choose_sub hσ]

/-- **Spherical Fischer decomposition**: every polynomial function on the unit sphere is a finite
sum of restrictions of harmonic homogeneous polynomials, because `r² = 1` on the unit sphere
collapses every factor `r^(2k)` in
`MvPolynomial.homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow`. -/
theorem range_sphereEval_eq_iSup_range_harmonicSphereRestriction :
    (sphereEval (σ := σ) (R := K)).range.toSubmodule =
      ⨆ d, LinearMap.range (harmonicSphereRestriction (R := K) σ d) := by
  refine le_antisymm ?_ (iSup_le fun d ↦ by rintro _ ⟨p, rfl⟩; exact ⟨p, rfl⟩)
  have hhom (d : ℕ) :
      (homogeneousSubmodule σ K d).map (sphereEval (σ := σ) (R := K)).toLinearMap ≤
        ⨆ e, LinearMap.range (harmonicSphereRestriction (R := K) σ e) := by
    rw [homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow d]
    simp_rw [Submodule.map_iSup]
    refine iSup₂_le fun k _ ↦ ?_
    rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine le_iSup
      (fun e ↦ LinearMap.range (harmonicSphereRestriction (R := K) σ e)) (d - 2 * k) ?_
    refine ⟨⟨h, hh⟩, ?_⟩
    change sphereEval h = sphereEval (normSq σ K ^ k * h)
    simp
  rintro _ ⟨p, rfl⟩
  rw [← sum_homogeneousComponent p, map_sum]
  exact Submodule.sum_mem _ fun d _ ↦
    hhom d ⟨homogeneousComponent d p, homogeneousComponent_isHomogeneous d p, rfl⟩

end Field

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pointwise conjugation of a polynomial function on the real unit sphere is the restriction of
the coefficientwise-conjugated polynomial, since the sphere coordinates are real. -/
theorem star_sphereEval (p : MvPolynomial σ 𝕜) :
    star (sphereEval p) = sphereEval (map (starRingEnd 𝕜) p) := by
  ext x
  change starRingEnd 𝕜 (sphereEval p x) = _
  rw [sphereEval_apply, sphereEval_apply, map_eval]
  refine congrArg (eval · (map (starRingEnd 𝕜) p)) (funext fun i ↦ ?_)
  simp

private def sphereEvalStarSubalgebra (σ 𝕜 : Type*) [Fintype σ] [RCLike 𝕜] :
    StarSubalgebra 𝕜 C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, 𝕜) :=
  { (sphereEval (σ := σ) (R := 𝕜)).range with
    star_mem' := by
      rintro _ ⟨p, rfl⟩
      exact ⟨map (starRingEnd 𝕜) p, (star_sphereEval p).symm⟩ }

/-- Polynomial restrictions separate points of the Euclidean unit sphere. -/
theorem separatesPoints_range_sphereEval :
    (sphereEval (σ := σ) (R := 𝕜)).range.SeparatesPoints := by
  intro x y hxy
  have hval : ∃ i : σ, x.val i ≠ y.val i := by
    by_contra! h
    exact hxy (Subtype.ext (PiLp.ext h))
  obtain ⟨i, hi⟩ := hval
  refine ⟨_, ⟨sphereEval (X i : MvPolynomial σ 𝕜), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa only [sphereEval_X, RCLike.algebraMap_eq_ofReal] using RCLike.ofReal_injective.ne hi

/-- **Stone–Weierstrass density of polynomials on the unit sphere**: polynomial restrictions are
uniformly dense in `C(S, 𝕜)` for `[RCLike 𝕜]`. -/
theorem topologicalClosure_range_sphereEval :
    (sphereEval (σ := σ) (R := 𝕜)).range.topologicalClosure = ⊤ := by
  have hstar : (sphereEvalStarSubalgebra σ 𝕜).topologicalClosure = ⊤ :=
    ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      separatesPoints_range_sphereEval
  exact (StarSubalgebra.topologicalClosure_toSubalgebra_comm
    (sphereEvalStarSubalgebra σ 𝕜)).symm.trans (congrArg StarSubalgebra.toSubalgebra hstar)

/-- **Uniform density of spherical harmonics**: finite sums of spherical harmonics are uniformly
dense in `C(S, 𝕜)` for `[RCLike 𝕜]`. -/
theorem topologicalClosure_iSup_range_harmonicSphereRestriction :
    (⨆ d, LinearMap.range (harmonicSphereRestriction (R := 𝕜) σ d)).topologicalClosure = ⊤ := by
  rw [← range_sphereEval_eq_iSup_range_harmonicSphereRestriction]
  exact SetLike.coe_injective <| by
    rw [Submodule.topologicalClosure_coe, Submodule.top_coe, Subalgebra.coe_toSubmodule]
    simpa [Subalgebra.topologicalClosure_coe] using
      congrArg (SetLike.coe : Subalgebra 𝕜 C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, 𝕜) → _)
        (topologicalClosure_range_sphereEval (σ := σ) (𝕜 := 𝕜))

end RCLike

end FischerAndDensity

end MvPolynomial

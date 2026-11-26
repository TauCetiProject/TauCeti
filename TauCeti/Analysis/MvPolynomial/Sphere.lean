/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.RingTheory.MvPolynomial.Harmonic.Orthogonal
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.Algebra.Algebra
import TauCeti.RingTheory.MvPolynomial.Homogeneous
import TauCeti.Topology.Sphere.Coord
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Polynomial restriction to the Euclidean unit sphere and spherical-harmonic density

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

Over any commutative topological `ℝ`-algebra `R`, every polynomial function on `S` equals a finite
sum of spherical harmonics
(`MvPolynomial.range_sphereEval_eq_iSup_range_harmonicSphereRestriction`), and whenever `R` is
nontrivial the range separates points of `S` (`MvPolynomial.separatesPoints_range_sphereEval`).
Over `𝕜` with `[RCLike 𝕜]`, the range is closed under pointwise conjugation, so the
Stone–Weierstrass theorem proves uniform density in `C(S, 𝕜)`
(`MvPolynomial.topologicalClosure_iSup_range_harmonicSphereRestriction`), hence `Lᵖ(S, μ; 𝕜)`
density for every `1 ≤ p < ∞` and finite Borel measure `μ`
(`TauCeti.topologicalClosure_iSup_map_toLp_harmonicSphereRestriction`) and `L²(S, μ; 𝕜)` orthogonal
completeness (`TauCeti.eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero`).

## Main definitions

* `MvPolynomial.sphereEval`: restriction `MvPolynomial σ R →ₐ[R] C(S, R)` of polynomials to the
  Euclidean unit sphere `S`.
* `MvPolynomial.harmonicSphereRestriction`: linear restriction
  `harmonicSubmodule σ R d →ₗ[R] C(S, R)` of harmonic homogeneous polynomials of degree `d` to `S`.

## Main results

* `MvPolynomial.sphereEval_addMonoidAlgebra_map_apply`,
  `MvPolynomial.harmonicSphereRestriction_mapHarmonicSubmodule_apply`: coefficientwise `ℝ`-linear
  maps intertwine with `sphereEval` and `harmonicSphereRestriction`.
* `MvPolynomial.sphereEval_normSq`: `sphereEval (normSq σ R) = 1`.
* `MvPolynomial.IsHomogeneous.norm_pow_smul_sphereExtend_sphereEval`: `‖x‖ ^ d` times the
  `0`-homogeneous radial extension of `sphereEval p` recovers `p` on `ℝ^σ \ {0}`.
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
* `TauCeti.topologicalClosure_iSup_map_toLp_harmonicSphereRestriction`,
  `TauCeti.eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero`: `Lᵖ` density
  (`1 ≤ p < ∞`) and `L²` orthogonal completeness of spherical harmonics for any finite Borel
  measure on `S`.

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

/-- Restriction of a polynomial over an `ℝ`-algebra `R` to the Euclidean unit sphere, as an
`R`-valued continuous function. -/
def sphereEval : MvPolynomial σ R →ₐ[R] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, R) :=
  aeval (TauCeti.sphereCoord R)

@[simp]
theorem sphereEval_apply (p : MvPolynomial σ R)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval p x = eval (fun i ↦ algebraMap ℝ R (x.val i)) p := by
  rw [sphereEval, ← ContinuousMap.evalAlgHom_apply R R x, comp_aeval_apply]
  simp only [ContinuousMap.evalAlgHom_apply, TauCeti.sphereCoord_apply, aeval_eq_eval]

/-- Applying an `ℝ`-linear map coefficientwise to a polynomial intertwines with `sphereEval`,
since the coordinates of points on the unit sphere are real. -/
theorem sphereEval_addMonoidAlgebra_map_apply {S : Type*} [CommSemiring S] [Algebra ℝ S]
    [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousSMul ℝ S]
    (φ : R →ₗ[ℝ] S) (p : MvPolynomial σ R)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (AddMonoidAlgebra.map φ.toAddMonoidHom p : MvPolynomial σ S) x =
      φ (sphereEval p x) := by
  induction p using MvPolynomial.induction_on' with
  | monomial s r =>
    have hmap : (AddMonoidAlgebra.map φ.toAddMonoidHom (monomial s r) : MvPolynomial σ S) =
        monomial s (φ r) := by
      simp only [monomial, AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.map_single,
        LinearMap.toAddMonoidHom_coe]
    rw [hmap]
    simp only [sphereEval_apply, eval_monomial]
    have hprod : ∏ i ∈ s.support, algebraMap ℝ R (x.val i) ^ s i =
        algebraMap ℝ R (∏ i ∈ s.support, x.val i ^ s i) := by simp
    have hprodS : ∏ i ∈ s.support, algebraMap ℝ S (x.val i) ^ s i =
        algebraMap ℝ S (∏ i ∈ s.support, x.val i ^ s i) := by simp
    rw [Finsupp.prod, Finsupp.prod, hprod, hprodS, mul_comm r, ← Algebra.smul_def,
      map_smul, Algebra.smul_def, mul_comm]
  | add p q hp hq =>
    simp [AddMonoidAlgebra.map_add, hp, hq]

/-- Restricting a real polynomial after extending scalars to `R` agrees with applying
`algebraMap ℝ R` to its real restriction. -/
theorem sphereEval_map_algebraMap_apply (p : MvPolynomial σ ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    sphereEval (map (algebraMap ℝ R) p) x = algebraMap ℝ R (sphereEval p x) := by
  simp only [sphereEval_apply, Algebra.algebraMap_self, RingHom.id_apply, map_eval]
  rfl

/-- The squared-norm polynomial `∑ᵢ Xᵢ²` restricts to the constant function `1` on the unit
sphere. -/
@[simp]
theorem sphereEval_normSq : sphereEval (normSq σ R) = 1 := by
  ext x
  rw [← map_normSq (σ := σ) (algebraMap ℝ R), sphereEval_map_algebraMap_apply, sphereEval_apply]
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

/-- Away from the origin, scaling the `0`-homogeneous radial extension `TauCeti.sphereExtend` of
a degree-`d` homogeneous polynomial's unit-sphere restriction by `‖x‖ ^ d` recovers its evaluation
at `x`. -/
theorem IsHomogeneous.norm_pow_smul_sphereExtend_sphereEval {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) {x : EuclideanSpace ℝ σ} (hx : x ≠ 0) :
    ‖x‖ ^ d • TauCeti.sphereExtend (sphereEval p) x = eval (fun i ↦ algebraMap ℝ R (x i)) p := by
  rw [TauCeti.sphereExtend_of_ne_zero _ hx]
  simpa only [NormedSpace.normalize] using
    (hp.eval_algebraMap_eq_norm_pow_smul_sphereEval hx).symm

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

/-- Applying an `ℝ`-linear map coefficientwise to a harmonic homogeneous polynomial intertwines
with `harmonicSphereRestriction`. -/
theorem harmonicSphereRestriction_mapHarmonicSubmodule_apply {S : Type*} [CommSemiring S]
    [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousSMul ℝ S]
    (φ : R →ₗ[ℝ] S) {d : ℕ} (p : harmonicSubmodule σ R d)
    (x : Metric.sphere (0 : EuclideanSpace ℝ σ) 1) :
    harmonicSphereRestriction σ d (mapHarmonicSubmodule φ.toAddMonoidHom d p) x =
      φ (harmonicSphereRestriction σ d p x) := by
  rw [harmonicSphereRestriction_coe, harmonicSphereRestriction_coe,
    coe_mapHarmonicSubmodule_apply, sphereEval_addMonoidAlgebra_map_apply]

/-- **Spherical Fischer decomposition**: the space of polynomial functions on the unit sphere equals
the span of spherical harmonics of all degrees. -/
theorem range_sphereEval_eq_iSup_range_harmonicSphereRestriction :
    (sphereEval (σ := σ) (R := R)).range.toSubmodule =
      ⨆ d, LinearMap.range (harmonicSphereRestriction (R := R) σ d) := by
  refine le_antisymm ?_ (iSup_le fun d ↦ by
    rintro _ ⟨p, rfl⟩
    exact ⟨p.val, (harmonicSphereRestriction_coe d p).symm⟩)
  let f : MvPolynomial σ ℝ →ₗ[ℝ] C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, R) :=
    (sphereEval (σ := σ) (R := R)).toLinearMap.restrictScalars ℝ ∘ₗ
      (mapAlgHom (Algebra.ofId ℝ R)).toLinearMap
  have hf_apply (r : MvPolynomial σ ℝ) : f r = sphereEval (map (algebraMap ℝ R) r) := by
    simp [f]
  have hhom_real (d : ℕ) {q : MvPolynomial σ ℝ} (hq : q.IsHomogeneous d) :
      sphereEval (map (algebraMap ℝ R) q) ∈
        ⨆ e, LinearMap.range (harmonicSphereRestriction (R := R) σ e) := by
    have hq_mem : q ∈ ⨆ k ≤ d / 2,
        (harmonicSubmodule σ ℝ (d - 2 * k)).map (LinearMap.mulLeft ℝ (normSq σ ℝ ^ k)) := by
      rw [← homogeneousSubmodule_eq_iSup_map_mulLeft_normSq_pow]
      exact hq
    have hle : (⨆ k ≤ d / 2,
        (harmonicSubmodule σ ℝ (d - 2 * k)).map (LinearMap.mulLeft ℝ (normSq σ ℝ ^ k))).map f ≤
        (⨆ e, LinearMap.range (harmonicSphereRestriction (R := R) σ e)).restrictScalars ℝ := by
      simp_rw [Submodule.map_iSup]
      refine iSup₂_le fun k _ ↦ ?_
      rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine (Submodule.restrictScalars_mem ℝ _ _).2 <|
        le_iSup (fun e ↦ LinearMap.range (harmonicSphereRestriction (R := R) σ e)) (d - 2 * k)
          ⟨⟨map (algebraMap ℝ R) h, map_mem_harmonicSubmodule (algebraMap ℝ R) hh⟩, ?_⟩
      simp [f, harmonicSphereRestriction_coe, map_normSq]
    rw [← hf_apply]
    exact (Submodule.restrictScalars_mem ℝ _ _).1 (hle (Submodule.mem_map_of_mem hq_mem))
  intro y hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range (φ := sphereEval (σ := σ) (R := R))).1 hy
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s _ ↦ ?_
  have hmon : monomial s (p.coeff s) =
      p.coeff s • map (algebraMap ℝ R) (monomial s (1 : ℝ)) := by
    simp [map_monomial, smul_monomial]
  rw [hmon, map_smul]
  exact Submodule.smul_mem _ _ (hhom_real s.degree (isHomogeneous_monomial (1 : ℝ) rfl))

/-- Polynomial restrictions separate points of the Euclidean unit sphere. -/
theorem separatesPoints_range_sphereEval [Nontrivial R] :
    (sphereEval (σ := σ) (R := R)).range.SeparatesPoints := by
  intro x y hxy
  have hval : ∃ i : σ, x.val i ≠ y.val i := by
    by_contra! h
    exact hxy (Subtype.ext (PiLp.ext h))
  obtain ⟨i, hi⟩ := hval
  refine ⟨_, ⟨sphereEval (X i : MvPolynomial σ R), ⟨X i, rfl⟩, rfl⟩, ?_⟩
  simpa only [sphereEval_apply, eval_X] using (algebraMap ℝ R).injective.ne hi

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

omit [DecidableEq σ] in
/-- Spherical harmonics are closed under pullback by Euclidean linear isometries. -/
theorem comp_unitSphereIsometryEquiv_mem_range_harmonicSphereRestriction {d : ℕ}
    {e : EuclideanSpace ℝ σ ≃ₗᵢ[ℝ] EuclideanSpace ℝ σ}
    {f : C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, ℝ)}
    (hf : f ∈ LinearMap.range (harmonicSphereRestriction σ (R := ℝ) d)) :
    f.comp ⟨e.unitSphereIsometryEquiv, e.unitSphereIsometryEquiv.isometry.continuous⟩ ∈
      LinearMap.range (harmonicSphereRestriction σ (R := ℝ) d) := by
  classical
  obtain ⟨p, rfl⟩ := hf
  set g : Matrix.orthogonalGroup σ ℝ :=
    (Matrix.UnitaryGroup.toLinearIsometryEquiv).symm e⁻¹
  have hg : Matrix.UnitaryGroup.toLinearIsometryEquiv g⁻¹ = e := by
    rw [map_inv, MulEquiv.apply_symm_apply, inv_inv]
  refine ⟨harmonicRep σ ℝ d g p, ContinuousMap.ext fun x ↦ ?_⟩
  rw [harmonicSphereRestriction_harmonicRep_apply, hg]
  exact congrArg (harmonicSphereRestriction σ (R := ℝ) d p)
    (e.unitSphereIsometryEquiv_apply_eq_smul x).symm

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
    have hrad := hp.eval_algebraMap_eq_norm_pow_smul_sphereEval hnonzero
    simp only [Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul] at hrad
    rw [hcoord] at hrad
    rw [hrad, h]
    simp

variable [CommRing R] [Algebra ℝ R] [TopologicalSpace R] [IsTopologicalSemiring R]
  [ContinuousSMul ℝ R]

/-- A homogeneous polynomial over a commutative topological `ℝ`-algebra that vanishes on the unit
sphere is zero, including in degree zero. The nonempty variable type ensures that the unit sphere
is nonempty. -/
theorem IsHomogeneous.eq_zero_of_sphereEval_eq_zero {p : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : sphereEval p = 0) : p = 0 := by
  ext m
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff ℝ]
  intro φ
  have hq_eval :
      sphereEval (AddMonoidAlgebra.map φ.toAddMonoidHom p : MvPolynomial σ ℝ) = 0 := by
    ext x
    simp only [sphereEval_addMonoidAlgebra_map_apply, h, ContinuousMap.zero_apply, map_zero]
  have hq0 := eq_zero_of_sphereEval_eq_zero_real (hp.addMonoidAlgebra_map φ.toAddMonoidHom) hq_eval
  simpa using congrArg (fun f : MvPolynomial σ ℝ ↦ f.coeff m) hq0

/-- Homogeneous polynomials of the same degree over a commutative topological `ℝ`-algebra are
determined by their restrictions to the unit sphere. No harmonicity assumption is needed. -/
theorem IsHomogeneous.sphereEval_inj {p q : MvPolynomial σ R} {d : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) :
    sphereEval p = sphereEval q ↔ p = q := by
  refine ⟨fun h ↦ sub_eq_zero.1 <| (hp.sub hq).eq_zero_of_sphereEval_eq_zero ?_, fun h ↦ h ▸ rfl⟩
  ext x
  rw [ContinuousMap.zero_apply, sphereEval_apply, map_sub, ← sphereEval_apply, ← sphereEval_apply,
    h, sub_self]

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

variable {K : Type*} [Field K] [Algebra ℝ K] [TopologicalSpace K]
  [IsTopologicalSemiring K] [ContinuousSMul ℝ K]

/-- The dimension of the space of spherical harmonics of degree `e + 2` in `n` variables is
`n.multichoose (e + 2) - n.multichoose e`. -/
theorem finrank_range_harmonicSphereRestriction_add_two (e : ℕ) :
    Module.finrank K (LinearMap.range (harmonicSphereRestriction (R := K) σ (e + 2))) =
      (Fintype.card σ).multichoose (e + 2) - (Fintype.card σ).multichoose e := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℝ K).injective
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · have hbot : harmonicSubmodule σ K (e + 2) = ⊥ :=
      harmonicSubmodule_succ_eq_bot_of_isEmpty (e + 1)
    have hrange : LinearMap.range (harmonicSphereRestriction (R := K) σ (e + 2)) = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨p, rfl⟩
      have hp : p = 0 := Subtype.ext ((Submodule.mem_bot K).1 (hbot ▸ p.property))
      simp [hp]
    rw [hrange, finrank_bot]
    simp [Fintype.card_eq_zero]
  · rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_add_two]

/-- **Dimension of spherical harmonics on `S^m ⊂ ℝ^(m+1)`**: when `|σ| = m + 1`, the space of
spherical harmonics of degree `d` has dimension `C(m + d, d) - C(m + d - 2, d - 2)`, where the
subtracted term is `0` for `d < 2`. -/
theorem finrank_range_harmonicSphereRestriction_eq_choose_sub {m : ℕ}
    (hσ : Fintype.card σ = m + 1) (d : ℕ) :
    Module.finrank K (LinearMap.range (harmonicSphereRestriction (R := K) σ d)) =
      (m + d).choose d - if 2 ≤ d then (m + d - 2).choose (d - 2) else 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℝ K).injective
  have : Nonempty σ := Fintype.card_pos_iff.1 (by omega)
  rw [finrank_range_harmonicSphereRestriction, finrank_harmonicSubmodule_eq_choose_sub hσ]

/-- Every degree of spherical harmonics has positive dimension on a positive-dimensional sphere. -/
theorem finrank_range_harmonicSphereRestriction_pos {m : ℕ}
    (hσ : Fintype.card σ = m + 1) (d : ℕ) (hm : 1 ≤ m) :
    0 < Module.finrank K (LinearMap.range (harmonicSphereRestriction (R := K) σ d)) := by
  rw [finrank_range_harmonicSphereRestriction_eq_choose_sub hσ]
  split_ifs with hd
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le' hd
    apply Nat.sub_pos_of_lt
    have hpos : 0 < (m + e + 1).choose (e + 1 + 1) := Nat.choose_pos (by omega)
    have hpascal : (m + e + 1 + 1).choose (e + 1 + 1) =
        (m + e).choose e + (m + e).choose (e + 1) + (m + e + 1).choose (e + 1 + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_succ_succ']
    have hlt : (m + e).choose e < (m + e + 1 + 1).choose (e + 1 + 1) := by omega
    rw [show m + (e + 2) - 2 = m + e by omega, Nat.add_sub_cancel]
    simpa only [Nat.add_assoc] using hlt
  · simpa using Nat.choose_pos (show d ≤ m + d by omega)

end Field

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pointwise conjugation of a polynomial function on the real unit sphere is the restriction of
the coefficientwise-conjugated polynomial, since the sphere coordinates are real. -/
theorem star_sphereEval (p : MvPolynomial σ 𝕜) :
    star (sphereEval p) = sphereEval (map (starRingEnd 𝕜) p) := by
  ext x
  rw [ContinuousMap.star_apply, ← starRingEnd_apply, sphereEval_apply, sphereEval_apply, map_eval]
  refine congrArg (eval · (map (starRingEnd 𝕜) p)) (funext fun i ↦ ?_)
  simp

private def sphereEvalStarSubalgebra (σ 𝕜 : Type*) [Fintype σ] [RCLike 𝕜] :
    StarSubalgebra 𝕜 C(Metric.sphere (0 : EuclideanSpace ℝ σ) 1, 𝕜) :=
  { (sphereEval (σ := σ) (R := 𝕜)).range with
    star_mem' := by
      rintro _ ⟨p, rfl⟩
      exact ⟨map (starRingEnd 𝕜) p, (star_sphereEval p).symm⟩ }

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

namespace TauCeti

section LpCompleteness

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- **`Lᵖ` density of spherical harmonics on the unit sphere.** For `[RCLike 𝕜]`, `1 ≤ p < ∞`,
and any finite Borel measure `μ` on the unit sphere `S`, the span of the images in `Lᵖ(S, μ; 𝕜)`
of all harmonic sphere-restriction spaces is dense. -/
theorem topologicalClosure_iSup_map_toLp_harmonicSphereRestriction {σ 𝕜 : Type*} [Fintype σ]
    [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (μ : Measure (Metric.sphere (0 : EuclideanSpace ℝ σ) 1)) [IsFiniteMeasure μ] :
    Submodule.topologicalClosure
      (⨆ d, (LinearMap.range (MvPolynomial.harmonicSphereRestriction (R := 𝕜) σ d)).map
        (ContinuousMap.toLp (E := 𝕜) p μ 𝕜).toLinearMap) = ⊤ := by
  rw [← Submodule.map_iSup]
  exact (ContinuousMap.toLp_denseRange (p := p) 𝕜 μ 𝕜 hp).topologicalClosure_map_submodule
    MvPolynomial.topologicalClosure_iSup_range_harmonicSphereRestriction

/-- An element of `L²(S, μ; 𝕜)` (for any finite Borel measure `μ` on the unit sphere `S`)
orthogonal to all spherical harmonics (of every degree `d : ℕ`) is zero. -/
theorem eq_zero_of_forall_inner_toLp_harmonicSphereRestriction_eq_zero {σ 𝕜 : Type*} [Fintype σ]
    [RCLike 𝕜] {μ : Measure (Metric.sphere (0 : EuclideanSpace ℝ σ) 1)} [IsFiniteMeasure μ]
    {g : Lp 𝕜 2 μ}
    (horth : ∀ (d : ℕ) (p : MvPolynomial.harmonicSubmodule σ 𝕜 d),
      ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜
        (MvPolynomial.harmonicSphereRestriction σ d p), g⟫_𝕜 = 0) :
    g = 0 := by
  let T := ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜
  let W : Submodule 𝕜 (Lp 𝕜 2 μ) :=
    ⨆ d, (LinearMap.range (MvPolynomial.harmonicSphereRestriction (R := 𝕜) σ d)).map T.toLinearMap
  have hg : g ∈ Wᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro d
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
    exact horth d p
  rw [← W.orthogonal_closure,
    topologicalClosure_iSup_map_toLp_harmonicSphereRestriction 2 (by simp) μ,
    Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hg
  exact hg

end LpCompleteness

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hopf reduction: the reduced spaces of `ℂ²` by the diagonal circle

Give `ℂ²` its Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ`, which in the coordinates `z_j = q_j + i p_j` is
`dq₀ ∧ dp₀ + dq₁ ∧ dp₁`. The statements below take any symplectic form `Ω` with this formula, such
as `(AlmostComplexStructure.ofComplexModule ℂ²).symplecticForm`, `⟪i v, w⟫_ℝ`. The diagonal circle
action `z ↦ e^(-iθ) z` is Hamiltonian with moment map `μ(z) = ‖z‖² / 2`
(`TauCeti.hamiltonianVectorField_half_norm_sq_eq_neg_I_smul`). This file computes its
symplectic reductions. For `c ≥ 0` the level `μ⁻¹(c)` is the sphere of radius `√(2c)`, which
`z ↦ √(2c) z` parametrizes by the unit sphere `S³` (`TauCeti.range_smul_coe_sphere`), and the
quotient of the level by the circle is the two-sphere, through the **Hopf map**

`h : S³ → S²`, `h(z) = (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²)`

(`TauCeti.hopfMap`). It is smooth, onto, and a submersion, and its fibres are exactly the circle
orbits `{u z | |u| = 1}` (`TauCeti.hopfMap_eq_hopfMap_iff`). The reduced symplectic form is
computed by the identity

`h^* ((c / 2) σ) = (z ↦ √(2c) z)^* Ω`

on `S³` (`TauCeti.mpullback_smul_coe_sphere_constSmooth`), where
`σ_x(v, w) = x ⬝ (v × w)` is the area form of the unit sphere `S²` (`TauCeti.sphereAreaForm`).
Since `h` is a surjective submersion, `(c / 2) σ` is the only form on `S²` with this property
(`TauCeti.mpullback_hopfMap_eq_iff`): it is the reduced form of the level `c`. As `S²` has area
`4π`, the reduced space has symplectic area `2πc`
(`TauCeti.liouvilleMeasure_univ_of_mpullback_hopfMap_eq`), so the area grows by `2π δ` when the
level grows by `δ`, the Duistermaat–Heckman variation for the Hopf circle bundle.

The pullback identity rests on one polynomial identity. For the quadratic map `F : ℂ² → ℝ³`
underlying `h`, with `α₁ = Re ⟪z, ·⟫_ℂ` and `α₂ = Im ⟪z, ·⟫_ℂ`,

`F(z) ⬝ (dF_z v × dF_z w) = 4 ‖z‖² (‖z‖² Ω(v, w) - α₁(v) α₂(w) + α₂(v) α₁(w))`,

and at a point of `S³` the tangent vectors `v, w` satisfy `α₁(v) = α₁(w) = 0`, so the left side is
`4 Ω(v, w)`. The orientation matters: the conjugate map
`z ↦ (2 Re (z₀ conj z₁), 2 Im (z₀ conj z₁), |z₀|² - |z₁|²)` differs from `h` by a reflection of
`ℝ³`, and reduces `Ω` to `-(c / 2) σ`.

## Main definitions

* `TauCeti.hopfMap`: the Hopf map `S³ → S²`.

## Main results

* `TauCeti.contMDiff_hopfMap`, `TauCeti.hopfMap_surjective`, `TauCeti.mfderiv_hopfMap_surjective`:
  the Hopf map is a smooth surjective submersion.
* `TauCeti.hopfMap_eq_hopfMap_iff`: its fibres are the circle orbits.
* `TauCeti.range_smul_coe_sphere`: `z ↦ √(2c) z` parametrizes the level `‖x‖² / 2 = c`.
* `TauCeti.hamiltonianVectorField_half_norm_sq_eq_neg_I_smul`: `‖x‖² / 2` is the moment map of the
  diagonal circle action.
* `TauCeti.mpullback_smul_coe_sphere_constSmooth`: the reduced form of the level `c` is
  `(c / 2) σ`.
* `TauCeti.mpullback_hopfMap_eq_iff`: it is the unique form with this property.
* `TauCeti.liouvilleMeasure_univ_of_mpullback_hopfMap_eq`: the reduced space has area `2πc`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (symplectic reduction, with the reduction of `ℂⁿ` by the diagonal
  circle to `ℂℙⁿ⁻¹` among its examples) and Section 30.3 (the variation of the reduced
  symplectic volume).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Section 5.4 (symplectic reduction).
-/

public section

noncomputable section

open Metric Module Matrix WithLp Complex Real
open scoped Manifold ContDiff InnerProductSpace ComplexConjugate

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S³" => sphere (0 : ℂ²) 1
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The Hopf map on `ℂ²` -/

/-- The quadratic map `ℂ² → ℝ³` underlying the Hopf map, written in the real coordinates
`z₀ = a + b i`, `z₁ = c + d i`: `(2 (a c + b d), 2 (a d - b c), a² + b² - c² - d²)`, that is
`(2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²)`. -/
private def hopfVec (z : ℂ²) : ℝ³ :=
  toLp 2 ![2 * ((z 0).re * (z 1).re + (z 0).im * (z 1).im),
    2 * ((z 0).re * (z 1).im - (z 0).im * (z 1).re),
    (z 0).re ^ 2 + (z 0).im ^ 2 - (z 1).re ^ 2 - (z 1).im ^ 2]

private theorem norm_sq_eq (z : ℂ²) :
    ‖z‖ ^ 2 = (z 0).re ^ 2 + (z 0).im ^ 2 + ((z 1).re ^ 2 + (z 1).im ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  ring

/-- `‖hopfVec z‖ = ‖z‖²`. -/
private theorem norm_hopfVec (z : ℂ²) : ‖hopfVec z‖ = ‖z‖ ^ 2 := by
  have h : ‖hopfVec z‖ ^ 2 = (‖z‖ ^ 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, norm_sq_eq]
    simp only [hopfVec, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

private theorem hopfVec_mem_sphere (z : S³) : hopfVec z ∈ S² := by
  rw [mem_sphere_zero_iff_norm, norm_hopfVec, norm_eq_of_mem_sphere z, one_pow]

private theorem hasFDerivAt_re (j : Fin 2) (z : ℂ²) :
    HasFDerivAt (fun x : ℂ² ↦ (x j).re)
      (Complex.reCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) j)) z :=
  Complex.reCLM.hasFDerivAt.comp z (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j)

private theorem hasFDerivAt_im (j : Fin 2) (z : ℂ²) :
    HasFDerivAt (fun x : ℂ² ↦ (x j).im)
      (Complex.imCLM.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) j)) z :=
  Complex.imCLM.hasFDerivAt.comp z (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z j)

private theorem contDiff_hopfVec : ContDiff ℝ ∞ hopfVec := by
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  have hre (j : Fin 2) : ContDiff ℝ ∞ (fun x : ℂ² ↦ (x j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_piLp_apply (𝕜 := ℝ) 2)
  have him (j : Fin 2) : ContDiff ℝ ∞ (fun x : ℂ² ↦ (x j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_piLp_apply (𝕜 := ℝ) 2)
  fin_cases i
  · exact contDiff_const.mul (((hre 0).mul (hre 1)).add ((him 0).mul (him 1)))
  · exact contDiff_const.mul (((hre 0).mul (him 1)).sub ((him 0).mul (hre 1)))
  · exact ((((hre 0).pow 2).add ((him 0).pow 2)).sub ((hre 1).pow 2)).sub ((him 1).pow 2)

/-- The derivative of `hopfVec`, in real coordinates. -/
private theorem fderiv_hopfVec_apply (z v : ℂ²) :
    fderiv ℝ hopfVec z v = toLp 2
      ![2 * ((v 0).re * (z 1).re + (z 0).re * (v 1).re + (v 0).im * (z 1).im +
          (z 0).im * (v 1).im),
        2 * ((v 0).re * (z 1).im + (z 0).re * (v 1).im - (v 0).im * (z 1).re -
          (z 0).im * (v 1).re),
        2 * ((z 0).re * (v 0).re + (z 0).im * (v 0).im - (z 1).re * (v 1).re -
          (z 1).im * (v 1).im)] := by
  have hd := (contDiff_hopfVec.differentiable (by simp) z).hasFDerivAt
  have key (i : Fin 3) (D : ℂ² →L[ℝ] ℝ) (hD : HasFDerivAt (fun x ↦ hopfVec x i) D z) :
      fderiv ℝ hopfVec z v i = D v :=
    congrArg (· v) (((EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ).hasFDerivAt.comp z hd).unique hD)
  ext i
  fin_cases i
  · refine (key 0 _ ((((hasFDerivAt_re 0 z).mul (hasFDerivAt_re 1 z)).add
      ((hasFDerivAt_im 0 z).mul (hasFDerivAt_im 1 z))).const_mul 2)).trans ?_
    simp
    ring
  · refine (key 1 _ ((((hasFDerivAt_re 0 z).mul (hasFDerivAt_im 1 z)).sub
      ((hasFDerivAt_im 0 z).mul (hasFDerivAt_re 1 z))).const_mul 2)).trans ?_
    simp
    ring
  · refine (key 2 _ (((((hasFDerivAt_re 0 z).pow 2).add ((hasFDerivAt_im 0 z).pow 2)).sub
      ((hasFDerivAt_re 1 z).pow 2)).sub ((hasFDerivAt_im 1 z).pow 2))).trans ?_
    simp
    ring

private theorem inner_re (z v : ℂ²) :
    (⟪z, v⟫_ℂ).re = (z 0).re * (v 0).re + (z 0).im * (v 0).im + ((z 1).re * (v 1).re +
      (z 1).im * (v 1).im) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, Complex.mul_re]
  ring

private theorem inner_im (z v : ℂ²) :
    (⟪z, v⟫_ℂ).im = (z 0).re * (v 0).im - (z 0).im * (v 0).re + ((z 1).re * (v 1).im -
      (z 1).im * (v 1).re) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, Complex.mul_im]
  ring

/-- The triple product of `hopfVec z` with two of its derivatives at `z`. -/
private theorem dotProduct_cross_fderiv_hopfVec (z v w : ℂ²) :
    (hopfVec z).ofLp ⬝ᵥ (fderiv ℝ hopfVec z v).ofLp ⨯₃ (fderiv ℝ hopfVec z w).ofLp =
      4 * ‖z‖ ^ 2 * (‖z‖ ^ 2 * (⟪v, w⟫_ℂ).im - (⟪z, v⟫_ℂ).re * (⟪z, w⟫_ℂ).im +
        (⟪z, v⟫_ℂ).im * (⟪z, w⟫_ℂ).re) := by
  rw [fderiv_hopfVec_apply, fderiv_hopfVec_apply, norm_sq_eq, inner_re, inner_re, inner_im,
    inner_im, inner_im]
  simp only [hopfVec, cross_apply, dotProduct, Fin.sum_univ_three, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- A tangent vector of `S³` at `z`, read in `ℂ²`, is real-orthogonal to `z`. -/
private theorem re_inner_mvfderiv_coe (z : S³) (v : TangentSpace (𝓡 3) z) :
    (⟪(z : ℂ²), mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v⟫_ℂ).re = 0 := by
  have h : mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v ∈ (ℝ ∙ (z : ℂ²))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := 3)]
    exact LinearMap.mem_range_self _ v
  rw [← EuclideanSpace.real_inner_eq_re_inner]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _) h

/-- Every vector of `ℂ²` real-orthogonal to `z ∈ S³` is a tangent vector of `S³` at `z`. -/
private theorem exists_mvfderiv_coe_eq (z : S³) {u : ℂ²} (hu : (⟪(z : ℂ²), u⟫_ℂ).re = 0) :
    ∃ v : TangentSpace (𝓡 3) z, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v = u := by
  have h : u ∈ (ℝ ∙ (z : ℂ²))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
      EuclideanSpace.real_inner_eq_re_inner, hu]
  rw [← range_mvfderiv_subtypeVal (n := 3)] at h
  exact h

/-! ### The Hopf map `S³ → S²` -/

/-- The **Hopf map** `S³ → S²`, `z ↦ (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²)`
(`TauCeti.coe_hopfMap`). Its fibres are the orbits of the diagonal circle action
`z ↦ u z` (`TauCeti.hopfMap_eq_hopfMap_iff`), it is onto (`TauCeti.hopfMap_surjective`), and it is
a submersion (`TauCeti.mfderiv_hopfMap_surjective`). -/
def hopfMap : S³ → S² :=
  Set.codRestrict (fun z : S³ ↦ hopfVec z) _ hopfVec_mem_sphere

private theorem coe_hopfMap_eq_hopfVec (z : S³) : (hopfMap z : ℝ³) = hopfVec z :=
  Set.val_codRestrict_apply _ _ _ _

/-- The Hopf map, read in `ℝ³`. -/
@[simp]
theorem coe_hopfMap (z : S³) :
    (hopfMap z : ℝ³) = toLp 2 ![2 * (conj ((z : ℂ²) 0) * (z : ℂ²) 1).re,
      2 * (conj ((z : ℂ²) 0) * (z : ℂ²) 1).im,
      Complex.normSq ((z : ℂ²) 0) - Complex.normSq ((z : ℂ²) 1)] := by
  ext i
  fin_cases i <;>
    simp [hopfMap, hopfVec, Complex.mul_re, Complex.mul_im, Complex.normSq_apply] <;> ring

/-- The Hopf map is smooth. -/
theorem contMDiff_hopfMap : ContMDiff (𝓡 3) (𝓡 2) ∞ hopfMap :=
  ContMDiff.codRestrict_sphere (contDiff_hopfVec.contMDiff.comp contMDiff_coe_sphere) _

/-- Read in `ℂ²` and `ℝ³`, the differential of the Hopf map is the derivative of `hopfVec`. -/
private theorem mvfderiv_coe_mfderiv_hopfMap (z : S³) (v : TangentSpace (𝓡 3) z) :
    mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (hopfMap z) (mfderiv (𝓡 3) (𝓡 2) hopfMap z v) =
      fderiv ℝ hopfVec z (mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v) := by
  rw [← mvfderiv_comp_apply z ((contMDiff_coe_sphere (n := 2) (m := 1) _).mdifferentiableAt
      one_ne_zero) ((contMDiff_hopfMap z).mdifferentiableAt (by simp)) v]
  have hcomp : ((↑) : S² → ℝ³) ∘ hopfMap = hopfVec ∘ ((↑) : S³ → ℂ²) :=
    funext (Set.val_codRestrict_apply _ _ _)
  rw [hcomp, mvfderiv_comp_apply_of_differentiableAt
    (contDiff_hopfVec.differentiable (by simp) _)
    ((contMDiff_coe_sphere (n := 3) (m := 1) z).mdifferentiableAt one_ne_zero)]

/-- **The Hopf map pulls the area form of `S²` back to four times `Im ⟪·, ·⟫_ℂ`.** For tangent
vectors `v, w` of `S³` at `z`, `σ(dh v, dh w) = 4 Im ⟪v, w⟫_ℂ`. -/
private theorem eval₂_sphereAreaForm_mfderiv_hopfMap (z : S³) (v w : TangentSpace (𝓡 3) z) :
    SmoothBundleForm.eval₂ sphereAreaForm (hopfMap z) (mfderiv (𝓡 3) (𝓡 2) hopfMap z v)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap z w) =
      4 * (⟪mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z w⟫_ℂ).im := by
  rw [eval₂_sphereAreaForm, mvfderiv_coe_mfderiv_hopfMap, mvfderiv_coe_mfderiv_hopfMap,
    coe_hopfMap_eq_hopfVec, dotProduct_cross_fderiv_hopfVec,
    re_inner_mvfderiv_coe, re_inner_mvfderiv_coe, norm_eq_of_mem_sphere z]
  ring

/-- On `S³`, `|z₀|² + |z₁|² = 1`. -/
private theorem normSq_add_normSq (z : S³) :
    Complex.normSq ((z : ℂ²) 0) + Complex.normSq ((z : ℂ²) 1) = 1 := by
  have h2 : ‖(z : ℂ²)‖ ^ 2 = 1 := by rw [norm_eq_of_mem_sphere z, one_pow]
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two] at h2
  simpa [Complex.normSq_eq_norm_sq] using h2

/-- Points of `S³` with the same image under the Hopf map differ by the phase `⟪z, w⟫_ℂ`. -/
private theorem exists_coe_eq_smul_of_hopfMap_eq {z w : S³} (h : hopfMap z = hopfMap w) :
    ∃ u : Circle, (w : ℂ²) = (u : ℂ) • (z : ℂ²) := by
  have hc (i : Fin 3) := congrArg (fun q : S² ↦ (q : ℝ³) i) h
  simp only [coe_hopfMap, PiLp.toLp_apply] at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hz := normSq_add_normSq z
  have hw := normSq_add_normSq w
  set a := (z : ℂ²) 0
  set b := (z : ℂ²) 1
  set a' := (w : ℂ²) 0
  set b' := (w : ℂ²) 1
  -- The Hopf map remembers `conj z₀ z₁` and the two moduli `|z₀|²`, `|z₁|²`.
  have hP : conj a * b = conj a' * b' := Complex.ext (by linarith) (by linarith)
  have hP' : a * conj b = a' * conj b' := by
    simpa [mul_comm] using congrArg conj hP
  have ha : conj a * a = conj a' * a' := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    exact congrArg _ (by linarith)
  have hb : conj b * b = conj b' * b' := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    exact congrArg _ (by linarith)
  have hw' : conj a' * a' + conj b' * b' = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast hw
  -- The phase is `u = ⟪z, w⟫ = conj z₀ w₀ + conj z₁ w₁`.
  set u := conj a * a' + conj b * b'
  have e0 : a' = u * a := by linear_combination (-a') * ha - b' * hP' - a' * hw'
  have e1 : b' = u * b := by linear_combination (-a') * hP - b' * hb - b' * hw'
  have hu : (w : ℂ²) = u • (z : ℂ²) := by
    ext j
    fin_cases j
    exacts [e0, e1]
  have hnorm : ‖u‖ = 1 := by
    have := congrArg norm hu
    rwa [norm_smul, norm_eq_of_mem_sphere z, norm_eq_of_mem_sphere w, mul_one, eq_comm] at this
  exact ⟨⟨u, mem_sphere_zero_iff_norm.2 hnorm⟩, hu⟩

/-- The Hopf map is constant on circle orbits. -/
private theorem hopfMap_eq_of_coe_eq_smul {z w : S³} {u : Circle}
    (hu : (w : ℂ²) = (u : ℂ) • (z : ℂ²)) : hopfMap z = hopfMap w := by
  refine Subtype.ext ?_
  have hu' : conj (u : ℂ) * u = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Circle.normSq_coe, ofReal_one]
  have key : conj (u : ℂ) * conj ((z : ℂ²) 0) * ((u : ℂ) * (z : ℂ²) 1) =
      conj ((z : ℂ²) 0) * (z : ℂ²) 1 := by
    linear_combination (conj ((z : ℂ²) 0) * (z : ℂ²) 1) * hu'
  rw [coe_hopfMap, coe_hopfMap, hu]
  simp only [PiLp.smul_apply, smul_eq_mul, key, map_mul, Circle.normSq_coe, one_mul]

/-- **The fibres of the Hopf map are the circle orbits**: `h z = h w` exactly when `w = u z` for a
unit complex number `u`. -/
theorem hopfMap_eq_hopfMap_iff {z w : S³} :
    hopfMap z = hopfMap w ↔ ∃ u : Circle, (w : ℂ²) = (u : ℂ) • (z : ℂ²) :=
  ⟨exists_coe_eq_smul_of_hopfMap_eq, fun ⟨_, hu⟩ ↦ hopfMap_eq_of_coe_eq_smul hu⟩

/-- A point of `ℂ²` with `|z₀|² + |z₁|² = 1`, in real coordinates, lies on `S³`. -/
private theorem mem_sphere_of_sq {z : ℂ²}
    (h : (z 0).re ^ 2 + (z 0).im ^ 2 + ((z 1).re ^ 2 + (z 1).im ^ 2) = 1) : z ∈ S³ := by
  rw [mem_sphere_zero_iff_norm, ← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero,
    norm_sq_eq, h, one_pow]

/-- The Hopf map is onto. Over a point `(x, y, t)` of `S²` with `t ≠ -1` lies
`(r, (x + y i) / (2 r))` with `r = √((1 + t) / 2)`, and over the south pole lies `(0, 1)`. -/
theorem hopfMap_surjective : Function.Surjective hopfMap := by
  intro p
  have hp : (p : ℝ³) 0 ^ 2 + (p : ℝ³) 1 ^ 2 + (p : ℝ³) 2 ^ 2 = 1 := by
    have h := norm_eq_of_mem_sphere p
    rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, one_pow,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three] at h
    simpa using h
  by_cases ht : (p : ℝ³) 2 = -1
  · have hx : (p : ℝ³) 0 = 0 := by nlinarith
    have hy : (p : ℝ³) 1 = 0 := by nlinarith
    let z : ℂ² := toLp 2 ![0, 1]
    refine ⟨⟨z, mem_sphere_of_sq (by simp [z])⟩, Subtype.ext ?_⟩
    rw [coe_hopfMap_eq_hopfVec]
    ext i
    fin_cases i <;> simp [hopfVec, z, hx, hy, ht]
  · have h1t : 0 < 1 + (p : ℝ³) 2 := by
      rcases lt_or_gt_of_ne ht with h | h
      · nlinarith
      · linarith
    set r := √((1 + (p : ℝ³) 2) / 2)
    have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
    have hr2 : r ^ 2 = (1 + (p : ℝ³) 2) / 2 := Real.sq_sqrt (by linarith)
    let z : ℂ² := toLp 2 ![(r : ℂ), ⟨(p : ℝ³) 0 / (2 * r), (p : ℝ³) 1 / (2 * r)⟩]
    have hz : z ∈ S³ := by
      refine mem_sphere_of_sq ?_
      simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, ofReal_re, ofReal_im]
      field_simp
      nlinarith
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    rw [coe_hopfMap_eq_hopfVec]
    ext i
    fin_cases i
    · simp [hopfVec, z]
      field_simp
    · simp [hopfVec, z]
      field_simp
    · simp [hopfVec, z]
      field_simp
      linear_combination (4 * r ^ 2 + 2 * (1 + (p : ℝ³) 2) - 4 * (p : ℝ³) 2) * hr2 - hp

/-- **The Hopf map is a submersion.** At `z ∈ S³`, the vectors `u = (-conj z₁, conj z₀)` and `i u`
are tangent to `S³`, and the area form pairs their images to `4 ‖u‖² = 4`, so the images span the
tangent plane of `S²`. -/
theorem mfderiv_hopfMap_surjective (z : S³) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) hopfMap z) := by
  set u : ℂ² := toLp 2 ![-conj ((z : ℂ²) 1), conj ((z : ℂ²) 0)]
  have hu : (⟪(z : ℂ²), u⟫_ℂ).re = 0 := by
    rw [inner_re]
    simp [u]
    ring
  have hIu : (⟪(z : ℂ²), I • u⟫_ℂ).re = 0 := by
    rw [inner_re]
    simp [u]
    ring
  have hnorm : ‖u‖ ^ 2 = 1 := by
    rw [norm_sq_eq, ← normSq_add_normSq z]
    simp [u, Complex.normSq_apply]
    ring
  obtain ⟨a, ha⟩ := exists_mvfderiv_coe_eq z hu
  obtain ⟨b, hb⟩ := exists_mvfderiv_coe_eq z hIu
  have hI : (⟪u, I • u⟫_ℂ).im = 1 := by
    rw [inner_smul_right, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      zero_add, ← hnorm]
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
  have hab : sphereAreaForm.bilinFormAt (hopfMap z)
      ((1 / 4 : ℝ) • mfderiv (𝓡 3) (𝓡 2) hopfMap z a) (mfderiv (𝓡 3) (𝓡 2) hopfMap z b) = 1 := by
    rw [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_smul_left,
      eval₂_sphereAreaForm_mfderiv_hopfMap, ha, hb, hI, smul_eq_mul]
    norm_num
  have hspan := ((SmoothForm.isAlt_bilinFormAt _ _).linearIndependent_pair_of_apply_eq_one
    hab).span_eq_top_of_card_eq_finrank (by simp)
  refine LinearMap.range_eq_top.1 (eq_top_iff.2 (hspan ▸ Submodule.span_le.2 ?_))
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact ⟨b, rfl⟩
  · exact ⟨(1 / 4 : ℝ) • a, map_smul _ _ _⟩

/-! ### The reduced space of a level -/

/-- **`‖x‖² / 2` generates the reversed diagonal rotation.** For a symplectic form `Ω` on
`EuclideanSpace ℂ ι` with `Ω(v, w) = Im ⟪v, w⟫_ℂ`, and the convention `ι_(X_H) Ω = dH`, the
Hamiltonian vector field of `‖x‖² / 2` is `-i x`, the generator of the circle action
`x ↦ e^(-iθ) x`. So `‖x‖² / 2` is the moment map of that action. -/
theorem hamiltonianVectorField_half_norm_sq_eq_neg_I_smul {ι : Type*} [Fintype ι]
    {Ω : SymplecticForm (EuclideanSpace ℂ ι)} (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    (x : EuclideanSpace ℂ ι) :
    Ω.hamiltonianVectorField (fun y ↦ ‖y‖ ^ 2 / 2) x = -(I • x) := by
  refine ((Ω.eq_hamiltonianVectorField_iff _ x _).2 fun v ↦ ?_).symm
  have hd : HasFDerivAt (fun y : EuclideanSpace ℂ ι ↦ ‖y‖ ^ 2 / 2) (innerSL ℝ x) x := by
    convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.mul_const (1 / 2 : ℝ) using 1
    · ext y
      ring
    · ext v
      simp
  rw [hd.fderiv, innerSL_apply_apply, EuclideanSpace.real_inner_eq_re_inner, hΩ, inner_neg_left,
    inner_smul_left]
  simp

/-- The parametrization `z ↦ √(2c) z` of the level `‖x‖² / 2 = c` of `ℂ²` by `S³` is smooth. -/
theorem contMDiff_smul_coe_sphere (c : ℝ) :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℂ²) ∞ (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) :=
  (√(2 * c) • ContinuousLinearMap.id ℝ ℂ²).contMDiff.comp contMDiff_coe_sphere

/-- For `c ≥ 0`, the map `z ↦ √(2c) z` carries `S³` onto the level `‖x‖² / 2 = c` of `ℂ²`. -/
theorem range_smul_coe_sphere {c : ℝ} (hc : 0 ≤ c) :
    Set.range (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) = {x : ℂ² | ‖x‖ ^ 2 / 2 = c} := by
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨z, rfl⟩
    rw [norm_smul, norm_eq_of_mem_sphere z, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (by positivity)]
    ring
  · intro hx
    rcases eq_or_lt_of_le hc with rfl | hc
    · refine ⟨⟨EuclideanSpace.single 0 1, by simp⟩, ?_⟩
      have : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
      simp [norm_eq_zero.1 this]
    · have hr : 0 < √(2 * c) := Real.sqrt_pos.2 (by positivity)
      have hn : ‖x‖ = √(2 * c) := by
        rw [← Real.sqrt_sq (norm_nonneg x)]
        congr 1
        linarith
      refine ⟨⟨(√(2 * c))⁻¹ • x, ?_⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), hn,
          inv_mul_cancel₀ hr.ne']
      · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

/-- **Hopf reduction.** For `c ≥ 0`, the Kähler form `Ω = Im ⟪v, w⟫_ℂ` of `ℂ²` restricted to the
level `‖x‖² / 2 = c`, parametrized by `z ↦ √(2c) z`, is the pullback along the Hopf map of `c / 2`
times the area form `σ` of `S²`. In other words, the level data `(z ↦ √(2c) z, hopfMap)` of the
reversed diagonal circle action reduce the Kähler form to `(c / 2) σ`. -/
theorem mpullback_smul_coe_sphere_constSmooth {Ω : SymplecticForm ℂ²}
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} (hc : 0 ≤ c) :
    SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) (contMDiff_smul_coe_sphere c)
        Ω.constSmooth =
      SmoothForm.mpullback hopfMap contMDiff_hopfMap ((c / 2) • sphereAreaForm) := by
  refine Subtype.ext (funext fun z ↦ ?_)
  ext v
  have hv : v = ![v 0, v 1] := by
    ext i
    fin_cases i <;> rfl
  have hd (u : TangentSpace (𝓡 3) z) :
      mvfderiv (𝓡 3) (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) z u =
        √(2 * c) • mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z u :=
    (√(2 * c) • ContinuousLinearMap.id ℝ ℂ²).mvfderiv_comp_apply
      ((contMDiff_coe_sphere (n := 3) (m := 1) z).mdifferentiableAt one_ne_zero) u
  rw [hv, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback]
  refine (SymplecticForm.eval₂_constSmooth_mfderiv_eq Ω
    (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) z _ _).trans ?_
  have hσ : SmoothBundleForm.eval₂ ((c / 2) • sphereAreaForm) (hopfMap z)
      (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 0)) (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 1)) =
      c / 2 * SmoothBundleForm.eval₂ sphereAreaForm (hopfMap z)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 0)) (mfderiv (𝓡 3) (𝓡 2) hopfMap z (v 1)) := by
    simp [SmoothBundleForm.eval₂_apply]
  have hsmul (a b : ℂ²) : Ω (√(2 * c) • a) (√(2 * c) • b) =
      √(2 * c) * √(2 * c) * (⟪a, b⟫_ℂ).im := by
    simp [hΩ, mul_assoc]
  rw [hd, hd, hσ, eval₂_sphereAreaForm_mfderiv_hopfMap, hsmul, Real.mul_self_sqrt (by positivity)]
  ring

/-- **The reduced form of Hopf reduction is `(c / 2) σ`.** For `c ≥ 0`, a two-form `η` on `S²`
pulls back along the Hopf map to the restriction of the Kähler form `Ω` of `ℂ²` to the level
`‖x‖² / 2 = c` exactly when `η` is `c / 2` times the area form. -/
theorem mpullback_hopfMap_eq_iff {Ω : SymplecticForm ℂ²} (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    {c : ℝ} (hc : 0 ≤ c) {η : SmoothTwoForm (𝓡 2) S²} :
    SmoothForm.mpullback hopfMap contMDiff_hopfMap η =
        SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) (contMDiff_smul_coe_sphere c)
          Ω.constSmooth ↔
      η = (c / 2) • sphereAreaForm := by
  rw [mpullback_smul_coe_sphere_constSmooth hΩ hc]
  exact (SmoothForm.mpullback_injective_of_surjective contMDiff_hopfMap hopfMap_surjective
    mfderiv_hopfMap_surjective).eq_iff

/-- **The reduced space of the level `c` has area `2πc`.** For `c ≥ 0`, the reduced form `η` of
Hopf reduction at the level `‖x‖² / 2 = c` of `ℂ²` gives `S²` the symplectic area `2πc`. -/
theorem liouvilleMeasure_univ_of_mpullback_hopfMap_eq {Ω : SymplecticForm ℂ²}
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} (hc : 0 ≤ c) {η : SmoothTwoForm (𝓡 2) S²}
    (hη : SmoothForm.mpullback hopfMap contMDiff_hopfMap η =
      SmoothForm.mpullback (fun z : S³ ↦ √(2 * c) • (z : ℂ²)) (contMDiff_smul_coe_sphere c)
        Ω.constSmooth) :
    η.liouvilleMeasure 1 Set.univ = ENNReal.ofReal (2 * π * c) := by
  rw [(mpullback_hopfMap_eq_iff hΩ hc).1 hη, liouvilleMeasure_smul_sphereAreaForm_univ,
    abs_of_nonneg (by positivity)]
  congr 1
  ring

end TauCeti

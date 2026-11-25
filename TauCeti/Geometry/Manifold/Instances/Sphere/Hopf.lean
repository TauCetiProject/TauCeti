/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.CrossProduct
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# The Hopf map `S³ → S²`

The **Hopf map** is

`h : S³ → S²`, `h(z) = (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²)`

on the unit sphere `S³` of `ℂ²` (`TauCeti.hopfMap`). It is smooth and onto, and its fibres are
exactly the orbits `{u z | |u| = 1}` of the diagonal circle action
(`TauCeti.hopfMap_eq_hopfMap_iff`). Its differential multiplies oriented area by four: for
tangent vectors `v, w` of `S³` at `z`,

`h(z) ⬝ (dh v × dh w) = 4 Im ⟪v, w⟫_ℂ`

(`TauCeti.dotProduct_cross_mvfderiv_coe_mfderiv_hopfMap`). This rests on one polynomial identity.
For the quadratic map `F : ℂ² → ℝ³` underlying `h`, with `α₁ = Re ⟪z, ·⟫_ℂ` and
`α₂ = Im ⟪z, ·⟫_ℂ`,

`F(z) ⬝ (dF_z v × dF_z w) = 4 ‖z‖² (‖z‖² Im ⟪v, w⟫_ℂ - α₁(v) α₂(w) + α₂(v) α₁(w))`,

and at a point of `S³` the tangent vectors `v, w` satisfy `α₁(v) = α₁(w) = 0`. The orientation
matters: the conjugate map `z ↦ (2 Re (z₀ conj z₁), 2 Im (z₀ conj z₁), |z₀|² - |z₁|²)` differs
from `h` by a reflection of `ℝ³`, which reverses the sign of the triple product.

## Main definitions

* `TauCeti.hopfMap`: the Hopf map `S³ → S²`.

## Main results

* `TauCeti.contMDiff_hopfMap`, `TauCeti.hopfMap_surjective`: the Hopf map is smooth and onto.
* `TauCeti.hopfMap_eq_hopfMap_iff`: its fibres are the circle orbits.
* `TauCeti.dotProduct_cross_mvfderiv_coe_mfderiv_hopfMap`: its differential multiplies oriented
  area by four.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (the Hopf fibration as the quotient of `S³` by the diagonal circle).
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

/-! ### The quadratic map underlying the Hopf map -/

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

/-! ### The Hopf map `S³ → S²` -/

/-- The **Hopf map** `S³ → S²`, `z ↦ (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²)`
(`TauCeti.coe_hopfMap`). Its fibres are the orbits of the diagonal circle action
`z ↦ u z` (`TauCeti.hopfMap_eq_hopfMap_iff`), and it is onto (`TauCeti.hopfMap_surjective`). -/
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


/-- **The Hopf map multiplies oriented area by four.** For tangent vectors `v, w` of `S³` at `z`,
read in `ℂ²` and `ℝ³`, the triple product `h(z) ⬝ (dh v × dh w)` is `4 Im ⟪v, w⟫_ℂ`. -/
theorem dotProduct_cross_mvfderiv_coe_mfderiv_hopfMap (z : S³) (v w : TangentSpace (𝓡 3) z) :
    ofLp (hopfMap z : ℝ³) ⬝ᵥ
        ofLp (mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (hopfMap z) (mfderiv (𝓡 3) (𝓡 2) hopfMap z v)) ⨯₃
          ofLp (mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (hopfMap z) (mfderiv (𝓡 3) (𝓡 2) hopfMap z w)) =
      4 * (⟪mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z w⟫_ℂ).im := by
  rw [mvfderiv_coe_mfderiv_hopfMap, mvfderiv_coe_mfderiv_hopfMap, coe_hopfMap_eq_hopfVec,
    dotProduct_cross_fderiv_hopfVec, ← EuclideanSpace.real_inner_eq_re_inner,
    ← EuclideanSpace.real_inner_eq_re_inner, inner_coe_mvfderiv_subtypeVal_sphere,
    inner_coe_mvfderiv_subtypeVal_sphere, norm_eq_of_mem_sphere z]
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

end TauCeti

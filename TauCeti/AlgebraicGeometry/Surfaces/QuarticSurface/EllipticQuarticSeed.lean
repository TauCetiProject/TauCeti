/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus

/-!
# A smooth quartic surface containing two disjoint lines

In complex projective space `ℂℙ³`, with homogeneous coordinates `z₀, z₁, z₂, z₃`, consider the
two disjoint lines `L₀ = {z₂ = z₃ = 0}` and `L₁ = {z₀ = z₁ = 0}`. The quartic

`F₀ = z₀³ z₂ + z₂³ z₁ + z₁³ z₃ + z₃³ z₀`

(`TauCeti.ellipticQuarticSeedPolynomial`) vanishes on both lines, since each of its monomials
involves a coordinate from each pair `{z₀, z₁}` and `{z₂, z₃}`. This file proves that the quartic
surface `F₀ = 0` is smooth: no nonzero vector of `ℂ⁴` is a common zero of the four partial
derivatives of `F₀`, even off the zero locus. Consequently the derivative of the evaluation map
`ℂ⁴ → ℂ` of `F₀` (`TauCeti.ellipticQuarticSeedMap`) is surjective at every nonzero vector, and the
cone Jacobian of `F₀` has full rank there, which is the hypothesis of the complex manifold
structure on smooth projective zero loci.

A smooth quartic surface containing two disjoint lines `L₀` and `L₁` carries an elliptic
fibration: the planes through `L₀` cut out, besides `L₀`, a pencil of plane cubics, and `L₁` meets
each of these planes in one point, giving a section. In this way smooth quartic surfaces, the K3
surfaces of degree four, are compared with the elliptic surface `E(2)`. Full rank of the cone
Jacobian at every nonzero common zero is an open condition on the coefficients
(`TauCeti.isOpen_setOfPred_forall_mulVec_surjective_jacobiMatrixAt`), and `F₀` satisfies it, so
the quartics containing `L₀` and `L₁` with coefficients near those of `F₀` are smooth as well.

The four partial derivatives are cyclic in the order `z₀ → z₂ → z₁ → z₃ → z₀`:

* `∂F₀/∂z₀ = 3 z₀² z₂ + z₃³`, `∂F₀/∂z₁ = z₂³ + 3 z₁² z₃`,
* `∂F₀/∂z₂ = z₀³ + 3 z₂² z₁`, `∂F₀/∂z₃ = z₁³ + 3 z₃² z₀`.

At a common zero, if some coordinate vanishes then so does the next one in the reversed cycle
`z₀ → z₃ → z₁ → z₂ → z₀`, so all coordinates vanish. If none vanishes, multiplying the four
relations `z₃³ = -3 z₀² z₂`, `z₂³ = -3 z₁² z₃`, `z₀³ = -3 z₂² z₁` and `z₁³ = -3 z₃² z₀` gives
`(z₀ z₁ z₂ z₃)³ = 81 (z₀ z₁ z₂ z₃)³`, which is impossible.

## Main definitions

* `TauCeti.ellipticQuarticSeedPolynomial`: the quartic `z₀³ z₂ + z₂³ z₁ + z₁³ z₃ + z₃³ z₀`.
* `TauCeti.ellipticQuarticSeedMap`: its evaluation map `ℂ⁴ → ℂ`.

## Main results

* `TauCeti.ellipticQuarticSeedMap_smul`: evaluation scales by the fourth power of a scalar.
* `TauCeti.ellipticQuarticSeedMap_eq_zero_of_apply_two_eq_zero_of_apply_three_eq_zero` and
  `TauCeti.ellipticQuarticSeedMap_eq_zero_of_apply_zero_eq_zero_of_apply_one_eq_zero`: the
  quartic vanishes on the cones over `L₀` and `L₁`.
* `TauCeti.mk_mem_complexProjectiveZeroLocus_ellipticQuarticSeedPolynomial_iff`: a projective
  point lies on the quartic surface exactly when the evaluation map vanishes at a representative.
* `TauCeti.exists_eval_pderiv_ellipticQuarticSeedPolynomial_ne_zero`: the partial derivatives
  have no common nonzero zero.
* `TauCeti.mulVec_surjective_jacobiMatrixAt_ellipticQuarticSeedPolynomial`: the cone Jacobian is
  surjective at every nonzero vector.
* `TauCeti.ellipticQuarticSeedMap_fderiv_surjective`: the derivative of the evaluation map is
  surjective at every nonzero vector.

## References

* R. E. Gompf and A. I. Stipsicz, *4-Manifolds and Kirby Calculus*, Graduate Studies in
  Mathematics 20, American Mathematical Society, 1999, §3.1, for elliptic surfaces and `E(2)`.
* M. J. D. Hamilton, *On symplectic 4-manifolds and contact 5-manifolds*, PhD thesis, LMU
  München, 2008, §II.3.4–§II.3.5, for the identification of `E(2)` with the K3 surface.
-/

public section

open MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace TauCeti

/-- The quartic `z₀³ z₂ + z₂³ z₁ + z₁³ z₃ + z₃³ z₀` in four complex variables. It vanishes on the
disjoint coordinate lines `{z₂ = z₃ = 0}` and `{z₀ = z₁ = 0}` of `ℂℙ³`, and its zero locus is a
smooth quartic surface. -/
noncomputable def ellipticQuarticSeedPolynomial : MvPolynomial (Fin 4) ℂ :=
  X 0 ^ 3 * X 2 + X 2 ^ 3 * X 1 + X 1 ^ 3 * X 3 + X 3 ^ 3 * X 0

/-- The quartic `ellipticQuarticSeedPolynomial` as an explicit polynomial. -/
theorem ellipticQuarticSeedPolynomial_def :
    ellipticQuarticSeedPolynomial = X 0 ^ 3 * X 2 + X 2 ^ 3 * X 1 + X 1 ^ 3 * X 3 + X 3 ^ 3 * X 0 :=
  (rfl)

/-- The quartic `ellipticQuarticSeedPolynomial` is homogeneous of degree `4`. -/
theorem isHomogeneous_ellipticQuarticSeedPolynomial :
    ellipticQuarticSeedPolynomial.IsHomogeneous 4 :=
  (((((isHomogeneous_X ℂ 0).pow 3).mul (isHomogeneous_X ℂ 2)).add
    (((isHomogeneous_X ℂ 2).pow 3).mul (isHomogeneous_X ℂ 1))).add
    (((isHomogeneous_X ℂ 1).pow 3).mul (isHomogeneous_X ℂ 3))).add
    (((isHomogeneous_X ℂ 3).pow 3).mul (isHomogeneous_X ℂ 0))

/-- The value of `ellipticQuarticSeedPolynomial` at a vector `v`. -/
@[simp]
theorem eval_ellipticQuarticSeedPolynomial (v : Fin 4 → ℂ) :
    eval v ellipticQuarticSeedPolynomial =
      v 0 ^ 3 * v 2 + v 2 ^ 3 * v 1 + v 1 ^ 3 * v 3 + v 3 ^ 3 * v 0 := by
  simp [ellipticQuarticSeedPolynomial]

/-- The partial derivative `∂/∂z₀ = 3 z₀² z₂ + z₃³` of `ellipticQuarticSeedPolynomial` at `v`. -/
@[simp]
theorem eval_pderiv_zero_ellipticQuarticSeedPolynomial (v : Fin 4 → ℂ) :
    eval v (pderiv 0 ellipticQuarticSeedPolynomial) = 3 * v 0 ^ 2 * v 2 + v 3 ^ 3 := by
  simp [ellipticQuarticSeedPolynomial, pderiv_X]
  ring

/-- The partial derivative `∂/∂z₁ = z₂³ + 3 z₁² z₃` of `ellipticQuarticSeedPolynomial` at `v`. -/
@[simp]
theorem eval_pderiv_one_ellipticQuarticSeedPolynomial (v : Fin 4 → ℂ) :
    eval v (pderiv 1 ellipticQuarticSeedPolynomial) = v 2 ^ 3 + 3 * v 1 ^ 2 * v 3 := by
  simp [ellipticQuarticSeedPolynomial, pderiv_X]
  ring

/-- The partial derivative `∂/∂z₂ = z₀³ + 3 z₂² z₁` of `ellipticQuarticSeedPolynomial` at `v`. -/
@[simp]
theorem eval_pderiv_two_ellipticQuarticSeedPolynomial (v : Fin 4 → ℂ) :
    eval v (pderiv 2 ellipticQuarticSeedPolynomial) = v 0 ^ 3 + 3 * v 2 ^ 2 * v 1 := by
  simp [ellipticQuarticSeedPolynomial, pderiv_X]
  ring

/-- The partial derivative `∂/∂z₃ = z₁³ + 3 z₃² z₀` of `ellipticQuarticSeedPolynomial` at `v`. -/
@[simp]
theorem eval_pderiv_three_ellipticQuarticSeedPolynomial (v : Fin 4 → ℂ) :
    eval v (pderiv 3 ellipticQuarticSeedPolynomial) = v 1 ^ 3 + 3 * v 3 ^ 2 * v 0 := by
  simp [ellipticQuarticSeedPolynomial, pderiv_X]
  ring

/-- **The partial derivatives of the seed quartic have no common nonzero zero.** At every nonzero
vector of `ℂ⁴`, whether or not it lies on the quartic, some partial derivative of
`ellipticQuarticSeedPolynomial` is nonzero. -/
theorem exists_eval_pderiv_ellipticQuarticSeedPolynomial_ne_zero {v : Fin 4 → ℂ} (hv : v ≠ 0) :
    ∃ i, eval v (pderiv i ellipticQuarticSeedPolynomial) ≠ 0 := by
  by_contra! hd
  have h₀ := hd 0
  have h₁ := hd 1
  have h₂ := hd 2
  have h₃ := hd 3
  simp only [eval_pderiv_zero_ellipticQuarticSeedPolynomial,
    eval_pderiv_one_ellipticQuarticSeedPolynomial, eval_pderiv_two_ellipticQuarticSeedPolynomial,
    eval_pderiv_three_ellipticQuarticSeedPolynomial] at h₀ h₁ h₂ h₃
  -- A vanishing coordinate forces the next one in the cycle `z₀ → z₃ → z₁ → z₂ → z₀` to vanish.
  have h03 : v 0 = 0 → v 3 = 0 := fun h ↦ by simpa [h] using h₀
  have h31 : v 3 = 0 → v 1 = 0 := fun h ↦ by simpa [h] using h₃
  have h12 : v 1 = 0 → v 2 = 0 := fun h ↦ by simpa [h] using h₁
  have h20 : v 2 = 0 → v 0 = 0 := fun h ↦ by simpa [h] using h₂
  -- Multiplying the four relations gives `(z₀ z₁ z₂ z₃)³ = 81 (z₀ z₁ z₂ z₃)³`.
  have h80 : 80 * (v 0 * v 1 * v 2 * v 3) ^ 3 = 0 := by
    linear_combination -(v 1 ^ 3 * v 2 ^ 3 * v 3 ^ 3) * h₂ + 3 * v 1 * v 2 ^ 5 * v 3 ^ 3 * h₃ -
      9 * v 0 * v 1 * v 2 ^ 2 * v 3 ^ 5 * h₁ + 27 * v 0 * v 1 ^ 3 * v 2 ^ 2 * v 3 ^ 3 * h₀
  have h0 : v 0 = 0 := by
    rcases mul_eq_zero.mp h80 with h | h
    · norm_num at h
    simp only [pow_eq_zero_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_eq_zero] at h
    rcases h with ((h | h) | h) | h
    exacts [h, h20 (h12 h), h20 h, h20 (h12 (h31 h))]
  refine hv (funext fun i ↦ ?_)
  fin_cases i
  exacts [h0, h31 (h03 h0), h12 (h31 (h03 h0)), h03 h0]

/-- **The seed quartic surface is smooth.** At every nonzero vector of `ℂ⁴` the cone Jacobian of
`ellipticQuarticSeedPolynomial` is surjective. In particular it is surjective at every point of
its projective zero locus. -/
theorem mulVec_surjective_jacobiMatrixAt_ellipticQuarticSeedPolynomial {v : Fin 4 → ℂ}
    (hv : v ≠ 0) :
    (jacobiMatrixAt (fun _ : Unit ↦ ellipticQuarticSeedPolynomial) v).mulVec.Surjective :=
  mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero.2
    (exists_eval_pderiv_ellipticQuarticSeedPolynomial_ne_zero hv)

/-- The evaluation map `ℂ⁴ → ℂ` of the quartic `ellipticQuarticSeedPolynomial`,
`v ↦ v₀³ v₂ + v₂³ v₁ + v₁³ v₃ + v₃³ v₀`. -/
noncomputable def ellipticQuarticSeedMap (v : Fin 4 → ℂ) : ℂ :=
  eval v ellipticQuarticSeedPolynomial

/-- The evaluation map `ellipticQuarticSeedMap` is evaluation of `ellipticQuarticSeedPolynomial`.
-/
theorem ellipticQuarticSeedMap_eq_eval :
    ellipticQuarticSeedMap = fun v ↦ eval v ellipticQuarticSeedPolynomial :=
  (rfl)

/-- The value of `ellipticQuarticSeedMap` at a vector `v`. -/
@[simp]
theorem ellipticQuarticSeedMap_apply (v : Fin 4 → ℂ) :
    ellipticQuarticSeedMap v = v 0 ^ 3 * v 2 + v 2 ^ 3 * v 1 + v 1 ^ 3 * v 3 + v 3 ^ 3 * v 0 :=
  eval_ellipticQuarticSeedPolynomial v

/-- Scaling a vector by `t` multiplies the value of `ellipticQuarticSeedMap` by `t ^ 4`. -/
theorem ellipticQuarticSeedMap_smul (t : ℂ) (v : Fin 4 → ℂ) :
    ellipticQuarticSeedMap (t • v) = t ^ 4 * ellipticQuarticSeedMap v :=
  isHomogeneous_ellipticQuarticSeedPolynomial.eval_smul t v

/-- The quartic vanishes on the plane `{z₂ = z₃ = 0}` of `ℂ⁴`, the cone over the line `L₀`. -/
theorem ellipticQuarticSeedMap_eq_zero_of_apply_two_eq_zero_of_apply_three_eq_zero
    {v : Fin 4 → ℂ} (h₂ : v 2 = 0) (h₃ : v 3 = 0) : ellipticQuarticSeedMap v = 0 := by
  simp [h₂, h₃]

/-- The quartic vanishes on the plane `{z₀ = z₁ = 0}` of `ℂ⁴`, the cone over the line `L₁`. -/
theorem ellipticQuarticSeedMap_eq_zero_of_apply_zero_eq_zero_of_apply_one_eq_zero
    {v : Fin 4 → ℂ} (h₀ : v 0 = 0) (h₁ : v 1 = 0) : ellipticQuarticSeedMap v = 0 := by
  simp [h₀, h₁]

/-- The class of a nonzero vector `v` lies on the projective quartic surface of
`ellipticQuarticSeedPolynomial` exactly when `ellipticQuarticSeedMap` vanishes at `v`. With
`ellipticQuarticSeedMap_eq_zero_of_apply_two_eq_zero_of_apply_three_eq_zero` and
`ellipticQuarticSeedMap_eq_zero_of_apply_zero_eq_zero_of_apply_one_eq_zero`, this puts the lines
`L₀` and `L₁` on the surface. -/
theorem mk_mem_complexProjectiveZeroLocus_ellipticQuarticSeedPolynomial_iff {v : Fin 4 → ℂ}
    (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈
        complexProjectiveZeroLocus (fun _ : Unit ↦ ellipticQuarticSeedPolynomial) ↔
      ellipticQuarticSeedMap v = 0 := by
  rw [complexProjectiveZeroLocus_mk_iff (fun _ ↦ isHomogeneous_ellipticQuarticSeedPolynomial),
    ellipticQuarticSeedMap_eq_eval, Unique.forall_iff]

/-- **The seed quartic is regular away from the origin.** The derivative of the evaluation map
`ellipticQuarticSeedMap : ℂ⁴ → ℂ` is surjective at every nonzero vector, whether or not the
vector lies on the quartic. -/
theorem ellipticQuarticSeedMap_fderiv_surjective (v : Fin 4 → ℂ) (hv : v ≠ 0) :
    Function.Surjective (fderiv ℂ ellipticQuarticSeedMap v) := by
  rw [ellipticQuarticSeedMap_eq_eval, surjective_fderiv_eval_iff]
  exact exists_eval_pderiv_ellipticQuarticSeedPolynomial_ne_zero hv

end TauCeti

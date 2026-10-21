/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HermitianSignature.Basic
public import TauCeti.Analysis.Normed.Algebra.SquareRoot
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Analysis.Matrix.Normed

/-!
# Local constancy of the Hermitian signature

The signature of a nonsingular Hermitian matrix is unchanged by sufficiently small
Hermitian perturbations. More precisely, nearby Hermitian matrices are congruent to the
original matrix by an invertible matrix. This gives local constancy for continuous
Hermitian families, without choosing or ordering their eigenvalues continuously.

The congruence uses the square root near the identity from
`TauCeti.Analysis.Normed.Algebra.SquareRoot`. For a fixed nonsingular Hermitian matrix `A`,
the comparison `A⁻¹ * B` is self-adjoint for the pairing defined by `A`. Uniqueness of the
square root near the identity makes its square root self-adjoint for that pairing too,
and hence gives `Rᴴ * A * R = B`. This is the matrix version of the square-root argument
in `TauCeti.exists_congruence_of_symmetric_family`.

This stability result applies in particular to signature functions of Seifert matrices
away from their singular parameters. Through Gram matrices, it also gives local constancy of the
negative index of a continuous family of symmetric bilinear forms on a finite-dimensional real
space at a nondegenerate member.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299–340,
  Section 2 (congruences from operator square roots).
-/

public section

open Filter Topology
open scoped Matrix.Norms.Operator

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {A : Matrix ι ι 𝕜}

/-- Every Hermitian matrix sufficiently close to a nonsingular Hermitian matrix is
congruent to it by an invertible matrix. -/
theorem eventually_exists_conjTranspose_mul_mul_eq (hA : A.IsHermitian)
    (hdet : IsUnit A.det) :
    ∀ᶠ B in 𝓝 A, B.IsHermitian →
      ∃ R : Matrix ι ι 𝕜, IsUnit R.det ∧ Rᴴ * A * R = B := by
  let adj : Matrix ι ι 𝕜 → Matrix ι ι 𝕜 := fun R => A⁻¹ * Rᴴ * A
  have hadj_one : adj 1 = 1 := by
    simp [adj, A.nonsing_inv_mul hdet]
  have hadj_mul (R S : Matrix ι ι 𝕜) : adj (R * S) = adj S * adj R := by
    simp only [adj, conjTranspose_mul]
    simp only [Matrix.mul_assoc, A.mul_nonsing_inv_cancel_left (Rᴴ * A) hdet]
  have hadj_C {B : Matrix ι ι 𝕜} (hB : B.IsHermitian) : adj (A⁻¹ * B) = A⁻¹ * B := by
    simp only [adj, conjTranspose_mul, conjTranspose_nonsing_inv, hA.eq, hB.eq]
    simp [Matrix.mul_assoc, A.nonsing_inv_mul hdet]
  have hC : Tendsto (fun B : Matrix ι ι 𝕜 => A⁻¹ * B) (𝓝 A) (𝓝 1) := by
    simpa only [A.nonsing_inv_mul hdet] using
      (by fun_prop : Continuous (fun B : Matrix ι ι 𝕜 => A⁻¹ * B)).tendsto A
  let root : Matrix ι ι 𝕜 → Matrix ι ι 𝕜 := TauCeti.sqrtNearOne (Matrix ι ι 𝕜)
  have hroot : ContinuousAt root 1 := TauCeti.continuousAt_sqrtNearOne
  have hroot_one : root 1 = 1 := TauCeti.sqrtNearOne_one
  let R : Matrix ι ι 𝕜 → Matrix ι ι 𝕜 := root ∘ (fun B => A⁻¹ * B)
  have hR : Tendsto R (𝓝 A) (𝓝 1) := by
    simpa only [hroot_one] using hroot.tendsto.comp hC
  have hadj : Continuous adj := by
    exact (continuous_const.mul continuous_id.matrix_conjTranspose).mul continuous_const
  have hunit : ∀ᶠ B in 𝓝 A, IsUnit (R B) :=
    hR.eventually (Units.isOpen.mem_nhds isUnit_one)
  filter_upwards [hC.eventually TauCeti.eventually_mul_self_sqrtNearOne,
    hC.eventually (TauCeti.eventually_sqrtNearOne_fixed hadj.continuousAt hadj_one hadj_mul),
    hunit] with B hs hu hunit
  intro hB
  have hs' : R B * R B = A⁻¹ * B := hs
  have hself : adj (R B) = R B := hu (hadj_C hB)
  have hAR : (R B)ᴴ * A = A * R B := by
    have h := congrArg (fun S => A * S) hself
    simpa only [adj, ← Matrix.mul_assoc, A.mul_nonsing_inv hdet, Matrix.one_mul] using h
  refine ⟨R B, (Matrix.isUnit_iff_isUnit_det _).mp hunit, ?_⟩
  rw [hAR, Matrix.mul_assoc, hs', A.mul_nonsing_inv_cancel_left B hdet]

/-- The Hermitian signature is constant near every nonsingular Hermitian matrix,
when restricted to Hermitian perturbations. -/
theorem eventually_signature_eq (hA : A.IsHermitian) (hdet : IsUnit A.det) :
    ∀ᶠ B in 𝓝 A, ∀ hB : B.IsHermitian, hB.signature = hA.signature := by
  filter_upwards [hA.eventually_exists_conjTranspose_mul_mul_eq hdet] with B hB
  intro hherm
  obtain ⟨R, hR, heq⟩ := hB hherm
  convert hA.signature_congr (P := Rᴴ) (by simpa using hR.star) using 2
  simpa only [conjTranspose_conjTranspose] using heq.symm

/-- A continuous Hermitian family has locally constant signature at every parameter
where its matrix is nonsingular. The parameter space is arbitrary. -/
theorem eventually_signature_eq_of_continuousAt {X : Type*} [TopologicalSpace X]
    {B : X → Matrix ι ι 𝕜} (hB : ∀ x, (B x).IsHermitian) {x : X}
    (hc : ContinuousAt B x) (hdet : IsUnit (B x).det) :
    ∀ᶠ y in 𝓝 x, (hB y).signature = (hB x).signature := by
  filter_upwards [hc.eventually ((hB x).eventually_signature_eq hdet)] with y hy
  exact hy (hB y)

/-- The negative index of the quadratic form of a continuous real symmetric matrix family is
locally constant at a nonsingular member. Only local symmetry of the family is required. -/
theorem eventually_sigNeg_toQuadraticForm'_eq_of_continuousAt {X : Type*} [TopologicalSpace X]
    {B : X → Matrix ι ι ℝ} {x : X} (hx : (B x).IsHermitian)
    (hB : ∀ᶠ y in nhds x, (B y).IsHermitian) (hc : ContinuousAt B x)
    (hdet : IsUnit (B x).det) :
    ∀ᶠ y in nhds x,
      sigNeg ((B y).toQuadraticForm') = sigNeg ((B x).toQuadraticForm') := by
  filter_upwards [hc.eventually (hx.eventually_exists_conjTranspose_mul_mul_eq hdet), hB]
    with y hy hhy
  obtain ⟨R, hR, hRB⟩ := hy hhy
  have hRB' : R.transpose * B x * R.transpose.transpose = B y := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using hRB
  apply QuadraticMap.Equivalent.sigNeg_eq
  rw [← hRB']
  exact ⟨Matrix.isometryEquivCongr (by simpa using hR) (B x)⟩

end Matrix.IsHermitian

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The negative index of a continuous family of symmetric bilinear forms on a
finite-dimensional real space is locally constant at a nondegenerate member. Only local
symmetry of the family is required. -/
theorem eventually_sigNeg_toBilinForm_eq_of_continuousAt {X : Type*} [TopologicalSpace X]
    {V : X → E →L[ℝ] E →L[ℝ] ℝ} {x : X} (hsymm : ∀ᶠ y in 𝓝 x, (V y).toBilinForm.IsSymm)
    (hc : ContinuousAt V x) (hnd : (V x).toBilinForm.Nondegenerate) :
    ∀ᶠ y in 𝓝 x,
      sigNeg (V y).toBilinForm.toQuadraticMap = sigNeg (V x).toBilinForm.toQuadraticMap := by
  let b := Module.finBasis ℝ E
  let A : X → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun y ↦ (V y).toBilinForm.toMatrix b
  have hA : ContinuousAt A x := by
    refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    simpa only [A, LinearMap.BilinForm.toMatrix_apply, toBilinForm_apply] using
      (hc.clm_apply continuousAt_const).clm_apply continuousAt_const
  have hHermitian {y : X} (hy : (V y).toBilinForm.IsSymm) : (A y).IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.IsSymm] using ((V y).toBilinForm.isSymm_toMatrix_iff_isSymm b).mpr hy
  have hdet : IsUnit (A x).det :=
    isUnit_iff_ne_zero.mpr ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hnd)
  have hindex := Matrix.IsHermitian.eventually_sigNeg_toQuadraticForm'_eq_of_continuousAt
    (hHermitian hsymm.self_of_nhds) (hsymm.mono fun _ ↦ hHermitian) hA hdet
  filter_upwards [hindex] with y hy
  simpa only [A, LinearMap.BilinForm.sigNeg_toMatrix] using hy

end ContinuousLinearMap

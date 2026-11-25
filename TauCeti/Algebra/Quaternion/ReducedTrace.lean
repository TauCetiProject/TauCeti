/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Algebra.QuadraticAlgebra.Discriminant` supplies `QuadraticAlgebra.discr`, the
-- discriminant `c₂ ^ 2 + 4 * c₁` of `X ^ 2 - c₂ * X - c₁`, which occurs in the Gram determinant.
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
-- `LinearMap.BilinForm.dualSubmodule` and `LinearMap.BilinForm.dualBasis` occur in the statements
-- about the dual lattice, `LinearMap.BilinForm.toMatrix` in those about the Gram matrix.
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
-- The norm form, whose polar form is related to the reduced trace pairing.
public import TauCeti.Algebra.Quaternion.NormForm
-- Used only in proofs.
import Mathlib.Tactic.LinearCombination

/-!
# The reduced trace pairing of a quaternion algebra

The sum `x + star x` of a quaternion and its conjugate is the scalar `2 x.re + c₂ x.imI`
(`QuaternionAlgebra.self_add_star'`). This file packages it as the **reduced trace**
`QuaternionAlgebra.reducedTrace c₁ c₂ c₃ : ℍ[R,c₁,c₂,c₃] →ₗ[R] R` and the **reduced trace pairing**
`QuaternionAlgebra.reducedTraceForm`, the symmetric bilinear form `(x, y) ↦ trd (x * y)`, over an
arbitrary commutative ring.

The pairing is the form from which discriminants, trace duals and codifferents of lattices and
orders in a quaternion algebra are built. Its Gram matrix in the basis `1, i, j, k` is block
diagonal, with determinant `-(c₃ (c₂² + 4 c₁))²`, where `c₂² + 4 c₁` is the discriminant of
`X² - c₂ X - c₁`. For the symbol algebra `ℍ[R,a,b] = ℍ[R,a,0,b]` the Gram matrix is the diagonal
matrix `diag(2, 2a, 2b, -2ab)`, of determinant `-16 a² b²`, so over a domain in which `2 a b ≠ 0`
the pairing is nondegenerate. Over a field the dual basis of `1, i, j, k` is then
`1/2, i/(2a), j/(2b), -k/(2ab)`, and the trace dual of the lattice spanned by `1, i, j, k` over any
subring is spanned by these four elements.

The trace of left multiplication by `x` is `2 trd x` (`QuaternionAlgebra.trace_mulLeft`, in
`TauCeti/Algebra/Quaternion/AlgEquiv.lean`), so the regular trace pairing `(x, y) ↦ Tr (x * y)`
vanishes identically in characteristic two, while over a domain of characteristic two the reduced
trace pairing stays nondegenerate whenever `c₂ c₃ ≠ 0`. An algebra equivalence of quaternion
algebras carries one reduced trace pairing to the other once `2` is regular
(`QuaternionAlgebra.congr_reducedTraceForm`, also in `AlgEquiv.lean`). On a central simple
quaternion algebra over a field of characteristic other than two, `reducedTrace` is the reduced
trace of the central simple algebra (`TauCeti.Algebra.reducedTrace_quaternionAlgebra`, in
`TauCeti/Algebra/CentralSimple/ReducedTrace.lean`).

## Main definitions

* `QuaternionAlgebra.reducedTrace`: the reduced trace `x ↦ 2 x.re + c₂ x.imI`.
* `QuaternionAlgebra.reducedTraceForm`: the reduced trace pairing `(x, y) ↦ trd (x * y)`.

## Main results

* `QuaternionAlgebra.coe_reducedTrace`: the reduced trace of `x` is `x + star x`.
* `QuaternionAlgebra.polar_normForm_eq_reducedTraceForm`: the polar form of the norm form is
  `(x, y) ↦ trd (x * star y)`.
* `QuaternionAlgebra.toMatrix_reducedTraceForm` and
  `QuaternionAlgebra.toMatrix_reducedTraceForm_eq_diagonal`: the Gram matrix in the basis
  `1, i, j, k`, and its diagonal form `diag(2, 2a, 2b, -2ab)` for `ℍ[R,a,b]`.
* `QuaternionAlgebra.det_toMatrix_reducedTraceForm`: the Gram determinant is
  `-(c₃ (c₂² + 4 c₁))²`.
* `QuaternionAlgebra.nondegenerate_reducedTraceForm_iff`: over a domain, the pairing is
  nondegenerate exactly when `c₃ (c₂² + 4 c₁) ≠ 0`.
* `QuaternionAlgebra.dualBasis_reducedTraceForm` and
  `QuaternionAlgebra.dualSubmodule_reducedTraceForm_span_basisOneIJK`: the dual basis of
  `1, i, j, k` in `ℍ[K,a,b]` and the trace dual of the lattice it spans.

## References

* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288 (2021), Chapter 15, in
  particular 15.2.10 for the Gram matrix of the reduced trace pairing in the basis `1, i, j, k`.
-/

public section

open LinearMap (BilinForm)
open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

section General

variable (c₁ c₂ c₃ : R)

/-- The **reduced trace** `x ↦ 2 x.re + c₂ x.imI` of `ℍ[R,c₁,c₂,c₃]`, the scalar `x + star x`
(`QuaternionAlgebra.coe_reducedTrace`). -/
def reducedTrace : ℍ[R,c₁,c₂,c₃] →ₗ[R] R :=
  (2 : R) • reₗ c₁ c₂ c₃ + c₂ • imIₗ c₁ c₂ c₃

theorem reducedTrace_apply (x : ℍ[R,c₁,c₂,c₃]) :
    reducedTrace c₁ c₂ c₃ x = 2 * x.re + c₂ * x.imI := (rfl)

/-- The reduced trace of a quaternion is its sum with its conjugate. -/
@[simp]
theorem coe_reducedTrace (x : ℍ[R,c₁,c₂,c₃]) :
    (reducedTrace c₁ c₂ c₃ x : ℍ[R,c₁,c₂,c₃]) = x + star x := by
  rw [reducedTrace_apply, self_add_star']

/-- The reduced trace of a scalar `r` is `2 r`. -/
@[simp]
theorem reducedTrace_coe (r : R) : reducedTrace c₁ c₂ c₃ (r : ℍ[R,c₁,c₂,c₃]) = 2 * r := by
  simp [reducedTrace_apply]

@[simp]
theorem reducedTrace_one : reducedTrace c₁ c₂ c₃ (1 : ℍ[R,c₁,c₂,c₃]) = 2 := by
  simpa using reducedTrace_coe c₁ c₂ c₃ 1

@[simp]
theorem reducedTrace_star (x : ℍ[R,c₁,c₂,c₃]) :
    reducedTrace c₁ c₂ c₃ (star x) = reducedTrace c₁ c₂ c₃ x := by
  simp only [reducedTrace_apply, re_star, imI_star]
  ring

/-- The reduced trace is a trace: `trd (x * y) = trd (y * x)`. -/
theorem reducedTrace_mul_comm (x y : ℍ[R,c₁,c₂,c₃]) :
    reducedTrace c₁ c₂ c₃ (x * y) = reducedTrace c₁ c₂ c₃ (y * x) := by
  simp only [reducedTrace_apply, re_mul, imI_mul]
  ring

/-- The **reduced trace pairing** `(x, y) ↦ trd (x * y)` of `ℍ[R,c₁,c₂,c₃]`. -/
def reducedTraceForm : BilinForm R ℍ[R,c₁,c₂,c₃] :=
  (LinearMap.mul R ℍ[R,c₁,c₂,c₃]).compr₂ (reducedTrace c₁ c₂ c₃)

@[simp]
theorem reducedTraceForm_apply (x y : ℍ[R,c₁,c₂,c₃]) :
    reducedTraceForm c₁ c₂ c₃ x y = reducedTrace c₁ c₂ c₃ (x * y) := (rfl)

/-- The reduced trace pairing is symmetric. -/
theorem isSymm_reducedTraceForm : (reducedTraceForm c₁ c₂ c₃).IsSymm :=
  ⟨fun x y => reducedTrace_mul_comm c₁ c₂ c₃ x y⟩

/-- The polar form of the norm form is the reduced trace pairing against the conjugate,
`(x, y) ↦ trd (x * star y)`. -/
theorem polar_normForm_eq_reducedTraceForm (x y : ℍ[R,c₁,c₂,c₃]) :
    QuadraticMap.polar (normForm c₁ c₂ c₃) x y = reducedTraceForm c₁ c₂ c₃ x (star y) := by
  rw [polar_normForm, reducedTraceForm_apply, ← re_coe (c₁ := c₁) (c₂ := c₂) (c₃ := c₃)
    (reducedTrace c₁ c₂ c₃ _), coe_reducedTrace, star_mul, star_star]

/-- **The Gram matrix of the reduced trace pairing** in the basis `1, i, j, k`. -/
theorem toMatrix_reducedTraceForm :
    BilinForm.toMatrix (basisOneIJK c₁ c₂ c₃) (reducedTraceForm c₁ c₂ c₃) =
      !![2, c₂, 0, 0;
        c₂, 2 * c₁ + c₂ ^ 2, 0, 0;
        0, 0, 2 * c₃, c₂ * c₃;
        0, 0, c₂ * c₃, -(2 * c₁ * c₃)] := by
  ext i j
  rw [BilinForm.toMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [basisOneIJK, reducedTrace_apply] <;> ring

/-- **The Gram determinant of the reduced trace pairing** in the basis `1, i, j, k` is
`-(c₃ (c₂² + 4 c₁))²`. -/
theorem det_toMatrix_reducedTraceForm :
    (BilinForm.toMatrix (basisOneIJK c₁ c₂ c₃) (reducedTraceForm c₁ c₂ c₃)).det =
      -(c₃ * QuadraticAlgebra.discr c₁ c₂) ^ 2 := by
  rw [toMatrix_reducedTraceForm, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, QuadraticAlgebra.discr_def, Fin.succAbove]
  ring

/-- **The reduced trace pairing is nondegenerate exactly when `c₃ (c₂² + 4 c₁) ≠ 0`**, over a
domain. -/
theorem nondegenerate_reducedTraceForm_iff [IsDomain R] :
    (reducedTraceForm c₁ c₂ c₃).Nondegenerate ↔ c₃ * QuadraticAlgebra.discr c₁ c₂ ≠ 0 := by
  rw [BilinForm.nondegenerate_iff_det_ne_zero (basisOneIJK c₁ c₂ c₃),
    det_toMatrix_reducedTraceForm, neg_ne_zero, pow_ne_zero_iff two_ne_zero]

end General

section Symbol

/-- **The Gram matrix of the reduced trace pairing of `ℍ[R,a,b]`** in the basis `1, i, j, k` is
`diag(2, 2a, 2b, -2ab)`. -/
theorem toMatrix_reducedTraceForm_eq_diagonal (a b : R) :
    BilinForm.toMatrix (basisOneIJK a 0 b) (reducedTraceForm a 0 b) =
      Matrix.diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] := by
  rw [toMatrix_reducedTraceForm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The reduced trace pairing of `ℍ[R,a,b]` is nondegenerate** over a domain in which
`2`, `a` and `b` are nonzero. -/
theorem nondegenerate_reducedTraceForm [IsDomain R] {a b : R} (h2 : (2 : R) ≠ 0) (ha : a ≠ 0)
    (hb : b ≠ 0) : (reducedTraceForm a 0 b).Nondegenerate := by
  rw [nondegenerate_reducedTraceForm_iff, QuadraticAlgebra.discr_def]
  have h4 : (4 : R) = 2 * 2 := by norm_num
  simp [h4, h2, ha, hb]

end Symbol

section DualBasis

variable {K : Type*} [Field K] {a b : K}

/-- **The dual basis of `1, i, j, k` for the reduced trace pairing of `ℍ[K,a,b]`** is
`1/2, i/(2a), j/(2b), -k/(2ab)`. -/
theorem dualBasis_reducedTraceForm (hB : (reducedTraceForm a 0 b).Nondegenerate) :
    ⇑((reducedTraceForm a 0 b).dualBasis hB (basisOneIJK a 0 b)) =
      ![⟨2⁻¹, 0, 0, 0⟩, ⟨0, (2 * a)⁻¹, 0, 0⟩, ⟨0, 0, (2 * b)⁻¹, 0⟩,
        ⟨0, 0, 0, -(2 * a * b)⁻¹⟩] := by
  have h := (nondegenerate_reducedTraceForm_iff a 0 b).mp hB
  rw [QuadraticAlgebra.discr_def] at h
  have h2 : (2 : K) ≠ 0 := fun h2 => h (by linear_combination (2 * a * b) * h2)
  have ha : a ≠ 0 := fun ha => h (by simp [ha])
  have hb : b ≠ 0 := fun hb => h (by simp [hb])
  funext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((basisOneIJK a 0 b).ext fun j => ?_)
  rw [BilinForm.apply_dualBasis_left]
  fin_cases i <;> fin_cases j <;> simp [basisOneIJK, reducedTrace_apply] <;> field_simp

/-- **The trace dual of the lattice spanned by `1, i, j, k`.** For a ring `S` with an algebra map
to `K`, such as a subring of `K`, the elements of `ℍ[K,a,b]` whose reduced trace pairing with the
`S`-span of `1, i, j, k` lies in `S` form the `S`-span of `1/2, i/(2a), j/(2b), -k/(2ab)`. -/
theorem dualSubmodule_reducedTraceForm_span_basisOneIJK {S : Type*} [CommRing S] [Algebra S K]
    (hB : (reducedTraceForm a 0 b).Nondegenerate) :
    (reducedTraceForm a 0 b).dualSubmodule (Submodule.span S (Set.range (basisOneIJK a 0 b))) =
      Submodule.span S (Set.range ![(⟨2⁻¹, 0, 0, 0⟩ : ℍ[K,a,b]), ⟨0, (2 * a)⁻¹, 0, 0⟩,
        ⟨0, 0, (2 * b)⁻¹, 0⟩, ⟨0, 0, 0, -(2 * a * b)⁻¹⟩]) := by
  rw [BilinForm.dualSubmodule_span_of_basis _ hB, dualBasis_reducedTraceForm hB]

end DualBasis

/-! ### Worked Gram determinants -/

/-- For `ℍ[ℚ,3,-1]` the Gram determinant is `-144`. -/
example :
    (BilinForm.toMatrix (basisOneIJK (3 : ℚ) 0 (-1)) (reducedTraceForm 3 0 (-1))).det = -144 := by
  rw [det_toMatrix_reducedTraceForm, QuadraticAlgebra.discr_def]
  norm_num

/-- For Hamilton's quaternions `ℍ[ℚ,-1,-1]` the Gram determinant is `-16`. -/
example :
    (BilinForm.toMatrix (basisOneIJK (-1 : ℚ) 0 (-1)) (reducedTraceForm (-1) 0 (-1))).det =
      -16 := by
  rw [det_toMatrix_reducedTraceForm, QuadraticAlgebra.discr_def]
  norm_num

/-- For the split algebra `ℍ[ℚ,1,1]` the Gram determinant is also `-16`: nondegeneracy of the
reduced trace pairing does not distinguish division algebras from matrix algebras. -/
example :
    (BilinForm.toMatrix (basisOneIJK (1 : ℚ) 0 1) (reducedTraceForm 1 0 1)).det = -16 := by
  rw [det_toMatrix_reducedTraceForm, QuadraticAlgebra.discr_def]
  norm_num

/-- The Gram determinant of `ℍ[R,a,b]` is `-16 a² b²`. -/
example (a b : R) :
    (BilinForm.toMatrix (basisOneIJK a 0 b) (reducedTraceForm a 0 b)).det =
      -16 * a ^ 2 * b ^ 2 := by
  rw [det_toMatrix_reducedTraceForm, QuadraticAlgebra.discr_def]
  ring

end QuaternionAlgebra

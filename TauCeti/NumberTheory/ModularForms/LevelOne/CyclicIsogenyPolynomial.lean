/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.UpperHalfPlane.FixedDetMatrices
public import TauCeti.NumberTheory.ModularForms.Degeneracy
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold
import TauCeti.RingTheory.Polynomial.Roots

/-!
# The polynomial of an `SL(2, ℤ)`-invariant function over the cyclic `n`-isogenies

Let `n` be a positive integer. An integral matrix is *primitive* when the greatest common divisor
of its entries is one (`TauCeti.IsPrimitive`). Left multiplication by `SL(2, ℤ)` permutes the
primitive integral matrices of determinant `n`, and the upper-triangular matrices
`(a b; 0 d)` with `ad = n`, `0 ≤ b < d` and `gcd(a, b, d) = 1` represent the orbits
(`FixedDetMatrices.primitiveReps n`). These orbits correspond to the sublattices `L' ⊆ L` of
index `n` with cyclic quotient `L / L'`, that is, to the cyclic `n`-isogenies out of the complex
elliptic curve `ℂ / L`.

For a function `f` on the upper half-plane, `TauCeti.ModularForm.cyclicIsogenyPolynomial n f τ` is
the monic polynomial

  `∏_{(a b; 0 d)} (X - f((a τ + b) / d))`

over these representatives. For `f = j` it is the classical modular polynomial `Φ_n(X, j(τ))`.
When `f` is `SL(2, ℤ)`-invariant, so is this polynomial: right multiplication by `γ ∈ SL(2, ℤ)`
permutes the orbits, and `f(A τ)` depends only on the orbit of `A`. The value `f(A τ)` at
*every* primitive matrix `A` of determinant `n`, not only at a representative, is a root;
in particular `f(n τ)` is. When `f` is holomorphic, so are the coefficients.
The coefficients of `Φ_n(X, j(τ))` are therefore holomorphic `SL(2, ℤ)`-invariant functions:
these are the inputs to the `q`-expansion argument that makes `Φ_n` a polynomial in `j` with
integer coefficients, and the root property at a fixed point `A τ = τ` of a primitive matrix is
what makes the value of `j` at an imaginary quadratic point an algebraic integer.

The matrices act on the upper half-plane through `FixedDetMatrices.toGLReal`. Right
multiplication on the representatives is the shared `TauCeti.repsRightMul`, and the invariance
proof follows that of the level-one Hecke operators, `TauCeti.heckeSlashLevelOne_slash_eq` in
`TauCeti.NumberTheory.ModularForms.LevelOne.Hecke`: the factor of `A` at `γ τ` is the factor at
`τ` of the representative of `A γ`, and `TauCeti.image_repsRightMul_primitiveReps` makes this a
permutation.

## Main definitions

* `TauCeti.ModularForm.cyclicIsogenyPolynomial n f τ`: the polynomial `∏ (X - f(A τ))` over
  `A ∈ FixedDetMatrices.primitiveReps n`.

## Main results

* `TauCeti.ModularForm.cyclicIsogenyPolynomial_smul`: for `SL(2, ℤ)`-invariant `f`, the
  polynomial takes the same value at `γ τ` as at `τ`.
* `TauCeti.ModularForm.roots_cyclicIsogenyPolynomial`: its roots are the values `f(A τ)` over
  the representatives, and `TauCeti.ModularForm.isRoot_cyclicIsogenyPolynomial`: for invariant
  `f`, `f(A τ)` is a root for every primitive `A` of determinant `n`; in particular
  (`TauCeti.ModularForm.isRoot_cyclicIsogenyPolynomial_scaleGL_smul`) `f(n τ)` is, where
  `n τ = TauCeti.scaleGL n • τ`.
* `TauCeti.ModularForm.mdifferentiable_coeff_cyclicIsogenyPolynomial`: for holomorphic `f` the
  coefficients are holomorphic.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §11.C (the modular equation: the orbit
  representatives of the primitive matrices of determinant `m` and the invariance of
  `Φ_m(X, j(τ))`).
* S. Lang, *Elliptic Functions*, Chapter 5 (the modular equation).
-/

public section

open Matrix Polynomial UpperHalfPlane
open scoped MatrixGroups Manifold

namespace TauCeti.ModularForm

open FixedDetMatrices

/-! ### The polynomial over the cyclic `n`-isogenies -/

variable (n : ℕ) [NeZero n]

/-- **The polynomial of `f` over the cyclic `n`-isogenies**: `∏ (X - f((a τ + b) / d))` over the
primitive upper-triangular representatives `(a b; 0 d)` of determinant `n`. For `f = j` this is
the classical modular polynomial `Φ_n(X, j(τ))`. -/
noncomputable def cyclicIsogenyPolynomial (f : ℍ → ℂ) (τ : ℍ) : ℂ[X] :=
  ∏ A ∈ primitiveReps (n : ℤ), (X - C (f (toGLReal (NeZero.ne (n : ℤ)) A • τ)))

/-- The defining equation of `cyclicIsogenyPolynomial`: the product of the linear factors
`X - f(A τ)` over the primitive representatives `A`. -/
theorem cyclicIsogenyPolynomial_def (f : ℍ → ℂ) (τ : ℍ) :
    cyclicIsogenyPolynomial n f τ =
      ∏ A ∈ primitiveReps (n : ℤ), (X - C (f (toGLReal (NeZero.ne (n : ℤ)) A • τ))) := (rfl)

variable {n}

/-- The polynomial over the cyclic `n`-isogenies is monic. -/
theorem monic_cyclicIsogenyPolynomial (f : ℍ → ℂ) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

/-- The degree of the polynomial over the cyclic `n`-isogenies is the number of cyclic
`n`-isogenies. -/
@[simp]
theorem natDegree_cyclicIsogenyPolynomial (f : ℍ → ℂ) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).natDegree = (primitiveReps (n : ℤ)).card :=
  natDegree_finsetProd_X_sub_C_eq_card _ _

/-- The roots of the polynomial over the cyclic `n`-isogenies, with multiplicity, are the values
`f(A τ)` at the representatives `A`. -/
theorem roots_cyclicIsogenyPolynomial (f : ℍ → ℂ) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).roots =
      (primitiveReps (n : ℤ)).val.map
        fun A ↦ f (toGLReal (NeZero.ne (n : ℤ)) A • τ) := by
  rw [cyclicIsogenyPolynomial_def, roots_prod_X_sub_C_map]

/-- **The polynomial over the cyclic `n`-isogenies of an `SL(2, ℤ)`-invariant function is
`SL(2, ℤ)`-invariant**: it takes the same value at `γ τ` as at `τ`. -/
theorem cyclicIsogenyPolynomial_smul {f : ℍ → ℂ} (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    cyclicIsogenyPolynomial n f (γ • τ) = cyclicIsogenyPolynomial n f τ := by
  classical
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  have hSL (g : SL(2, ℤ)) (z : ℍ) : SpecialLinearGroup.mapGL ℝ g • z = g • z :=
    (MulAction.compHom_smul_def _ _ _).symm
  -- the factor of `A` at `γ τ` is the factor at `τ` of the representative of `A γ`
  have hperm (A : FixedDetMatrix (Fin 2) ℤ n) :
      X - C (f (toGLReal hn A • γ • τ)) =
        X - C (f (toGLReal hn (repsRightMul hn γ⁻¹ A) • τ)) := by
    rw [toGLReal_repsRightMul, inv_inv, mul_smul, mul_smul, hSL, hSL, hf]
  rw [cyclicIsogenyPolynomial_def, cyclicIsogenyPolynomial_def,
    Finset.prod_congr rfl fun A _ ↦ hperm A,
    ← Finset.prod_image (f := fun A ↦ X - C (f (toGLReal hn A • τ)))
      (repsRightMul_injOn_primitiveReps hn γ⁻¹), image_repsRightMul_primitiveReps]

/-- For an `SL(2, ℤ)`-invariant `f`, the value `f(A τ)` at **every** primitive integral matrix `A`
of determinant `n` is a root of the polynomial over the cyclic `n`-isogenies at `τ`. -/
theorem isRoot_cyclicIsogenyPolynomial {f : ℍ → ℂ}
    (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).IsRoot
      (f (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  obtain ⟨g, hg⟩ := exists_smul_mem_primitiveReps hn hA
  rw [IsRoot, cyclicIsogenyPolynomial_def, eval_prod]
  refine Finset.prod_eq_zero hg ?_
  rw [toGLReal_smul_smul, hf]
  simp

/-- For an `SL(2, ℤ)`-invariant `f`, the value `f(n τ)` is a root of the polynomial over the
cyclic `n`-isogenies at `τ`, where `n τ = TauCeti.scaleGL n • τ` is the action of `diag(n, 1)`.
For `f = j` this is the classical identity `Φ_n(j(n τ), j(τ)) = 0`. -/
theorem isRoot_cyclicIsogenyPolynomial_scaleGL_smul {f : ℍ → ℂ}
    (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).IsRoot (f (scaleGL n • τ)) := by
  -- `diag(n, 1)` is a primitive integral matrix of determinant `n`, acting as `scaleGL n`
  let D := TraceFormulaMatrix.diagonal (n : ℤ) 1 (mul_one _)
  have hD : toGLReal (NeZero.ne (n : ℤ)) D = scaleGL n := by
    refine Units.ext ?_
    rw [coe_toGLReal, coe_scaleGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D]
  rw [← hD]
  exact isRoot_cyclicIsogenyPolynomial hf
    (isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 1 1).toIntLinearMap, by simp [D]⟩) τ

/-- **The coefficients of the polynomial over the cyclic `n`-isogenies of a holomorphic function
are holomorphic.** -/
theorem mdifferentiable_coeff_cyclicIsogenyPolynomial {f : ℍ → ℂ} (hf : MDiff f) (k : ℕ) :
    MDiff fun τ : ℍ ↦ (cyclicIsogenyPolynomial n f τ).coeff k :=
  TauCeti.UpperHalfPlane.mdifferentiable_coeff_prod_X_sub_C
    (a := fun A τ ↦ f (toGLReal _ A • τ)) _
    (fun A _ ↦ MDifferentiable.comp hf
      (mdifferentiable_toGLReal_smul (Int.natCast_pos.2 (NeZero.pos n)) A)) k

end TauCeti.ModularForm

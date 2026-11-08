/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Complex.UpperHalfPlane.FixedDetMatrices
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Complex.UpperHalfPlane.Manifold

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
`τ` of the representative of `A γ`, and `TauCeti.repsRightMul_injOn` makes this a permutation.

## Main definitions

* `TauCeti.ModularForm.cyclicIsogenyPolynomial n f τ`: the polynomial `∏ (X - f(A τ))` over
  `A ∈ FixedDetMatrices.primitiveReps n`.

## Main results

* `TauCeti.ModularForm.cyclicIsogenyPolynomial_smul`: for `SL(2, ℤ)`-invariant `f`, the
  polynomial takes the same value at `γ τ` as at `τ`.
* `TauCeti.ModularForm.roots_cyclicIsogenyPolynomial`: its roots are the values `f(A τ)` over
  the representatives, and `TauCeti.ModularForm.isRoot_cyclicIsogenyPolynomial`: for invariant
  `f`, `f(A τ)` is a root for every primitive `A` of determinant `n`; in particular
  (`TauCeti.ModularForm.isRoot_cyclicIsogenyPolynomial_natCast_smul`) `f(n τ)` is.
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

namespace FixedDetMatrices

variable {n : ℤ}

/-! ### Right multiplication permutes the orbits -/

private theorem repsRightMul_mem_primitiveReps (hn : n ≠ 0) (γ : SL(2, ℤ))
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps n) :
    TauCeti.repsRightMul hn γ A ∈ primitiveReps n := by
  refine mem_primitiveReps.2 ⟨TauCeti.repsRightMul_mem_reps hn γ A, ?_⟩
  rw [TauCeti.repsRightMul_def, isPrimitive_smul_iff,
    TauCeti.isPrimitive_traceFormulaMatrixRight_iff]
  exact (mem_primitiveReps.1 hA).2

private theorem toGLReal_repsRightMul_inv_smul (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) (τ : ℍ) :
    toGLReal hn (TauCeti.repsRightMul hn γ⁻¹ A) • τ =
      TauCeti.repsRightMulFactor hn γ⁻¹ A • toGLReal hn A • γ • τ := by
  have hγ : SpecialLinearGroup.mapGL ℝ γ • τ = γ • τ := (MulAction.compHom_smul_def _ _ _).symm
  rw [TauCeti.repsRightMul_def, toGLReal_smul_smul, TauCeti.toGLReal_traceFormulaMatrixRight,
    inv_inv, mul_smul, hγ]

/-- Right multiplication is injective on the primitive representatives. -/
private theorem repsRightMul_injOn_primitiveReps (hn : n ≠ 0) (γ : SL(2, ℤ)) :
    Set.InjOn (TauCeti.repsRightMul hn γ)
      (primitiveReps n : Set (FixedDetMatrix (Fin 2) ℤ n)) :=
  (TauCeti.repsRightMul_injOn hn γ).mono fun _ hA ↦ (mem_primitiveReps.1 hA).1

open scoped Classical in
/-- Right multiplication by `SL(2, ℤ)` permutes the orbits: the representatives of the right
translates, `A ∈ primitiveReps n`, are again all of `primitiveReps n`. -/
private theorem image_repsRightMul (hn : n ≠ 0) (γ : SL(2, ℤ)) :
    (primitiveReps n).image (TauCeti.repsRightMul hn γ) = primitiveReps n := by
  refine Finset.eq_of_subset_of_card_le ?_
    (Finset.card_image_of_injOn (repsRightMul_injOn_primitiveReps hn γ)).ge
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
  exact repsRightMul_mem_primitiveReps hn γ hA

end FixedDetMatrices

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
  have h := roots_multiset_prod_X_sub_C ((primitiveReps (n : ℤ)).val.map
    fun A ↦ f (toGLReal (NeZero.ne (n : ℤ)) A • τ))
  rw [Multiset.map_map] at h
  rwa [cyclicIsogenyPolynomial_def, Finset.prod_eq_multiset_prod]

/-- **The polynomial over the cyclic `n`-isogenies of an `SL(2, ℤ)`-invariant function is
`SL(2, ℤ)`-invariant**: it takes the same value at `γ τ` as at `τ`. -/
theorem cyclicIsogenyPolynomial_smul {f : ℍ → ℂ} (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    cyclicIsogenyPolynomial n f (γ • τ) = cyclicIsogenyPolynomial n f τ := by
  classical
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  -- the factor of `A` at `γ τ` is the factor at `τ` of the representative of `A γ`
  have hperm (A : FixedDetMatrix (Fin 2) ℤ n) :
      X - C (f (toGLReal hn A • γ • τ)) =
        X - C (f (toGLReal hn (TauCeti.repsRightMul hn γ⁻¹ A) • τ)) := by
    rw [toGLReal_repsRightMul_inv_smul, hf]
  rw [cyclicIsogenyPolynomial_def, cyclicIsogenyPolynomial_def,
    Finset.prod_congr rfl fun A _ ↦ hperm A,
    ← Finset.prod_image (f := fun A ↦ X - C (f (toGLReal hn A • τ)))
      (repsRightMul_injOn_primitiveReps hn γ⁻¹), image_repsRightMul]

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

/-- The diagonal matrix `diag(n, 1)` is a primitive integral matrix of determinant `n`. -/
private def diagNatOne : FixedDetMatrix (Fin 2) ℤ n :=
  ⟨!![(n : ℤ), 0; 0, 1], by simp [det_fin_two_of]⟩

omit [NeZero n] in
private theorem isPrimitive_diagNatOne : IsPrimitive (diagNatOne (n := n)).1 :=
  isPrimitive_def.2 ⟨(entryAddMonoidHom ℤ 1 1).toIntLinearMap, by simp [diagNatOne]⟩

private theorem toGLReal_diagNatOne_smul (τ : ℍ) :
    toGLReal (NeZero.ne (n : ℤ)) diagNatOne • τ =
      (⟨n, Nat.cast_pos.2 (NeZero.pos n)⟩ : {x : ℝ // 0 < x}) • τ := by
  have hdet : 0 < (toGLReal (NeZero.ne (n : ℤ)) diagNatOne).det.val := by
    rw [det_toGLReal]
    exact_mod_cast NeZero.pos n
  ext
  rw [coe_smul_of_det_pos hdet, coe_pos_real_smul]
  -- `num` and `denom` see the matrix through a different `Semiring ℝ` instance path, which `simp`
  -- does not unify with `toGLReal_apply`; `rw` does
  simp only [num, denom]
  rw [toGLReal_apply, toGLReal_apply, toGLReal_apply, toGLReal_apply]
  simp [diagNatOne, Complex.real_smul]

/-- For an `SL(2, ℤ)`-invariant `f`, the value `f(n τ)` is a root of the polynomial over the
cyclic `n`-isogenies at `τ`. For `f = j` this is the classical identity `Φ_n(j(n τ), j(τ)) = 0`. -/
theorem isRoot_cyclicIsogenyPolynomial_natCast_smul {f : ℍ → ℂ}
    (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).IsRoot
      (f ((⟨n, Nat.cast_pos.2 (NeZero.pos n)⟩ : {x : ℝ // 0 < x}) • τ)) := by
  rw [← toGLReal_diagNatOne_smul]
  exact isRoot_cyclicIsogenyPolynomial hf isPrimitive_diagNatOne τ

/-- **The coefficients of the polynomial over the cyclic `n`-isogenies of a holomorphic function
are holomorphic.** -/
theorem mdifferentiable_coeff_cyclicIsogenyPolynomial {f : ℍ → ℂ} (hf : MDiff f) (k : ℕ) :
    MDiff fun τ : ℍ ↦ (cyclicIsogenyPolynomial n f τ).coeff k :=
  TauCeti.UpperHalfPlane.mdifferentiable_coeff_prod_X_sub_C
    (a := fun A τ ↦ f (toGLReal _ A • τ)) _
    (fun A _ ↦ MDifferentiable.comp hf
      (mdifferentiable_toGLReal_smul (Int.natCast_pos.2 (NeZero.pos n)) A)) k

end TauCeti.ModularForm

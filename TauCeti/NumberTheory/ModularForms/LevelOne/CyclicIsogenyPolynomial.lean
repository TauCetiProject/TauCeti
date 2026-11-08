/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

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

The matrices act on the upper half-plane through `FixedDetMatrices.toGLReal`.

## Main definitions

* `TauCeti.ModularForm.cyclicIsogenyPolynomial n f τ`: the polynomial `∏ (X - f(A τ))` over
  `A ∈ FixedDetMatrices.primitiveReps n`.

## Main results

* `FixedDetMatrices.toGLReal_smul_smul`, `FixedDetMatrices.mdifferentiable_toGLReal_smul`: the
  action of `g • A` is that of `A` followed by `g`, and for `0 < n` it is holomorphic.
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

/-! ### Integral matrices acting on the upper half-plane -/

/-- Inverse right multiplication by `g ∈ SL(2, ℤ)` becomes right multiplication by the image of
`g⁻¹` in `GL(2, ℝ)`. -/
theorem toGLReal_traceFormulaMatrixRight (hn : n ≠ 0) (g : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) :
    toGLReal hn (TauCeti.traceFormulaMatrixRight g A) =
      toGLReal hn A * SpecialLinearGroup.mapGL ℝ g⁻¹ := by
  rw [toGLReal_eq_map_toGL, TauCeti.toGL_traceFormulaMatrixRight, map_mul,
    SpecialLinearGroup.map_mapGL, toGLReal_eq_map_toGL]

/-- The action of `g • A` on the upper half-plane is that of `A` followed by that of `g`. -/
theorem toGLReal_smul_smul (hn : n ≠ 0) (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n)
    (τ : ℍ) : toGLReal hn (g • A) • τ = g • toGLReal hn A • τ := by
  rw [toGLReal_smul, mul_smul]
  exact (MulAction.compHom_smul_def _ _ _).symm

/-- For `0 < n`, the action of an integral matrix of determinant `n` on the upper half-plane is
holomorphic. -/
theorem mdifferentiable_toGLReal_smul (hn : 0 < n) (A : FixedDetMatrix (Fin 2) ℤ n) :
    MDiff fun τ : ℍ ↦ toGLReal hn.ne' A • τ :=
  mdifferentiable_smul (by rw [det_toGLReal]; exact_mod_cast hn)

/-! ### Right multiplication permutes the orbits -/

/-- Inverse right multiplication by `SL(2, ℤ)` preserves and reflects primitivity. -/
theorem isPrimitive_traceFormulaMatrixRight_iff (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n) :
    TauCeti.IsPrimitive (TauCeti.traceFormulaMatrixRight g A).1 ↔ TauCeti.IsPrimitive A.1 := by
  rw [TauCeti.val_traceFormulaMatrixRight, ← SpecialLinearGroup.coe_GL_coe_matrix,
    Units.isPrimitive_mul_units_iff]

/-- A matrix of `SL(2, ℤ)` moving the right translate `A γ` back into `reps n`. -/
private noncomputable def rightMulFactor (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) : SL(2, ℤ) :=
  (exists_smul_mem_reps hn (TauCeti.traceFormulaMatrixRight γ⁻¹ A)).choose

/-- The representative in `reps n` of the right translate `A γ`. -/
private noncomputable def rightMul (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) : FixedDetMatrix (Fin 2) ℤ n :=
  rightMulFactor hn γ A • TauCeti.traceFormulaMatrixRight γ⁻¹ A

private theorem rightMul_mem_primitiveReps (hn : n ≠ 0) (γ : SL(2, ℤ))
    {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ primitiveReps n) :
    rightMul hn γ A ∈ primitiveReps n := by
  refine mem_primitiveReps.2
    ⟨(exists_smul_mem_reps hn (TauCeti.traceFormulaMatrixRight γ⁻¹ A)).choose_spec, ?_⟩
  rw [rightMul, isPrimitive_smul_iff, isPrimitive_traceFormulaMatrixRight_iff]
  exact (mem_primitiveReps.1 hA).2

private theorem toGL_rightMul (hn : n ≠ 0) (γ : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n) :
    toGL hn (rightMul hn γ A) =
      SpecialLinearGroup.mapGL ℚ (rightMulFactor hn γ A) *
        (toGL hn A * SpecialLinearGroup.mapGL ℚ γ) := by
  rw [rightMul, toGL_smul, TauCeti.toGL_traceFormulaMatrixRight, inv_inv]

private theorem toGLReal_rightMul_smul (hn : n ≠ 0) (γ : SL(2, ℤ))
    (A : FixedDetMatrix (Fin 2) ℤ n) (τ : ℍ) :
    toGLReal hn (rightMul hn γ A) • τ = rightMulFactor hn γ A • toGLReal hn A • γ • τ := by
  have hγ : SpecialLinearGroup.mapGL ℝ γ • τ = γ • τ := (MulAction.compHom_smul_def _ _ _).symm
  rw [rightMul, toGLReal_smul_smul, toGLReal_traceFormulaMatrixRight, inv_inv, mul_smul, hγ]

/-- Right multiplication by `γ` is injective on the representatives. -/
private theorem rightMul_injOn (hn : n ≠ 0) (γ : SL(2, ℤ)) :
    Set.InjOn (rightMul hn γ) (primitiveReps n : Set (FixedDetMatrix (Fin 2) ℤ n)) := by
  intro A hA B hB h
  have hGL := congrArg (toGL hn) h
  simp only [toGL_rightMul] at hGL
  -- cancel `γ` on the right and move the left factors across: `A = g • B` for some `g`
  have hAB : toGL hn A =
      toGL hn (((rightMulFactor hn γ A)⁻¹ * rightMulFactor hn γ B) • B) := by
    rw [toGL_smul, map_mul, map_inv]
    simpa [mul_assoc] using
      congrArg (fun x ↦ (SpecialLinearGroup.mapGL ℚ (rightMulFactor hn γ A))⁻¹ * x *
        (SpecialLinearGroup.mapGL ℚ γ)⁻¹) hGL
  exact (eq_of_smul_eq_of_mem_reps (mem_primitiveReps.1 hB).1 (mem_primitiveReps.1 hA).1
    (toGL_injective hn hAB).symm).symm

open scoped Classical in
/-- Right multiplication by `γ ∈ SL(2, ℤ)` permutes the orbits: the representatives of the right
translates `A γ`, `A ∈ primitiveReps n`, are again all of `primitiveReps n`. -/
private theorem image_rightMul (hn : n ≠ 0) (γ : SL(2, ℤ)) :
    (primitiveReps n).image (rightMul hn γ) = primitiveReps n := by
  refine Finset.eq_of_subset_of_card_le ?_ (Finset.card_image_of_injOn (rightMul_injOn hn γ)).ge
  intro B hB
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 hB
  exact rightMul_mem_primitiveReps hn γ hA

end FixedDetMatrices

namespace TauCeti.ModularForm

open FixedDetMatrices

/-! ### Holomorphic coefficients -/

/-- The coefficients of `∏ (X - C (aᵢ τ))` are holomorphic functions of `τ` when every `aᵢ` is. -/
theorem mdifferentiable_coeff_prod_X_sub_C {ι : Type*} (s : Finset ι) {a : ι → ℍ → ℂ}
    (ha : ∀ i ∈ s, MDiff (a i)) (k : ℕ) :
    MDiff fun τ : ℍ ↦ ((∏ i ∈ s, (X - C (a i τ))).coeff k : ℂ) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simpa [coeff_one] using mdifferentiable_const
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, MDiff (a j) := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi, sub_mul, coeff_sub, coeff_C_mul]
    refine MDifferentiable.sub ?_ ((ha i (Finset.mem_insert_self i s)).mul (ih hs k))
    cases k with
    | zero => simpa using mdifferentiable_const
    | succ k => simpa only [coeff_X_mul] using ih hs k

/-! ### The polynomial over the cyclic `n`-isogenies -/

variable (n : ℕ) [NeZero n]

/-- **The polynomial of `f` over the cyclic `n`-isogenies**: `∏ (X - f((a τ + b) / d))` over the
primitive upper-triangular representatives `(a b; 0 d)` of determinant `n`. For `f = j` this is
the classical modular polynomial `Φ_n(X, j(τ))`. -/
noncomputable def cyclicIsogenyPolynomial (f : ℍ → ℂ) (τ : ℍ) : ℂ[X] :=
  ∏ A ∈ primitiveReps (n : ℤ), (X - C (f (toGLReal (NeZero.ne (n : ℤ)) A • τ)))

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
  rwa [cyclicIsogenyPolynomial, Finset.prod_eq_multiset_prod]

/-- **The polynomial over the cyclic `n`-isogenies of an `SL(2, ℤ)`-invariant function is
`SL(2, ℤ)`-invariant**: it takes the same value at `γ τ` as at `τ`. -/
theorem cyclicIsogenyPolynomial_smul {f : ℍ → ℂ} (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    cyclicIsogenyPolynomial n f (γ • τ) = cyclicIsogenyPolynomial n f τ := by
  classical
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  -- the factor of `A` at `γ τ` is the factor at `τ` of the representative of `A γ`
  have hperm (A : FixedDetMatrix (Fin 2) ℤ n) :
      X - C (f (toGLReal hn A • γ • τ)) = X - C (f (toGLReal hn (rightMul hn γ A) • τ)) := by
    rw [toGLReal_rightMul_smul, hf]
  rw [cyclicIsogenyPolynomial, cyclicIsogenyPolynomial, Finset.prod_congr rfl fun A _ ↦ hperm A,
    ← Finset.prod_image (f := fun A ↦ X - C (f (toGLReal hn A • τ)))
      (rightMul_injOn hn γ), image_rightMul]

/-- For an `SL(2, ℤ)`-invariant `f`, the value `f(A τ)` at **every** primitive integral matrix `A`
of determinant `n` is a root of the polynomial over the cyclic `n`-isogenies at `τ`. -/
theorem isRoot_cyclicIsogenyPolynomial {f : ℍ → ℂ}
    (hf : ∀ (γ : SL(2, ℤ)) (τ : ℍ), f (γ • τ) = f τ) {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : IsPrimitive A.1) (τ : ℍ) :
    (cyclicIsogenyPolynomial n f τ).IsRoot
      (f (toGLReal (NeZero.ne (n : ℤ)) A • τ)) := by
  have hn : (n : ℤ) ≠ 0 := NeZero.ne (n : ℤ)
  obtain ⟨g, hg⟩ := exists_smul_mem_primitiveReps hn hA
  rw [IsRoot, cyclicIsogenyPolynomial, eval_prod]
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
  mdifferentiable_coeff_prod_X_sub_C (a := fun A τ ↦ f (toGLReal _ A • τ)) _
    (fun A _ ↦ MDifferentiable.comp hf
      (mdifferentiable_toGLReal_smul (Int.natCast_pos.2 (NeZero.pos n)) A)) k

end TauCeti.ModularForm

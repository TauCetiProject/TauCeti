/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Reflection

/-!
# The form and the reflections of a square matrix on a free module

A square matrix `A` indexed by an arbitrary type `I` defines the bilinear form
`(x, y) ↦ ∑ᵢⱼ xᵢ Aᵢⱼ yⱼ` on the free module `I →₀ R` and, for each `i`, the reflection
`x ↦ x - (∑ⱼ A i j xⱼ) eᵢ` at the basis vector `eᵢ = Finsupp.single i 1`. When `A` is symmetric
with `2` on the diagonal the reflections preserve the form; this is the situation of a Cartan or
Gram matrix, with roots normalised to squared length `2`. Unlike `Matrix.toBilin'`, no finiteness
of `I` is needed, so this covers the geometric representation of a Coxeter system of infinite rank.

Applying a ring homomorphism `f` to the coefficients carries the form and the reflections of `A` to
those of `A.map f`; this is how the integral and the real versions of these reflections, or the
integral version and its reduction modulo `n`, are compared.

## Main definitions

* `Matrix.finsuppBilinForm`: the bilinear form `(x, y) ↦ ∑ᵢⱼ xᵢ Aᵢⱼ yⱼ` on `I →₀ R`.
* `Matrix.finsuppReflection`: the reflection `x ↦ x - (∑ⱼ A i j xⱼ) eᵢ` of `I →₀ R`.

## Main results

* `Matrix.finsuppBilinForm_apply`: the form is the double sum `∑ᵢⱼ xᵢ Aᵢⱼ yⱼ`, and
  `Matrix.finsuppBilinForm_eq_vecMul_dotProduct` compares it with `(x ᵥ* A) ⬝ᵥ y` for finite `I`.
* `Matrix.finsuppReflection_mul_self` and `Matrix.finsuppBilinForm_finsuppReflection`: for `A`
  with `2` on the diagonal the reflections are involutions, and for `A` also symmetric they
  preserve the form.
* `Matrix.map_finsuppBilinForm`, `Matrix.mapRange_finsuppReflection` and
  `Matrix.mapRange_pow_finsuppReflection_mul`: compatibility with ring homomorphisms applied to
  the coefficients.
-/

public section

namespace Matrix

variable {I R S : Type*} [CommRing R] [CommRing S] (A : Matrix I I R)

/-! ### The bilinear form and the reflections of a square matrix -/

/-- The bilinear form `(x, y) ↦ ∑ᵢⱼ xᵢ Aᵢⱼ yⱼ` on the free module `I →₀ R`, whose Gram matrix in
the basis `Finsupp.single i 1` is `A`. -/
noncomputable def finsuppBilinForm : LinearMap.BilinForm R (I →₀ R) :=
  Finsupp.linearCombination R fun i ↦ Finsupp.linearCombination R (A i)

/-- **The Gram matrix of `Matrix.finsuppBilinForm`** in the basis of the `Finsupp.single i 1`. -/
@[simp]
theorem finsuppBilinForm_single_single (i j : I) (a b : R) :
    A.finsuppBilinForm (Finsupp.single i a) (Finsupp.single j b) = a * A i j * b := by
  simp only [finsuppBilinForm, Finsupp.linearCombination_single, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- `Matrix.finsuppBilinForm` as the double sum `∑ᵢⱼ xᵢ Aᵢⱼ yⱼ`. -/
theorem finsuppBilinForm_apply (x y : I →₀ R) :
    A.finsuppBilinForm x y = x.sum fun i a ↦ y.sum fun j b ↦ a * A i j * b := by
  simp only [finsuppBilinForm, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- For a finite index type, `Matrix.finsuppBilinForm` is the usual form `(x ᵥ* A) ⬝ᵥ y` of the
matrix `A` on the underlying functions. -/
theorem finsuppBilinForm_eq_vecMul_dotProduct [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = (⇑x ᵥ* A) ⬝ᵥ ⇑y := by
  simp only [finsuppBilinForm_apply, vecMul, dotProduct, Finset.sum_mul]
  rw [Finsupp.sum_fintype _ _ (by simp), Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finsupp.sum_fintype _ _ (by simp)

/-- **`Matrix.finsuppBilinForm` is symmetric** when `A` is. -/
theorem finsuppBilinForm_comm {A : Matrix I I R} (hA : A.IsSymm) (x y : I →₀ R) :
    A.finsuppBilinForm x y = A.finsuppBilinForm y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
    | single j b =>
      rw [finsuppBilinForm_single_single, finsuppBilinForm_single_single, hA.apply i j]
      ring

/-- **Applying a ring homomorphism to the coefficients** carries the form of `A` to the form of
the image matrix `A.map f`. -/
theorem map_finsuppBilinForm (f : R →+* S) (x y : I →₀ R) :
    f (A.finsuppBilinForm x y) =
      (A.map f).finsuppBilinForm (x.mapRange f (map_zero f)) (y.mapRange f (map_zero f)) := by
  simp only [finsuppBilinForm_apply, map_finsuppSum, map_mul, map_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [Finsupp.sum_mapRange_index (by simp)]

/-- The reflection of `I →₀ R` at the `i`-th basis vector `eᵢ` along the form with Gram matrix
`A`: it sends `x` to `x - (∑ⱼ A i j xⱼ) eᵢ`. This is Mathlib's `Module.preReflection`; it is
an involution when `A i i = 2`. -/
noncomputable def finsuppReflection (i : I) : Module.End R (I →₀ R) :=
  Module.preReflection (Finsupp.single i 1) (A.finsuppBilinForm (Finsupp.single i 1))

/-- **The reflection formula** `x ↦ x - B(eᵢ, x) eᵢ`. -/
@[simp]
theorem finsuppReflection_apply (i : I) (x : I →₀ R) :
    A.finsuppReflection i x =
      x - A.finsuppBilinForm (Finsupp.single i 1) x • Finsupp.single i 1 :=
  Module.preReflection_apply _ _ x

/-- **The reflection at `i` is an involution** when `A i i = 2`. -/
theorem finsuppReflection_mul_self {i : I} (hi : A i i = 2) :
    A.finsuppReflection i * A.finsuppReflection i = 1 :=
  LinearMap.ext <| Module.involutive_preReflection (by simp [hi])

/-- The reflection at `i` of a basis vector: `eⱼ ↦ eⱼ - A i j • eᵢ`. -/
theorem finsuppReflection_single_one (i j : I) :
    A.finsuppReflection i (Finsupp.single j 1) =
      Finsupp.single j 1 - A i j • Finsupp.single i 1 := by
  simp

/-- **The reflections preserve the form** when `A` is symmetric with `2` on the diagonal. -/
theorem finsuppBilinForm_finsuppReflection {A : Matrix I I R} (hA : A.IsSymm) {i : I}
    (hi : A i i = 2) (x y : I →₀ R) :
    A.finsuppBilinForm (A.finsuppReflection i x) (A.finsuppReflection i y) =
      A.finsuppBilinForm x y := by
  simp only [finsuppReflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, finsuppBilinForm_single_single, one_mul, mul_one, hi,
    finsuppBilinForm_comm hA x (Finsupp.single i 1)]
  ring

/-- **Applying a ring homomorphism to the coefficients** intertwines the reflections of `A` and of
the image matrix `A.map f`. -/
theorem mapRange_finsuppReflection (f : R →+* S) (i : I) (x : I →₀ R) :
    (A.finsuppReflection i x).mapRange f (map_zero f) =
      (A.map f).finsuppReflection i (x.mapRange f (map_zero f)) := by
  ext k
  obtain rfl | hk := eq_or_ne i k
  · simp [map_finsuppBilinForm]
  · simp [hk]

/-- **Applying a ring homomorphism to the coefficients** intertwines the powers of a product of two
reflections of `A` with those of the image matrix `A.map f`. -/
theorem mapRange_pow_finsuppReflection_mul (f : R →+* S) (i j : I) (n : ℕ) (x : I →₀ R) :
    (((A.finsuppReflection i * A.finsuppReflection j) ^ n) x).mapRange f (map_zero f) =
      (((A.map f).finsuppReflection i * (A.map f).finsuppReflection j) ^ n)
        (x.mapRange f (map_zero f)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simp only [pow_succ, mul_apply_eq_comp, ih, mapRange_finsuppReflection]

end Matrix

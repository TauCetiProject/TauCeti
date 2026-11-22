/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Substituting `A * X * B` for the generic matrix

Let `R` be a commutative semiring and `ι` a finite index type. For matrices `A` and `B`, the
substitution `f ↦ f (A * X * B)` is an algebra endomorphism of the polynomial functions
`MvPolynomial (ι × ι) R` in the entries of an `ι × ι` matrix. It preserves homogeneous
components, and composing two substitutions multiplies the outer factors. Hence
`GL_ι(R) × GL_ι(R)` acts on `MvPolynomial (ι × ι) R` by

`((g₁, g₂) • f)(X) = f (g₁⁻¹ * X * g₂)`.

## Main definitions

* `Matrix.mvPolynomialSubst A B`: the algebra endomorphism `f ↦ f (A * X * B)` of
  `MvPolynomial (ι × ι) R`.
* `TauCeti.mvPolynomialMatrixRep R ι`: the representation of `GL ι R × GL ι R` on
  `MvPolynomial (ι × ι) R` by `(g₁, g₂) • f = f (g₁⁻¹ * X * g₂)`.

## Main results

* `Matrix.aeval_mvPolynomialSubst`: evaluating `f (A * X * B)` at `Z` evaluates `f` at
  `A * Z * B`.
* `Matrix.mvPolynomialSubst_comp_mvPolynomialSubst`: composition of substitutions.
* `MvPolynomial.IsHomogeneous.mvPolynomialSubst`: substitution preserves homogeneous components.
-/

public section

open MvPolynomial

namespace Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The substitution of `A * X * B` for the generic matrix `X`: the algebra endomorphism of the
polynomial functions in the entries of an `ι × ι` matrix sending `f` to `X ↦ f (A * X * B)`. -/
noncomputable def mvPolynomialSubst (A B : Matrix ι ι R) :
    MvPolynomial (ι × ι) R →ₐ[R] MvPolynomial (ι × ι) R :=
  aeval fun p ↦ (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R))
    p.1 p.2

/-- The defining formula of `Matrix.mvPolynomialSubst`. -/
theorem mvPolynomialSubst_apply (A B : Matrix ι ι R) (f : MvPolynomial (ι × ι) R) :
    mvPolynomialSubst A B f = aeval (fun p ↦
      (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2)
        f := (rfl)

/-- Substitution replaces the variable `X (i, j)` by the `(i, j)` entry of `A * X * B`. -/
@[simp]
theorem mvPolynomialSubst_X (A B : Matrix ι ι R) (p : ι × ι) :
    mvPolynomialSubst A B (X p) =
      (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2 :=
  aeval_X _ _

/-- Evaluating `f (A * X * B)` at a matrix `Z` evaluates `f` at `A * Z * B`. -/
theorem aeval_mvPolynomialSubst {S : Type*} [CommSemiring S] [Algebra R S] (A B : Matrix ι ι R)
    (Z : Matrix ι ι S) (f : MvPolynomial (ι × ι) R) :
    aeval (fun p ↦ Z p.1 p.2) (mvPolynomialSubst A B f) =
      aeval (fun p ↦ (A.map (algebraMap R S) * Z * B.map (algebraMap R S)) p.1 p.2) f := by
  rw [mvPolynomialSubst_apply, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext p
  simp [Matrix.mul_apply, Finset.sum_mul]

/-- The entries of `A * X * B` are linear forms. -/
theorem isHomogeneous_map_mul_mvPolynomialX_mul_map_apply (A B : Matrix ι ι R) (i j : ι) :
    (A.map C * mvPolynomialX ι ι R * B.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) i j
      |>.IsHomogeneous 1 := by
  simp only [Matrix.mul_apply, Matrix.map_apply, mvPolynomialX_apply]
  exact IsHomogeneous.sum _ _ _ fun k _ ↦ by
    simpa using (IsHomogeneous.sum _ _ _ fun l _ ↦
      (isHomogeneous_C_mul_X (A i l) (l, k))).mul (isHomogeneous_C _ (B k j))

/-- Substitution sends the generic matrix `X` to `A * X * B`. -/
@[simp]
theorem mvPolynomialX_map_mvPolynomialSubst (A B : Matrix ι ι R) :
    (mvPolynomialX ι ι R).map (mvPolynomialSubst A B) =
      A.map C * mvPolynomialX ι ι R * B.map C := by
  ext i j
  simp only [map_apply, mvPolynomialX_apply, mvPolynomialSubst_X]

/-- Substituting `1 * X * 1` is the identity. -/
@[simp]
theorem mvPolynomialSubst_one_one [DecidableEq ι] :
    mvPolynomialSubst (1 : Matrix ι ι R) 1 = AlgHom.id R (MvPolynomial (ι × ι) R) := by
  refine algHom_ext fun p ↦ ?_
  rw [mvPolynomialSubst_X, ← RingHom.mapMatrix_apply, map_one, Matrix.one_mul, Matrix.mul_one]
  simp

/-- Substituting `A' * X * B'` and then `A * X * B` substitutes `A' * A * X * B * B'`. -/
theorem mvPolynomialSubst_comp_mvPolynomialSubst (A B A' B' : Matrix ι ι R) :
    (mvPolynomialSubst A B).comp (mvPolynomialSubst A' B') =
      mvPolynomialSubst (A' * A) (B * B') := by
  classical
  refine algHom_ext fun p ↦ ?_
  have hC (M : Matrix ι ι R) : (mvPolynomialSubst A B).mapMatrix (M.map C) = M.map C := by
    ext i j
    simp
  rw [AlgHom.comp_apply, mvPolynomialSubst_X, mvPolynomialSubst_X]
  calc mvPolynomialSubst A B
        ((A'.map C * mvPolynomialX ι ι R * B'.map C : Matrix ι ι (MvPolynomial (ι × ι) R)) p.1 p.2)
      = (mvPolynomialSubst A B).mapMatrix (A'.map C * mvPolynomialX ι ι R * B'.map C) p.1 p.2 := by
        rw [AlgHom.mapMatrix_apply, map_apply]
    _ = _ := by
      rw [map_mul, map_mul, hC, hC, AlgHom.mapMatrix_apply, mvPolynomialX_map_mvPolynomialSubst,
        Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]

end Matrix

namespace MvPolynomial.IsHomogeneous

open Matrix

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Substitution of `A * X * B` for the generic matrix preserves homogeneous polynomials and
their degree. -/
theorem mvPolynomialSubst {f : MvPolynomial (ι × ι) R} {d : ℕ} (hf : f.IsHomogeneous d)
    (A B : Matrix ι ι R) : (mvPolynomialSubst A B f).IsHomogeneous d := by
  rw [mvPolynomialSubst_apply]
  simpa only [one_mul] using
    hf.aeval _ fun p ↦ isHomogeneous_map_mul_mvPolynomialX_mul_map_apply A B p.1 p.2

end MvPolynomial.IsHomogeneous

namespace TauCeti

open Matrix

variable (R ι : Type*) [CommSemiring R] [Fintype ι] [DecidableEq ι]

/-- The representation of `GL ι R × GL ι R` on the polynomial functions in the entries of an
`ι × ι` matrix by `((g₁, g₂) • f)(X) = f (g₁⁻¹ * X * g₂)`. -/
noncomputable def mvPolynomialMatrixRep :
    Representation R (GL ι R × GL ι R) (MvPolynomial (ι × ι) R) where
  toFun g := (mvPolynomialSubst (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R)).toLinearMap
  map_one' := LinearMap.ext fun f ↦ by simp
  map_mul' g h := LinearMap.ext fun f ↦ by
    simp only [Module.End.mul_eq_comp, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      ← AlgHom.comp_apply, mvPolynomialSubst_comp_mvPolynomialSubst]
    simp

variable {R ι}

/-- The defining formula of `TauCeti.mvPolynomialMatrixRep`. -/
theorem mvPolynomialMatrixRep_apply (g : GL ι R × GL ι R) (f : MvPolynomial (ι × ι) R) :
    mvPolynomialMatrixRep R ι g f =
      mvPolynomialSubst (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R) f := (rfl)

/-- The representation acts by algebra automorphisms. -/
@[simp]
theorem mvPolynomialMatrixRep_mul (g : GL ι R × GL ι R) (f f' : MvPolynomial (ι × ι) R) :
    mvPolynomialMatrixRep R ι g (f * f') =
      mvPolynomialMatrixRep R ι g f * mvPolynomialMatrixRep R ι g f' := by
  simp only [mvPolynomialMatrixRep_apply, map_mul]

/-- Evaluating `(g₁, g₂) • f` at a matrix `Z` evaluates `f` at `g₁⁻¹ * Z * g₂`. -/
theorem eval_mvPolynomialMatrixRep (g : GL ι R × GL ι R) (f : MvPolynomial (ι × ι) R)
    (Z : Matrix ι ι R) :
    eval (fun p ↦ Z p.1 p.2) (mvPolynomialMatrixRep R ι g f) =
      eval (fun p ↦ ((g.1⁻¹ : GL ι R) * Z * (g.2 : Matrix ι ι R) : Matrix ι ι R) p.1 p.2) f := by
  simpa [mvPolynomialMatrixRep_apply] using
    aeval_mvPolynomialSubst (S := R) (g.1⁻¹ : GL ι R) (g.2 : Matrix ι ι R) Z f

/-- The representation preserves homogeneous polynomials and their degree. -/
theorem isHomogeneous_mvPolynomialMatrixRep {f : MvPolynomial (ι × ι) R} {d : ℕ}
    (hf : f.IsHomogeneous d) (g : GL ι R × GL ι R) :
    (mvPolynomialMatrixRep R ι g f).IsHomogeneous d :=
  hf.mvPolynomialSubst _ _

end TauCeti

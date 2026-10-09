/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import TauCeti.LinearAlgebra.Determinant.Projective

/-!
# The norm of a finite locally free algebra

Let `S` be an `R`-algebra which is finite projective as an `R`-module, that is, finite locally free
over `R`. Mathlib's `Algebra.norm R` is the determinant of multiplication when `S` has a finite
basis over `R`, and is `1` otherwise. This file defines the norm
`Algebra.projectiveNorm R : S →* R` as the determinant `LinearMap.projectiveDet` of multiplication,
which is defined for every finite projective module. It agrees with `Algebra.norm R` when `S` is
free (`Algebra.projectiveNorm_eq_norm`), commutes with arbitrary base change
(`Algebra.projectiveNorm_baseChange_tmul`), is invariant under isomorphisms of algebras, and
detects units.

Geometrically, for a finite locally free morphism `Spec S ⟶ Spec R`, this is the norm
`Norm_{S/R} : S → R` of functions, whose compatibility with base change is the compatibility of the
norm with pullback along every `Spec A ⟶ Spec R`. Full sets of sections of a finite locally free
scheme over a base are defined by an identity between this norm and a product of values of
sections, required after every base change (Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*,
1.8).

## Main definitions

* `Algebra.projectiveNorm R`: the norm of a finite projective `R`-algebra.

## Main results

* `Algebra.projectiveNorm_eq_norm`: for a free algebra of finite rank, `projectiveNorm` is
  `Algebra.norm`.
* `Algebra.projectiveNorm_baseChange_tmul`: the norm commutes with base change along any ring
  homomorphism.
* `Algebra.projectiveNorm_eq_of_algEquiv`: the norm is invariant under isomorphisms of algebras.
* `Algebra.isUnit_projectiveNorm_iff`: an element is a unit if and only if its norm is.

## References

* The Stacks Project, Tag 0BIF (the norm of a finite locally free algebra).
* N. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 1.8.
-/

public section

open Module TensorProduct

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [Ring S] [Algebra R S] [Module.Finite R S]
  [Module.Projective R S]

/-- The **norm** of an element `x` of an `R`-algebra `S` which is finite projective as an
`R`-module: the determinant `LinearMap.projectiveDet` of multiplication by `x`. It is
`Algebra.norm R x` when `S` is free over `R` (`projectiveNorm_eq_norm`). -/
@[stacks 0BIF "Norm"]
noncomputable def projectiveNorm : S →* R :=
  LinearMap.projectiveDet.comp (lmul R S).toRingHom.toMonoidHom

theorem projectiveNorm_apply (x : S) :
    projectiveNorm R x = LinearMap.projectiveDet (lmul R S x) :=
  (rfl)

/-- For an algebra which is free of finite rank, `projectiveNorm` is the norm `Algebra.norm`. -/
@[simp]
theorem projectiveNorm_eq_norm [Module.Free R S] (x : S) : projectiveNorm R x = norm R x := by
  rw [projectiveNorm_apply, LinearMap.projectiveDet_eq_det, norm_apply]

variable {R}

/-- The norm of a finite projective algebra commutes with base change: the norm of `1 ⊗ x` in
`A ⊗[R] S` over `A` is the image in `A` of the norm of `x` over `R`. -/
@[simp]
theorem projectiveNorm_baseChange_tmul (A : Type*) [CommRing A] [Algebra R A] (x : S) :
    projectiveNorm A ((1 : A) ⊗ₜ[R] x) = algebraMap R A (projectiveNorm R x) := by
  rw [projectiveNorm_apply, projectiveNorm_apply, ← baseChange_lmul,
    LinearMap.projectiveDet_baseChange]

/-- The norm of a finite projective algebra is invariant under isomorphisms of algebras. -/
theorem projectiveNorm_eq_of_algEquiv {T : Type*} [Ring T] [Algebra R T] [Module.Finite R T]
    [Module.Projective R T] (e : S ≃ₐ[R] T) (x : S) :
    projectiveNorm R (e x) = projectiveNorm R x := by
  have h : lmul R T (e x) = (e.toLinearEquiv : S →ₗ[R] T) ∘ₗ lmul R S x ∘ₗ
      (e.toLinearEquiv.symm : T →ₗ[R] S) := by
    ext y
    simp
  rw [projectiveNorm_apply, projectiveNorm_apply, h, LinearMap.projectiveDet_conj]

/-- An element of a finite projective algebra is a unit if and only if its norm is a unit. -/
@[simp]
theorem isUnit_projectiveNorm_iff {x : S} : IsUnit (projectiveNorm R x) ↔ IsUnit x := by
  rw [projectiveNorm_apply, ← LinearMap.isUnit_iff_isUnit_projectiveDet, lmul_isUnit_iff]

end Algebra

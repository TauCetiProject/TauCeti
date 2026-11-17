/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Descending a nonsingular intertwining matrix to a smaller ring

Let `K` be an algebra over an infinite integral domain `F`, projective (for instance free) as an
`F`-module. A nonsingular matrix `X` over `K` need not have a nonsingular entrywise image under a
given `F`-linear functional `K → F`, but it has one under *some* functional: writing the entries of
`X` in coordinates given by a splitting of `K` off a free `F`-module, the determinant of the generic
image is a nonzero polynomial over `F` in the coordinates of the functional, and a nonzero
polynomial over an infinite domain does not vanish everywhere (`MvPolynomial.funext`). This is
`Matrix.exists_linearMap_det_map_ne_zero`.

An `F`-linear functional respects every linear relation with coefficients in `F` between the
entries. So if a nonsingular matrix over `K` intertwines two families of matrices over `F`,
`B s * X = X * A s`, then so does a nonsingular matrix over `F`
(`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap`). This is the matrix form of the
Noether–Deuring theorem for an infinite base field: representations over `F` which become
isomorphic over `K` are already isomorphic over `F`.

With `F = ℚ` this applies to integral representations that become isomorphic over a `ℚ`-algebra,
for instance over `ℝ`: their rationalizations are then isomorphic, which is the algebraic content of
Tate's lemma on lattices in a real representation.

## Main results

* `Matrix.exists_linearMap_det_map_ne_zero`: a nonsingular matrix over `K` has a nonsingular image
  under some `F`-linear functional `K → F`.
* `Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap`: a nonsingular matrix over `K`
  intertwining two families of matrices over `F` can be replaced by one over `F`.
* `Matrix.map_algebraMap_mul`, `Matrix.map_mul_algebraMap`: an `F`-linear functional applied
  entrywise commutes with multiplication by a matrix over `F`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, the Herbrand quotient of the unit group.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §29 (the Noether–Deuring theorem).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **A nonsingular matrix descends along some linear functional.** If `K` is an algebra over an
infinite integral domain `F` which is projective (for instance free) as an `F`-module, then every
matrix over `K` with nonzero determinant has, under some `F`-linear functional `f : K → F` applied
entrywise, an image with nonzero determinant. -/
theorem exists_linearMap_det_map_ne_zero [DecidableEq n] {F K : Type*} [CommRing F] [IsDomain F]
    [Infinite F] [CommRing K] [Algebra F K] [Module.Projective F K] {X : Matrix n n K}
    (hX : X.det ≠ 0) :
    ∃ f : K →ₗ[F] F, (X.map f).det ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def.mp ‹Module.Projective F K›
  -- the generic functional: `s` writes `k` as a formal combination of elements of `K`, and `ℓ`
  -- replaces each of these elements by the corresponding variable
  let ℓ : K →ₗ[F] MvPolynomial K F := Finsupp.linearCombination F MvPolynomial.X ∘ₗ s
  have hℓ (k : K) : MvPolynomial.aeval id (ℓ k) = k := by
    simpa [ℓ, Finsupp.linearCombination_apply, map_finsuppSum] using hs k
  have hP : (X.map ℓ).det ≠ 0 := fun h ↦ hX <| by
    simpa [AlgHom.map_det, Function.comp_def, hℓ] using congrArg (MvPolynomial.aeval id) h
  obtain ⟨q, hq⟩ : ∃ q, MvPolynomial.eval q (X.map ℓ).det ≠ 0 := by
    simpa [MvPolynomial.funext_iff] using hP
  refine ⟨(MvPolynomial.aeval q).toLinearMap ∘ₗ ℓ, ?_⟩
  simpa [RingHom.map_det, MvPolynomial.coe_aeval_eq_eval] using hq

/-- An `F`-linear functional applied entrywise commutes with left multiplication by a matrix over
`F`. -/
@[simp]
theorem map_algebraMap_mul {l m o F K : Type*} [Fintype m] [CommSemiring F] [Semiring K]
    [Algebra F K] (f : K →ₗ[F] F) (C : Matrix l m F) (X : Matrix m o K) :
    (C.map (algebraMap F K) * X).map f = C * X.map f := by
  ext i j
  simp [Matrix.mul_apply, ← Algebra.smul_def]

/-- An `F`-linear functional applied entrywise commutes with right multiplication by a matrix over
`F`. -/
@[simp]
theorem map_mul_algebraMap {l m o F K : Type*} [Fintype m] [CommSemiring F] [Semiring K]
    [Algebra F K] (f : K →ₗ[F] F) (C : Matrix m o F) (X : Matrix l m K) :
    (X * C.map (algebraMap F K)).map f = X.map f * C := by
  ext i j
  simp [Matrix.mul_apply, ← Algebra.commutes, ← Algebra.smul_def, mul_comm]

/-- **A nonsingular intertwiner descends to an infinite base ring.** Let `K` be an algebra over an
infinite integral domain `F`, projective (for instance free) as an `F`-module, and let `A s` and
`B s` be two families of matrices over `F`. If a matrix `X` over `K` with nonzero determinant
satisfies `B s * X = X * A s` for every `s`, after mapping `A s` and `B s` to `K`, then so does a
matrix over `F` with nonzero determinant. This is the matrix form of the Noether–Deuring theorem
for an infinite field. -/
theorem exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap [DecidableEq n] {ι F K : Type*}
    [CommRing F] [IsDomain F] [Infinite F] [CommRing K] [Algebra F K] [Module.Projective F K]
    (A B : ι → Matrix n n F) {X : Matrix n n K} (hX : X.det ≠ 0)
    (hAB : ∀ s, (B s).map (algebraMap F K) * X = X * (A s).map (algebraMap F K)) :
    ∃ Y : Matrix n n F, Y.det ≠ 0 ∧ ∀ s, B s * Y = Y * A s := by
  obtain ⟨f, hf⟩ := exists_linearMap_det_map_ne_zero (F := F) hX
  exact ⟨X.map f, hf, fun s ↦ by simpa using congrArg (Matrix.map · f) (hAB s)⟩

end Matrix

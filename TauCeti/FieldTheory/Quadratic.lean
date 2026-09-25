/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Algebra.trace` occurs in the statements below, and `Algebra.trace_eq_matrix_trace` computes it.
public import Mathlib.RingTheory.Trace.Defs
-- `Algebra.norm` occurs in the statements below, and `Algebra.norm_eq_matrix_det` computes it.
public import Mathlib.RingTheory.Norm.Defs
-- Non-public: the matrix of multiplication by `x` in the basis `(1, x)` is the companion matrix
-- `TauCeti.companionFinTwo`, whose trace and determinant are already known; used in proofs only.
import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo
-- Non-public: `basisOfLinearIndependentOfCardEqFinrank` builds that basis, inside a proof only.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
-- Non-public: `TauCeti.linearIndependent_one_of_notMem_range_algebraMap` gives the
-- independence of `1` and `x` that the basis rests on; used in a proof only.
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
-- Non-public: the extension theory of finite fields supplies the root of an irreducible quadratic,
-- inside a proof only.
import Mathlib.FieldTheory.Finite.Extension
-- Non-public: a quadratic without a root is irreducible, used only to build `AdjoinRoot`.
import Mathlib.Algebra.Polynomial.SpecificDegree
-- Non-public: `AdjoinRoot` and its power basis are the source of that root.
import Mathlib.RingTheory.AdjoinRoot
-- Non-public: `Matrix.aeval_self_charpoly` and `Matrix.charpoly_fin_two` are Cayley-Hamilton in
-- size two, used only in the proof of the trace-norm quadratic.
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The trace and the norm of a quadratic irrationality

An element `x` of a degree-`2` extension `E/F` that does not lie in `F` satisfies a monic quadratic
`x² = t x - d` over `F`, and the pair `(1, x)` is then an `F`-basis of `E`. In that basis
multiplication by `x` **is** the companion matrix `TauCeti.companionFinTwo t d` of `X² - t X + d`,
which is the reading of the companion matrix its own docstring advertises. Since the trace and the
norm of `x` are the trace and the determinant of that matrix, and both are basis independent,
`Tr_{E/F} x = t` and `N_{E/F} x = d`.

These are what pin the elliptic normal form of `GL₂` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NormalForm.lean`, where the quadratic is the
characteristic polynomial of a matrix and `x` is the eigenvalue it acquires in `E`.

Read in the other direction, every `x : E` satisfies the quadratic built from its own trace and
norm, `x² = Tr_{E/F}(x) · x - N_{E/F}(x)`, with no hypothesis on `x`: what the `x ∉ F` hypothesis
buys the two theorems above is not the equation but the *uniqueness* of its coefficients. This is
what separates the elliptic conjugacy classes of `GL₂(F)` from the split ones, an eigenvalue in `E`
outside `F` being exactly what a split class does not have.

Over a *finite* base field such an `x` always exists as soon as the quadratic has no root in `F`:
the quadratic is then irreducible, so `AdjoinRoot` of it is a degree-`2` extension of `F`, and any
two extensions of a finite field of the same degree are isomorphic
(`FiniteField.algEquivExtension`), so every degree-`2` extension already contains a root.

## Main results

* `TauCeti.Algebra.trace_eq_of_mul_self_eq` and `TauCeti.Algebra.norm_eq_of_mul_self_eq`: the trace
  and the norm of an element `x` of a degree-`2` extension satisfying `x² = t x - d`, and lying
  outside the base field, are `t` and `d`.
* `TauCeti.Algebra.mul_self_eq_trace_mul_sub_norm`: conversely, every element of a degree-`2`
  extension satisfies the quadratic built from its own trace and norm.
* `TauCeti.exists_mul_self_eq_of_finite`: over a finite field, a quadratic with no root in `F` has
  a root in every degree-`2` extension.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
-/

public section

open Polynomial

namespace TauCeti

variable {F : Type*} [Field F]

/-! ### The basis `(1, x)` -/

section Basis

variable {E : Type*} [Field E] [Algebra F E]

/-- The `F`-basis `(1, x)` of a degree-`2` extension `E/F` attached to an element `x` outside `F`.
It is used only to compute the trace and the norm of `x`, both of which are basis independent. -/
private noncomputable def oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : Module.Basis (Fin 2) F E :=
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  basisOfLinearIndependentOfCardEqFinrank (b := ![1, x])
    (TauCeti.linearIndependent_one_of_notMem_range_algebraMap F E hx) (by simp [hE])

private theorem coe_oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : ⇑(oneRootBasis hE hx) = ![1, x] := by
  simp only [oneRootBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

/-- In the basis `(1, x)`, multiplication by `x` **is** the companion matrix of the monic quadratic
that `x` satisfies. -/
private theorem leftMulMatrix_oneRootBasis (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.leftMulMatrix (oneRootBasis hE hx) x = companionFinTwo t d := by
  have hb := coe_oneRootBasis hE hx
  have e0 : x * oneRootBasis hE hx 0 = oneRootBasis hE hx 1 := by
    simp [hb]
  have e1 : x * oneRootBasis hE hx 1
      = (-d) • oneRootBasis hE hx 0 + t • oneRootBasis hE hx 1 := by
    simp only [hb, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one, map_neg]
    linear_combination hx2
  rw [companionFinTwo_def]
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j <;> fin_cases i <;> simp [e0, e1]

end Basis

/-! ### The trace and the norm -/

namespace Algebra

variable {E : Type*} [Field E] [Algebra F E]

/-- **The trace of a quadratic irrationality.** If `E/F` has degree `2` and `x : E` lies outside
`F` and satisfies `x² = t x - d`, then `Tr_{E/F} x = t`. -/
theorem trace_eq_of_mul_self_eq (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.trace F E x = t := by
  rw [Algebra.trace_eq_matrix_trace (oneRootBasis hE hx), leftMulMatrix_oneRootBasis hE hx hx2,
    trace_companionFinTwo]

/-- **The norm of a quadratic irrationality.** If `E/F` has degree `2` and `x : E` lies outside `F`
and satisfies `x² = t x - d`, then `N_{E/F} x = d`. -/
theorem norm_eq_of_mul_self_eq (hE : Module.finrank F E = 2) {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : x * x = algebraMap F E t * x - algebraMap F E d) :
    Algebra.norm F x = d := by
  rw [Algebra.norm_eq_matrix_det (oneRootBasis hE hx), leftMulMatrix_oneRootBasis hE hx hx2,
    det_companionFinTwo]

/-- **An element of a quadratic extension satisfies the quadratic built from its own trace and
norm**: if `E/F` has degree `2` then `x² = Tr_{E/F}(x) · x - N_{E/F}(x)` for every `x : E`, with no
hypothesis on `x`. Together with `TauCeti.Algebra.trace_eq_of_mul_self_eq` and
`TauCeti.Algebra.norm_eq_of_mul_self_eq` this makes `(Tr x, N x)` the *unique* pair of coefficients
of a monic quadratic over `F` satisfied by an `x` outside `F`. For an `x` inside `F` the equation
still holds, `Tr x` being `2 x` and `N x` being `x²`, but the pair is no longer unique there, the
minimal polynomial being linear. This is what separates the elliptic conjugacy classes of `GL₂(F)`
from the split ones in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NormalForm.lean`: matching the trace and the
determinant of a split or a Jordan normal form makes `x` a root of that form's characteristic
polynomial, whose roots lie in `F`. -/
theorem mul_self_eq_trace_mul_sub_norm (hE : Module.finrank F E = 2) (x : E) :
    x * x = algebraMap F E (Algebra.trace F E x) * x - algebraMap F E (Algebra.norm F x) := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  set b := Module.finBasisOfFinrankEq F E hE
  have h : Polynomial.aeval x (Algebra.leftMulMatrix b x).charpoly = 0 :=
    Algebra.leftMulMatrix_injective b (by
      rw [← Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero])
  rw [Matrix.charpoly_fin_two, ← Algebra.trace_eq_matrix_trace b,
    ← Algebra.norm_eq_matrix_det b] at h
  simp only [map_add, map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h
  linear_combination h

end Algebra

/-! ### A root of the quadratic in the extension -/

/-- **Over a finite field a quadratic without a root has a root in every degree-`2` extension.**
A quadratic with no root in `F` is irreducible, so `AdjoinRoot` of it is a degree-`2` extension of
`F`; over a finite field any two extensions of the same degree are isomorphic, so the supplied `E`
already contains a root. -/
theorem exists_mul_self_eq_of_finite [Finite F] (E : Type*) [Field E] [Algebra F E]
    (hE : Module.finrank F E = 2) {t d : F} (hroot : ∀ a : F, a * a ≠ t * a - d) :
    ∃ x : E, x * x = algebraMap F E t * x - algebraMap F E d := by
  classical
  have key : ∃ y : E, (Polynomial.aeval y) (X ^ 2 - C t * X + C d : F[X]) = 0 := by
    set p : F[X] := X ^ 2 - C t * X + C d with hpdef
    have hdeg : p.natDegree = 2 := by rw [hpdef]; compute_degree!
    have hmonic : p.Monic := by rw [hpdef]; monicity!
    have hirr : Irreducible p := by
      refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by simp [hdeg]) fun a ha => ?_
      refine hroot a ?_
      rw [Polynomial.IsRoot, hpdef] at ha
      simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_C, eval_X] at ha
      linear_combination ha
    have : Fact (Irreducible p) := ⟨hirr⟩
    have hfr : Module.finrank F (AdjoinRoot p) = 2 := by
      rw [PowerBasis.finrank (AdjoinRoot.powerBasis hmonic.ne_zero), AdjoinRoot.powerBasis_dim,
        hdeg]
    obtain ⟨q, hq⟩ := CharP.exists F
    have : Fact q.Prime := ⟨CharP.char_is_prime F q⟩
    let e : AdjoinRoot p ≃ₐ[F] E :=
      (FiniteField.algEquivExtension F q 2 (AdjoinRoot p) hfr).trans
        (FiniteField.algEquivExtension F q 2 E hE).symm
    refine ⟨e (AdjoinRoot.root p), ?_⟩
    rw [Polynomial.aeval_algHom_apply e, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  obtain ⟨y, hy⟩ := key
  simp only [map_add, map_sub, map_pow, map_mul, aeval_C, aeval_X] at hy
  exact ⟨y, by linear_combination hy⟩

end TauCeti

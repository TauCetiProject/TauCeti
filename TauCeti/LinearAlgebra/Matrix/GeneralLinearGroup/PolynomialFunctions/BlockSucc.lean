/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.PolynomialFunctions.Basic

/-!
# Polynomial and rational functions under the block inclusion

The block inclusion `TauCeti.glBlockSucc : GL (Fin n) k →* GL (Fin (n + 1)) k` replaces a
matrix `g` by `diag(g, 1)`.  Substitution of this block matrix into a polynomial in the entries of
an `(n + 1)`-square matrix again gives a polynomial in the entries of `g`.  Moreover the block
inclusion preserves determinants.  Consequently polynomial and rational functions pull back along
the inclusion.

## Main results

* `TauCeti.Matrix.GeneralLinearGroup.comp_glBlockSucc_mem_polynomialFunctions` and
  `TauCeti.Matrix.GeneralLinearGroup.comp_glBlockSucc_mem_rationalFunctions`: polynomial and
  rational functions pull back along the block inclusion.
-/

public section

open Matrix MvPolynomial

universe u

namespace TauCeti

section BlockSuccPolynomial

variable {k : Type u} [CommSemiring k] {n : ℕ}

/-- Substitute the generic block matrix `diag(X, 1)` into a polynomial in the entries of an
`(n + 1)`-square matrix. -/
private noncomputable def blockSuccPolynomial
    (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) k) :
    MvPolynomial (Fin n × Fin n) k :=
  MvPolynomial.aeval (fun p =>
    Matrix.blockSucc (Matrix.mvPolynomialX (Fin n) (Fin n) k) p.1 p.2) P

/-- Evaluating after substitution by the generic block matrix is evaluation at the corresponding
concrete block matrix. -/
private theorem eval_blockSuccPolynomial
    (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) k)
    (M : Matrix (Fin n) (Fin n) k) :
    MvPolynomial.eval (fun p => M p.1 p.2) (blockSuccPolynomial P) =
      MvPolynomial.eval (fun p => Matrix.blockSucc M p.1 p.2) P := by
  rw [blockSuccPolynomial, ← MvPolynomial.aeval_eq_eval, MvPolynomial.comp_aeval_apply,
    ← MvPolynomial.aeval_eq_eval]
  apply congrArg (fun f => MvPolynomial.aeval f P)
  funext p
  induction p.1 using Fin.lastCases with
  | last =>
      induction p.2 using Fin.lastCases with
      | last => simp
      | cast j => simp
  | cast i =>
      induction p.2 using Fin.lastCases with
      | last => simp
      | cast j => simp

end BlockSuccPolynomial

namespace Matrix.GeneralLinearGroup

section CommSemiring

variable {k : Type u} [CommSemiring k] {n : ℕ}

/-- **A polynomial function pulls back to a polynomial function along the block inclusion.** -/
theorem comp_glBlockSucc_mem_polynomialFunctions
    {f : GL (Fin (n + 1)) k → k} (hf : f ∈ polynomialFunctions k (n + 1)) :
    (fun g => f (glBlockSucc k n g)) ∈ polynomialFunctions k n := by
  obtain ⟨P, hP⟩ := mem_polynomialFunctions.mp hf
  refine mem_polynomialFunctions.mpr ⟨blockSuccPolynomial P, fun g => ?_⟩
  rw [hP, eval_blockSuccPolynomial, coe_glBlockSucc]

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

/-- **A rational function pulls back to a rational function along the block inclusion.**  The
denominator remains the same power because `diag(g, 1)` has determinant `det g`. -/
theorem comp_glBlockSucc_mem_rationalFunctions
    {f : GL (Fin (n + 1)) k → k} (hf : f ∈ rationalFunctions k (n + 1)) :
    (fun g => f (glBlockSucc k n g)) ∈ rationalFunctions k n := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions.mp hf
  refine mem_rationalFunctions.mpr ⟨blockSuccPolynomial P, m, fun g => ?_⟩
  simpa only [coe_glBlockSucc, det_blockSucc, eval_blockSuccPolynomial] using
    hP (glBlockSucc k n g)

end CommRing

end Matrix.GeneralLinearGroup

end TauCeti

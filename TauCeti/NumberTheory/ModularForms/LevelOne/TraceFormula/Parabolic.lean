/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Parabolic
public import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.Trace

/-!
# The zero parabolic automorphism-weighted trace contribution

A parabolic integral matrix is nonscalar with discriminant zero. Its centralizer in `SL(2, ℤ)`
is infinite, so its automorphism weight is zero, under the convention that `Nat.card` of an
infinite type is zero and division by zero is zero. Thus the sum of the binary-form traces
weighted by `2 / |Z_SL(M)|` over the parabolic conjugacy classes of any fixed trace and
determinant is zero.

Scalar classes are deliberately excluded: although their discriminant also vanishes, their
trace-formula weight is a separate volume term, not an inverse-centralizer weight. The result
here computes the automorphism-weighted side of the parabolic contribution; identifying the
conjugacy-class sums of the coefficients of Popa–Zagier's element with these weights is a
separate assertion.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1 and §4.
-/

public section

open Matrix MulAction MulOpposite MvPolynomial
open scoped MatrixGroups

namespace TauCeti

/-- A parabolic conjugacy class in a fixed trace-and-determinant fibre has infinite
stabilizer, hence stabilizer cardinality zero in `ℕ`. -/
theorem cardStabilizerOnOrbit_eq_zero_of_isParabolic {t n : ℤ}
    (X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n))
    (hX : (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ).IsParabolic) :
    cardStabilizerOnOrbit X = 0 := by
  have hcard := card_stabilizer_congr (MulEquiv.refl (ConjAct SL(2, ℤ)))
    (f := fun M : traceDetFiber (Fin 2) t n ↦ (M : Matrix (Fin 2) (Fin 2) ℤ))
    X.out (fun _ ↦ rfl) (fun _ h ↦ Subtype.ext h)
  have : Infinite (stabilizer (ConjAct SL(2, ℤ))
      (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ)) := infinite_stabilizer_of_isParabolic _ hX
  have hzero : Nat.card (stabilizer (ConjAct SL(2, ℤ)) X.out) = 0 :=
    hcard.symm.trans Nat.card_eq_zero_of_infinite
  simpa only [← cardStabilizerOnOrbit_mk, Quotient.out_eq] using hzero

/-- **The parabolic automorphism-weighted contribution is zero.** Summing the traces on
binary forms of degree `w` over the nonscalar repeated-eigenvalue conjugacy classes of any
fixed trace and determinant, with the weights `2 / |Z_SL(M)|`, gives zero. No finiteness of
the set of parabolic conjugacy classes is assumed. -/
theorem finsum_parabolic_binaryForm_trace {K : Type*} [Field K] (w : ℕ) (t n : ℤ) :
    ∑ᶠ X : {X : orbitRel.Quotient (ConjAct SL(2, ℤ)) (traceDetFiber (Fin 2) t n) //
        (X.out.1 : Matrix (Fin 2) (Fin 2) ℤ).IsParabolic},
      (2 / (cardStabilizerOnOrbit X.1 : K)) *
        LinearMap.trace K (homogeneousSubmodule (Fin 2) K w)
          (binaryFormRep K w (op (X.1.out.1 : Matrix (Fin 2) (Fin 2) ℤ))) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro X
  rw [cardStabilizerOnOrbit_eq_zero_of_isParabolic X.1 X.2, Nat.cast_zero, div_zero, zero_mul]

end TauCeti

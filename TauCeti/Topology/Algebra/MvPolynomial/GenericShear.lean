/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.LineRestriction
public import TauCeti.Topology.Algebra.MvPolynomial.Nonvanishing
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Generic shears have constant nonzero leading coefficients

For a finite family of polynomials, the directions `i.insertNth 1 a`, with 1 in coordinate `i`
and `a` in the remaining coordinates, on which every nonzero equation's top homogeneous
component is nonzero form an open dense set. Together with
`MvPolynomial.coeff_shearToPolynomial_totalDegree` and
`MvPolynomial.natDegree_shearToPolynomial_eq_of_eval_ne_zero`, this makes each sheared equation
a polynomial in the distinguished coordinate with constant nonzero leading coefficient.
Zero equations impose no restriction; constants and the case of one original variable are
included.

This is the generic-direction input to cylindrical frontier preparation and semialgebraic
triangulation. The algebraic ingredients are dehomogenization injectivity on a fixed
homogeneous degree and polynomial nonvanishing density.

## References

* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, §9.1,
  Proposition 9.1.2, for the generic-direction preparation argument.
-/

public section

open MvPolynomial Set

namespace TauCeti

variable {ι R : Type*} {n : ℕ} [Finite ι] [TopologicalSpace R]

/-- The simultaneous good shear directions for a finite polynomial family form an open set.
Zero equations are ignored. -/
theorem isOpen_setOf_forall_eval_insertNth_homogeneousComponent_ne_zero
    [CommSemiring R] [IsTopologicalSemiring R] [T1Space R]
    (p : ι → MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    IsOpen {a : Fin n → R | ∀ k, p k ≠ 0 →
      eval (i.insertNth 1 a) (homogeneousComponent (p k).totalDegree (p k)) ≠ 0} := by
  classical
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro k
  by_cases hk : p k = 0
  · simp [hk]
  · simpa [hk, eval_dehomogenize] using
      (isOpen_ne (x := (0 : R))).preimage
        (dehomogenize i (homogeneousComponent (p k).totalDegree (p k))).continuous_eval

/-- There is a dense set of simultaneous good shear directions for a finite polynomial family.
In particular every nonempty open set of parameters contains a direction making all nonzero
sheared equations have constant nonzero leading coefficients. -/
theorem dense_setOf_forall_eval_insertNth_homogeneousComponent_ne_zero
    [CommRing R] [IsDomain R] [T1Space R] [PerfectSpace R]
    (p : ι → MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)) :
    Dense {a : Fin n → R | ∀ k, p k ≠ 0 →
      eval (i.insertNth 1 a) (homogeneousComponent (p k).totalDegree (p k)) ≠ 0} := by
  classical
  cases nonempty_fintype ι
  let H (k : ι) : MvPolynomial (Fin n) R :=
    if p k = 0 then 1 else dehomogenize i (homogeneousComponent (p k).totalDegree (p k))
  have hH (k : ι) : H k ≠ 0 := by
    by_cases hk : p k = 0
    · simp [H, hk]
    · simp only [H, hk, ite_false]
      intro hzero
      apply (p k).homogeneousComponent_totalDegree_ne_zero hk
      exact dehomogenize_injOn i (p k).totalDegree
        (homogeneousComponent_isHomogeneous _ _) (isHomogeneous_zero _ _ _)
        (by simpa using hzero)
  have hprod : (∏ k, H k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hH k
  convert (∏ k, H k).dense_setOf_eval_ne_zero hprod using 1
  ext a
  simp only [mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  apply forall_congr' fun k ↦ ?_
  by_cases hk : p k = 0 <;> simp [H, hk]

end TauCeti

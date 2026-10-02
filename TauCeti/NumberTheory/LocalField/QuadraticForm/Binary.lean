/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuadraticForm.Hasse
import TauCeti.Algebra.Ring.Int.Units

/-!
# Binary quadratic forms over a local field

Over a nonarchimedean local field of characteristic different from two, a binary regular
quadratic form is determined by its discriminant and local Hasse invariant. Its nonzero
represented values are determined by the same invariants: `⟨a, b⟩` represents a unit `c`
exactly when `(c, -ab) = (a, b)`. This describes both the hyperbolic case, which represents
every unit, and the anisotropic case, whose values form a coset of the quadratic norm group.

The representation criterion is stated for arbitrary regular binary spaces, so a caller need
not choose a diagonalization. These are the binary inputs to classification by splitting off
a represented line and cancelling.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §2.2, Theorem 6 and its corollary,
  and §2.3, Theorem 7, in dimension two.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §63:20–21.
-/

public section

open QuadraticMap

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]

/-- A binary diagonal form over a local field represents a unit `c` exactly when its Hilbert
symbol with the negative discriminant equals the local Hasse invariant of the form. -/
theorem mem_unitValueSet_binary_iff_hilbertSymbol_eq (a b c : Kˣ) :
    c ∈ unitValueSet (weightedSumSquares K ![(a : K), (b : K)]) ↔
      hilbertSymbol c (-(a * b)) = hilbertSymbol a b := by
  have hself : hilbertSymbol (-(a * b)) a = hilbertSymbol a b := by
    rw [hilbertSymbol_comm, hilbertSymbol_neg_self_mul (Invertible.ne_zero 2)]
  rw [mem_unitValueSet_binary_iff_mul_mem_quadraticNormSubgroup,
    ← Units.val_mul, ← Units.val_neg,
    ← hilbertSymbol_eq_one_iff_mem_quadraticNormSubgroup (-(a * b)),
    hilbertSymbol_mul_right (Invertible.ne_zero 2), hself, hilbertSymbol_comm (-(a * b)) c]
  rw [← Int.units_eq_iff_mul_eq_one, eq_comm]

/-- **Local binary classification.** Two binary diagonal forms over a nonarchimedean local field
are isometric exactly when their discriminants and local Hasse invariants agree. -/
theorem equivalent_binary_iff_isSquare_and_hilbertSymbol_eq (a b c d : Kˣ) :
    (weightedSumSquares K ![(a : K), (b : K)]).Equivalent
      (weightedSumSquares K ![(c : K), (d : K)]) ↔
      IsSquare (a * b * (c * d)) ∧ hilbertSymbol a b = hilbertSymbol c d := by
  refine ⟨fun h => ⟨isSquare_mul_mul_of_equivalent_binary h,
    hilbertSymbol_eq_of_equivalent_binary h⟩, ?_⟩
  rintro ⟨hd, hs⟩
  refine equivalent_binary_of_isSquare_of_mem_unitValueSet hd ?_
    (mem_unitValueSet_binary_left c d)
  rw [mem_unitValueSet_binary_iff_hilbertSymbol_eq]
  have hneg : IsSquare (-(a * b) * -(c * d)) := by simpa using hd
  rw [hilbertSymbol_congr_sq c c (-(a * b)) (-(c * d)) ⟨c, rfl⟩ hneg, hs]
  exact hilbertSymbol_neg_self_mul (Invertible.ne_zero 2) c d

end TauCeti

namespace QuadraticForm

open TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Invertible (2 : K)]
variable {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **The represented units of a regular binary space.** A unit `c` is represented exactly when
its Hilbert symbol with the negative discriminant equals the local Hasse invariant of the space.
The discriminant is the plain discriminant, written in the additive square-class group. -/
theorem mem_unitValueSet_iff_hilbertSymbol_eq_localHasse_of_finrank_eq_two
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 2) (c : Kˣ) :
    c ∈ Q.unitValueSet ↔
      hilbertSymbolOnSquareClasses (squareClass c)
        (squareClass (-1 : Kˣ) + RegularFormClass.discr (formClass Q hQ)) =
      RegularFormClass.localHasse (formClass Q hQ) := by
  obtain ⟨⟨n, w⟩, hw⟩ := exists_presentedForm_equivalent Q hQ
  have hn : n = 2 := by
    obtain ⟨e⟩ := hw
    simpa [hV] using e.toLinearEquiv.finrank_eq.symm
  subst n
  have hwvec : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [formClass_mk Q hQ ⟨2, w⟩ hw, hwvec, RegularFormClass.localHasse_mk_binary,
    RegularFormClass.discr_mk, Fin.prod_univ_two, ← squareClass_mul, neg_one_mul,
    hilbertSymbolOnSquareClasses_squareClass, hw.unitValueSet_eq]
  rw [presentedForm_two]
  exact mem_unitValueSet_binary_iff_hilbertSymbol_eq _ _ _

end QuadraticForm

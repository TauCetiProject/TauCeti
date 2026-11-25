/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Scalar and conjugation bounds for the continuous-functional-calculus square root

In a unital algebra with a continuous functional calculus for self-adjoint elements, the order
between a self-adjoint element `a` and a scalar `algebraMap ℝ A r` is read off the spectrum of `a`.
Since the real square root is monotone, the square root `CFC.sqrt a` then satisfies the same bound
with `√r` in place of `r`:

* `a ≤ r` gives `√a ≤ √r`,
* `r ≤ a` gives `√r ≤ √a`.

These are the two scalar cases of the operator monotonicity of the square root
(`CFC.monotone_sqrt`), which Mathlib proves only in C⋆-algebras. The scalar cases need no
C⋆-structure, so they apply, for instance, to real matrices with the Loewner order, which are not a
complex C⋆-algebra. They are the estimates that keep a map built from square roots of congruences
inside an order interval `[α, β]` of scalars.

In a non-unital algebra with a continuous functional calculus, the square root also commutes with
passing to the opposite algebra `Aᵐᵒᵖ`, which has the same order and the same squares, and
`CFC.sqrt x` commutes with every element commuting with `x` (`Commute.cfcSqrt`). In a unital
algebra the same holds for `√(1 - x)` and `√(1 - x²)`.

For a strictly positive element `c`, conjugation by the square root `CFC.conjSqrt c` is an order
isomorphism with inverse `CFC.conjSqrt c⁻¹ʳ` (`CFC.conjSqrt_le_conjSqrt_iff`). Consequently,
conjugation by `√c` or `√(c⁻¹)` moves across `≤` to its inverse on the opposite side, and scalar
bounds on `CFC.conjSqrt c⁻¹ʳ a` are equivalent to `a ≤ r • c` and `r • c ≤ a`.

## Main statements

* `CFC.sqrt_le_algebraMap`: if `a ≤ algebraMap ℝ A r`, then
  `CFC.sqrt a ≤ algebraMap ℝ A √r`.
* `CFC.algebraMap_le_sqrt`: if `algebraMap ℝ A r ≤ a`, then
  `algebraMap ℝ A √r ≤ CFC.sqrt a`.
* `CFC.unop_sqrt`, `CFC.op_sqrt`: the square root may be computed in `A` or in `Aᵐᵒᵖ`.
* `Commute.cfcSqrt`: `CFC.sqrt x` commutes with every element commuting with `x`.
* `CFC.conjSqrt_algebraMap`: `CFC.conjSqrt c (algebraMap ℝ A r) = r • c` for `0 ≤ c`.
* `CFC.conjSqrt_le_conjSqrt_iff`: for strictly positive `c`, `CFC.conjSqrt c` reflects order.
* `CFC.conjSqrt_le_iff`, `CFC.le_conjSqrt_iff`, `CFC.conjSqrt_ringInverse_le_iff`,
  `CFC.le_conjSqrt_ringInverse_iff`: moving `CFC.conjSqrt c` or `CFC.conjSqrt c⁻¹ʳ` across `≤`.
* `CFC.conjSqrt_ringInverse_le_algebraMap_iff`, `CFC.algebraMap_le_conjSqrt_ringInverse_iff`:
  scalar bounds on `CFC.conjSqrt c⁻¹ʳ a` are equivalent to `a ≤ r • c` and `r • c ≤ a`.
-/

public section

open MulOpposite

section Commute

/-- The square root `CFC.sqrt x` commutes with every element that commutes with `x`. -/
protected theorem Commute.cfcSqrt {A : Type*} [PartialOrder A] [NonUnitalRing A]
    [TopologicalSpace A] [StarRing A] [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A]
    [StarOrderedRing A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A] {x b : A} (h : Commute x b) :
    Commute (CFC.sqrt x) b :=
  h.cfcₙ_nnreal NNReal.sqrt

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsTopologicalRing A] [T2Space A]

/-- The square root `√(1 - x)` commutes with every element that commutes with `x`. -/
theorem Commute.cfcSqrt_one_sub {x b : A} (h : Commute x b) : Commute (CFC.sqrt (1 - x)) b :=
  ((Commute.one_left b).sub_left h).cfcSqrt

/-- The square root `√(1 - x²)` commutes with every element that commutes with `x`. -/
theorem Commute.cfcSqrt_one_sub_mul_self {x b : A} (h : Commute x b) :
    Commute (CFC.sqrt (1 - x * x)) b :=
  (h.mul_left h).cfcSqrt_one_sub

end Commute

namespace CFC

section MulOpposite

variable {A : Type*} [PartialOrder A] [NonUnitalRing A] [TopologicalSpace A] [StarRing A]
  [Module ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [StarOrderedRing A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonUnitalContinuousFunctionalCalculus ℝ Aᵐᵒᵖ IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [NonnegSpectrumClass ℝ Aᵐᵒᵖ] [IsSemitopologicalRing A] [T2Space A]

/-- The square root in the opposite algebra `Aᵐᵒᵖ` is the square root in `A`. -/
@[simp]
theorem unop_sqrt (a : Aᵐᵒᵖ) : unop (sqrt a) = sqrt (unop a) := by
  by_cases ha : 0 ≤ a
  · refine (sqrt_unique ?_ (unop_nonneg.mpr (sqrt_nonneg a))).symm
    rw [← unop_mul, sqrt_mul_sqrt_self a ha]
  · rw [sqrt_of_not_nonneg ha, sqrt_of_not_nonneg (unop_nonneg.not.mpr ha), unop_zero]

/-- The square root in `A` is the square root in the opposite algebra `Aᵐᵒᵖ`. -/
@[simp]
theorem op_sqrt (a : A) : op (sqrt a) = sqrt (op a) := by
  rw [← unop_inj, unop_sqrt, unop_op, unop_op]

end MulOpposite

section Scalar

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [StarModule ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [NonnegSpectrumClass ℝ A]
  [IsSemitopologicalRing A] [T2Space A]

/-- An element bounded above by the scalar `r` has square root bounded above by the scalar `√r`.
No nonnegativity hypothesis is needed: the square root of an element that is not nonnegative is
`0`. -/
theorem sqrt_le_algebraMap {a : A} {r : ℝ} (h : a ≤ algebraMap ℝ A r) :
    sqrt a ≤ algebraMap ℝ A √r := by
  by_cases ha : 0 ≤ a
  · rw [sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
    exact cfc_le_algebraMap _ _ a fun x hx ↦
      Real.sqrt_le_sqrt ((le_algebraMap_iff_spectrum_le (ha := ha.isSelfAdjoint)).1 h x hx)
  · rw [sqrt_eq_cfc, cfc_apply_of_not_predicate a ha]
    exact algebraMap_nonneg A (Real.sqrt_nonneg r)

/-- An element bounded below by the scalar `r` has square root bounded below by the scalar `√r`.
No nonnegativity hypothesis is needed: `√r = 0` for `r ≤ 0`. -/
theorem algebraMap_le_sqrt {a : A} {r : ℝ} (h : algebraMap ℝ A r ≤ a) :
    algebraMap ℝ A √r ≤ sqrt a := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Real.sqrt_eq_zero'.2 hr]
  have ha : 0 ≤ a := (algebraMap_nonneg A hr.le).trans h
  rw [sqrt_eq_real_sqrt a ha, cfcₙ_eq_cfc]
  exact algebraMap_le_cfc _ _ a fun x hx ↦
    Real.sqrt_le_sqrt ((algebraMap_le_iff_le_spectrum (ha := ha.isSelfAdjoint)).1 h x hx)

end Scalar

section ConjSqrt

open scoped Ring

variable {A : Type*} [PartialOrder A] [Ring A] [StarRing A] [TopologicalSpace A]
  [StarOrderedRing A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A] [IsSemitopologicalRing A] [T2Space A]

/-- For nonnegative `c`, conjugating a real scalar `algebraMap ℝ A r` by `√c` yields `r • c`. -/
theorem conjSqrt_algebraMap {c : A} {r : ℝ} (hc : 0 ≤ c := by cfc_tac) :
    conjSqrt c (algebraMap ℝ A r) = r • c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, conjSqrt_one c hc]

/-- For strictly positive `c`, conjugation by `√c` is order-reflecting as well as monotone:
`√c * a * √c ≤ √c * b * √c` holds iff `a ≤ b`. -/
theorem conjSqrt_le_conjSqrt_iff {c a b : A} (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c a ≤ conjSqrt c b ↔ a ≤ b :=
  ⟨fun h ↦ by
    simpa only [conjSqrt_ringInverse_conjSqrt c _ hc] using conjSqrt_le_conjSqrt (c := c⁻¹ʳ) h,
   conjSqrt_le_conjSqrt⟩

/-- For strictly positive `c`, moving conjugation by `√c` to the right turns it into
conjugation by `√(c⁻¹)`: `√c * a * √c ≤ b` iff `a ≤ √(c⁻¹) * b * √(c⁻¹)`. -/
theorem conjSqrt_le_iff {c a b : A} (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c a ≤ b ↔ a ≤ conjSqrt c⁻¹ʳ b := by
  rw [← conjSqrt_le_conjSqrt_iff hc.ringInverse, conjSqrt_ringInverse_conjSqrt c a hc]

/-- For strictly positive `c`, moving conjugation by `√(c⁻¹)` to the right turns it into
conjugation by `√c`: `√(c⁻¹) * a * √(c⁻¹) ≤ b` iff `a ≤ √c * b * √c`. -/
theorem conjSqrt_ringInverse_le_iff {c a b : A} (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ a ≤ b ↔ a ≤ conjSqrt c b := by
  rw [← conjSqrt_le_conjSqrt_iff hc, conjSqrt_conjSqrt_ringInverse c a hc]

/-- For strictly positive `c`, moving conjugation by `√c` to the left turns it into
conjugation by `√(c⁻¹)`: `a ≤ √c * b * √c` iff `√(c⁻¹) * a * √(c⁻¹) ≤ b`. -/
theorem le_conjSqrt_iff {c a b : A} (hc : IsStrictlyPositive c := by cfc_tac) :
    a ≤ conjSqrt c b ↔ conjSqrt c⁻¹ʳ a ≤ b :=
  (conjSqrt_ringInverse_le_iff hc).symm

/-- For strictly positive `c`, moving conjugation by `√(c⁻¹)` to the left turns it into
conjugation by `√c`: `a ≤ √(c⁻¹) * b * √(c⁻¹)` iff `√c * a * √c ≤ b`. -/
theorem le_conjSqrt_ringInverse_iff {c a b : A} (hc : IsStrictlyPositive c := by cfc_tac) :
    a ≤ conjSqrt c⁻¹ʳ b ↔ conjSqrt c a ≤ b :=
  (conjSqrt_le_iff hc).symm

/-- For strictly positive `c`, conjugating `a` by `√(c⁻¹)` is bounded above by the real scalar
`r` iff `a ≤ r • c`. -/
theorem conjSqrt_ringInverse_le_algebraMap_iff {c a : A} {r : ℝ}
    (hc : IsStrictlyPositive c := by cfc_tac) :
    conjSqrt c⁻¹ʳ a ≤ algebraMap ℝ A r ↔ a ≤ r • c := by
  rw [conjSqrt_ringInverse_le_iff hc, conjSqrt_algebraMap hc.nonneg]

/-- For strictly positive `c`, conjugating `a` by `√(c⁻¹)` is bounded below by the real scalar
`r` iff `r • c ≤ a`. -/
theorem algebraMap_le_conjSqrt_ringInverse_iff {c a : A} {r : ℝ}
    (hc : IsStrictlyPositive c := by cfc_tac) :
    algebraMap ℝ A r ≤ conjSqrt c⁻¹ʳ a ↔ r • c ≤ a := by
  rw [le_conjSqrt_ringInverse_iff hc, conjSqrt_algebraMap hc.nonneg]

end ConjSqrt

end CFC

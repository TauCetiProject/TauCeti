/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.OrthogonalGroup.Diagonal.Finite
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.DoubleCoset

/-!
# Finite adelic double cosets of orthogonal and Spin groups

Let `Q` be a quadratic form over `ℚ` and let `U` be compatible compact-open reference data.
The finite adelic class sets attached to `U` are

`G(ℚ) \ G(𝔸_f) / ∏_p U_p`

for `G = O`, `SO`, and `Spin`. The left subgroup is the range of the corresponding rational
diagonal, rather than an unrelated copy of `G(ℚ)`, and the right subgroup is the
everywhere-integral subgroup of the restricted product.

The comparisons for these types are deliberately the general double-coset constructions:

* `DoubleCoset.quotientMapOfLERight` is the surjection obtained by enlarging a compact-open
  subgroup;
* `DoubleCoset.quotientConjRight` is the canonical equivalence for conjugate compact-open
  subgroups, induced by right translation;
* `TauCeti.doubleCosetCongrRight` transports both subgroups along a componentwise equivalence of
  restricted products.

Keeping these maps separate matters. An eventual change of reference family canonically
identifies the ambient restricted products, but need not carry one everywhere-integral subgroup
to the other.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §101.
* A. Weil, *Adeles and Algebraic Groups* (1982), Chapter I.
-/

public section

namespace TauCeti
namespace QuadraticMap
namespace OrthogonalCompactOpens

open _root_.QuadraticMap

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  {Q : QuadraticForm ℚ V} (U : OrthogonalCompactOpens Q)

/-- The finite adelic orthogonal double-coset set
`O(V)(ℚ) \ O(V)(𝔸_f) / ∏_p U_p^O`. -/
abbrev finiteAdelicOrthogonalDoubleCoset : Type _ :=
  DoubleCoset.Quotient (U.finiteAdelicOrthogonalDiagonal.range : Set U.finiteAdelicOrthogonal)
    (integralSubgroup U.orthogonal : Set U.finiteAdelicOrthogonal)

/-- The finite adelic Spin double-coset set
`Spin(V)(ℚ) \ Spin(V)(𝔸_f) / ∏_p U_p^{Spin}`. -/
abbrev finiteAdelicSpinDoubleCoset : Type _ :=
  DoubleCoset.Quotient (U.finiteAdelicSpinDiagonal.range : Set U.finiteAdelicSpin)
    (integralSubgroup U.spin : Set U.finiteAdelicSpin)

variable [FiniteDimensional ℚ V]

/-- The finite adelic special-orthogonal double-coset set
`SO(V)(ℚ) \ SO(V)(𝔸_f) / ∏_p U_p^{SO}`. -/
abbrev finiteAdelicSpecialOrthogonalDoubleCoset : Type _ :=
  DoubleCoset.Quotient
    (U.finiteAdelicSpecialOrthogonalDiagonal.range : Set U.finiteAdelicSpecialOrthogonal)
    (integralSubgroup U.specialOrthogonal : Set U.finiteAdelicSpecialOrthogonal)

end

end OrthogonalCompactOpens
end QuadraticMap
end TauCeti

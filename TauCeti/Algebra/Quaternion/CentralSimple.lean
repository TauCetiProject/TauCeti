/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Algebra.Quaternion.SplittingCriterion
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Simple quaternion symbol algebras

For a field `K` with `2` invertible, this file proves simplicity for the general quaternion algebra
`ℍ[K,a,b,c]` when `c * QuadraticAlgebra.discr a b ≠ 0`. Completing the square reduces this case to
a symbol with both parameters units, for which the norm criterion gives either a division algebra or
a two-by-two matrix algebra. Centrality for the general symbol is in
`TauCeti.Algebra.Central.Quaternion`; the two-parameter symbol `ℍ[K,a,b]` is the specialization used
by the Brauer-valued invariants.

## Main results

* `TauCeti.QuaternionAlgebra.isSimpleRing_of_j_sq_mul_discr_ne_zero`: a quaternion algebra with
  nonzero `j`-square and nonzero discriminant is simple.
* `TauCeti.QuaternionAlgebra.instIsSimpleRing`: quaternion symbol algebras with both parameters
  units are simple.

The split/division dichotomy used here is the norm-equation criterion in
`TauCeti.Algebra.Quaternion.SplittingCriterion`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, §2.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), §1.1.
-/

public section

open scoped Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {K : Type*}

section Field

variable [Field K] [Invertible (2 : K)] (a b : Kˣ)

/-- A quaternion symbol with both parameters units is a simple ring. -/
instance instIsSimpleRing : IsSimpleRing ℍ[K,(a : K),(b : K)] := by
  rcases QuaternionAlgebra.forall_isUnit_or_nonempty_algEquiv_matrix a b with hdiv | hsplit
  · let divisionRing : DivisionRing ℍ[K,(a : K),(b : K)] :=
      DivisionRing.ofIsUnitOrEqZero (fun x ↦ by
        by_cases hx : x = 0
        · exact Or.inr hx
        · exact Or.inl (hdiv x hx))
    exact @DivisionRing.isSimpleRing _ divisionRing
  · obtain ⟨e⟩ := hsplit
    exact IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance

/-- A quaternion algebra with nonzero `j`-square and nonzero discriminant is simple. -/
theorem isSimpleRing_of_j_sq_mul_discr_ne_zero {a b c : K}
    (h : c * QuadraticAlgebra.discr a b ≠ 0) : IsSimpleRing ℍ[K,a,b,c] := by
  have ⟨hc, hd⟩ := mul_ne_zero_iff.mp h
  let u : Kˣ := Units.mk0 (QuadraticAlgebra.discr a b) hd
  let v : Kˣ := Units.mk0 c hc
  have htarget : IsSimpleRing ℍ[K,QuadraticAlgebra.discr a b,0,c] := instIsSimpleRing u v
  exact IsSimpleRing.of_ringEquiv (completeSquareEquiv a b c).symm.toRingEquiv htarget

end Field

end QuaternionAlgebra

end TauCeti

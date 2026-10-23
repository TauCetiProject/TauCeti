/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Six.SpecialLinear
public import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# The six-dimensional Spin group

Over a separably closed field of characteristic different from two, every nondegenerate
six-dimensional quadratic form is equivalent to three hyperbolic planes. Transporting the Spin
group along such an equivalence and using the split calculation identifies it noncanonically with
`SL₄`.

## Main result

* `TauCeti.nonempty_spinGroup_mulEquiv_specialLinearGroup_of_finrank_eq_six` identifies the Spin
  group of a regular six-dimensional quadratic space with `SL₄`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter II, §3.
-/

public section

open CliffordAlgebra Module

namespace TauCeti

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- A nondegenerate six-dimensional quadratic space over a separably closed field of
characteristic different from two has Spin group noncanonically isomorphic to `SL₄`. -/
theorem nonempty_spinGroup_mulEquiv_specialLinearGroup_of_finrank_eq_six
    [NeZero (2 : K)] [IsSepClosed K] (hQ : Q.Nondegenerate) (hV : finrank K V = 6) :
    Nonempty (spinGroup Q ≃* Matrix.SpecialLinearGroup (Fin 4) K) := by
  let _ : FiniteDimensional K V := Module.finite_of_finrank_pos (by omega)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨e⟩ := QuadraticForm.equivalent_of_finrank_eq_of_isSepClosed Q
    (splitEvenForm K 3) hQ (nondegenerate_splitEvenForm K 3) (by simpa using hV)
  exact ⟨e.spinGroupEquiv.trans (hyperbolicSixSpinEquivSpecialLinear K)⟩

end TauCeti

end

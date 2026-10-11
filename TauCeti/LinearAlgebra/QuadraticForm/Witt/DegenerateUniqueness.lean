/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The radical summand of a degenerate quadratic form

If a quadratic form is isometric to a zero form orthogonally summed with a regular form, the
dimension of that zero summand is determined by the original form. This lets a decomposition by
the radical be compared independently of the chosen regular complement.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, §4.
-/

public section

open QuadraticMap QuadraticForm

namespace QuadraticForm

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- If a quadratic form is isometric to a zero form orthogonally summed with a regular form, the
dimension of its radical is the dimension of the zero summand. -/
theorem finrank_radical_eq_of_equivalent_zero_prod
    {V R W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup R] [Module K R] [FiniteDimensional K R]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Q : QuadraticForm K V) (A : QuadraticForm K W) (hA : A.Nondegenerate)
    (e : Q.Equivalent ((0 : QuadraticForm K R).prod A)) :
    Module.finrank K Q.radical = Module.finrank K R := by
  have hzeroR : (0 : QuadraticForm K R).radical = ⊤ := by
    ext x
    simp [QuadraticMap.mem_radical_iff']
  have hradA : ((0 : QuadraticForm K R).prod A).radical =
      (⊤ : Submodule K R).prod (⊥ : Submodule K W) := by
    rw [radical_prod, hzeroR, hA.radical_eq_bot]
  have hdimA : Module.finrank K R = Module.finrank K ((0 : QuadraticForm K R).prod A).radical := by
    rw [hradA]
    calc
      Module.finrank K R = Module.finrank K
          ((⊤ : Submodule K R) × (⊥ : Submodule K W)) := by
        rw [Module.finrank_prod, finrank_top, finrank_bot, add_zero]
      _ = Module.finrank K ((⊤ : Submodule K R).prod (⊥ : Submodule K W)) :=
        (Submodule.prodEquiv _ _).finrank_eq.symm
  exact (Equivalent.rank_radical_eq e).trans hdimA.symm

/-- The dimensions of the zero summands agree whenever one quadratic form is isometric to two
orthogonal sums of a zero form and a regular form. -/
theorem finrank_zeroPart_eq_of_equivalent_zero_prod
    {V R S W W' : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup R] [Module K R] [FiniteDimensional K R]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup W'] [Module K W'] [FiniteDimensional K W']
    (Q : QuadraticForm K V) (A : QuadraticForm K W) (B : QuadraticForm K W')
    (hA : A.Nondegenerate) (hB : B.Nondegenerate)
    (e : Q.Equivalent ((0 : QuadraticForm K R).prod A))
    (e' : Q.Equivalent ((0 : QuadraticForm K S).prod B)) :
    Module.finrank K R = Module.finrank K S := by
  rw [← finrank_radical_eq_of_equivalent_zero_prod Q A hA e,
    ← finrank_radical_eq_of_equivalent_zero_prod Q B hB e']

end QuadraticForm

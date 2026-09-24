/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Representation
public import TauCeti.NumberTheory.QuadraticForm.Global.Operations

/-!
# Common local values of the summands of a non-anisotropic orthogonal sum

Let `U` and `W` be quadratic forms over a number field. If `U ⊥ W` is not anisotropic at a finite
or real place, with `U` regular and `W` anisotropic on a nonzero space at that place, this file
produces local vectors `x` of `U` and `y` of `W` with

`U(x) = -W(y) ≠ 0`.

These are the local values that a global vector of `U` has to approximate in the proof of the
Hasse–Minkowski theorem in rank at least five, where `U` is a binary summand and `W` is its
(regular) orthogonal complement: at the places where the regular form `W` stays isotropic every
nonzero scalar is already represented by `W`, so only the places where `W` is anisotropic impose
a condition. The results of this file do not assume `W` regular.

## Main results

* `QuadraticForm.exists_atFinitePlace_ne_zero_eq_neg`
* `QuadraticForm.exists_atRealPlace_ne_zero_eq_neg`

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, 66:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [Nontrivial W]

/-- If `U ⊥ R` is not anisotropic at a finite place where `R` is anisotropic, with `U` regular
and `R` on a nonzero space, then some nonzero local value of `U` is the negative of a local value
of `R`. -/
theorem exists_atFinitePlace_ne_zero_eq_neg
    {U : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W} [NumberField K]
    {v : HeightOneSpectrum (𝓞 K)} (h : ¬(atFinitePlace (U.prod R) v).Anisotropic)
    (hU : U.Nondegenerate) (hR : (R.atFinitePlace v).Anisotropic) :
    ∃ x y, U.atFinitePlace v x ≠ 0 ∧ U.atFinitePlace v x = -R.atFinitePlace v y := by
  refine hR.exists_ne_zero_eq_neg_of_not_anisotropic_prod
    (Nondegenerate.atFinitePlace hU v).radical_eq_bot ?_
  rw [← QuadraticMap.Equivalent.anisotropic_iff ⟨atFinitePlaceProd U R v⟩]
  exact h

/-- If `U ⊥ R` is not anisotropic at a real place where `R` is anisotropic, with `U` regular
and `R` on a nonzero space, then some nonzero local value of `U` is the negative of a local value
of `R`. -/
theorem exists_atRealPlace_ne_zero_eq_neg
    {U : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    {w : {w : InfinitePlace K // w.IsReal}}
    (h : ¬(atRealPlace (U.prod R) w).Anisotropic) (hU : U.Nondegenerate)
    (hR : (R.atRealPlace w).Anisotropic) :
    ∃ x y, U.atRealPlace w x ≠ 0 ∧ U.atRealPlace w x = -R.atRealPlace w y := by
  let : Algebra K ℝ := (embedding_of_isReal w.2).toAlgebra
  refine hR.exists_ne_zero_eq_neg_of_not_anisotropic_prod
    (Nondegenerate.atRealPlace hU w).radical_eq_bot ?_
  rw [← QuadraticMap.Equivalent.anisotropic_iff ⟨atRealPlaceProd U R w⟩]
  exact h

end QuadraticForm

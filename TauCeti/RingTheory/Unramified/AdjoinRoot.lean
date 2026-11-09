/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# The derivative of an unramified monogenic algebra

If `R[X]/(f)` is formally unramified over `R`, the image of `f'` is a unit.
Equivalently, `f` is separable in the ring-theoretic sense of being coprime to its derivative.
No monicity or finiteness assumption is needed for this implication.

For monic polynomials this supplies the necessary half of the monogenic étaleness criterion;
compare the definition of standard étale maps in the Stacks Project, Tag 00UB. It detects the
obstruction to étaleness of root extractions in residue characteristics dividing the exponent.
The square-zero test algebra used here is the trivial extension of `R[X]/(f, f')` by itself.
-/

public section

open AdjoinRoot

namespace Polynomial

variable {R : Type*} [CommRing R] (f : R[X])

/-- In a formally unramified monogenic algebra, the derivative of its defining equation is
invertible. -/
theorem isUnit_mk_derivative_of_formallyUnramified_adjoinRoot
    [Algebra.FormallyUnramified R (AdjoinRoot f)] : IsUnit (mk f f.derivative) := by
  -- Test uniqueness on Q[ε]/(ε²), where both the equation and its derivative vanish in Q.
  let I : Ideal (AdjoinRoot f) := Ideal.span {mk f f.derivative}
  let Q := AdjoinRoot f ⧸ I
  let q : AdjoinRoot f →ₐ[R] Q := Ideal.Quotient.mkₐ R I
  let g : AdjoinRoot f →ₐ[R] TrivSqZeroExt Q Q :=
    (TrivSqZeroExt.inlAlgHom R Q Q).comp q
  have hd : q (mk f f.derivative) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hg : aeval (g (root f)) f = 0 := aeval_algHom_eq_zero f g
  have hgd : aeval (g (root f)) f.derivative = 0 := by
    rw [aeval_algHom_apply, aeval_eq, AlgHom.comp_apply, hd, map_zero]
  have hroot : aeval (g (root f) + TrivSqZeroExt.inr (1 : Q)) f = 0 := by
    rw [aeval_add_of_sq_eq_zero]
    · simp [hg, hgd]
    · simp [pow_two]
  let h : AdjoinRoot f →ₐ[R] TrivSqZeroExt Q Q :=
    liftAlgHom f (Algebra.ofId R _) _ hroot
  have heq : g = h := by
    -- The two roots have the same projection to Q, whose kernel is square-zero.
    apply Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom R Q Q).toRingHom
      (⟨2, TrivSqZeroExt.kerIdeal_sq Q Q⟩ : IsNilpotent (TrivSqZeroExt.kerIdeal Q Q))
    have hc : (TrivSqZeroExt.fstHom R Q Q).comp g =
        (TrivSqZeroExt.fstHom R Q Q).comp h := by
      apply AdjoinRoot.algHom_ext
      simp [g, h]
    exact AlgHom.congr_fun hc
  have h10 : (1 : Q) = 0 := by
    have := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun heq (root f))
    simpa [g, h] using this.symm
  exact Ideal.span_singleton_eq_top.mp
    ((Ideal.eq_top_iff_one _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp h10))

end Polynomial

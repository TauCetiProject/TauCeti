/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# Quaternary quadratic forms

This file develops basic results about four-dimensional quadratic forms over fields in which two
is invertible.

## Main results

* `QuadraticMap.Nondegenerate.equivalent_hyperbolicPlane_prod_self`: a regular isotropic
  quaternary form with square discriminant is the orthogonal sum of two hyperbolic planes.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer, 1963, §42:12.
-/

public section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over a field in which two is invertible, a regular isotropic quaternary form with square
discriminant is isometric to the orthogonal sum of two hyperbolic planes. -/
theorem _root_.QuadraticMap.Nondegenerate.equivalent_hyperbolicPlane_prod_self
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (hrank : Module.finrank K V = 4)
    (hdiscr : RegularFormClass.discr (formClass Q hQ) = 0) (hiso : ¬ Q.Anisotropic) :
    Q.Equivalent ((hyperbolicPlane K).prod (hyperbolicPlane K)) := by
  obtain ⟨p, hp⟩ := exists_hyperbolicPlane_prod_equivalent Q hQ hiso
  have hpRank : p.1 = 2 := by
    obtain ⟨e⟩ := hp
    have hfin := e.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at hfin
    rw [hrank] at hfin
    omega
  obtain ⟨_, w⟩ := p
  subst hpRank
  have hprodNondegenerate :
      ((hyperbolicPlane K).prod (presentedForm ⟨2, w⟩)).Nondegenerate :=
    nondegenerate_hyperbolicPlane.prod (nondegenerate_presentedForm ⟨2, w⟩)
  have hclass : formClass Q hQ =
      hyperbolicClass K + formClass (presentedForm ⟨2, w⟩)
        (nondegenerate_presentedForm ⟨2, w⟩) := by
    rw [← formClass_hyperbolicPlane, ← formClass_prod]
    exact (formClass_eq_iff Q hQ _ hprodNondegenerate).mpr hp
  have hwDiscr : RegularFormClass.discr
      (formClass (presentedForm ⟨2, w⟩) (nondegenerate_presentedForm ⟨2, w⟩)) =
        squareClass (-1 : Kˣ) := by
    have hd := congrArg RegularFormClass.discr hclass
    rw [hdiscr, RegularFormClass.discr_add,
      RegularFormClass.discr_hyperbolicClass] at hd
    exact (add_eq_zero_iff_neg_eq.mp hd.symm).symm.trans (ZModModule.neg_eq_self _)
  rw [formClass_presentedForm, RegularFormClass.discr_mk, Fin.prod_univ_two] at hwDiscr
  have hwHyperbolic :=
    equivalent_presentedForm_hyperbolicPlane_of_squareClass_prod_eq_neg_one w hwDiscr
  exact hp.trans (QuadraticMap.Equivalent.prod (QuadraticMap.Equivalent.refl _) hwHyperbolic)

end TauCeti

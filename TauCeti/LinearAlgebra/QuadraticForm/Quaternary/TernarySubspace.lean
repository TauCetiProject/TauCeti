/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# Ternary subspaces of quaternary quadratic spaces

This file proves that, over a field in which two is invertible, a subspace of dimension at least
three in a regular four-dimensional isotropic quadratic space with square discriminant is
isotropic. The ambient hypotheses first force the space to be the orthogonal sum of two
hyperbolic planes. Such a space has a two-dimensional totally isotropic subspace, which must meet
every subspace of dimension at least three nontrivially.

The resulting equivalence between isotropy of the restricted and ambient forms is the
field-theoretic step used in the square-discriminant case of the quaternary Hasse principle.

## Main results

* `QuadraticMap.Nondegenerate.equivalent_hyperbolicPlane_prod_self`: a regular isotropic
  quaternary form over a field in which two is invertible and with square discriminant is the sum
  of two hyperbolic planes.
* `QuadraticMap.Nondegenerate.not_anisotropic_restrict_of_finrank_ge_three`: isotropy of such an
  ambient form implies isotropy of any restriction of dimension at least three.
* `QuadraticMap.Nondegenerate.not_anisotropic_restrict_iff_of_finrank_ge_three`: isotropy of a
  restriction of dimension at least three is equivalent to isotropy of its regular quaternary
  ambient form when the latter has square discriminant.

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

/-- Parametrises a totally isotropic plane in `H ⊥ H` by diagonal vectors in each factor. -/
private def hyperbolicPlaneProdIsotropicMap :
    K × K →ₗ[K] (Fin 2 → K) × (Fin 2 → K) where
  toFun x := (![x.1, x.1], ![x.2, x.2])
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

omit [Invertible (2 : K)] in
/-- The parametrisation of the diagonal plane in `H ⊥ H` is injective. -/
private theorem hyperbolicPlaneProdIsotropicMap_injective :
    Function.Injective (hyperbolicPlaneProdIsotropicMap (K := K)) := by
  intro x y hxy
  apply Prod.ext
  · have := congrArg (fun z ↦ z.1 0) hxy
    simpa [hyperbolicPlaneProdIsotropicMap] using this
  · have := congrArg (fun z ↦ z.2 0) hxy
    simpa [hyperbolicPlaneProdIsotropicMap] using this

/-- Every vector in the parametrised diagonal plane in `H ⊥ H` is isotropic. -/
private theorem hyperbolicPlane_prod_self_isotropicMap (x : K × K) :
    ((hyperbolicPlane K).prod (hyperbolicPlane K))
      (hyperbolicPlaneProdIsotropicMap x) = 0 := by
  rcases x with ⟨x, y⟩
  simp [hyperbolicPlaneProdIsotropicMap, QuadraticMap.prod_apply]

/-- Over a field in which two is invertible, a subspace of dimension at least three in a regular
quaternary isotropic space with square discriminant is isotropic. No regularity hypothesis on the
subspace is needed. -/
theorem _root_.QuadraticMap.Nondegenerate.not_anisotropic_restrict_of_finrank_ge_three
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (U : Submodule K V)
    (hUrank : 3 ≤ Module.finrank K U) (hrank : Module.finrank K V = 4)
    (hdiscr : RegularFormClass.discr (formClass Q hQ) = 0) (hiso : ¬ Q.Anisotropic) :
    ¬ (Q.restrict U).Anisotropic := by
  let e := (hQ.equivalent_hyperbolicPlane_prod_self hrank hdiscr hiso).some
  let f : K × K →ₗ[K] V :=
    e.symm.toLinearEquiv.toLinearMap.comp hyperbolicPlaneProdIsotropicMap
  let P : Submodule K V := LinearMap.range f
  have hf : Function.Injective f :=
    e.symm.injective.comp hyperbolicPlaneProdIsotropicMap_injective
  have hPrank : Module.finrank K P = 2 := by
    dsimp only [P]
    rw [LinearMap.finrank_range_of_inj hf, Module.finrank_prod]
    simp
  have hPzero (x : P) : Q x = 0 := by
    obtain ⟨y, hy⟩ := x.2
    rw [← hy]
    exact (e.symm.map_app (hyperbolicPlaneProdIsotropicMap y)).trans
      (hyperbolicPlane_prod_self_isotropicMap y)
  have hinterRank : 0 < Module.finrank K (U ⊓ P : Submodule K V) := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq U P
    have hsup : Module.finrank K (U ⊔ P : Submodule K V) ≤ 4 := by
      rw [← hrank]
      exact Submodule.finrank_le _
    rw [hPrank] at hdim
    omega
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hinterRank
  rw [QuadraticMap.not_anisotropic_iff_exists]
  refine ⟨⟨x, x.2.1⟩, ?_, ?_⟩
  · intro hzero
    apply hx
    apply Subtype.ext
    exact (Submodule.coe_eq_zero (p := U)).mpr hzero
  · simpa only [QuadraticMap.restrict_apply] using hPzero ⟨x, x.2.2⟩

/-- **O'Meara 42:12.** Over a field in which two is invertible, for a subspace of dimension at
least three in a regular quaternary quadratic space with square discriminant, the restricted form
is isotropic exactly when the ambient form is.

The restriction need not be assumed regular. -/
theorem _root_.QuadraticMap.Nondegenerate.not_anisotropic_restrict_iff_of_finrank_ge_three
    {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) (U : Submodule K V)
    (hUrank : 3 ≤ Module.finrank K U) (hrank : Module.finrank K V = 4)
    (hdiscr : RegularFormClass.discr (formClass Q hQ) = 0) :
    ¬ (Q.restrict U).Anisotropic ↔ ¬ Q.Anisotropic := by
  constructor
  · exact (Q.restrict_isRepresentedBy U).not_anisotropic
  · exact hQ.not_anisotropic_restrict_of_finrank_ge_three U hUrank hrank hdiscr

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

/-!
# Witt decomposition for degenerate forms

A possibly degenerate quadratic form splits as the zero form on its radical and a regular form.
This identifies the part discarded on passing to the regular quotient, before applying the usual
Witt decomposition to the nondegenerate summand.

The construction uses the standard complement argument for finite-dimensional vector spaces; see
Lam, *Introduction to Quadratic Forms over Fields*, Chapter I, §4.

All three summands of a decomposition `Q ≅ 0 ⊥ m ℍ ⊥ A` are determined by `Q`: the zero summand
lives on a copy of the radical
(`QuadraticMap.nonempty_linearEquiv_radical_of_equivalent_zero_prod`), and `m` and the class of `A`
are the Witt index and the anisotropic part of the class of the regular part
`Q.lift Q.radical le_rfl`.

## Main results

* `QuadraticForm.exists_equivalent_zero_radical_wittDecomposition`: **Witt decomposition** of a
  possibly degenerate form, `Q ≅ 0 ⊥ m ℍ ⊥ A` with the zero form on the radical.
* `TauCeti.wittIndex_formClass_lift_radical_eq`,
  `TauCeti.anisotropicPart_formClass_lift_radical_eq`: uniqueness of the hyperbolic and anisotropic
  summands of a decomposition of a possibly degenerate form.
-/

public section

namespace QuadraticForm

open TauCeti

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A possibly degenerate finite-dimensional quadratic form is a zero form on its radical,
orthogonally summed with the usual Witt decomposition of a nondegenerate complement. The integer
`m` is the Witt index of that complement and `p` is its anisotropic diagonal part. -/
theorem exists_equivalent_zero_radical_wittDecomposition (Q : QuadraticForm K V) :
    ∃ (C : Submodule K V) (m : ℕ) (p : RegularFormPresentation K),
      IsCompl Q.radical C ∧ (presentedForm p).Anisotropic ∧
        Module.finrank K V = Module.finrank K Q.radical + 2 * m + p.1 ∧
        Q.Equivalent ((0 : QuadraticForm K Q.radical).prod
          ((presentedForm (hyperbolicPresentation K m)).prod (presentedForm p))) := by
  obtain ⟨C, hC, hCreg, hzero⟩ := exists_equivalent_zero_radical_prod Q
  obtain ⟨p, hp, hdim, hrest⟩ :=
    QuadraticForm.exists_equivalent_hyperbolicPresentation_prod (Q.restrict C) hCreg
  obtain ⟨e₁⟩ := hzero
  obtain ⟨e₂⟩ := hrest
  refine ⟨C, RegularFormClass.wittIndex (formClass (Q.restrict C) hCreg), p,
    hC, hp, ?_, ?_⟩
  · have hdimC := Submodule.finrank_sup_add_finrank_inf_eq Q.radical C
    rw [hC.sup_eq_top, hC.disjoint.eq_bot, finrank_top, finrank_bot,
      add_zero] at hdimC
    omega
  · have e₀ : (0 : QuadraticForm K Q.radical).IsometryEquiv 0 :=
      QuadraticMap.IsometryEquiv.refl _
    exact ⟨e₁.trans (e₀.prod e₂)⟩

end QuadraticForm

namespace TauCeti

section Uniqueness

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {T : Type*} [AddCommGroup T] [Module K T] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

-- The class of the regular part, read off a decomposition `Q ≅ 0 ⊥ m ℍ ⊥ A`.
private theorem formClass_lift_radical_eq_nsmul_hyperbolicClass_add {Q : QuadraticForm K V}
    {m : ℕ} {A : QuadraticForm K W} (hA : A.Anisotropic)
    (h : Q.Equivalent ((0 : QuadraticForm K T).prod
      ((presentedForm (hyperbolicPresentation K m)).prod A))) :
    formClass _ Q.nondegenerate_lift_radical =
      m • hyperbolicClass K + formClass A hA.nondegenerate := by
  rw [formClass_lift_radical_eq ((nondegenerate_presentedForm _).prod hA.nondegenerate) h,
    formClass_prod _ (nondegenerate_presentedForm _) _ hA.nondegenerate, formClass_presentedForm,
    mk_hyperbolicPresentation]

/-- **Uniqueness of the Witt index** in a Witt decomposition of a possibly degenerate form: in any
decomposition `Q ≅ 0 ⊥ m ℍ ⊥ A` with `A` anisotropic, `m` is the Witt index of the regular part
of `Q`. -/
theorem wittIndex_formClass_lift_radical_eq {Q : QuadraticForm K V}
    {m : ℕ} {A : QuadraticForm K W} (hA : A.Anisotropic)
    (h : Q.Equivalent ((0 : QuadraticForm K T).prod
      ((presentedForm (hyperbolicPresentation K m)).prod A))) :
    RegularFormClass.wittIndex (formClass _ Q.nondegenerate_lift_radical) = m :=
  RegularFormClass.wittIndex_eq ((A.anisotropic_formClass hA.nondegenerate).mpr hA)
    (formClass_lift_radical_eq_nsmul_hyperbolicClass_add hA h)

/-- **Uniqueness of the anisotropic part** in a Witt decomposition of a possibly degenerate form:
in any decomposition `Q ≅ 0 ⊥ m ℍ ⊥ A` with `A` anisotropic, the class of `A` is the anisotropic
part of the regular part of `Q`. -/
theorem anisotropicPart_formClass_lift_radical_eq {Q : QuadraticForm K V}
    {m : ℕ} {A : QuadraticForm K W} (hA : A.Anisotropic)
    (h : Q.Equivalent ((0 : QuadraticForm K T).prod
      ((presentedForm (hyperbolicPresentation K m)).prod A))) :
    RegularFormClass.anisotropicPart (formClass _ Q.nondegenerate_lift_radical) =
      formClass A hA.nondegenerate :=
  RegularFormClass.anisotropicPart_eq ((A.anisotropic_formClass hA.nondegenerate).mpr hA)
    (formClass_lift_radical_eq_nsmul_hyperbolicClass_add hA h)

end Uniqueness

end TauCeti

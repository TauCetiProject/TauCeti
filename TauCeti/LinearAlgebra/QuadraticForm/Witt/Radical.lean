/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Radical
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

/-!
# Witt decomposition of possibly singular forms

Every finite-dimensional quadratic form over a field in which `2` is invertible is isometric
to the zero form on its radical, an orthogonal sum of hyperbolic planes, and an anisotropic form.
The radical dimension, number of planes, and anisotropic isometry class are complete isometry
invariants. In particular, the regular part is taken on the canonical quotient by the radical;
no chosen complement enters these invariants.

This extends the regular Witt decomposition using `TauCeti.regularQuotientClass`, built from
Mathlib's quotient form `QuadraticMap.lift`. The references are T. Y. Lam, *Introduction to
Quadratic Forms over Fields* (2005), I §4, especially Theorem I.4.1, and Elman–Karpenko–Merkurjev,
*The Algebraic and Geometric Theory of Quadratic Forms* (2008), II §7, for the radical.
-/

public section

namespace TauCeti

universe u v w

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- **Witt decomposition**, including the radical: every form is isometric to the zero form
on its radical, its regular quotient's Witt index worth of hyperbolic planes, and an anisotropic
diagonal form. The dimensions of these three summands add up to the original dimension. -/
theorem _root_.QuadraticForm.exists_equivalent_zero_prod_hyperbolicPresentation_prod
    (Q : QuadraticForm K V) :
    ∃ p : RegularFormPresentation K, (presentedForm p).Anisotropic ∧
      Module.finrank K V = Module.finrank K Q.radical +
        2 * RegularFormClass.wittIndex (regularQuotientClass Q) + p.1 ∧
      Q.Equivalent ((0 : QuadraticForm K Q.radical).prod
        ((presentedForm (hyperbolicPresentation K
          (RegularFormClass.wittIndex (regularQuotientClass Q)))).prod (presentedForm p))) := by
  obtain ⟨p, ha, hdim, he⟩ := QuadraticForm.exists_equivalent_hyperbolicPresentation_prod
    (Q.lift Q.radical le_rfl) Q.nondegenerate_lift_radical
  rw [← regularQuotientClass_def] at hdim he
  refine ⟨p, ha, ?_, ?_⟩
  · have h := Q.radical.finrank_quotient_add_finrank
    omega
  · exact Q.equivalent_zero_prod_lift_radical.trans ((QuadraticMap.Equivalent.refl _).prod he)

/-- **Uniqueness of the three parts of Witt decomposition**: the radical dimension, the
regular quotient's Witt index, and its anisotropic class together classify all forms, including
singular ones. Equality of the first invariant means isometry of the zero radical forms. -/
theorem equivalent_iff_finrank_radical_eq_wittIndex_eq_anisotropicPart_eq
    (Q : QuadraticForm K V) (Q' : QuadraticForm K W) :
    Q.Equivalent Q' ↔
      Module.finrank K Q.radical = Module.finrank K Q'.radical ∧
      RegularFormClass.wittIndex (regularQuotientClass Q) =
        RegularFormClass.wittIndex (regularQuotientClass Q') ∧
      RegularFormClass.anisotropicPart (regularQuotientClass Q) =
        RegularFormClass.anisotropicPart (regularQuotientClass Q') := by
  rw [equivalent_iff_finrank_radical_eq_and_regularQuotientClass_eq]
  refine ⟨fun ⟨hdim, h⟩ => ⟨hdim, congrArg RegularFormClass.wittIndex h,
    congrArg RegularFormClass.anisotropicPart h⟩, ?_⟩
  rintro ⟨hdim, hm, ha⟩
  refine ⟨hdim, ?_⟩
  calc
    regularQuotientClass Q =
        RegularFormClass.wittIndex (regularQuotientClass Q) • hyperbolicClass K +
          RegularFormClass.anisotropicPart (regularQuotientClass Q) :=
      RegularFormClass.wittDecomposition _
    _ = RegularFormClass.wittIndex (regularQuotientClass Q') • hyperbolicClass K +
          RegularFormClass.anisotropicPart (regularQuotientClass Q') := by rw [hm, ha]
    _ = regularQuotientClass Q' := (RegularFormClass.wittDecomposition _).symm

/-- The zero form in any finite dimension has no hyperbolic planes in its regular quotient. -/
example : RegularFormClass.wittIndex (regularQuotientClass (0 : QuadraticForm K V)) = 0 := by
  simp

/-- A singular form with a one-dimensional zero summand and a hyperbolic plane retains that
plane: discarding the radical does not discard the regular isotropic summand. -/
example : RegularFormClass.wittIndex
    (regularQuotientClass ((0 : QuadraticForm ℚ ℚ).prod (hyperbolicPlane ℚ))) = 1 := by
  rw [regularQuotientClass_zero_prod _ nondegenerate_hyperbolicPlane,
    formClass_hyperbolicPlane, RegularFormClass.wittIndex_hyperbolicClass]

end TauCeti

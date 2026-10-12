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

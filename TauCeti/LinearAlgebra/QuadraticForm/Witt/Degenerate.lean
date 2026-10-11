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

/-- Every finite-dimensional quadratic form is an orthogonal sum of the zero form on its radical
and a nondegenerate restriction to a complementary subspace. -/
theorem exists_equivalent_zero_radical_prod (Q : QuadraticForm K V) :
    ∃ C : Submodule K V, IsCompl Q.radical C ∧ (Q.restrict C).Nondegenerate ∧
      Q.Equivalent ((0 : QuadraticForm K Q.radical).prod (Q.restrict C)) := by
  obtain ⟨C, hC⟩ := Q.radical.exists_isCompl
  have hCreg : (Q.restrict C).Nondegenerate := by
    apply QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr
    rw [QuadraticMap.radical_eq_ker_polarBilin]
    apply le_antisymm
    · intro x hx
      have hxrad : (x : V) ∈ Q.radical := by
        rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
        ext y
        have hymem : y ∈ Q.radical ⊔ C := by
          rw [hC.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨r, hr, c, hc, rfl⟩ := Submodule.mem_sup.mp hymem
        have hxr : Q.polarBilin (x : V) r = 0 := by
          rw [Q.isSymm_polarBilin.eq]
          have hrker : r ∈ Q.polarBilin.ker := Q.radical_le_ker_polarBilin hr
          have hr0 : Q.polarBilin r = 0 := by simpa only [LinearMap.mem_ker] using hrker
          rw [hr0]
          rfl
        have hxc : Q.polarBilin (x : V) c = 0 := by
          have hx0 : (Q.restrict C).polarBilin x = 0 := by
            simpa only [LinearMap.mem_ker] using hx
          have hx' := congrArg (fun f : C →ₗ[K] K => f ⟨c, hc⟩) hx0
          simpa only [QuadraticMap.polarBilin_restrict,
            LinearMap.domRestrict₁₂_apply, LinearMap.zero_apply] using hx'
        simp [map_add, hxr, hxc]
      have hx' : (x : V) ∈ Q.radical ⊓ C := ⟨hxrad, x.2⟩
      simpa [hC.disjoint.eq_bot] using hx'
    · exact bot_le
  have horth : LinearMap.BilinForm.orthogonal Q.polarBilin C = Q.radical := by
    apply le_antisymm
    · intro x hx
      rw [QuadraticMap.radical_eq_ker_polarBilin, LinearMap.mem_ker]
      ext y
      have hymem : y ∈ Q.radical ⊔ C := by
        rw [hC.sup_eq_top]
        exact Submodule.mem_top
      obtain ⟨r, hr, c, hc, rfl⟩ := Submodule.mem_sup.mp hymem
      have hxr : Q.polarBilin x r = 0 := by
        rw [Q.isSymm_polarBilin.eq]
        have hrker : r ∈ Q.polarBilin.ker := Q.radical_le_ker_polarBilin hr
        have hr0 : Q.polarBilin r = 0 := by simpa only [LinearMap.mem_ker] using hrker
        rw [hr0]
        rfl
      have hxc := hx c hc
      rw [Q.isSymm_polarBilin.eq] at hxc
      simp [map_add, hxr, hxc]
    · intro x hx y hy
      rw [Q.isSymm_polarBilin.eq]
      have hxker : x ∈ Q.polarBilin.ker := Q.radical_le_ker_polarBilin hx
      have hx0 : Q.polarBilin x = 0 := by simpa only [LinearMap.mem_ker] using hxker
      rw [hx0]
      rfl
  have heq : ((Q.restrict C).prod
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin C))).IsometryEquiv Q :=
    QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q C hCreg.isCompl_orthogonal
  have hradZero : Q.restrict Q.radical = (0 : QuadraticForm K Q.radical) := by
    ext x
    exact (QuadraticMap.mem_radical_iff'.mp x.2).1
  refine ⟨C, hC, hCreg, ?_⟩
  rw [horth] at heq
  rw [hradZero] at heq
  have heqRad : ((Q.restrict C).prod (0 : QuadraticForm K Q.radical)).IsometryEquiv Q := heq
  exact ⟨heqRad.symm.trans (QuadraticMap.IsometryEquiv.prodComm _ _)⟩

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

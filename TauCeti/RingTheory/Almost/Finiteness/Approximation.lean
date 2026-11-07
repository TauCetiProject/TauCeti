/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Finiteness.Basic

import Mathlib.RingTheory.Ideal.Colon

/-!
# Finite approximations of almost finitely presented modules

Almost finite presentation can be tested by maps from finitely presented modules whose kernels
and cokernels are annihilated by any prescribed finitely generated subideal of the setup ideal.
The approximating module is the quotient of a finite free module by the finitely many relations
in an almost presentation.

When the setup ideal is a filtered union of principal ideals, it suffices to test individual
elements `ε` of the ideal. This gives the epsilon criteria for almost finite generation, almost
finite presentation, and a fixed bound on the number of generators. In the first two criteria,
both the kernel and cokernel of the approximation map are killed by `ε`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, §2.3, Proposition 2.3.10.
* P. Scholze, *Perfectoid spaces*, §4, Definition/Proposition 4.7(iii).
-/

public section

open LinearMap Submodule
open scoped Pointwise

namespace TauCeti.Almost.BasicSetup

universe u

variable {V : Type u} [CommRing V] {S : BasicSetup V}
  {N : Type*} [AddCommGroup N] [Module V N]

/-- Almost finite presentation is equivalent to approximation by finitely presented modules,
with kernel and cokernel annihilated by each finitely generated subideal of the setup ideal. -/
theorem almostFP_iff_forall_exists_finitePresentation : S.AlmostFP N ↔
    ∀ K : Ideal V, K ≤ S.ideal → K.FG →
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
        Module.FinitePresentation V P ∧ ∃ f : P →ₗ[V] N,
          K ≤ Module.annihilator V (ker f) ∧
          K ≤ Module.annihilator V (N ⧸ range f) := by
  rw [almostFP_iff]
  constructor
  · intro h K hK hKfg
    obtain ⟨r, n, ψ, φ, hφψ, hφ, hψ⟩ := h K hK hKfg
    let Q := range ψ
    let f : ((Fin n → V) ⧸ Q) →ₗ[V] N := Q.liftQ φ (range_le_ker_iff.mpr hφψ)
    have hQfg : Q.FG := (fg_iff_exists_fin_linearMap _ _).mpr ⟨r, ψ, rfl⟩
    have hP : Module.FinitePresentation V ((Fin n → V) ⧸ Q) :=
      Module.finitePresentation_of_surjective Q.mkQ Q.mkQ_surjective
        (by simpa using hQfg)
    refine ⟨_, inferInstance, inferInstance, hP, f, ?_, ?_⟩
    · intro ε hε
      apply Module.mem_annihilator.mpr
      rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Q.mkQ_surjective x
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero Q).mpr
      exact hψ (smul_mem_smul hε (by simpa [f] using hx))
    · rw [annihilator_quotient, Submodule.range_liftQ]
      exact fun ε hε ↦ mem_colon.mpr fun x _ ↦ hφ (smul_mem_smul hε mem_top)
  · intro h K hK hKfg
    obtain ⟨P, _, _, hP, f, hker, hcoker⟩ := h K hK hKfg
    have := hP
    obtain ⟨n, r, φ, ψ, hφ, hψφ⟩ := Module.FinitePresentation.exists_fin' V P
    refine ⟨r, n, ψ, f ∘ₗ φ, ?_, ?_, ?_⟩
    · rw [comp_assoc, hψφ.linearMap_comp_eq_zero, comp_zero]
    · rw [range_comp_of_range_eq_top _ (range_eq_top.mpr hφ)]
      refine smul_le.mpr fun ε hε x _ ↦ ?_
      rw [annihilator_quotient] at hcoker
      exact mem_colon.mp (hcoker hε) x (Set.mem_univ x)
    · refine smul_le.mpr fun ε hε x hx ↦ ?_
      rw [← hψφ.linearMap_ker_eq, mem_ker, map_smul]
      exact congrArg Subtype.val (Module.mem_annihilator.mp (hker hε)
        ⟨φ x, by simpa using hx⟩)

/-- Under condition (A), a fixed bound on the number of generators can be tested one element of
the setup ideal at a time. -/
theorem uniformlyAlmostFG_iff_epsilon (hS : S.IsFilteredPrincipal) (n : ℕ) :
    S.UniformlyAlmostFG N n ↔ ∀ ε ∈ S.ideal,
      ∃ φ : (Fin n → V) →ₗ[V] N, ∀ x, ε • x ∈ range φ := by
  rw [uniformlyAlmostFG_iff]
  constructor
  · intro h ε hε
    obtain ⟨φ, hφ⟩ := h (Ideal.span {ε}) (by simpa [Ideal.span_le])
      (Submodule.fg_span_singleton ε)
    exact ⟨φ, fun x ↦ hφ (smul_mem_smul (Ideal.mem_span_singleton_self ε) mem_top)⟩
  · intro h K hK hKfg
    obtain ⟨ε, hε, hKε⟩ := hS.exists_le_span_singleton hKfg hK
    obtain ⟨φ, hφ⟩ := h ε hε
    refine ⟨φ, (smul_mono_left hKε).trans (smul_le.mpr ?_)⟩
    intro a ha x _
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simpa [mul_smul] using (range φ).smul_mem b (hφ x)

/-- Under condition (A), almost finite generation is equivalent to approximation by finitely
generated modules with kernel and cokernel killed by each `ε` in the setup ideal. -/
theorem almostFG_iff_epsilon (hS : S.IsFilteredPrincipal) : S.AlmostFG N ↔
    ∀ ε ∈ S.ideal, ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
      Module.Finite V P ∧ ∃ f : P →ₗ[V] N,
        ε ∈ Module.annihilator V (ker f) ∧
        ε ∈ Module.annihilator V (N ⧸ range f) := by
  rw [almostFG_iff]
  constructor
  · intro h ε hε
    obtain ⟨n, φ, hφ⟩ := h (Ideal.span {ε}) (by simpa [Ideal.span_le])
      (Submodule.fg_span_singleton ε)
    let Q := ker φ
    let f : ((Fin n → V) ⧸ Q) →ₗ[V] N := Q.liftQ φ le_rfl
    have hf : ker f = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    refine ⟨_, inferInstance, inferInstance, inferInstance, f, ?_, ?_⟩
    · rw [hf]
      exact Module.mem_annihilator.mpr fun x ↦ Subsingleton.elim _ _
    · rw [annihilator_quotient, Submodule.range_liftQ]
      exact mem_colon.mpr fun x _ ↦
        hφ (smul_mem_smul (Ideal.mem_span_singleton_self ε) mem_top)
  · intro h K hK hKfg
    obtain ⟨ε, hε, hKε⟩ := hS.exists_le_span_singleton hKfg hK
    obtain ⟨P, _, _, hP, f, _, hcoker⟩ := h ε hε
    have := hP
    obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' V P
    refine ⟨n, f ∘ₗ φ, ?_⟩
    rw [range_comp_of_range_eq_top _ (range_eq_top.mpr hφ)]
    refine (smul_mono_left hKε).trans (smul_le.mpr fun a ha x _ ↦ ?_)
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [annihilator_quotient] at hcoker
    simpa [mul_smul] using (range f).smul_mem b (mem_colon.mp hcoker x (Set.mem_univ x))

/-- Under condition (A), almost finite presentation is equivalent to approximation by finitely
presented modules with kernel and cokernel killed by each `ε` in the setup ideal. -/
theorem almostFP_iff_epsilon (hS : S.IsFilteredPrincipal) : S.AlmostFP N ↔
    ∀ ε ∈ S.ideal, ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
      Module.FinitePresentation V P ∧ ∃ f : P →ₗ[V] N,
        ε ∈ Module.annihilator V (ker f) ∧
        ε ∈ Module.annihilator V (N ⧸ range f) := by
  rw [almostFP_iff_forall_exists_finitePresentation]
  constructor
  · intro h ε hε
    obtain ⟨P, hP₁, hP₂, hP, f, hker, hcoker⟩ :=
      h (Ideal.span {ε}) (by simpa [Ideal.span_le]) (Submodule.fg_span_singleton ε)
    exact ⟨P, hP₁, hP₂, hP, f, hker (Ideal.mem_span_singleton_self ε),
      hcoker (Ideal.mem_span_singleton_self ε)⟩
  · intro h K hK hKfg
    obtain ⟨ε, hε, hKε⟩ := hS.exists_le_span_singleton hKfg hK
    obtain ⟨P, hP₁, hP₂, hP, f, hker, hcoker⟩ := h ε hε
    exact ⟨P, hP₁, hP₂, hP, f, hKε.trans (by simpa [Ideal.span_le] using hker),
      hKε.trans (by simpa [Ideal.span_le] using hcoker)⟩

end TauCeti.Almost.BasicSetup

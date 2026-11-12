/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Finiteness.Basic

import TauCeti.RingTheory.Ideal.Colon

/-!
# Finite approximations of almost finitely generated and presented modules

Almost finite generation can be tested by maps from finite modules whose cokernels are
annihilated by any prescribed finitely generated subideal of the setup ideal. The map can be
chosen injective. Almost finite presentation can be tested by maps from finitely presented
modules whose kernels and cokernels are annihilated by any prescribed finitely generated
subideal of the setup ideal.
The approximating module is the quotient of a finite free module by the finitely many relations
in an almost presentation.

When the setup ideal is a filtered union of principal ideals, it suffices to test individual
elements `ε` of the ideal. This gives the epsilon criteria for almost finite generation, almost
finite presentation, and a fixed bound on the number of generators. The finite-generation
criterion requires only cokernel annihilation; the finite-presentation criterion requires both
kernel and cokernel annihilation.

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

/-- Almost finite generation gives an injective approximation by a finite module with cokernel
annihilated by any prescribed finitely generated subideal of the setup ideal. -/
theorem AlmostFG.exists_finite_injective (h : S.AlmostFG N) (K : Ideal V)
    (hK : K ≤ S.ideal) (hKfg : K.FG) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
      Module.Finite V P ∧ ∃ f : P →ₗ[V] N,
        Function.Injective f ∧ K ≤ Module.annihilator V (N ⧸ range f) := by
  obtain ⟨n, φ, hφ⟩ := almostFG_iff.mp h K hK hKfg
  let Q := ker φ
  let f : ((Fin n → V) ⧸ Q) →ₗ[V] N := Q.liftQ φ le_rfl
  refine ⟨_, inferInstance, inferInstance, inferInstance, f,
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl), ?_⟩
  rw [le_annihilator_quotient_iff, Submodule.range_liftQ]
  exact hφ

/-- Almost finite generation is equivalent to approximation by finite modules with cokernel
annihilated by each finitely generated subideal of the setup ideal. -/
theorem almostFG_iff_forall_exists_finite : S.AlmostFG N ↔
    ∀ K : Ideal V, K ≤ S.ideal → K.FG →
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
        Module.Finite V P ∧ ∃ f : P →ₗ[V] N,
          K ≤ Module.annihilator V (N ⧸ range f) := by
  constructor
  · intro h K hK hKfg
    obtain ⟨P, hP₁, hP₂, hP, f, _, hcoker⟩ := h.exists_finite_injective K hK hKfg
    exact ⟨P, hP₁, hP₂, hP, f, hcoker⟩
  · rw [almostFG_iff]
    intro h K hK hKfg
    obtain ⟨P, _, _, hP, f, hcoker⟩ := h K hK hKfg
    obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' V P
    refine ⟨n, f ∘ₗ φ, ?_⟩
    rw [range_comp_of_range_eq_top _ (range_eq_top.mpr hφ)]
    exact le_annihilator_quotient_iff.mp hcoker

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
    · rwa [le_annihilator_quotient_iff, Submodule.range_liftQ]
  · intro h K hK hKfg
    obtain ⟨P, _, _, hP, f, hker, hcoker⟩ := h K hK hKfg
    obtain ⟨n, r, φ, ψ, hφ, hψφ⟩ := Module.FinitePresentation.exists_fin' V P
    refine ⟨r, n, ψ, f ∘ₗ φ, ?_, ?_, ?_⟩
    · rw [comp_assoc, hψφ.linearMap_comp_eq_zero, comp_zero]
    · rw [range_comp_of_range_eq_top _ (range_eq_top.mpr hφ)]
      exact le_annihilator_quotient_iff.mp hcoker
    · refine smul_le.mpr fun ε hε x hx ↦ ?_
      rw [← hψφ.linearMap_ker_eq, mem_ker, map_smul]
      exact congrArg Subtype.val (Module.mem_annihilator.mp (hker hε)
        ⟨φ x, by simpa using hx⟩)

/-- Under condition (A), a fixed bound on the number of generators can be tested one element of
the setup ideal at a time. -/
theorem uniformlyAlmostFG_iff_forall_mem_exists_smul_mem_range
    (hS : S.IsFilteredPrincipal) (n : ℕ) :
    S.UniformlyAlmostFG N n ↔ ∀ ε ∈ S.ideal,
      ∃ φ : (Fin n → V) →ₗ[V] N, ∀ x, ε • x ∈ range φ := by
  rw [uniformlyAlmostFG_iff, hS.forall_fg_iff_forall_span_singleton
    (fun _ _ hIJ ⟨φ, hφ⟩ ↦ ⟨φ, (smul_mono_left hIJ).trans hφ⟩)]
  simp only [ideal_span_singleton_smul]
  exact forall₂_congr fun ε _ ↦ exists_congr fun φ ↦
    ⟨fun h x ↦ h ⟨x, mem_top, rfl⟩,
      fun h x ⟨y, _, hy⟩ ↦ hy ▸ h y⟩

/-- Under condition (A), almost finite generation is equivalent to approximation by finite
modules with cokernel killed by each `ε` in the setup ideal. -/
theorem almostFG_iff_forall_mem_exists_finite (hS : S.IsFilteredPrincipal) : S.AlmostFG N ↔
    ∀ ε ∈ S.ideal, ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
      Module.Finite V P ∧ ∃ f : P →ₗ[V] N,
        ε ∈ Module.annihilator V (N ⧸ range f) := by
  rw [almostFG_iff_forall_exists_finite, hS.forall_fg_iff_forall_span_singleton
    (fun _ _ hIJ ⟨P, hP₁, hP₂, hP, f, hcoker⟩ ↦
      ⟨P, hP₁, hP₂, hP, f, hIJ.trans hcoker⟩)]
  simp only [Ideal.span_singleton_le_iff_mem]

/-- Under condition (A), almost finite presentation is equivalent to approximation by finitely
presented modules with kernel and cokernel killed by each `ε` in the setup ideal. -/
theorem almostFP_iff_forall_mem_exists_finitePresentation (hS : S.IsFilteredPrincipal) :
    S.AlmostFP N ↔ ∀ ε ∈ S.ideal,
      ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module V P),
        Module.FinitePresentation V P ∧ ∃ f : P →ₗ[V] N,
          ε ∈ Module.annihilator V (ker f) ∧
          ε ∈ Module.annihilator V (N ⧸ range f) := by
  rw [almostFP_iff_forall_exists_finitePresentation,
    hS.forall_fg_iff_forall_span_singleton
      (fun _ _ hIJ ⟨P, hP₁, hP₂, hP, f, hker, hcoker⟩ ↦
        ⟨P, hP₁, hP₂, hP, f, hIJ.trans hker, hIJ.trans hcoker⟩)]
  simp only [Ideal.span_singleton_le_iff_mem]

end TauCeti.Almost.BasicSetup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import TauCeti.LinearAlgebra.Span.ScalarTower
import TauCeti.Algebra.Module.LocalizedModule.Submodule
import TauCeti.RingTheory.Ideal.Quotient.Index

/-!
# Extending a lattice to an overorder

Let `Λ` and `Γ` be orders in an algebra, and choose a denominator `r` with `r Γ ⊆ Λ`.
For a `Λ`-submodule `M` of a representation, its `Γ`-span `N` satisfies `r N ⊆ M ⊆ N`.
When the base ring has finite quotients, only finitely many `M` can therefore give the
same finitely generated `N`. They represent every `Λ`-lattice whose enlarged span is isomorphic
to `N`, even in a different representation. This is the reduction to an overorder in the
Jordan–Zassenhaus theorem (I. Reiner, *Maximal Orders*, §26).
-/

public section

open Submodule Pointwise

namespace Submodule

/-- If `r Γ ⊆ Λ` and `R / (r)` is finite, only finitely many `Λ`-submodules have a prescribed
`Γ`-span finitely generated over `R`. -/
theorem finite_setOf_span_eq_of_smul_mem {R A V : Type*} [CommRing R] [Semiring A] [Algebra R A]
    [AddCommMonoid V] [Module A V] [Module R V] [IsScalarTower R A V]
    {Λ Γ : Subalgebra R A} (N : Submodule Γ V) (hN : (N.restrictScalars R).FG)
    {r : R} (h : ∀ a ∈ Γ, r • a ∈ Λ) [Finite (R ⧸ Ideal.span {r})] :
    {M : Submodule Λ V | span Γ (M : Set V) = N}.Finite := by
  have hfin := (N.restrictScalars R).finite_Icc_smul hN (Ideal.span {r})
  rw [ideal_span_singleton_smul] at hfin
  refine (hfin.preimage (restrictScalars_injective R Λ V).injOn).subset ?_
  intro M (hM : span Γ (M : Set V) = N)
  refine ⟨hM ▸ M.smul_restrictScalars_span_le h, ?_⟩
  exact fun x hx => hM ▸ subset_span hx

/-- **Finite fibers up to isomorphism in the reduction to an overorder.** Suppose `R` has finite
quotients by nonzero ideals. Let `Λ ≤ Γ` be subalgebras with `Γ` finite over `R` and contained in
the fraction-field span of `Λ`. For each finitely generated `Γ`-module `N` inside a representation,
there is a finite family of `Λ`-submodules spanning `N` which represents every `Λ`-submodule with
`Γ`-span isomorphic to `N`. The representatives work in every ambient representation. -/
theorem exists_finset_representatives_of_span {R K A V : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] [Semiring A] [Algebra R A] [Algebra K A]
    [IsScalarTower R K A] [Ring.HasFiniteQuotients R]
    [AddCommMonoid V] [Module A V]
    {Λ Γ : Subalgebra R A} (N : Submodule Γ V) (hN : N.FG) (hle : Λ ≤ Γ)
    (hspan : (Γ : Set A) ⊆ span K (Λ : Set A)) [Module.Finite R Γ] :
    ∃ s : Finset (Submodule Λ V), (∀ P, P ∈ s ↔ span Γ (P : Set V) = N) ∧
      ∀ {W : Type*} [AddCommMonoid W] [Module A W] (M : Submodule Λ W),
        (span Γ (M : Set W) ≃ₗ[Γ] N) → ∃ P ∈ s, Nonempty (M ≃ₗ[Λ] P) := by
  classical
  have hΓ : (Subalgebra.toSubmodule Γ).FG := Module.Finite.iff_fg.1 ‹_›
  obtain ⟨r, hr, h⟩ := hΓ.exists_smul_mem_of_le_span (M := Subalgebra.toSubmodule Λ)
    (nonZeroDivisors R) hspan
  have := IsDomain.of_faithfulSMul R K
  have : Finite (R ⧸ Ideal.span {r}) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr (nonZeroDivisors.ne_zero hr))
  let := Module.compHom V (algebraMap R A)
  let := IsScalarTower.of_compHom R A V
  have hs := N.finite_setOf_span_eq_of_smul_mem (hN.restrictScalars (R := R)) h
  refine ⟨hs.toFinset, fun _ => hs.mem_toFinset, ?_⟩
  intro W _ _ M e
  -- The inclusion of subalgebras lets the span isomorphism restrict to Λ-scalars.
  let : SMul Λ Γ := ⟨fun a b => Subalgebra.inclusion hle a * b⟩
  let : IsScalarTower Λ Γ W := ⟨fun a b x => mul_smul (a : A) (b : A) x⟩
  let : IsScalarTower Λ Γ V := ⟨fun a b x => mul_smul (a : A) (b : A) x⟩
  obtain ⟨P, hP, eP⟩ := M.exists_span_eq_and_nonempty_linearEquiv e
  exact ⟨P, hs.mem_toFinset.2 hP, eP⟩

end Submodule

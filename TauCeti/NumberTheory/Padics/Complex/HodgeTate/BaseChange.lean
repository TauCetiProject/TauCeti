/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.NumberTheory.Padics.Complex.FixedPoints

/-!
# Pullback and base change for Hodge–Tate maps and jumps

This file establishes functoriality of PadicComplex.hodgeTateMaps under equivariant semilinear
maps and proves that PadicComplex.hodgeTateJump is invariant under extension of scalars.

Given a φ-semilinear map i : T' →ₛₗ[φ] T equivariant near 1 and compatible ring maps
γ' = γ ∘ φ, precomposition sends Hodge–Tate maps of weight u on T to Hodge–Tate maps of
weight u on T'. Moreover, when γ takes algebraic values, checking the Hodge–Tate condition on
a spanning set of T suffices for the whole module. Combining these shows that a φ-semilinear
map sending an R-basis of T to an R'-basis of T' induces a PadicAlgCl p-linear
isomorphism on Hodge–Tate maps and preserves all Hodge–Tate jumps.

## Main definitions

* PadicComplex.hodgeTateMapsComp: pullback of Hodge–Tate maps along a semilinear map equivariant
  near 1.

## Main results

* PadicComplex.mem_hodgeTateMaps_of_span: the Hodge–Tate condition on a spanning set extends to
  the whole module when γ takes algebraic values.
* PadicComplex.hodgeTateJump_baseChange: invariance of Hodge–Tate jumps under extension of
  scalars along a basis-preserving semilinear map.

## Provenance

Adapted from New.Period.mem_hodgeTateMaps_of_span
(src/Lib/PadicHodge/Crystalline/HodgeTateForms.lean) and New.Period.hodgeTateMaps.pull,
New.Period.jump_baseChange (src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean) of grh-lean
(https://github.com/lsernau/grh-lean, commit 72fead102f663d5c7a407964a13dc0cf9d977207,
Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R R' T T' : Type*} [Monoid Γ]

/-- Pullback of Hodge–Tate maps of weight u along a φ-semilinear map i : T' →ₛₗ[φ] T that is
equivariant for g near 1. -/
noncomputable def hodgeTateMapsComp [CommSemiring R] [CommSemiring R'] [AddCommMonoid T]
    [AddCommMonoid T'] [Module R T] [Module R' T']
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {ρ : Representation R Γ T}
    {σ : Representation R' Γ T'} {γ : R →+* ℂ_[p]} {γ' : R' →+* ℂ_[p]} {φ : R' →+* R}
    [RingHomCompTriple φ γ γ'] {u : ℤ} (i : T' →ₛₗ[φ] T)
    (hi : ∀ᶠ g in comap j (𝓝 1), ∀ x, i (σ g x) = ρ g (i x)) :
    hodgeTateMaps j ρ γ u →ₗ[PadicAlgCl p] hodgeTateMaps j σ γ' u where
  toFun f := ⟨f.val.comp i, by
    rw [mem_hodgeTateMaps]
    intro x
    filter_upwards [hi, (mem_hodgeTateMaps.mp f.property) (i x)] with g heq hw
    simpa [heq] using hw⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- If γ : R →+* ℂ_p takes algebraic values and s spans T over R, then a γ-semilinear map
satisfying the Hodge–Tate condition of weight u on every element of s lies in
hodgeTateMaps j ρ γ u. -/
theorem mem_hodgeTateMaps_of_span [CommSemiring R] [AddCommMonoid T] [Module R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {ρ : Representation R Γ T} {γ : R →+* ℂ_[p]}
    (hγ : ∀ r : R, γ r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p])) {s : Set T}
    (hs : Submodule.span R s = ⊤) {u : ℤ} {f : T →ₛₗ[γ] ℂ_[p]}
    (hf : ∀ x ∈ s, ∀ᶠ g in comap j (𝓝 1),
      f (ρ g x) = twist (-u) (j g).toRingEquiv * j g • f x) :
    f ∈ hodgeTateMaps j ρ γ u := by
  rw [mem_hodgeTateMaps]
  intro x
  have hx : x ∈ Submodule.span R s := hs.symm ▸ Submodule.mem_top
  refine Submodule.span_induction hf (by simp) (fun y z _ _ hy hz ↦ ?_) (fun r y _ hy ↦ ?_) hx
  · filter_upwards [hy, hz] with g hgy hgz
    simp [map_add, hgy, hgz, mul_add]
  · filter_upwards [hy, (mem_range_coe_iff_eventually_smul_eq.mp (hγ r)).comap j] with g hgy hgr
    simp only [map_smul, map_smulₛₗ, smul_eq_mul, smul_mul', hgy, hgr]
    ring

/-- Invariance of Hodge–Tate jumps under extension of scalars: if  : T →ₛₗ[φ] T' maps an
R-basis  of T to an R'-basis ' of T' and is equivariant near 1, and γ' : R' →+* ℂ_p
takes algebraic values, then hodgeTateJump j σ γ' u = hodgeTateJump j ρ γ u where γ = γ' ∘ φ. -/
theorem hodgeTateJump_baseChange [CommRing R] [CommRing R'] [AddCommGroup T] [AddCommGroup T']
    [Module R T] [Module R' T'] {ι : Type*}
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {ρ : Representation R Γ T}
    {σ : Representation R' Γ T'} {φ : R →+* R'} {γ' : R' →+* ℂ_[p]} {γ : R →+* ℂ_[p]}
    [RingHomCompTriple φ γ' γ] (hγ' : ∀ r : R', γ' r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p]))
    (f : T →ₛₗ[φ] T') (b : Basis ι R T) (b' : Basis ι R' T') (hb : ∀ i, f (b i) = b' i)
    (hf : ∀ᶠ g in comap j (𝓝 1), ∀ x, f (ρ g x) = σ g (f x)) (u : ℤ) :
    hodgeTateJump j σ γ' u = hodgeTateJump j ρ γ u := by
  have heval_bij' : Function.Bijective (fun F : T' →ₛₗ[γ'] ℂ_[p] ↦ fun i ↦ F (b' i)) := by
    refine ⟨fun F G hFG ↦ b'.ext (congrFun hFG), fun v ↦ ?_⟩
    let : Algebra R' ℂ_[p] := γ'.toAlgebra
    exact ⟨⟨(b'.constr ℕ v).toAddHom, (b'.constr ℕ v).map_smul'⟩, funext (b'.constr_basis ℕ v)⟩
  have hcomp_bij : Function.Bijective (fun F : T' →ₛₗ[γ'] ℂ_[p] ↦ (F.comp f : T →ₛₗ[γ] ℂ_[p])) := by
    refine Function.Bijective.of_comp_left ?_ (fun F G hFG ↦ b.ext (congrFun hFG))
    have heq : (fun F : T →ₛₗ[γ] ℂ_[p] ↦ fun i ↦ F (b i)) ∘
        (fun F : T' →ₛₗ[γ'] ℂ_[p] ↦ (F.comp f : T →ₛₗ[γ] ℂ_[p])) =
        (fun F : T' →ₛₗ[γ'] ℂ_[p] ↦ fun i ↦ F (b' i)) :=
      funext fun F ↦ funext fun i ↦ congrArg F (hb i)
    rw [heq]
    exact heval_bij'
  have hiff (F : T' →ₛₗ[γ'] ℂ_[p]) :
      F ∈ hodgeTateMaps j σ γ' u ↔ F.comp f ∈ hodgeTateMaps j ρ γ u := by
    refine ⟨fun hF ↦ (hodgeTateMapsComp f hf ⟨F, hF⟩).property, fun hF ↦ ?_⟩
    refine mem_hodgeTateMaps_of_span hγ' b'.span_eq ?_
    rintro _ ⟨i, rfl⟩
    filter_upwards [hf, (mem_hodgeTateMaps.mp hF) (b i)] with g heq hg
    simpa [heq, hb] using hg
  let eForms : hodgeTateMaps j σ γ' u ≃ₗ[PadicAlgCl p] hodgeTateMaps j ρ γ u :=
    { hodgeTateMapsComp f hf, (Equiv.ofBijective _ hcomp_bij).subtypeEquiv hiff with }
  rw [hodgeTateJump_def, hodgeTateJump_def]
  exact LinearEquiv.finrank_eq eForms

end PadicComplex

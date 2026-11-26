/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Module.Submodule.Superfluous
import TauCeti.RingTheory.Ideal.Annihilator

/-!
# Reflexive modules over a self-injective local ring are finitely generated

A module `M` over a commutative ring `R` is reflexive (`Module.IsReflexive`) when evaluation
`M → M**` into its double `R`-dual is bijective. Over a field the reflexive modules are exactly the
finite-dimensional ones (`Module.instFiniteDimensionalOfIsReflexive`). This file proves the same
finiteness over a self-injective local ring whose maximal ideal is nilpotent, for instance over
`O ⧸ 𝔪 ^ k` for a discrete valuation ring `O` and `k ≥ 1`, or over `ℤ ⧸ ℓ ^ k`: there every
reflexive module is finitely generated. These are the coefficient rings of torsion étale
cohomology, where reflexivity of the cohomology modules is what makes the biduality map of a
complex an isomorphism.

The argument reduces to linear algebra over the residue field. Let `I` be a maximal ideal of a
self-injective ring `R` and `s ≠ 0` an element killed by `I`, so that `r ↦ r * s` embeds `R ⧸ I`
into `R`. Through this embedding every `R ⧸ I`-linear functional on `V = M ⧸ I • M` becomes an
`R`-linear functional on `M`, and self-injectivity extends functionals along the resulting
embedding of duals. Hence every `R ⧸ I`-linear functional on the dual of `V` comes from a
functional on `M**`, that is from an element of `M` when `M` is reflexive. So `V` is reflexive over
the field `R ⧸ I` and therefore finite-dimensional. When the maximal ideal is nilpotent, the last
nonzero power of it supplies `s`, and Nakayama's lemma for a nilpotent ideal lifts finiteness from
`M ⧸ 𝔪 • M` to `M`.

## Main results

* `Module.finite_quotient_smul_top_of_isReflexive`: over a self-injective ring, if a maximal ideal
  `I` kills a nonzero element, the top `M ⧸ I • M` of a reflexive module is finite-dimensional
  over `R ⧸ I`.
* `Module.Finite.of_isReflexive_of_isNilpotent`: over a self-injective local ring with nilpotent
  maximal ideal, every reflexive module is finitely generated.

## References

* D. Hansen, T. Kaletha, J. Weinstein, *On the Kottwitz conjecture for local shtuka spaces*,
  Forum Math. Pi 10 (2022), Lemma B.1.1, where the statement is proved over `O ⧸ 𝔪 ^ k` by
  induction on `k`.
-/

public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Over a self-injective commutative ring `R`, let `I` be a maximal ideal killing a nonzero
element `s` of `R`. Then the top `M ⧸ I • M` of every reflexive `R`-module `M` is
finite-dimensional over the residue field `R ⧸ I`. -/
theorem finite_quotient_smul_top_of_isReflexive [Module.Injective R R] (I : Ideal R)
    [I.IsMaximal] {s : R} (hs : s ≠ 0) (hIs : ∀ x ∈ I, x * s = 0) [IsReflexive R M] :
    Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) := by
  let := Ideal.Quotient.field I
  let V := M ⧸ I • (⊤ : Submodule R M)
  let π := (I • (⊤ : Submodule R M)).mkQ
  -- Multiplication by `s` embeds the residue field `R ⧸ I` into `R`.
  let σ : (R ⧸ I) →ₗ[R] R :=
    Submodule.liftQ I (LinearMap.toSpanSingleton R R s) fun x hx ↦ by
      simpa using hIs x hx
  have hσ : Function.Injective σ := by
    refine LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ fun x hx ↦ ?_)
    by_contra hxI
    obtain ⟨y, i, hi, hyx⟩ := Ideal.IsMaximal.exists_inv ‹_› hxI
    have hxs : x * s = 0 := by simpa using hx
    exact hs (by linear_combination (-s) * hyx + y * hxs + hIs i hi)
  -- Composing with `σ` and `π` turns residue-field functionals on `V` into functionals on `M`.
  let j : Dual (R ⧸ I) V →ₗ[R] Dual R M :=
    { toFun := fun φ ↦ σ ∘ₗ φ.restrictScalars R ∘ₗ π
      map_add' := fun φ ψ ↦ by ext; simp
      map_smul' := fun r φ ↦ by ext; simp }
  have hj_apply (φ : Dual (R ⧸ I) V) (m : M) : j φ m = σ (φ (π m)) := rfl
  have hj : Function.Injective j := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun φ hφ ↦ LinearMap.ext fun v ↦ ?_)
    obtain ⟨m, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective v
    have hm : σ (φ (π m)) = 0 := by simpa [hj_apply] using LinearMap.congr_fun hφ m
    exact hσ (by simpa [π] using hm)
  -- Self-injectivity extends functionals along `j`, and reflexivity of `M` realises the
  -- extension as evaluation at an element of `M`.
  have hsurj : Function.Surjective (Dual.eval (R ⧸ I) V) := by
    intro Ψ
    obtain ⟨h, hh⟩ :=
      Module.Injective.extension_property R R _ _ j hj (σ ∘ₗ Ψ.restrictScalars R)
    obtain ⟨m, rfl⟩ := (bijective_dual_eval R M).2 h
    refine ⟨π m, LinearMap.ext fun φ ↦ hσ ?_⟩
    simpa [hj_apply] using LinearMap.congr_fun hh φ
  have : IsReflexive (R ⧸ I) V := ⟨⟨eval_apply_injective _, hsurj⟩⟩
  infer_instance

/-- **Reflexive modules over a self-injective local ring with nilpotent maximal ideal are finitely
generated.** This applies to `O ⧸ 𝔪 ^ k` for a discrete valuation ring `O` and `k ≥ 1`, and more
generally to every self-injective Artinian local ring. -/
theorem Finite.of_isReflexive_of_isNilpotent [IsLocalRing R] [Module.Injective R R]
    (h : IsNilpotent (IsLocalRing.maximalIdeal R)) [IsReflexive R M] : Module.Finite R M := by
  set 𝔪 := IsLocalRing.maximalIdeal R
  obtain ⟨s, hs, h𝔪s⟩ := Ideal.exists_ne_zero_forall_mul_eq_zero_of_isNilpotent h
  have : 𝔪.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  have : Module.Finite (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)) :=
    finite_quotient_smul_top_of_isReflexive 𝔪 hs h𝔪s
  have : Module.Finite R (M ⧸ 𝔪 • (⊤ : Submodule R M)) := .trans (R ⧸ 𝔪) _
  exact (TauCeti.isSuperfluous_smul_top_of_isNilpotent h).finite_of_finite_quotient

end Module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Real finrank of a compatible complex module

This file records the tower-law dimension formula for a complex module whose real scalar
structure is the ambient one. It is the linear-algebra input for almost-complex even-dimensionality
results, but has no symplectic hypotheses. Consequently a real-linear isomorphism between two such
modules preserves the complex dimension (`LinearEquiv.finrank_complex_eq`) and finite
dimensionality (`LinearEquiv.finiteDimensional_complex`), and one anticommuting with `I`, that is,
a conjugate-linear isomorphism, maps complex bases to complex bases
(`LinearEquiv.exists_basis_coe_eq_comp_of_map_I_smul`).
-/

public section

namespace TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- A compatible complex module structure forces the real dimension to be twice the complex
dimension. This is the ambient-real-structure form of Mathlib's `finrank_real_of_complex`: that
lemma fixes the real structure to be the one induced by restricting scalars
(`Module.complexToReal`), whereas here `V` already carries an ambient `Module ℝ V` made compatible
via `IsScalarTower ℝ ℂ V` (the situation produced by an almost complex structure). -/
theorem finrank_real_eq_two_mul_finrank_complex [Module ℂ V] [IsScalarTower ℝ ℂ V] :
    Module.finrank ℝ V = 2 * Module.finrank ℂ V := by
  rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]

end TauCeti

/-- Real-linearly isomorphic complex modules have the same complex dimension, since the real
dimension is twice the complex one (`TauCeti.finrank_real_eq_two_mul_finrank_complex`). -/
theorem LinearEquiv.finrank_complex_eq {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V]
    [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]
    (g : V ≃ₗ[ℝ] W) : Module.finrank ℂ V = Module.finrank ℂ W := by
  have := g.finrank_eq
  rw [TauCeti.finrank_real_eq_two_mul_finrank_complex,
    TauCeti.finrank_real_eq_two_mul_finrank_complex] at this
  omega

/-- A complex module real-linearly isomorphic to a finite-dimensional complex module is
finite-dimensional. -/
theorem LinearEquiv.finiteDimensional_complex {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [Module ℂ V] [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W] [Module ℂ W]
    [IsScalarTower ℝ ℂ W] (g : V ≃ₗ[ℝ] W) [FiniteDimensional ℂ V] : FiniteDimensional ℂ W :=
  have : Module.Finite ℝ V := .trans ℂ V
  have : Module.Finite ℝ W := .equiv g
  .of_restrictScalars_finite ℝ ℂ W

/-- A real-linear isomorphism anticommuting with `I`, that is, a conjugate-linear isomorphism,
maps a complex basis to a complex basis. -/
theorem LinearEquiv.exists_basis_coe_eq_comp_of_map_I_smul {V W : Type*} [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] [AddCommGroup W] [Module ℝ W] [Module ℂ W]
    [IsScalarTower ℝ ℂ W] {n : ℕ} (g : V ≃ₗ[ℝ] W)
    (hg : ∀ x, g (Complex.I • x) = -(Complex.I • g x)) (b : Module.Basis (Fin n) ℂ V) :
    ∃ b' : Module.Basis (Fin n) ℂ W, ⇑b' = g ∘ b := by
  have : FiniteDimensional ℂ V := .of_basis b
  have := g.finiteDimensional_complex
  have hconj := g.toLinearMap.map_smul_eq_conj_smul_of_map_I_smul hg
  have hli : LinearIndependent ℂ (g ∘ b) :=
    b.linearIndependent.map_of_injective_injectiveₛ (starRingEnd ℂ) g.toAddEquiv.toAddMonoidHom
      (RingHom.injective _) g.injective fun r m ↦ by simpa using hconj (starRingEnd ℂ r) m
  have hn : Fintype.card (Fin n) = Module.finrank ℂ W := by
    rw [← g.finrank_complex_eq, Module.finrank_eq_card_basis b]
  exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hn, by simp⟩

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import TauCeti.RingTheory.Trace.EmbeddingsMatrix.Basic

import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Small invertible matrices of algebra homomorphism values

For a full family of distinct algebra homomorphisms from a finite-dimensional seminormed
commutative algebra over a nontrivially normed field to an extension field,
`TauCeti.exists_norm_lt_isUnit_embeddingsMatrix` gives a basis of arbitrarily small vectors
whose matrix of homomorphism values is invertible.
-/

public section

namespace TauCeti

/-- For a full family of distinct algebra homomorphisms to a field, there is an invertible matrix
of their values on a basis whose elements have norm less than any given positive bound. -/
theorem exists_norm_lt_isUnit_embeddingsMatrix {F K Ω : Type*} [NontriviallyNormedField F]
    [SeminormedCommRing K] [NormedAlgebra F K] [FiniteDimensional F K] [Field Ω] [Algebra F Ω]
    {k : ℕ} (σ : Fin k → K →ₐ[F] Ω) (hσ : Function.Injective σ)
    (hk : Module.finrank F K = k) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : Fin k → K, (∀ j, ‖b j‖ < ε) ∧
      IsUnit ((Algebra.embeddingsMatrix F Ω b).submatrix id σ) := by
  let b := Module.finBasisOfFinrankEq F K hk
  have h (j : Fin k) : ∃ c : F, 0 < ‖c‖ ∧ ‖c‖ * ‖b j‖ < ε := by
    have hpos : 0 < ‖b j‖ + 1 := by positivity
    obtain ⟨c, hc, hc'⟩ := NormedField.exists_norm_lt F (div_pos hε hpos)
    refine ⟨c, hc, ?_⟩
    exact (mul_le_mul_of_nonneg_left (by simp) hc.le).trans_lt ((lt_div_iff₀ hpos).mp hc')
  choose c hc hc' using h
  let e := b.unitsSMul (fun j ↦ Units.mk0 (c j) (norm_pos_iff.mp (hc j)))
  refine ⟨e, fun j ↦ ?_, ?_⟩
  · simpa [e, Module.Basis.unitsSMul_apply, Units.smul_def, norm_smul] using hc' j
  · rw [← Matrix.linearIndependent_col_iff_isUnit]
    have h := (linearIndependent_algHom_toLinearMap F K Ω).comp σ hσ
    have hcoord : ((Algebra.embeddingsMatrix F Ω (e : Fin k → K)).submatrix id σ).col =
        (e.constr Ω).symm.toLinearMap ∘ (fun i ↦ (σ i).toLinearMap) := by
      funext i j
      simp only [Matrix.col_apply, Matrix.submatrix_apply, id_eq,
        Algebra.embeddingsMatrix_apply, Function.comp_apply, LinearEquiv.coe_coe,
        Module.Basis.constr_symm_apply, AlgHom.coe_toLinearMap]
    rw [hcoord]
    exact h.map' (e.constr Ω).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (e.constr Ω).symm.injective)

end TauCeti

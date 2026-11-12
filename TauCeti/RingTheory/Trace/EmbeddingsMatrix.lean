/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Linear independence of the rows of an embeddings matrix

Let `K` be a finite-dimensional algebra over a field `F` and `Ω` a field over `F`. For a family
`α : ι → K`, Mathlib's `Algebra.embeddingsMatrix F Ω α` is the matrix whose `(i, σ)` entry is
`σ (α i)`, the column index `σ` running over the `F`-algebra maps `K →ₐ[F] Ω`. When there are as
many of these maps as the degree `[K : F]` (for instance when `K / F` is a separable field
extension and `Ω` is algebraically closed, `AlgHom.card`), the rows of this matrix are linearly
independent over `Ω` exactly when `α` is linearly independent over `F`.

The proof uses that the `[K : F]` maps `K →ₐ[F] Ω` are linearly independent over `Ω` (Dedekind's
lemma, `linearIndependent_algHom_toLinearMap`) and hence form an `Ω`-basis of `K →ₗ[F] Ω`, whose
dimension is `[K : F]`. A linear relation between the rows is then a linear relation
`∑ᵢ cᵢ φ(αᵢ) = 0` valid for every `F`-linear `φ : K → Ω`, and choosing `φ` dual to `α` forces
`c = 0`.

For a number field `K` and `Ω = ℂ` this says that `ℚ`-linearly independent numbers
`α₁, …, αₙ ∈ K` have `ℂ`-linearly independent vectors of conjugates `(σ(αᵢ))_σ`, the input to the
general position of conjugate linear forms in the theory of norm form equations.

## Main results

* `Algebra.linearIndependent_embeddingsMatrix_row`: if `α` is linearly independent over `F`, the
  rows of `Algebra.embeddingsMatrix F Ω α` are linearly independent over `Ω`.
* `Algebra.linearIndependent_embeddingsMatrix_row_iff`: the converse also holds.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 7, Lemma 7.10.
-/

public section

namespace Algebra

variable {F K Ω ι : Type*} [Field F] [CommRing K] [Algebra F K] [Field Ω] [Algebra F Ω]

/-- **Conjugate vectors of independent elements are independent.** If there are `[K : F]`
algebra maps `K →ₐ[F] Ω` and `α` is linearly independent over `F`, then the vectors
`(σ (α i))_σ` are linearly independent over `Ω`. -/
theorem linearIndependent_embeddingsMatrix_row [FiniteDimensional F K]
    (hcard : Nat.card (K →ₐ[F] Ω) = Module.finrank F K) {α : ι → K}
    (hα : LinearIndependent F α) : LinearIndependent Ω (embeddingsMatrix F Ω α).row := by
  classical
  have := Fintype.ofFinite (K →ₐ[F] Ω)
  -- The `[K : F]` algebra maps span the `[K : F]`-dimensional space `K →ₗ[F] Ω` over `Ω`.
  have hspan : Submodule.span Ω
      (Set.range (AlgHom.toLinearMap : (K →ₐ[F] Ω) → K →ₗ[F] Ω)) = ⊤ :=
    (linearIndependent_algHom_toLinearMap F K Ω).span_eq_top_of_card_eq_finrank' <| by
      rw [Module.finrank_linearMap_self, ← hcard, Nat.card_eq_fintype_card]
  -- A family of `F`-linear maps `K → F` dual to `α`.
  obtain ⟨ψ, hψ⟩ := (Finsupp.linearCombination F α).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hα)
  have hψα (i : ι) : ψ (α i) = Finsupp.single i 1 := by
    simpa using LinearMap.congr_fun hψ (Finsupp.single i 1)
  rw [linearIndependent_iff']
  intro s c hc j hj
  -- The `Ω`-linear functional `φ ↦ ∑ᵢ cᵢ φ(αᵢ)` vanishes on the algebra maps, hence everywhere.
  let Λ : (K →ₗ[F] Ω) →ₗ[Ω] Ω :=
    { toFun φ := ∑ i ∈ s, c i * φ (α i)
      map_add' φ φ' := by simp [mul_add, Finset.sum_add_distrib]
      map_smul' a φ := by simp [Finset.mul_sum, mul_left_comm] }
  have hΛ : Λ = 0 := LinearMap.ext_on_range hspan fun σ ↦ by
    simpa [Λ, Finset.sum_apply, Matrix.row] using congr_fun hc σ
  simpa [Λ, hψα, Finsupp.single_apply, hj] using
    LinearMap.congr_fun hΛ ((Algebra.linearMap F Ω).comp ((Finsupp.lapply j).comp ψ))

/-- If there are `[K : F]` algebra maps `K →ₐ[F] Ω`, the vectors `(σ (α i))_σ` are linearly
independent over `Ω` exactly when `α` is linearly independent over `F`. -/
theorem linearIndependent_embeddingsMatrix_row_iff [FiniteDimensional F K]
    (hcard : Nat.card (K →ₐ[F] Ω) = Module.finrank F K) {α : ι → K} :
    LinearIndependent Ω (embeddingsMatrix F Ω α).row ↔ LinearIndependent F α := by
  refine ⟨fun h ↦ ?_, linearIndependent_embeddingsMatrix_row hcard⟩
  -- The rows are the images of `α` under the `F`-linear map `x ↦ (σ x)_σ`.
  exact (h.restrict_scalars' F).of_comp (LinearMap.pi fun σ : K →ₐ[F] Ω ↦ σ.toLinearMap)

end Algebra

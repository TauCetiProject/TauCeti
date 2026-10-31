/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.AlgHom
public import TauCeti.LinearAlgebra.LinearIndependent.GeneralPosition
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.RingTheory.Trace.Basic
import TauCeti.GroupTheory.GroupAction.MultipleTransitivity
import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.RingTheory.Trace.EmbeddingsMatrix

/-!
# Conjugate linear forms in general position

Let `K` be a finite-dimensional algebra over a field `F`, let `Ω` be a field over `F` admitting
`[K : F]` algebra maps `K →ₐ[F] Ω`, and let `α₁, …, αₙ ∈ K` be linearly independent over `F`.
Every `σ : K →ₐ[F] Ω` gives a conjugate linear form `∑ᵢ σ(αᵢ) Xᵢ`, whose coefficient vector
`(σ(α₁), …, σ(αₙ))` is the column of `Algebra.embeddingsMatrix F Ω α` at `σ`.

The automorphism group `Ω ≃ₐ[F] Ω` acts on these maps by postcomposition. If it acts
`n`-pretransitively, the conjugate forms are in general position: any `n` of them are linearly
independent. Indeed the rows of the embeddings matrix are independent
(`Algebra.linearIndependent_embeddingsMatrix_row`), so some `n × n` minor is nonzero. Any other
`n` columns are the image of these under an automorphism `τ` of `Ω`, so their minor is the image
of a nonzero minor under `τ`, and is nonzero as well.

The hypothesis holds when the automorphism group induces every permutation of the maps
`K →ₐ[F] Ω`. For a number field `K = ℚ(θ)` of degree `d` and a normal closure `Ω` of `K`, this
is the condition that the Galois group of `Ω / ℚ` is the full symmetric group `S_d`. In that case
the norm form `N_{K/ℚ}(α₁ X₁ + ⋯ + αₙ Xₙ)`, the product of the `d` conjugate forms, is a product
of linear forms in general position, to which the Subspace Theorem applies.

## Main results

* `TauCeti.inGeneralPosition_embeddingsMatrix_col`: if `Ω ≃ₐ[F] Ω` acts `n`-pretransitively on
  `K →ₐ[F] Ω`, the conjugate forms of independent `α₁, …, αₙ` are in general position.
* `TauCeti.inGeneralPosition_embeddingsMatrix_col_of_surjective`: the same when `Ω ≃ₐ[F] Ω`
  induces every permutation of `K →ₐ[F] Ω`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), Chapter 7, Lemma 7.11.
-/

public section

open MulAction

namespace TauCeti

variable {F K Ω : Type*} [Field F] [CommRing K] [Algebra F K] [Field Ω] [Algebra F Ω]
  [FiniteDimensional F K] {n : ℕ}

/-- **Conjugate linear forms are in general position.** Suppose that there are `[K : F]` algebra
maps `K →ₐ[F] Ω` and that `Ω ≃ₐ[F] Ω` acts `n`-pretransitively on them. If `α₁, …, αₙ ∈ K` are
linearly independent over `F`, then the coefficient vectors `(σ(α₁), …, σ(αₙ))` of the conjugate
forms `∑ᵢ σ(αᵢ) Xᵢ`, for `σ : K →ₐ[F] Ω`, are in general position. -/
theorem inGeneralPosition_embeddingsMatrix_col
    [IsMultiplyPretransitive (Ω ≃ₐ[F] Ω) (K →ₐ[F] Ω) n]
    (hcard : Nat.card (K →ₐ[F] Ω) = Module.finrank F K) {α : Fin n → K}
    (hα : LinearIndependent F α) :
    InGeneralPosition (Algebra.embeddingsMatrix F Ω α).col := by
  classical
  -- Some `n` columns of the embeddings matrix have a nonzero minor.
  obtain ⟨e₀, he₀⟩ := Matrix.linearIndependent_row_iff_exists_det_submatrix_ne_zero.mp
    (Algebra.linearIndependent_embeddingsMatrix_row hcard hα)
  rw [inGeneralPosition_iff_det_ne_zero]
  intro e he
  -- Any other `n` columns are obtained by applying an automorphism `τ` to those.
  obtain ⟨τ, hτ⟩ := exists_smul_eq (Ω ≃ₐ[F] Ω) e₀ ⟨e, he⟩
  have hminor : Matrix.of (fun k i ↦ (Algebra.embeddingsMatrix F Ω α).col (e k) i) =
      (τ : Ω →+* Ω).mapMatrix ((Algebra.embeddingsMatrix F Ω α).submatrix id e₀).transpose := by
    ext k i
    have hk : e k = τ • e₀ k := by
      simpa [Function.Embedding.smul_apply] using (DFunLike.congr_fun hτ k).symm
    simp [hk, Matrix.col]
  rw [hminor, ← RingHom.map_det, Matrix.det_transpose]
  exact (map_ne_zero _).mpr he₀

/-- **Conjugate linear forms are in general position, full symmetric case.** Suppose that there
are `[K : F]` algebra maps `K →ₐ[F] Ω` and that every permutation of them is induced by an
automorphism of `Ω`. If `α₁, …, αₙ ∈ K` are linearly independent over `F`, then the coefficient
vectors `(σ(α₁), …, σ(αₙ))` of the conjugate forms `∑ᵢ σ(αᵢ) Xᵢ` are in general position. -/
theorem inGeneralPosition_embeddingsMatrix_col_of_surjective
    (hG : Function.Surjective (toPermHom (Ω ≃ₐ[F] Ω) (K →ₐ[F] Ω)))
    (hcard : Nat.card (K →ₐ[F] Ω) = Module.finrank F K) {α : Fin n → K}
    (hα : LinearIndependent F α) :
    InGeneralPosition (Algebra.embeddingsMatrix F Ω α).col :=
  have := isMultiplyPretransitive_of_surjective_toPermHom hG n
  inGeneralPosition_embeddingsMatrix_col hcard hα

end TauCeti

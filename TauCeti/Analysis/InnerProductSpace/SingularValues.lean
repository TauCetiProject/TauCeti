/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Data.Finsupp.Antitone
public import TauCeti.LinearAlgebra.Eigenspace.Comp

/-!
# Singular values of the adjoint and the two Gram spectra

Mathlib defines the singular values of a linear map `A : E →ₗ[𝕜] F` between finite-dimensional
inner product spaces from the source Gram operator `A† A` (`LinearMap.singularValues`). This file
shows that the target Gram operator `A A†` carries the same information: the nonzero eigenvalues
of `A† A` and `A A†` agree with multiplicity, so their sorted eigenvalue lists agree through the
common dimension and vanish beyond the rank of `A`. Equivalently, `A` and `A†` have the same
singular values.

The multiplicity statement is `Module.End.finrank_eigenspace_comp_comm` applied to `A` and `A†`.
A positive value `s` occurs among the singular values of `A` as often as `s²` occurs among the
eigenvalues of `A† A` (`LinearMap.ncard_ofPred_singularValues_eq`), and a sorted zero-padded
sequence is determined by these multiplicities (`Finsupp.eq_of_antitone_of_ncard_eq`).

## Main declarations

* `LinearMap.ncard_ofPred_singularValues_eq`: the multiplicity of a positive singular value `s`
  is the dimension of the `s²`-eigenspace of `A† A`.
* `LinearMap.singularValues_adjoint`: `A†` has the same singular values as `A`.
* `LinearMap.sq_singularValues_eq_eigenvalues_self_comp_adjoint`: the squared singular values
  are also the sorted eigenvalues of `A A†`.
* `LinearMap.eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint`: the sorted
  eigenvalues of `A† A` and `A A†` agree at every index below both dimensions.
* `LinearMap.eigenvalues_adjoint_comp_self_eq_zero_iff`,
  `LinearMap.eigenvalues_self_comp_adjoint_eq_zero_iff`: both sorted eigenvalue lists vanish
  exactly from the rank of `A` on.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22 and Section 7.3.
-/

public section

open Module Module.End

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- A positive value `s` occurs among the singular values of `T` as many times as the dimension
of the `s²`-eigenspace of `T† T`. -/
theorem ncard_ofPred_singularValues_eq (T : E →ₗ[𝕜] F) {s : ℝ} (hs : 0 < s) :
    {i | T.singularValues i = s}.ncard =
      finrank 𝕜 (eigenspace (adjoint T ∘ₗ T) ((s ^ 2 : ℝ) : 𝕜)) := by
  have hT := T.isSymmetric_adjoint_comp_self
  have hset : {i | T.singularValues i = s} =
      Fin.val '' {k | (hT.eigenvalues rfl k : 𝕜) = ((s ^ 2 : ℝ) : 𝕜)} := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_image, RCLike.ofReal_inj]
    constructor
    · intro hi
      have hlt : i < finrank 𝕜 E :=
        lt_of_not_ge fun h ↦ hs.ne' (hi ▸ T.singularValues_of_finrank_le h)
      exact ⟨⟨i, hlt⟩, by rw [← T.sq_singularValues_of_lt rfl hlt, hi], rfl⟩
    · rintro ⟨k, hk, rfl⟩
      rwa [← T.sq_singularValues_fin rfl k, sq_eq_sq₀ (T.singularValues_nonneg _) hs.le] at hk
  rw [hset, Set.ncard_image_of_injective _ Fin.val_injective, ← hT.card_filter_eigenvalues_eq rfl,
    ← Set.ncard_coe_finset, Finset.coe_filter_univ]

/-- A linear map and its adjoint have the same singular values. -/
@[simp]
theorem singularValues_adjoint (A : E →ₗ[𝕜] F) :
    (adjoint A).singularValues = A.singularValues := by
  refine Finsupp.eq_of_antitone_of_ncard_eq (singularValues_antitone _)
    (singularValues_antitone _) fun s hs ↦ ?_
  rcases hs.lt_or_gt with hs | hs
  · have hempty (σ : ℕ →₀ ℝ) (hσ : ∀ i, 0 ≤ σ i) : {i | σ i = s} = ∅ :=
      Set.eq_empty_of_forall_notMem fun i hi ↦ (hσ i).not_gt (hi ▸ hs)
    rw [hempty _ (singularValues_nonneg _), hempty _ (singularValues_nonneg _)]
  · rw [ncard_ofPred_singularValues_eq _ hs, ncard_ofPred_singularValues_eq _ hs, adjoint_adjoint,
      finrank_eigenspace_comp_comm A (adjoint A) (by simpa using hs.ne')]

/-- The squared singular values of `A` are the sorted eigenvalues of the target Gram operator
`A A†`, at every index below the dimension of the target. -/
theorem sq_singularValues_eq_eigenvalues_self_comp_adjoint (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) {i : ℕ} (hin : i < n) :
    A.singularValues i ^ 2 = A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ := by
  simpa only [adjoint_adjoint, singularValues_adjoint] using
    (adjoint A).sq_singularValues_of_lt hn hin

/-- The sorted eigenvalues of the source Gram operator `A† A` and the target Gram operator `A A†`
agree at every index below both dimensions. -/
theorem eigenvalues_adjoint_comp_self_eq_eigenvalues_self_comp_adjoint (A : E →ₗ[𝕜] F)
    {m n : ℕ} (hm : finrank 𝕜 E = m) (hn : finrank 𝕜 F = n) {i : ℕ} (him : i < m) (hin : i < n) :
    A.isSymmetric_adjoint_comp_self.eigenvalues hm ⟨i, him⟩ =
      A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ := by
  rw [← A.sq_singularValues_of_lt hm him, A.sq_singularValues_eq_eigenvalues_self_comp_adjoint]

/-- The sorted eigenvalues of the source Gram operator `A† A` vanish exactly from the rank of `A`
on. -/
theorem eigenvalues_adjoint_comp_self_eq_zero_iff (A : E →ₗ[𝕜] F) {m : ℕ}
    (hm : finrank 𝕜 E = m) {i : ℕ} (him : i < m) :
    A.isSymmetric_adjoint_comp_self.eigenvalues hm ⟨i, him⟩ = 0 ↔ finrank 𝕜 (range A) ≤ i := by
  rw [← A.sq_singularValues_of_lt hm him, sq_eq_zero_iff,
    singularValues_eq_zero_iff_le_finrank_range]

/-- The sorted eigenvalues of the target Gram operator `A A†` vanish exactly from the rank of `A`
on. -/
theorem eigenvalues_self_comp_adjoint_eq_zero_iff (A : E →ₗ[𝕜] F) {n : ℕ}
    (hn : finrank 𝕜 F = n) {i : ℕ} (hin : i < n) :
    A.isSymmetric_self_comp_adjoint.eigenvalues hn ⟨i, hin⟩ = 0 ↔ finrank 𝕜 (range A) ≤ i := by
  rw [← A.sq_singularValues_eq_eigenvalues_self_comp_adjoint hn hin, sq_eq_zero_iff,
    singularValues_eq_zero_iff_le_finrank_range]

end LinearMap

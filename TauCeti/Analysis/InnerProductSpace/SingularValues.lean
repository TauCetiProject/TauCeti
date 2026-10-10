/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Data.Finsupp.Antitone
public import TauCeti.LinearAlgebra.Eigenspace.Comp

/-!
# Singular values, the two Gram spectra, and the singular system

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

## The singular system

The second half of the file builds the singular system of `A` from these spectra. The right
singular basis `(vᵢ) = A.rightSingularBasis` is the ordered orthonormal eigenbasis of `A† A`, in
whose order the singular values are listed (`LinearMap.sq_singularValues_fin`), and the left
singular vectors are `uᵢ = σᵢ⁻¹ A vᵢ = A.leftSingularVector i`, using total field inversion so
that `uᵢ = 0` when `σᵢ = 0`. The singular relations hold at every index, which lets the expansion
of `A` run over the whole basis without splitting off the kernel.

* `LinearMap.adjoint_comp_self_rightSingularBasis`: `A† A vᵢ = σᵢ² vᵢ`.
* `LinearMap.apply_rightSingularBasis`: `A vᵢ = σᵢ uᵢ`.
* `LinearMap.adjoint_leftSingularVector`: `A† uᵢ = σᵢ vᵢ`.
* `LinearMap.self_comp_adjoint_leftSingularVector`: `A A† uᵢ = σᵢ² uᵢ`.
* `LinearMap.orthonormal_leftSingularVector`: the `uᵢ` with `σᵢ ≠ 0` are orthonormal.
* `LinearMap.sum_norm_inner_leftSingularVector_sq_le`: Bessel's inequality for the whole family
  `(uᵢ)`, zero vectors included.
* `LinearMap.apply_eq_sum_singularValues_smul`: `A x = ∑ᵢ σᵢ ⟪vᵢ, x⟫ uᵢ`.
* `LinearMap.eq_sum_singularValues_smul_rankOne`: `A = ∑ᵢ σᵢ uᵢ ⊗ vᵢ`, the singular value
  decomposition in rank-one form.
* `LinearMap.exists_orthonormalBasis_apply_eq_leftSingularVector`: the nonzero left singular
  vectors extend, index by index, to an orthonormal basis of the codomain.

## Comparison of singular values

The last section compares the singular values of two maps with the same source through the
Courant–Fischer min–max principle for their source Gram operators.

* `LinearMap.singularValues_le_mul_of_norm_apply_le`: if `‖B x‖ ≤ c ‖A x‖` for every `x`, then
  `σᵢ(B) ≤ c σᵢ(A)` for every `i`.
* `LinearMap.singularValues_comp_le`: if `‖C y‖ ≤ c ‖y‖` for every `y`, then
  `σᵢ(C A) ≤ c σᵢ(A)` for every `i`.

## Source

The singular-system definitions `LinearMap.rightSingularBasis` and
`LinearMap.leftSingularVector` are adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22, Theorem 2.6.3 and Section 7.3.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991,
  Section 3.3.
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

section SingularSystem

open InnerProductSpace

variable (A : E →ₗ[𝕜] F)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **right singular basis** of `A`: the orthonormal eigenbasis `(vᵢ)` of the source Gram
operator `A† A`, ordered so that `A† A vᵢ = σᵢ² vᵢ` for the singular values
`σᵢ = A.singularValues i` of `A`, listed in nonincreasing order. -/
noncomputable def rightSingularBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The right singular basis is Mathlib's ordered eigenbasis of `A† A`; this connects it to the
`LinearMap.IsSymmetric.eigenvectorBasis` API. -/
theorem rightSingularBasis_def :
    A.rightSingularBasis = A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl :=
  (rfl)

/-- The right singular vectors are eigenvectors of `A† A` for the squared singular values. -/
theorem adjoint_comp_self_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    (adjoint A ∘ₗ A) (A.rightSingularBasis i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.rightSingularBasis i := by
  rw [A.sq_singularValues_fin rfl, rightSingularBasis_def]
  exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i

/-- Inner products of `A vᵢ` against the range of `A`: `⟪A vᵢ, A x⟫ = σᵢ² ⟪vᵢ, x⟫` for a right
singular vector `vᵢ`. -/
theorem inner_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) (x : E) :
    ⟪A (A.rightSingularBasis i), A x⟫ =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) * ⟪A.rightSingularBasis i, x⟫ := by
  rw [← adjoint_inner_left, ← comp_apply, adjoint_comp_self_rightSingularBasis, inner_smul_left,
    RCLike.conj_ofReal]

/-- `A` stretches the `i`-th right singular vector by the `i`-th singular value:
`‖A vᵢ‖ = σᵢ`. -/
@[simp]
theorem norm_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    ‖A (A.rightSingularBasis i)‖ = A.singularValues i := by
  have h := A.inner_apply_rightSingularBasis i (A.rightSingularBasis i)
  simp only [inner_self_eq_norm_sq_to_K, OrthonormalBasis.norm_eq_one, RCLike.ofReal_one,
    one_pow, mul_one] at h
  norm_cast at h
  exact (sq_eq_sq₀ (norm_nonneg _) (A.singularValues_nonneg _)).mp h

/-- A right singular vector lies in the kernel of `A` exactly when its singular value
vanishes. -/
@[simp]
theorem apply_rightSingularBasis_eq_zero_iff {i : Fin (finrank 𝕜 E)} :
    A (A.rightSingularBasis i) = 0 ↔ A.singularValues i = 0 := by
  rw [← norm_eq_zero, norm_apply_rightSingularBasis]

/-- A right singular vector with singular value zero lies in the kernel, so `A vᵢ` is fixed by
the scalar `σᵢ⁻² σᵢ²` (with total field inversion) even when `σᵢ = 0`. -/
theorem inv_mul_smul_apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    (((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) •
      A (A.rightSingularBasis i) = A (A.rightSingularBasis i) := by
  by_cases hc : A.singularValues i = 0
  · rw [(A.apply_rightSingularBasis_eq_zero_iff).mpr hc, smul_zero]
  · rw [inv_mul_cancel₀ (by simpa using hc), one_smul]

/-- The **left singular vectors** of `A`: `uᵢ = σᵢ⁻¹ A vᵢ` for the right singular basis `(vᵢ)`,
with total field inversion, so that `uᵢ = 0` when `σᵢ = 0`. The vectors with `σᵢ ≠ 0` form an
orthonormal family (`LinearMap.orthonormal_leftSingularVector`). -/
noncomputable def leftSingularVector (i : Fin (finrank 𝕜 E)) : F :=
  ((A.singularValues i : ℝ) : 𝕜)⁻¹ • A (A.rightSingularBasis i)

/-- Unfolds the left singular vector `uᵢ = σᵢ⁻¹ A vᵢ`. -/
theorem leftSingularVector_def (i : Fin (finrank 𝕜 E)) :
    A.leftSingularVector i = ((A.singularValues i : ℝ) : 𝕜)⁻¹ • A (A.rightSingularBasis i) :=
  (rfl)

/-- The singular relation `A vᵢ = σᵢ uᵢ`, valid at every index, including those with
`σᵢ = 0`. -/
theorem apply_rightSingularBasis (i : Fin (finrank 𝕜 E)) :
    A (A.rightSingularBasis i) = ((A.singularValues i : ℝ) : 𝕜) • A.leftSingularVector i := by
  rw [leftSingularVector_def, smul_smul]
  by_cases hc : A.singularValues i = 0
  · rw [(A.apply_rightSingularBasis_eq_zero_iff).mpr hc, smul_zero]
  · rw [mul_inv_cancel₀ (by simpa using hc), one_smul]

/-- The left singular vectors are orthonormal up to the zero vectors at the vanishing singular
values: `⟪uᵢ, uⱼ⟫` is `1` if `i = j` and `σᵢ ≠ 0`, and `0` otherwise. -/
theorem inner_leftSingularVector (i j : Fin (finrank 𝕜 E)) :
    ⟪A.leftSingularVector i, A.leftSingularVector j⟫ =
      if i = j ∧ A.singularValues i ≠ 0 then 1 else 0 := by
  simp only [leftSingularVector_def, inner_smul_left, inner_smul_right,
    inner_apply_rightSingularBasis, orthonormal_iff_ite.mp (A.rightSingularBasis).orthonormal]
  rcases eq_or_ne i j with rfl | hij
  · by_cases hc : A.singularValues i = 0
    · simp [hc]
    · have hc' : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := by simpa using hc
      simp [hc]
      field_simp [hc']
  · simp [hij]

/-- The left singular vectors with nonzero singular value form an orthonormal family. -/
theorem orthonormal_leftSingularVector :
    Orthonormal 𝕜 fun i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0} ↦
      A.leftSingularVector i := by
  classical
  refine orthonormal_iff_ite.mpr fun i j ↦ ?_
  simp [inner_leftSingularVector, i.2, Subtype.ext_iff]

/-- A left singular vector vanishes exactly when its singular value does. -/
@[simp]
theorem leftSingularVector_eq_zero_iff {i : Fin (finrank 𝕜 E)} :
    A.leftSingularVector i = 0 ↔ A.singularValues i = 0 := by
  rw [← inner_self_eq_zero (𝕜 := 𝕜), inner_leftSingularVector]
  simp

/-- A left singular vector has norm at most one: it is a unit vector when its singular value is
nonzero and zero otherwise. -/
theorem norm_leftSingularVector_le_one (i : Fin (finrank 𝕜 E)) : ‖A.leftSingularVector i‖ ≤ 1 := by
  by_cases hσ : A.singularValues i = 0
  · simp [(A.leftSingularVector_eq_zero_iff).mpr hσ]
  · exact (A.orthonormal_leftSingularVector.1 ⟨i, hσ⟩).le

/-- **Bessel's inequality** for the left singular vectors: `∑ᵢ ‖⟪uᵢ, x⟫‖² ≤ ‖x‖²`. The vectors at
the vanishing singular values are zero, so the orthonormal subfamily carries the whole sum. -/
theorem sum_norm_inner_leftSingularVector_sq_le (x : F) :
    ∑ i, ‖⟪A.leftSingularVector i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  calc ∑ i, ‖⟪A.leftSingularVector i, x⟫‖ ^ 2
      = ∑ i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0},
          ‖⟪A.leftSingularVector i, x⟫‖ ^ 2 := by
        rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun i ↦ A.singularValues i ≠ 0)
          (f := fun i ↦ ‖⟪A.leftSingularVector i, x⟫‖ ^ 2) fun i _ h hσ ↦ h (by
            simp [(A.leftSingularVector_eq_zero_iff).mpr hσ])]
        exact Finset.sum_subtype _ (by simp) _
    _ ≤ ‖x‖ ^ 2 := A.orthonormal_leftSingularVector.sum_inner_products_le x

/-- The adjoint singular relation `A† uᵢ = σᵢ vᵢ`, valid at every index, including those with
`σᵢ = 0`. -/
@[simp]
theorem adjoint_leftSingularVector (i : Fin (finrank 𝕜 E)) :
    adjoint A (A.leftSingularVector i) =
      ((A.singularValues i : ℝ) : 𝕜) • A.rightSingularBasis i := by
  rw [leftSingularVector_def, map_smul, ← comp_apply, adjoint_comp_self_rightSingularBasis]
  simp [smul_smul, sq, ← mul_assoc]

/-- The eigenvalue equation `A A† uᵢ = σᵢ² uᵢ` for the target Gram operator, at every index.
When `σᵢ ≠ 0`, `uᵢ` is an eigenvector of `A A†` for `σᵢ²`; when `σᵢ = 0`, `uᵢ = 0`. -/
theorem self_comp_adjoint_leftSingularVector (i : Fin (finrank 𝕜 E)) :
    (A ∘ₗ adjoint A) (A.leftSingularVector i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) • A.leftSingularVector i := by
  simp [adjoint_leftSingularVector, apply_rightSingularBasis, smul_smul, sq]

/-- The **singular expansion** of a vector: `A x = ∑ᵢ σᵢ ⟪vᵢ, x⟫ uᵢ`. -/
theorem apply_eq_sum_singularValues_smul (x : E) :
    A x = ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i : ℝ) : 𝕜) • ⟪A.rightSingularBasis i, x⟫ •
      A.leftSingularVector i := by
  conv_lhs => rw [← (A.rightSingularBasis).sum_repr' x]
  simp only [map_sum, map_smul, apply_rightSingularBasis]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- The **singular value decomposition** in rank-one form: `A = ∑ᵢ σᵢ uᵢ ⊗ vᵢ`, where
`u ⊗ v` is the rank-one map `x ↦ ⟪v, x⟫ u`. -/
theorem eq_sum_singularValues_smul_rankOne :
    A = ∑ i : Fin (finrank 𝕜 E), ((A.singularValues i : ℝ) : 𝕜) •
      (rankOne 𝕜 (A.leftSingularVector i) (A.rightSingularBasis i)).toLinearMap := by
  ext x
  simp [A.apply_eq_sum_singularValues_smul x]

/-- The left singular vectors with nonzero singular value extend to an orthonormal basis of the
codomain, indexed compatibly with the right singular basis: there is an orthonormal basis `(wⱼ)`
of `F` with `wᵢ = uᵢ` whenever `σᵢ ≠ 0`. Together with `LinearMap.apply_rightSingularBasis`
this gives `A vᵢ = σᵢ wᵢ` at every index below both dimensions. -/
theorem exists_orthonormalBasis_apply_eq_leftSingularVector :
    ∃ w : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F, ∀ (i : Fin (finrank 𝕜 E))
      (j : Fin (finrank 𝕜 F)), (i : ℕ) = j → A.singularValues i ≠ 0 →
        w j = A.leftSingularVector i := by
  -- Reindex the left singular vectors by `Fin (finrank 𝕜 F)`, padding with zero, and extend the
  -- orthonormal subfamily at the nonzero singular values.
  have hlt {j : ℕ} (hj : A.singularValues j ≠ 0) : j < finrank 𝕜 E :=
    lt_of_not_ge fun h ↦ hj (A.singularValues_of_finrank_le h)
  let u : Fin (finrank 𝕜 F) → F := fun j ↦
    if h : (j : ℕ) < finrank 𝕜 E then A.leftSingularVector ⟨j, h⟩ else 0
  let s : Set (Fin (finrank 𝕜 F)) := {j | A.singularValues j ≠ 0}
  have hu : s.domRestrict u = (fun i : {i : Fin (finrank 𝕜 E) // A.singularValues i ≠ 0} ↦
      A.leftSingularVector i) ∘ fun j ↦ ⟨⟨j.1, hlt j.2⟩, j.2⟩ := by
    ext j
    simp [u, hlt j.2]
  have hs : Orthonormal 𝕜 (s.domRestrict u) := by
    rw [hu]
    exact A.orthonormal_leftSingularVector.comp _ fun j k h ↦ by
      simpa [Subtype.ext_iff, Fin.ext_iff] using h
  obtain ⟨w, hw⟩ := hs.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨w, fun i j hij hi ↦ ?_⟩
  have hj : j ∈ s := by simpa [s, ← hij] using hi
  rw [hw j hj]
  simp [u, ← hij]

end SingularSystem

section Comparison

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]

/-- If `‖B x‖ ≤ c * ‖A x‖` for every `x`, then every singular value of `B` is at most `c` times the
corresponding singular value of `A`. -/
theorem singularValues_le_mul_of_norm_apply_le {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] G} {c : ℝ}
    (h : ∀ x, ‖B x‖ ≤ c * ‖A x‖) (i : ℕ) :
    B.singularValues i ≤ c * A.singularValues i := by
  rcases lt_or_ge c 0 with hc | hc
  · -- A negative constant forces `A = 0` and `B = 0`.
    have hA : A = 0 := ext fun x ↦ norm_le_zero_iff.mp <|
      nonpos_of_mul_nonneg_right ((norm_nonneg _).trans (h x)) hc
    have hB : B = 0 := ext fun x ↦ norm_le_zero_iff.mp <| by simpa [hA] using h x
    simp [hA, hB]
  rcases lt_or_ge i (finrank 𝕜 E) with hi | hi
  swap
  · simp [B.singularValues_of_finrank_le hi, A.singularValues_of_finrank_le hi]
  -- Courant–Fischer: on an `(i + 1)`-dimensional subspace where the Rayleigh quotient of `B† B` is
  -- at least `σᵢ(B)²`, find a unit vector where that of `A† A` is at most `σᵢ(A)²`.
  obtain ⟨V, hV, hBV⟩ :=
    B.isSymmetric_adjoint_comp_self.exists_submodule_forall_unit_eigenvalue_le_re_inner rfl ⟨i, hi⟩
  obtain ⟨x, hxV, hx, hAx⟩ :=
    A.isSymmetric_adjoint_comp_self.exists_unit_vector_re_inner_le_eigenvalue rfl ⟨i, hi⟩ V hV
  have hBx := hBV x hxV hx
  simp only [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq] at hAx hBx
  have hsq : B.singularValues i ^ 2 ≤ (c * A.singularValues i) ^ 2 := by
    rw [mul_pow, B.sq_singularValues_of_lt rfl hi, A.sq_singularValues_of_lt rfl hi]
    calc _ ≤ ‖B x‖ ^ 2 := hBx
      _ ≤ (c * ‖A x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (h x) 2
      _ ≤ _ := by rw [mul_pow]; exact mul_le_mul_of_nonneg_left hAx (sq_nonneg c)
  exact (pow_le_pow_iff_left₀ (B.singularValues_nonneg i)
    (mul_nonneg hc (A.singularValues_nonneg i)) two_ne_zero).mp hsq

/-- **Bounded-factor domination.** If `‖C y‖ ≤ c * ‖y‖` for every `y` (for `c ≥ 0`: if `C` has
operator norm at most `c`), then `σᵢ(C A) ≤ c σᵢ(A)` for every `i`. -/
theorem singularValues_comp_le (C : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) {c : ℝ}
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) (i : ℕ) :
    (C ∘ₗ A).singularValues i ≤ c * A.singularValues i :=
  singularValues_le_mul_of_norm_apply_le (fun x ↦ hC (A x)) i

end Comparison

end LinearMap

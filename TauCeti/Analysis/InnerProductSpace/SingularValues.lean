/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import TauCeti.Analysis.InnerProductSpace.Adjoint
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
* `LinearMap.singularValues_eq_of_norm_apply_eq`: if `‖B x‖ = ‖A x‖` for every `x`, then `A` and
  `B` have the same singular values.
* `LinearMap.singularValues_linearIsometryEquiv_comp`,
  `LinearMap.singularValues_comp_linearIsometryEquiv`: composing with isometric isomorphisms on
  either side leaves the singular values unchanged.

## Diagonal models

For an orthonormal basis `(eᵢ)` of `E` and scalars `(dᵢ)`, the diagonal operator with `eᵢ` as
eigenvectors and diagonal entries `dᵢ` is Mathlib's
`Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)`. Its additivity in `d`
(`Matrix.diagonal_add`), its adjoint (`Matrix.toLin_conjTranspose` with
`Matrix.diagonal_conjTranspose`) and its symmetry for real entries (`Matrix.isSymmetric_toLin_iff`)
are in Mathlib. The last section computes its singular values and shows that every map is a
diagonal map up to isometries on both sides.

* `Matrix.toLin_diagonal_apply_self`: the diagonal operator sends `eᵢ` to `dᵢ eᵢ`.
* `Matrix.singularValues_toLin_diagonal`: the singular values of the diagonal operator are the
  norms `‖dᵢ‖` listed in nonincreasing order.
* `LinearMap.exists_linearIsometryEquiv_eq_comp_toLin_comp`: every map `A : E →ₗ[𝕜] F` is `U D V`
  for linear isometric equivalences `U` of `F` and `V` of `E` and the rectangular diagonal map `D`
  with the singular values of `A` on its diagonal, in any prescribed orthonormal bases.
* `LinearMap.exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp`: every endomorphism `A` is
  `U D V` for linear isometric equivalences `U`, `V` and the diagonal operator `D` with the
  singular values of `A` as entries, in any prescribed orthonormal basis.
* `LinearMap.exists_orthonormal_eq_sum_singularValues_smul_rankOne`: the compact singular value
  decomposition `A = ∑_{i < p} σᵢ wᵢ ⊗ vᵢ`, with `p = min (dim E) (dim F)` and both families
  orthonormal.

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
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section I.2
  (the singular value decomposition).
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

/-- The singular values of `A : E →ₗ[𝕜] F` vanish from the dimension of the target on. -/
theorem singularValues_of_finrank_le_right (A : E →ₗ[𝕜] F) {i : ℕ} (hi : finrank 𝕜 F ≤ i) :
    A.singularValues i = 0 := by
  rw [← singularValues_adjoint]
  exact (adjoint A).singularValues_of_finrank_le hi

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

/-- Two maps with the same source and `‖B x‖ = ‖A x‖` for every `x` have the same singular
values. -/
theorem singularValues_eq_of_norm_apply_eq {A : E →ₗ[𝕜] F} {B : E →ₗ[𝕜] G}
    (h : ∀ x, ‖B x‖ = ‖A x‖) : B.singularValues = A.singularValues := by
  ext i
  exact le_antisymm
    (by simpa using singularValues_le_mul_of_norm_apply_le (c := 1) (by simp [h]) i)
    (by simpa using singularValues_le_mul_of_norm_apply_le (c := 1) (by simp [h]) i)

/-- Composing on the left with an isometric isomorphism leaves the singular values unchanged. -/
@[simp]
theorem singularValues_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] G) (A : E →ₗ[𝕜] F) :
    ((U : F →ₗ[𝕜] G) ∘ₗ A).singularValues = A.singularValues :=
  singularValues_eq_of_norm_apply_eq fun x ↦ by simp

/-- Composing on the right with an isometric isomorphism leaves the singular values unchanged. -/
@[simp]
theorem singularValues_comp_linearIsometryEquiv (A : E →ₗ[𝕜] F) (V : G ≃ₗᵢ[𝕜] E) :
    (A ∘ₗ (V : G →ₗ[𝕜] E)).singularValues = A.singularValues := by
  rw [← singularValues_adjoint, adjoint_comp, V.adjoint_coe_eq_symm,
    singularValues_linearIsometryEquiv_comp, singularValues_adjoint]

end Comparison

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional 𝕜 E] in
/-- The diagonal operator of an orthonormal basis `(eᵢ)` with entries `(dᵢ)` has `eᵢ` as an
eigenvector with eigenvalue `dᵢ`. -/
@[simp]
theorem _root_.Matrix.toLin_diagonal_apply_self (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜)
    (i : ι) : Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d) (e i) = d i • e i := by
  simpa using (hasEigenvector_toLin_diagonal d i e.toBasis).apply_eq_smul

/-- **Singular values of a diagonal operator.** If `π` lists the indices so that the norms
`‖d (π k)‖` are nonincreasing, then the `k`-th singular value of the diagonal operator with entries
`d` in an orthonormal basis is `‖d (π k)‖`. The singular values from `Fintype.card ι` on vanish
(`LinearMap.singularValues_of_finrank_le`). -/
theorem _root_.Matrix.singularValues_toLin_diagonal (e : OrthonormalBasis ι 𝕜 E) (d : ι → 𝕜)
    {n : ℕ} (π : Fin n ≃ ι) (hπ : Antitone fun k ↦ ‖d (π k)‖) (k : Fin n) :
    (Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)).singularValues k = ‖d (π k)‖ := by
  set D := Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal d)
  have hn : finrank 𝕜 E = n := by
    rw [finrank_eq_card_basis e.toBasis, Fintype.card_congr π.symm, Fintype.card_fin]
  have hDadj : adjoint D = Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal (star d)) := by
    rw [← Matrix.toLin_conjTranspose, Matrix.diagonal_conjTranspose]
  -- The reindexed basis `e ∘ π` diagonalizes `D† D` with the nonincreasing entries `‖d (π k)‖²`,
  -- so these are the sorted eigenvalues of `D† D`.
  have hGram (k : Fin n) : (adjoint D ∘ₗ D) ((e.reindex π.symm) k) =
      ((‖d (π k)‖ ^ 2 : ℝ) : 𝕜) • (e.reindex π.symm) k := by
    simp [D, hDadj, smul_smul, RCLike.mul_conj]
  have heig := D.isSymmetric_adjoint_comp_self.eigenvalues_eq_of_eigenbasis hn (e.reindex π.symm)
    (fun i j hij ↦ pow_le_pow_left₀ (norm_nonneg _) (hπ hij) 2) hGram
  rw [← sq_eq_sq₀ (D.singularValues_nonneg _) (norm_nonneg _), D.sq_singularValues_fin hn k, heig]

/-- **Rectangular singular-value factorization.** Every linear map `A : E →ₗ[𝕜] F` between
finite-dimensional inner product spaces factors as `A = U D V`, where `U` and `V` are linear
isometric equivalences of `F` and `E`, and `D` is the rectangular diagonal map whose matrix in
prescribed orthonormal bases `(eᵢ)` of `E` and `(fⱼ)` of `F` has the singular values of `A` on its
diagonal: `D eᵢ = σᵢ fᵢ` when `i` is also an index of `(fⱼ)`, and `D eᵢ = 0` otherwise. -/
theorem exists_linearIsometryEquiv_eq_comp_toLin_comp (A : E →ₗ[𝕜] F) {m n : ℕ}
    (e : OrthonormalBasis (Fin m) 𝕜 E) (f : OrthonormalBasis (Fin n) 𝕜 F) :
    ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), A = (U : F →ₗ[𝕜] F) ∘ₗ
      Matrix.toLin e.toBasis f.toBasis
        (Matrix.of fun j i ↦ if (j : ℕ) = i then (A.singularValues i : 𝕜) else 0) ∘ₗ
        (V : E →ₗ[𝕜] E) := by
  have hm : finrank 𝕜 E = m := by rw [finrank_eq_card_basis e.toBasis, Fintype.card_fin]
  have hn : finrank 𝕜 F = n := by rw [finrank_eq_card_basis f.toBasis, Fintype.card_fin]
  subst hm hn
  -- `V` sends the right singular basis `(vᵢ)` to `(eᵢ)`, and `U` sends `(fⱼ)` to an orthonormal
  -- basis `(wⱼ)` extending the left singular vectors, so both sides send `vᵢ` to `σᵢ wᵢ`, read
  -- as `0` when `i` is not an index of `(wⱼ)`.
  obtain ⟨w, hw⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  refine ⟨f.equiv w (.refl _), A.rightSingularBasis.equiv e (.refl _), ?_⟩
  refine A.rightSingularBasis.toBasis.ext fun i ↦ ?_
  simp only [coe_comp, Function.comp_apply, OrthonormalBasis.coe_toBasis, apply_rightSingularBasis,
    LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, OrthonormalBasis.equiv_apply_basis,
    Equiv.refl_apply]
  rw [← e.coe_toBasis, Matrix.toLin_self]
  simp only [Matrix.of_apply]
  rcases lt_or_ge (i : ℕ) (finrank 𝕜 F) with hi | hi
  · rw [Finset.sum_eq_single ⟨i, hi⟩
      (fun j _ hj ↦ by simp [show (j : ℕ) ≠ i from fun h ↦ hj (Fin.ext h)]) (by simp)]
    rcases eq_or_ne (A.singularValues i) 0 with hσ | hσ
    · simp [hσ]
    · simp [hw i ⟨i, hi⟩ rfl hσ]
  · simp [A.singularValues_of_finrank_le_right hi]

/-- **Singular-value diagonal factorization.** Every endomorphism `A` of a finite-dimensional
inner product space factors as `A = U D V`, where `U` and `V` are linear isometric equivalences
and `D` is the diagonal operator whose entries in a prescribed orthonormal basis `(eᵢ)` are the
singular values of `A`. -/
theorem exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp (A : E →ₗ[𝕜] E) {n : ℕ}
    (e : OrthonormalBasis (Fin n) 𝕜 E) :
    ∃ U V : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ
      Matrix.toLin e.toBasis e.toBasis (Matrix.diagonal fun i ↦ (A.singularValues i : 𝕜)) ∘ₗ
        (V : E →ₗ[𝕜] E) := by
  have hD : (Matrix.diagonal fun i : Fin n ↦ (A.singularValues i : 𝕜)) =
      Matrix.of fun j i : Fin n ↦ if (j : ℕ) = i then (A.singularValues i : 𝕜) else 0 := by
    ext j i
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [h, Fin.val_ne_of_ne h]
  rw [hD]
  exact A.exists_linearIsometryEquiv_eq_comp_toLin_comp e e

/-- **Compact singular value decomposition.** With `p = min (dim E) (dim F)`, every map
`A : E →ₗ[𝕜] F` is `∑_{i < p} σᵢ wᵢ ⊗ vᵢ` for orthonormal families `(vᵢ)` in `E` and `(wᵢ)` in
`F`, where `u ⊗ v` is the rank-one map `x ↦ ⟪v, x⟫ u`. Unlike
`LinearMap.eq_sum_singularValues_smul_rankOne`, both families are orthonormal, including at the
indices where `σᵢ = 0`. -/
theorem exists_orthonormal_eq_sum_singularValues_smul_rankOne (A : E →ₗ[𝕜] F) :
    ∃ (v : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → E)
      (w : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → F), Orthonormal 𝕜 v ∧ Orthonormal 𝕜 w ∧
        A = ∑ i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)), ((A.singularValues i : ℝ) : 𝕜) •
          (InnerProductSpace.rankOne 𝕜 (w i) (v i)).toLinearMap := by
  let e := stdOrthonormalBasis 𝕜 E
  let f := stdOrthonormalBasis 𝕜 F
  obtain ⟨U, V, hA⟩ := A.exists_linearIsometryEquiv_eq_comp_toLin_comp e f
  let iE : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → Fin (finrank 𝕜 E) :=
    Fin.castLE (min_le_left _ _)
  let iF : Fin (min (finrank 𝕜 E) (finrank 𝕜 F)) → Fin (finrank 𝕜 F) :=
    Fin.castLE (min_le_right _ _)
  refine ⟨V.symm ∘ e ∘ iE, U ∘ f ∘ iF,
    (e.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv _,
    (f.orthonormal.comp _ (Fin.castLE_injective _)).comp_linearIsometryEquiv _, ?_⟩
  -- Compare both sides on the orthonormal basis `(V⁻¹ eₖ)`: each sends `V⁻¹ eₖ` to `σₖ U fₖ`,
  -- read as `0` when `k` is not an index of `(fⱼ)`.
  refine (e.map V.symm).toBasis.ext fun k ↦ ?_
  conv_lhs => rw [hA]
  simp only [OrthonormalBasis.toBasis_map, LinearIsometryEquiv.toLinearEquiv_symm,
    Basis.map_apply, OrthonormalBasis.coe_toBasis, LinearIsometryEquiv.coe_symm_toLinearEquiv,
    coe_comp, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_apply,
    LinearIsometryEquiv.apply_symm_apply, coe_sum, coe_smul, ContinuousLinearMap.coe_coe,
    Finset.sum_apply, Pi.smul_apply, InnerProductSpace.rankOne_apply,
    LinearIsometryEquiv.inner_map_map, orthonormal_iff_ite.mp e.orthonormal, ite_smul, one_smul,
    zero_smul, smul_ite, smul_zero]
  rw [← e.coe_toBasis, Matrix.toLin_self]
  simp only [Matrix.of_apply]
  have hiE (i : Fin (min (finrank 𝕜 E) (finrank 𝕜 F))) : iE i = k ↔ (i : ℕ) = k := Fin.ext_iff
  rcases lt_or_ge (k : ℕ) (finrank 𝕜 F) with hk | hk
  · rw [Finset.sum_eq_single ⟨k, hk⟩
        (fun j _ hj ↦ by simp [show (j : ℕ) ≠ k from fun h ↦ hj (Fin.ext h)]) (by simp),
      Finset.sum_eq_single ⟨k, lt_min k.2 hk⟩
        (fun i _ hi ↦ by simp [hiE, show (i : ℕ) ≠ k from fun h ↦ hi (Fin.ext h)]) (by simp)]
    simp [hiE, iF, f]
  · rw [Finset.sum_eq_zero fun j _ ↦ by simp [show (j : ℕ) ≠ k from fun h ↦ (h ▸ j.2).not_ge hk],
      Finset.sum_eq_zero fun i _ ↦ by
        simp [hiE, show (i : ℕ) ≠ k from fun h ↦ (h ▸ i.2).not_ge (min_le_right _ _ |>.trans hk)]]
    simp

end Diagonal

end LinearMap

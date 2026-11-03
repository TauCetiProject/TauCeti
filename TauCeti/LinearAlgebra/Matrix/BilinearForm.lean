/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# Bilinear forms attached to matrices

Mathlib's `Matrix.toBilin'` reads a square matrix `M` over a commutative semiring `R` as the
bilinear form `(x, y) ↦ xᵀ M y` on `n → R`. This file records facts about these forms that
Mathlib lacks. The identity matrix gives the standard form `∑ i, x i * y i`, which takes the value
`1` on every standard basis vector, so over a nontrivial `R` it is alternating only when the index
type is empty (over the trivial semiring `1 = 0` and every form is alternating). Since the identity
matrix is symmetric and invertible, the standard form over a nontrivial `R` is in every positive
dimension a nondegenerate symmetric form that is not alternating, the model for the orthonormal
normal form of such forms.

In the other direction, `LinearMap.BilinForm.toMatrix` reads a bilinear form in a basis as its
Gram matrix. For a nondegenerate form, the Gram matrix in the `B`-dual basis is the inverse
transpose of the Gram matrix in the original basis; for a symmetric form it is the inverse Gram
matrix, which is how the dual of a lattice is described in coordinates. Likewise, the
coordinates of a vector are recovered from its pairings with the basis vectors through the inverse
Gram matrix.

## Main results

* `Matrix.isAlt_toBilin'_one_iff`: for `R` nontrivial, the standard form on `n → R` is alternating
  exactly when `n` is empty.
* `LinearMap.BilinForm.toMatrix_dualBasis`: the Gram matrix of a nondegenerate form in a `B`-dual
  basis is the inverse transpose of its Gram matrix in the original basis.
* `LinearMap.BilinForm.det_toMatrix_dualBasis_mul_det_toMatrix`: the Gram determinants of a
  nondegenerate form in a basis and in its `B`-dual basis are inverse to each other.
* `LinearMap.BilinForm.Nondegenerate.repr_eq_sum_inv_toMatrix₂_mul_apply`: the coordinates of a
  vector in a basis are its pairings with the basis, contracted against the inverse Gram matrix.
* `LinearMap.BilinForm.separatingLeft_of_toMatrix_mul_eq_smul`: over a domain, a form whose Gram
  matrix has a right inverse up to a nonzero scalar is nondegenerate.
* `LinearMap.BilinForm.toMatrix_collectedBasis`: the Gram matrix of a form in a basis collected
  from a pairwise orthogonal internal direct sum is block diagonal, with the Gram matrices of the
  summands as blocks.
* `LinearMap.BilinForm.exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal`: Gram matrices
  of two forms on the summands of an orthogonal internal direct sum that multiply to `c • 1` give
  Gram matrices on the whole module with the same product; the same holds for the restrictions to
  the supremum of finitely many independent submodules
  (`LinearMap.BilinForm.exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul`).
* `LinearMap.BilinForm.equivalent_iff_equivalent_of_toMatrix_mul_eq_smul`: if the Gram matrices of
  `B` and `D` in some basis multiply to `c • 1`, for a non-zero-divisor `c`, then `D` is determined
  up to isometry by `B` and conversely: such pairs `(B₁, D₁)` and `(B₂, D₂)` have `B₁ ≅ B₂` exactly
  when `D₁ ≅ D₂`. On a lattice `D` is the form `c B⁻¹`, read on the dual lattice, so this compares
  isometry classes of lattices with those of their `c`-scaled duals.
-/

public section

universe u

namespace Matrix

/-- Over a nontrivial commutative semiring `R`, the standard form `∑ i, x i * y i` on `n → R` is
alternating only when `n` is empty: it takes the value `1 ≠ 0` on every standard basis vector. -/
@[simp]
theorem isAlt_toBilin'_one_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [Nontrivial R] : (toBilin' (1 : Matrix n n R)).IsAlt ↔ IsEmpty n := by
  refine ⟨fun h => ⟨fun i => by simpa using h (Pi.single i 1)⟩, fun hn x => ?_⟩
  simp [Subsingleton.elim x 0]

end Matrix

namespace LinearMap.BilinForm

open Matrix Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of a nondegenerate bilinear form in the `B`-dual basis of `b` is the inverse of
the transpose of its Gram matrix in `b`. For a symmetric form this is the inverse Gram matrix. -/
theorem toMatrix_dualBasis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    toMatrix (B.dualBasis hB b) B = (toMatrix b B)ᵀ⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  ext i j
  calc (toMatrix (B.dualBasis hB b) B * (toMatrix b B)ᵀ) i j
      = B (B.dualBasis hB b i)
          (∑ k, (B.dualBasis hB b).repr (b j) k • B.dualBasis hB b k) := by
        simp [Matrix.mul_apply, toMatrix_apply, dualBasis_repr_apply, mul_comm]
    _ = (1 : Matrix ι ι K) i j := by
        rw [(B.dualBasis hB b).sum_repr, apply_dualBasis_left, Matrix.one_apply]
        simp only [eq_comm]

/-- The Gram determinants of a nondegenerate bilinear form in a basis and in its `B`-dual basis
are inverse to each other. -/
theorem det_toMatrix_dualBasis_mul_det_toMatrix (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (b : Basis ι K V) : (toMatrix (B.dualBasis hB b) B).det * (toMatrix b B).det = 1 := by
  rw [toMatrix_dualBasis, det_nonsing_inv, det_transpose,
    Ring.inverse_mul_cancel _ (isUnit_iff_ne_zero.mpr ((nondegenerate_iff_det_ne_zero b).mp hB))]

/-- **Coordinates from pairings.** For a nondegenerate bilinear form `B` and a basis `b`, the
`k`-th coordinate of a vector `v` is `Σ_l B^(kl) B(b l, v)`, where `B^(kl)` is the inverse of the
Gram matrix `B_ij = B(b i, b j)`. -/
theorem Nondegenerate.repr_eq_sum_inv_toMatrix₂_mul_apply {B : LinearMap.BilinForm K V}
    (hB : B.Nondegenerate) (b : Basis ι K V) (v : V) (k : ι) :
    b.repr v k = ∑ l, (LinearMap.toMatrix₂ b b B)⁻¹ k l * B (b l) v := by
  set G := LinearMap.toMatrix₂ b b B
  -- The coordinate vector `c` of `v` satisfies `G c = r`, with `r` the pairings `B(b l, v)`.
  set c : ι → K := fun k ↦ b.repr v k
  set r : ι → K := fun l ↦ B (b l) v
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.2 ((LinearMap.nondegenerate_iff_det_ne_zero b).1 hB)
  have hGc : G *ᵥ c = r := by
    ext l
    conv_rhs => simp only [r]; rw [← b.sum_repr v]
    simp only [Matrix.mulVec, dotProduct, G, LinearMap.toMatrix₂_apply, c, map_sum, map_smul,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ ↦ mul_comm _ _
  have hc : c = G⁻¹ *ᵥ r := by
    rw [← hGc, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG, Matrix.one_mulVec]
  exact congrFun hc k

section Domain

variable {R M n : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] [Fintype n]
  [DecidableEq n]

/-- A bilinear form whose Gram matrix in some basis, times some matrix, is a nonzero scalar matrix
is nondegenerate: its Gram determinant divides a power of a nonzero element of a domain. -/
theorem separatingLeft_of_toMatrix_mul_eq_smul {B : LinearMap.BilinForm R M} (b : Basis n R M)
    {H : Matrix n n R} {c : R} (hc : c ≠ 0) (hH : B.toMatrix b * H = c • 1) : B.SeparatingLeft := by
  refine ((nondegenerate_iff_det_ne_zero b).mpr fun h ↦ ?_).1
  have := congrArg Matrix.det hH
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

end Domain

section CollectedBasis

open LinearMap (BilinForm)

variable {R : Type*} [CommSemiring R]

/-- **The Gram matrix of an orthogonal sum.** If `M` is the internal direct sum of submodules
`P i` which are pairwise orthogonal for `B`, the Gram matrix of `B` in the basis collected from
bases `d i` of the `P i` is block diagonal, with blocks the Gram matrices of the restrictions of
`B` to the `P i`. -/
theorem toMatrix_collectedBasis {M o : Type*} [AddCommMonoid M] [Module R M] [Fintype o]
    [DecidableEq o] {B : BilinForm R M} {P : o → Submodule R M} (hP : DirectSum.IsInternal P)
    (horth : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', B x y = 0) {α : o → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] (d : ∀ i, Basis (α i) R (P i)) :
    B.toMatrix (hP.collectedBasis d) =
      Matrix.blockDiagonal' fun i ↦ (B.restrict (P i)).toMatrix (d i) := by
  ext ⟨i, a⟩ ⟨i', a'⟩
  rw [toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
  by_cases hii : i = i'
  · subst hii
    simp [Matrix.blockDiagonal'_apply_eq, toMatrix_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hii]
    exact horth _ _ hii _ (d i a).2 _ (d i' a').2

/-- If two forms are pairwise orthogonal across a family of submodules `P i` of which `M` is the
internal direct sum, and their Gram matrices in bases `d i` of the `P i` multiply to `c • 1`, then
so do their Gram matrices in the collected basis. -/
theorem toMatrix_collectedBasis_mul_toMatrix_collectedBasis {M o : Type*} [AddCommMonoid M]
    [Module R M] [Fintype o] [DecidableEq o] {B D : BilinForm R M} {P : o → Submodule R M}
    (hP : DirectSum.IsInternal P) (hB : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ P i, ∀ y ∈ P i', D x y = 0) {α : o → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] (d : ∀ i, Basis (α i) R (P i)) {c : R}
    (hd : ∀ i, (B.restrict (P i)).toMatrix (d i) * (D.restrict (P i)).toMatrix (d i) = c • 1) :
    B.toMatrix (hP.collectedBasis d) * D.toMatrix (hP.collectedBasis d) = c • 1 := by
  rw [toMatrix_collectedBasis hP hB, toMatrix_collectedBasis hP hD, ← Matrix.blockDiagonal'_mul]
  simp only [hd]
  have := Matrix.blockDiagonal'_smul c (1 : ∀ i, Matrix (α i) (α i) R)
  rwa [Matrix.blockDiagonal'_one] at this

end CollectedBasis

section Dual

open LinearMap (BilinForm)

variable {R M₁ M₂ ι κ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- If two forms are pairwise orthogonal across a family of submodules `N i` of which `M` is the
internal direct sum, finitely many of them nonzero, and their Gram matrices in some basis of each
nonzero `N i` multiply to `c • 1`, then so do their Gram matrices in some basis of `M`. -/
theorem exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal {M : Type*} {o : Type u}
    [AddCommGroup M] [Module R M] [DecidableEq o] {B D : BilinForm R M} {N : o → Submodule R M}
    (hN : DirectSum.IsInternal N) (hfin : {i | N i ≠ ⊥}.Finite)
    (hB : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', D x y = 0) {c : R}
    (hd : ∀ i, N i ≠ ⊥ → ∃ (α : Type u) (_ : Fintype α) (_ : DecidableEq α) (d : Basis α R (N i)),
      (B.restrict (N i)).toMatrix d * (D.restrict (N i)).toMatrix d = c • 1) :
    ∃ (β : Type u) (_ : Fintype β) (_ : DecidableEq β) (b : Basis β R M),
      B.toMatrix b * D.toMatrix b = c • 1 := by
  have : Finite {i // N i ≠ ⊥} := hfin.to_subtype
  have : Fintype {i // N i ≠ ⊥} := Fintype.ofFinite _
  choose α _ _ d hd using fun i : {i // N i ≠ ⊥} ↦ hd i i.2
  have hP : DirectSum.IsInternal fun i : {i // N i ≠ ⊥} ↦ N i :=
    DirectSum.isInternal_ne_bot_iff.mpr hN
  refine ⟨_, inferInstance, inferInstance, hP.collectedBasis d,
    toMatrix_collectedBasis_mul_toMatrix_collectedBasis hP ?_ ?_ d hd⟩
  · exact fun i i' hii ↦ hB i i' fun h ↦ hii (Subtype.ext h)
  · exact fun i i' hii ↦ hD i i' fun h ↦ hii (Subtype.ext h)

/-- The version of `exists_basis_toMatrix_mul_toMatrix_eq_smul_of_isInternal` for the
restrictions of the forms to the supremum of finitely many members `N i`, `i ∈ s`, of an
independent family of submodules. -/
theorem exists_basis_restrict_biSup_toMatrix_mul_toMatrix_eq_smul {M : Type*} {o : Type u}
    [AddCommGroup M] [Module R M] {B D : BilinForm R M} {N : o → Submodule R M}
    (hN : iSupIndep N) (hB : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', B x y = 0)
    (hD : ∀ i i', i ≠ i' → ∀ x ∈ N i, ∀ y ∈ N i', D x y = 0) {s : Set o} (hs : s.Finite) {c : R}
    (hd : ∀ i ∈ s, ∃ (α : Type u) (_ : Fintype α) (_ : DecidableEq α) (d : Basis α R (N i)),
      (B.restrict (N i)).toMatrix d * (D.restrict (N i)).toMatrix d = c • 1) :
    ∃ (β : Type u) (_ : Fintype β) (_ : DecidableEq β) (b : Basis β R ↥(⨆ i ∈ s, N i)),
      (B.restrict (⨆ i ∈ s, N i)).toMatrix b * (D.restrict (⨆ i ∈ s, N i)).toMatrix b =
        c • 1 := by
  classical
  have : Fintype s := hs.fintype
  choose α _ _ d hd using fun i : s ↦ hd i i.2
  set A := ⨆ i ∈ s, N i
  have hle (i : s) : N i ≤ A := le_biSup N i.2
  -- Transport the bases of the `N i` into `A`.
  let d' (i : s) : Basis (α i) R ((N i).comap A.subtype) :=
    (d i).map (Submodule.comapSubtypeEquivOfLe (hle i)).symm
  have hgram (F : BilinForm R M) (i : s) :
      ((F.restrict A).restrict ((N i).comap A.subtype)).toMatrix (d' i) =
        (F.restrict (N i)).toMatrix (d i) := by
    ext a a'
    simp only [toMatrix_apply, restrict_apply, LinearMap.domRestrict_apply, d', Basis.map_apply,
      Submodule.comapSubtypeEquivOfLe_symm_apply]
  have hP := DirectSum.isInternal_biSup_submodule_of_iSupIndep s (hN.comp Subtype.val_injective)
  refine ⟨_, inferInstance, inferInstance, hP.collectedBasis d',
    toMatrix_collectedBasis_mul_toMatrix_collectedBasis hP ?_ ?_ d' fun i ↦ ?_⟩
  · exact fun i i' hii x hx y hy ↦ hB i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy
  · exact fun i i' hii x hx y hy ↦ hD i i' (fun h ↦ hii (Subtype.ext h)) _ hx _ hy
  · rw [hgram, hgram]
    exact hd i

/-- One direction of `LinearMap.BilinForm.equivalent_iff_equivalent_of_toMatrix_mul_eq_smul`. If
`e` is an isometry with matrix `P`, the contragredient map, with matrix the inverse transpose of
`P`, carries `D₁` to `D₂`. -/
private theorem Equivalent.of_toMatrix_mul_eq_smul {B₁ D₁ : BilinForm R M₁}
    {B₂ D₂ : BilinForm R M₂} (b₁ : Basis ι R M₁) (b₂ : Basis κ R M₂) {c : R}
    (hc : c ∈ nonZeroDivisors R) (h₁ : B₁.toMatrix b₁ * D₁.toMatrix b₁ = c • 1)
    (h₂ : B₂.toMatrix b₂ * D₂.toMatrix b₂ = c • 1) (h : B₁.Equivalent B₂) : D₁.Equivalent D₂ := by
  obtain ⟨e⟩ := h
  set P := LinearMap.toMatrix b₁ b₂ e.toLinearEquiv.toLinearMap
  set P' := LinearMap.toMatrix b₂ b₁ e.toLinearEquiv.symm.toLinearMap
  have hP'P : P' * P = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp
  have hPP' : P * P' = 1 := by
    rw [← LinearMap.toMatrix_comp]
    simp
  have hG : B₁.toMatrix b₁ = Pᵀ * B₂.toMatrix b₂ * P := by
    rw [← toMatrix_comp]
    congr 1
    ext x y
    simp [e.map_app]
  -- The candidate Gram matrix `P' * H₂ * P'ᵀ` of `D₂` pulled back is `D₁`'s, after cancelling `c`.
  have hX : P' * D₂.toMatrix b₂ * P'ᵀ = D₁.toMatrix b₁ := by
    have hHG := (Matrix.mul_eq_smul_one_comm hc).mp h₁
    have key : c • (P' * D₂.toMatrix b₂ * P'ᵀ) = c • D₁.toMatrix b₁ := by
      calc c • (P' * D₂.toMatrix b₂ * P'ᵀ)
          = D₁.toMatrix b₁ * B₁.toMatrix b₁ * (P' * D₂.toMatrix b₂ * P'ᵀ) := by
            rw [hHG, Matrix.smul_mul, Matrix.one_mul]
        _ = D₁.toMatrix b₁ * Pᵀ * (B₂.toMatrix b₂ * D₂.toMatrix b₂) * P'ᵀ := by
            rw [hG]
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc P P', hPP', Matrix.one_mul]
        _ = c • D₁.toMatrix b₁ := by
            rw [h₂, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc,
              ← Matrix.transpose_mul, hP'P, Matrix.transpose_one, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun key i) j
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_cancel_left_mem_nonZeroDivisors hc] at this
  let f : M₁ ≃ₗ[R] M₂ := LinearEquiv.ofLinearMap (Matrix.toLin b₁ b₂ P'ᵀ) (Matrix.toLin b₂ b₁ Pᵀ)
    (by rw [← Matrix.toLin_mul, ← Matrix.transpose_mul, hPP', Matrix.transpose_one,
      Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul, ← Matrix.transpose_mul, hP'P, Matrix.transpose_one,
      Matrix.toLin_one])
  have hf : D₂.comp f.toLinearMap f.toLinearMap = D₁ := by
    refine (toMatrix b₁).injective ?_
    rw [toMatrix_comp b₂, LinearEquiv.toLinearMap_ofLinearMap, LinearMap.toMatrix_toLin,
      Matrix.transpose_transpose, hX]
  exact ⟨{ toLinearEquiv := f, map_app' := fun x y ↦ by simpa using LinearMap.congr_fun₂ hf x y }⟩

/-- **Isometry classes of forms and of their scaled duals.** Let `c` be a non-zero-divisor, and
let `B₁, D₁` and `B₂, D₂` be bilinear forms whose Gram matrices in bases `b₁` and `b₂` multiply to
`c • 1`. Then `B₁` and `B₂` are isometric exactly when `D₁` and `D₂` are. On a lattice, `D` is
the form `c B⁻¹` transported from the dual lattice, so the isometry class of a nondegenerate form
determines that of its `c`-scaled dual and conversely. -/
theorem equivalent_iff_equivalent_of_toMatrix_mul_eq_smul {B₁ D₁ : BilinForm R M₁}
    {B₂ D₂ : BilinForm R M₂} (b₁ : Basis ι R M₁) (b₂ : Basis κ R M₂) {c : R}
    (hc : c ∈ nonZeroDivisors R) (h₁ : B₁.toMatrix b₁ * D₁.toMatrix b₁ = c • 1)
    (h₂ : B₂.toMatrix b₂ * D₂.toMatrix b₂ = c • 1) : B₁.Equivalent B₂ ↔ D₁.Equivalent D₂ :=
  ⟨Equivalent.of_toMatrix_mul_eq_smul b₁ b₂ hc h₁ h₂,
    Equivalent.of_toMatrix_mul_eq_smul b₁ b₂ hc ((Matrix.mul_eq_smul_one_comm hc).mp h₁)
      ((Matrix.mul_eq_smul_one_comm hc).mp h₂)⟩

end Dual

end LinearMap.BilinForm

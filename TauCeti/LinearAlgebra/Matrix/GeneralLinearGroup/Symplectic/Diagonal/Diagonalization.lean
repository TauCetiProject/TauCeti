/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic

/-!
# Diagonalizing symplectic matrices by symplectic matrices

Let `k` be a field and `Q` a commutative `k`-algebra. Suppose a symplectic matrix `M` over `Q` is
diagonalized by an invertible matrix `P₀` over `k`, with unit eigenvalues: `M P₀ = P₀ diag(t)`.
Then `M` is already diagonalized by a *symplectic* matrix `P` over `k`, and the eigenvalues can be
taken paired, `M P = P diag(u₁, …, uₘ, u₁⁻¹, …, uₘ⁻¹)`: a conjugate of `M` by a rational symplectic
matrix lies in the paired diagonal torus.

The proof sorts rational vectors by eigenvalue. For a unit `s` of `Q`, the `s`-eigenspace is the
`k`-subspace of vectors `v` with `M v = s v` after extending scalars. The columns of `P₀` show that
these subspaces span `k²ᵐ`. Since `M` preserves the standard alternating form `J`, a vector of the
`s`-eigenspace and a vector of the `r`-eigenspace pair to `vᵀ J w = s r · vᵀ J w`, so they are
orthogonal unless `r = s⁻¹`. The graded symplectic basis theorem
`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top` then supplies a symplectic
basis of eigenvectors; its matrix is `P`, and each hyperbolic pair of basis vectors carries
mutually inverse eigenvalues.

This is the linear algebra that conjugates a diagonalizable subgroup of `Sp₂ₘ` into the paired
diagonal torus, with `Q` the coordinate ring of the subgroup and `M` its generic point.

## Main declarations

* `Matrix.exists_mem_symplecticGroup_mul_map_eq_map_mul_diagonal`: the statement in Mathlib's
  `Fin m ⊕ Fin m` coordinates.
* `TauCeti.GLSymplecticFin.exists_mul_map_eq_map_mul_diagonal`: the statement for
  `TauCeti.GLSymplecticFin`, with the paired diagonal matrix `TauCeti.GLSymplecticFin.diagonal`.

## References

* E. Artin, *Geometric Algebra* (1957), Theorem 3.7, for symplectic bases; the graded form used
  here is `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_of_iSup_eq_top`.
-/

public section

open Matrix

namespace Matrix

variable {k Q : Type*} [Field k] [CommRing Q] [Algebra k Q]

/-- The `k`-subspace of rational vectors which the matrix `M` over `Q` scales by `s`. -/
private def rationalEigenspace {n : Type*} [Fintype n] (M : Matrix n n Q) (s : Qˣ) :
    Submodule k (n → k) :=
  LinearMap.ker (((M.mulVecLin - (s : Q) • LinearMap.id).restrictScalars k) ∘ₗ
    LinearMap.compLeft (Algebra.linearMap k Q) n)

private theorem mem_rationalEigenspace {n : Type*} [Fintype n] {M : Matrix n n Q} {s : Qˣ}
    {v : n → k} :
    v ∈ rationalEigenspace (k := k) M s ↔
      M *ᵥ (algebraMap k Q ∘ v) = (s : Q) • (algebraMap k Q ∘ v) := by
  simp [rationalEigenspace, sub_eq_zero, LinearMap.compLeft, Function.comp_def]

/-- If `P₀` diagonalizes `M` with unit eigenvalues, the rational eigenspaces of `M` span, since
they contain the columns of `P₀`. -/
private theorem iSup_rationalEigenspace_eq_top {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n Q} {P₀ : Matrix n n k} (hP₀ : IsUnit P₀) {t : n → Qˣ}
    (h : M * P₀.map (algebraMap k Q) = P₀.map (algebraMap k Q) * diagonal fun i ↦ (t i : Q)) :
    ⨆ s, rationalEigenspace (k := k) M s = ⊤ := by
  have hcol (j : n) : P₀.col j ∈ rationalEigenspace (k := k) M (t j) := by
    rw [mem_rationalEigenspace]
    funext i
    have hij := congr_fun (congr_fun h i) j
    rw [mul_diagonal, mul_apply] at hij
    simp only [map_apply] at hij
    simp only [mulVec, dotProduct, Function.comp_apply, col_apply, Pi.smul_apply, smul_eq_mul,
      hij, mul_comm]
  have hspan : Submodule.span k (Set.range P₀.col) = ⊤ := by
    rw [← range_mulVecLin, LinearMap.range_eq_top]
    exact mulVec_surjective_iff_isUnit.2 hP₀
  refine eq_top_iff.2 (hspan ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨j, rfl⟩
  exact Submodule.mem_iSup_of_mem (t j) (hcol j)

variable {m : ℕ}

/-- Eigenvectors of a symplectic matrix are orthogonal for the standard alternating form unless
their eigenvalues are mutually inverse. -/
private theorem stdSymplecticBilinForm_eq_zero_of_mem_rationalEigenspace
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Q} (hM : Mᵀ * J (Fin m) Q * M = J (Fin m) Q)
    {s r : Qˣ} (hsr : r ≠ s⁻¹) {v w : Fin m ⊕ Fin m → k}
    (hv : v ∈ rationalEigenspace (k := k) M s) (hw : w ∈ rationalEigenspace (k := k) M r) :
    TauCeti.stdSymplecticBilinForm k m v w = 0 := by
  rw [mem_rationalEigenspace] at hv hw
  rw [TauCeti.stdSymplecticBilinForm_apply]
  set φ := algebraMap k Q
  have key : φ (v ⬝ᵥ J (Fin m) k *ᵥ w) = ((s * r : Qˣ) : Q) * φ (v ⬝ᵥ J (Fin m) k *ᵥ w) := by
    have hφ : φ (v ⬝ᵥ J (Fin m) k *ᵥ w) = (φ ∘ v) ⬝ᵥ J (Fin m) Q *ᵥ (φ ∘ w) := by
      rw [RingHom.map_dotProduct]
      congr 1
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, map_J]
    calc φ (v ⬝ᵥ J (Fin m) k *ᵥ w)
        = (φ ∘ v) ⬝ᵥ (Mᵀ * J (Fin m) Q * M) *ᵥ (φ ∘ w) := by rw [hφ, hM]
      _ = (M *ᵥ (φ ∘ v)) ⬝ᵥ J (Fin m) Q *ᵥ (M *ᵥ (φ ∘ w)) := by
        rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
      _ = ((s * r : Qˣ) : Q) * φ (v ⬝ᵥ J (Fin m) k *ᵥ w) := by
        rw [hv, hw, mulVec_smul, smul_dotProduct, dotProduct_smul, hφ, smul_eq_mul, smul_eq_mul,
          Units.val_mul]
        ring
  by_contra hne
  have hunit : IsUnit (φ (v ⬝ᵥ J (Fin m) k *ᵥ w)) := (IsUnit.mk0 _ hne).map φ
  have hone : s * r = 1 := by
    apply Units.ext
    rw [Units.val_one]
    exact hunit.mul_right_cancel (by rw [one_mul]; exact key.symm)
  exact hsr (eq_inv_of_mul_eq_one_right hone)

/-- **A symplectic matrix diagonalized by a rational matrix is diagonalized by a rational
symplectic matrix**, in Mathlib's `Fin m ⊕ Fin m` coordinates.

If `M ∈ Sp₂ₘ(Q)` satisfies `M P₀ = P₀ diag(t)` for an invertible `P₀` over `k` and units `t` of
`Q`, then `M P = P diag(u, u⁻¹)` for some symplectic `P` over `k` and units `u` of `Q`. -/
theorem exists_mem_symplecticGroup_mul_map_eq_map_mul_diagonal
    {M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) Q} (hM : M ∈ symplecticGroup (Fin m) Q)
    {P₀ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k} (hP₀ : IsUnit P₀)
    {t : Fin m ⊕ Fin m → Qˣ}
    (h : M * P₀.map (algebraMap k Q) = P₀.map (algebraMap k Q) * diagonal fun i ↦ (t i : Q)) :
    ∃ P ∈ symplecticGroup (Fin m) k, ∃ u : Fin m → Qˣ,
      M * P.map (algebraMap k Q) =
        P.map (algebraMap k Q) *
          diagonal fun x ↦ ((Sum.elim u (fun i ↦ (u i)⁻¹) x : Qˣ) : Q) := by
  classical
  have hM' := SymplecticGroup.mem_iff'.1 hM
  have hW := iSup_rationalEigenspace_eq_top hP₀ h
  -- A homogeneous symplectic basis.
  obtain ⟨m', b, hb, hbW⟩ :=
    (TauCeti.isAlt_stdSymplecticBilinForm k m).exists_basis_toMatrix_eq_J_of_iSup_eq_top
      (TauCeti.stdSymplecticBilinForm_nondegenerate k m) (W := rationalEigenspace M)
      (σ := fun s ↦ s⁻¹) inv_involutive hW fun s r hsr v hv w hw ↦
        stdSymplecticBilinForm_eq_zero_of_mem_rationalEigenspace hM' hsr hv hw
  obtain rfl : m = m' := by
    have hcard := (Module.finrank_eq_card_basis b).symm.trans
      (Module.finrank_fintype_fun_eq_card k)
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  choose s hs using hbW
  have hbB (x y : Fin m ⊕ Fin m) : TauCeti.stdSymplecticBilinForm k m (b x) (b y) =
      J (Fin m) k x y := by
    rw [← LinearMap.BilinForm.toMatrix_apply b, hb]
  -- Each hyperbolic pair of basis vectors carries mutually inverse eigenvalues.
  have hpair (i : Fin m) : s (Sum.inr i) = (s (Sum.inl i))⁻¹ := by
    by_contra hne
    have h0 := stdSymplecticBilinForm_eq_zero_of_mem_rationalEigenspace hM' hne
      (hs (Sum.inl i)) (hs (Sum.inr i))
    rw [hbB] at h0
    simp [J] at h0
  refine ⟨(Pi.basisFun k _).toMatrix b, ?_, fun i ↦ s (Sum.inl i), ?_⟩
  · rw [SymplecticGroup.mem_iff']
    have hJ : LinearMap.BilinForm.toMatrix (Pi.basisFun k (Fin m ⊕ Fin m))
        (TauCeti.stdSymplecticBilinForm k m) = J (Fin m) k := by
      ext x y
      rw [LinearMap.BilinForm.toMatrix_apply, TauCeti.stdSymplecticBilinForm_apply]
      simp [Pi.basisFun_apply, mulVec_single, single_dotProduct]
    have hPJ := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun k _) b
      (TauCeti.stdSymplecticBilinForm k m)
    rwa [hJ, hb] at hPJ
  · ext i x
    have hx := congr_fun (mem_rationalEigenspace.1 (hs x)) i
    have hsx : (Sum.elim (fun i ↦ s (Sum.inl i)) (fun i ↦ (s (Sum.inl i))⁻¹) x : Qˣ) = s x := by
      rcases x with x | x
      · exact Sum.elim_inl _ _ x
      · exact (Sum.elim_inr _ _ x).trans (hpair x).symm
    rw [mul_diagonal, hsx, mul_apply, mul_comm]
    simpa [mulVec, dotProduct, Module.Basis.toMatrix_apply] using hx

end Matrix

namespace TauCeti.GLSymplecticFin

variable {k Q : Type*} [Field k] [CommRing Q] [Algebra k Q] {m : ℕ}

/-- **A symplectic matrix diagonalized by a rational matrix is diagonalized by a rational
symplectic matrix.**

If `M ∈ Sp₂ₘ(Q)` satisfies `M P₀ = P₀ diag(t)` for some `P₀ ∈ GL₂ₘ(k)` and units `t` of `Q`, then
some rational symplectic matrix `P` conjugates `M` into the paired diagonal torus:
`M P = P diag(u₁, …, uₘ, u₁⁻¹, …, uₘ⁻¹)`. -/
theorem exists_mul_map_eq_map_mul_diagonal (M : GLSymplecticFin m Q)
    {P₀ : GL (Fin (m + m)) k} {t : Fin (m + m) → Qˣ}
    (h : (M : GL (Fin (m + m)) Q) * GeneralLinearGroup.map (algebraMap k Q) P₀ =
      GeneralLinearGroup.map (algebraMap k Q) P₀ * diagGL t) :
    ∃ (P : GLSymplecticFin m k) (u : Fin m → Qˣ),
      M * map m k (algebraMap k Q) P = map m k (algebraMap k Q) P * diagonal u := by
  classical
  set e : Fin m ⊕ Fin m ≃ Fin (m + m) := finSumFinEquiv
  have hsub := congrArg (fun X : GL (Fin (m + m)) Q ↦ (X : Matrix _ _ Q).submatrix e e) h
  simp only [Units.val_mul, GeneralLinearGroup.val_map_apply, diagGL_coe,
    ← submatrix_mul_equiv _ _ _ e _, submatrix_map, submatrix_diagonal_equiv] at hsub
  have hP₀ : IsUnit ((P₀ : Matrix _ _ k).submatrix e e) := by
    rw [isUnit_iff_isUnit_det, det_submatrix_equiv_self, ← isUnit_iff_isUnit_det]
    exact P₀.isUnit
  obtain ⟨P', hP', u, hu⟩ := exists_mem_symplecticGroup_mul_map_eq_map_mul_diagonal
    (submatrix_mem_symplecticGroup (mem_iff.1 M.2)) hP₀ hsub
  let P : GLSymplecticFin m k := (mulEquivGLSymplectic m k).symm
    ((GLSymplectic.mulEquivSymplecticGroup (Fin m) k).symm ⟨P', hP'⟩)
  have hP : ((P : GL (Fin (m + m)) k) : Matrix _ _ k).submatrix e e = P' := by
    have h1 := congrArg
      (fun X : GL (Fin m ⊕ Fin m) k ↦ (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) k))
      (coe_mulEquivGLSymplectic m k P)
    simp only [P, MulEquiv.apply_symm_apply, Equiv.coe_reindexGL, Equiv.symm_symm] at h1
    rw [← h1, ← GLSymplectic.coe_mulEquivSymplecticGroup, MulEquiv.apply_symm_apply]
  refine ⟨P, u, Subtype.ext (Units.ext ?_)⟩
  apply (reindex e.symm e.symm).injective
  simp only [reindex_apply, Equiv.symm_symm, Subgroup.coe_mul, Units.val_mul, coe_map,
    GeneralLinearGroup.val_map_apply, coe_diagonal, diagGL_coe, ← submatrix_mul_equiv _ _ _ e _,
    submatrix_map, hP, submatrix_diagonal_equiv]
  rw [hu]
  congr 2
  funext x
  rcases x with x | x <;> simp [e]

end TauCeti.GLSymplecticFin

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.GaussSum
import TauCeti.LinearAlgebra.Matrix.Symmetric
import TauCeti.LinearAlgebra.Submodule.Compl

/-!
# The Gauss sum of the lower constituents of a Jordan splitting

Let `B` be a symmetric form on a finite free module `M` over a local ring, with a Jordan splitting
`N` with respect to `π`, where `2 ∣ π`. Reduce the Gram matrix `G` of the sum `L₍ⱼ₎` of the
constituents of index at most `j` along a ring homomorphism `f` to a finite ring `S` that kills
`2 π ^ (j + 1)`, and form the Gauss sum `∑_x ψ(xᵀ f(G) x)` for an additive character `ψ` of `S`.
If the constituent `N (j + 1)` is even at its own scale (of type II, possibly zero), this Gauss
sum is an isometry invariant of `B`, although `L₍ⱼ₎` is not
(`LinearMap.BilinForm.IsJordanSplitting.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent`).
Over `ℤ_[2]`, with `f` the reduction modulo `2 ^ (j + 2)` and `ψ` the standard character of
`ℤ/2 ^ (j + 2)`, this is the Gauss sum `∑_x e(xᵀ G x / 2 ^ (j + 2))` over `(ℤ/2 ^ (j + 2))ⁿ`.

This invariant sees the oddity, which the determinant of `L₍ⱼ₎` does not. Over `ℤ_[2]`, a unit `u`
has `∑_{x ∈ ℤ/4} e(u x² / 4) = 2 (1 + i ^ u)`, so the lower constituents `⟨1, 1⟩` and `⟨3, 3⟩` of
`⟨1, 1⟩ ⊥ 2 !![0, 1; 1, 0]` and `⟨3, 3⟩ ⊥ 2 !![0, 1; 1, 0]` have the Gauss sums `8i` and `-8i`
modulo `4`, while their determinants `1` and `9` are both squares. So these two lattices are not
isometric. On the other hand, the sign walking `⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`) changes the lower constituent from `⟨1⟩` to
`⟨5⟩`, and both have the Gauss sum `2 (1 + i)` modulo `4`. Conditions on the partial sums `L₍ⱼ₎`
beyond their determinants enter O'Meara's classification of lattices over dyadic local fields
(93:28), and this Gauss sum is such a condition for lattices over `ℤ_[2]`, complementing the
determinant condition of
`LinearMap.BilinForm.IsJordanSplitting.exists_sq_mul_det_toMatrix_eq_of_equivalent`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent`:
  if `N (j + 1)` is even at its own scale, then the Gauss sums of the sums of the constituents of
  index at most `j` of Jordan splittings of isometric forms agree.

## Implementation notes

In a basis of `M` adapted to the decomposition `M = L₍ⱼ₎ ⊕ U`, with `U` the sum of the
constituents of index above `j`, the Gram matrix of `B` is block diagonal, so its Gauss sum is the
product of the Gauss sums of `L₍ⱼ₎` and of `U`
(`Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec`). The Gram matrix of `U` is
`π ^ (j + 1) (D + Dᵀ)` for some `D`, because its entries are divisible by `π ^ (j + 1)` and its
diagonal by `2 π ^ (j + 1)`
(`LinearMap.BilinForm.IsJordanSplitting.two_mul_pow_succ_dvd_apply_self_of_mem_biSup`). So its
quadratic form vanishes modulo `2 π ^ (j + 1)`, and its Gauss sum is the number of vectors. The
Gauss sum of the Gram matrix of `B` does not depend on the basis
(`Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec`), and that of `U` is the same for both
splittings, because the ranks agree.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93, in particular 93:28.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {R M M' S T : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [CommRing S] [Fintype S] [CommRing T] {B : BilinForm R M}
  {N : ℕ → Submodule R M} {π : R}

/-- The Gauss sum of the Gram matrix of `B` in a basis adapted to the decomposition into the
constituents of index at most `j` and those above `j` is `#S ^ #κ` times the Gauss sum of the
constituents of index at most `j`, when `f` kills `2 π ^ (j + 1)` and `N (j + 1)` is even at its
own scale. -/
private theorem IsJordanSplitting.sum_addChar_toMatrix_map_prod (h : B.IsJordanSplitting π N)
    (hB : B.IsSymm) (h2 : 2 ∣ π) {j : ℕ} (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w)
    (f : R →+* S) (hf : f (2 * π ^ (j + 1)) = 0) (ψ : AddChar S T) {ι κ : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype κ] [DecidableEq κ] (b : Basis ι R ↥(⨆ i ∈ Set.Iic j, N i))
    (c : Basis κ R ↥(⨆ i ∈ Set.Ici (j + 1), N i)) :
    ∑ x : ι ⊕ κ → S, ψ (x ⬝ᵥ (B.toMatrix ((b.prod c).map
      (Submodule.prodEquivOfIsCompl _ _ (h.isCompl_biSup_Iic_biSup_Ici j)))).map f *ᵥ x) =
      (Fintype.card S : T) ^ Fintype.card κ *
        ∑ x : ι → S, ψ (x ⬝ᵥ ((B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b).map f *ᵥ x) := by
  have hdisj : Disjoint (Set.Iic j) (Set.Ici (j + 1)) :=
    Set.disjoint_left.mpr fun i hi hi' ↦ by simp_all; omega
  -- In the adapted basis the Gram matrix is block diagonal.
  have hblock : B.toMatrix ((b.prod c).map (Submodule.prodEquivOfIsCompl _ _
      (h.isCompl_biSup_Iic_biSup_Ici j))) =
      Matrix.fromBlocks ((B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b) 0 0
        ((B.restrict (⨆ i ∈ Set.Ici (j + 1), N i)).toMatrix c) := by
    ext (i | i) (k | k)
    · simp
    · simpa using B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj (b i).2 (c k).2
    · simpa using B.apply_eq_zero_of_mem_biSup h.apply_eq_zero hdisj.symm (c i).2 (b k).2
    · simp
  -- The quadratic form of the constituents above `j` vanishes after reduction along `f`.
  obtain ⟨D, hD⟩ := ((isSymm_toMatrix_iff_isSymm c).mpr
    (hB.restrict _)).exists_eq_smul_add_transpose (π ^ (j + 1))
    (fun k k' ↦ by simpa using h.pow_dvd_apply_of_mem_biSup (c k).2 (c k'))
    (fun k ↦ by simpa using h.two_mul_pow_succ_dvd_apply_self_of_mem_biSup h2 hnext (c k).2)
  have hU (y : κ → S) :
      y ⬝ᵥ ((B.restrict (⨆ i ∈ Set.Ici (j + 1), N i)).toMatrix c).map f *ᵥ y = 0 := by
    have hmap : ((B.restrict (⨆ i ∈ Set.Ici (j + 1), N i)).toMatrix c).map f =
        f (π ^ (j + 1)) • (D.map f + (D.map f)ᵀ) := by
      rw [hD]
      ext
      simp [mul_add]
    have htr : y ⬝ᵥ (D.map f)ᵀ *ᵥ y = y ⬝ᵥ D.map f *ᵥ y := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    rw [hmap, Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add, htr,
      smul_eq_mul, ← two_mul, ← mul_assoc]
    rw [map_mul, map_ofNat] at hf
    rw [mul_comm (f _), hf, zero_mul]
  rw [hblock, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero f),
    Matrix.map_zero _ (map_zero f), Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec,
    mul_comm]
  simp [hU]

/-- **The Gauss sum of the lower constituents of a Jordan splitting.** Let `R` be a local ring and
`π ∈ R` a non-zero-divisor with `2 ∣ π`, for instance `ℤ_[2]` with `π = 2`. Let `B` be a symmetric
form on a finite free module, isometric to a form `B'`, and let `N` and `N'` be Jordan splittings
of `B` and `B'` with respect to `π`. Suppose that `N (j + 1)` is even at its own scale (of type II,
possibly zero). Let `f : R →+* S` be a ring homomorphism to a finite ring that kills
`2 * π ^ (j + 1)`, and `ψ` an additive character of `S` with values in a domain of characteristic
zero. Then in any bases of the sums of the constituents of index at most `j` of the two
splittings, the Gram matrices `G` and `G'` have the same Gauss sum
`∑_x ψ(xᵀ f(G) x) = ∑_x ψ(xᵀ f(G') x)`.

Over `ℤ_[2]`, with `f` the reduction modulo `2 ^ (j + 2)`, this invariant detects the oddity:
`⟨1, 1⟩ ⊥ 2 !![0, 1; 1, 0]` and `⟨3, 3⟩ ⊥ 2 !![0, 1; 1, 0]` are not isometric, since `⟨1, 1⟩` and
`⟨3, 3⟩` have the Gauss sums `8i` and `-8i` modulo `4`. The parity hypothesis cannot be dropped:
`⟨1⟩ ⊥ ⟨2⟩ ≅ ⟨3⟩ ⊥ ⟨6⟩`, while `⟨1⟩` and `⟨3⟩` have the Gauss sums `2 (1 + i)` and `2 (1 - i)`
modulo `4`. -/
theorem IsJordanSplitting.sum_addChar_dotProduct_toMatrix_mulVec_eq_of_equivalent
    [IsLocalRing R] [Module.Free R M] [Module.Finite R M] [IsDomain T] [CharZero T]
    {B' : BilinForm R M'} {N' : ℕ → Submodule R M'} (h : B.IsJordanSplitting π N)
    (h' : B'.IsJordanSplitting π N') (hB : B.IsSymm) (hBB' : B.Equivalent B')
    (hπ : π ∈ nonZeroDivisors R) (h2 : 2 ∣ π) {j : ℕ}
    (hnext : ∀ w ∈ N (j + 1), 2 * π ^ (j + 1) ∣ B w w) (f : R →+* S)
    (hf : f (2 * π ^ (j + 1)) = 0) (ψ : AddChar S T) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι R ↥(⨆ i ∈ Set.Iic j, N i)) (b' : Basis ι R ↥(⨆ i ∈ Set.Iic j, N' i)) :
    ∑ x : ι → S, ψ (x ⬝ᵥ ((B.restrict (⨆ i ∈ Set.Iic j, N i)).toMatrix b).map f *ᵥ x) =
      ∑ x : ι → S, ψ (x ⬝ᵥ ((B'.restrict (⨆ i ∈ Set.Iic j, N' i)).toMatrix b').map f *ᵥ x) := by
  classical
  obtain ⟨ε⟩ := _root_.id hBB'
  have : Module.Free R M' := .of_equiv ε.toLinearEquiv
  have : Module.Finite R M' := .equiv ε.toLinearEquiv
  have hB' : B'.IsSymm := ⟨fun x y ↦ by rw [← ε.symm.map_app, ← ε.symm.map_app, hB.eq]⟩
  have hnext' := h.forall_two_mul_pow_dvd_of_equivalent h' hBB' hπ h2 hnext
  -- Bases of `M` and `M'` adapted to the decompositions at `j`.
  obtain ⟨_, _⟩ := (⨆ i ∈ Set.Ici (j + 1), N i).finite_free_of_isCompl
    (h.isCompl_biSup_Iic_biSup_Ici j).symm
  obtain ⟨_, _⟩ := (⨆ i ∈ Set.Ici (j + 1), N' i).finite_free_of_isCompl
    (h'.isCompl_biSup_Iic_biSup_Ici j).symm
  set c := Free.chooseBasis R ↥(⨆ i ∈ Set.Ici (j + 1), N i)
  set c' := Free.chooseBasis R ↥(⨆ i ∈ Set.Ici (j + 1), N' i)
  set d := (b.prod c).map (Submodule.prodEquivOfIsCompl _ _ (h.isCompl_biSup_Iic_biSup_Ici j))
  set d' := (b'.prod c').map (Submodule.prodEquivOfIsCompl _ _ (h'.isCompl_biSup_Iic_biSup_Ici j))
  have hd := h.sum_addChar_toMatrix_map_prod hB h2 hnext f hf ψ b c
  have hd' := h'.sum_addChar_toMatrix_map_prod hB' h2 hnext' f hf ψ b' c'
  -- The two splittings have the same number of basis vectors above `j`.
  have hκ := (finrank_eq_card_basis d).symm.trans
    (ε.toLinearEquiv.finrank_eq.trans (finrank_eq_card_basis d'))
  simp only [Fintype.card_sum, Nat.add_left_cancel_iff] at hκ
  -- The Gauss sums of the Gram matrices of `B` and `B'` in these bases agree.
  have hM : ∑ x, ψ (x ⬝ᵥ (B.toMatrix d).map f *ᵥ x) =
      ∑ x, ψ (x ⬝ᵥ (B'.toMatrix d').map f *ᵥ x) := by
    have hdd : B'.toMatrix (d.map ε.toLinearEquiv) = B.toMatrix d := by
      ext
      simp [ε.map_app]
    have hbij : Function.Bijective (((d.map ε.toLinearEquiv).toMatrix d').map f).mulVec := by
      refine Function.bijective_iff_has_inverse.mpr
        ⟨((d'.toMatrix (d.map ε.toLinearEquiv)).map f).mulVec, fun x ↦ ?_, fun x ↦ ?_⟩ <;>
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Basis.toMatrix_mul_toMatrix_flip,
        Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec]
    rw [← toMatrix_mul_basis_toMatrix (d.map ε.toLinearEquiv) d' B', hdd, Matrix.map_mul,
      Matrix.map_mul, Matrix.transpose_map, Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec
        ψ _ hbij]
  rw [hd, hd', hκ] at hM
  exact mul_left_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) hM

end LinearMap.BilinForm

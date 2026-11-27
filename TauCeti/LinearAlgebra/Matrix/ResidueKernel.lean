/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.IdealDivisibility
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.SubspaceOrbit
import TauCeti.LinearAlgebra.Matrix.IdealEntries

/-!
# The kernel of the reduction of a matrix over a local ring

For a square matrix `A` over a local ring `R` with residue field `k`, `A.residueKer` is the kernel
of its reduction `Ā : kⁿ → kⁿ`. This file studies it over a discrete valuation ring with
uniformizer `ϖ`, for the matrices `A` such that `ϖ A⁻¹` is again integral, that is
`A * B = ϖ • 1` for some integral `B`. Such a matrix is determined up to left multiplication by
`GL_n(R)` by the kernel of its reduction, and the dimension of that kernel is the valuation of
its determinant:

* `Matrix.associated_det_pow_finrank_residueKer`: if `A * B = ϖ • 1`, then `det A` is associated
  to `ϖ ^ dim ker Ā`;
* `Matrix.exists_eq_mul_iff_residueKer_eq`: if `A * B = ϖ • 1` and `A' * B' = ϖ • 1`, then
  `A' = U A` for some `U ∈ GL_n(R)` exactly when `ker Ā = ker Ā'`;
* `Matrix.exists_residueKer_mul_eq`: right multiplication by `GL_n(R)` moves the kernel of the
  reduction of any square matrix over a local ring to every subspace of the same dimension.

In lattice terms, `A * B = ϖ • 1` says `ϖ Rⁿ ⊆ A Rⁿ ⊆ Rⁿ`, the lattice `A⁻¹ Rⁿ` lies between `Rⁿ`
and `ϖ⁻¹ Rⁿ`, and `ker Ā` is its image in `ϖ⁻¹ Rⁿ / Rⁿ ≅ kⁿ`. These are the facts behind the
decomposition of the double coset `GL_n(R) diag(ϖ, …, ϖ, 1, …, 1) GL_n(R)` into single cosets
indexed by the subspaces of `kⁿ`, which is the basis of the spherical Hecke operators of `GL_n`
over a local field.

## Main definitions

* `Matrix.residueKer A`: the kernel of the reduction of `A` modulo the maximal ideal.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), §3.2.
* I. G. Macdonald, *Symmetric functions and Hall polynomials*, 2nd ed., Oxford (1995),
  Chapter V, §2.

The classification of the cosets by the kernel of the reduction is adapted from grh-lean
(<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic PBC),
`Lib/Weil/Unramified/HeckeGL.lean`, declarations `New.residueKer`,
`New.mul_inv_mem_localIntGL_iff` and `New.finrank_residueKer`.
-/

public section

noncomputable section

open Module IsLocalRing
open scoped Pointwise

namespace Matrix

variable {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]

section LocalRing

variable [IsLocalRing R]

/-- The kernel of the reduction `Ā : kⁿ → kⁿ` of a square matrix `A` over a local ring `R`
modulo its maximal ideal, `k` the residue field. -/
def residueKer (A : Matrix ι ι R) : Submodule (ResidueField R) (ι → ResidueField R) :=
  LinearMap.ker (A.map (residue R)).mulVecLin

/-- The defining equation of `residueKer`, for modules that import it: the definition is not
exposed. -/
theorem residueKer_def (A : Matrix ι ι R) :
    A.residueKer = LinearMap.ker (A.map (residue R)).mulVecLin :=
  (rfl)

/-- A vector lies in the kernel of the reduction of `A` when `Ā` sends it to `0`. -/
@[simp]
theorem mem_residueKer {A : Matrix ι ι R} {v : ι → ResidueField R} :
    v ∈ A.residueKer ↔ A.map (residue R) *ᵥ v = 0 := by
  rw [residueKer_def, LinearMap.mem_ker, mulVecLin_apply]

/-- The reduction of the zero matrix kills every vector. -/
@[simp]
theorem residueKer_zero : (0 : Matrix ι ι R).residueKer = ⊤ := by
  ext v
  simp

variable [DecidableEq ι]

/-- The reduction of the identity matrix is injective. -/
@[simp]
theorem residueKer_one : (1 : Matrix ι ι R).residueKer = ⊥ := by
  ext v
  simp [Submodule.mem_bot]

/-- Left multiplication by `GL_n(R)` does not change the kernel of the reduction. -/
@[simp]
theorem residueKer_units_mul (U : GL ι R) (A : Matrix ι ι R) :
    ((U : Matrix ι ι R) * A).residueKer = A.residueKer := by
  ext v
  simp only [mem_residueKer, Matrix.map_mul, ← mulVec_mulVec]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, mulVec_zero]⟩
  -- the reduction of `U⁻¹` undoes the reduction of `U`
  have hU : ((U⁻¹ : GL ι R) : Matrix ι ι R).map (residue R) *
      (U : Matrix ι ι R).map (residue R) = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← one_mulVec (A.map (residue R) *ᵥ v), ← hU, ← mulVec_mulVec, h, mulVec_zero]

/-- Right multiplication by `U ∈ GL_n(R)` moves the kernel of the reduction by the reduction of
`U⁻¹`. -/
theorem residueKer_mul_units (A : Matrix ι ι R) (U : GL ι R) :
    (A * (U : Matrix ι ι R)).residueKer =
      (GeneralLinearGroup.map (residue R) U)⁻¹ • A.residueKer := by
  set Ū := GeneralLinearGroup.map (residue R) U
  -- the matrix of `Ū` is the entrywise reduction of `U`
  have hŪ (v : ι → ResidueField R) :
      (U : Matrix ι ι R).map (residue R) *ᵥ v = Ū • v := by
    rw [GeneralLinearGroup.smul_eq_mulVec, GeneralLinearGroup.val_map_apply]
  ext v
  refine ⟨fun h ↦ (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨Ū • v, mem_residueKer.mpr ?_, inv_smul_smul Ū v⟩, fun h ↦ ?_⟩
  · rw [← hŪ, mulVec_mulVec, ← Matrix.map_mul]
    exact mem_residueKer.mp h
  · obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
    rw [mem_residueKer, Matrix.map_mul, ← mulVec_mulVec, hŪ, smul_inv_smul]
    exact mem_residueKer.mp hw

/-- **Moving the kernel of the reduction.** Right multiplication by `GL_n(R)` carries the kernel
of the reduction of a square matrix over a local ring to any subspace of the same dimension. -/
theorem exists_residueKer_mul_eq (A : Matrix ι ι R)
    {W : Submodule (ResidueField R) (ι → ResidueField R)}
    (hW : finrank (ResidueField R) W = finrank (ResidueField R) A.residueKer) :
    ∃ U : GL ι R, (A * (U : Matrix ι ι R)).residueKer = W := by
  obtain ⟨P, hP⟩ := GeneralLinearGroup.exists_smul_eq_of_finrank_eq hW.symm
  obtain ⟨U, hU⟩ := GeneralLinearGroup.map_surjective (n := ι) (residue R) residue_surjective P⁻¹
  exact ⟨U, by rw [residueKer_mul_units, hU, inv_inv, hP]⟩

/-- If `ϖ` generates the maximal ideal, then `ϖ ^ dim ker Ā` divides `det A`. -/
theorem pow_finrank_residueKer_dvd_det {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (A : Matrix ι ι R) : ϖ ^ finrank (ResidueField R) A.residueKer ∣ A.det := by
  -- after a change of basis `U ∈ GL_n(R)`, the columns of `A U` indexed by a basis of `ker Ā` are
  -- divisible by `ϖ`
  -- a set `s` of `dim ker Ā` coordinates and the subspace `W` spanned by their basis vectors
  have hle : finrank (ResidueField R) A.residueKer ≤ (Finset.univ : Finset ι).card := by
    have := Submodule.finrank_le A.residueKer
    rwa [finrank_fintype_fun_eq_card, ← Finset.card_univ] at this
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq hle
  have he := (Pi.basisFun (ResidueField R) ι).linearIndependent.comp ((↑) : s → ι)
    Subtype.val_injective
  have hW : finrank (ResidueField R) (Submodule.span (ResidueField R)
      (Set.range (Pi.basisFun (ResidueField R) ι ∘ ((↑) : s → ι)))) =
      finrank (ResidueField R) A.residueKer := by
    rw [finrank_span_eq_card he, Fintype.card_coe, hs]
  obtain ⟨U, hU⟩ := exists_residueKer_mul_eq A hW
  -- the columns of `A U` indexed by `s` reduce to zero
  have hcol (j : ι) (hj : j ∈ s) (i : ι) : ϖ ∣ (A * (U : Matrix ι ι R)) i j := by
    have hmem : Pi.single j 1 ∈ (A * (U : Matrix ι ι R)).residueKer := by
      rw [hU, ← Pi.basisFun_apply]
      exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    have h := congrFun (mem_residueKer.mp hmem) i
    rw [mulVec_single_one, col_apply, Pi.zero_apply, map_apply, residue_eq_zero_iff, hϖ] at h
    exact Ideal.mem_span_singleton.mp h
  have hdvd := prod_dvd_det_of_dvd_row (A * (U : Matrix ι ι R))ᵀ
    (fun j ↦ if j ∈ s then ϖ else 1) fun j i ↦ by
      split_ifs with hj
      · exact hcol j hj i
      · exact one_dvd _
  simp only [det_transpose, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const, hs,
    det_mul, ← GeneralLinearGroup.val_det_apply] at hdvd
  exact (Units.dvd_mul_right).mp hdvd

end LocalRing

section DiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

variable [DecidableEq ι]

omit [Fintype ι] in
/-- The reduction of `ϖ • 1` vanishes. -/
private theorem map_residue_smul_one (hϖ : Irreducible ϖ) :
    (ϖ • (1 : Matrix ι ι R)).map (residue R) = 0 := by
  have : residue R ϖ = 0 := (residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit
  ext i j
  simp [this]

/-- If `A * B = ϖ • 1`, the image of the reduction of `B` lies in the kernel of `Ā`. -/
private theorem mulVec_mem_residueKer (hϖ : Irreducible ϖ) {A B : Matrix ι ι R}
    (h : A * B = ϖ • 1) (v : ι → ResidueField R) : B.map (residue R) *ᵥ v ∈ A.residueKer := by
  rw [mem_residueKer, mulVec_mulVec, ← Matrix.map_mul, h, map_residue_smul_one hϖ, zero_mulVec]

/-- **The determinant and the kernel of the reduction.** If `ϖ` is a uniformizer and
`A * B = ϖ • 1`, so that `ϖ A⁻¹` is integral, then `det A` is associated to `ϖ ^ dim ker Ā`. -/
theorem associated_det_pow_finrank_residueKer (hϖ : Irreducible ϖ) {A B : Matrix ι ι R}
    (h : A * B = ϖ • 1) :
    Associated A.det (ϖ ^ finrank (ResidueField R) A.residueKer) := by
  have hmax := hϖ.maximalIdeal_eq
  obtain ⟨a, ha⟩ := pow_finrank_residueKer_dvd_det hmax A
  obtain ⟨b, hb⟩ := pow_finrank_residueKer_dvd_det hmax B
  -- the reduction of `B` kills the image of `Ā`, as `B * A = ϖ • 1`; so
  -- `n = dim im Ā + dim ker Ā ≤ dim ker Ā + dim B.residueKer`
  have hBA := (mul_eq_smul_one_comm (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero)).mp h
  have hle : Fintype.card ι ≤ finrank (ResidueField R) A.residueKer +
      finrank (ResidueField R) B.residueKer := by
    have hrange : LinearMap.range (A.map (residue R)).mulVecLin ≤ B.residueKer := by
      rintro _ ⟨v, rfl⟩
      exact mulVec_mem_residueKer hϖ hBA v
    have := (A.map (residue R)).mulVecLin.finrank_range_add_finrank_ker
    rw [finrank_fintype_fun_eq_card, ← residueKer_def] at this
    have := Submodule.finrank_mono hrange
    omega
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
  -- `ϖ ^ k * a * (ϖ ^ m * b) = det A * det B = ϖ ^ n` and `ϖ ^ k * ϖ ^ m = ϖ ^ n * ϖ ^ t`, so
  -- `ϖ ^ n * (ϖ ^ t * a * b) = ϖ ^ n`, and cancelling `ϖ ^ n` shows that `a` is a unit
  have hpow : ϖ ^ finrank (ResidueField R) A.residueKer *
      ϖ ^ finrank (ResidueField R) B.residueKer = ϖ ^ Fintype.card ι * ϖ ^ t := by
    rw [← pow_add, ← pow_add, ht]
  have hprod : ϖ ^ Fintype.card ι * (ϖ ^ t * a * b) = ϖ ^ Fintype.card ι * 1 := by
    have hdet := congrArg det h
    rw [det_mul, det_smul, det_one, mul_one, ha, hb] at hdet
    linear_combination hdet - a * b * hpow
  have hunit : IsUnit a := IsUnit.of_mul_eq_one (ϖ ^ t * b) <| by
    linear_combination mul_left_cancel₀ (pow_ne_zero _ hϖ.ne_zero) hprod
  rw [ha]
  exact (associated_mul_unit_right _ _ hunit).symm

/-- If `A * B = ϖ • 1` and `det A` is associated to `ϖ ^ j`, the kernel of the reduction of `A`
has dimension `j`. -/
theorem finrank_residueKer_eq_of_associated_det (hϖ : Irreducible ϖ) {A B : Matrix ι ι R}
    (h : A * B = ϖ • 1) {j : ℕ} (hj : Associated A.det (ϖ ^ j)) :
    finrank (ResidueField R) A.residueKer = j := by
  have h' := (associated_det_pow_finrank_residueKer hϖ h).symm.trans hj
  exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h'.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h'.symm.dvd)

/-- If `A * B = ϖ • 1`, the valuation of `det A` is at most the size of the matrix. -/
theorem le_card_of_associated_det (hϖ : Irreducible ϖ) {A B : Matrix ι ι R} (h : A * B = ϖ • 1)
    {j : ℕ} (hj : Associated A.det (ϖ ^ j)) : j ≤ Fintype.card ι := by
  rw [← finrank_residueKer_eq_of_associated_det hϖ h hj]
  simpa using Submodule.finrank_le A.residueKer

/-- If `A * B = ϖ • 1` and the kernel of `Ā` lies in that of `Ā'`, then `A' * B` reduces to `0`,
so it is divisible by `ϖ`. -/
private theorem exists_mul_eq_smul (hϖ : Irreducible ϖ) {A B A' : Matrix ι ι R}
    (h : A * B = ϖ • 1) (hker : A.residueKer ≤ A'.residueKer) :
    ∃ C : Matrix ι ι R, A' * B = ϖ • C := by
  refine (map_eq_zero_iff_exists_eq_smul (ker_residue.trans hϖ.maximalIdeal_eq)).mp
    (ext fun i j ↦ ?_)
  have h0 := congrFun (mem_residueKer.mp (hker (mulVec_mem_residueKer hϖ h (Pi.single j 1)))) i
  rwa [mulVec_mulVec, ← Matrix.map_mul, mulVec_single_one, col_apply] at h0

/-- **The cosets `GL_n(R) A` and the kernel of the reduction.** Let `A * B = ϖ • 1` and
`A' * B' = ϖ • 1` for a uniformizer `ϖ`. Then `A' = U A` for some `U ∈ GL_n(R)` exactly when the
reductions of `A` and `A'` have the same kernel. -/
theorem exists_eq_mul_iff_residueKer_eq (hϖ : Irreducible ϖ) {A B A' B' : Matrix ι ι R}
    (h : A * B = ϖ • 1) (h' : A' * B' = ϖ • 1) :
    (∃ U : GL ι R, A' = (U : Matrix ι ι R) * A) ↔ A.residueKer = A'.residueKer := by
  refine ⟨?_, fun hker ↦ ?_⟩
  · rintro ⟨U, rfl⟩
    exact (residueKer_units_mul U A).symm
  obtain ⟨C, hC⟩ := exists_mul_eq_smul hϖ h hker.le
  obtain ⟨C', hC'⟩ := exists_mul_eq_smul hϖ h' hker.ge
  have hϖ0 := hϖ.ne_zero
  have hBA := (mul_eq_smul_one_comm (mem_nonZeroDivisors_of_ne_zero hϖ0)).mp h
  -- `ϖ (C A) = A' B A = ϖ A'`
  have hCA : C * A = A' := (smul_right_inj hϖ0).mp <| by
    rw [← smul_mul, ← hC]
    simp [Matrix.mul_assoc, hBA]
  -- `ϖ (C C') = C A B' = A' B' = ϖ 1`
  have hCC' : C * C' = 1 := (smul_right_inj hϖ0).mp <| by
    rw [← Matrix.mul_smul, ← hC']
    simpa only [← Matrix.mul_assoc, hCA] using h'
  exact ⟨⟨C, C', hCC', mul_eq_one_comm.mp hCC'⟩, hCA.symm⟩

end DiscreteValuationRing

end Matrix

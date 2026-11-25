/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap.Order
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.FiniteSpectrum
import TauCeti.Analysis.CStarAlgebra.Matrix.Order
import TauCeti.Analysis.CStarAlgebra.State.Space

/-!
# Completely positive maps into matrix algebras

This file supplies operations on completely positive maps into the matrix algebras
`CStarMatrix n n B` over a C⋆-algebra `B`, indexed by finite types, that are used in matrix
approximation arguments for traces on C⋆-algebras, and the Choi–Effros factorization of a
completely positive map from a nonzero unital C⋆-algebra into a matrix algebra, or more generally
into a unital C⋆-algebra in which `φ 1` has finite spectrum.

* `CompletelyPositiveMap.blockDiagonal`: the block-diagonal sum `a ↦ diag(φ_i(a))` of completely
  positive maps into matrix algebras over a C⋆-algebra, built from the corner embeddings
  `CStarMatrix.blockDiagonalSingle`, with the trace formula
  `CompletelyPositiveMap.normalizedTrace_blockDiagonal_apply`, which weights the block `i` by
  `|n i| / |Σ i, n i|`, the norm `CompletelyPositiveMap.norm_blockDiagonal_apply`
  (`‖diag(φ_i(a))‖ = maxᵢ ‖φ_i(a)‖`), the multiplicativity defect
  `CompletelyPositiveMap.blockDiagonal_map_mul_sub`, which is the block-diagonal matrix of the
  defects of the `φ_i`, and contractivity `CompletelyPositiveMap.norm_blockDiagonal_map_one_le_one`.
* `CompletelyPositiveMap.compression`: the compression `T ↦ (⟪e i, T e j⟫)ᵢⱼ` of `B(H)` by a finite
  family of vectors, which is the map `T ↦ V⋆TV` for `V x = Σ xᵢ eᵢ`. It is unital when the family
  is orthonormal (`CompletelyPositiveMap.compression_map_one`), and its normalized trace is
  `n⁻¹ Σᵢ ⟪eᵢ, T eᵢ⟫` (`CompletelyPositiveMap.normalizedTrace_compression`). For an orthonormal
  basis of the range of a finite-rank projection `P` this is the compression `T ↦ PTP`.
* `CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt`: the **Choi–Effros factorization**.
  A completely positive map `φ` from a nonzero unital C⋆-algebra into a matrix algebra factors
  as `φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` and `ψ` unital completely positive. The general form
  `CompletelyPositiveMap.exists_unital_eq_sqrt_mul_mul_sqrt_of_finite_spectrum` allows any unital
  C⋆-algebra as codomain, provided `φ 1` has finite spectrum.

For the factorization, let `p` be the support projection of `h` and `h⁺` the inverse of `h` on
the range of `p`, both obtained from the continuous functional calculus, which applies to any
function since the spectrum is finite (`TauCeti.exists_support_projection_of_finite_spectrum`).
The Kadison–Schwarz inequality gives `φ(a)⋆φ(a) ≤ ‖φ 1‖ ‖a‖² φ(1)`, so `φ(a)(1 - p) = 0`
(`CompletelyPositiveMapClass.map_mul_eq_zero_of_map_one_mul_eq_zero`), and by symmetry
`φ(a) = p φ(a) p`. The map `ψ(a) = h⁺ φ(a) h⁺ + ω(a)(1 - p)` for a state `ω` is completely
positive and unital, and `h ψ(a) h = p φ(a) p = φ(a)`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*,
  Mem. Amer. Math. Soc. 184 (2006), no. 865; arXiv:math/0304009v2 (numbering cited), proof of
  Lemma 2.7.
* M.-D. Choi and E. G. Effros, *The completely positive lifting problem for C⋆-algebras*,
  Ann. of Math. 104 (1976), 585–609.
-/

public section

noncomputable section

open scoped CStarAlgebra InnerProductSpace ComplexOrder Matrix
open CStarMatrix (ofMatrix)

namespace CompletelyPositiveMap

section BlockDiagonal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*} [∀ i, Fintype (n i)]

/-- The **block-diagonal sum** `a ↦ diag(φ_i(a))` of completely positive maps
`φ_i : A → M_{n i}(B)`, a completely positive map into `M_{Σ i, n i}(B)`: the sum of the
compositions of the `φ_i` with the corner embeddings. -/
def blockDiagonal (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) :
    A →CP CStarMatrix (Σ i, n i) (Σ i, n i) B :=
  ∑ i, (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.blockDiagonalSingle ℂ B i)).comp (φ i)

/-- The block-diagonal sum evaluates to the block-diagonal matrix `diag(φ_i(a))`. -/
theorem blockDiagonal_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) (a : A) :
    blockDiagonal φ a = ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (φ i a)) := by
  rw [blockDiagonal, sum_apply, ← CStarMatrix.sum_blockDiagonalSingle (R := ℂ)]
  simp only [comp_apply, CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap]

/-- The block `i` of the block-diagonal sum is `φ_i`. -/
@[simp]
theorem blockDiagonal_apply_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) (a : A) (i : ι)
    (j k : n i) : blockDiagonal φ a ⟨i, j⟩ ⟨i, k⟩ = φ i a j k := by
  rw [blockDiagonal_apply, CStarMatrix.ofMatrix_apply, Matrix.blockDiagonal'_apply_eq,
    CStarMatrix.ofMatrix_symm_apply]

/-- The block-diagonal sum vanishes off the diagonal blocks. -/
theorem blockDiagonal_apply_ne (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) (a : A) {i i' : ι}
    (j : n i) (k : n i') (h : i ≠ i') : blockDiagonal φ a ⟨i, j⟩ ⟨i', k⟩ = 0 := by
  rw [blockDiagonal_apply, CStarMatrix.ofMatrix_apply, Matrix.blockDiagonal'_apply_ne _ j k h]

/-- The normalized trace of the block-diagonal sum weights the trace of `φ_i` by
`|n i| / |Σ i, n i|`: for blocks of sizes `1` and `3` the weights are `1/4` and `3/4`. -/
theorem normalizedTrace_blockDiagonal_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) ℂ) (a : A) :
    CStarMatrix.normalizedTrace (blockDiagonal φ a) =
      ∑ i, (Fintype.card (n i) / Fintype.card (Σ i, n i) : ℂ) *
        CStarMatrix.normalizedTrace (φ i a) := by
  rw [blockDiagonal_apply, CStarMatrix.normalizedTrace_blockDiagonal']

/-- The norm of `diag(φ_i(a))` is the largest of the norms `‖φ_i(a)‖`, so a block-diagonal sum of
completely positive contractions is a contraction. -/
theorem norm_blockDiagonal_apply (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) (a : A) :
    ‖blockDiagonal φ a‖ = ‖fun i => φ i a‖ := by
  rw [blockDiagonal_apply, CStarMatrix.norm_ofMatrix_blockDiagonal']

/-- The multiplicativity defect of the block-diagonal sum is the block-diagonal matrix of the
multiplicativity defects of the `φ_i`. -/
theorem blockDiagonal_map_mul_sub (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B) (a b : A) :
    blockDiagonal φ (a * b) - blockDiagonal φ a * blockDiagonal φ b =
      ofMatrix (Matrix.blockDiagonal' fun i => ofMatrix.symm (φ i (a * b) - φ i a * φ i b)) := by
  simp only [blockDiagonal_apply, ← CStarMatrix.blockDiagonalNonUnitalStarAlgHom_apply (R := ℂ),
    ← map_mul, ← map_sub]
  -- unfold the embedding and evaluate the pointwise operations blockwise
  simp only [CStarMatrix.blockDiagonalNonUnitalStarAlgHom_apply, Pi.sub_apply, Pi.mul_apply]

end BlockDiagonal

section BlockDiagonalUnital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ι → Type*} [∀ i, Fintype (n i)]

/-- The block-diagonal sum of unital completely positive maps is unital. -/
theorem blockDiagonal_map_one [∀ i, DecidableEq (n i)] (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B)
    (h : ∀ i, φ i 1 = 1) : blockDiagonal φ 1 = 1 := by
  rw [blockDiagonal_apply, ← CStarMatrix.sum_blockDiagonalSingle (R := ℂ),
    ← CStarMatrix.sum_blockDiagonalSingle_one ℂ]
  simp [h]

/-- A block-diagonal sum of contractive completely positive maps on a unital C⋆-algebra is
contractive. -/
theorem norm_blockDiagonal_map_one_le_one (φ : ∀ i, A →CP CStarMatrix (n i) (n i) B)
    (h : ∀ i, ‖φ i 1‖ ≤ 1) : ‖blockDiagonal φ 1‖ ≤ 1 := by
  classical
  have h0 : 0 ≤ blockDiagonal φ 1 := map_nonneg _ (zero_le_one (α := A))
  rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ h0, ← sub_nonneg,
    ← CStarMatrix.sum_blockDiagonalSingle_one ℂ, blockDiagonal, sum_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [comp_apply, CompletelyPositiveMapClass.coe_toCompletelyPositiveLinearMap, ← map_sub]
  have hi : 0 ≤ 1 - φ i 1 := sub_nonneg.mpr
    ((CStarAlgebra.norm_le_one_iff_of_nonneg _ (map_nonneg _ (zero_le_one (α := A)))).mp (h i))
  exact map_nonneg (CStarMatrix.blockDiagonalSingle ℂ B i) hi

end BlockDiagonalUnital

section Compression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {n : Type*} [Fintype n]

/-- The **compression** of `B(H)` by a finite family of vectors `e : n → H`: the matrix
`(⟪e i, T e j⟫)ᵢⱼ`, as a completely positive map; it is the matrix of `V⋆TV` for
`V x = Σ xᵢ eᵢ`. -/
def compression (e : n → H) : (H →L[ℂ] H) →CP CStarMatrix n n ℂ where
  toLinearMap :=
    { toFun T := ofMatrix (Matrix.of fun i j => ⟪e i, T (e j)⟫_ℂ)
      map_add' S T := by ext i j; simp
      map_smul' c T := by ext i j; simp }
  -- The quadratic forms of the compression are those of `T` at the vectors `Σ_a v_a e_a`.
  map_cstarMatrix_nonneg' k M hM := by
    rw [← map_le_map_iff (CStarMatrix.compStarAlgEquiv ℂ (Fin k) n ℂ), map_zero]
    refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun v => ?_
    have key := CStarMatrix.nonneg_iff_forall_sum_inner_nonneg.mp hM
      fun p => (∑ a, v (p, a) • e a : H)
    convert key using 1
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun q _ => ?_)
    refine Finset.sum_comm.trans
      (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_)
    rw [CStarMatrix.compStarAlgEquiv_apply, CStarMatrix.map_apply]
    simp [CStarMatrix.ofMatrix_apply]
    ring

/-- The entries of the compression are `⟪e i, T e j⟫`. -/
@[simp]
theorem compression_apply (e : n → H) (T : H →L[ℂ] H) (i j : n) :
    compression e T i j = ⟪e i, T (e j)⟫_ℂ :=
  (rfl)

/-- The compression by an orthonormal family is unital. -/
theorem compression_map_one [DecidableEq n] {e : n → H} (he : Orthonormal ℂ e) :
    compression e 1 = 1 := by
  ext i j
  rw [compression_apply, one_apply_eq_self, orthonormal_iff_ite.mp he i j, CStarMatrix.one_apply]

/-- The normalized trace of the compression `(⟪e i, T e j⟫)ᵢⱼ` is `n⁻¹ Σᵢ ⟪e i, T e i⟫`. For an
orthonormal basis of the range of a finite-rank projection `P` this is `Tr(TP) / Tr(P)`. -/
theorem normalizedTrace_compression (e : n → H) (T : H →L[ℂ] H) :
    CStarMatrix.normalizedTrace (compression e T) =
      (Fintype.card n : ℂ)⁻¹ * ∑ i, ⟪e i, T (e i)⟫_ℂ := by
  simp [CStarMatrix.normalizedTrace_eq_sum]

end Compression

section ChoiEffros

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **The Choi–Effros factorization**, for a codomain in which `φ 1` has finite spectrum. A
completely positive map `φ` from a nonzero unital C⋆-algebra into a unital C⋆-algebra, with
`φ 1` of finite spectrum, factors as `φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` for some unital
completely positive `ψ`. -/
theorem exists_unital_eq_sqrt_mul_mul_sqrt_of_finite_spectrum [Nontrivial A] (φ : A →CP B)
    (hφ : (spectrum ℝ (φ 1)).Finite) :
    ∃ ψ : A →CP B, ψ 1 = 1 ∧ ∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) := by
  obtain ⟨p, g, hp, hgsa, hsg, hgs, hgxg, hsp, hxp⟩ :=
    TauCeti.exists_support_projection_of_finite_spectrum (map_nonneg φ zero_le_one) hφ
  have hq : IsStarProjection (1 - p) := hp.one_sub
  -- a state `ω` of `A`
  obtain ⟨f, hf⟩ := TauCeti.stateSpace_nonempty (A := A)
  obtain ⟨ω, -, hω⟩ := TauCeti.mem_stateSpace_iff_exists_positiveLinearMap.mp hf
  have hω1 : ω 1 = 1 := by
    rw [← (TauCeti.mem_stateSpace_iff_map_one.mp hf).2, ← hω]
    simp
  -- `ψ(a) = g φ(a) g + ω(a)(1 - p)` for the support projection `p` of `h`, the inverse `g` of `h`
  -- on the range of `p`, and a state `ω`.
  let ψ : A →CP B := (conj g).comp φ + (conj (1 - p)).comp
    ((CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (StarAlgHom.ofId ℂ B)).comp
      ω.toCompletelyPositiveMap)
  have hψ (a : A) : ψ a = g * φ a * g + ω a • (1 - p) := by
    simp [ψ, hgsa.star_eq, hq.isSelfAdjoint.star_eq, Algebra.algebraMap_eq_smul_one,
      hq.isIdempotentElem.eq]
  refine ⟨ψ, ?_, fun a => ?_⟩
  · rw [hψ, hgxg, hω1, one_smul, add_sub_cancel]
  -- `φ a = p φ(a) p`, since `φ(a)(1 - p) = 0` and `(1 - p)φ(a) = 0`
  have hr := CompletelyPositiveMapClass.map_mul_eq_zero_of_map_one_mul_eq_zero φ hxp a
  have hl : (1 - p) * φ a = 0 := by
    refine CompletelyPositiveMapClass.mul_map_eq_zero_of_mul_map_one_eq_zero φ ?_ a
    simpa [star_mul, hq.isSelfAdjoint.star_eq,
      (map_nonneg φ (zero_le_one (α := A))).isSelfAdjoint.star_eq] using congrArg star hxp
  rw [mul_sub, mul_one, sub_eq_zero] at hr
  rw [sub_mul, one_mul, sub_eq_zero] at hl
  calc φ a = p * φ a * p := by rw [← hl, ← hr]
    _ = CFC.sqrt (φ 1) * (g * φ a * g) * CFC.sqrt (φ 1) := by
      have e : CFC.sqrt (φ 1) * (g * φ a * g) * CFC.sqrt (φ 1) =
          CFC.sqrt (φ 1) * g * φ a * (g * CFC.sqrt (φ 1)) := by simp only [mul_assoc]
      rw [e, hsg, hgs]
    _ = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) := by
      simp [hψ, mul_add, hsp]

/-- **The Choi–Effros factorization.** A completely positive map `φ` from a nonzero unital
C⋆-algebra into a matrix algebra factors as `φ(a) = h ψ(a) h` with `h = φ(1)^{1/2}` for some
unital completely positive `ψ`. For example, for `φ(a) = diag(a₁, 0)` on `ℂ²`, `h = e₁₁` and one
such `ψ` is `ψ(a) = diag(a₁, ω(a))` for a state `ω`. -/
theorem exists_unital_eq_sqrt_mul_mul_sqrt [Nontrivial A] {n : Type*} [Fintype n] [DecidableEq n]
    (φ : A →CP CStarMatrix n n ℂ) :
    ∃ ψ : A →CP CStarMatrix n n ℂ, ψ 1 = 1 ∧ ∀ a, φ a = CFC.sqrt (φ 1) * ψ a * CFC.sqrt (φ 1) :=
  exists_unital_eq_sqrt_mul_mul_sqrt_of_finite_spectrum φ (CStarMatrix.finite_real_spectrum _)

end ChoiEffros

end CompletelyPositiveMap

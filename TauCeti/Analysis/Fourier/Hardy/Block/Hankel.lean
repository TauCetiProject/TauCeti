/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Toeplitz
public import TauCeti.Analysis.Fourier.Hardy.Compact
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Block Hankel operators, Toeplitz products, and continuous-symbol compactness

For `A : BlockSymbol r`, the block Hankel operator
`TauCeti.blockHankel r A : BlockHardySpace r →L[ℂ] ↥(blockHardySubmodule r)ᗮ` projects
`Lp.operatorMultiplication 2 A` of a block Hardy function onto `(blockHardySubmodule r)ᗮ`, yielding
the ambient splitting `TauCeti.coe_blockToeplitz_add_coe_blockHankel`, coordinatewise and
scalar-diagonal Hankel decompositions (`TauCeti.blockHardyOrthogonalEquiv_blockHankel_apply`,
`TauCeti.blockHardyOrthogonalEquiv_blockHankel_smul_one`), and negative-mode Fourier matrix elements
(`TauCeti.inner_blockFourierMode_blockHankel_blockHardyBasis`). From this follow the **block
Toeplitz semicommutator identity** `TauCeti.blockToeplitz_comp_sub_blockToeplitz`
(`T_A ∘L T_B - T_{A * B} = -(H_{star A}† ∘L H_B)`), the Fourier vanishing criterion
`TauCeti.blockHankel_eq_zero_iff`, exact analytic/coanalytic products
(`TauCeti.blockToeplitz_comp_of_analytic`, `TauCeti.blockToeplitz_comp_of_coanalytic`), and
compactness of continuous-symbol block Hankel operators and semicommutators
(`TauCeti.isCompactOperator_blockHankel_toLp`,
`TauCeti.isCompactOperator_blockToeplitz_comp_sub_blockToeplitz_toLp`).

References: A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators* (2nd ed., §2.9);
J. B. Conway, *A Course in Functional Analysis* (2nd ed.); E. Park, *Toeplitz operators*.
-/

public noncomputable section

open AddCircle ContinuousLinearMap MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Bounded complex-linear block Hankel symbol map `H_A = (1 - P) M_A |H²` into
`↥(blockHardySubmodule r)ᗮ`. -/
def blockHankel (r : ℕ) : BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] ↥(blockHardySubmodule r)ᗮ :=
  compL ℂ (BlockHardySpace r) (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))
      ↥(blockHardySubmodule r)ᗮ (blockHardySubmodule r)ᗮ.orthogonalProjectionOnto ∘L
    (compL ℂ (BlockHardySpace r) (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))
        (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))).flip
      ((blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap) ∘L
    Lp.operatorMultiplication 2

/-- Definition of `blockHankel r A` via projection onto `(blockHardySubmodule r)ᗮ`. -/
theorem blockHankel_apply (r : ℕ) (A : BlockSymbol r) :
    blockHankel r A =
      (blockHardySubmodule r)ᗮ.orthogonalProjectionOnto ∘L Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap := by
  simp only [blockHankel, comp_apply, compL_apply, flip_apply]

/-- Ambient `L²` value of `blockHankel r A f` via complementary `starProjection`. -/
theorem coe_blockHankel_apply {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) :
    (blockHankel r A f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f) -
        (blockHardySubmodule r).starProjection
          (Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f)) := by
  simp [blockHankel_apply, starProjection_orthogonal_val]

/-- Ambient `L²` splitting of `M_A` on block Hardy functions into Toeplitz and Hankel parts. -/
theorem coe_blockToeplitz_add_coe_blockHankel {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) :
    ((blockHardyEquiv r).symm (blockToeplitz r A f) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) +
      (blockHankel r A f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f) := by
  rw [coe_blockHardyEquiv_symm_blockToeplitz_apply, coe_blockHankel_apply, add_sub_cancel]

/-- Block Hankel compression does not increase the operator norm of its symbol. -/
theorem norm_blockHankel_le {r : ℕ} (A : BlockSymbol r) : ‖blockHankel r A‖ ≤ ‖A‖ := by
  rw [blockHankel_apply]
  grw [opNorm_comp_le, opNorm_comp_le, opNorm_comp_le, orthogonalProjectionOnto_norm_le,
    Lp.norm_operatorMultiplication_le, norm_subtypeL_le,
    LinearIsometry.norm_toContinuousLinearMap_le]
  simp

/-- Action of `blockHankel r A` on `PiLp.single 2 j h` under `blockHardyOrthogonalEquiv r`. -/
@[simp] theorem blockHardyOrthogonalEquiv_blockHankel_single {r : ℕ} (A : BlockSymbol r)
    (i j : Fin r) (h : HardySpace) :
    blockHardyOrthogonalEquiv r (blockHankel r A (PiLp.single 2 j h)) i =
      hankel (blockSymbolEntry r i j A) h := by
  simp [blockHankel_apply, coe_blockHardyEquiv_symm_single,
    piLpEquiv_operatorMultiplication_symm_single, hankel_apply, Lp.multiplicationOperator_apply]

/-- Coordinatewise action of `blockHankel r A` through scalar Hankel entry operators. -/
theorem blockHardyOrthogonalEquiv_blockHankel_apply {r : ℕ} (A : BlockSymbol r)
    (f : BlockHardySpace r) (i : Fin r) :
    blockHardyOrthogonalEquiv r (blockHankel r A f) i =
      ∑ j : Fin r, hankel (blockSymbolEntry r i j A) (f j) := by
  conv_lhs => rw [← PiLp.univ_sum_single f]
  simp only [map_sum (blockHankel r A), map_sum (blockHardyOrthogonalEquiv r), WithLp.ofLp_sum,
    Finset.sum_apply, blockHardyOrthogonalEquiv_blockHankel_single]

/-- Scalar-diagonal symbol `a • (1 : BlockSymbol r)` acts coordinatewise by `hankel a`. -/
theorem blockHardyOrthogonalEquiv_blockHankel_smul_one {r : ℕ}
    (a : Lp ℂ ∞ (haarAddCircle (T := 1))) (f : BlockHardySpace r) (i : Fin r) :
    blockHardyOrthogonalEquiv r
      (blockHankel r (a • (1 : BlockSymbol r) : BlockSymbol r) f) i = hankel a (f i) := by
  rw [blockHardyOrthogonalEquiv_blockHankel_apply,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) fun j _ hji ↦ ?_]
  · rw [blockSymbolEntry_smul_one, ite_eq_left rfl]
  · rw [blockSymbolEntry_smul_one, ite_eq_right hji.symm, map_zero, zero_apply]

/-- **Block Hankel Fourier-entry formula (operator form).** -/
theorem inner_blockFourierMode_blockHankel_blockHardyBasis {r : ℕ} (A : BlockSymbol r)
    (m n : ℕ) (i j : Fin r) :
    ⟪(⟨blockFourierMode r (-(m : ℤ) - 1) i,
        blockFourierMode_mem_blockHardySubmodule_orthogonal r m i⟩ : ↥(blockHardySubmodule r)ᗮ),
      blockHankel r A (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪EuclideanSpace.single i (1 : ℂ),
        fourierCoeff A (-(m : ℤ) - 1 - n) (EuclideanSpace.single j (1 : ℂ))⟫_ℂ := by
  rw [← (blockHardyOrthogonalEquiv r).inner_map_map, blockHardyOrthogonalEquiv_blockFourierMode,
    blockHardyBasis_apply, PiLp.inner_apply,
    Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki]) (by simp), PiLp.single_eq_same,
    blockHardyOrthogonalEquiv_blockHankel_single, inner_negativeHardyBasis_hankel_hardyBasis,
    inner_single_fourierCoeff_blockSymbol]

/-- Scalar-entry form of `inner_blockFourierMode_blockHankel_blockHardyBasis`. -/
theorem inner_blockFourierMode_blockHankel_blockHardyBasis_eq_fourierCoeff_blockSymbolEntry {r : ℕ}
    (A : BlockSymbol r) (m n : ℕ) (i j : Fin r) :
    ⟪(⟨blockFourierMode r (-(m : ℤ) - 1) i,
        blockFourierMode_mem_blockHardySubmodule_orthogonal r m i⟩ : ↥(blockHardySubmodule r)ᗮ),
      blockHankel r A (blockHardyBasis r (n, j))⟫_ℂ =
      fourierCoeff (blockSymbolEntry r i j A) (-(m : ℤ) - 1 - n) := by
  rw [inner_blockFourierMode_blockHankel_blockHardyBasis, inner_single_fourierCoeff_blockSymbol]

/-- Every constant matrix symbol has zero block Hankel operator. -/
@[simp] theorem blockHankel_const {r : ℕ}
    (M : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    blockHankel r (Lp.const ∞ (haarAddCircle (T := 1)) M) = 0 := by
  ext f : 1; refine (blockHardyOrthogonalEquiv r).injective (PiLp.ext fun i ↦ ?_)
  rw [zero_apply, blockHardyOrthogonalEquiv_blockHankel_apply, map_zero, PiLp.zero_apply]
  exact Finset.sum_eq_zero fun j _ ↦ by rw [blockSymbolEntry_const, hankel_const, zero_apply]

/-- Every scalar algebra symbol `algebraMap ℂ (BlockSymbol r) c` has zero block Hankel operator. -/
@[simp] theorem blockHankel_algebraMap {r : ℕ} (c : ℂ) :
    blockHankel r ((algebraMap ℂ (BlockSymbol r) : ℂ →+* BlockSymbol r) c) = 0 := by
  rw [Lp.algebraMap_eq_const, blockHankel_const]

/-- The identity symbol `1 : BlockSymbol r` has zero block Hankel operator. -/
@[simp] theorem blockHankel_one (r : ℕ) : blockHankel r (1 : BlockSymbol r) = 0 := by
  simpa using blockHankel_algebraMap (r := r) 1

/-- Adjoint of `blockHankel r A` as multiplication by `star A` compressed onto `BlockHardySpace`. -/
theorem adjoint_blockHankel {r : ℕ} (A : BlockSymbol r) :
    adjoint (blockHankel r A) =
      (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 (star A) ∘L (blockHardySubmodule r)ᗮ.subtypeL := by
  simp only [blockHankel_apply, adjoint_comp,
    LinearIsometryEquiv.toContinuousLinearMap_toLinearIsometry, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, adjoint_subtypeL, adjoint_orthogonalProjectionOnto,
    Lp.adjoint_operatorMultiplication, comp_assoc]

/-- **Block Toeplitz semicommutator identity.** -/
theorem blockToeplitz_comp_sub_blockToeplitz {r : ℕ} (A B : BlockSymbol r) :
    blockToeplitz r A ∘L blockToeplitz r B - blockToeplitz r (A * B) =
      -(adjoint (blockHankel r (star A)) ∘L blockHankel r B) := by
  ext f : 1; apply (blockHardyEquiv r).symm.injective; apply Subtype.ext
  have hmul := DFunLike.congr_fun
    (Lp.operatorMultiplication_comp_operatorMultiplication (p := 2) A B)
    ((blockHardyEquiv r).symm f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))
  rw [comp_apply] at hmul
  simp only [comp_apply, sub_apply, neg_apply, map_sub, map_neg, Submodule.coe_sub,
    Submodule.coe_neg, coe_blockHardyEquiv_symm_blockToeplitz_apply, adjoint_blockHankel, star_star,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_apply_apply, subtypeL_apply, coe_orthogonalProjectionOnto_apply,
    coe_blockHankel_apply]
  rw [← hmul]; abel

/-- `blockHankel r A = 0` iff all negative operator-valued Fourier coefficients of `A` vanish. -/
theorem blockHankel_eq_zero_iff {r : ℕ} (A : BlockSymbol r) :
    blockHankel r A = 0 ↔ ∀ n : ℤ, n < 0 → fourierCoeff A n = 0 := by
  refine ⟨fun hA n hn ↦ ext fun v ↦ PiLp.ext fun i ↦ ?_, fun hA ↦ ?_⟩
  · rw [zero_apply, PiLp.zero_apply, ← (EuclideanSpace.basisFun (Fin r) ℂ).sum_repr v]
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      map_sum (fourierCoeff A n), WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hij : hankel (blockSymbolEntry r i j A) = 0 := by
      ext h : 1
      simpa using congrArg (fun H ↦ blockHardyOrthogonalEquiv r (H (PiLp.single 2 j h)) i) hA
    rw [map_smul, PiLp.smul_apply, ← fourierCoeff_blockSymbolEntry,
      (hankel_eq_zero_iff _).mp hij n hn, smul_zero]
  · ext f : 1; refine (blockHardyOrthogonalEquiv r).injective (PiLp.ext fun i ↦ ?_)
    rw [blockHardyOrthogonalEquiv_blockHankel_apply, zero_apply, map_zero, PiLp.zero_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hij : hankel (blockSymbolEntry r i j A) = 0 := (hankel_eq_zero_iff _).mpr fun n hn ↦ by
      rw [fourierCoeff_blockSymbolEntry, hA n hn, zero_apply, PiLp.zero_apply]
    rw [hij, zero_apply]

/-- `T_A ∘L T_B = T_{A * B}` when `B` is analytic (`fourierCoeff B n = 0` for `n < 0`). -/
theorem blockToeplitz_comp_of_analytic {r : ℕ} (A B : BlockSymbol r)
    (hB : ∀ n : ℤ, n < 0 → fourierCoeff B n = 0) :
    blockToeplitz r A ∘L blockToeplitz r B = blockToeplitz r (A * B) := by
  rw [← sub_eq_zero, blockToeplitz_comp_sub_blockToeplitz, (blockHankel_eq_zero_iff B).mpr hB,
    comp_zero, neg_zero]

/-- `T_A ∘L T_B = T_{A * B}` when `A` is coanalytic (`fourierCoeff (star A) n = 0` for `n < 0`). -/
theorem blockToeplitz_comp_of_coanalytic {r : ℕ} (A B : BlockSymbol r)
    (hA : ∀ n : ℤ, n < 0 → fourierCoeff (star A : BlockSymbol r) n = 0) :
    blockToeplitz r A ∘L blockToeplitz r B = blockToeplitz r (A * B) := by
  rw [← sub_eq_zero, blockToeplitz_comp_sub_blockToeplitz,
    (blockHankel_eq_zero_iff (star A)).mpr hA, adjoint.map_zero, zero_comp, neg_zero]

/-- **Compactness of continuous-symbol block Hankel operators.** -/
theorem isCompactOperator_blockHankel_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    IsCompactOperator (blockHankel r (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F)) := by
  set A : BlockSymbol r := ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F
  let row (i : Fin r) : BlockHardySpace r →L[ℂ] ↥hardySubmoduleᗮ :=
    ∑ j : Fin r, hankel (blockSymbolEntry r i j A) ∘L PiLp.proj (𝕜 := ℂ) 2 (fun _ ↦ HardySpace) j
  have hrow (i : Fin r) : IsCompactOperator (row i) :=
    (compactOperator (RingHom.id ℂ) (BlockHardySpace r) ↥hardySubmoduleᗮ).sum_mem fun j _ ↦ by
      rw [blockSymbolEntry_toLp]; exact (isCompactOperator_hankel_toLp _).comp_clm _
  let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ↥hardySubmoduleᗮ)).symm
  convert (IsCompactOperator.pi hrow).clm_comp
    ((blockHardyOrthogonalEquiv r).symm.toLinearIsometry.toContinuousLinearMap ∘L
      e.toContinuousLinearMap) using 1
  ext f : 1; apply (blockHardyOrthogonalEquiv r).injective; ext i : 1
  simp [row, e, blockHardyOrthogonalEquiv_blockHankel_apply]

/-- **Compactness of block Toeplitz semicommutators** when the right symbol is continuous. -/
theorem isCompactOperator_blockToeplitz_comp_sub_blockToeplitz_toLp {r : ℕ} (A : BlockSymbol r)
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    IsCompactOperator (blockToeplitz r A ∘L
        blockToeplitz r (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F) -
      blockToeplitz r (A * ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F)) := by
  rw [blockToeplitz_comp_sub_blockToeplitz, FunLike.coe_neg, coe_comp]
  exact ((isCompactOperator_blockHankel_toLp F).clm_comp _).neg

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Toeplitz
public import TauCeti.Analysis.Fourier.Hardy.Compact

/-!
# Block Hankel operators, Toeplitz products, and continuous-symbol compactness

For an operator-valued symbol `A : BlockSymbol r` on `UnitAddCircle`, the block Hankel operator
`TauCeti.blockHankel r A : BlockHardySpace r →L[ℂ] ↥(blockHardySubmodule r)ᗮ` applies the `L²`
operator multiplier `Lp.operatorMultiplication 2 A` to a block Hardy function and projects onto the
actual orthogonal complement `↥(blockHardySubmodule r)ᗮ` of `blockHardySubmodule r` inside
`Lp (EuclideanSpace ℂ (Fin r)) 2 haarAddCircle`.

## Main definitions

* `TauCeti.blockHankel`: the bounded complex-linear block Hankel symbol map
  `BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] ↥(blockHardySubmodule r)ᗮ`.

## Main results

* `TauCeti.coe_blockToeplitz_add_coe_blockHankel`: orthogonal splitting of `M_A` on block Hardy
  functions into its block Toeplitz and block Hankel parts.
* `TauCeti.blockHardyOrthogonalEquiv_blockHankel_apply`: under `blockHardyOrthogonalEquiv r`,
  `blockHankel r A` acts coordinatewise through the scalar Hankel operators of `blockSymbolEntry`.
* `TauCeti.blockToeplitz_comp_sub_blockToeplitz`: **block Toeplitz semicommutator identity**
  `T_A ∘L T_B - T_{A • B} = -(H_{star A}† ∘L H_B)`.
* `TauCeti.blockHankel_eq_zero_iff`: `blockHankel r A = 0` iff all negative operator-valued Fourier
  coefficients of `A` vanish.
* `TauCeti.blockToeplitz_comp_of_analytic`, `TauCeti.blockToeplitz_comp_of_coanalytic`:
  `T_A ∘L T_B = T_{A • B}` when `B` is analytic or `A` is coanalytic.
* `TauCeti.isCompactOperator_blockHankel_toLp`,
  `TauCeti.isCompactOperator_blockToeplitz_comp_sub_blockToeplitz_toLp`: compactness of block
  Hankel operators and block Toeplitz semicommutators for continuous matrix symbols.

## References

* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.9.
* J. B. Conway, *A Course in Functional Analysis*, second edition.
* E. Park, *Toeplitz operators*.
-/

public section

noncomputable section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

private theorem norm_compress_blockHankel_le {r : ℕ} (A : BlockSymbol r) :
    ‖(blockHardySubmodule r)ᗮ.orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry]
  exact ((blockHardySubmodule r)ᗮ.norm_orthogonalProjectionOnto_apply_le _).trans <|
    (Lp.norm_operatorMultiplication_apply_le (p := 2) A _).trans <| by
      rw [Submodule.subtypeL_apply, Submodule.norm_coe, LinearIsometryEquiv.norm_map]

/-- The block Hankel symbol map `H_A = (1 - P) M_A |H²`, mapping `BlockHardySpace r` into the
actual orthogonal complement `↥(blockHardySubmodule r)ᗮ` of `blockHardySubmodule r`. -/
def blockHankel (r : ℕ) :
    BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] ↥(blockHardySubmodule r)ᗮ :=
  LinearMap.mkContinuous
    { toFun A := (blockHardySubmodule r)ᗮ.orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap
      map_add' A B := by
        simp only [Lp.operatorMultiplication_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c A := by
        simp only [Lp.operatorMultiplication_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun A ↦ (one_mul ‖A‖).symm ▸ norm_compress_blockHankel_le A

/-- Definition of `blockHankel r A` as projection onto `(blockHardySubmodule r)ᗮ` after
`Lp.operatorMultiplication 2 A`. -/
theorem blockHankel_apply (r : ℕ) (A : BlockSymbol r) :
    blockHankel r A =
      (blockHardySubmodule r)ᗮ.orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap :=
  (rfl)

/-- The ambient `L²` value of `blockHankel r A f` is the complementary block Hardy projection of
`Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f)`. -/
theorem coe_blockHankel_apply {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) :
    (blockHankel r A f :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) =
      Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f) -
        (blockHardySubmodule r).starProjection
          (Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f)) := by
  rw [blockHankel_apply]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, Submodule.subtypeL_apply,
    ← Submodule.starProjection_apply, Submodule.starProjection_orthogonal_val]

/-- Operator multiplication on a block Hardy function decomposes into its block Toeplitz and block
Hankel parts in ambient vector-valued `L²`. -/
theorem coe_blockToeplitz_add_coe_blockHankel {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) :
    ((blockHardyEquiv r).symm (blockToeplitz r A f) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) +
      (blockHankel r A f :
        Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) =
      Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f) := by
  rw [coe_blockHardyEquiv_symm_blockToeplitz_apply, coe_blockHankel_apply]
  exact add_sub_cancel _ _

/-- Block Hankel compression does not increase the operator norm of its symbol. -/
theorem norm_blockHankel_le {r : ℕ} (A : BlockSymbol r) :
    ‖blockHankel r A‖ ≤ ‖A‖ :=
  norm_compress_blockHankel_le A

/-- Under `blockHardyOrthogonalEquiv r`, `blockHankel r A` acts on a vector concentrated in
coordinate `j` via the scalar Hankel operators of the `j`-th column of `A`. -/
@[simp]
theorem blockHardyOrthogonalEquiv_blockHankel_single {r : ℕ} (A : BlockSymbol r)
    (i j : Fin r) (h : HardySpace) :
    blockHardyOrthogonalEquiv r (blockHankel r A (PiLp.single 2 j h)) i =
      hankel (blockSymbolEntry r i j A) h := by
  rw [blockHankel_apply]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, Submodule.subtypeL_apply,
    blockHardyOrthogonalEquiv_orthogonalProjectionOnto]
  rw [coe_blockHardyEquiv_symm_single, piLpEquiv_operatorMultiplication_symm_single,
    hankel_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Lp.multiplicationOperator_apply]

/-- Under `blockHardyOrthogonalEquiv r`, `blockHankel r A` acts coordinatewise through the scalar
Hankel operators of `blockSymbolEntry r i j A`. -/
theorem blockHardyOrthogonalEquiv_blockHankel_apply {r : ℕ} (A : BlockSymbol r)
    (f : BlockHardySpace r) (i : Fin r) :
    blockHardyOrthogonalEquiv r (blockHankel r A f) i =
      ∑ j : Fin r, hankel (blockSymbolEntry r i j A) (f j) := by
  have hf : f = ∑ j : Fin r, PiLp.single 2 j (f j) := by
    ext k : 1
    simp [WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hf]
  simp only [map_sum, WithLp.ofLp_sum, Finset.sum_apply,
    blockHardyOrthogonalEquiv_blockHankel_single]

/-- Every constant matrix symbol has zero block Hankel operator. -/
@[simp]
theorem blockHankel_const {r : ℕ}
    (M : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :
    blockHankel r (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) M) = 0 := by
  ext f : 1
  apply (blockHardyOrthogonalEquiv r).injective
  ext i : 1
  rw [zero_apply, blockHardyOrthogonalEquiv_blockHankel_apply, map_zero, PiLp.zero_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [blockSymbolEntry_const, hankel_const, zero_apply]

/-- The adjoint of `blockHankel r A` multiplies negative-mode vector functions by `star A` and
projects back onto `BlockHardySpace r`. -/
theorem adjoint_blockHankel {r : ℕ} (A : BlockSymbol r) :
    ContinuousLinearMap.adjoint (blockHankel r A) =
      (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 (star A) ∘L
        (blockHardySubmodule r)ᗮ.subtypeL := by
  have hadj_equiv :
      ContinuousLinearMap.adjoint (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap =
        (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap := by
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
    simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [← (blockHardyEquiv r).symm.inner_map_map, LinearIsometryEquiv.symm_apply_apply]
  simp only [blockHankel_apply, ContinuousLinearMap.adjoint_comp, hadj_equiv,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto,
    Lp.adjoint_operatorMultiplication, ContinuousLinearMap.comp_assoc]

/-- **Block Toeplitz semicommutator identity.** The multiplicative defect of block Toeplitz
compression is minus the composition of `(blockHankel r (star A))†` with `blockHankel r B`. -/
theorem blockToeplitz_comp_sub_blockToeplitz {r : ℕ} (A B : BlockSymbol r) :
    blockToeplitz r A ∘L blockToeplitz r B -
      blockToeplitz r (A • B : BlockSymbol r) =
      -(ContinuousLinearMap.adjoint (blockHankel r (star A)) ∘L blockHankel r B) := by
  ext f : 1
  apply (blockHardyEquiv r).symm.injective
  apply Subtype.ext
  have hmul := DFunLike.congr_fun
    (Lp.operatorMultiplication_comp_operatorMultiplication (p := 2) A B)
    ((blockHardyEquiv r).symm f :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1)))
  rw [ContinuousLinearMap.comp_apply] at hmul
  simp only [ContinuousLinearMap.comp_apply, sub_apply, neg_apply, map_sub, map_neg,
    Submodule.coe_sub, Submodule.coe_neg, coe_blockHardyEquiv_symm_blockToeplitz_apply,
    adjoint_blockHankel, star_star, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply, coe_blockHankel_apply]
  rw [← hmul]
  abel

/-- A block Hankel operator vanishes if and only if all negative operator-valued Fourier
coefficients of its symbol vanish. -/
theorem blockHankel_eq_zero_iff {r : ℕ} (A : BlockSymbol r) :
    blockHankel r A = 0 ↔ ∀ n : ℤ, n < 0 → fourierCoeff A n = 0 := by
  constructor
  · intro hA n hn
    refine ContinuousLinearMap.ext fun v ↦ PiLp.ext fun i ↦ ?_
    have hv : v = ∑ j : Fin r, v j • EuclideanSpace.single j (1 : ℂ) := by
      ext m
      simp [EuclideanSpace.single, Pi.single_apply]
    rw [zero_apply, PiLp.zero_apply, hv, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hij : hankel (blockSymbolEntry r i j A) = 0 := by
      ext h : 1
      have hzero := congrArg (fun H ↦ blockHardyOrthogonalEquiv r (H (PiLp.single 2 j h)) i) hA
      simpa using hzero
    rw [map_smul, PiLp.smul_apply, ← fourierCoeff_blockSymbolEntry,
      (hankel_eq_zero_iff _).mp hij n hn, smul_zero]
  · intro hA
    ext f : 1
    apply (blockHardyOrthogonalEquiv r).injective
    ext i : 1
    rw [blockHardyOrthogonalEquiv_blockHankel_apply, zero_apply, map_zero, PiLp.zero_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hij : hankel (blockSymbolEntry r i j A) = 0 := by
      rw [hankel_eq_zero_iff]
      intro n hn
      rw [fourierCoeff_blockSymbolEntry, hA n hn, zero_apply, PiLp.zero_apply]
    rw [hij, zero_apply]

/-- Block Toeplitz multiplication `T_A ∘L T_B = T_{A • B}` is exact when the right symbol `B` is
analytic (its negative Fourier coefficients vanish). -/
theorem blockToeplitz_comp_of_analytic {r : ℕ} (A B : BlockSymbol r)
    (hB : ∀ n : ℤ, n < 0 → fourierCoeff B n = 0) :
    blockToeplitz r A ∘L blockToeplitz r B = blockToeplitz r (A • B : BlockSymbol r) := by
  ext f : 1
  have hf := congrArg (fun T ↦ T f) (blockToeplitz_comp_sub_blockToeplitz A B)
  simpa only [sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
    (blockHankel_eq_zero_iff B).mpr hB, zero_apply, map_zero, neg_zero, sub_eq_zero] using hf

/-- Block Toeplitz multiplication `T_A ∘L T_B = T_{A • B}` is exact when the left symbol `A` is
coanalytic (the negative Fourier coefficients of `star A` vanish). -/
theorem blockToeplitz_comp_of_coanalytic {r : ℕ} (A B : BlockSymbol r)
    (hA : ∀ n : ℤ, n < 0 → fourierCoeff (star A : BlockSymbol r) n = 0) :
    blockToeplitz r A ∘L blockToeplitz r B = blockToeplitz r (A • B : BlockSymbol r) := by
  ext f : 1
  have hf := congrArg (fun T ↦ T f) (blockToeplitz_comp_sub_blockToeplitz A B)
  simpa only [sub_apply, neg_apply, ContinuousLinearMap.comp_apply,
    (blockHankel_eq_zero_iff (star A)).mpr hA, ContinuousLinearMap.adjoint.map_zero,
    zero_apply, neg_zero, sub_eq_zero] using hf

/-- Extracting the `(i, j)` scalar entry commutes with `ContinuousMap.toLp ∞`. -/
theorem blockSymbolEntry_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)))
    (i j : Fin r) :
    blockSymbolEntry r i j (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F) =
      ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ
        ((ContinuousMap.mk (euclideanMatrixEntryCLM r i j)
          (euclideanMatrixEntryCLM r i j).continuous).comp F) := by
  apply Lp.ext
  filter_upwards [blockSymbolEntry_ae i j
      (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F),
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1)) F,
    ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (AddCircle.haarAddCircle (T := 1))
      ((ContinuousMap.mk (euclideanMatrixEntryCLM r i j)
        (euclideanMatrixEntryCLM r i j).continuous).comp F)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp

private theorem isCompactOperator_finset_sum {ι M₁ M₂ : Type*} [TopologicalSpace M₁]
    [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [ContinuousAdd M₂]
    (s : Finset ι) {f : ι → M₁ → M₂} (hf : ∀ i ∈ s, IsCompactOperator (f i)) :
    IsCompactOperator (fun x ↦ ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty, Pi.zero_def] using
        (isCompactOperator_zero (M₁ := M₁) (M₂ := M₂))
  | insert a s ha ih =>
      simpa only [Finset.sum_insert ha, Pi.add_def] using
        (hf a (Finset.mem_insert_self a s)).add
          (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-- **Compactness of continuous-symbol block Hankel operators.** For a continuous matrix symbol `F`
on the unit circle, `blockHankel r (ContinuousMap.toLp ∞ haarAddCircle ℂ F)` is compact. -/
theorem isCompactOperator_blockHankel_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    IsCompactOperator
      (blockHankel r (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F)) := by
  set A : BlockSymbol r := ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F
  let incl (i : Fin r) : ↥hardySubmoduleᗮ →L[ℂ] PiLp 2 (fun _ : Fin r ↦ ↥hardySubmoduleᗮ) :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ↥hardySubmoduleᗮ)).symm.toContinuousLinearMap
      ∘L ContinuousLinearMap.single ℂ (fun _ : Fin r ↦ ↥hardySubmoduleᗮ) i
  have hincl (i : Fin r) (g : ↥hardySubmoduleᗮ) : incl i g = PiLp.single 2 i g := rfl
  have hdecomp : (blockHankel r A : BlockHardySpace r → ↥(blockHardySubmodule r)ᗮ) =
      (blockHardyOrthogonalEquiv r).symm ∘ fun f ↦
        ∑ i : Fin r, incl i (∑ j : Fin r, hankel (blockSymbolEntry r i j A) (f j)) := by
    funext f
    apply (blockHardyOrthogonalEquiv r).injective
    rw [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    ext k : 1
    rw [blockHardyOrthogonalEquiv_blockHankel_apply]
    simp [hincl, WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]
  rw [hdecomp]
  refine (isCompactOperator_finset_sum Finset.univ fun i _ ↦ ?_).continuous_comp
    (blockHardyOrthogonalEquiv r).symm.continuous
  have hi : (fun f : BlockHardySpace r ↦
        incl i (∑ j : Fin r, hankel (blockSymbolEntry r i j A) (f j))) =
      incl i ∘ fun f ↦ ∑ j : Fin r, hankel (blockSymbolEntry r i j A) (f j) := rfl
  rw [hi]
  refine (isCompactOperator_finset_sum Finset.univ fun j _ ↦ ?_).clm_comp (incl i)
  have hproj : (fun f : BlockHardySpace r ↦ hankel (blockSymbolEntry r i j A) (f j)) =
      hankel (blockSymbolEntry r i j A) ∘
        PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ HardySpace) j := rfl
  rw [hproj, blockSymbolEntry_toLp]
  exact (isCompactOperator_hankel_toLp _).comp_clm _

/-- **Compactness of block Toeplitz semicommutators.** For any essentially bounded block symbol `A`
and any continuous matrix symbol `F` on the unit circle, the semicommutator
`T_A ∘L T_F - T_{A • F}` is compact. -/
theorem isCompactOperator_blockToeplitz_comp_sub_blockToeplitz_toLp {r : ℕ}
    (A : BlockSymbol r)
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    IsCompactOperator (blockToeplitz r A ∘L
        blockToeplitz r (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F) -
      blockToeplitz r
        (A • ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F : BlockSymbol r)) := by
  rw [blockToeplitz_comp_sub_blockToeplitz, FunLike.coe_neg, ContinuousLinearMap.coe_comp]
  exact ((isCompactOperator_blockHankel_toLp F).clm_comp _).neg

end TauCeti

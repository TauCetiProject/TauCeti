/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Basic
public import TauCeti.Analysis.Fourier.Hardy.BrownHalmos
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous

/-!
# Block Toeplitz operators and the block Brown–Halmos theorem

For an essentially bounded operator-valued symbol `A : BlockSymbol r` on `UnitAddCircle`, the block
Toeplitz operator `TauCeti.blockToeplitz r A : BlockHardySpace r →L[ℂ] BlockHardySpace r` compresses
the `L²` operator multiplier `MeasureTheory.Lp.operatorMultiplication 2 A` onto the nonnegative-mode
subspace `blockHardySubmodule r`, conjugated by the unitary identification `blockHardyEquiv r` with
`BlockHardySpace r = PiLp 2 (fun _ : Fin r ↦ HardySpace)`.

## Main definitions

* `TauCeti.blockToeplitz`: the bounded complex-linear block Toeplitz symbol map
  `BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] BlockHardySpace r`.

## Main results

* `TauCeti.piLpEntry_blockToeplitz`, `TauCeti.blockToeplitz_apply_apply`: the `(i, j)` Hilbert-sum
  block entry of `blockToeplitz r A` is the scalar Toeplitz operator of `blockSymbolEntry r i j A`.
* `TauCeti.inner_blockHardyBasis_blockToeplitz_blockHardyBasis`: in `blockHardyBasis r`, the matrix
  entry between `(m, i)` and `(n, j)` is `⟪e_i, â(m - n) e_j⟫ = (A_{i,j})^(m - n)`.
* `TauCeti.adjoint_blockToeplitz`: `(blockToeplitz r A)† = blockToeplitz r (star A)`.
* `TauCeti.blockToeplitz_smul_const_one`, `TauCeti.blockToeplitz_const_one`: scalar symbols tensor
  the identity act diagonally via `PiLp.diagStarAlgHom`, and the constant unit acts as the identity;
  in particular the block forward shift raises `blockHardyBasis r (n, i)` to `(n + 1, i)`.
* `TauCeti.norm_blockToeplitz`, `TauCeti.isometry_blockToeplitz`, `TauCeti.norm_blockToeplitz_toLp`:
  `‖blockToeplitz r A‖ = ‖A‖`, so `blockToeplitz r` is an isometry, and for continuous matrix
  symbols `F` the operator norm of `blockToeplitz r (ContinuousMap.toLp ∞ haarAddCircle ℂ F)`
  equals the uniform operator norm `‖F‖`.
* `TauCeti.exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ`,
  `TauCeti.existsUnique_blockToeplitz_eq_iff_adjoint_comp_comp_eq`: **block Brown–Halmos theorem**
  characterizing block Toeplitz operators by block-diagonal shift invariance or intertwining with
  the block forward shift.

## References

* A. Brown and P. R. Halmos, *Algebraic properties of Toeplitz operators*, J. Reine Angew. Math.
  213 (1964), 89–102.
* A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators*, second edition, §2.9.
* J. B. Conway, *A Course in Functional Analysis*, second edition.
* E. Park, *Toeplitz operators*.
-/

public section

noncomputable section

open MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

private theorem norm_compress_operatorMultiplication_le {r : ℕ} (A : BlockSymbol r) :
    ‖(blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro f
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map]
  exact ((blockHardySubmodule r).norm_orthogonalProjectionOnto_apply_le _).trans <|
    (Lp.norm_operatorMultiplication_apply_le (p := 2) A _).trans <| by
      rw [Submodule.subtypeL_apply, Submodule.norm_coe, LinearIsometryEquiv.norm_map]

/-- The block Toeplitz symbol map, sending an essentially bounded `(r × r)` matrix symbol
`A : BlockSymbol r` on the unit circle to the compression of `Lp.operatorMultiplication 2 A` onto
`BlockHardySpace r`. -/
def blockToeplitz (r : ℕ) :
    BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] BlockHardySpace r :=
  LinearMap.mkContinuous
    { toFun A := (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap
      map_add' A B := by
        simp only [Lp.operatorMultiplication_add, ContinuousLinearMap.add_comp,
          ContinuousLinearMap.comp_add]
      map_smul' c A := by
        simp only [Lp.operatorMultiplication_smul, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, RingHom.id_apply] }
    1 fun A ↦ (one_mul ‖A‖).symm ▸ norm_compress_operatorMultiplication_le A

/-- Definition of `blockToeplitz r A` as compression of `Lp.operatorMultiplication 2 A`. -/
theorem blockToeplitz_apply (r : ℕ) (A : BlockSymbol r) :
    blockToeplitz r A =
      (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L
        Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap :=
  (rfl)

/-- Under `(blockHardyEquiv r).symm`, the ambient `L²` value of `blockToeplitz r A f` is the
orthogonal projection onto `blockHardySubmodule r` of `Lp.operatorMultiplication 2 A` applied to
`(blockHardyEquiv r).symm f`. -/
theorem coe_blockHardyEquiv_symm_blockToeplitz_apply {r : ℕ} (A : BlockSymbol r)
    (f : BlockHardySpace r) :
    ((blockHardyEquiv r).symm (blockToeplitz r A f) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) =
      (blockHardySubmodule r).starProjection
        (Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f)) := by
  rw [blockToeplitz_apply]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply]

/-- Compressing to `BlockHardySpace r` preserves inner products against block Hardy vectors. -/
theorem inner_blockToeplitz_apply {r : ℕ} (A : BlockSymbol r) (f g : BlockHardySpace r) :
    ⟪f, blockToeplitz r A g⟫_ℂ =
      ⟪((blockHardyEquiv r).symm f :
          Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))),
        Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm g)⟫_ℂ := by
  rw [← (blockHardyEquiv r).symm.inner_map_map, blockToeplitz_apply]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.symm_apply_apply,
    Submodule.subtypeL_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

/-- On a vector concentrated in coordinate `j`, `Lp.operatorMultiplication 2 A` acts in coordinate
`i` by heterogeneous scalar multiplication by `blockSymbolEntry r i j A`. -/
theorem piLpEquiv_operatorMultiplication_symm_single {r : ℕ} (A : BlockSymbol r)
    (i j : Fin r) (h : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (AddCircle.haarAddCircle (T := 1))
      (Lp.operatorMultiplication 2 A
        ((Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (AddCircle.haarAddCircle (T := 1))).symm
          (PiLp.single 2 j h))) i =
      (blockSymbolEntry r i j A • h : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))) := by
  set e := Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (AddCircle.haarAddCircle (T := 1))
  apply Lp.ext
  filter_upwards [Lp.coeFn_piLpEquiv_apply (𝕜 := ℂ)
      (Lp.operatorMultiplication 2 A (e.symm (PiLp.single 2 j h))) i,
    Lp.operatorMultiplication_ae (p := 2) A (e.symm (PiLp.single 2 j h)),
    Lp.coeFn_piLpEquiv_symm_single (p := 2) (𝕜 := ℂ) (E := fun _ : Fin r ↦ ℂ) j h,
    Lp.coeFn_lpSMul (r := 2) (blockSymbolEntry r i j A) h,
    blockSymbolEntry_ae i j A] with x h₁ h₂ h₃ h₄ h₅
  have hsingle : (PiLp.single 2 j (h x) : EuclideanSpace ℂ (Fin r)) =
      h x • EuclideanSpace.single j (1 : ℂ) := by ext k; simp [EuclideanSpace.single]
  rw [h₁, h₂, h₃, hsingle, map_smul, PiLp.smul_apply, h₄, Pi.smul_apply', h₅, smul_eq_mul,
    smul_eq_mul, mul_comm]

/-- A block Hardy vector concentrated in coordinate `j` embeds into ambient vector `L²` as a single
coordinate under `Lp.piLpEquiv`. -/
theorem coe_blockHardyEquiv_symm_single {r : ℕ} (j : Fin r) (h : HardySpace) :
    ((blockHardyEquiv r).symm (PiLp.single 2 j h) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) =
      (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (AddCircle.haarAddCircle (T := 1))).symm
        (PiLp.single 2 j (h : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)))) := by
  apply (Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (AddCircle.haarAddCircle (T := 1))).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext k : 1
  rw [piLpEquiv_coe_blockHardyEquiv_symm]
  by_cases hkj : k = j <;> simp [hkj]

/-- The `(i, j)` block entry of `blockToeplitz r A` is the scalar Toeplitz operator of the `(i, j)`
entry of `A`. -/
@[simp]
theorem piLpEntry_blockToeplitz {r : ℕ} (A : BlockSymbol r) (i j : Fin r) :
    (blockToeplitz r A).piLpEntry i j = toeplitz (blockSymbolEntry r i j A) := by
  ext h : 1
  rw [ContinuousLinearMap.piLpEntry_apply, blockToeplitz_apply]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, Submodule.subtypeL_apply,
    blockHardyEquiv_orthogonalProjectionOnto]
  rw [coe_blockHardyEquiv_symm_single, piLpEquiv_operatorMultiplication_symm_single,
    toeplitz_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Lp.multiplicationOperator_apply]

/-- Coordinatewise action of a block Toeplitz operator through scalar Toeplitz operators of the
matrix entries of its symbol. -/
theorem blockToeplitz_apply_apply {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) (i : Fin r) :
    blockToeplitz r A f i = ∑ j : Fin r, toeplitz (blockSymbolEntry r i j A) (f j) := by
  rw [ContinuousLinearMap.apply_eq_sum_piLpEntry]
  simp only [piLpEntry_blockToeplitz]

/-- In `blockHardyBasis r`, matrix elements of any operator `T` on `BlockHardySpace r` are the
Hardy-basis matrix elements of its `piLpEntry` blocks. -/
theorem inner_blockHardyBasis_apply {r : ℕ} (T : BlockHardySpace r →L[ℂ] BlockHardySpace r)
    (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), T (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪hardyBasis m, T.piLpEntry i j (hardyBasis n)⟫_ℂ := by
  rw [blockHardyBasis_apply, blockHardyBasis_apply, PiLp.inner_apply,
    Finset.sum_eq_single i (fun k _ hki ↦ by simp [hki]) (by simp)]
  simp

/-- **Block matrix Fourier-entry formula (operator form).** In `blockHardyBasis r`, the matrix
element between `(m, i)` and `(n, j)` of `blockToeplitz r A` is the `(i, j)` entry of the
operator-valued Fourier coefficient `fourierCoeff A (m - n)`. -/
theorem inner_blockHardyBasis_blockToeplitz_blockHardyBasis {r : ℕ} (A : BlockSymbol r)
    (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), blockToeplitz r A (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪EuclideanSpace.single i (1 : ℂ),
        fourierCoeff A ((m : ℤ) - n) (EuclideanSpace.single j (1 : ℂ))⟫_ℂ := by
  rw [inner_blockHardyBasis_apply, piLpEntry_blockToeplitz, inner_hardyBasis_toeplitz_hardyBasis,
    inner_single_fourierCoeff_blockSymbol]

/-- Scalar-entry form of `inner_blockHardyBasis_blockToeplitz_blockHardyBasis`. -/
theorem inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_entry {r : ℕ} (A : BlockSymbol r)
    (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), blockToeplitz r A (blockHardyBasis r (n, j))⟫_ℂ =
      fourierCoeff (blockSymbolEntry r i j A) ((m : ℤ) - n) := by
  rw [inner_blockHardyBasis_blockToeplitz_blockHardyBasis, inner_single_fourierCoeff_blockSymbol]

/-- The adjoint of `blockToeplitz r A` is the block Toeplitz operator of the pointwise Hilbert-space
adjoint symbol `star A`. -/
@[simp]
theorem adjoint_blockToeplitz {r : ℕ} (A : BlockSymbol r) :
    ContinuousLinearMap.adjoint (blockToeplitz r A) = blockToeplitz r (star A) := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g ↦ ?_).symm
  rw [inner_blockToeplitz_apply, ← inner_conj_symm, inner_blockToeplitz_apply, inner_conj_symm,
    ← ContinuousLinearMap.adjoint_inner_left, Lp.adjoint_operatorMultiplication]

/-- The `(i, j)` scalar entry of a constant matrix symbol is the corresponding constant scalar
symbol. -/
@[simp]
theorem blockSymbolEntry_const {r : ℕ}
    (M : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) (i j : Fin r) :
    blockSymbolEntry r i j (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) M) =
      Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) (M (EuclideanSpace.single j 1) i) := by
  apply Lp.ext
  filter_upwards [blockSymbolEntry_ae i j (Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) M),
    Lp.coeFn_const ∞ (AddCircle.haarAddCircle (T := 1)) M,
    Lp.coeFn_const ∞ (AddCircle.haarAddCircle (T := 1))
      (M (EuclideanSpace.single j 1) i)] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]; rfl

/-- The `(i, j)` scalar entry of a scalar symbol tensor the identity matrix is `a` on the diagonal
and `0` off the diagonal. -/
theorem blockSymbolEntry_smul_const_one {r : ℕ}
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) (i j : Fin r) :
    blockSymbolEntry r i j
      (a • Lp.const ∞ (AddCircle.haarAddCircle (T := 1))
        (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) : BlockSymbol r) =
      if i = j then a else 0 := by
  let oneSym : BlockSymbol r := Lp.const ∞ (AddCircle.haarAddCircle (T := 1)) 1
  have hone := Lp.coeFn_const ∞ (AddCircle.haarAddCircle (T := 1))
    (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
  by_cases hij : i = j
  · subst hij; rw [ite_eq_left rfl]; apply Lp.ext
    filter_upwards [blockSymbolEntry_ae i i (a • oneSym), Lp.coeFn_lpSMul (r := ∞) a oneSym,
      hone] with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply', h₃]; simp [EuclideanSpace.single]
  · rw [ite_eq_right hij]; apply Lp.ext
    filter_upwards [blockSymbolEntry_ae i j (a • oneSym), Lp.coeFn_lpSMul (r := ∞) a oneSym,
      hone, Lp.coeFn_zero ℂ ∞ (AddCircle.haarAddCircle (T := 1))] with x h₁ h₂ h₃ h₀
    rw [h₁, h₂, Pi.smul_apply', h₃, h₀]; simp [EuclideanSpace.single, hij]

/-- A scalar symbol tensor the identity matrix acts on `BlockHardySpace r` by diagonal amplification
of its scalar Toeplitz operator. -/
theorem blockToeplitz_smul_const_one {r : ℕ}
    (a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1))) :
    blockToeplitz r
      (a • Lp.const ∞ (AddCircle.haarAddCircle (T := 1))
        (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) : BlockSymbol r) =
      PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz a) := by
  ext f i : 2
  rw [blockToeplitz_apply_apply, ContinuousLinearMap.apply_eq_sum_piLpEntry]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [blockSymbolEntry_smul_const_one, ContinuousLinearMap.piLpEntry_diagStarAlgHom]
  split_ifs <;> simp

/-- The constant identity symbol acts as the identity operator on `BlockHardySpace r`. -/
theorem blockToeplitz_const_one (r : ℕ) :
    blockToeplitz r
      (Lp.const ∞ (AddCircle.haarAddCircle (T := 1))
        (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) =
      ContinuousLinearMap.id ℂ (BlockHardySpace r) := by
  ext f i : 2
  rw [blockToeplitz_apply_apply]
  simp only [blockSymbolEntry_const, one_apply_eq_self, EuclideanSpace.single, PiLp.single_apply]
  rw [Finset.sum_eq_single i (fun j _ hji ↦ by simp [hji.symm]) (by simp)]
  simp

/-- The block forward shift `T_{z I}` raises `blockHardyBasis r (n, i)` to
`blockHardyBasis r (n + 1, i)`. -/
theorem blockToeplitz_fourierLp_one_smul_const_one_blockHardyBasis {r : ℕ} (n : ℕ) (i : Fin r) :
    blockToeplitz r
      (fourierLp (T := 1) ∞ 1 • Lp.const ∞ (AddCircle.haarAddCircle (T := 1))
        (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) : BlockSymbol r)
      (blockHardyBasis r (n, i)) = blockHardyBasis r (n + 1, i) := by
  rw [blockToeplitz_smul_const_one, blockHardyBasis_apply, PiLp.diagStarAlgHom_apply_single,
    toeplitz_fourierLp_one_hardyBasis, blockHardyBasis_apply]

/-- The operator norm of `blockToeplitz r A` is at most the `L∞` operator norm of `A`. -/
theorem norm_blockToeplitz_le {r : ℕ} (A : BlockSymbol r) :
    ‖blockToeplitz r A‖ ≤ ‖A‖ :=
  norm_compress_operatorMultiplication_le A

private theorem norm_inner_operatorMultiplication_le_of_mem_span {r : ℕ} (A : BlockSymbol r)
    {f g : Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))}
    (hf : f ∈ Submodule.span ℂ (Set.range fun p : ℤ × Fin r ↦ blockFourierMode r p.1 p.2))
    (hg : g ∈ Submodule.span ℂ (Set.range fun p : ℤ × Fin r ↦ blockFourierMode r p.1 p.2)) :
    ‖⟪f, Lp.operatorMultiplication 2 A g⟫_ℂ‖ ≤ ‖blockToeplitz r A‖ * ‖f‖ * ‖g‖ := by
  obtain ⟨N, hfN, hgN⟩ := ((eventually_fourierLp_smul_mem_blockHardySubmodule hf).and
    (eventually_fourierLp_smul_mem_blockHardySubmodule hg)).exists
  have hu := ae_norm_fourierLp_eq_one (T := 1) ∞ N
  have hnorm (h : Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1))) :
      ‖(fourierLp (T := 1) ∞ N • h :
        Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1)))‖ = ‖h‖ := by
    rw [← Lp.multiplicationOperator_apply,
      Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one hu]
  set f' : BlockHardySpace r := blockHardyEquiv r ⟨_, hfN⟩
  set g' : BlockHardySpace r := blockHardyEquiv r ⟨_, hgN⟩
  have hinner : ⟪f, Lp.operatorMultiplication 2 A g⟫_ℂ = ⟪f', blockToeplitz r A g'⟫_ℂ := by
    rw [inner_blockToeplitz_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, Submodule.coe_mk, Submodule.coe_mk,
      Lp.operatorMultiplication_lpSMul, ← Lp.multiplicationOperator_apply,
      ← Lp.multiplicationOperator_apply]
    exact ((LinearMap.norm_map_iff_inner_map_map
      (Lp.multiplicationOperator (E := EuclideanSpace ℂ (Fin r)) (fourierLp (T := 1) ∞ N))).1
        (Lp.norm_multiplicationOperator_apply_of_ae_norm_eq_one hu) f
          (Lp.operatorMultiplication 2 A g)).symm
  calc ‖⟪f, Lp.operatorMultiplication 2 A g⟫_ℂ‖
      ≤ ‖f'‖ * (‖blockToeplitz r A‖ * ‖g'‖) := by
          rw [hinner]
          exact (norm_inner_le_norm _ _).trans
            (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ = ‖blockToeplitz r A‖ * ‖f‖ * ‖g‖ := by
          have hf' : ‖f'‖ = ‖f‖ := by rw [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, hnorm]
          have hg' : ‖g'‖ = ‖g‖ := by rw [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, hnorm]
          rw [hf', hg']; ring

private theorem norm_operatorMultiplication_le_norm_blockToeplitz {r : ℕ} (A : BlockSymbol r) :
    ‖Lp.operatorMultiplication 2 A‖ ≤ ‖blockToeplitz r A‖ := by
  have hD := dense_span_blockFourierMode r
  have hbound : ∀ p : Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1)) ×
      Lp (EuclideanSpace ℂ (Fin r)) 2 (AddCircle.haarAddCircle (T := 1)),
      ‖⟪p.1, Lp.operatorMultiplication 2 A p.2⟫_ℂ‖ ≤
        ‖blockToeplitz r A‖ * ‖p.1‖ * ‖p.2‖ := by
    refine (hD.prod hD).induction (fun p hp ↦ ?_) (isClosed_le (by fun_prop) (by fun_prop))
    exact norm_inner_operatorMultiplication_le_of_mem_span A hp.1 hp.2
  refine ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg (blockToeplitz r A)) ?_
  intro x y hx hy
  calc RCLike.re ⟪Lp.operatorMultiplication 2 A x, y⟫_ℂ
      ≤ ‖⟪Lp.operatorMultiplication 2 A x, y⟫_ℂ‖ := RCLike.re_le_norm _
    _ = ‖⟪y, Lp.operatorMultiplication 2 A x⟫_ℂ‖ := norm_inner_symm _ _
    _ ≤ ‖blockToeplitz r A‖ := by simpa only [hx, hy, mul_one] using hbound (y, x)

/-- **Block symbol norm.** The operator norm of `blockToeplitz r A` on `BlockHardySpace r` equals
the `L∞` operator norm of `A`. -/
@[simp]
theorem norm_blockToeplitz {r : ℕ} (A : BlockSymbol r) :
    ‖blockToeplitz r A‖ = ‖A‖ := by
  refine le_antisymm (norm_blockToeplitz_le A) ?_
  rw [← Lp.norm_operatorMultiplication (p := 2) A]
  exact norm_operatorMultiplication_le_norm_blockToeplitz A

/-- The block Toeplitz symbol map `A ↦ blockToeplitz r A` is an isometry. -/
theorem isometry_blockToeplitz (r : ℕ) : Isometry (blockToeplitz r) :=
  AddMonoidHomClass.isometry_of_norm (blockToeplitz r) norm_blockToeplitz

/-- A block symbol is uniquely determined by its block Toeplitz operator. -/
theorem blockToeplitz_injective (r : ℕ) : Function.Injective (blockToeplitz r) :=
  (isometry_blockToeplitz r).injective

/-- For a continuous operator-valued symbol `F` on the unit circle, the operator norm of its block
Toeplitz operator equals the uniform sup operator norm `‖F‖`. -/
theorem norm_blockToeplitz_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    ‖blockToeplitz r (ContinuousMap.toLp ∞ (AddCircle.haarAddCircle (T := 1)) ℂ F)‖ = ‖F‖ := by
  rw [norm_blockToeplitz, ContinuousMap.norm_toLp_top]

/-- An operator on `BlockHardySpace r` is a block Toeplitz operator if and only if its matrix in
`blockHardyBasis r` is invariant under shifting the mode index `(m, n) ↦ (m + 1, n + 1)` on every
`(i, j)` block. -/
theorem exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) :
    (∃ A : BlockSymbol r, blockToeplitz r A = T) ↔
      ∀ (m n : ℕ) (i j : Fin r),
        ⟪blockHardyBasis r (m + 1, i), T (blockHardyBasis r (n + 1, j))⟫_ℂ =
          ⟪blockHardyBasis r (m, i), T (blockHardyBasis r (n, j))⟫_ℂ := by
  constructor
  · rintro ⟨A, rfl⟩ m n i j
    rw [inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_entry,
      inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_entry]
    congr 1; push_cast; ring
  · intro h
    have hentry : ∀ i j : Fin r,
        ∃ a : Lp ℂ ∞ (AddCircle.haarAddCircle (T := 1)), toeplitz a = T.piLpEntry i j :=
      fun i j ↦ (exists_toeplitz_eq_iff_inner_hardyBasis_succ _).mpr fun m n ↦ by
        simpa only [inner_blockHardyBasis_apply] using h m n i j
    choose a ha using hentry
    refine ⟨∑ i : Fin r, ∑ j : Fin r, blockSymbolSingle r i j (a i j), ?_⟩
    ext f i : 2
    rw [blockToeplitz_apply_apply, ContinuousLinearMap.apply_eq_sum_piLpEntry]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hij : blockSymbolEntry r i j
        (∑ k : Fin r, ∑ l : Fin r, blockSymbolSingle r k l (a k l)) = a i j := by
      simp only [map_sum, blockSymbolEntry_blockSymbolSingle]
      rw [Finset.sum_eq_single i
        (fun k _ hki ↦ Finset.sum_eq_zero fun l _ ↦ by simp [hki.symm]) (by simp),
        Finset.sum_eq_single j (fun l _ hlj ↦ by simp [hlj.symm]) (by simp)]
      simp
    rw [hij, ha i j]

/-- **Block Brown–Halmos theorem.** A bounded operator `T` on `BlockHardySpace r` equals
`blockToeplitz r A` for a unique symbol `A : BlockSymbol r` if and only if `S_r† T S_r = T`, where
`S_r = PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp ∞ 1))` is the block forward
shift. -/
theorem existsUnique_blockToeplitz_eq_iff_adjoint_comp_comp_eq {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) :
    (∃! A : BlockSymbol r, blockToeplitz r A = T) ↔
      ContinuousLinearMap.adjoint
        (PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1))) ∘L T ∘L
        PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1)) = T := by
  set S := PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1))
  have hS (n : ℕ) (i : Fin r) : S (blockHardyBasis r (n, i)) = blockHardyBasis r (n + 1, i) := by
    simp only [S, blockHardyBasis_apply, PiLp.diagStarAlgHom_apply_single,
      toeplitz_fourierLp_one_hardyBasis]
  have hshift (m n : ℕ) (i j : Fin r) :
      ⟪blockHardyBasis r (m, i),
        (ContinuousLinearMap.adjoint S ∘L T ∘L S) (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪blockHardyBasis r (m + 1, i), T (blockHardyBasis r (n + 1, j))⟫_ℂ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right, hS, hS]
  have hexists : (∃ A : BlockSymbol r, blockToeplitz r A = T) ↔
      ContinuousLinearMap.adjoint S ∘L T ∘L S = T := by
    rw [exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ]
    refine ⟨fun h ↦ HilbertBasis.ext_inner_apply (blockHardyBasis r) (blockHardyBasis r)
      fun ⟨m, i⟩ ⟨n, j⟩ ↦ by rw [hshift, h], fun h m n i j ↦ by rw [← hshift, h]⟩
  refine ⟨fun ⟨A, hA, _⟩ ↦ hexists.1 ⟨A, hA⟩, fun h ↦ ?_⟩
  obtain ⟨A, hA⟩ := hexists.2 h
  exact ⟨A, hA, fun A' hA' ↦ blockToeplitz_injective r (hA'.trans hA.symm)⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Block.Basic
public import TauCeti.Analysis.Fourier.Hardy.BrownHalmos
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous

/-!
# Block Toeplitz operators and the block Brown–Halmos theorem

For `A : BlockSymbol r`, `TauCeti.blockToeplitz r A : BlockHardySpace r →L[ℂ] BlockHardySpace r`
compresses `MeasureTheory.Lp.operatorMultiplication 2 A` onto `blockHardySubmodule r` via
`blockHardyEquiv r`. Its `(i, j)` block entry is `toeplitz (blockSymbolEntry r i j A)`
(`TauCeti.piLpEntry_blockToeplitz`), its matrix in `blockHardyBasis r` has entries
`⟪e_i, â(m - n) e_j⟫` (`TauCeti.inner_blockHardyBasis_blockToeplitz_blockHardyBasis`),
`(blockToeplitz r A)† = blockToeplitz r (star A)` (`TauCeti.adjoint_blockToeplitz`), scalar symbols
act diagonally (`TauCeti.blockToeplitz_smul_one`, `TauCeti.blockToeplitz_one`,
`TauCeti.blockToeplitz_algebraMap`), and `‖blockToeplitz r A‖ = ‖A‖` (`TauCeti.norm_blockToeplitz`,
`TauCeti.isometry_blockToeplitz`, `TauCeti.norm_blockToeplitz_toLp`).

Finally, `TauCeti.exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ` and
`TauCeti.existsUnique_blockToeplitz_eq_iff_adjoint_comp_comp_eq` prove the **block Brown–Halmos
theorem**, characterizing block Toeplitz operators by mode-shift invariance
`(m, n) ↦ (m + 1, n + 1)` on every `(i, j)` block and compression invariance
`S_r† ∘L T ∘L S_r = T` under the block forward shift.

References: A. Brown and P. R. Halmos, *Algebraic properties of Toeplitz operators*, J. Reine Angew.
Math. 213 (1964), 89–102; A. Böttcher and B. Silbermann, *Analysis of Toeplitz Operators* (2nd ed.,
§2.9); J. B. Conway, *A Course in Functional Analysis* (2nd ed.); E. Park, *Toeplitz operators*.
-/

public noncomputable section

open AddCircle ContinuousLinearMap MeasureTheory Submodule
open scoped ENNReal InnerProductSpace

namespace TauCeti

/-- Block Toeplitz map compressing `Lp.operatorMultiplication 2` onto `BlockHardySpace r`. -/
def blockToeplitz (r : ℕ) : BlockSymbol r →L[ℂ] BlockHardySpace r →L[ℂ] BlockHardySpace r :=
  compL ℂ (BlockHardySpace r) (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))
      (BlockHardySpace r) ((blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto) ∘L
    (compL ℂ (BlockHardySpace r) (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))
        (Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1)))).flip
      ((blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap) ∘L
    Lp.operatorMultiplication 2

/-- Definition of `blockToeplitz r A` as compression of `Lp.operatorMultiplication 2 A`. -/
theorem blockToeplitz_apply (r : ℕ) (A : BlockSymbol r) :
    blockToeplitz r A =
      (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap ∘L
        (blockHardySubmodule r).orthogonalProjectionOnto ∘L Lp.operatorMultiplication 2 A ∘L
        (blockHardySubmodule r).subtypeL ∘L
        (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap := by
  simp only [blockToeplitz, comp_apply, compL_apply, flip_apply, comp_assoc]

/-- Ambient `L²` value of `blockToeplitz r A f` as `starProjection` onto `blockHardySubmodule r`. -/
theorem coe_blockHardyEquiv_symm_blockToeplitz_apply {r : ℕ} (A : BlockSymbol r)
    (f : BlockHardySpace r) :
    ((blockHardyEquiv r).symm (blockToeplitz r A f) :
      Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))) =
      (blockHardySubmodule r).starProjection
        (Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f)) := by
  simp [blockToeplitz_apply, coe_orthogonalProjectionOnto_apply]

/-- `blockToeplitz r A f = 0` iff `M_A f` lies in `(blockHardySubmodule r)ᗮ`. -/
theorem blockToeplitz_apply_eq_zero_iff {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) :
    blockToeplitz r A f = 0 ↔
      Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm f) ∈ (blockHardySubmodule r)ᗮ := by
  simp [blockToeplitz_apply, orthogonalProjectionOnto_eq_zero_iff]

/-- Compressing to `BlockHardySpace r` preserves inner products against block Hardy vectors. -/
theorem inner_blockToeplitz_apply {r : ℕ} (A : BlockSymbol r) (f g : BlockHardySpace r) :
    ⟪f, blockToeplitz r A g⟫_ℂ =
      ⟪((blockHardyEquiv r).symm f : Lp (EuclideanSpace ℂ (Fin r)) 2 (haarAddCircle (T := 1))),
        Lp.operatorMultiplication 2 A ((blockHardyEquiv r).symm g)⟫_ℂ := by
  rw [← (blockHardyEquiv r).symm.inner_map_map, blockToeplitz_apply]; simp

/-- On `single 2 j h`, `Lp.operatorMultiplication 2 A` acts in slot `i` by `blockSymbolEntry`. -/
theorem piLpEquiv_operatorMultiplication_symm_single {r : ℕ} (A : BlockSymbol r) (i j : Fin r)
    (h : Lp ℂ 2 (haarAddCircle (T := 1))) :
    Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
      (Lp.operatorMultiplication 2 A
        ((Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))).symm
          (PiLp.single 2 j h))) i =
      (blockSymbolEntry r i j A • h : Lp ℂ 2 (haarAddCircle (T := 1))) := Lp.ext <| by
  set e := Lp.piLpEquiv 2 ℂ (fun _ : Fin r ↦ ℂ) (haarAddCircle (T := 1))
  filter_upwards [Lp.coeFn_piLpEquiv_apply (𝕜 := ℂ)
      (Lp.operatorMultiplication 2 A (e.symm (PiLp.single 2 j h))) i,
    Lp.operatorMultiplication_ae (p := 2) A (e.symm (PiLp.single 2 j h)),
    Lp.coeFn_piLpEquiv_symm_single (p := 2) (𝕜 := ℂ) (E := fun _ : Fin r ↦ ℂ) j h,
    Lp.coeFn_lpSMul (r := 2) (blockSymbolEntry r i j A) h, blockSymbolEntry_ae i j A]
    with x h₁ h₂ h₃ h₄ h₅
  have hsingle : (PiLp.single 2 j (h x) : EuclideanSpace ℂ (Fin r)) =
      h x • EuclideanSpace.single j (1 : ℂ) := by ext k; simp [EuclideanSpace.single]
  rw [h₁, h₂, h₃, hsingle, map_smul, PiLp.smul_apply, h₄, Pi.smul_apply', h₅, smul_eq_mul,
    smul_eq_mul, mul_comm]

/-- The `(i, j)` block entry of `blockToeplitz r A` is `toeplitz (blockSymbolEntry r i j A)`. -/
@[simp] theorem piLpEntry_blockToeplitz {r : ℕ} (A : BlockSymbol r) (i j : Fin r) :
    (blockToeplitz r A).piLpEntry i j = toeplitz (blockSymbolEntry r i j A) := by
  ext h : 1; simp [piLpEntry_apply, blockToeplitz_apply, coe_blockHardyEquiv_symm_single,
    piLpEquiv_operatorMultiplication_symm_single, toeplitz_apply, Lp.multiplicationOperator_apply]

/-- Coordinatewise action of `blockToeplitz r A` through scalar Toeplitz entry operators. -/
theorem blockToeplitz_apply_apply {r : ℕ} (A : BlockSymbol r) (f : BlockHardySpace r) (i : Fin r) :
    blockToeplitz r A f i = ∑ j : Fin r, toeplitz (blockSymbolEntry r i j A) (f j) := by
  simp [apply_eq_sum_piLpEntry (blockToeplitz r A) f i]

/-- **Block matrix Fourier-entry formula (operator form).** -/
theorem inner_blockHardyBasis_blockToeplitz_blockHardyBasis {r : ℕ} (A : BlockSymbol r)
    (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), blockToeplitz r A (blockHardyBasis r (n, j))⟫_ℂ =
      ⟪EuclideanSpace.single i (1 : ℂ),
        fourierCoeff A ((m : ℤ) - n) (EuclideanSpace.single j (1 : ℂ))⟫_ℂ := by
  rw [inner_blockHardyBasis_apply, piLpEntry_blockToeplitz, inner_hardyBasis_toeplitz_hardyBasis,
    inner_single_fourierCoeff_blockSymbol]

/-- Scalar-entry form of `inner_blockHardyBasis_blockToeplitz_blockHardyBasis`. -/
theorem inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_fourierCoeff_blockSymbolEntry {r : ℕ}
    (A : BlockSymbol r) (m n : ℕ) (i j : Fin r) :
    ⟪blockHardyBasis r (m, i), blockToeplitz r A (blockHardyBasis r (n, j))⟫_ℂ =
      fourierCoeff (blockSymbolEntry r i j A) ((m : ℤ) - n) := by
  rw [inner_blockHardyBasis_blockToeplitz_blockHardyBasis, inner_single_fourierCoeff_blockSymbol]

/-- The adjoint of `blockToeplitz r A` is `blockToeplitz r (star A)`. -/
@[simp] theorem adjoint_blockToeplitz {r : ℕ} (A : BlockSymbol r) :
    adjoint (blockToeplitz r A) = blockToeplitz r (star A) :=
  ((eq_adjoint_iff _ _).2 fun f g ↦ by
    rw [inner_blockToeplitz_apply, ← inner_conj_symm, inner_blockToeplitz_apply, inner_conj_symm,
      ← adjoint_inner_left, Lp.adjoint_operatorMultiplication]).symm

/-- `a • (1 : BlockSymbol r)` acts diagonally via `PiLp.diagStarAlgHom ℂ HardySpace (Fin r)`. -/
theorem blockToeplitz_smul_one {r : ℕ} (a : Lp ℂ ∞ (haarAddCircle (T := 1))) :
    blockToeplitz r (a • (1 : BlockSymbol r) : BlockSymbol r) =
      PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz a) := by
  ext f i : 2; rw [blockToeplitz_apply_apply, apply_eq_sum_piLpEntry]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [blockSymbolEntry_smul_one, piLpEntry_diagStarAlgHom]; split_ifs <;> simp

/-- `1 : BlockSymbol r` induces the identity operator on `BlockHardySpace r`. -/
@[simp] theorem blockToeplitz_one (r : ℕ) :
    blockToeplitz r (1 : BlockSymbol r) = ContinuousLinearMap.id ℂ (BlockHardySpace r) := by
  ext f : 1; simp [blockToeplitz_apply]

/-- `algebraMap ℂ (BlockSymbol r) c` acts on `BlockHardySpace r` by scalar multiplication. -/
@[simp] theorem blockToeplitz_algebraMap {r : ℕ} (c : ℂ) :
    blockToeplitz r ((algebraMap ℂ (BlockSymbol r) : ℂ →+* BlockSymbol r) c) =
      c • ContinuousLinearMap.id ℂ (BlockHardySpace r) := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, blockToeplitz_one]

/-- The constant identity symbol acts as the identity operator on `BlockHardySpace r`. -/
@[simp] theorem blockToeplitz_const_one (r : ℕ) :
    blockToeplitz r (Lp.const ∞ (haarAddCircle (T := 1))
      (1 : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) =
      ContinuousLinearMap.id ℂ (BlockHardySpace r) := by
  have h := Lp.algebraMap_eq_const (R := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))
    (μ := haarAddCircle (T := 1)) (1 : ℂ)
  rw [map_one, map_one] at h; rw [← h, blockToeplitz_one]

/-- The block forward shift `T_{z I}` sends `blockHardyBasis r (n, i)` to `(n + 1, i)`. -/
theorem blockToeplitz_fourierLp_one_smul_one_blockHardyBasis {r : ℕ} (n : ℕ) (i : Fin r) :
    blockToeplitz r (fourierLp (T := 1) ∞ 1 • (1 : BlockSymbol r) : BlockSymbol r)
      (blockHardyBasis r (n, i)) = blockHardyBasis r (n + 1, i) := by
  rw [blockToeplitz_smul_one, blockHardyBasis_apply, PiLp.diagStarAlgHom_apply_single,
    toeplitz_fourierLp_one_hardyBasis, blockHardyBasis_apply]

/-- The operator norm of `blockToeplitz r A` is at most `‖A‖`. -/
theorem norm_blockToeplitz_le {r : ℕ} (A : BlockSymbol r) : ‖blockToeplitz r A‖ ≤ ‖A‖ := by
  rw [blockToeplitz_apply]
  grw [opNorm_comp_le, opNorm_comp_le, opNorm_comp_le, opNorm_comp_le,
    LinearIsometry.norm_toContinuousLinearMap_le, orthogonalProjectionOnto_norm_le,
    Lp.norm_operatorMultiplication_le, norm_subtypeL_le,
    LinearIsometry.norm_toContinuousLinearMap_le]
  simp

private theorem norm_operatorMultiplication_le_norm_blockToeplitz {r : ℕ} (A : BlockSymbol r) :
    ‖Lp.operatorMultiplication 2 A‖ ≤ ‖blockToeplitz r A‖ := by
  have hT : (blockHardySubmodule r).orthogonalProjectionOnto ∘L
      Lp.operatorMultiplication 2 A ∘L (blockHardySubmodule r).subtypeL =
      (blockHardyEquiv r).symm.toLinearIsometry.toContinuousLinearMap ∘L
        blockToeplitz r A ∘L (blockHardyEquiv r).toLinearIsometry.toContinuousLinearMap := by
    ext f : 1; simp [blockToeplitz_apply]
  refine ((blockHardySubmodule r).norm_le_norm_orthogonalProjectionOnto_comp_comp_subtypeL
    (Lp.operatorMultiplication 2 A) (dense_span_blockFourierMode r)
    (fun _ hg ↦ eventually_fourierLp_smul_mem_blockHardySubmodule hg) fun N g ↦
      Lp.operatorMultiplication_lpSMul_right (fourierLp (T := 1) ∞ N) A g).trans ?_
  rw [hT]; grw [opNorm_comp_le, opNorm_comp_le, LinearIsometry.norm_toContinuousLinearMap_le,
    LinearIsometry.norm_toContinuousLinearMap_le]; simp

/-- **Block symbol norm.** The operator norm of `blockToeplitz r A` equals `‖A‖`. -/
@[simp] theorem norm_blockToeplitz {r : ℕ} (A : BlockSymbol r) : ‖blockToeplitz r A‖ = ‖A‖ :=
  le_antisymm (norm_blockToeplitz_le A) <|
    Lp.norm_operatorMultiplication (p := 2) A ▸ norm_operatorMultiplication_le_norm_blockToeplitz A

/-- The block Toeplitz symbol map `blockToeplitz r` is an isometry. -/
theorem isometry_blockToeplitz (r : ℕ) : Isometry (blockToeplitz r) :=
  AddMonoidHomClass.isometry_of_norm (blockToeplitz r) norm_blockToeplitz

/-- A block symbol is uniquely determined by its block Toeplitz operator. -/
theorem blockToeplitz_injective (r : ℕ) : Function.Injective (blockToeplitz r) :=
  (isometry_blockToeplitz r).injective

/-- For continuous `F`, `‖blockToeplitz r (ContinuousMap.toLp ∞ haarAddCircle ℂ F)‖ = ‖F‖`. -/
theorem norm_blockToeplitz_toLp {r : ℕ}
    (F : C(UnitAddCircle, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r))) :
    ‖blockToeplitz r (ContinuousMap.toLp ∞ (haarAddCircle (T := 1)) ℂ F)‖ = ‖F‖ := by
  rw [norm_blockToeplitz, ContinuousMap.norm_toLp_top]

/-- `T` is a block Toeplitz operator iff its matrix in `blockHardyBasis r` is invariant under
`(m, n) ↦ (m + 1, n + 1)` on every `(i, j)` block. -/
theorem exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) :
    (∃ A : BlockSymbol r, blockToeplitz r A = T) ↔
      ∀ (m n : ℕ) (i j : Fin r),
        ⟪blockHardyBasis r (m + 1, i), T (blockHardyBasis r (n + 1, j))⟫_ℂ =
          ⟪blockHardyBasis r (m, i), T (blockHardyBasis r (n, j))⟫_ℂ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨A, rfl⟩ m n i j
    rw [inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_fourierCoeff_blockSymbolEntry,
      inner_blockHardyBasis_blockToeplitz_blockHardyBasis_eq_fourierCoeff_blockSymbolEntry]
    congr 1; push_cast; ring
  · choose a ha using fun i j : Fin r ↦ (exists_toeplitz_eq_iff_inner_hardyBasis_succ _).mpr
      fun m n ↦ by simpa only [inner_blockHardyBasis_apply] using h m n i j
    refine ⟨∑ i : Fin r, ∑ j : Fin r, blockSymbolSingle r i j (a i j), ?_⟩
    ext f i : 2; rw [blockToeplitz_apply_apply, apply_eq_sum_piLpEntry]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [blockSymbolEntry_sum_blockSymbolSingle, ha i j]

/-- **Block Brown–Halmos theorem.** `T = blockToeplitz r A` for a unique `A : BlockSymbol r` iff
`S_r† ∘L T ∘L S_r = T`, where `S_r` is the block forward shift. -/
theorem existsUnique_blockToeplitz_eq_iff_adjoint_comp_comp_eq {r : ℕ}
    (T : BlockHardySpace r →L[ℂ] BlockHardySpace r) :
    (∃! A : BlockSymbol r, blockToeplitz r A = T) ↔
      adjoint (PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1))) ∘L
        T ∘L PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1)) = T := by
  set S := PiLp.diagStarAlgHom ℂ HardySpace (Fin r) (toeplitz (fourierLp (T := 1) ∞ 1))
  have hS (n : ℕ) (i : Fin r) : S (blockHardyBasis r (n, i)) = blockHardyBasis r (n + 1, i) := by
    simpa only [S, ← blockToeplitz_smul_one] using
      blockToeplitz_fourierLp_one_smul_one_blockHardyBasis n i
  have hshift (m n : ℕ) (i j : Fin r) :
      ⟪blockHardyBasis r (m, i), (adjoint S ∘L T ∘L S) (blockHardyBasis r (n, j))⟫_ℂ =
        ⟪blockHardyBasis r (m + 1, i), T (blockHardyBasis r (n + 1, j))⟫_ℂ := by
    rw [comp_apply, comp_apply, adjoint_inner_right, hS, hS]
  have hexists : (∃ A : BlockSymbol r, blockToeplitz r A = T) ↔ adjoint S ∘L T ∘L S = T := by
    rw [exists_blockToeplitz_eq_iff_inner_blockHardyBasis_succ]
    exact ⟨fun h ↦ HilbertBasis.ext_inner_apply (blockHardyBasis r) (blockHardyBasis r)
      fun ⟨m, i⟩ ⟨n, j⟩ ↦ by rw [hshift, h], fun h m n i j ↦ by rw [← hshift, h]⟩
  refine ⟨fun ⟨A, hA, _⟩ ↦ hexists.1 ⟨A, hA⟩, fun h ↦ ?_⟩
  obtain ⟨A, hA⟩ := hexists.2 h
  exact ⟨A, hA, fun A' hA' ↦ blockToeplitz_injective r (hA'.trans hA.symm)⟩

end TauCeti

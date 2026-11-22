/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.StructureGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential
import TauCeti.Analysis.Normed.Algebra.MatrixExponential

/-!
# Concrete compact matrix structure groups and counterexample

This file records the basic concrete examples of compact matrix structure groups:

* **`U(1)` (`CompactMatrixStructureGroup.unitary (Fin 1)`):** `𝔲(1) = iℝ` is abelian, `Ad` is
  trivial, and every symmetric positive-definite real bilinear form on `𝔲(1)` is
  `Ad(U(1))`-invariant.
* **`SU(2)` (`CompactMatrixStructureGroup.specialUnitary (Fin 2)`):** with the trace inner product
  `⟨X, Y⟩ = -Re tr (X Y)`, the quaternion basis `i = !![0, 1; -1, 0]`, `j = !![0, I; I, 0]`,
  `k = !![I, 0; 0, -I]` satisfies `⟨i, i⟩ = ⟨j, j⟩ = ⟨k, k⟩ = 2`, pairwise orthogonality, and
  `[i, j] = 2k`, `[j, k] = 2i`, `[k, i] = 2j`.
* **The finite group `{±1} ⊂ U(1)`:** its Lie algebra is trivial (`⊥`), so its Lie algebra is a
  subsingleton.
* **The disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)`:** diagonal and anti-diagonal unitary
  `2 × 2` matrices form a closed subgroup whose Lie algebra consists of purely imaginary diagonal
  matrices (abelian). The weighted inner product with `⟨e₁, e₁⟩ = 1`, `⟨e₂, e₂⟩ = 2`,
  `⟨e₁, e₂⟩ = 0` is infinitesimally `ad`-invariant, yet conjugation by the swap matrix
  `!![0, 1; 1, 0]` exchanges `e₁` and `e₂`, so it fails `Ad`-invariance.

## Main definitions

* `TauCeti.YangMills.unitaryOneOfBilinForm`: equips `U(1)` with any symmetric positive-definite
  bilinear form on `𝔲(1)`.
* `TauCeti.YangMills.su2I`, `TauCeti.YangMills.su2J`, `TauCeti.YangMills.su2K`: the standard
  quaternion basis of `𝔰𝔲(2)`.
* `TauCeti.YangMills.pmOneSubgroup` and `TauCeti.YangMills.pmOne`: the finite structure group
  `{±1} ⊂ U(1)`.
* `TauCeti.YangMills.torusSemidirectZ2Subgroup`, `TauCeti.YangMills.swapUnitary`,
  `TauCeti.YangMills.torusE₁`, `TauCeti.YangMills.torusE₂`, and
  `TauCeti.YangMills.weightedDiagBilinForm`: the disconnected subgroup `T² ⋊ ℤ/2 ⊂ U(2)` and an
  `ad`-invariant inner product that is not `Ad`-invariant.

## Main results

* `TauCeti.YangMills.mem_matrixLieAlgebra_unitary_fin_one_iff`,
  `TauCeti.YangMills.lie_eq_zero_unitary_fin_one`,
  `TauCeti.YangMills.matrixAdjointRepresentation_unitary_fin_one`.
* `TauCeti.YangMills.innerForm_su2I_self`, `TauCeti.YangMills.innerForm_su2J_self`,
  `TauCeti.YangMills.innerForm_su2K_self`, `TauCeti.YangMills.innerForm_su2I_su2J`,
  `TauCeti.YangMills.innerForm_su2J_su2K`, `TauCeti.YangMills.innerForm_su2K_su2I`,
  `TauCeti.YangMills.lie_su2I_su2J`, `TauCeti.YangMills.lie_su2J_su2K`,
  `TauCeti.YangMills.lie_su2K_su2I`.
* `TauCeti.YangMills.matrixLieAlgebra_pmOne`,
  `TauCeti.YangMills.subsingleton_matrixLieAlgebra_pmOne`.
* `TauCeti.YangMills.mem_matrixLieAlgebra_torusSemidirectZ2_iff`,
  `TauCeti.YangMills.weightedDiagBilinForm_lieInvariant`,
  `TauCeti.YangMills.not_Ad_invariant_weightedDiagBilinForm`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436 (2022),
  §1.1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), §1.1 and §6.1, (6.1)–(6.2).
-/

public section

open scoped ComplexConjugate Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.YangMills

/-! ### `U(1)`: abelian Lie algebra `iℝ` and trivial adjoint action -/

section UnitaryOne

/-- A `1 × 1` complex matrix lies in `𝔲(1)` iff its entry is purely imaginary (`re = 0`). -/
theorem mem_matrixLieAlgebra_unitary_fin_one_iff (X : Matrix (Fin 1) (Fin 1) ℂ) :
    X ∈ (CompactMatrixStructureGroup.unitary (Fin 1)).group.matrixLieAlgebra ↔ (X 0 0).re = 0 := by
  rw [CompactMatrixStructureGroup.mem_matrixLieAlgebra_unitary_iff]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def] at h00
    have hre := congrArg Complex.re h00
    simp only [Complex.conj_re, Complex.neg_re] at hre
    linarith
  · intro hre
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def]
    apply Complex.ext
    · simp [hre]
    · simp

/-- `𝔲(1)` is abelian: every Lie bracket vanishes. -/
@[simp]
theorem lie_eq_zero_unitary_fin_one
    (X Y : (CompactMatrixStructureGroup.unitary (Fin 1)).group.matrixLieAlgebra) :
    ⁅X, Y⁆ = 0 := by
  apply Subtype.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [LieRing.of_associative_ring_bracket, Matrix.mul_apply, mul_comm]

private theorem conj_eq_self_unitary_fin_one (U : Matrix.unitaryGroup (Fin 1) ℂ)
    (X : Matrix (Fin 1) (Fin 1) ℂ) :
    (U : Matrix (Fin 1) (Fin 1) ℂ) * X * star (U : Matrix (Fin 1) (Fin 1) ℂ) = X := by
  ext i j
  fin_cases i
  fin_cases j
  have h1 : (U : Matrix (Fin 1) (Fin 1) ℂ) * (U : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 U.property
  have h00 := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h00
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  calc (U : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * X 0 0 * star ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
      = ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * star ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0)) *
          X 0 0 := by ring
    _ = X 0 0 := by rw [h00, one_mul]

/-- The adjoint action of `U(1)` on `𝔲(1)` is trivial. -/
@[simp]
theorem matrixAdjointRepresentation_unitary_fin_one
    (g : (CompactMatrixStructureGroup.unitary (Fin 1)).group) :
    (CompactMatrixStructureGroup.unitary (Fin 1)).group.matrixAdjointRepresentation g =
      LinearMap.id := by
  ext1 X
  ext1
  rw [ClosedSubgroup.coe_matrixAdjointRepresentation_apply]
  exact conj_eq_self_unitary_fin_one g.val X.val

/-- Every symmetric positive-definite real bilinear form on `𝔲(1)` is automatically
`Ad(U(1))`-invariant and therefore defines a `CompactMatrixStructureGroup (Fin 1)`. -/
@[expose]
def unitaryOneOfBilinForm
    (B : LinearMap.BilinForm ℝ (ClosedSubgroup.unitary (Fin 1) ℂ).matrixLieAlgebra)
    (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    CompactMatrixStructureGroup (Fin 1) where
  group := ClosedSubgroup.unitary (Fin 1) ℂ
  innerForm := B
  isSymm_innerForm := hSymm
  posDef_innerForm := hPos
  isInvariantForm_innerForm := TauCeti.Representation.isInvariantForm_iff.mpr fun g X Y ↦ by
    have hfix (Z : (ClosedSubgroup.unitary (Fin 1) ℂ).matrixLieAlgebra) :
        (ClosedSubgroup.unitary (Fin 1) ℂ).matrixAdjointRepresentation g Z = Z := by
      ext1
      rw [ClosedSubgroup.coe_matrixAdjointRepresentation_apply]
      exact conj_eq_self_unitary_fin_one g.val Z.val
    rw [hfix X, hfix Y]

/-- The underlying subgroup of `unitaryOneOfBilinForm` is `U(1)`. -/
@[simp]
theorem unitaryOneOfBilinForm_group
    (B : LinearMap.BilinForm ℝ (ClosedSubgroup.unitary (Fin 1) ℂ).matrixLieAlgebra)
    (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef) :
    (unitaryOneOfBilinForm B hSymm hPos).group = ClosedSubgroup.unitary (Fin 1) ℂ :=
  (rfl)

/-- The inner product of `unitaryOneOfBilinForm B` evaluates to `B`. -/
@[simp]
theorem unitaryOneOfBilinForm_innerForm_apply
    (B : LinearMap.BilinForm ℝ (ClosedSubgroup.unitary (Fin 1) ℂ).matrixLieAlgebra)
    (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (X Y : (ClosedSubgroup.unitary (Fin 1) ℂ).matrixLieAlgebra) :
    (unitaryOneOfBilinForm B hSymm hPos).innerForm X Y = B X Y :=
  (rfl)

end UnitaryOne

/-! ### `SU(2)`: quaternion basis and commutation relations -/

section SpecialUnitaryTwo

/-- On `𝔰𝔲(2)`, `-tr (X * Y)` is real and coincides with the trace inner product. -/
theorem neg_trace_mul_specialUnitary_fin_two
    (X Y : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra) :
    -((X : Matrix (Fin 2) (Fin 2) ℂ) * (Y : Matrix (Fin 2) (Fin 2) ℂ)).trace =
      ((CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm X Y : ℂ) :=
  CompactMatrixStructureGroup.ofTraceForm_neg_trace_mul
    (ClosedSubgroup.specialUnitary (Fin 2) ℂ) X Y

/-- The quaternion basis element `i = !![0, 1; -1, 0]` of `𝔰𝔲(2)`. -/
def su2I : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  ⟨!![0, 1; -1, 0], by
    rw [CompactMatrixStructureGroup.mem_matrixLieAlgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- The quaternion basis element `j = !![0, I; I, 0]` of `𝔰𝔲(2)`. -/
def su2J : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    rw [CompactMatrixStructureGroup.mem_matrixLieAlgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- The quaternion basis element `k = !![I, 0; 0, -I]` of `𝔰𝔲(2)`. -/
def su2K : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [CompactMatrixStructureGroup.mem_matrixLieAlgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- The underlying matrix of `su2I` is `!![0, 1; -1, 0]`. -/
@[simp] theorem coe_su2I : (su2I : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := (rfl)

/-- The underlying matrix of `su2J` is `!![0, I; I, 0]`. -/
@[simp] theorem coe_su2J : (su2J : Matrix (Fin 2) (Fin 2) ℂ) = !![0, Complex.I; Complex.I, 0] :=
  (rfl)

/-- The underlying matrix of `su2K` is `!![I, 0; 0, -I]`. -/
@[simp] theorem coe_su2K :
    (su2K : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.I, 0; 0, -Complex.I] :=
  (rfl)

/-- Trace-metric normalization of the quaternion basis element `i ∈ 𝔰𝔲(2)`:
`⟨i, i⟩ = -Re tr (i²) = 2`. -/
theorem innerForm_su2I_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2I su2I = 2 := by
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

/-- Trace-metric normalization of the quaternion basis element `j ∈ 𝔰𝔲(2)`:
`⟨j, j⟩ = -Re tr (j²) = 2`. -/
theorem innerForm_su2J_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2J su2J = 2 := by
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

/-- Trace-metric normalization of the quaternion basis element `k ∈ 𝔰𝔲(2)`:
`⟨k, k⟩ = -Re tr (k²) = 2`. -/
theorem innerForm_su2K_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2K su2K = 2 := by
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

/-- Trace-metric orthogonality of the quaternion basis elements `i` and `j` in `𝔰𝔲(2)`:
`⟨i, j⟩ = 0`. -/
theorem innerForm_su2I_su2J :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2I su2J = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Trace-metric orthogonality of the quaternion basis elements `j` and `k` in `𝔰𝔲(2)`:
`⟨j, k⟩ = 0`. -/
theorem innerForm_su2J_su2K :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2J su2K = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Trace-metric orthogonality of the quaternion basis elements `k` and `i` in `𝔰𝔲(2)`:
`⟨k, i⟩ = 0`. -/
theorem innerForm_su2K_su2I :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2K su2I = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[i, j] = 2k`. -/
theorem lie_su2I_su2J : ⁅su2I, su2J⁆ = (2 : ℝ) • su2K := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LieRing.of_associative_ring_bracket, Complex.real_smul] <;> ring

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[j, k] = 2i`. -/
theorem lie_su2J_su2K : ⁅su2J, su2K⁆ = (2 : ℝ) • su2I := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LieRing.of_associative_ring_bracket, Complex.real_smul] <;> ring

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[k, i] = 2j`. -/
theorem lie_su2K_su2I : ⁅su2K, su2I⁆ = (2 : ℝ) • su2J := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LieRing.of_associative_ring_bracket, Complex.real_smul] <;> ring

end SpecialUnitaryTwo

/-! ### Finite group `{±1} ⊂ U(1)` -/

section FinitePmOne

private theorem finite_pmOne_carrier :
    ({U : Matrix.unitaryGroup (Fin 1) ℂ |
      (U : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨ (U : Matrix (Fin 1) (Fin 1) ℂ) = -1}).Finite := by
  let negOne : Matrix.unitaryGroup (Fin 1) ℂ :=
    ⟨-(1 : Matrix (Fin 1) (Fin 1) ℂ), by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_neg,
        Matrix.conjTranspose_one, neg_mul_neg, mul_one]⟩
  refine ((Set.finite_singleton negOne).insert 1).subset fun U hU ↦ ?_
  rcases hU with h1 | hm1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext hm1)

/-- The finite closed subgroup `{±1} ⊂ U(1)`. -/
def pmOneSubgroup : ClosedSubgroup (Matrix.unitaryGroup (Fin 1) ℂ) where
  carrier := {U | (U : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨ (U : Matrix (Fin 1) (Fin 1) ℂ) = -1}
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq, MulMemClass.coe_mul] at hA hB ⊢
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
  one_mem' := Or.inl rfl
  inv_mem' {A} hA := by
    have hinv : ((A⁻¹ : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) =
        (A : Matrix (Fin 1) (Fin 1) ℂ)ᴴ := by
      rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
    simp only [Set.mem_ofPred_eq, hinv] at hA ⊢
    rcases hA with hA | hA
    · left; simp [hA]
    · right; simp [hA]
  isClosed' := finite_pmOne_carrier.isClosed

/-- `{±1} ⊂ U(1)` is finite. -/
theorem finite_pmOneSubgroup :
    (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)).Finite :=
  finite_pmOne_carrier

/-- `{±1} ⊂ U(1)` as a compact matrix structure group. -/
@[expose]
def pmOne : CompactMatrixStructureGroup (Fin 1) :=
  CompactMatrixStructureGroup.ofTraceForm pmOneSubgroup

/-- The underlying subgroup of `pmOne` is `pmOneSubgroup`. -/
@[simp]
theorem pmOne_group : pmOne.group = pmOneSubgroup :=
  (rfl)

/-- The Lie algebra of `{±1} ⊂ U(1)` is trivial (`⊥`). -/
theorem matrixLieAlgebra_pmOne : pmOne.group.matrixLieAlgebra = ⊥ :=
  pmOne.matrixLieAlgebra_eq_bot_of_finite (by rw [pmOne_group]; exact finite_pmOneSubgroup)

/-- `pmOne.group.matrixLieAlgebra` is a subsingleton (every `pmOne`-valued connection vanishes). -/
theorem subsingleton_matrixLieAlgebra_pmOne : Subsingleton pmOne.group.matrixLieAlgebra :=
  pmOne.subsingleton_matrixLieAlgebra_of_finite (by rw [pmOne_group]; exact finite_pmOneSubgroup)

end FinitePmOne

/-! ### Disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)` -/

section DisconnectedCounterexample

private theorem isClosed_torusSemidirectZ2_carrier :
    IsClosed {U : Matrix.unitaryGroup (Fin 2) ℂ |
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
        ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0)} := by
  have heval : ∀ i j : Fin 2, Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ ↦
      (U : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtypeVal)
  have h1 : IsClosed {U : Matrix.unitaryGroup (Fin 2) ℂ |
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0} :=
    (isClosed_eq (heval 0 1) continuous_const).inter (isClosed_eq (heval 1 0) continuous_const)
  have h2 : IsClosed {U : Matrix.unitaryGroup (Fin 2) ℂ |
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0} :=
    (isClosed_eq (heval 0 0) continuous_const).inter (isClosed_eq (heval 1 1) continuous_const)
  exact h1.union h2

/-- The disconnected closed subgroup `T² ⋊ ℤ/2 ⊂ U(2)` consisting of diagonal and anti-diagonal
unitary `2 × 2` complex matrices. -/
def torusSemidirectZ2Subgroup : ClosedSubgroup (Matrix.unitaryGroup (Fin 2) ℂ) where
  carrier :=
    {U | ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0)}
  mul_mem' {A B} hA hB := by
    simp only [Set.mem_ofPred_eq, MulMemClass.coe_mul] at hA hB ⊢
    rcases hA with ⟨hA01, hA10⟩ | ⟨hA00, hA11⟩ <;> rcases hB with ⟨hB01, hB10⟩ | ⟨hB00, hB11⟩
    · left; simp [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10]
    · right; simp [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB00, hB11]
    · right; simp [Matrix.mul_apply, Fin.sum_univ_two, hA00, hA11, hB01, hB10]
    · left; simp [Matrix.mul_apply, Fin.sum_univ_two, hA00, hA11, hB00, hB11]
  one_mem' := Or.inl ⟨by simp, by simp⟩
  inv_mem' {A} hA := by
    have hinv : ((A⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
        (A : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
      rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
    simp only [Set.mem_ofPred_eq, hinv] at hA ⊢
    rcases hA with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · left; simp [h01, h10]
    · right; simp [h00, h11]
  isClosed' := isClosed_torusSemidirectZ2_carrier

/-- Membership in `torusSemidirectZ2Subgroup` means being diagonal or anti-diagonal. -/
theorem mem_torusSemidirectZ2Subgroup_iff {U : Matrix.unitaryGroup (Fin 2) ℂ} :
    U ∈ torusSemidirectZ2Subgroup ↔
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
        ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0) :=
  Iff.rfl

/-- The permutation matrix `!![0, 1; 1, 0]` as an element of `U(2)`. -/
def swapUnitary : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The underlying matrix of `swapUnitary` is `!![0, 1; 1, 0]`. -/
@[simp]
theorem coe_swapUnitary : (swapUnitary : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] :=
  (rfl)

/-- The permutation matrix `swapUnitary` lies in `T² ⋊ ℤ/2`. -/
theorem swapUnitary_mem_torusSemidirectZ2Subgroup :
    swapUnitary ∈ torusSemidirectZ2Subgroup :=
  Or.inr ⟨by simp, by simp⟩

/-- The Lie algebra of `T² ⋊ ℤ/2 ⊂ U(2)` is the abelian algebra of purely imaginary diagonal
`2 × 2` matrices. -/
theorem mem_matrixLieAlgebra_torusSemidirectZ2_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ torusSemidirectZ2Subgroup.matrixLieAlgebra ↔
      X 0 1 = 0 ∧ X 1 0 = 0 ∧ (X 0 0).re = 0 ∧ (X 1 1).re = 0 := by
  constructor
  · intro hX
    have hskew := ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra hX
    have hre0 : (X 0 0).re = 0 := by
      have h00 := congrFun (congrFun hskew 0) 0
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def] at h00
      have := congrArg Complex.re h00
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hre1 : (X 1 1).re = 0 := by
      have h11 := congrFun (congrFun hskew 1) 1
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def] at h11
      have := congrArg Complex.re h11
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    rw [ClosedSubgroup.mem_matrixLieAlgebra_iff] at hX
    let D : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 1 = 0 ∧ M 1 0 = 0}
    let A : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 0 = 0 ∧ M 1 1 = 0}
    have hD_closed : IsClosed D :=
      (isClosed_eq ((continuous_apply 1).comp (continuous_apply 0)) continuous_const).inter
        (isClosed_eq ((continuous_apply 0).comp (continuous_apply 1)) continuous_const)
    have hA_closed : IsClosed A :=
      (isClosed_eq ((continuous_apply 0).comp (continuous_apply 0)) continuous_const).inter
        (isClosed_eq ((continuous_apply 1).comp (continuous_apply 1)) continuous_const)
    have hD : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ D :=
      Matrix.forall_exp_smul_mem_of_isClosed_union X hD_closed hA_closed
        (fun t ↦ by
          obtain ⟨u, hu, hEq⟩ := hX t
          rw [← hEq]
          exact mem_torusSemidirectZ2Subgroup_iff.mp hu)
        (fun t ⟨htD, htA⟩ ↦ by
          obtain ⟨u, -, hEq⟩ := hX t
          have hzero : (u : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
            ext i j
            fin_cases i <;> fin_cases j
            · exact hEq.symm ▸ htA.1
            · exact hEq.symm ▸ htD.1
            · exact hEq.symm ▸ htD.2
            · exact hEq.symm ▸ htA.2
          have h1 := Matrix.mem_unitaryGroup_iff.1 u.property
          rw [hzero, zero_mul] at h1
          have h00 := congrFun (congrFun h1 0) 0
          simp at h00)
        ⟨by simp, by simp⟩
    have h01 : X 0 1 = 0 :=
      Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).1
    have h10 : X 1 0 = 0 :=
      Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).2
    exact ⟨h01, h10, hre0, hre1⟩
  · rintro ⟨h01, h10, hre0, hre1⟩
    rw [ClosedSubgroup.mem_matrixLieAlgebra_iff]
    intro t
    let v : Fin 2 → ℂ := fun i ↦ (t : ℂ) * X i i
    have hdiag : t • X = Matrix.diagonal v := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [v, Complex.real_smul, h01, h10]
    have hexp_diag : NormedSpace.exp (t • X) = Matrix.diagonal (fun i ↦ Complex.exp (v i)) := by
      rw [hdiag, Matrix.exp_diagonal]
      let _ : NormedAlgebra ℚ ℂ := TauCeti.normedAlgebraRatOfReal
      rw [Pi.exp_def]
      congr 1
      ext i
      rw [← Complex.exp_eq_exp_ℂ]
    have hunit : Matrix.diagonal (fun i ↦ Complex.exp (v i)) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal]
      have hmul : ∀ i : Fin 2, Complex.exp (v i) * (starRingEnd ℂ) (Complex.exp (v i)) = 1 := by
        intro i
        have hre_v : (v i).re = 0 := by
          fin_cases i <;> simp [v, hre0, hre1]
        have hconj_v : (starRingEnd ℂ) (v i) = -v i := by
          apply Complex.ext
          · simp [hre_v]
          · simp
        rw [← Complex.exp_conj, hconj_v, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hmul]
    refine ⟨⟨Matrix.diagonal (fun i ↦ Complex.exp (v i)), hunit⟩,
      Or.inl ⟨by simp, by simp⟩, hexp_diag.symm⟩

/-- First diagonal basis element `e₁ = diag(i, 0)` of the Lie algebra of `T² ⋊ ℤ/2`. -/
def torusE₁ : torusSemidirectZ2Subgroup.matrixLieAlgebra :=
  ⟨!![Complex.I, 0; 0, 0], (mem_matrixLieAlgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- Second diagonal basis element `e₂ = diag(0, i)` of the Lie algebra of `T² ⋊ ℤ/2`. -/
def torusE₂ : torusSemidirectZ2Subgroup.matrixLieAlgebra :=
  ⟨!![0, 0; 0, Complex.I], (mem_matrixLieAlgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- The underlying matrix of `torusE₁` is `diag(i, 0)`. -/
@[simp]
theorem coe_torusE₁ : (torusE₁ : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.I, 0; 0, 0] :=
  (rfl)

/-- The underlying matrix of `torusE₂` is `diag(0, i)`. -/
@[simp]
theorem coe_torusE₂ : (torusE₂ : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 0; 0, Complex.I] :=
  (rfl)

/-- The weighted inner product on the abelian Lie algebra of `T² ⋊ ℤ/2` with
`⟨e₁, e₁⟩ = 1`, `⟨e₂, e₂⟩ = 2`, and `⟨e₁, e₂⟩ = 0`. -/
def weightedDiagBilinForm :
    LinearMap.BilinForm ℝ torusSemidirectZ2Subgroup.matrixLieAlgebra :=
  LinearMap.mk₂ ℝ
    (fun X Y ↦ (X.val 0 0).im * (Y.val 0 0).im + 2 * (X.val 1 1).im * (Y.val 1 1).im)
    (fun X Y Z ↦ by
      simp only [AddMemClass.coe_add, Matrix.add_apply, Complex.add_im]
      ring)
    (fun r X Y ↦ by
      simp only [SetLike.val_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)
    (fun X Y Z ↦ by
      simp only [AddMemClass.coe_add, Matrix.add_apply, Complex.add_im]
      ring)
    (fun r X Y ↦ by
      simp only [SetLike.val_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)

/-- Evaluation formula for `weightedDiagBilinForm`. -/
@[simp]
theorem weightedDiagBilinForm_apply (X Y : torusSemidirectZ2Subgroup.matrixLieAlgebra) :
    weightedDiagBilinForm X Y =
      (X.val 0 0).im * (Y.val 0 0).im + 2 * (X.val 1 1).im * (Y.val 1 1).im :=
  (rfl)

/-- `weightedDiagBilinForm` is symmetric. -/
theorem weightedDiagBilinForm_isSymm : weightedDiagBilinForm.IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    simp only [weightedDiagBilinForm_apply]
    ring

/-- `weightedDiagBilinForm` is positive definite on `torusSemidirectZ2Subgroup.matrixLieAlgebra`. -/
theorem weightedDiagBilinForm_posDef : weightedDiagBilinForm.toQuadraticMap.PosDef := by
  intro X hX
  rw [LinearMap.BilinMap.toQuadraticMap_apply, weightedDiagBilinForm_apply]
  obtain ⟨h01, h10, hre0, hre1⟩ :=
    (mem_matrixLieAlgebra_torusSemidirectZ2_iff X.val).1 X.property
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ (X.val 0 0).im * (X.val 0 0).im := mul_self_nonneg _
  have h1 : 0 ≤ (X.val 1 1).im * (X.val 1 1).im := mul_self_nonneg _
  have him0 : (X.val 0 0).im = 0 := mul_self_eq_zero.1 (by linarith)
  have him1 : (X.val 1 1).im = 0 := mul_self_eq_zero.1 (by linarith)
  apply hX
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact Complex.ext hre0 him0
  · exact h01
  · exact h10
  · exact Complex.ext hre1 him1

/-- Normalization of `e₁` under `weightedDiagBilinForm`: `⟨e₁, e₁⟩ = 1`. -/
theorem weightedDiagBilinForm_e₁_e₁ : weightedDiagBilinForm torusE₁ torusE₁ = 1 := by
  simp

/-- Normalization of `e₂` under `weightedDiagBilinForm`: `⟨e₂, e₂⟩ = 2`. -/
theorem weightedDiagBilinForm_e₂_e₂ : weightedDiagBilinForm torusE₂ torusE₂ = 2 := by
  simp

/-- Orthogonality of `e₁` and `e₂` under `weightedDiagBilinForm`: `⟨e₁, e₂⟩ = 0`. -/
theorem weightedDiagBilinForm_e₁_e₂ : weightedDiagBilinForm torusE₁ torusE₂ = 0 := by
  simp

/-- `weightedDiagBilinForm` is infinitesimally `ad`-invariant because the Lie algebra of
`T² ⋊ ℤ/2` is abelian. -/
theorem weightedDiagBilinForm_lieInvariant :
    weightedDiagBilinForm.lieInvariant torusSemidirectZ2Subgroup.matrixLieAlgebra := by
  intro X Y Z
  have hlie : ∀ A B : torusSemidirectZ2Subgroup.matrixLieAlgebra, ⁅A, B⁆ = 0 := by
    intro A B
    obtain ⟨hA01, hA10, _, _⟩ := (mem_matrixLieAlgebra_torusSemidirectZ2_iff A.val).1 A.property
    obtain ⟨hB01, hB10, _, _⟩ := (mem_matrixLieAlgebra_torusSemidirectZ2_iff B.val).1 B.property
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10,
        hB01, hB10, mul_comm]
  simp [hlie]

/-- Conjugation by the swap matrix `!![0, 1; 1, 0] ∈ T² ⋊ ℤ/2` exchanges `e₁` and `e₂`, so
`weightedDiagBilinForm` is **not** `Ad(T² ⋊ ℤ/2)`-invariant even though it is `ad`-invariant. -/
theorem not_Ad_invariant_weightedDiagBilinForm :
    ¬ TauCeti.Representation.IsInvariantForm torusSemidirectZ2Subgroup.matrixAdjointRepresentation
      weightedDiagBilinForm := by
  intro hInv
  have hspec := TauCeti.Representation.isInvariantForm_iff.mp hInv
    ⟨swapUnitary, swapUnitary_mem_torusSemidirectZ2Subgroup⟩ torusE₁ torusE₁
  have hconj :
      torusSemidirectZ2Subgroup.matrixAdjointRepresentation
        ⟨swapUnitary, swapUnitary_mem_torusSemidirectZ2Subgroup⟩ torusE₁ = torusE₂ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  rw [hconj, weightedDiagBilinForm_e₂_e₂, weightedDiagBilinForm_e₁_e₁] at hspec
  norm_num at hspec

end DisconnectedCounterexample

end TauCeti.YangMills

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.StructureGroup.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Concrete compact matrix structure groups and counterexample

This file records the basic concrete examples of compact matrix structure groups:

* **`U(1)` (`StructureGroup.unitary (Fin 1)`):** `𝔲(1) = iℝ` is abelian, `Ad` is trivial, and
  every symmetric positive-definite real bilinear form on `𝔲(1)` is `Ad(U(1))`-invariant.
* **`SU(2)` (`StructureGroup.specialUnitary (Fin 2)`):** with the trace inner product
  `⟨X, Y⟩ = -tr(X Y)`, the quaternion basis `i = !![0, 1; -1, 0]`, `j = !![0, I; I, 0]`,
  `k = !![I, 0; 0, -I]` satisfies `‖i‖² = ‖j‖² = ‖k‖² = 2`, pairwise orthogonality, and
  `[i, j] = 2k`, `[j, k] = 2i`, `[k, i] = 2j`.
* **The finite group `{±1} ⊂ U(1)`:** its Lie algebra is trivial (`⊥`), so its `LieAlgebra` is a
  subsingleton.
* **The disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)`:** diagonal and anti-diagonal unitary
  `2 × 2` matrices form a closed subgroup whose Lie algebra consists of purely imaginary diagonal
  matrices (abelian). The weighted inner product with `|e₁|² = 1`, `|e₂|² = 2`, `⟨e₁, e₂⟩ = 0` is
  infinitesimally `ad`-invariant, yet conjugation by the swap matrix `!![0, 1; 1, 0]` exchanges
  `e₁` and `e₂`, so it fails `Ad`-invariance.

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

* `TauCeti.YangMills.mem_lieSubalgebra_unitary_fin_one_iff`,
  `TauCeti.YangMills.lie_eq_zero_unitary_fin_one`,
  `TauCeti.YangMills.Ad_eq_refl_unitary_fin_one`.
* `TauCeti.YangMills.norm_sq_su2I`, `norm_sq_su2J`, `norm_sq_su2K`,
  `inner_su2I_su2J`, `inner_su2J_su2K`, `inner_su2K_su2I`,
  `lie_su2I_su2J`, `lie_su2J_su2K`, `lie_su2K_su2I`.
* `TauCeti.YangMills.lieSubalgebra_pmOne`, `TauCeti.YangMills.subsingleton_lieAlgebra_pmOne`.
* `TauCeti.YangMills.mem_unitaryLieSubalgebra_torusSemidirectZ2_iff`,
  `TauCeti.YangMills.weightedDiagBilinForm_lieInvariant`,
  `TauCeti.YangMills.not_Ad_invariant_weightedDiagBilinForm`.

## References

* S.-J. Oh and D. Tataru, *The Yang–Mills heat flow and the caloric gauge*, Astérisque 436 (2022),
  §1.1.
* S.-J. Oh and D. Tataru, *The hyperbolic Yang–Mills equation for connections in an arbitrary
  topological class*, Comm. Math. Phys. 365 (2019), §1.1 and §6.1, (6.1)–(6.2).
-/

public section

open NormedSpace Set
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

namespace TauCeti.YangMills

/-! ### `U(1)`: abelian Lie algebra `iℝ` and trivial adjoint action -/

section UnitaryOne

/-- A `1 × 1` complex matrix lies in `𝔲(1)` iff its entry is purely imaginary (`re = 0`). -/
theorem mem_lieSubalgebra_unitary_fin_one_iff (X : Matrix (Fin 1) (Fin 1) ℂ) :
    X ∈ (StructureGroup.unitary (Fin 1)).lieSubalgebra ↔ (X 0 0).re = 0 := by
  rw [StructureGroup.mem_lieSubalgebra_unitary_iff]
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
theorem lie_eq_zero_unitary_fin_one (X Y : (StructureGroup.unitary (Fin 1)).LieAlgebra) :
    ⁅X, Y⁆ = 0 := by
  apply StructureGroup.LieAlgebra.ext
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

private theorem conj_eq_self_unitary_fin_one (U : Matrix.unitaryGroup (Fin 1) ℂ)
    (X : Matrix (Fin 1) (Fin 1) ℂ) :
    (U : Matrix (Fin 1) (Fin 1) ℂ) * X * (U : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = X := by
  ext i j
  fin_cases i
  fin_cases j
  have h1 : (U : Matrix (Fin 1) (Fin 1) ℂ) * (U : Matrix (Fin 1) (Fin 1) ℂ)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 U.2
  have h00 := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h00
  simp only [Matrix.mul_apply, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    Matrix.conjTranspose_apply]
  calc (U : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * X 0 0 * star ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0)
      = ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * star ((U : Matrix (Fin 1) (Fin 1) ℂ) 0 0)) *
          X 0 0 := by ring
    _ = X 0 0 := by rw [h00, one_mul]

/-- The adjoint action of `U(1)` on `𝔲(1)` is trivial. -/
@[simp]
theorem Ad_eq_refl_unitary_fin_one (g : (StructureGroup.unitary (Fin 1)).subgroup) :
    (StructureGroup.unitary (Fin 1)).Ad g = LinearIsometryEquiv.refl ℝ _ := by
  ext X i j
  simp only [StructureGroup.Ad_val, LinearIsometryEquiv.coe_refl, id_eq,
    conj_eq_self_unitary_fin_one]

/-- Every symmetric positive-definite real bilinear form on `𝔲(1)` is automatically
`Ad(U(1))`-invariant and therefore defines a `StructureGroup (Fin 1)`. -/
def unitaryOneOfBilinForm
    (B : LinearMap.BilinForm ℝ
      (unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ))))
    (hSymm : B.IsSymm)
    (hPos : ∀ X, X ≠ 0 → 0 < B X X) : StructureGroup (Fin 1) where
  subgroup := ⊤
  isClosed := isClosed_univ
  bilinForm := B
  bilinForm_symm := hSymm
  bilinForm_pos := hPos
  bilinForm_conj g X Y := by
    have hfix : ∀ Z : unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ)),
        (⟨(g.1 : Matrix (Fin 1) (Fin 1) ℂ) * Z.1 * (g.1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 Z.2⟩ :
          unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ))) = Z :=
      fun Z ↦ Subtype.ext (conj_eq_self_unitary_fin_one g.1 Z.1)
    rw [hfix X, hfix Y]

@[simp]
theorem unitaryOneOfBilinForm_subgroup
    (B : LinearMap.BilinForm ℝ
      (unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ))))
    (hSymm : B.IsSymm) (hPos : ∀ X, X ≠ 0 → 0 < B X X) :
    (unitaryOneOfBilinForm B hSymm hPos).subgroup = ⊤ :=
  (rfl)

@[simp]
theorem unitaryOneOfBilinForm_inner
    (B : LinearMap.BilinForm ℝ
      (unitaryLieSubalgebra (⊤ : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ))))
    (hSymm : B.IsSymm) (hPos : ∀ X, X ≠ 0 → 0 < B X X)
    (X Y : (unitaryOneOfBilinForm B hSymm hPos).LieAlgebra) :
    ⟪X, Y⟫_ℝ =
      B ⟨X.val, (mem_unitaryLieSubalgebra_top_iff _).2 X.conjTranspose_val⟩
        ⟨Y.val, (mem_unitaryLieSubalgebra_top_iff _).2 Y.conjTranspose_val⟩ := by
  rw [StructureGroup.LieAlgebra.inner_eq_bilinForm]
  rfl

end UnitaryOne

/-! ### `SU(2)`: quaternion basis and commutation relations -/

section SpecialUnitaryTwo

/-- On `𝔰𝔲(2)`, `-tr(X * Y)` is real and coincides with the trace inner product `⟪X, Y⟫_ℝ`. -/
theorem neg_trace_mul_specialUnitary_fin_two
    (X Y : (StructureGroup.specialUnitary (Fin 2)).LieAlgebra) :
    -(X.val * Y.val).trace = (⟪X, Y⟫_ℝ : ℂ) :=
  StructureGroup.specialUnitary_neg_trace_mul X Y

/-- The quaternion basis element `i = !![0, 1; -1, 0]` of `𝔰𝔲(2)`. -/
def su2I : (StructureGroup.specialUnitary (Fin 2)).LieAlgebra :=
  ⟨!![0, 1; -1, 0], by
    rw [StructureGroup.mem_lieSubalgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- The quaternion basis element `j = !![0, I; I, 0]` of `𝔰𝔲(2)`. -/
def su2J : (StructureGroup.specialUnitary (Fin 2)).LieAlgebra :=
  ⟨!![0, Complex.I; Complex.I, 0], by
    rw [StructureGroup.mem_lieSubalgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- The quaternion basis element `k = !![I, 0; 0, -I]` of `𝔰𝔲(2)`. -/
def su2K : (StructureGroup.specialUnitary (Fin 2)).LieAlgebra :=
  ⟨!![Complex.I, 0; 0, -Complex.I], by
    rw [StructureGroup.mem_lieSubalgebra_specialUnitary_iff]
    refine ⟨?_, by simp [Matrix.trace, Fin.sum_univ_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

@[simp] theorem su2I_val : su2I.val = !![0, 1; -1, 0] := (rfl)
@[simp] theorem su2J_val : su2J.val = !![0, Complex.I; Complex.I, 0] := (rfl)
@[simp] theorem su2K_val : su2K.val = !![Complex.I, 0; 0, -Complex.I] := (rfl)

theorem norm_sq_su2I : ‖su2I‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, StructureGroup.specialUnitary_inner, su2I_val]
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem norm_sq_su2J : ‖su2J‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, StructureGroup.specialUnitary_inner, su2J_val]
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem norm_sq_su2K : ‖su2K‖ ^ 2 = 2 := by
  rw [← real_inner_self_eq_norm_sq, StructureGroup.specialUnitary_inner, su2K_val]
  simp [Matrix.trace, Fin.sum_univ_two]
  norm_num

theorem inner_su2I_su2J : ⟪su2I, su2J⟫_ℝ = 0 := by
  rw [StructureGroup.specialUnitary_inner, su2I_val, su2J_val]
  simp [Matrix.trace, Fin.sum_univ_two]

theorem inner_su2J_su2K : ⟪su2J, su2K⟫_ℝ = 0 := by
  rw [StructureGroup.specialUnitary_inner, su2J_val, su2K_val]
  simp [Matrix.trace, Fin.sum_univ_two]

theorem inner_su2K_su2I : ⟪su2K, su2I⟫_ℝ = 0 := by
  rw [StructureGroup.specialUnitary_inner, su2K_val, su2I_val]
  simp [Matrix.trace, Fin.sum_univ_two]

theorem lie_su2I_su2J : ⁅su2I, su2J⁆ = (2 : ℝ) • su2K := by
  apply StructureGroup.LieAlgebra.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

theorem lie_su2J_su2K : ⁅su2J, su2K⁆ = (2 : ℝ) • su2I := by
  apply StructureGroup.LieAlgebra.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

theorem lie_su2K_su2I : ⁅su2K, su2I⁆ = (2 : ℝ) • su2J := by
  apply StructureGroup.LieAlgebra.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.real_smul] <;> ring

end SpecialUnitaryTwo

/-! ### Finite group `{±1} ⊂ U(1)` -/

section FinitePmOne

/-- The finite subgroup `{±1} ⊂ U(1)`. -/
def pmOneSubgroup : Subgroup (Matrix.unitaryGroup (Fin 1) ℂ) where
  carrier := {U | (U : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨ (U : Matrix (Fin 1) (Fin 1) ℂ) = -1}
  mul_mem' {A B} hA hB := by
    change ((A : Matrix (Fin 1) (Fin 1) ℂ) * (B : Matrix (Fin 1) (Fin 1) ℂ)) = 1 ∨
      ((A : Matrix (Fin 1) (Fin 1) ℂ) * (B : Matrix (Fin 1) (Fin 1) ℂ)) = -1
    rcases hA with hA | hA <;> rcases hB with hB | hB <;> simp [hA, hB]
  one_mem' := Or.inl rfl
  inv_mem' {A} hA := by
    have hinv : ((A⁻¹ : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) =
        (A : Matrix (Fin 1) (Fin 1) ℂ)ᴴ := by
      rw [← Unitary.star_eq_inv, Unitary.coe_star, Matrix.star_eq_conjTranspose]
    change ((A⁻¹ : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨
      ((A⁻¹ : Matrix.unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) = -1
    rw [hinv]
    rcases hA with hA | hA
    · left; simp [hA]
    · right; simp [hA]

theorem finite_pmOneSubgroup : (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)).Finite := by
  let negOne : Matrix.unitaryGroup (Fin 1) ℂ :=
    ⟨-(1 : Matrix (Fin 1) (Fin 1) ℂ), by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_neg,
        Matrix.conjTranspose_one, neg_mul_neg, mul_one]⟩
  have hsub : (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)) ⊆ {1, negOne} := by
    intro U hU
    rcases hU with h1 | hm1
    · left; exact Subtype.ext h1
    · right; exact Subtype.ext hm1
  exact ((Set.finite_singleton negOne).insert 1).subset hsub

theorem isClosed_pmOneSubgroup : IsClosed (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)) :=
  finite_pmOneSubgroup.isClosed

/-- `{±1} ⊂ U(1)` as a compact matrix structure group. -/
def pmOne : StructureGroup (Fin 1) :=
  StructureGroup.ofClosedSubgroup pmOneSubgroup isClosed_pmOneSubgroup

@[simp]
theorem pmOne_subgroup : pmOne.subgroup = pmOneSubgroup :=
  StructureGroup.ofClosedSubgroup_subgroup _ _

/-- The Lie algebra of `{±1} ⊂ U(1)` is trivial (`⊥`). -/
theorem lieSubalgebra_pmOne : pmOne.lieSubalgebra = ⊥ :=
  pmOne.lieSubalgebra_eq_bot_of_finite (by rw [pmOne_subgroup]; exact finite_pmOneSubgroup)

/-- `pmOne.LieAlgebra` is a subsingleton (every `pmOne`-valued connection vanishes). -/
theorem subsingleton_lieAlgebra_pmOne : Subsingleton pmOne.LieAlgebra :=
  pmOne.subsingleton_lieAlgebra_of_finite (by rw [pmOne_subgroup]; exact finite_pmOneSubgroup)

end FinitePmOne

/-! ### Disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)` -/

section DisconnectedCounterexample

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The disconnected closed subgroup `T² ⋊ ℤ/2 ⊂ U(2)` consisting of diagonal and anti-diagonal
unitary `2 × 2` complex matrices. -/
def torusSemidirectZ2Subgroup : Subgroup (Matrix.unitaryGroup (Fin 2) ℂ) where
  carrier :=
    {U | ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0)}
  mul_mem' {A B} hA hB := by
    change (((A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ)) 0 1 = 0 ∧
        ((A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ)) 1 0 = 0) ∨
      (((A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 = 0 ∧
        ((A : Matrix (Fin 2) (Fin 2) ℂ) * (B : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 = 0)
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
    change (((A⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧
        ((A⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
      (((A⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧
        ((A⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0)
    rw [hinv]
    rcases hA with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · left; simp [h01, h10]
    · right; simp [h00, h11]

theorem isClosed_torusSemidirectZ2Subgroup :
    IsClosed (torusSemidirectZ2Subgroup : Set (Matrix.unitaryGroup (Fin 2) ℂ)) := by
  have heval : ∀ i j : Fin 2, Continuous fun U : Matrix.unitaryGroup (Fin 2) ℂ ↦
      (U : Matrix (Fin 2) (Fin 2) ℂ) i j := fun i j ↦
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  have h1 : IsClosed {U : Matrix.unitaryGroup (Fin 2) ℂ |
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0} :=
    (isClosed_eq (heval 0 1) continuous_const).inter (isClosed_eq (heval 1 0) continuous_const)
  have h2 : IsClosed {U : Matrix.unitaryGroup (Fin 2) ℂ |
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0} :=
    (isClosed_eq (heval 0 0) continuous_const).inter (isClosed_eq (heval 1 1) continuous_const)
  exact h1.union h2

/-- The permutation matrix `!![0, 1; 1, 0]` as an element of `U(2)`. -/
def swapUnitary : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

@[simp]
theorem swapUnitary_val : (swapUnitary : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; 1, 0] :=
  (rfl)

theorem swapUnitary_mem_torusSemidirectZ2Subgroup :
    swapUnitary ∈ torusSemidirectZ2Subgroup :=
  Or.inr ⟨by simp [swapUnitary_val], by simp [swapUnitary_val]⟩

open scoped Matrix.Norms.Operator in
private theorem continuous_exp_smul_two (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Continuous (fun t : ℝ ↦ NormedSpace.exp (t • X)) := by
  let _ : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := TauCeti.normedAlgebraRatOfReal
  exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

open scoped Matrix.Norms.Operator in
private theorem hasDerivAt_exp_smul_entry_two (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) a b) (X a b) 0 := by
  let _ : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := TauCeti.normedAlgebraRatOfReal
  let eval : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M ↦ M a b
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hexp := hasDerivAt_exp_smul_const X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hexp
  exact (LinearMap.toContinuousLinearMap eval).hasFDerivAt.comp_hasDerivAt 0 hexp

private theorem hasDerivAt_exp_smul_entry_two' (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) a b) (X a b) 0 :=
  hasDerivAt_exp_smul_entry_two X a b

/-- The Lie algebra of `T² ⋊ ℤ/2 ⊂ U(2)` is the abelian algebra of purely imaginary diagonal
`2 × 2` matrices. -/
theorem mem_unitaryLieSubalgebra_torusSemidirectZ2_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ unitaryLieSubalgebra torusSemidirectZ2Subgroup ↔
      X 0 1 = 0 ∧ X 1 0 = 0 ∧ (X 0 0).re = 0 ∧ (X 1 1).re = 0 := by
  constructor
  · intro hX
    have hskew := conjTranspose_eq_neg_of_mem_unitaryLieSubalgebra hX
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
    have hexp := (mem_unitaryLieSubalgebra_iff isClosed_torusSemidirectZ2Subgroup X).1 hX
    let f : ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun t ↦ NormedSpace.exp (t • X)
    have hf : Continuous f := continuous_exp_smul_two X
    let D : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 1 = 0 ∧ M 1 0 = 0}
    let A : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 0 = 0 ∧ M 1 1 = 0}
    let U : Set ℝ := f ⁻¹' D
    let V : Set ℝ := f ⁻¹' A
    have hD_closed : IsClosed D :=
      (isClosed_eq ((continuous_apply 1).comp (continuous_apply 0)) continuous_const).inter
        (isClosed_eq ((continuous_apply 0).comp (continuous_apply 1)) continuous_const)
    have hA_closed : IsClosed A :=
      (isClosed_eq ((continuous_apply 0).comp (continuous_apply 0)) continuous_const).inter
        (isClosed_eq ((continuous_apply 1).comp (continuous_apply 1)) continuous_const)
    have hU_closed : IsClosed U := hD_closed.preimage hf
    have hV_closed : IsClosed V := hA_closed.preimage hf
    have hcov : (Set.univ : Set ℝ) ⊆ U ∪ V := by
      intro t _
      rcases hexp t with ⟨u, hu, hEq⟩
      rcases hu with ⟨h01, h10⟩ | ⟨h00, h11⟩
      · exact Or.inl ⟨by simpa [f, ← hEq] using h01, by simpa [f, ← hEq] using h10⟩
      · exact Or.inr ⟨by simpa [f, ← hEq] using h00, by simpa [f, ← hEq] using h11⟩
    have hdisj : Disjoint U V := by
      refine Set.disjoint_left.2 fun t htU htV ↦ ?_
      rcases hexp t with ⟨u, _, hEq⟩
      have hzero : (u : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
        ext i j
        fin_cases i <;> fin_cases j
        · exact hEq.symm ▸ htV.1
        · exact hEq.symm ▸ htU.1
        · exact hEq.symm ▸ htU.2
        · exact hEq.symm ▸ htV.2
      have h1 := Matrix.mem_unitaryGroup_iff.1 u.2
      rw [hzero, zero_mul] at h1
      have h00 := congrFun (congrFun h1 0) 0
      simp at h00
    have hU_open : IsOpen U := by
      have : U = Vᶜ := Set.Subset.antisymm hdisj.subset_compl_right fun t ht ↦
        (hcov (Set.mem_univ t)).resolve_right ht
      rw [this]
      exact hV_closed.isOpen_compl
    have hV_open : IsOpen V := by
      have : V = Uᶜ := Set.Subset.antisymm hdisj.symm.subset_compl_right fun t ht ↦
        (hcov (Set.mem_univ t)).resolve_left ht
      rw [this]
      exact hU_closed.isOpen_compl
    have h0 : (0 : ℝ) ∈ U := by
      have h1 : f 0 = 1 := by simp [f]
      exact ⟨by simp [h1], by simp [h1]⟩
    have hsub : (Set.univ : Set ℝ) ⊆ U :=
      isPreconnected_univ.subset_left_of_subset_union hU_open hV_open hdisj hcov ⟨0, trivial, h0⟩
    have h01 : X 0 1 = 0 := by
      have hconst : (fun t : ℝ ↦ NormedSpace.exp (t • X) 0 1) = fun _ ↦ 0 :=
        funext fun t ↦ (hsub (Set.mem_univ t)).1
      have hderiv0 : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) 0 1) 0 0 := by
        rw [hconst]
        exact hasDerivAt_const 0 (0 : ℂ)
      exact (hasDerivAt_exp_smul_entry_two' X 0 1).unique hderiv0
    have h10 : X 1 0 = 0 := by
      have hconst : (fun t : ℝ ↦ NormedSpace.exp (t • X) 1 0) = fun _ ↦ 0 :=
        funext fun t ↦ (hsub (Set.mem_univ t)).2
      have hderiv0 : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (t • X) 1 0) 0 0 := by
        rw [hconst]
        exact hasDerivAt_const 0 (0 : ℂ)
      exact (hasDerivAt_exp_smul_entry_two' X 1 0).unique hderiv0
    exact ⟨h01, h10, hre0, hre1⟩
  · rintro ⟨h01, h10, hre0, hre1⟩
    rw [mem_unitaryLieSubalgebra_iff isClosed_torusSemidirectZ2Subgroup]
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
def torusE₁ : unitaryLieSubalgebra torusSemidirectZ2Subgroup :=
  ⟨!![Complex.I, 0; 0, 0], (mem_unitaryLieSubalgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- Second diagonal basis element `e₂ = diag(0, i)` of the Lie algebra of `T² ⋊ ℤ/2`. -/
def torusE₂ : unitaryLieSubalgebra torusSemidirectZ2Subgroup :=
  ⟨!![0, 0; 0, Complex.I], (mem_unitaryLieSubalgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- The weighted inner product on the abelian Lie algebra of `T² ⋊ ℤ/2` with
`‖e₁‖² = 1`, `‖e₂‖² = 2`, and `⟨e₁, e₂⟩ = 0`. -/
def weightedDiagBilinForm :
    LinearMap.BilinForm ℝ (unitaryLieSubalgebra torusSemidirectZ2Subgroup) :=
  LinearMap.mk₂ ℝ
    (fun X Y ↦ (X.1 0 0).im * (Y.1 0 0).im + 2 * (X.1 1 1).im * (Y.1 1 1).im)
    (fun X Y Z ↦ by
      change ((X.1 0 0 + Y.1 0 0).im * (Z.1 0 0).im +
          2 * (X.1 1 1 + Y.1 1 1).im * (Z.1 1 1).im) = _
      simp only [Complex.add_im]
      ring)
    (fun r X Y ↦ by
      change (((r • X.1) 0 0).im * (Y.1 0 0).im +
          2 * ((r • X.1) 1 1).im * (Y.1 1 1).im) = _
      simp only [Matrix.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)
    (fun X Y Z ↦ by
      change ((X.1 0 0).im * (Y.1 0 0 + Z.1 0 0).im +
          2 * (X.1 1 1).im * (Y.1 1 1 + Z.1 1 1).im) = _
      simp only [Complex.add_im]
      ring)
    (fun r X Y ↦ by
      change ((X.1 0 0).im * ((r • Y.1) 0 0).im +
          2 * (X.1 1 1).im * ((r • Y.1) 1 1).im) = _
      simp only [Matrix.smul_apply, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, smul_eq_mul]
      ring)

theorem weightedDiagBilinForm_isSymm : weightedDiagBilinForm.IsSymm :=
  LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by
    change (X.1 0 0).im * (Y.1 0 0).im + 2 * (X.1 1 1).im * (Y.1 1 1).im =
      (Y.1 0 0).im * (X.1 0 0).im + 2 * (Y.1 1 1).im * (X.1 1 1).im
    ring

theorem weightedDiagBilinForm_pos (X : unitaryLieSubalgebra torusSemidirectZ2Subgroup)
    (hX : X ≠ 0) :
    0 < weightedDiagBilinForm X X := by
  change 0 < (X.1 0 0).im * (X.1 0 0).im + 2 * (X.1 1 1).im * (X.1 1 1).im
  obtain ⟨h01, h10, hre0, hre1⟩ :=
    (mem_unitaryLieSubalgebra_torusSemidirectZ2_iff X.1).1 X.2
  by_contra hle
  push Not at hle
  have h0 : 0 ≤ (X.1 0 0).im * (X.1 0 0).im := mul_self_nonneg _
  have h1 : 0 ≤ (X.1 1 1).im * (X.1 1 1).im := mul_self_nonneg _
  have him0 : (X.1 0 0).im = 0 := mul_self_eq_zero.1 (by linarith)
  have him1 : (X.1 1 1).im = 0 := mul_self_eq_zero.1 (by linarith)
  apply hX
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · exact Complex.ext hre0 him0
  · exact h01
  · exact h10
  · exact Complex.ext hre1 him1

theorem weightedDiagBilinForm_e₁_e₁ : weightedDiagBilinForm torusE₁ torusE₁ = 1 := by
  change ((torusE₁.1 0 0).im * (torusE₁.1 0 0).im +
    2 * (torusE₁.1 1 1).im * (torusE₁.1 1 1).im) = 1
  simp [torusE₁]

theorem weightedDiagBilinForm_e₂_e₂ : weightedDiagBilinForm torusE₂ torusE₂ = 2 := by
  change ((torusE₂.1 0 0).im * (torusE₂.1 0 0).im +
    2 * (torusE₂.1 1 1).im * (torusE₂.1 1 1).im) = 2
  simp [torusE₂]

theorem weightedDiagBilinForm_e₁_e₂ : weightedDiagBilinForm torusE₁ torusE₂ = 0 := by
  change ((torusE₁.1 0 0).im * (torusE₂.1 0 0).im +
    2 * (torusE₁.1 1 1).im * (torusE₂.1 1 1).im) = 0
  simp [torusE₁, torusE₂]

/-- `weightedDiagBilinForm` is infinitesimally `ad`-invariant because the Lie algebra of
`T² ⋊ ℤ/2` is abelian. -/
theorem weightedDiagBilinForm_lieInvariant :
    weightedDiagBilinForm.lieInvariant (unitaryLieSubalgebra torusSemidirectZ2Subgroup) := by
  intro X Y Z
  have hlie : ∀ A B : unitaryLieSubalgebra torusSemidirectZ2Subgroup, ⁅A, B⁆ = 0 := by
    intro A B
    obtain ⟨hA01, hA10, _, _⟩ := (mem_unitaryLieSubalgebra_torusSemidirectZ2_iff A.1).1 A.2
    obtain ⟨hB01, hB10, _, _⟩ := (mem_unitaryLieSubalgebra_torusSemidirectZ2_iff B.1).1 B.2
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hB01, hB10, mul_comm]
  simp [hlie]

/-- Conjugation by the swap matrix `!![0, 1; 1, 0] ∈ T² ⋊ ℤ/2` exchanges `e₁` and `e₂`, so
`weightedDiagBilinForm` is **not** `Ad(T² ⋊ ℤ/2)`-invariant even though it is `ad`-invariant. -/
theorem not_Ad_invariant_weightedDiagBilinForm :
    ¬ ∀ (g : torusSemidirectZ2Subgroup)
        (X Y : unitaryLieSubalgebra torusSemidirectZ2Subgroup),
      weightedDiagBilinForm
        ⟨(g.1 : Matrix (Fin 2) (Fin 2) ℂ) * X.1 * (g.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 X.2⟩
        ⟨(g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Y.1 * (g.1 : Matrix (Fin 2) (Fin 2) ℂ)ᴴ,
          conj_mem_unitaryLieSubalgebra g.2 Y.2⟩ =
      weightedDiagBilinForm X Y := by
  intro hInv
  have hspec := hInv ⟨swapUnitary, swapUnitary_mem_torusSemidirectZ2Subgroup⟩ torusE₁ torusE₁
  have hconj : (⟨(swapUnitary : Matrix (Fin 2) (Fin 2) ℂ) * torusE₁.1 *
      (swapUnitary : Matrix (Fin 2) (Fin 2) ℂ)ᴴ,
      conj_mem_unitaryLieSubalgebra swapUnitary_mem_torusSemidirectZ2Subgroup torusE₁.2⟩ :
      unitaryLieSubalgebra torusSemidirectZ2Subgroup) = torusE₂ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swapUnitary_val, torusE₁, torusE₂, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hconj, weightedDiagBilinForm_e₂_e₂, weightedDiagBilinForm_e₁_e₁] at hspec
  norm_num at hspec

end DisconnectedCounterexample

end TauCeti.YangMills

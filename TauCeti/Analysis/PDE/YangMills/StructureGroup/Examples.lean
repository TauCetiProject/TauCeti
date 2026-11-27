/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.YangMills.StructureGroup
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Examples
import TauCeti.RepresentationTheory.SU2.StandardBasis

/-!
# Concrete compact matrix structure groups

This file records the basic concrete examples of `TauCeti.CompactMatrixStructureGroup`:

* **`U(1)` (`CompactMatrixStructureGroup.unitary (Fin 1)`):** since `𝔲(1) = iℝ` is abelian and
  `Ad` is trivial (`ClosedSubgroup.matrixAdjointRepresentation_eq_id_of_unique`), every symmetric
  positive-definite real bilinear form on `𝔲(1)` is `Ad(U(1))`-invariant and defines a structure
  group (`TauCeti.YangMills.unitaryOneOfBilinForm`).
* **`SU(2)` (`CompactMatrixStructureGroup.specialUnitary (Fin 2)`):** with the trace inner product
  `⟨X, Y⟩ = -Re tr (X Y)`, the quaternion basis `i = !![0, 1; -1, 0]`, `j = !![0, I; I, 0]`,
  `k = !![I, 0; 0, -I]` satisfies `⟨i, i⟩ = ⟨j, j⟩ = ⟨k, k⟩ = 2`, pairwise orthogonality, and
  `[i, j] = 2k`, `[j, k] = 2i`, `[k, i] = 2j`.
* **The finite group `{±1} ⊂ U(1)` (`TauCeti.YangMills.pmOne`):** wrapping
  `TauCeti.Lie.pmOneSubgroup`, its Lie algebra is trivial (`⊥`), so its Lie algebra is a
  subsingleton.

For the subgroup-only `ClosedSubgroup` examples—including `TauCeti.Lie.pmOneSubgroup` and the
disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)` (`TauCeti.Lie.torusSemidirectZ2Subgroup`), which
carries an `ad`-invariant inner product that fails `Ad`-invariance—see
`TauCeti.Geometry.Lie.Subgroup.Unitary.Examples`.

## Main definitions

* `TauCeti.YangMills.unitaryOneOfBilinForm`: equips `U(1)` with any symmetric positive-definite
  bilinear form on `𝔲(1)`.
* `TauCeti.YangMills.su2I`, `TauCeti.YangMills.su2J`, `TauCeti.YangMills.su2K`: the standard
  quaternion basis of `𝔰𝔲(2)`.
* `TauCeti.YangMills.pmOne`: the finite structure group `{±1} ⊂ U(1)`.

## Main results

* `TauCeti.YangMills.innerForm_su2I_self`, `TauCeti.YangMills.innerForm_su2J_self`,
  `TauCeti.YangMills.innerForm_su2K_self`, `TauCeti.YangMills.innerForm_su2I_su2J`,
  `TauCeti.YangMills.innerForm_su2J_su2K`, `TauCeti.YangMills.innerForm_su2K_su2I`,
  `TauCeti.YangMills.lie_su2I_su2J`, `TauCeti.YangMills.lie_su2J_su2K`,
  `TauCeti.YangMills.lie_su2K_su2I`.
* `TauCeti.YangMills.pmOne_group`, `TauCeti.YangMills.pmOne_innerForm`,
  `TauCeti.YangMills.matrixLieAlgebra_pmOne`,
  `TauCeti.YangMills.subsingleton_matrixLieAlgebra_pmOne`.

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

/-! ### `U(1)`: arbitrary inner products on `𝔲(1)` -/

section UnitaryOne

/-- Every symmetric positive-definite real bilinear form on `𝔲(1)` is automatically
`Ad(U(1))`-invariant and therefore defines a `CompactMatrixStructureGroup (Fin 1)`. -/
-- The type of `innerForm` depends on `group`, so its value can only be stated once `group` reduces.
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
    simp

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

private def su2OfCoord (x : Fin 3 → ℝ) :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  ⟨SU2.toMatrix (suTwoEquiv x), by
    rw [CompactMatrixStructureGroup.specialUnitary_group,
      ClosedSubgroup.mem_matrixLieAlgebra_specialUnitary_iff]
    exact ⟨SU2.conjTranspose_toMatrix _, SU2.trace_toMatrix _⟩⟩

private theorem innerForm_su2OfCoord (x y : Fin 3 → ℝ) :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm
        (su2OfCoord x) (su2OfCoord y) =
      (x ⬝ᵥ y) / 2 :=
  (ClosedSubgroup.matrixTraceForm_apply (su2OfCoord x) (su2OfCoord y)).trans <| by
    dsimp [su2OfCoord]
    rw [trace_toMatrix_suTwoEquiv_mul]
    simp
    ring

private theorem coe_su2OfCoord (x : Fin 3 → ℝ) :
    (su2OfCoord x : Matrix (Fin 2) (Fin 2) ℂ) = SU2.toMatrix (suTwoEquiv x) :=
  rfl

private theorem lie_su2OfCoord (x y : Fin 3 → ℝ) :
    ⁅su2OfCoord x, su2OfCoord y⁆ = su2OfCoord (x ⨯₃ y) := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, ← Ring.lie_def,
    coe_su2OfCoord, coe_su2OfCoord, coe_su2OfCoord, ← LieHom.map_lie, lie_suTwoEquiv]

private theorem smul_su2OfCoord (c : ℝ) (x : Fin 3 → ℝ) :
    c • su2OfCoord x = su2OfCoord (c • x) :=
  Subtype.ext (by simp [su2OfCoord, map_smul])

/-- The quaternion basis element `i = !![0, 1; -1, 0]` of `𝔰𝔲(2)`. -/
def su2I : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  su2OfCoord ((-2 : ℝ) • Pi.single 1 1)

/-- The quaternion basis element `j = !![0, I; I, 0]` of `𝔰𝔲(2)`. -/
def su2J : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  su2OfCoord ((-2 : ℝ) • Pi.single 0 1)

/-- The quaternion basis element `k = !![I, 0; 0, -I]` of `𝔰𝔲(2)`. -/
def su2K : (CompactMatrixStructureGroup.specialUnitary (Fin 2)).group.matrixLieAlgebra :=
  su2OfCoord ((-2 : ℝ) • Pi.single 2 1)

/-- The underlying matrix of `su2I` is `!![0, 1; -1, 0]`. -/
@[simp] theorem coe_su2I : (su2I : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := by
  simp only [su2I, su2OfCoord, toMatrix_suTwoEquiv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply]
  · linear_combination -Complex.I_sq
  · linear_combination Complex.I_sq

/-- The underlying matrix of `su2J` is `!![0, I; I, 0]`. -/
@[simp] theorem coe_su2J : (su2J : Matrix (Fin 2) (Fin 2) ℂ) = !![0, Complex.I; Complex.I, 0] := by
  simp only [su2J, su2OfCoord, toMatrix_suTwoEquiv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply]

/-- The underlying matrix of `su2K` is `!![I, 0; 0, -I]`. -/
@[simp] theorem coe_su2K :
    (su2K : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.I, 0; 0, -Complex.I] := by
  simp only [su2K, su2OfCoord, toMatrix_suTwoEquiv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply]

/-- Trace-metric normalization of the quaternion basis element `i ∈ 𝔰𝔲(2)`:
`⟨i, i⟩ = -Re tr (i²) = 2`. -/
theorem innerForm_su2I_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2I su2I = 2 := by
  rw [su2I, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Trace-metric normalization of the quaternion basis element `j ∈ 𝔰𝔲(2)`:
`⟨j, j⟩ = -Re tr (j²) = 2`. -/
theorem innerForm_su2J_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2J su2J = 2 := by
  rw [su2J, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Trace-metric normalization of the quaternion basis element `k ∈ 𝔰𝔲(2)`:
`⟨k, k⟩ = -Re tr (k²) = 2`. -/
theorem innerForm_su2K_self :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2K su2K = 2 := by
  rw [su2K, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Trace-metric orthogonality of the quaternion basis elements `i` and `j` in `𝔰𝔲(2)`:
`⟨i, j⟩ = 0`. -/
theorem innerForm_su2I_su2J :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2I su2J = 0 := by
  rw [su2I, su2J, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Trace-metric orthogonality of the quaternion basis elements `j` and `k` in `𝔰𝔲(2)`:
`⟨j, k⟩ = 0`. -/
theorem innerForm_su2J_su2K :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2J su2K = 0 := by
  rw [su2J, su2K, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Trace-metric orthogonality of the quaternion basis elements `k` and `i` in `𝔰𝔲(2)`:
`⟨k, i⟩ = 0`. -/
theorem innerForm_su2K_su2I :
    (CompactMatrixStructureGroup.specialUnitary (Fin 2)).innerForm su2K su2I = 0 := by
  rw [su2K, su2I, innerForm_su2OfCoord]
  simp [dotProduct, Fin.sum_univ_three]

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[i, j] = 2k`. -/
theorem lie_su2I_su2J : ⁅su2I, su2J⁆ = (2 : ℝ) • su2K := by
  rw [su2I, su2J, su2K, lie_su2OfCoord, smul_su2OfCoord]
  congr 1
  ext i
  fin_cases i <;> norm_num [crossProduct]

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[j, k] = 2i`. -/
theorem lie_su2J_su2K : ⁅su2J, su2K⁆ = (2 : ℝ) • su2I := by
  rw [su2J, su2K, su2I, lie_su2OfCoord, smul_su2OfCoord]
  congr 1
  ext i
  fin_cases i <;> norm_num [crossProduct]

/-- Signed quaternion commutator convention in `𝔰𝔲(2)`: `[k, i] = 2j`. -/
theorem lie_su2K_su2I : ⁅su2K, su2I⁆ = (2 : ℝ) • su2J := by
  rw [su2K, su2I, su2J, lie_su2OfCoord, smul_su2OfCoord]
  congr 1
  ext i
  fin_cases i <;> norm_num [crossProduct]

end SpecialUnitaryTwo

/-! ### Finite group `{±1} ⊂ U(1)` -/

section FinitePmOne

/-- `{±1} ⊂ U(1)` as a compact matrix structure group. -/
-- The type of `innerForm` depends on `group`, so `pmOne_innerForm` needs `group` to reduce.
@[expose]
def pmOne : CompactMatrixStructureGroup (Fin 1) :=
  CompactMatrixStructureGroup.ofTraceForm TauCeti.Lie.pmOneSubgroup

/-- The underlying subgroup of `pmOne` is `TauCeti.Lie.pmOneSubgroup`. -/
@[simp]
theorem pmOne_group : pmOne.group = TauCeti.Lie.pmOneSubgroup :=
  (rfl)

/-- The inner product of `pmOne` is the trace form on `TauCeti.Lie.pmOneSubgroup`. -/
@[simp]
theorem pmOne_innerForm : pmOne.innerForm = TauCeti.Lie.pmOneSubgroup.matrixTraceForm :=
  (rfl)

/-- The Lie algebra of `pmOne` is trivial (`⊥`). -/
theorem matrixLieAlgebra_pmOne : pmOne.group.matrixLieAlgebra = ⊥ := by
  rw [pmOne_group, TauCeti.Lie.matrixLieAlgebra_pmOneSubgroup]

/-- The Lie algebra `pmOne.group.matrixLieAlgebra` has a single element. -/
theorem subsingleton_matrixLieAlgebra_pmOne : Subsingleton pmOne.group.matrixLieAlgebra := by
  rw [matrixLieAlgebra_pmOne]
  exact LieSubalgebra.subsingleton_bot

end FinitePmOne

end TauCeti.YangMills

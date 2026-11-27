/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Unitary.Matrix
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.Analysis.Matrix.UnitaryGroup.Weyl
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.LinearAlgebra.Matrix.Hermitian.Basic
import TauCeti.Topology.Algebra.Group.Subgroup

/-!
# Concrete closed subgroups of the unitary group and counterexample

This file records concrete examples of closed subgroups of `Matrix.unitaryGroup n ℂ` and their
matrix Lie algebras:

* **The finite group `{±1} ⊂ U(1)` (`TauCeti.Lie.pmOneSubgroup`):** its Lie algebra is trivial
  (`⊥`).
* **The disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)`
  (`TauCeti.Lie.torusSemidirectZ2Subgroup`):** diagonal and anti-diagonal unitary `2 × 2` matrices
  form a closed subgroup whose Lie algebra consists of purely imaginary diagonal matrices (abelian).
  The weighted inner product with `⟨e₁, e₁⟩ = 1`, `⟨e₂, e₂⟩ = 2`, `⟨e₁, e₂⟩ = 0` is
  infinitesimally `ad`-invariant, yet conjugation by the swap matrix `!![0, 1; 1, 0]` exchanges
  `e₁` and `e₂`, so it fails `Ad`-invariance.

## Main definitions

* `TauCeti.Lie.pmOneSubgroup`: the finite closed subgroup `{±1} ⊂ U(1)`.
* `TauCeti.Lie.torusSemidirectZ2Subgroup`, `TauCeti.Lie.torusE₁`, `TauCeti.Lie.torusE₂`, and
  `TauCeti.Lie.weightedDiagBilinForm`: the disconnected subgroup `T² ⋊ ℤ/2 ⊂ U(2)` and an
  `ad`-invariant inner product that is not `Ad`-invariant.

## Main results

* `TauCeti.Lie.finite_pmOneSubgroup`, `TauCeti.Lie.mem_pmOneSubgroup_iff`,
  `TauCeti.Lie.matrixLieAlgebra_pmOneSubgroup`.
* `TauCeti.Lie.mem_torusSemidirectZ2Subgroup_iff`,
  `TauCeti.Lie.mem_matrixLieAlgebra_torusSemidirectZ2_iff`,
  `TauCeti.Lie.weightedDiagBilinForm_lieInvariant`,
  `TauCeti.Lie.not_Ad_invariant_weightedDiagBilinForm`.

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

namespace TauCeti.Lie

/-! ### Finite group `{±1} ⊂ U(1)` -/

section FinitePmOne

private def pmOneGen : Matrix.unitaryGroup (Fin 1) ℂ :=
  ⟨-(1 : Matrix (Fin 1) (Fin 1) ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_neg,
      Matrix.conjTranspose_one, neg_mul_neg, mul_one]⟩

private theorem pmOneGen_sq : pmOneGen ^ 2 = 1 :=
  Subtype.ext (by simp [pmOneGen, sq])

private theorem isOfFinOrder_pmOneGen : IsOfFinOrder pmOneGen :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, pmOneGen_sq⟩

/-- The finite closed subgroup `{±1} ⊂ U(1)`. -/
def pmOneSubgroup : ClosedSubgroup (Matrix.unitaryGroup (Fin 1) ℂ) where
  toSubgroup := Subgroup.zpowers pmOneGen
  isClosed' :=
    have : Finite (Subgroup.zpowers pmOneGen) := isOfFinOrder_pmOneGen.finite_zpowers
    (Set.toFinite _).isClosed

/-- The underlying subgroup of `pmOneSubgroup` is `Subgroup.zpowers pmOneGen`. -/
private theorem toSubgroup_pmOneSubgroup :
    pmOneSubgroup.toSubgroup = Subgroup.zpowers pmOneGen := by
  unfold pmOneSubgroup
  rfl

@[simp]
private theorem mem_pmOneSubgroup_iff_mem_zpowers {U : Matrix.unitaryGroup (Fin 1) ℂ} :
    U ∈ pmOneSubgroup ↔ U ∈ Subgroup.zpowers pmOneGen := by
  have hmem : U ∈ pmOneSubgroup ↔ U ∈ pmOneSubgroup.toSubgroup := Iff.rfl
  rw [hmem, toSubgroup_pmOneSubgroup]

/-- `{±1} ⊂ U(1)` is finite. -/
theorem finite_pmOneSubgroup :
    (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)).Finite := by
  have hset : (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)) =
      (Subgroup.zpowers pmOneGen : Set (Matrix.unitaryGroup (Fin 1) ℂ)) :=
    Set.ext fun _ ↦ mem_pmOneSubgroup_iff_mem_zpowers
  rw [hset]
  have : Finite (Subgroup.zpowers pmOneGen) := isOfFinOrder_pmOneGen.finite_zpowers
  exact Set.toFinite _

/-- Membership in `pmOneSubgroup` characterizes the two-element group `{1, -1} ⊂ U(1)`. -/
theorem mem_pmOneSubgroup_iff {U : Matrix.unitaryGroup (Fin 1) ℂ} :
    U ∈ pmOneSubgroup ↔
      (U : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨ (U : Matrix (Fin 1) (Fin 1) ℂ) = -1 := by
  rw [mem_pmOneSubgroup_iff_mem_zpowers, Subgroup.mem_zpowers_iff_of_sq_eq_one pmOneGen_sq]
  exact ⟨fun h ↦ h.imp (congrArg Subtype.val) (congrArg Subtype.val),
    fun h ↦ h.imp Subtype.ext Subtype.ext⟩

/-- The Lie algebra of `{±1} ⊂ U(1)` is trivial (`⊥`). -/
@[simp]
theorem matrixLieAlgebra_pmOneSubgroup : pmOneSubgroup.matrixLieAlgebra = ⊥ :=
  ClosedSubgroup.matrixLieAlgebra_eq_bot_of_countable finite_pmOneSubgroup.countable

end FinitePmOne

/-! ### Disconnected counterexample `T² ⋊ ℤ/2 ⊂ U(2)` -/

section DisconnectedCounterexample

/-- The disconnected closed subgroup `T² ⋊ ℤ/2 ⊂ U(2)`, realized as the normalizer of the
diagonal torus `TauCeti.unitaryTorus (Fin 2)` in `U(2)`. -/
def torusSemidirectZ2Subgroup : ClosedSubgroup (Matrix.unitaryGroup (Fin 2) ℂ) where
  toSubgroup := Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ))
  isClosed' := Subgroup.isClosed_normalizer <| by
    rw [show (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ)) =
        Set.range (unitaryTorusHom (Fin 2)) from
      Set.ext fun _ ↦ mem_unitaryTorus_iff_exists_unitaryTorusHom.trans (by simp [eq_comm])]
    exact (isCompact_range (continuous_unitaryTorusHom (n := Fin 2))).isClosed

private theorem toSubgroup_torusSemidirectZ2Subgroup :
    torusSemidirectZ2Subgroup.toSubgroup =
      Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ)) := by
  unfold torusSemidirectZ2Subgroup
  rfl

@[simp]
private theorem mem_torusSemidirectZ2Subgroup_iff_mem_normalizer
    {U : Matrix.unitaryGroup (Fin 2) ℂ} :
    U ∈ torusSemidirectZ2Subgroup ↔
      U ∈ Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ)) := by
  have hmem : U ∈ torusSemidirectZ2Subgroup ↔ U ∈ torusSemidirectZ2Subgroup.toSubgroup := Iff.rfl
  rw [hmem, toSubgroup_torusSemidirectZ2Subgroup]

/-- Membership in `torusSemidirectZ2Subgroup` means being diagonal or anti-diagonal. -/
theorem mem_torusSemidirectZ2Subgroup_iff {U : Matrix.unitaryGroup (Fin 2) ℂ} :
    U ∈ torusSemidirectZ2Subgroup ↔
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
        ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0) := by
  rw [mem_torusSemidirectZ2Subgroup_iff_mem_normalizer, mem_normalizer_unitaryTorus_iff]
  constructor
  · rintro ⟨z, σ, rfl⟩
    have hperm : ∀ τ : Equiv.Perm (Fin 2), τ = 1 ∨ τ = Equiv.swap 0 1 := by decide
    rcases hperm σ with rfl | rfl
    · left; simp
    · right; simp [coe_unitaryTorusHom_mul_permutationUnitary_apply]
  · rintro (⟨h01, h10⟩ | ⟨h00, h11⟩)
    · have hdiag : (U : Matrix (Fin 2) (Fin 2) ℂ).IsDiag := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp
        (mem_unitaryTorus_iff.mpr hdiag)
      exact ⟨z, 1, by simp [hz]⟩
    · let P : Matrix.unitaryGroup (Fin 2) ℂ := Matrix.permutationUnitary (Equiv.swap 0 1)
      have hP2 : P * P = 1 := by
        simp [P, ← map_mul, Equiv.swap_mul_self]
      have hdiag : ((U * P : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).IsDiag := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.coe_permutationUnitary]
      obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp
        (mem_unitaryTorus_iff.mpr hdiag)
      refine ⟨z, Equiv.swap 0 1, ?_⟩
      calc U = U * (P * P) := by rw [hP2, mul_one]
        _ = (U * P) * P := (mul_assoc _ _ _).symm
        _ = unitaryTorusHom (Fin 2) z * Matrix.permutationUnitary (Equiv.swap 0 1) := by rw [hz]

/-- A skew-Hermitian `2 × 2` complex matrix has unitary exponential line. -/
private theorem exp_smul_mem_unitaryGroup_of_conjTranspose_eq_neg
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hskew : Xᴴ = -X) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hX : X ∈ (ClosedSubgroup.unitary (Fin 2) ℂ).matrixLieAlgebra :=
    ClosedSubgroup.mem_matrixLieAlgebra_unitary_iff.mpr hskew
  obtain ⟨u, -, hu⟩ := ClosedSubgroup.mem_matrixLieAlgebra_iff.mp hX t
  exact hu ▸ u.property

/-- An exponential line staying in `torusSemidirectZ2Subgroup` remains in the diagonal torus. -/
private theorem exp_smul_diag_of_mem_torusSemidirectZ2Subgroup
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ torusSemidirectZ2Subgroup.matrixLieAlgebra)
    (t : ℝ) :
    NormedSpace.exp (t • X) 0 1 = 0 ∧ NormedSpace.exp (t • X) 1 0 = 0 := by
  have hexp := ClosedSubgroup.mem_matrixLieAlgebra_iff.mp hX
  let D : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 1 = 0 ∧ M 1 0 = 0}
  let A : Set (Matrix (Fin 2) (Fin 2) ℂ) := {M | M 0 0 = 0 ∧ M 1 1 = 0}
  have hD_closed : IsClosed D :=
    (isClosed_eq ((continuous_apply 1).comp (continuous_apply 0)) continuous_const).inter
      (isClosed_eq ((continuous_apply 0).comp (continuous_apply 1)) continuous_const)
  have hA_closed : IsClosed A :=
    (isClosed_eq ((continuous_apply 0).comp (continuous_apply 0)) continuous_const).inter
      (isClosed_eq ((continuous_apply 1).comp (continuous_apply 1)) continuous_const)
  -- Every point on the exponential line lies in `D ∪ A`, and no unitary matrix lies in `D ∩ A`.
  have hcov : Set.range (fun s : ℝ ↦ NormedSpace.exp (s • X)) ⊆ D ∪ A := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨u, hu, hEq⟩ := hexp s
    simpa [← hEq, D, A] using mem_torusSemidirectZ2Subgroup_iff.mp hu
  have hdisj : Set.range (fun s : ℝ ↦ NormedSpace.exp (s • X)) ∩ (D ∩ A) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro M ⟨⟨s, rfl⟩, hsD, hsA⟩
    obtain ⟨u, -, hEq⟩ := hexp s
    have hzero : (u : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j
      · exact hEq.symm ▸ hsA.1
      · exact hEq.symm ▸ hsD.1
      · exact hEq.symm ▸ hsD.2
      · exact hEq.symm ▸ hsA.2
    have h1 := Matrix.mem_unitaryGroup_iff.1 u.property
    rw [hzero, zero_mul] at h1
    have h00 := congrFun (congrFun h1 0) 0
    simp at h00
  -- Connectedness of `ℝ` forces the range into `D` because `exp 0 = 1 ∈ D \ A`.
  have hsub := (isPreconnected_iff_subset_of_disjoint_closed.1
    (isPreconnected_range (Matrix.continuous_exp_smul X)) D A hD_closed hA_closed hcov
      hdisj).resolve_right fun hA ↦ by
    have h1A : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ A := by
      simpa using hA ⟨0, rfl⟩
    simpa [A] using h1A.1
  exact hsub ⟨t, rfl⟩

/-- The Lie algebra of `T² ⋊ ℤ/2 ⊂ U(2)` is the abelian algebra of purely imaginary diagonal
`2 × 2` matrices. -/
theorem mem_matrixLieAlgebra_torusSemidirectZ2_iff (X : Matrix (Fin 2) (Fin 2) ℂ) :
    X ∈ torusSemidirectZ2Subgroup.matrixLieAlgebra ↔
      X 0 1 = 0 ∧ X 1 0 = 0 ∧ (X 0 0).re = 0 ∧ (X 1 1).re = 0 := by
  constructor
  · intro hX
    -- Skew-Hermitianness gives purely imaginary diagonal entries; connectedness keeps off-diagonal
    -- entries of `exp (t • X)` zero for all `t`, forcing off-diagonal entries of `X` to vanish.
    have hskew := ClosedSubgroup.conjTranspose_eq_neg_of_mem_matrixLieAlgebra hX
    have hre0 : (X 0 0).re = 0 := by
      simpa using Matrix.re_apply_self_eq_zero_of_conjTranspose_eq_neg hskew 0
    have hre1 : (X 1 1).re = 0 := by
      simpa using Matrix.re_apply_self_eq_zero_of_conjTranspose_eq_neg hskew 1
    have hD := exp_smul_diag_of_mem_torusSemidirectZ2Subgroup hX
    have h01 : X 0 1 = 0 :=
      Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).1
    have h10 : X 1 0 = 0 :=
      Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).2
    exact ⟨h01, h10, hre0, hre1⟩
  · rintro ⟨h01, h10, hre0, hre1⟩
    -- Purely imaginary diagonal matrices have diagonal skew-Hermitian exponential line in `U(2)`.
    have hskew : Xᴴ = -X := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, h01, h10, hre0, hre1]
    rw [ClosedSubgroup.mem_matrixLieAlgebra_iff]
    intro t
    have hdiag : t • X = Matrix.diagonal (fun i ↦ (t : ℂ) * X i i) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Complex.real_smul, h01, h10]
    refine ⟨⟨NormedSpace.exp (t • X), exp_smul_mem_unitaryGroup_of_conjTranspose_eq_neg hskew t⟩,
      mem_torusSemidirectZ2Subgroup_iff.mpr (Or.inl ?_), rfl⟩
    dsimp only
    rw [hdiag, Matrix.exp_diagonal]
    simp

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
  let f (i : Fin 2) : torusSemidirectZ2Subgroup.matrixLieAlgebra →ₗ[ℝ] ℝ :=
    Complex.imLm.comp
      ((Matrix.entryLinearMap ℝ ℂ i i).comp
        torusSemidirectZ2Subgroup.matrixLieAlgebra.incl.toLinearMap)
  LinearMap.BilinForm.linMulLin (f 0) (f 0) + (2 : ℝ) • LinearMap.BilinForm.linMulLin (f 1) (f 1)

/-- Evaluation formula for `weightedDiagBilinForm`. -/
@[simp]
theorem weightedDiagBilinForm_apply (X Y : torusSemidirectZ2Subgroup.matrixLieAlgebra) :
    weightedDiagBilinForm X Y =
      (X.val 0 0).im * (Y.val 0 0).im + 2 * (X.val 1 1).im * (Y.val 1 1).im := by
  simp [weightedDiagBilinForm, mul_assoc]

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
  let swap : torusSemidirectZ2Subgroup :=
    ⟨Matrix.permutationUnitary (Equiv.swap 0 1), permutationUnitary_mem_normalizer (Equiv.swap 0 1)⟩
  have hspec := TauCeti.Representation.isInvariantForm_iff.mp hInv swap torusE₁ torusE₁
  have hconj : torusSemidirectZ2Subgroup.matrixAdjointRepresentation swap torusE₁ = torusE₂ := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap, Matrix.coe_permutationUnitary, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose]
  rw [hconj, weightedDiagBilinForm_e₂_e₂, weightedDiagBilinForm_e₁_e₁] at hspec
  norm_num at hspec

end DisconnectedCounterexample

end TauCeti.Lie

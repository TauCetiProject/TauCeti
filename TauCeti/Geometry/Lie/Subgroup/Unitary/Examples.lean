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
import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
import TauCeti.Analysis.Matrix.Normed
import TauCeti.Analysis.Matrix.UnitaryGroup.MaximalTorus
import TauCeti.Analysis.Matrix.UnitaryGroup.Weyl
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Geometry.Lie.Subgroup.Weyl.Finite
import TauCeti.Geometry.Manifold.Instances.Unitary
import TauCeti.LinearAlgebra.Matrix.Hermitian.Basic
import TauCeti.LinearAlgebra.QuadraticForm.PosDef
import TauCeti.Topology.Algebra.Group.Subgroup
import TauCeti.Topology.Algebra.Star.Unitary

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

open scoped ComplexConjugate Matrix Manifold

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

/-- `{±1} ⊂ U(1)` is finite. -/
theorem finite_pmOneSubgroup :
    (pmOneSubgroup : Set (Matrix.unitaryGroup (Fin 1) ℂ)).Finite := by
  have : Finite (Subgroup.zpowers pmOneGen) := isOfFinOrder_pmOneGen.finite_zpowers
  change Set.Finite (Subgroup.zpowers pmOneGen : Set (Matrix.unitaryGroup (Fin 1) ℂ))
  exact Set.toFinite _

/-- Membership in `pmOneSubgroup` characterizes the two-element group `{1, -1} ⊂ U(1)`. -/
theorem mem_pmOneSubgroup_iff {U : Matrix.unitaryGroup (Fin 1) ℂ} :
    U ∈ pmOneSubgroup ↔
      (U : Matrix (Fin 1) (Fin 1) ℂ) = 1 ∨ (U : Matrix (Fin 1) (Fin 1) ℂ) = -1 := by
  change U ∈ Subgroup.zpowers pmOneGen ↔ _
  rw [Subgroup.mem_zpowers_iff_of_sq_eq_one pmOneGen_sq]
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
  isClosed' := Subgroup.isClosed_normalizer (isTorus_unitaryTorus (n := Fin 2)).isClosed

/-- Membership in `torusSemidirectZ2Subgroup` means being diagonal or anti-diagonal. -/
theorem mem_torusSemidirectZ2Subgroup_iff {U : Matrix.unitaryGroup (Fin 2) ℂ} :
    U ∈ torusSemidirectZ2Subgroup ↔
      ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0) ∨
        ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 0 ∧ (U : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 0) := by
  change U ∈ Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ)) ↔ _
  rw [mem_normalizer_unitaryTorus_iff]
  constructor
  · rintro ⟨z, σ, rfl⟩
    have hperm : ∀ τ : Equiv.Perm (Fin 2), τ = 1 ∨ τ = Equiv.swap 0 1 := by decide
    rcases hperm σ with rfl | rfl
    · left; simp
    · right; simp [coe_unitaryTorusHom_mul_permutationUnitary_apply]
  · rintro (⟨h01, h10⟩ | ⟨h00, h11⟩)
    · have hdiag : (U : Matrix (Fin 2) (Fin 2) ℂ).IsDiag := fun i j hij ↦ by
        fin_cases i <;> fin_cases j <;> simp_all
      obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp
        (mem_unitaryTorus_iff.mpr hdiag)
      exact ⟨z, 1, by simp [hz]⟩
    · let P : Matrix.unitaryGroup (Fin 2) ℂ := Matrix.permutationUnitary (Equiv.swap 0 1)
      have hP2 : P * P = 1 := by simp [P, ← map_mul, Equiv.swap_mul_self]
      have hdiag : ((U * P : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).IsDiag :=
        fun i j hij ↦ by
          fin_cases i <;> fin_cases j <;>
            simp_all [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.coe_permutationUnitary]
      obtain ⟨z, hz⟩ := mem_unitaryTorus_iff_exists_unitaryTorusHom.mp
        (mem_unitaryTorus_iff.mpr hdiag)
      refine ⟨z, Equiv.swap 0 1, ?_⟩
      calc U = U * (P * P) := by rw [hP2, mul_one]
        _ = (U * P) * P := (mul_assoc _ _ _).symm
        _ = unitaryTorusHom (Fin 2) z * Matrix.permutationUnitary (Equiv.swap 0 1) := by rw [hz]

section
open scoped ContDiff Matrix.Norms.Operator
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

private theorem isOpen_unitaryTorus_subgroupOf_normalizer :
    IsOpen ((unitaryTorus (Fin 2)).subgroupOf
      (Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ))) :
      Set (Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ)))) := by
  let _ : CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) :=
    ⟨(Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val :
        Matrix.unitaryGroup (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)).isCompact_iff.mpr
      (by rw [Set.image_univ, Subtype.range_coe]
          exact TauCeti.Matrix.isCompact_unitaryGroup (n := Fin 2) (𝕜 := ℂ))⟩
  let _ : ChartedSpace _ (Matrix.unitaryGroup (Fin 2) ℂ) :=
    Unitary.instChartedSpace (R := Matrix (Fin 2) (Fin 2) ℂ)
  let _ : IsManifold (Unitary.model (Matrix (Fin 2) (Fin 2) ℂ)) ∞
      (Matrix.unitaryGroup (Fin 2) ℂ) :=
    Unitary.instIsManifold (R := Matrix (Fin 2) (Fin 2) ℂ)
  let _ : LieGroup (Unitary.model (Matrix (Fin 2) (Fin 2) ℂ)) ∞
      (Matrix.unitaryGroup (Fin 2) ℂ) :=
    Unitary.instLieGroup (R := Matrix (Fin 2) (Fin 2) ℂ)
  have hT : TauCeti.Lie.IsMaximalTorus (unitaryTorus (Fin 2)) := isMaximalTorus_unitaryTorus
  exact hT.isOpen_subgroupOf_normalizer (Unitary.model (Matrix (Fin 2) (Fin 2) ℂ))
end

/-- An exponential line staying in `torusSemidirectZ2Subgroup` remains in the diagonal torus. -/
private theorem exp_smul_diag_of_mem_torusSemidirectZ2Subgroup
    {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ∈ torusSemidirectZ2Subgroup.matrixLieAlgebra)
    (t : ℝ) :
    NormedSpace.exp (t • X) 0 1 = 0 ∧ NormedSpace.exp (t • X) 1 0 = 0 := by
  let N := Subgroup.normalizer (unitaryTorus (Fin 2) : Set (Matrix.unitaryGroup (Fin 2) ℂ))
  let f : torusSemidirectZ2Subgroup → N := fun g ↦
    ⟨g.val, by change g.val ∈ torusSemidirectZ2Subgroup.toSubgroup; exact g.property⟩
  have hf_cont : Continuous f := continuous_induced_rng.mpr continuous_subtypeVal
  let γ : ℝ → N := fun s ↦ f (torusSemidirectZ2Subgroup.exp (s • ⟨X, hX⟩))
  have hγ_cont : Continuous γ :=
    hf_cont.comp (ClosedSubgroup.continuous_exp.comp (continuous_id.smul continuous_const))
  let TN : Set N := ((unitaryTorus (Fin 2)).subgroupOf N : Set N)
  have h0 : γ 0 ∈ TN := by
    change (γ 0 : Matrix.unitaryGroup (Fin 2) ℂ) ∈ unitaryTorus (Fin 2)
    rw [show (γ 0 : Matrix.unitaryGroup (Fin 2) ℂ) = 1 from Subtype.ext (by simp [γ, f])]
    exact one_mem _
  have hsub : Set.range γ ⊆ TN := (isPreconnected_range hγ_cont).subset_isClopen
    ⟨(isTorus_unitaryTorus (n := Fin 2)).isClosed.preimage continuous_subtypeVal,
      isOpen_unitaryTorus_subgroupOf_normalizer⟩ ⟨γ 0, ⟨0, rfl⟩, h0⟩
  have hdiag : ((γ t : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).IsDiag :=
    mem_unitaryTorus_iff.mp (hsub ⟨t, rfl⟩)
  rw [show ((γ t : Matrix.unitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      NormedSpace.exp (t • X) by simp [γ, f]] at hdiag
  exact ⟨hdiag (by decide), hdiag (by decide)⟩

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
    have hD := exp_smul_diag_of_mem_torusSemidirectZ2Subgroup hX
    exact ⟨Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).1,
      Matrix.apply_eq_zero_of_forall_exp_smul_apply_eq_zero fun t ↦ (hD t).2,
      by simpa using Matrix.re_apply_self_eq_zero_of_conjTranspose_eq_neg hskew 0,
      by simpa using Matrix.re_apply_self_eq_zero_of_conjTranspose_eq_neg hskew 1⟩
  · rintro ⟨h01, h10, hre0, hre1⟩
    -- Purely imaginary diagonal matrices have diagonal skew-Hermitian exponential line in `U(2)`.
    have hskew : Xᴴ = -X := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, h01, h10, hre0, hre1]
    rw [ClosedSubgroup.mem_matrixLieAlgebra_iff]
    intro t
    have hdiag : t • X = Matrix.diagonal (fun i ↦ (t : ℂ) * X i i) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Complex.real_smul, h01, h10]
    have hexp_unitary : NormedSpace.exp (t • X) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
      open scoped Matrix.Norms.Operator in
      letI : SeminormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := inferInstance
      letI := Matrix.linftyOpTopologicalSpace (Fin 2) (Fin 2) ℂ
      letI := Matrix.linftyOpContinuousStar (Fin 2) ℂ
      NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
        (skewAdjoint.smul_mem t (skewAdjoint.mem_iff.mpr hskew))
    refine ⟨⟨NormedSpace.exp (t • X), hexp_unitary⟩,
      mem_torusSemidirectZ2Subgroup_iff.mpr (Or.inl ?_), rfl⟩
    dsimp only; rw [hdiag, Matrix.exp_diagonal]; simp

/-- First diagonal basis element `e₁ = diag(i, 0)` of the Lie algebra of `T² ⋊ ℤ/2`. -/
def torusE₁ : torusSemidirectZ2Subgroup.matrixLieAlgebra :=
  ⟨!![Complex.I, 0; 0, 0], (mem_matrixLieAlgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- Second diagonal basis element `e₂ = diag(0, i)` of the Lie algebra of `T² ⋊ ℤ/2`. -/
def torusE₂ : torusSemidirectZ2Subgroup.matrixLieAlgebra :=
  ⟨!![0, 0; 0, Complex.I], (mem_matrixLieAlgebra_torusSemidirectZ2_iff _).2 (by simp)⟩

/-- The underlying matrix of `torusE₁` is `diag(i, 0)`. -/
@[simp] theorem coe_torusE₁ :
    (torusE₁ : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.I, 0; 0, 0] := (rfl)

/-- The underlying matrix of `torusE₂` is `diag(0, i)`. -/
@[simp] theorem coe_torusE₂ :
    (torusE₂ : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 0; 0, Complex.I] := (rfl)

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
  LinearMap.BilinForm.isSymm_def.2 fun X Y ↦ by simp only [weightedDiagBilinForm_apply]; ring

/-- `weightedDiagBilinForm` is positive definite on `torusSemidirectZ2Subgroup.matrixLieAlgebra`. -/
theorem weightedDiagBilinForm_posDef : weightedDiagBilinForm.toQuadraticMap.PosDef := by
  let diagIm : torusSemidirectZ2Subgroup.matrixLieAlgebra →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi fun i ↦ Complex.imLm.comp
      ((Matrix.entryLinearMap ℝ ℂ i i).comp
        torusSemidirectZ2Subgroup.matrixLieAlgebra.incl.toLinearMap)
  have hdiagIm : Function.Injective diagIm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    obtain ⟨h01, h10, hre0, hre1⟩ :=
      (mem_matrixLieAlgebra_torusSemidirectZ2_iff X.val).1 X.property
    have him0 : (X.val 0 0).im = 0 := congrFun hX 0
    have him1 : (X.val 1 1).im = 0 := congrFun hX 1
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ext_iff, h01, h10, hre0, hre1, him0, him1]
  have hq : weightedDiagBilinForm.toQuadraticMap =
      (QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), 2]).comp diagIm := by
    ext X; simp [diagIm, Fin.sum_univ_two]; ring
  have hws : (QuadraticMap.weightedSumSquares ℝ ![(1 : ℝ), 2]).PosDef :=
    (QuadraticMap.posDef_weightedSumSquares_iff _).mpr fun i ↦ by fin_cases i <;> norm_num
  exact hq ▸ hws.comp diagIm hdiagIm

/-- Normalization of `e₁` under `weightedDiagBilinForm`: `⟨e₁, e₁⟩ = 1`. -/
theorem weightedDiagBilinForm_e₁_e₁ : weightedDiagBilinForm torusE₁ torusE₁ = 1 := by simp

/-- Normalization of `e₂` under `weightedDiagBilinForm`: `⟨e₂, e₂⟩ = 2`. -/
theorem weightedDiagBilinForm_e₂_e₂ : weightedDiagBilinForm torusE₂ torusE₂ = 2 := by simp

/-- Orthogonality of `e₁` and `e₂` under `weightedDiagBilinForm`: `⟨e₁, e₂⟩ = 0`. -/
theorem weightedDiagBilinForm_e₁_e₂ : weightedDiagBilinForm torusE₁ torusE₂ = 0 := by simp

/-- `weightedDiagBilinForm` is infinitesimally `ad`-invariant because the Lie algebra of
`T² ⋊ ℤ/2` is abelian. -/
theorem weightedDiagBilinForm_lieInvariant :
    weightedDiagBilinForm.lieInvariant torusSemidirectZ2Subgroup.matrixLieAlgebra := by
  have isDiag_of_mem (A : torusSemidirectZ2Subgroup.matrixLieAlgebra) :
      (A : Matrix (Fin 2) (Fin 2) ℂ).IsDiag := fun i j hij ↦ by
    obtain ⟨h01, h10, _, _⟩ := (mem_matrixLieAlgebra_torusSemidirectZ2_iff A.val).1 A.property
    fin_cases i <;> fin_cases j <;> simp_all
  intro X Y Z
  have hlie (A B : torusSemidirectZ2Subgroup.matrixLieAlgebra) : ⁅A, B⁆ = 0 := Subtype.ext <| by
    rw [LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, ← Ring.lie_def]
    exact TauCeti.lie_eq_zero_of_isDiag (isDiag_of_mem A) (isDiag_of_mem B)
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
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [swap, Matrix.coe_permutationUnitary, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.star_eq_conjTranspose]
  rw [hconj, weightedDiagBilinForm_e₂_e₂, weightedDiagBilinForm_e₁_e₁] at hspec
  norm_num at hspec

end DisconnectedCounterexample

end TauCeti.Lie

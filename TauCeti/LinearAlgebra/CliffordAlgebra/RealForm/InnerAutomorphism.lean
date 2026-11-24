/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import TauCeti.LinearAlgebra.CliffordAlgebra.Filtration
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.Pauli
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InnerAut
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.CliffordAlgebra.Vectors
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Basic

/-!
# Inner automorphisms of real Clifford algebras not induced by isometries

An isometry `f` of `Q` induces the algebra automorphism `CliffordAlgebra.equivOfIsometry f`,
which maps the vectors `LinearMap.range (ι Q)` onto themselves, and so also the first step
`filtration Q 1 = R ⊕ range (ι Q)` of the word filtration. This file gives two inner
automorphisms of real Clifford algebras showing that neither condition comes for free.

**The positive plane.** In the Pauli model `TauCeti.realCliffordTwoZeroEquivPauli` of
`Cliff(2, 0)`, the generators `e₁, e₂` are the matrices `X = !![0, 1; 1, 0]` and
`Z = !![1, 0; 0, -1]`, so the vectors are the plane `span ℝ {X, Z}` of traceless symmetric
matrices (`TauCeti.ι_range_map_realCliffordTwoZeroEquivPauli`). Conjugation by
`D = !![2, 0; 0, 1]` fixes `Z`, but sends `X` to `!![0, 2; 1/2, 0]`, which is not symmetric. Its
transport `TauCeti.realCliffordTwoZeroDiagConj` to `Cliff(2, 0)` is therefore an algebra
automorphism moving the generator `e₁` out of the vectors, and so it is not
`equivOfIsometry f` for any isometry `f`
(`TauCeti.realCliffordTwoZeroDiagConj_ne_equivOfIsometry`). So the subgroup of automorphisms
preserving the vectors is a proper subgroup of the automorphism group.

**The grading is weaker than the filtration.** In `Cliff(4, 0)` the volume element
`ω = e₁ e₂ e₃ e₄` satisfies `ω² = 1` (`TauCeti.realCliffordFourZeroVolume_mul_self`), is even, and
anticommutes with every generator. Hence `u = 2 + ω` is an even unit with inverse `(2 - ω) / 3`.
Conjugation by it, `TauCeti.realCliffordFourZeroVolumeConj`, preserves both pieces of the
`ℤ/2`-grading (`TauCeti.evenOdd_map_realCliffordFourZeroVolumeConj`), but sends `e₁` to
`(5 e₁ - 4 e₂ e₃ e₄) / 3`, outside `filtration Q 1`. So a criterion stated on `evenOdd` instead of
on `filtration Q 1` would accept an automorphism that no isometry induces.

## Main definitions

* `TauCeti.realCliffordTwoZeroDiagConj`: conjugation by `diag(2, 1)` in the Pauli model
  of `Cliff(2, 0)`.
* `TauCeti.realCliffordFourZeroVolume`: the volume element `e₁ e₂ e₃ e₄` of `Cliff(4, 0)`.
* `TauCeti.realCliffordFourZeroVolumeUnit`: the unit `2 + ω`, with inverse `(2 - ω) / 3`.
* `TauCeti.realCliffordFourZeroVolumeConj`: conjugation by `2 + ω`.

## Main results

* `TauCeti.realCliffordTwoZeroDiagConj_ι_single_one`: the automorphism fixes `e₂`.
* `TauCeti.realCliffordTwoZeroDiagConj_ι_single_zero`: it sends `e₁` to `(5 e₁ - 3 e₁ e₂) / 4`.
* `TauCeti.ι_range_map_realCliffordTwoZeroDiagConj_ne`: it does not preserve the vectors.
* `TauCeti.evenOdd_map_realCliffordFourZeroVolumeConj`: conjugation by `2 + ω` preserves the
  `ℤ/2`-grading.
* `TauCeti.realCliffordFourZeroVolumeConj_ι_single_zero`: it sends `e₁` to
  `(5 e₁ - 4 e₂ e₃ e₄) / 3`.
* `TauCeti.filtration_one_map_realCliffordFourZeroVolumeConj_ne`: it does not preserve the first
  step of the word filtration.
* `TauCeti.realCliffordTwoZeroDiagConj_ne_equivOfIsometry` and
  `TauCeti.realCliffordFourZeroVolumeConj_ne_equivOfIsometry`: neither automorphism is induced by
  an isometry.

## Implementation notes

The plane example is often written with `e₁ ↦ Z` and `e₂ ↦ X`. The existing Pauli model
`TauCeti.realCliffordTwoZeroEquivPauli` uses the opposite order, `e₁ ↦ X` and `e₂ ↦ Z`, so here
the fixed generator is `e₂` and the moved one is `e₁`. The plane automorphism is built from
`Matrix.GeneralLinearGroup.innerAut`; conjugation by `2 + ω` is Mathlib's
`MulSemiringAction.toAlgEquiv` for the conjugation action `ConjAct` of a unit.

## References

* J. Gallier, *Clifford Algebras, Clifford Groups, and a Generalization of the Quaternions*,
  arXiv:0805.0311v3, Definition 1.3 and Theorem 1.4.
* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter II.
-/

public section

open CliffordAlgebra

namespace TauCeti

/-! ### The positive plane -/

/-- The invertible matrix `diag(2, 1)`. -/
private noncomputable def diagTwoOne : Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  diagGL ![Units.mk0 2 two_ne_zero, 1]

/-- Conjugation by `D = diag(2, 1)` in the Pauli model of `Cliff(2, 0)`, transported back to
`Cliff(2, 0)`. It fixes `e₂ ↦ Z` but moves `e₁ ↦ X` out of the vectors. -/
noncomputable def realCliffordTwoZeroDiagConj :
    CliffordAlgebra (realCliffordForm 2 0) ≃ₐ[ℝ] CliffordAlgebra (realCliffordForm 2 0) :=
  realCliffordTwoZeroEquivPauli.trans <|
    (Matrix.GeneralLinearGroup.innerAut diagTwoOne).trans realCliffordTwoZeroEquivPauli.symm

/-- In the Pauli model, the automorphism is `A ↦ D A D⁻¹` for `D = diag(2, 1)`. -/
theorem realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj
    (x : CliffordAlgebra (realCliffordForm 2 0)) :
    realCliffordTwoZeroEquivPauli (realCliffordTwoZeroDiagConj x) =
      !![2, 0; 0, 1] * realCliffordTwoZeroEquivPauli x * !![1 / 2, 0; 0, 1] := by
  simp only [realCliffordTwoZeroDiagConj, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    Matrix.GeneralLinearGroup.innerAut_apply, diagTwoOne, ← map_inv, diagGL_coe]
  congr 2 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- The automorphism sends the generator `e₁`, the matrix `X`, to `!![0, 2; 1/2, 0]`. -/
theorem realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj_ι_single_zero :
    realCliffordTwoZeroEquivPauli
        (realCliffordTwoZeroDiagConj (ι (realCliffordForm 2 0) (Pi.single 0 1))) =
      !![0, 2; 1 / 2, 0] := by
  rw [realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj, realCliffordTwoZeroEquivPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The automorphism fixes the generator `e₂`, the matrix `Z`, which commutes with `D`. -/
@[simp]
theorem realCliffordTwoZeroDiagConj_ι_single_one :
    realCliffordTwoZeroDiagConj (ι (realCliffordForm 2 0) (Pi.single 1 1)) =
      ι (realCliffordForm 2 0) (Pi.single 1 1) := by
  apply realCliffordTwoZeroEquivPauli.injective
  rw [realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj, realCliffordTwoZeroEquivPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The automorphism sends the generator `e₁` to `(5 e₁ - 3 e₁ e₂) / 4`. -/
theorem realCliffordTwoZeroDiagConj_ι_single_zero :
    realCliffordTwoZeroDiagConj (ι (realCliffordForm 2 0) (Pi.single 0 1)) =
      (5 / 4 : ℝ) • ι (realCliffordForm 2 0) (Pi.single 0 1) -
        (3 / 4 : ℝ) • (ι (realCliffordForm 2 0) (Pi.single 0 1) *
          ι (realCliffordForm 2 0) (Pi.single 1 1)) := by
  rw [← realCliffordTwoZeroEquivPauli.symm_apply_apply (realCliffordTwoZeroDiagConj _),
    realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj_ι_single_zero,
    realCliffordTwoZeroEquivPauli_symm_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  norm_num
  module

/-- The automorphism moves the generator `e₁` out of the vectors. -/
theorem realCliffordTwoZeroDiagConj_ι_single_zero_notMem_range_ι :
    realCliffordTwoZeroDiagConj (ι (realCliffordForm 2 0) (Pi.single 0 1)) ∉
      LinearMap.range (ι (realCliffordForm 2 0)) := by
  intro h
  have h' := Submodule.mem_map_of_mem (f := realCliffordTwoZeroEquivPauli.toLinearMap) h
  rw [ι_range_map_realCliffordTwoZeroEquivPauli, AlgEquiv.toLinearMap_apply,
    realCliffordTwoZeroEquivPauli_realCliffordTwoZeroDiagConj_ι_single_zero,
    Submodule.mem_span_pair] at h'
  -- In the plane of `X` and `Z` the two off-diagonal entries agree, but here they are `2, 1/2`.
  obtain ⟨a, b, hab⟩ := h'
  have h01 := congrFun (congrFun hab 0) 1
  have h10 := congrFun (congrFun hab 1) 0
  simp at h01 h10
  linarith

/-- The automorphism does not map the vectors onto themselves. -/
theorem ι_range_map_realCliffordTwoZeroDiagConj_ne :
    (LinearMap.range (ι (realCliffordForm 2 0))).map realCliffordTwoZeroDiagConj.toLinearMap ≠
      LinearMap.range (ι (realCliffordForm 2 0)) := fun h ↦
  realCliffordTwoZeroDiagConj_ι_single_zero_notMem_range_ι <|
    h ▸ Submodule.mem_map_of_mem (LinearMap.mem_range_self _ _)

/-- **Conjugation by `diag(2, 1)` is not induced by an isometry.** -/
theorem realCliffordTwoZeroDiagConj_ne_equivOfIsometry
    (f : (realCliffordForm 2 0).IsometryEquiv (realCliffordForm 2 0)) :
    realCliffordTwoZeroDiagConj ≠ equivOfIsometry f := fun h ↦
  realCliffordTwoZeroDiagConj_ι_single_zero_notMem_range_ι <| by
    rw [h, equivOfIsometry_apply, map_apply_ι]
    exact LinearMap.mem_range_self _ _

/-! ### The grading is weaker than the filtration -/

/-- The volume element `ω = e₁ e₂ e₃ e₄` of `Cliff(4, 0)`, the ordered product of the four
coordinate generators. The frame-free `CliffordAlgebra.volumeElement` needs an inner product
space, which the coordinate space `Fin 4 → ℝ` is not. -/
noncomputable def realCliffordFourZeroVolume : CliffordAlgebra (realCliffordForm 4 0) :=
  ι _ (Pi.single 0 1) * ι _ (Pi.single 1 1) * ι _ (Pi.single 2 1) * ι _ (Pi.single 3 1)

/-- The volume element is the ordered product of the four coordinate generators. -/
theorem realCliffordFourZeroVolume_def :
    realCliffordFourZeroVolume =
      ι (realCliffordForm 4 0) (Pi.single 0 1) * ι _ (Pi.single 1 1) * ι _ (Pi.single 2 1) *
        ι _ (Pi.single 3 1) := (rfl)

/-- The list of the four coordinate vectors of `Fin 4 → ℝ`. -/
private def basisList : List (Fin (4 + 0) → ℝ) :=
  [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1]

private theorem realCliffordFourZeroVolume_eq_prod :
    realCliffordFourZeroVolume = (basisList.map (ι (realCliffordForm 4 0))).prod := by
  simp [realCliffordFourZeroVolume_def, basisList, mul_assoc]

private theorem pairwise_isOrtho_basisList :
    basisList.Pairwise (realCliffordForm 4 0).IsOrtho := by
  simp only [basisList, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> apply isOrtho_realCliffordForm_single <;> decide

private theorem span_basisList :
    Submodule.span ℝ {x | x ∈ basisList} = ⊤ := by
  refine eq_top_iff.mpr ((Pi.basisFun ℝ (Fin (4 + 0))).span_eq ▸ Submodule.span_mono ?_)
  refine Set.range_subset_iff.mpr fun i ↦ ?_
  fin_cases i <;> simp [basisList]

private theorem realCliffordForm_ne_zero_of_mem_basisList :
    ∀ v ∈ basisList, realCliffordForm 4 0 v ≠ 0 := by
  simp [basisList, realCliffordForm_zero_single_one]

/-- `ω² = 1`. -/
@[simp]
theorem realCliffordFourZeroVolume_mul_self :
    realCliffordFourZeroVolume * realCliffordFourZeroVolume = 1 := by
  rw [realCliffordFourZeroVolume_eq_prod, prod_map_ι_sq_scalar pairwise_isOrtho_basisList]
  simp [basisList, realCliffordForm_zero_single_one, Nat.choose_two_right]
  norm_num

/-- The volume element anticommutes with every generator. -/
theorem realCliffordFourZeroVolume_mul_ι (v : Fin (4 + 0) → ℝ) :
    realCliffordFourZeroVolume * ι (realCliffordForm 4 0) v =
      -(ι (realCliffordForm 4 0) v * realCliffordFourZeroVolume) := by
  rw [realCliffordFourZeroVolume_eq_prod]
  exact prod_map_ι_mul_ι_of_even_length pairwise_isOrtho_basisList (by decide)
    (span_basisList ▸ Submodule.mem_top)

/-- The volume element is even. -/
theorem realCliffordFourZeroVolume_mem_evenOdd_zero :
    realCliffordFourZeroVolume ∈ evenOdd (realCliffordForm 4 0) 0 := by
  rw [realCliffordFourZeroVolume_eq_prod]
  exact prod_map_ι_mem_evenOdd_zero_of_even_length (by decide)

/-- `(2 + ω) (2 - ω) = (2 - ω) (2 + ω) = 3`. -/
private theorem mul_volume_sub_volume :
    (2 + realCliffordFourZeroVolume) * (2 - realCliffordFourZeroVolume) = 3 ∧
      (2 - realCliffordFourZeroVolume) * (2 + realCliffordFourZeroVolume) = 3 := by
  have h := algebraMap_add_smul_mul_algebraMap_sub_smul
    (realCliffordFourZeroVolume_mul_self.trans (map_one _).symm) (2 : ℝ) 1
  norm_num [map_ofNat] at h
  exact h

private theorem ι_single_zero_mul_volume :
    ι (realCliffordForm 4 0) (Pi.single 0 1) * realCliffordFourZeroVolume =
      ι (realCliffordForm 4 0) (Pi.single 1 1) * ι _ (Pi.single 2 1) * ι _ (Pi.single 3 1) := by
  have hee : ι (realCliffordForm 4 0) (Pi.single 0 1) * ι _ (Pi.single 0 1) = 1 := by
    rw [ι_sq_scalar, realCliffordForm_zero_single_one, map_one]
  simp only [realCliffordFourZeroVolume_def, ← mul_assoc, hee, one_mul]

/-- The unit `u = 2 + ω` of `Cliff(4, 0)`, with inverse `(2 - ω) / 3`. -/
noncomputable def realCliffordFourZeroVolumeUnit : (CliffordAlgebra (realCliffordForm 4 0))ˣ where
  val := 2 + realCliffordFourZeroVolume
  inv := (3⁻¹ : ℝ) • (2 - realCliffordFourZeroVolume)
  val_inv := by
    rw [mul_smul_comm, mul_volume_sub_volume.1, Algebra.smul_def,
      ← map_ofNat (algebraMap ℝ (CliffordAlgebra (realCliffordForm 4 0))) 3, ← map_mul]
    norm_num
  inv_val := by
    rw [smul_mul_assoc, mul_volume_sub_volume.2, Algebra.smul_def,
      ← map_ofNat (algebraMap ℝ (CliffordAlgebra (realCliffordForm 4 0))) 3, ← map_mul]
    norm_num

/-- The unit `u` is `2 + ω`. -/
@[simp]
theorem val_realCliffordFourZeroVolumeUnit :
    (realCliffordFourZeroVolumeUnit : CliffordAlgebra (realCliffordForm 4 0)) =
      2 + realCliffordFourZeroVolume := (rfl)

/-- The inverse of `u` is `(2 - ω) / 3`. -/
@[simp]
theorem val_inv_realCliffordFourZeroVolumeUnit :
    ((realCliffordFourZeroVolumeUnit⁻¹ : (CliffordAlgebra (realCliffordForm 4 0))ˣ) :
        CliffordAlgebra (realCliffordForm 4 0)) =
      (3⁻¹ : ℝ) • (2 - realCliffordFourZeroVolume) := (rfl)

/-- Conjugation `x ↦ u x u⁻¹` of `Cliff(4, 0)` by the even unit `u = 2 + ω`. -/
noncomputable def realCliffordFourZeroVolumeConj :
    CliffordAlgebra (realCliffordForm 4 0) ≃ₐ[ℝ] CliffordAlgebra (realCliffordForm 4 0) :=
  MulSemiringAction.toAlgEquiv ℝ _ (ConjAct.toConjAct realCliffordFourZeroVolumeUnit)

/-- Conjugation by `u` is `x ↦ (2 + ω) x (2 - ω) / 3`. -/
theorem realCliffordFourZeroVolumeConj_apply (x : CliffordAlgebra (realCliffordForm 4 0)) :
    realCliffordFourZeroVolumeConj x =
      (2 + realCliffordFourZeroVolume) * x * ((3⁻¹ : ℝ) • (2 - realCliffordFourZeroVolume)) := by
  simp [realCliffordFourZeroVolumeConj, ConjAct.units_smul_def]

/-- **Conjugation by `2 + ω` preserves the `ℤ/2`-grading.** -/
theorem evenOdd_map_realCliffordFourZeroVolumeConj (i : ZMod 2) :
    (evenOdd (realCliffordForm 4 0) i).map realCliffordFourZeroVolumeConj.toLinearMap =
      evenOdd (realCliffordForm 4 0) i := by
  have h2 : (2 : CliffordAlgebra (realCliffordForm 4 0)) ∈ evenOdd (realCliffordForm 4 0) 0 := by
    rw [← (one_add_one_eq_two : (1 : CliffordAlgebra (realCliffordForm 4 0)) + 1 = 2)]
    exact add_mem (Submodule.one_le.mp (one_le_evenOdd_zero _))
      (Submodule.one_le.mp (one_le_evenOdd_zero _))
  have hplus := add_mem h2 realCliffordFourZeroVolume_mem_evenOdd_zero
  have hminus := Submodule.smul_mem _ (3⁻¹ : ℝ)
    (sub_mem h2 realCliffordFourZeroVolume_mem_evenOdd_zero)
  refine le_antisymm (Submodule.map_le_iff_le_comap.mpr fun x hx ↦ ?_) fun x hx ↦
    ⟨realCliffordFourZeroVolumeConj.symm x, ?_, by simp⟩
  · rw [Submodule.mem_comap, AlgEquiv.toLinearMap_apply, realCliffordFourZeroVolumeConj_apply]
    simpa using SetLike.mul_mem_graded (SetLike.mul_mem_graded hplus hx) hminus
  · simp only [realCliffordFourZeroVolumeConj, MulSemiringAction.toAlgEquiv_symm_apply,
      ConjAct.units_smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
      val_inv_realCliffordFourZeroVolumeUnit, val_realCliffordFourZeroVolumeUnit]
    simpa using SetLike.mul_mem_graded (SetLike.mul_mem_graded hminus hx) hplus

/-- Conjugation by `2 + ω` sends the generator `e₁` to `(5 e₁ - 4 e₂ e₃ e₄) / 3`. -/
theorem realCliffordFourZeroVolumeConj_ι_single_zero :
    realCliffordFourZeroVolumeConj (ι (realCliffordForm 4 0) (Pi.single 0 1)) =
      (5 / 3 : ℝ) • ι (realCliffordForm 4 0) (Pi.single 0 1) -
        (4 / 3 : ℝ) • (ι (realCliffordForm 4 0) (Pi.single 1 1) * ι _ (Pi.single 2 1) *
          ι _ (Pi.single 3 1)) := by
  have key := algebraMap_add_smul_mul_ι_mul_algebraMap_sub_smul
    (realCliffordFourZeroVolume_mul_self.trans (map_one _).symm)
    (realCliffordFourZeroVolume_mul_ι (Pi.single 0 1)) (2 : ℝ) 1
  norm_num [map_ofNat] at key
  rw [realCliffordFourZeroVolumeConj_apply, mul_smul_comm, key, realCliffordFourZeroVolume_mul_ι,
    ι_single_zero_mul_volume]
  module

/-- Conjugation by `2 + ω` moves the generator `e₁` out of the first step of the word
filtration. -/
theorem realCliffordFourZeroVolumeConj_ι_single_zero_notMem_filtration_one :
    realCliffordFourZeroVolumeConj (ι (realCliffordForm 4 0) (Pi.single 0 1)) ∉
      filtration (realCliffordForm 4 0) 1 := by
  intro h
  -- The degree-three part `e₂ e₃ e₄ = e₁ ω = -(ω e₁)` would lie in `filtration Q 1`.
  have hmem : realCliffordFourZeroVolume * ι (realCliffordForm 4 0) (Pi.single 0 1) ∈
      filtration (realCliffordForm 4 0) 1 := by
    rw [realCliffordFourZeroVolumeConj_ι_single_zero, ← ι_single_zero_mul_volume] at h
    rw [realCliffordFourZeroVolume_mul_ι]
    have h' := Submodule.smul_mem _ (3 / 4 : ℝ)
      (sub_mem h (Submodule.smul_mem _ (5 / 3 : ℝ) (ι_mem_filtration_one _ (Pi.single 0 1))))
    convert h' using 1
    module
  -- It is odd, so its scalar part vanishes and it lies in the vectors.
  have hodd : realCliffordFourZeroVolume * ι (realCliffordForm 4 0) (Pi.single 0 1) ∈
      evenOdd (realCliffordForm 4 0) 1 := by
    simpa using SetLike.mul_mem_graded realCliffordFourZeroVolume_mem_evenOdd_zero
      (ι_mem_evenOdd_one _ (Pi.single 0 1))
  rw [← range_scalarAddVector] at hmem
  obtain ⟨⟨r, m⟩, hrm⟩ := hmem
  rw [scalarAddVector_apply] at hrm
  have hr : algebraMap ℝ (CliffordAlgebra (realCliffordForm 4 0)) r = 0 := by
    have h0 : algebraMap ℝ (CliffordAlgebra (realCliffordForm 4 0)) r ∈
        evenOdd (realCliffordForm 4 0) 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.one_le.mp (one_le_evenOdd_zero _))
    have h1 : algebraMap ℝ (CliffordAlgebra (realCliffordForm 4 0)) r ∈
        evenOdd (realCliffordForm 4 0) 1 := by
      rw [eq_sub_of_add_eq hrm]
      exact sub_mem hodd (ι_mem_evenOdd_one _ m)
    exact Submodule.disjoint_def.mp (evenOdd_isCompl _).disjoint _ h0 h1
  rw [hr, zero_add] at hrm
  -- But the volume element of four orthogonal anisotropic vectors moves `e₁` out of the vectors.
  refine prod_map_ι_mul_ι_notMem_range_ι pairwise_isOrtho_basisList (by decide) (by decide)
    realCliffordForm_ne_zero_of_mem_basisList (v := Pi.single 0 1) (by simp [basisList]) ?_
  rw [← realCliffordFourZeroVolume_eq_prod, ← hrm]
  exact LinearMap.mem_range_self _ m

/-- **Conjugation by `2 + ω` does not preserve the first step of the word filtration**, although
it preserves the `ℤ/2`-grading (`TauCeti.evenOdd_map_realCliffordFourZeroVolumeConj`). -/
theorem filtration_one_map_realCliffordFourZeroVolumeConj_ne :
    (filtration (realCliffordForm 4 0) 1).map realCliffordFourZeroVolumeConj.toLinearMap ≠
      filtration (realCliffordForm 4 0) 1 := fun h ↦
  realCliffordFourZeroVolumeConj_ι_single_zero_notMem_filtration_one <|
    h ▸ Submodule.mem_map_of_mem (ι_mem_filtration_one _ _)

/-- **Conjugation by `2 + ω` is not induced by an isometry.** -/
theorem realCliffordFourZeroVolumeConj_ne_equivOfIsometry
    (f : (realCliffordForm 4 0).IsometryEquiv (realCliffordForm 4 0)) :
    realCliffordFourZeroVolumeConj ≠ equivOfIsometry f := fun h ↦
  realCliffordFourZeroVolumeConj_ι_single_zero_notMem_filtration_one <| by
    rw [h, equivOfIsometry_apply, map_apply_ι]
    exact ι_mem_filtration_one _ _

end TauCeti

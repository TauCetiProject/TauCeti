/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.CategoryTheory.CStar.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Diagonal
import TauCeti.Analysis.InnerProductSpace.Modulus

/-!
# The C⋆-category of complex Hilbert spaces

Complex Hilbert spaces with bounded linear operators and the Hilbert-space adjoint form a
C⋆-category (`TauCeti.HilbertCat.instCStarCategory`). Positivity of `f ≫ f†` in `End X` is
witnessed directly by the bounded operator modulus `ContinuousLinearMap.modulus`.

The canonical `⋆`-algebra equivalence `HilbertCat.endStarAlgEquiv X : End X ≃⋆ₐ[ℂ] (X →L[ℂ] X)`
is isometric and identifies the C⋆-algebra spectral order on `End X` with Mathlib's Loewner order
on `X →L[ℂ] X` (`HilbertCat.end_le_iff`, `HilbertCat.end_nonneg_iff_isPositive`).

We also record the elementary boundary checks:
* The zero Hilbert space `HilbertCat.of ℂ PUnit` has subsingleton endomorphism algebra whose unit
  has norm `0`, whereas every nontrivial Hilbert space has `‖𝟙 X‖ = 1`.
* On `EuclideanSpace ℂ (Fin 2)`, the diagonal operator `diag(2, 1)` satisfies the C⋆-identity
  `‖f ≫ f†‖ = 4 = ‖f‖ ^ 2` in operator norm, while its Hilbert–Schmidt norm gives
  `‖f‖_HS ^ 2 = 5` and `‖f ≫ f†‖_HS = √17 ≠ 5`, showing that the Hilbert–Schmidt norm fails the
  C⋆-identity.
-/

public section

noncomputable section

open CategoryTheory
open scoped lp ENNReal InnerProductSpace

universe v

namespace TauCeti.HilbertCat

/-- Complex Hilbert spaces with continuous linear maps and adjoints form a C⋆-category,
retaining the existing Banach-space structures on `X →L[ℂ] Y`. -/
instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  norm_comp_le' f g := (HilbertCat.norm_comp_le f g).trans_eq (mul_comm _ _)
  norm_sq_le_norm_self_comp_dagger' f := by
    simpa only [sq] using (HilbertCat.norm_self_comp_dagger f).ge
  exists_self_comp_dagger f := by
    exact ⟨f.modulus, by simp only [comp_eq_comp, dagger_eq_adjoint,
      ContinuousLinearMap.adjoint_modulus, ContinuousLinearMap.modulus_comp_modulus]⟩

/-! ### Definitional compatibility of the Hom Banach structures -/

private theorem instNormedAddCommGroupHom_eq (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.instNormedAddCommGroupHom X Y =
      inferInstanceAs (NormedAddCommGroup (X ⟶ Y)) := rfl

private theorem instNormedSpaceHom_eq (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.instNormedSpaceHom X Y =
      inferInstanceAs (NormedSpace ℂ (X ⟶ Y)) := rfl

private theorem instCompleteSpaceHom_eq (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.instCompleteSpaceHom X Y =
      inferInstanceAs (CompleteSpace (X ⟶ Y)) := rfl

/-! ### Endomorphism algebra identification -/

/-- `HilbertCat.endStarAlgEquiv` is an isometry onto `X →L[ℂ] X`. -/
theorem endStarAlgEquiv_isometry (X : HilbertCat.{0, v} ℂ) :
    Isometry (endStarAlgEquiv X) :=
  StarAlgEquiv.isometry (endStarAlgEquiv X)

/-- The spectral order on `CategoryTheory.End X` coincides with the Loewner order on
`X →L[ℂ] X`. -/
theorem end_le_iff (X : HilbertCat.{0, v} ℂ) {a b : End X} :
    a ≤ b ↔ ConcreteCategory.hom a.asHom ≤ ConcreteCategory.hom b.asHom := by
  simpa only [endStarAlgEquiv_apply] using
    (NonUnitalStarAlgHom.map_le_map_iff (endStarAlgEquiv X) (endStarAlgEquiv X).injective).symm

/-- An endomorphism of a complex Hilbert space is positive in the C⋆-category sense iff its
underlying operator is positive in the sense of `ContinuousLinearMap.IsPositive`. -/
theorem end_nonneg_iff_isPositive (X : HilbertCat.{0, v} ℂ) (a : End X) :
    0 ≤ a ↔ (ConcreteCategory.hom a.asHom).IsPositive := by
  rw [end_le_iff, ← ContinuousLinearMap.nonneg_iff_isPositive]
  rfl

/-! ### Zero-object unit norm check -/

/-- The endomorphism algebra of the zero Hilbert space `PUnit` is subsingleton. -/
theorem subsingleton_end_punit : Subsingleton (End (of ℂ PUnit.{v + 1})) :=
  (End.subsingleton_iff_isZero _).mpr isZero_punit

/-- The identity arrow of the zero Hilbert space `PUnit` has norm `0`. -/
@[simp]
theorem norm_id_punit : ‖𝟙 (of ℂ PUnit.{v + 1})‖ = 0 :=
  CStarCategory.norm_id_of_isZero isZero_punit

/-- The identity arrow of a nontrivial complex Hilbert space has norm `1`. -/
theorem norm_id_eq_one_of_nontrivial (X : HilbertCat.{0, v} ℂ) [Nontrivial X] :
    ‖𝟙 X‖ = 1 :=
  CStarCategory.norm_id_of_not_isZero fun h =>
    not_subsingleton X ((isZero_iff_subsingleton X).mp h)

/-! ### Operator norm vs Hilbert–Schmidt norm on `diag(2, 1)` -/

section DiagTwoOne

/-- The standard Hilbert basis of `EuclideanSpace ℂ (Fin 2)`. -/
private def fin2Basis : HilbertBasis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (EuclideanSpace.basisFun (Fin 2) ℂ).toHilbertBasis

/-- The bounded sequence `![2, 1]` in `ℓ^∞(Fin 2, ℂ)`. -/
private def twoOneSeq : ℓ^∞(Fin 2, ℂ) :=
  ⟨![(2 : ℂ), 1], Memℓp.all (E := fun _ : Fin 2 => ℂ) (p := ∞) ![(2 : ℂ), 1]⟩

/-- The diagonal operator `diag(2, 1)` on `ℂ²` viewed as an endomorphism in `HilbertCat ℂ`. -/
def diagTwoOne :
    of ℂ (EuclideanSpace ℂ (Fin 2)) ⟶ of ℂ (EuclideanSpace ℂ (Fin 2)) :=
  fin2Basis.diagonal twoOneSeq

/-- `diagTwoOne` acts on `ℂ²` by multiplying coordinate `0` by `2` and coordinate `1` by `1`. -/
@[simp]
theorem diagTwoOne_apply (x : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (ConcreteCategory.hom diagTwoOne x) i = (![(2 : ℂ), 1] i) * x i := by
  have hrepr (v : EuclideanSpace ℂ (Fin 2)) (j : Fin 2) : fin2Basis.repr v j = v j := by
    rw [HilbertBasis.repr_apply_apply]
    simp [fin2Basis, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  simpa only [hom_eq, diagTwoOne, hrepr, twoOneSeq] using fin2Basis.repr_diagonal twoOneSeq x i

private theorem norm_twoOneSeq : ‖twoOneSeq‖ = 2 := by
  rw [lp.norm_eq_ciSup]
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun i => ?_
    fin_cases i <;> norm_num [twoOneSeq]
  · calc (2 : ℝ) = ‖twoOneSeq 0‖ := by norm_num [twoOneSeq]
      _ ≤ ⨆ i : Fin 2, ‖twoOneSeq i‖ :=
        le_ciSup (f := fun i : Fin 2 => ‖twoOneSeq i‖) (Set.finite_range _).bddAbove 0

private theorem nnnorm_fin2Basis (i : Fin 2) : ‖fin2Basis i‖₊ = 1 := by
  ext
  exact fin2Basis.orthonormal.1 i

/-- The operator norm of `diag(2, 1)` on `ℂ²` is `2`. -/
theorem norm_diagTwoOne : ‖diagTwoOne‖ = 2 := by
  change ‖fin2Basis.diagonal twoOneSeq‖ = 2
  rw [fin2Basis.norm_diagonal, norm_twoOneSeq]

/-- In operator norm, `diag(2, 1)` satisfies `‖f ≫ f†‖ = 4 = ‖f‖ ^ 2`. -/
theorem norm_diagTwoOne_comp_dagger :
    ‖diagTwoOne ≫ dagger diagTwoOne‖ = 4 := by
  rw [CStarCategory.norm_self_comp_dagger, norm_diagTwoOne]
  norm_num

/-- `diag(2, 1)` is self-adjoint (`dagger diagTwoOne = diagTwoOne`). -/
theorem dagger_diagTwoOne : dagger diagTwoOne = diagTwoOne := by
  rw [dagger_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← fin2Basis.repr.inner_map_map, ← fin2Basis.repr.inner_map_map,
    lp.inner_eq_tsum, lp.inner_eq_tsum, tsum_fintype, tsum_fintype]
  simp only [Fin.sum_univ_two, diagTwoOne, HilbertBasis.repr_diagonal, RCLike.inner_apply,
    map_mul, twoOneSeq, Matrix.cons_val_zero, Matrix.cons_val_one, map_ofNat, map_one]
  ring

/-- The Hilbert–Schmidt norm of `diag(2, 1)` is `√5`, so its square is `5`. -/
theorem hilbertSchmidtNorm_sq_diagTwoOne :
    (ConcreteCategory.hom diagTwoOne).hilbertSchmidtNorm ^ 2 = 5 := by
  have henergy :
      (ConcreteCategory.hom diagTwoOne).hilbertSchmidtEnergy fin2Basis = 5 := by
    rw [ContinuousLinearMap.hilbertSchmidtEnergy_def, tsum_fintype, Fin.sum_univ_two]
    simp only [hom_eq, diagTwoOne, HilbertBasis.diagonal_apply_self, eNorm_eq_nnNorm, nnNorm_smul,
      nnnorm_fin2Basis, mul_one]
    norm_num [twoOneSeq]
  rw [ContinuousLinearMap.hilbertSchmidtNorm_eq_sqrt _ fin2Basis, henergy,
    ENNReal.toReal_ofNat, Real.sq_sqrt (by norm_num)]

/-- The Hilbert–Schmidt norm of `diag(2, 1) ≫ diag(2, 1)†` is `√17`. -/
theorem hilbertSchmidtNorm_diagTwoOne_comp_dagger :
    (ConcreteCategory.hom (diagTwoOne ≫ dagger diagTwoOne)).hilbertSchmidtNorm = Real.sqrt 17 := by
  have henergy :
      (ConcreteCategory.hom (diagTwoOne ≫ dagger diagTwoOne)).hilbertSchmidtEnergy fin2Basis =
        17 := by
    rw [dagger_diagTwoOne, comp_eq_comp, ContinuousLinearMap.hilbertSchmidtEnergy_def,
      tsum_fintype, Fin.sum_univ_two]
    simp only [hom_eq, ContinuousLinearMap.comp_apply, diagTwoOne, HilbertBasis.diagonal_apply_self,
      map_smul, smul_smul, eNorm_eq_nnNorm, nnNorm_smul, nnnorm_fin2Basis, mul_one]
    norm_num [twoOneSeq]
  rw [ContinuousLinearMap.hilbertSchmidtNorm_eq_sqrt _ fin2Basis, henergy, ENNReal.toReal_ofNat]

/-- On `ℂ²`, the Hilbert–Schmidt norm fails the C⋆-identity at `diag(2, 1)`:
`‖f ≫ f†‖_HS = √17 ≠ 5 = ‖f‖_HS ^ 2`. -/
theorem hilbertSchmidtNorm_diagTwoOne_comp_dagger_ne_sq :
    (ConcreteCategory.hom (diagTwoOne ≫ dagger diagTwoOne)).hilbertSchmidtNorm ≠
      (ConcreteCategory.hom diagTwoOne).hilbertSchmidtNorm ^ 2 := by
  rw [hilbertSchmidtNorm_diagTwoOne_comp_dagger, hilbertSchmidtNorm_sq_diagTwoOne]
  intro h
  have hsq := congrArg (· ^ 2) h
  rw [Real.sq_sqrt (by norm_num)] at hsq
  norm_num at hsq

end DiagTwoOne

end TauCeti.HilbertCat

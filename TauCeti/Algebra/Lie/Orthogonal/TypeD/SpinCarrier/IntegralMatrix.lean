/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading

/-!
# Integral matrices of type-D spin generators

The invariant spin lattice gives an integral matrix for each numbered simple root generator of
type `Dₙ`. Each generator squares to zero, so its root subgroup points are `1 + u X` over any
commutative ring.

Each generator acts through an even Clifford element, so it preserves the exterior parity of the
spin module: it maps the even half-spin summand `S⁺` and the odd one `S⁻` into themselves. In the
lattice basis, indexed by sign sets, this says that the integral matrix vanishes at every entry
joining two sign sets whose cardinalities have different parities.

## Main declarations

* `TauCeti.TypeDSpinCarrier.rootIntMatrix`: the integral matrix of a numbered root generator.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_mul_self`: every numbered root matrix squares to zero.
* `TauCeti.TypeDSpinCarrier.lie_rootIntMatrix_eq_zero`,
  `TauCeti.TypeDSpinCarrier.lie_lie_rootIntMatrix_eq_smul` and
  `TauCeti.TypeDSpinCarrier.lie_rootIntMatrix_lie_eq_zero`: Serre-generator bracket relations
  hold for the integral root matrices.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_apply_of_eq`: a signed root step determines its
  integral matrix column.
* `TauCeti.TypeDSpinCarrier.coe_rootSubgroupPoints_eq_one_add_smul`: a numbered root-subgroup
  point is `1 + u X`.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_eq_zero_of_card_ne`: the integral matrix does not join
  the two half-spin summands.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_eq_zero_of_weight_ne`: the integral matrix vanishes off
  its signed simple-root weight difference.
* `TauCeti.TypeDSpinCarrier.lie_rootIntMatrix_inl_inr`: the opposite-root bracket is the diagonal
  matrix of simple-coroot weights.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, §20.2.

The matrix construction and its column formula use the generic Kostant lattice API, and the
carrier interface follows the type-`B` one in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix`.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeDSpinCarrier

universe v

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ) (hn : 4 ≤ n)

/-- The integral matrix of a represented numbered simple root generator in the lattice basis. -/
noncomputable def rootIntMatrix (k : Fin n ⊕ Fin n) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  kostantRootGeneratorIntMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (latticeBasis n)

/-- The integral matrix of a numbered root generator is the matrix of its integral root operator
in the lattice basis. -/
theorem rootIntMatrix_eq_toMatrix (k : Fin n ⊕ Fin n) :
    rootIntMatrix n hn k = LinearMap.toMatrix (latticeBasis n) (latticeBasis n)
      (kostantRootOperator
        (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) k) := by
  rw [rootIntMatrix]
  exact kostantRootGeneratorIntMatrix_eq_toMatrix _ _ _ _ _ _ _

/-- The integral matrix of every numbered spin root generator squares to zero. -/
@[simp] theorem rootIntMatrix_mul_self (i : Fin n ⊕ Fin n) :
    rootIntMatrix n hn i * rootIntMatrix n hn i = 0 := by
  apply kostantRootGeneratorIntMatrix_mul_self
  simpa only [pow_two, rep] using
    (polarization n).typeDSpinRep_rootGenerator_sq (polarizationBasis n) hn i

section BracketRelations

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Commuting Serre root generators give commuting integral spin root matrices. -/
theorem lie_rootIntMatrix_eq_zero {i j : Fin n ⊕ Fin n}
    (h : ⁅TauCeti.serreRootGenerator (CartanMatrix.D n) i,
      TauCeti.serreRootGenerator (CartanMatrix.D n) j⁆ = 0) :
    ⁅rootIntMatrix n hn i, rootIntMatrix n hn j⁆ = 0 := by
  rw [rootIntMatrix, rootIntMatrix]
  exact lie_kostantRootGeneratorIntMatrix_eq_zero _ _ _ _ _ _ _ h

/-- An integer nested-bracket relation of Serre generators holds for the integral spin matrices. -/
theorem lie_lie_rootIntMatrix_eq_smul {i j k l : Fin n ⊕ Fin n} (c : ℤ)
    (h : ⁅⁅TauCeti.serreRootGenerator (CartanMatrix.D n) i,
        TauCeti.serreRootGenerator (CartanMatrix.D n) j⁆,
      TauCeti.serreRootGenerator (CartanMatrix.D n) k⁆ =
      c • TauCeti.serreRootGenerator (CartanMatrix.D n) l) :
    ⁅⁅rootIntMatrix n hn i, rootIntMatrix n hn j⁆, rootIntMatrix n hn k⁆ =
      c • rootIntMatrix n hn l := by
  simp only [rootIntMatrix]
  exact lie_lie_kostantRootGeneratorIntMatrix_eq_smul _ _ _ _ _ _ _ c h

/-- A vanishing right-nested Serre bracket vanishes on the integral spin root matrices. -/
theorem lie_rootIntMatrix_lie_eq_zero {i j k : Fin n ⊕ Fin n}
    (h : ⁅TauCeti.serreRootGenerator (CartanMatrix.D n) i,
      ⁅TauCeti.serreRootGenerator (CartanMatrix.D n) j,
        TauCeti.serreRootGenerator (CartanMatrix.D n) k⁆⁆ = 0) :
    ⁅rootIntMatrix n hn i, ⁅rootIntMatrix n hn j, rootIntMatrix n hn k⁆⁆ = 0 := by
  simp only [rootIntMatrix]
  exact lie_kostantRootGeneratorIntMatrix_lie_eq_zero _ _ _ _ _ _ _ h

end BracketRelations

/-- A represented root generator acts on a lattice basis vector by its integral matrix column. -/
theorem rep_rootGenerator_latticeBasis_eq_sum (k : Fin n ⊕ Fin n) (s : Fin (dimension n)) :
    rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))
        (latticeBasis n s : ExteriorAlgebra ℚ (polarization n).W) =
      ∑ r, rootIntMatrix n hn k r s •
        (latticeBasis n r : ExteriorAlgebra ℚ (polarization n).W) :=
  rep_rootGenerator_basis_eq_sum _ _ _ _ _ _ _ _

/-- A signed root-generator step gives the corresponding signed integral matrix column. -/
theorem rootIntMatrix_apply_of_eq (j : Fin n ⊕ Fin n)
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) (r : Fin (dimension n)) :
    rootIntMatrix n hn j r a = if r = a' then (c : ℤ) else 0 :=
  kostantRootGeneratorIntMatrix_apply_of_eq _ _ _ _ _ _ _ h r

/-- A numbered root subgroup point is `1 + u X` for the integral matrix of its generator. -/
theorem coe_rootSubgroupPoints_eq_one_add_smul (k : Fin n ⊕ Fin n)
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints n hn k A u : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + Multiplicative.toAdd u • (rootIntMatrix n hn k).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    kostantRootSubgroupMatrix_eq_one_add_smul _ _ _ _ _ _ _ _
      (rootIntMatrix n hn k) (nilpotencyClass_rep_rootGenerator_le_two n hn k)
      (rep_rootGenerator_latticeBasis_eq_sum n hn k)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

/-- **The integral matrix of a numbered root generator does not join the two half-spin
summands**: its entry vanishes whenever the two sign sets have cardinalities of different
parities. -/
theorem rootIntMatrix_eq_zero_of_card_ne (k : Fin n ⊕ Fin n) {a b : Fin (dimension n)}
    (hab : ((signSet n a).card : ZMod 2) ≠ (signSet n b).card) :
    rootIntMatrix n hn k a b = 0 := by
  have hmem := (polarization n).typeDSpinRep_rootGenerator_mem_evenOdd (polarizationBasis n) hn k
    ((polarizationBasis n).exteriorAlgebra_mem_evenOdd_card (signSet n b))
  rw [← coe_latticeBasis, ← rep, rep_rootGenerator_latticeBasis_eq_sum] at hmem
  have hcoord :=
    (polarizationBasis n).mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero.1 hmem (signSet n a) hab
  rw [map_sum] at hcoord
  simp only [coe_latticeBasis, map_zsmul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq] at hcoord
  simpa using hcoord

/-- **A numbered root matrix has no entries outside its signed simple-root weight difference.**
The weights are the integral spin weights, before any change of coefficient ring. -/
theorem rootIntMatrix_eq_zero_of_weight_ne (k : Fin n ⊕ Fin n) {a b : Fin (dimension n)}
    (hab : basisWeight n a - basisWeight n b ≠ TypeDStd.rootGeneratorWeight n k) :
    rootIntMatrix n hn k a b = 0 := by
  rw [rootIntMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  exact repr_eq_zero_of_isCartanWeightVector
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (latticeBasis n) (basisWeight n)
    (isCartanWeightVector_latticeBasis n hn)
    (isCartanWeightVector_coe_kostantRootOperator
      (TauCeti.serreRootGenerator (CartanMatrix.D n))
      (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn) k (TypeDStd.lie_serreH_serreRootGenerator n k)
      (isCartanWeightVector_latticeBasis n hn b))
    fun h ↦ hab (sub_eq_iff_eq_add'.mpr h)

private theorem rootOperator_commutator_apply (i : Fin n) (a : Fin (dimension n)) :
    ⁅kostantRootOperator (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) (.inl i),
      kostantRootOperator (TauCeti.serreRootGenerator (CartanMatrix.D n))
        (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) (.inr i)⁆ (latticeBasis n a) =
      basisWeight n a i • latticeBasis n a := by
  apply Subtype.ext
  have h := congrArg (fun f ↦ f (latticeBasis n a :
      ExteriorAlgebra ℚ (polarization n).W))
    (isSl2Triple_rep_rootGenerator n hn i).lie_e_f
  rw [(isCartanWeightVector_iff (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn)).mp
    (isCartanWeightVector_latticeBasis n hn a) i] at h
  simpa only [LinearMap.sub_apply, mul_apply_eq_comp,
    AddSubgroup.coe_sub, coe_kostantRootOperator_apply,
    AddSubgroupClass.coe_zsmul, Ring.lie_def, Int.cast_smul_eq_zsmul] using h

/-- The bracket of the integral opposite simple-root matrices is the diagonal matrix of
simple-coroot weights, before any specialization of the coefficient ring. -/
theorem lie_rootIntMatrix_inl_inr (i : Fin n) :
    ⁅rootIntMatrix n hn (.inl i), rootIntMatrix n hn (.inr i)⁆ =
      Matrix.diagonal (fun a ↦ basisWeight n a i) := by
  let E : Module.End ℤ (lattice n).toAddSubgroup := kostantRootOperator
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (.inl i)
  let F : Module.End ℤ (lattice n).toAddSubgroup := kostantRootOperator
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (.inr i)
  let m := LinearMap.toMatrix (latticeBasis n) (latticeBasis n)
  trans m (E * F - F * E)
  · calc
      _ = m E * m F - m F * m E := congrArg₂ (fun X Y ↦ X * Y - Y * X)
        (rootIntMatrix_eq_toMatrix n hn (.inl i))
        (rootIntMatrix_eq_toMatrix n hn (.inr i))
      _ = m (E * F) - m (F * E) := congrArg₂ (fun X Y ↦ X - Y)
        (LinearMap.toMatrix_mul (latticeBasis n) E F).symm
        (LinearMap.toMatrix_mul (latticeBasis n) F E).symm
      _ = _ := (m.map_sub (E * F) (F * E)).symm
  ext a b
  calc
    _ = (latticeBasis n).repr ((E * F - F * E) (latticeBasis n b)) a :=
      LinearMap.toMatrix_apply (latticeBasis n) (latticeBasis n) (E * F - F * E) a b
    _ = (latticeBasis n).repr (basisWeight n b i • latticeBasis n b) a :=
      congrArg (fun v ↦ (latticeBasis n).repr v a) (rootOperator_commutator_apply n hn i b)
    _ = _ := by
      rw [map_smul, Module.Basis.repr_self]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        Matrix.diagonal_apply, mul_ite, mul_one, mul_zero]
      split_ifs <;> grind

end TauCeti.TypeDSpinCarrier

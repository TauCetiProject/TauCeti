/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.SquareZeroCoroot

/-!
# Integral matrices of type-B spin generators

The invariant spin lattice gives an integral matrix for each numbered simple root generator.
Each generator squares to zero, so its root subgroup points are `1 + u X` over any commutative
ring. Each matrix is supported on the pairs of basis vectors whose integral spin weights differ
by the signed simple root of its generator. The bracket of opposite integral root matrices
is the diagonal matrix of the basis spin weights' simple-coroot coordinates.

## References

C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

-- The matrix construction, its column formulas, and the weight support use the generic Kostant
-- lattice API. The carrier interface follows
-- `TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix`.

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.TypeBSpinCarrier

universe v

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- The integral matrix of a represented numbered simple root generator in the lattice basis. -/
@[expose] noncomputable def rootIntMatrix (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  kostantRootGeneratorIntMatrix
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) j (latticeBasis n)

/-- The integral matrix of a numbered root generator is the matrix of its integral root operator
in the lattice basis. -/
theorem rootIntMatrix_eq_toMatrix (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootIntMatrix n j = LinearMap.toMatrix (latticeBasis n) (latticeBasis n)
      (kostantRootOperator
        (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
        (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n) j) :=
  -- `rootIntMatrix` is by definition this Kostant generator matrix; rewriting with its equation
  -- lemma instead times out in `whnf`.
  kostantRootGeneratorIntMatrix_eq_toMatrix
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) j (latticeBasis n)

/-- A represented root generator acts on a lattice basis vector by its integral matrix column. -/
theorem rep_rootGenerator_latticeBasis_eq_sum (j : Fin (n + 1) ⊕ Fin (n + 1))
    (s : Fin (dimension n)) :
    rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n s : ExteriorAlgebra ℚ (polarization n).W) =
      ∑ r, rootIntMatrix n j r s •
        (latticeBasis n r : ExteriorAlgebra ℚ (polarization n).W) :=
  rep_rootGenerator_basis_eq_sum _ _ _ _ _ _ _ _

/-- A signed root-generator step gives the corresponding signed integral matrix column. -/
theorem rootIntMatrix_apply_of_eq (j : Fin (n + 1) ⊕ Fin (n + 1))
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) (r : Fin (dimension n)) :
    rootIntMatrix n j r a = if r = a' then (c : ℤ) else 0 :=
  kostantRootGeneratorIntMatrix_apply_of_eq _ _ _ _ _ _ _ h r

/-- A numbered root subgroup point is `1 + u X` for the integral matrix of its generator. -/
theorem coe_rootSubgroupPoints_eq_one_add_smul (j : Fin (n + 1) ⊕ Fin (n + 1))
    (A : Type v) [CommRing A] (u : Multiplicative A) :
    ((rootSubgroupPoints n j A u : Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + Multiplicative.toAdd u • (rootIntMatrix n j).map (Int.cast : ℤ → A) := by
  rw [coe_rootSubgroupPoints]
  simpa only [MulEquiv.apply_symm_apply] using
    kostantRootSubgroupMatrix_eq_one_add_smul _ _ _ _ _ _ _ _
      (rootIntMatrix n j) (nilpotencyClass_rep_rootGenerator_le_two n j)
      (rep_rootGenerator_latticeBasis_eq_sum n j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)

/-- **A numbered root matrix has no entries outside its signed simple-root weight difference.**
The weights are the integral spin weights, before any change of coefficient ring. -/
theorem rootIntMatrix_eq_zero_of_weight_ne (j : Fin (n + 1) ⊕ Fin (n + 1))
    {a b : Fin (dimension n)} (hab : basisWeight n a - basisWeight n b ≠ rootGeneratorWeight n j) :
    rootIntMatrix n j a b = 0 := by
  rw [rootIntMatrix_eq_toMatrix, LinearMap.toMatrix_apply]
  exact repr_eq_zero_of_isCartanWeightVector
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (latticeBasis n) (basisWeight n)
    (isCartanWeightVector_latticeBasis n)
    (isCartanWeightVector_coe_kostantRootOperator
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n) j (lie_coroot_rootGenerator n j)
      (isCartanWeightVector_latticeBasis n b))
    fun h ↦ hab (sub_eq_iff_eq_add'.mpr h)

/-- **A positive numbered root matrix only raises along simple reflections.** Its column at a
spin-basis index whose weight pairs to `-1` with the simple coroot is supported at the reflected
index, and every other column vanishes, since spin weights pair with simple coroots in
`{-1, 0, 1}`. -/
theorem rootIntMatrix_inl_eq_zero_of_ne_basisReflection (i : Fin (n + 1))
    {a b : Fin (dimension n)} (h : basisWeight n b i = -1 → a ≠ basisReflection n i b) :
    rootIntMatrix n (.inl i) a b = 0 := by
  have hpair (c : Fin (dimension n)) :
      basisWeight n c i = -1 ∨ basisWeight n c i = 0 ∨ basisWeight n c i = 1 :=
    DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n c) i
  rcases hpair b with hneg | hb | hb
  · obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inl_exteriorBasis n i _ _ hneg
      (signSet_basisReflection n i b).symm
    rw [← coe_latticeBasis, ← coe_latticeBasis] at hc
    rw [rootIntMatrix_apply_of_eq n (.inl i) hc a, ite_eq_right (h hneg)]
  all_goals
    apply rootIntMatrix_eq_zero_of_weight_ne
    intro hw
    have hi := congrFun hw i
    rw [Pi.sub_apply, rootGeneratorWeight_inl, CartanMatrix.B_diag] at hi
    rcases hpair a with ha | ha | ha <;> omega

/-- The bracket of opposite integral root matrices is the diagonal matrix whose entry at each
basis vector is its spin weight's coordinate at simple coroot `i`. This identity remains integral
at the short terminal node. -/
theorem lie_rootIntMatrix_inl_inr (i : Fin (n + 1)) :
    ⁅rootIntMatrix n (.inl i), rootIntMatrix n (.inr i)⁆ =
      Matrix.diagonal (fun a ↦ basisWeight n a i) := by
  let E := kostantRootOperator
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n)
  let H := kostantCartanOperator
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) i
  have hEF : ⁅E (.inl i), E (.inr i)⁆ = H := by
    ext v
    have h := congrArg (fun f ↦ f (v : ExteriorAlgebra ℚ (polarization n).W))
      (isSl2Triple_rep_rootGenerator n i).lie_e_f
    simpa only [E, H, Ring.lie_def, LinearMap.sub_apply, Module.End.mul_eq_comp,
      LinearMap.comp_apply,
      AddSubgroup.coe_sub, coe_kostantRootOperator_apply, coe_kostantCartanOperator_apply]
      using h
  have hm := congrArg (LinearMap.toMatrix (latticeBasis n) (latticeBasis n)) hEF
  simp only [Ring.lie_def, map_sub, LinearMap.toMatrix_mul, E] at hm
  simp only [rootIntMatrix_eq_toMatrix, Ring.lie_def, hm]
  ext a b
  rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  simp only [H, kostantCartanOperator_apply_of_isCartanWeightVector _ _ _ _ _
    (isCartanWeightVector_latticeBasis n b) i, map_zsmul, Module.Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : a = b
  · subst b
    simp only [↓reduceIte, mul_one]
  · simp only [h, Ne.symm h, ↓reduceIte, mul_zero]

private noncomputable abbrev rootOp (j : Fin (n + 1) ⊕ Fin (n + 1)) :=
  kostantRootOperator
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) j

/-- Every numbered integral spin root matrix squares to zero. -/
theorem rootIntMatrix_mul_self (j : Fin (n + 1) ⊕ Fin (n + 1)) :
    rootIntMatrix n j * rootIntMatrix n j = 0 := by
  have h : rootOp n j * rootOp n j = 0 :=
    kostantRootOperator_mul_eq_zero _ _ (rep n) _ (rep_kostantForm_mem_lattice n)
    (by simpa only [pow_two] using pow_two_rep_rootGenerator_eq_zero n j)
  simpa only [rootIntMatrix_eq_toMatrix, LinearMap.toMatrix_mul, rootOp, map_zero] using
    congrArg (LinearMap.toMatrix (latticeBasis n) (latticeBasis n)) h

-- Compute the endpoint identities over ℚ, then restrict to the invariant lattice before
-- reducing coefficients. In particular no division by two occurs in the value ring.
private theorem rootIntMatrix_mul_mul_of_rep_eq (j k : Fin (n + 1) ⊕ Fin (n + 1))
    (hjk : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily j)) *
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily k)) *
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily j)) =
      rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.typeBSimpleRootGeneratorFamily j))) :
    rootIntMatrix n j * rootIntMatrix n k * rootIntMatrix n j = rootIntMatrix n j := by
  simpa only [rootIntMatrix_eq_toMatrix, LinearMap.toMatrix_mul] using
    congrArg (LinearMap.toMatrix (latticeBasis n) (latticeBasis n))
      (kostantRootOperator_mul_mul_eq _ _ (rep n) _ (rep_kostantForm_mem_lattice n) hjk)

/-- The integral raising and lowering matrices satisfy `EFE = E` at every numbered node. -/
theorem rootIntMatrix_inl_mul_inr_mul_inl (i : Fin (n + 1)) :
    rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i) =
      rootIntMatrix n (.inl i) :=
  rootIntMatrix_mul_mul_of_rep_eq n _ _
    (rootOperator_endpoint_relations_of_sq_eq_zero _ _ (rep n)
      (isSl2Triple_rep_rootGenerator n i)
      (pow_two_rep_rootGenerator_eq_zero n (.inl i))
      (pow_two_rep_rootGenerator_eq_zero n (.inr i))).1

/-- The integral lowering and raising matrices satisfy `FEF = F` at every numbered node. -/
theorem rootIntMatrix_inr_mul_inl_mul_inr (i : Fin (n + 1)) :
    rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i) =
      rootIntMatrix n (.inr i) :=
  rootIntMatrix_mul_mul_of_rep_eq n _ _
    (rootOperator_endpoint_relations_of_sq_eq_zero _ _ (rep n)
      (isSl2Triple_rep_rootGenerator n i)
      (pow_two_rep_rootGenerator_eq_zero n (.inl i))
      (pow_two_rep_rootGenerator_eq_zero n (.inr i))).2

private theorem rootOp_endpoint_projections_apply (i : Fin (n + 1))
    (a : Fin (dimension n)) :
    (rootOp n (.inl i) * rootOp n (.inr i)) (latticeBasis n a) =
        (if basisWeight n a i = 1 then latticeBasis n a else 0) ∧
      (rootOp n (.inr i) * rootOp n (.inl i)) (latticeBasis n a) =
        (if basisWeight n a i = -1 then latticeBasis n a else 0) :=
  kostantRootOperator_endpoint_projections_apply _ _ (rep n) _
    (rep_kostantForm_mem_lattice n) (isCartanWeightVector_latticeBasis n a)
    (isSl2Triple_rep_rootGenerator n i)
    (pow_two_rep_rootGenerator_eq_zero n (.inl i))
    (pow_two_rep_rootGenerator_eq_zero n (.inr i))

/-- The integral product `EF` projects onto the basis vectors of simple-coroot weight `1`. -/
theorem rootIntMatrix_inl_mul_inr (i : Fin (n + 1)) :
    rootIntMatrix n (.inl i) * rootIntMatrix n (.inr i) =
      Matrix.diagonal (fun a ↦ if basisWeight n a i = 1 then 1 else 0) := by
  simp only [rootIntMatrix_eq_toMatrix, ← LinearMap.toMatrix_mul]
  ext a b
  simp only [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  have hP := (rootOp_endpoint_projections_apply n i b).1
  simp only [rootOp] at hP
  simp only [hP, apply_ite, map_zero, Module.Basis.repr_self]
  clear hP
  split_ifs <;> simp_all

/-- The integral product `FE` projects onto the basis vectors of simple-coroot weight `-1`. -/
theorem rootIntMatrix_inr_mul_inl (i : Fin (n + 1)) :
    rootIntMatrix n (.inr i) * rootIntMatrix n (.inl i) =
      Matrix.diagonal (fun a ↦ if basisWeight n a i = -1 then 1 else 0) := by
  simp only [rootIntMatrix_eq_toMatrix, ← LinearMap.toMatrix_mul]
  ext a b
  simp only [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
  have hQ := (rootOp_endpoint_projections_apply n i b).2
  simp only [rootOp] at hQ
  simp only [hQ, apply_ite, map_zero, Module.Basis.repr_self]
  clear hQ
  split_ifs <;> simp_all

end TauCeti.TypeBSpinCarrier

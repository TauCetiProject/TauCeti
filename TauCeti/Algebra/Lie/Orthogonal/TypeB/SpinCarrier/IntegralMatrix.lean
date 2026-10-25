/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ClosedImmersion

/-!
# Integral matrices of type-B spin generators

The invariant spin lattice gives an integral matrix for each numbered simple root generator.
Each generator squares to zero, so its root subgroup points are `1 + u X` over any commutative
ring. Each matrix is supported on the pairs of basis vectors whose integral spin weights differ
by the signed simple root of its generator.

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
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) (latticeBasis n) (basisWeight n)
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

end TauCeti.TypeBSpinCarrier

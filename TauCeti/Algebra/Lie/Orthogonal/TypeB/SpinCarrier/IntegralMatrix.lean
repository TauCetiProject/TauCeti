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
ring. The matrix construction and its column formulas use the generic Kostant lattice API.
The carrier interface follows
`TauCeti.Algebra.Lie.Symplectic.StandardCarrier.IntegralMatrix`.

## References

C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
-/

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

end TauCeti.TypeBSpinCarrier

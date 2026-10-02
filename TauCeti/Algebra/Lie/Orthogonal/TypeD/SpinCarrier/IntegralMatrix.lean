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
* `TauCeti.TypeDSpinCarrier.coe_rootSubgroupPoints_eq_one_add_smul`: a numbered root-subgroup
  point is `1 + u X`.
* `TauCeti.TypeDSpinCarrier.rootIntMatrix_eq_zero_of_card_ne`: the integral matrix does not join
  the two half-spin summands.

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

variable (n : ℕ) (hn : 4 ≤ n)

/-- The integral matrix of a represented numbered simple root generator in the lattice basis. -/
noncomputable def rootIntMatrix (k : Fin n ⊕ Fin n) :
    Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
  kostantRootGeneratorIntMatrix
    (TauCeti.serreRootGenerator (CartanMatrix.D n))
    (TauCeti.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) k (latticeBasis n)

/-- A represented root generator acts on a lattice basis vector by its integral matrix column. -/
theorem rep_rootGenerator_latticeBasis_eq_sum (k : Fin n ⊕ Fin n) (s : Fin (dimension n)) :
    rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator (CartanMatrix.D n) k))
        (latticeBasis n s : ExteriorAlgebra ℚ (polarization n).W) =
      ∑ r, rootIntMatrix n hn k r s •
        (latticeBasis n r : ExteriorAlgebra ℚ (polarization n).W) :=
  rep_rootGenerator_basis_eq_sum _ _ _ _ _ _ _ _

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
  have hmem := (polarization n).typeDSpinRep_rootGenerator_mem_evenOdd (polarizationBasis n) hn
    (TauCeti.splitEvenPolarization_line ℚ n) k
    ((polarizationBasis n).exteriorAlgebra_mem_evenOdd_card (signSet n b))
  rw [← coe_latticeBasis, ← rep, rep_rootGenerator_latticeBasis_eq_sum] at hmem
  have hcoord :=
    (polarizationBasis n).mem_evenOdd_iff_exteriorAlgebra_repr_eq_zero.1 hmem (signSet n a) hab
  rw [map_sum] at hcoord
  simp only [coe_latticeBasis, map_zsmul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply,
    EmbeddingLike.apply_eq_iff_eq] at hcoord
  simpa using hcoord

end TauCeti.TypeDSpinCarrier

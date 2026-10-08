/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.BaseChange
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Levi.Geometry

/-!
# The doubled E₆ carrier preserves its minuscule summands

The integral doubled minuscule carrier lies in the block-diagonal subgroup `GL₂₇ × GL₂₇`
of `GL₅₄`, with blocks labelled by `matrixSummand`. Every numbered root subgroup has zero
entries between the two summands, as does the diagonal weight torus. Their scheme-theoretic
closure therefore has the same property. The resulting coordinate equations hold after base
change to any commutative ring and make the two summands subcomodules of the standard carrier
representation.

This containment does not identify the carrier with the pinned simply connected group scheme
of type `E₆`. Constructions on this explicit carrier transfer to that pinned group along such
an identification once one is proved.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1–2.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* The containment argument follows `TauCeti.Algebra.Lie.D4.Tripled.Levi`, using the generic
  square-zero root-subgroup and weight-Levi kernel criteria.
-/

public section

open CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix TensorProduct

namespace TauCeti.E6DoubledMinuscule

attribute [local instance] TauCeti.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

/-- The integral doubled minuscule carrier lies in the block-diagonal subgroup of its two
summands, scheme-theoretically. -/
theorem weightLeviDefiningHopfIdeal_le_definingIdeal :
    GeneralLinear.weightLeviDefiningHopfIdeal ℤ matrixSummand ≤ definingIdeal := by
  rw [definingIdeal_def, le_kostantToralDefiningIdeal_iff]
  refine ⟨fun j ↦ ?_, ?_⟩
  · apply GeneralLinear.weightLeviDefiningHopfIdeal_toIdeal_le_ker
    intro a b hab
    have hne : a ≠ b := fun h ↦ hab (congrArg matrixSummand h)
    have hmatrix := map_genericMatrix_kostantRootSubgroupCoordinateMap_eq_one_add_smul
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep lattice.toAddSubgroup
      rep_kostantForm_mem_lattice j (isNilpotent_rep_serreRootGenerator j) matrixBasis
      (rootIntMatrix j) (nilpotencyClass_rep_rootGenerator_le_two j)
      (rep_rootGenerator_matrixBasis_eq_sum j)
    have hentry := congrArg (fun M ↦ M a b) hmatrix
    simpa only [Matrix.map_apply, GeneralLinear.genericMatrix_apply, Matrix.add_apply,
      Matrix.one_apply_ne hne, Matrix.smul_apply, rootIntMatrix_eq_zero_of_summand_ne j hab,
      Int.cast_zero, smul_zero, zero_add, BialgHom.coe_toAlgHom] using hentry
  · apply GeneralLinear.weightLeviDefiningHopfIdeal_toIdeal_le_ker
    intro a b hab
    have hne : a ≠ b := fun h ↦ hab (congrArg matrixSummand h)
    simpa only [hne, ↓reduceIte, BialgHom.coe_toAlgHom] using
      GeneralLinear.weightTorusCoordinateMap_X (R := ℤ) matrixWeight a b

variable (A : Type*) [CommRing A]

/-- Every coordinate between the two minuscule summands vanishes on the base-changed carrier,
over any commutative ring. -/
theorem coordinateMap_X_eq_zero {a b : Fin 54} (hab : matrixSummand a ≠ matrixSummand b) :
    (coordinateMap A).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv A 54
      (GeneralLinear.coordinateRingMap A 54 (MvPolynomial.X (a, b)))) = 0 := by
  have hmem : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 54
      (GeneralLinear.coordinateRingMap ℤ 54 (MvPolynomial.X (a, b))) ∈ definingIdeal := by
    apply weightLeviDefiningHopfIdeal_le_definingIdeal
    rw [← HopfIdeal.mem_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem]
    exact GeneralLinear.weightLeviQuotient_mk_genericMatrix_apply_of_ne ℤ matrixSummand hab
  have h := map_tmul_mem_baseChangeDefiningIdeal_of_mem A 1 hmem
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply, MvPolynomial.map_X,
    one_smul] at h
  rw [← RingHom.mem_ker, coordinateMap_ker]
  exact h

end TauCeti.E6DoubledMinuscule

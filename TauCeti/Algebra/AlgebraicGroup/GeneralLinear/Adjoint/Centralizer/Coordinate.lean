/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Centralizer.Basic
public import TauCeti.Algebra.AlgebraicGroup.MatrixMonoid.Centralizer
public import TauCeti.RingTheory.Localization.Away.Quotient

/-!
# The determinant open locus of a matrix centralizer

The scheme-theoretic centralizer of a matrix in `GLₙ` is the determinant open subscheme
of the affine scheme cut out by the linear commuting-matrix equations. We identify its
defining ideal with the extension of those equations to the general linear coordinate ring,
and its coordinate algebra with their quotient localized at the determinant.

The ideal comparison uses points over arbitrary commutative algebras, rather than only
field-valued points, so retains the full scheme structure.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1.
-/

public section

noncomputable section

namespace TauCeti.GeneralLinear

open WithConv

universe u

variable {k : Type u} [Field k] {n : ℕ}

private theorem map_centralizerIdeal_le_ker_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    {A : Type u} [CommRing A] [Algebra k A]
    (f : coordinateHopfAlgebra k n →ₐ[k] A) :
    (Matrix.centralizerIdeal (cotangentDualMatrixEquiv x)).map
        (((coordinateHopfAlgebraAlgEquiv k n).toAlgHom.comp
          (coordinateRingMap k n)).toRingHom) ≤ RingHom.ker f ↔
      (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal ≤ RingHom.ker f := by
  -- Express the pulled-back kernel using the bundled composite algebra homomorphism.
  rw [Ideal.map_le_iff_le_comap, AlgHom.ker_coe, RingHom.comap_ker,
    AlgHom.toRingHom_eq_coe, ← AlgHom.comp_toRingHom, ← AlgHom.ker_coe,
    Matrix.centralizerIdeal_le_ker_iff, ← AlgHom.ker_coe,
    centralizerHopfIdeal_le_ker_iff_commute x (toConv f)]
  have hM : (Matrix.mvPolynomialX (Fin n) (Fin n) k).map
        (f.comp ((coordinateHopfAlgebraAlgEquiv k n).toAlgHom.comp
          (coordinateRingMap k n))) =
      (pointsMulEquiv n (toConv f) : Matrix (Fin n) (Fin n) A) := by
    ext i j
    simp [Matrix.mvPolynomialX, pointToGeneralLinear_apply]
  rw [hM]

/-- The scheme centralizer in `GLₙ` is defined by extending the linear commuting-matrix
equations along the determinant localization. -/
theorem centralizerHopfIdeal_toIdeal_eq_map_centralizerIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal =
      (Matrix.centralizerIdeal (cotangentDualMatrixEquiv x)).map
        (((coordinateHopfAlgebraAlgEquiv k n).toAlgHom.comp
          (coordinateRingMap k n)).toRingHom) := by
  apply le_antisymm
  · have h := (map_centralizerIdeal_le_ker_iff x
        (Ideal.Quotient.mkₐ k ((Matrix.centralizerIdeal
          (cotangentDualMatrixEquiv x)).map
            (((coordinateHopfAlgebraAlgEquiv k n).toAlgHom.comp
              (coordinateRingMap k n)).toRingHom)))).mp
    simpa only [AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker] using
      h (by rw [AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker])
  · have h := (map_centralizerIdeal_le_ker_iff x
        (Ideal.Quotient.mkₐ k
          (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal)).mpr
    simpa only [AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker] using
      h (by rw [AlgHom.ker_coe, Ideal.Quotient.mkₐ_ker])

/-- The coordinate algebra of the group centralizer is the determinant localization of the
affine commuting-matrix scheme. This includes matrices of size zero, and needs neither
algebraic closure nor characteristic zero. -/
def centralizerCoordinateAlgEquiv
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    Localization.Away
        (Ideal.Quotient.mk (Matrix.centralizerIdeal (cotangentDualMatrixEquiv x))
          (Matrix.mvPolynomialX (Fin n) (Fin n) k).det) ≃ₐ[k]
      coordinateHopfAlgebra k n ⧸
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal := by
  let I := Matrix.centralizerIdeal (cotangentDualMatrixEquiv x)
  let J := I.map (algebraMap (MatrixMonoid.CoordinateRing k (Fin n)) (CoordinateRing k n))
  letI : IsScalarTower k (MatrixMonoid.CoordinateRing k (Fin n) ⧸ I)
      (CoordinateRing k n ⧸ J) :=
    IsScalarTower.to₁₃₄ k (MatrixMonoid.CoordinateRing k (Fin n)) _ _
  let e := (IsLocalization.algEquiv
    (Submonoid.powers (Ideal.Quotient.mk I (Matrix.mvPolynomialX (Fin n) (Fin n) k).det))
    (Localization.Away (Ideal.Quotient.mk I
      (Matrix.mvPolynomialX (Fin n) (Fin n) k).det)) (CoordinateRing k n ⧸ J)).restrictScalars k
  refine e.trans (Ideal.quotientEquivAlg J _ (coordinateHopfAlgebraAlgEquiv k n) ?_)
  rw [centralizerHopfIdeal_toIdeal_eq_map_centralizerIdeal, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  simp only [AlgHom.toRingHom_eq_coe, RingHom.comp_apply, AlgHom.coe_toRingHom,
    AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, coordinateRingMap_apply]
  -- The quotient equivalence uses the ring-hom coercion of the same algebra equivalence.
  rfl

/-- The centralizer coordinate equivalence carries a polynomial function to the restriction
of the same polynomial in the general linear matrix entries. -/
@[simp]
theorem centralizerCoordinateAlgEquiv_algebraMap
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (p : MatrixMonoid.CoordinateRing k (Fin n)) :
    centralizerCoordinateAlgEquiv x
        (algebraMap _ _ (Ideal.Quotient.mk
          (Matrix.centralizerIdeal (cotangentDualMatrixEquiv x)) p)) =
      Ideal.Quotient.mk (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal
        (coordinateHopfAlgebraAlgEquiv k n (coordinateRingMap k n p)) := by
  simp only [centralizerCoordinateAlgEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, AlgEquiv.commutes,
    Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.quotientEquivAlg_mk]
  rw [coordinateRingMap_apply]

/-- The inverse coordinate equivalence restricts polynomial matrix functions to the
determinant open locus of the commuting-matrix scheme. -/
@[simp]
theorem centralizerCoordinateAlgEquiv_symm_mk
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (p : MatrixMonoid.CoordinateRing k (Fin n)) :
    (centralizerCoordinateAlgEquiv x).symm
        (Ideal.Quotient.mk (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal
          (coordinateHopfAlgebraAlgEquiv k n (coordinateRingMap k n p))) =
      algebraMap _ _ (Ideal.Quotient.mk
        (Matrix.centralizerIdeal (cotangentDualMatrixEquiv x)) p) := by
  apply (centralizerCoordinateAlgEquiv x).symm_apply_eq.mpr
  exact (centralizerCoordinateAlgEquiv_algebraMap x p).symm

end TauCeti.GeneralLinear

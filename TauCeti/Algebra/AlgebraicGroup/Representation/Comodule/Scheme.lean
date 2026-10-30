/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Coordinate
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.PointAction

/-!
# Comodules and morphisms of group schemes into general linear groups

A finite basis identifies right comodule structures over `H` with group-scheme morphisms
`Spec H → GLₙ`. This is the coordinate correspondence transported through Mathlib's full
faithfulness of `AlgebraicGeometry.hopfSpec`. The forward map is the existing
`TauCeti.Comodule.coordinateGroupSchemeHom`; the inverse recovers an actual coaction.

The coefficient and point-action formulas identify this representation with the original
coordinate morphism on every commutative value algebra, including nonreduced ones.
Faithfulness of the recovered comodule is equivalent to the given morphism being a closed
immersion. No field, finite-type or smoothness assumption on `H` is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 4(a).
* The affine dictionary uses Mathlib's `AlgebraicGeometry.hopfSpec.fullyFaithful`.
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti

namespace Module.Basis

universe u v

variable {R H M : Type u} {n : ℕ}
variable [CommRing R] [CommRing H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M]

/-- Comodule structures correspond to morphisms from the represented group scheme into
`GLₙ`, using the given basis to identify its representation space with column vectors. -/
noncomputable def comoduleEquivGroupSchemeHom (b : Basis (Fin n) R M) :
    Comodule R H M ≃
      ((hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
        GeneralLinear.groupScheme R n) :=
  b.comoduleEquivCoordinateBialgHom.trans <|
    (ConcreteCategory.homEquiv (C := CommHopfAlgCat R)
      (X := GeneralLinear.coordinateHopfAlgebra R n) (Y := CommHopfAlgCat.of R H)).symm.trans <|
    (opEquiv (Opposite.op (CommHopfAlgCat.of R H))
      (Opposite.op (GeneralLinear.coordinateHopfAlgebra R n))).symm.trans <|
    (hopfSpec.fullyFaithful (R := CommRingCat.of R)).homEquiv.trans <|
    Iso.homCongr (Iso.refl _) (eqToIso (GeneralLinear.groupScheme_def R n)).symm

/-- The forward correspondence is the group-scheme map defined by the coefficient matrix. -/
-- Keep this as a rewrite: simp also changes the Hopf-spectrum object in the source type.
theorem comoduleEquivGroupSchemeHom_apply (b : Basis (Fin n) R M)
    (rho : Comodule R H M) :
    b.comoduleEquivGroupSchemeHom rho =
      letI := rho
      Comodule.coordinateGroupSchemeHom (H := H) b := by
  simp only [comoduleEquivGroupSchemeHom, Equiv.trans_apply,
    comoduleEquivCoordinateBialgHom_apply, Iso.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  rw [Comodule.coordinateGroupSchemeHom_def]
  rfl

/-- The inverse correspondence recovers the comodule of the unique coordinate map represented
by the given group-scheme morphism. -/
theorem comoduleEquivGroupSchemeHom_symm_apply (b : Basis (Fin n) R M)
    (f : (hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
      GeneralLinear.groupScheme R n) :
    b.comoduleEquivGroupSchemeHom.symm f =
      b.comoduleOfCoordinateBialgHom
        (((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage
          (f ≫ eqToHom (GeneralLinear.groupScheme_def R n))).unop.hom) := by
  simp [comoduleEquivGroupSchemeHom, Iso.homCongr, ConcreteCategory.homEquiv, opEquiv]

/-- The matrix of the algebra-valued point action is obtained by evaluating the coordinate
map attached to the corresponding group-scheme morphism. -/
theorem toMatrix_endOfPoint_comoduleEquivGroupSchemeHom_symm
    (b : Basis (Fin n) R M)
    (f : (hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
      GeneralLinear.groupScheme R n)
    {A : Type v} [CommRing A] [Algebra R A] (p : H →ₐ[R] A) :
    letI := b.comoduleEquivGroupSchemeHom.symm f
    LinearMap.toMatrix (b.baseChange A) (b.baseChange A) (Comodule.endOfPoint M p) =
      (GeneralLinear.genericMatrix R n).map
        (p.comp (((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage
          (f ≫ eqToHom (GeneralLinear.groupScheme_def R n))).unop.hom).toAlgHom) := by
  rw [comoduleEquivGroupSchemeHom_symm_apply]
  let := b.comoduleOfCoordinateBialgHom
    (((hopfSpec.fullyFaithful (R := CommRingCat.of R)).preimage
      (f ≫ eqToHom (GeneralLinear.groupScheme_def R n))).unop.hom)
  rw [Comodule.toMatrix_endOfPoint, coefficientMatrix_comoduleOfCoordinateBialgHom]
  ext i j
  rfl

/-- A group-scheme representation is a closed immersion exactly when its recovered comodule
is faithful. This tests the entire group scheme, rather than only field-valued points. -/
theorem isFaithful_comoduleEquivGroupSchemeHom_symm_iff
    (b : Basis (Fin n) R M)
    (f : (hopfSpec (CommRingCat.of R)).obj (Opposite.op (CommHopfAlgCat.of R H)) ⟶
      GeneralLinear.groupScheme R n) :
    letI := b.comoduleEquivGroupSchemeHom.symm f
    Comodule.IsFaithful (k := R) (H := H) (V := M) ↔
      IsClosedImmersion f.hom.hom.left := by
  let := b.comoduleEquivGroupSchemeHom.symm f
  rw [Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b,
    ← comoduleEquivGroupSchemeHom_apply, Equiv.apply_symm_apply]

end Module.Basis

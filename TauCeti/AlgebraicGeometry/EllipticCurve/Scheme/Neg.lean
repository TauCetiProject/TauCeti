/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Neg
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The negation morphism of the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`. The change of variables
`negVariableChange W = ⟨-1, 0, -a₁, -a₃⟩` fixes `W`, so the isomorphism
`projModelVariableChangeIso W (negVariableChange W)` it induces is, through
`negVariableChange W • W = W`, an automorphism of the projective Weierstrass model `projModel W`:
the negation morphism `projModelNeg W`, `[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]`. It is an
involution over `Spec R` fixing the zero section, which on points with homogeneous coordinates `P`
is Mathlib's negation `WeierstrassCurve.Projective.neg`,
`[P₀ : P₁ : P₂] ↦ [P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]`, and it commutes with base change and with the
isomorphisms induced by changes of variables. No ellipticity is needed.

Since every pointed isomorphism of projective models over the same base is induced by a change of
variables (`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), negation
commutes with every morphism of projective models that carries the zero section to the zero
section and is a base change square. This makes the negation of an elliptic curve over a scheme
independent of the local Weierstrass equations used to define it.

## Main definitions

* `WeierstrassCurve.projModelNeg W`: the negation morphism `projModel W ⟶ projModel W`.

## Main results

* `WeierstrassCurve.projModelNeg_projModelOver`: negation lies over `Spec R`.
* `WeierstrassCurve.projModelZero_projModelNeg`: negation fixes the zero section.
* `WeierstrassCurve.projModelNeg_projModelNeg`: negation is an involution.
* `WeierstrassCurve.isIso_projModelNeg`: negation is an isomorphism, its own inverse
  (`WeierstrassCurve.inv_projModelNeg`).
* `WeierstrassCurve.projModelPoint_projModelNeg`: negation sends the point with homogeneous
  coordinates `P` to the point with homogeneous coordinates `Projective.neg P`.
* `WeierstrassCurve.projModelNeg_projModelBaseChange`: negation commutes with the base change
  morphism `projModel (W.map f) ⟶ projModel W`.
* `WeierstrassCurve.projModelNeg_projModelVariableChangeIso_hom`: negation commutes with the
  isomorphism `projModel (C • W) ≅ projModel W` induced by a change of variables `C`.
* `WeierstrassCurve.projModelNeg_comp_hom_of_iso`: negation commutes with every pointed isomorphism
  of projective models over `Spec R`.
* `WeierstrassCurve.projModelNeg_comp_of_isPullback`: negation commutes with every pointed
  cartesian morphism of projective models.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*, III.2][silverman2009]

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/GroupLawConstruction.lean`, declarations
`negVec`, `negGradedQuot`, `negModelHom`, `negModelHom_π`, `negModelHom_negModelHom`,
`negModelHom_zero` and `negModelHom_specPoints`. Here the morphism is the isomorphism
`WeierstrassCurve.projModelVariableChangeIso` induced by the change of variables
`negVariableChange`, in place of `Proj` of the source's substitution `negVec`; the zero section is
fixed because every such isomorphism preserves it, in place of the source's rescaling automorphism
`allNegGradedQuot`; and the points are those of `projModelPoint`, for an arbitrary ring
homomorphism `g : R →+* S` and a solution with a unit coordinate, in place of the source's field
points matched with `W.toAffine.Point`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The **negation morphism** `[X : Y : Z] ↦ [X : -Y - a₁X - a₃Z : Z]` of the projective
Weierstrass model, `(x, y) ↦ (x, -y - a₁x - a₃)` on the affine part: the isomorphism
`projModel (negVariableChange W • W) ≅ projModel W` induced by the change of variables
`negVariableChange W`, read on `projModel W` through `negVariableChange W • W = W`. It acts on
homogeneous coordinates by `Projective.neg` (`projModelPoint_projModelNeg`). -/
noncomputable def projModelNeg : W.projModel ⟶ W.projModel :=
  eqToHom (congrArg projModel W.negVariableChange_smul_self.symm) ≫
    (W.projModelVariableChangeIso W.negVariableChange).hom

-- `projModelNeg W` is induced by any change of variables equal to `negVariableChange W`.
private theorem projModelNeg_eq {C : VariableChange R} (hC : W.negVariableChange = C)
    (h : C • W = W) :
    W.projModelNeg =
      eqToHom (congrArg projModel h.symm) ≫ (W.projModelVariableChangeIso C).hom := by
  subst hC
  rfl

/-- The negation morphism lies over the base `Spec R`. -/
@[reassoc (attr := simp)]
theorem projModelNeg_projModelOver : W.projModelNeg ≫ W.projModelOver = W.projModelOver := by
  rw [projModelNeg, Category.assoc, projModelVariableChangeIso_hom_projModelOver]
  simpa using (eqToHom_naturality projModelOver W.negVariableChange_smul_self.symm).symm

/-- The negation morphism fixes the zero section: `[0 : 1 : 0] ↦ [0 : -1 : 0] = [0 : 1 : 0]`. -/
@[reassoc (attr := simp)]
theorem projModelZero_projModelNeg : W.projModelZero ≫ W.projModelNeg = W.projModelZero := by
  have h := eqToHom_naturality (fun W' : WeierstrassCurve R ↦ W'.projModelZero)
    W.negVariableChange_smul_self.symm
  rw [eqToHom_refl, Category.id_comp] at h
  rw [projModelNeg, reassoc_of% h, projModelZero_projModelVariableChangeIso_hom]

/-- The negation morphism is an involution. -/
@[reassoc (attr := simp)]
theorem projModelNeg_projModelNeg : W.projModelNeg ≫ W.projModelNeg = 𝟙 _ := by
  -- `negVariableChange W * negVariableChange W = 1` induces the identity
  have h := congrArg Iso.hom (W.projModelVariableChangeIso_mul W.negVariableChange
    W.negVariableChange)
  have hC := eqToHom_iso_hom_naturality (fun C ↦ W.projModelVariableChangeIso C)
    W.negVariableChange_mul_self
  rw [eqToHom_refl, Category.comp_id] at hC
  simp only [hC, projModelVariableChangeIso_one, Iso.trans_hom, eqToIso.hom] at h
  rw [projModelNeg, Category.assoc, eqToHom_iso_hom_naturality_assoc
    (fun W' ↦ W'.projModelVariableChangeIso W.negVariableChange)
    W.negVariableChange_smul_self.symm, (eqToHom_comp_iff _ _ _).mp h.symm]
  simp

/-- The negation morphism is an isomorphism, being an involution. -/
instance isIso_projModelNeg : IsIso W.projModelNeg :=
  ⟨W.projModelNeg, W.projModelNeg_projModelNeg, W.projModelNeg_projModelNeg⟩

/-- The negation morphism is its own inverse. -/
@[simp]
theorem inv_projModelNeg : inv W.projModelNeg = W.projModelNeg :=
  IsIso.inv_eq_of_hom_inv_id W.projModelNeg_projModelNeg

/-- The negation morphism sends the point `projModelPoint W g hP hi` with homogeneous coordinates
`P` to the point with homogeneous coordinates `Projective.neg P = [P₀ : -P₁ - a₁P₀ - a₃P₂ : P₂]`,
the negation for the curve `W.map g`, defined through any chart `D₊(Xⱼ)` on which
`(Projective.neg P)ⱼ` is a unit. Negation fixes `P₀` and `P₂` (`Projective.neg_X`,
`Projective.neg_Z`), so for `j ≠ 1` the hypothesis `hj` says that `Pⱼ` is a unit. -/
@[reassoc]
theorem projModelPoint_projModelNeg {S : Type u} [CommRing S] {g : R →+* S} {P : Fin 3 → S}
    {hP : (W.toProjective.map g).Equation P} {i : Fin 3} (hi : IsUnit (P i)) {j : Fin 3}
    (hj : IsUnit ((W.toProjective.map g).neg P j)) :
    W.projModelPoint g hP hi ≫ W.projModelNeg =
      W.projModelPoint g (((W.toProjective.map g).equation_neg P).mpr hP) hj := by
  -- `negVariableChange W`, mapped along `g`, acts on homogeneous coordinates by `Projective.neg`
  have hQ : (W.negVariableChange.map g).toMatrix.mulVec P = (W.toProjective.map g).neg P := by
    rw [← negVariableChange_map]
    exact (W.map g).toMatrix_negVariableChange_mulVec P
  rw [projModelNeg, projModelPoint_eqToHom_assoc W.negVariableChange_smul_self.symm hi,
    projModelPoint_projModelVariableChangeIso_hom hi (hQ ▸ hj)]
  simp only [hQ]

/-- The negation morphism commutes with base change: negation on `projModel (W.map f)` followed by
the base change morphism `projModel (W.map f) ⟶ projModel W` along `f : R →+* R'` is the base change
morphism followed by negation on `projModel W`. -/
@[reassoc (attr := simp)]
theorem projModelNeg_projModelBaseChange {R' : Type u} [CommRing R'] (f : R →+* R') :
    (W.map f).projModelNeg ≫ W.projModelBaseChange f =
      W.projModelBaseChange f ≫ W.projModelNeg := by
  rw [projModelNeg_eq (W.map f) (W.negVariableChange_map f)
      (by rw [map_variableChange, negVariableChange_smul_self]),
    Category.assoc, projModelVariableChangeIso_hom_projModelBaseChange, eqToHom_trans_assoc,
    projModelNeg, eqToHom_naturality_assoc (fun W' ↦ W'.projModelBaseChange f)
      W.negVariableChange_smul_self.symm]

/-- The negation morphism commutes with the isomorphism `projModel (C • W) ≅ projModel W` induced by
a change of variables `C`: negation on `projModel (C • W)` followed by the isomorphism is the
isomorphism followed by negation on `projModel W`. -/
@[reassoc (attr := simp)]
theorem projModelNeg_projModelVariableChangeIso_hom (C : VariableChange R) :
    (C • W).projModelNeg ≫ (W.projModelVariableChangeIso C).hom =
      (W.projModelVariableChangeIso C).hom ≫ W.projModelNeg := by
  -- both are induced by `(C • W).negVariableChange * C = C * W.negVariableChange`
  have hmul : (C • W).negVariableChange * C = C * W.negVariableChange := by
    rw [negVariableChange_smul, inv_mul_cancel_right]
  have h₁ := congrArg Iso.hom (W.projModelVariableChangeIso_mul (C • W).negVariableChange C)
  have h₂ := congrArg Iso.hom (W.projModelVariableChangeIso_mul C W.negVariableChange)
  have hC := eqToHom_iso_hom_naturality (fun C ↦ W.projModelVariableChangeIso C) hmul
  rw [eqToHom_refl, Category.comp_id] at hC
  simp only [hC, h₂, Iso.trans_hom, eqToIso.hom] at h₁
  rw [projModelNeg, Category.assoc, (eqToHom_comp_iff _ _ _).mp h₁.symm, projModelNeg,
    eqToHom_iso_hom_naturality_assoc (fun W' ↦ W'.projModelVariableChangeIso C)
      W.negVariableChange_smul_self.symm]
  simp

/-- **Negation commutes with pointed isomorphisms.** An isomorphism
`e : projModel W ≅ projModel W'` of projective Weierstrass models over `Spec R`, carrying the zero
section to the zero section, carries the negation morphism of `W` to that of `W'`. -/
theorem projModelNeg_comp_hom_of_iso {W W' : WeierstrassCurve R} (e : W.projModel ≅ W'.projModel)
    (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) :
    W.projModelNeg ≫ e.hom = e.hom ≫ W'.projModelNeg := by
  -- `e` is induced by a change of variables `C` with `C • W' = W`
  obtain ⟨C, rfl, hC⟩ :=
    (existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0).exists
  rw [eqToHom_refl, Category.id_comp] at hC
  rw [hC]
  exact W'.projModelNeg_projModelVariableChangeIso_hom C

/-- **Negation commutes with pointed cartesian morphisms.** Let `F : projModel W ⟶ projModel W'` be
a morphism of projective Weierstrass models over `R` and `R'`, lying over `ψ : Spec R ⟶ Spec R'`,
such that the square formed by `F`, the structure morphisms and `ψ` is a pullback square, and
carrying the zero section to the zero section. Then `F` carries the negation morphism of `W` to
that of `W'`. -/
theorem projModelNeg_comp_of_isPullback {R R' : Type u} [CommRing R] [CommRing R']
    {W : WeierstrassCurve R} {W' : WeierstrassCurve R'} {F : W.projModel ⟶ W'.projModel}
    {ψ : Spec (.of R) ⟶ Spec (.of R')} (hF : IsPullback F W.projModelOver W'.projModelOver ψ)
    (h0 : W.projModelZero ≫ F = ψ ≫ W'.projModelZero) :
    W.projModelNeg ≫ F = F ≫ W'.projModelNeg := by
  -- `ψ` is `Spec φ`, and `F` is the composite of an isomorphism `e` over `Spec R` with the base
  -- change morphism along `φ`
  obtain ⟨φ, rfl⟩ : ∃ φ : R' →+* R, Spec.map (CommRingCat.ofHom φ) = ψ :=
    ⟨(Spec.preimage ψ).hom, by simp⟩
  have hB := W'.isPullback_projModelBaseChange φ
  let e := hF.isoIsPullback _ _ hB
  have he : e.hom ≫ (W'.map φ).projModelOver = W.projModelOver := hF.isoIsPullback_hom_snd _ _ hB
  have hF' : e.hom ≫ W'.projModelBaseChange φ = F := hF.isoIsPullback_hom_fst _ _ hB
  have h0' : W.projModelZero ≫ e.hom = (W'.map φ).projModelZero :=
    hB.hom_ext (by simp [hF', h0, projModelZero_projModelBaseChange]) (by simp [he])
  rw [← hF', reassoc_of% projModelNeg_comp_hom_of_iso e he h0', projModelNeg_projModelBaseChange,
    Category.assoc]

end WeierstrassCurve

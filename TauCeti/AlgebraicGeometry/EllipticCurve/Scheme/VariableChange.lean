/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points

/-!
# A change of variables is determined by its isomorphism of projective Weierstrass models

Let `W` be a Weierstrass curve over a commutative ring `R`. A change of variables
`C = (u, r, s, t)` induces the isomorphism
`projModelVariableChangeIso W C : projModel (C • W) ≅ projModel W`,
`[X : Y : Z] ↦ [u²X + rZ : u²sX + u³Y + tZ : Z]`, of projective Weierstrass models. This file shows
that the isomorphism determines `C`: changes of variables `C` and `C'` carrying `W` to the same
curve `W'` are equal as soon as they induce the same morphism `projModel W' ⟶ projModel W`. In
particular, among the changes of variables fixing `W`, only the identity induces the identity of
`projModel W`. No hypothesis on `W` or on `R` is needed.

This is the uniqueness part of the classification, by changes of variables, of the isomorphisms
over the base between projective Weierstrass models of elliptic curves that preserve the zero
section. The existence part, that every such isomorphism is induced by a change of variables, is
not proved here.

The two changes of variables are compared on the tautological point `[x : y : 1]` of `C • W`,
whose coordinates lie in the affine coordinate ring `R[x, y] ⧸ ((C • W)(x, y))`. The isomorphisms
induced by `C` and `C'` send it to the points `[u²x + r : u²sx + u³y + t : 1]` and
`[u'²x + r' : u'²s'x + u'³y + t' : 1]`, and `x`, `y` and `1` are linearly independent over `R`.

## Main results

* `WeierstrassCurve.projModelVariableChangeIso_hom_inj`: for `C • W = C' • W`, the isomorphisms
  induced by `C` and `C'` agree exactly when `C = C'`.
* `WeierstrassCurve.eqToHom_comp_projModelVariableChangeIso_hom_inj`: for `C • W = W'` and
  `C' • W = W'`, the morphisms `projModel W' ⟶ projModel W` induced by `C` and `C'` agree exactly
  when `C = C'`.
* `WeierstrassCurve.eqToHom_comp_projModelVariableChangeIso_hom_eq_id_iff`: for `C • W = W`, the
  endomorphism of `projModel W` induced by `C` is the identity exactly when `C = 1`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 (the change of
  variables) and III.3.1(b) (the classification over a field).
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.

## Provenance

The statement of `projModelVariableChangeIso_hom_inj` is that of AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/ComparisonInjective.lean`, declaration
`projModelVCIso_injective'`, stated here as an equivalence. The proof is not the source's. The
source transports each isomorphism to an isomorphism of affine coordinate rings
(`pointedIsoCoordEquiv`, computed for a change of variables by `bridge_coordX` and
`bridge_coordY`), and treats the zero ring separately. Here both isomorphisms are evaluated on one
point of the projective model, by `projModelPoint_projModelVariableChangeIso_hom`, with no case
distinction. What is kept from the source is the last step: the coefficients are read off the
linear independence of `x`, `y` and `1` over `R` (the source's `coordXY_ext`), and `u` and `s` are
recovered by cancelling the unit `u²`, here in
`WeierstrassCurve.VariableChange.toMatrix_injective`. The other two statements are not stated in
the source, which derives them where it uses them (`transVC_unique` and `transVC_self` in
`InvariantDifferential.lean`).
-/

public section

open CategoryTheory

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

open Matrix in
-- If the isomorphisms induced by `C` and `C'` agree, through the identification of
-- `projModel (C • W)` with `projModel (C' • W)`, then the matrices of `C` and `C'`, mapped along a
-- ring homomorphism `g : R →+* S`, take the same value at the homogeneous coordinates `P` of every
-- `S`-point of `projModel (C • W)` over `g` whose third coordinate is a unit.
private theorem toMatrix_map_mulVec_eq {C C' : VariableChange R} (h : C • W = C' • W)
    (hC : (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel h) ≫ (W.projModelVariableChangeIso C').hom) {S : Type u}
    [CommRing S] {g : R →+* S} {P : Fin 3 → S} (hP : ((C • W).toProjective.map g).Equation P)
    (hi : IsUnit (P 2)) : (C.map g).toMatrix *ᵥ P = (C'.map g).toMatrix *ᵥ P := by
  -- a change of variables fixes the third homogeneous coordinate
  have hZ (D : VariableChange R) : ((D.map g).toMatrix *ᵥ P) 2 = P 2 := by
    simp [VariableChange.toMatrix_def, mulVec, dotProduct, Fin.sum_univ_three]
  have hj (D : VariableChange R) : IsUnit (((D.map g).toMatrix *ᵥ P) 2) := by rwa [hZ D]
  -- both isomorphisms send the point with coordinates `P` to the same point of `projModel W`
  have key := projModelPoint_projModelVariableChangeIso_hom (hP := hP) hi (hj C)
  rw [hC, projModelPoint_eqToHom_assoc h hi,
    projModelPoint_projModelVariableChangeIso_hom hi (hj C'),
    projModelPoint_eq_projModelPoint_iff] at key
  obtain ⟨-, l, hl⟩ := key
  -- the two triples of coordinates are proportional, with the same unit third coordinate
  exact ((Projective.equiv_iff_eq_of_Z_eq' ((hZ C').trans (hZ C).symm)
    (hj C).mem_nonZeroDivisors).mp ⟨l, hl.symm⟩).symm

/-- A change of variables is determined by the isomorphism of projective Weierstrass models it
induces. For changes of variables `C` and `C'` with `C • W = C' • W`, the isomorphisms
`projModel (C • W) ≅ projModel W` and `projModel (C' • W) ≅ projModel W` induced by `C` and `C'`
agree, through the identification of `projModel (C • W)` with `projModel (C' • W)`, exactly when
`C = C'`. -/
@[simp]
theorem projModelVariableChangeIso_hom_inj {C C' : VariableChange R} (h : C • W = C' • W) :
    (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel h) ≫ (W.projModelVariableChangeIso C').hom ↔ C = C' := by
  refine ⟨fun hC ↦ ?_, by rintro rfl; rw [eqToHom_refl, Category.id_comp]⟩
  -- `C` and `C'` act in the same way on the tautological point `[x : y : 1]` of `C • W`, with
  -- coordinates in the affine coordinate ring
  have hM := toMatrix_map_mulVec_eq h hC (g := algebraMap R (C • W).toAffine.CoordinateRing)
    (P := ![AdjoinRoot.of _ Polynomial.X, AdjoinRoot.root _, 1])
    ((Projective.equation_some _ _).mpr (by
      simpa only [AlgHom.id_apply, Affine.baseChange, WeierstrassCurve.baseChange] using
        Affine.CoordinateRing.equation_of_algHom (AlgHom.id R (C • W).toAffine.CoordinateRing)))
    (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using isUnit_one)
  -- `x`, `y` and `1` are linearly independent over `R`, so the matrices of `C` and `C'` have the
  -- same rows
  refine VariableChange.toMatrix_injective (Matrix.ext fun i ↦
    (Affine.CoordinateRing.linearIndependent_X_root_one (C • W).toAffine).eq_coords_of_eq ?_)
  simpa only [Algebra.smul_def, Matrix.mulVec, dotProduct, VariableChange.toMatrix_map,
    Matrix.map_apply] using congrFun hM i

/-- A change of variables carrying `W` to `W'` is determined by the isomorphism
`projModel W' ≅ projModel W` it induces. For changes of variables `C` and `C'` with `C • W = W'`
and `C' • W = W'`, the isomorphisms induced by `C` and `C'`, read as morphisms
`projModel W' ⟶ projModel W` through the identifications of `projModel W'` with
`projModel (C • W)` and with `projModel (C' • W)`, agree exactly when `C = C'`. -/
@[simp]
theorem eqToHom_comp_projModelVariableChangeIso_hom_inj {W' : WeierstrassCurve R}
    {C C' : VariableChange R} (hC : C • W = W') (hC' : C' • W = W') :
    eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom =
      eqToHom (congrArg projModel hC'.symm) ≫ (W.projModelVariableChangeIso C').hom ↔ C = C' := by
  subst hC
  rw [eqToHom_refl, Category.id_comp, projModelVariableChangeIso_hom_inj hC'.symm]

/-- Among the changes of variables fixing `W`, only the identity induces the identity of the
projective Weierstrass model. For a change of variables `C` with `C • W = W`, the isomorphism
induced by `C`, read as an endomorphism of `projModel W` through the identification of
`projModel W` with `projModel (C • W)`, is the identity exactly when `C = 1`. The implication from
`C = 1` follows from `projModelVariableChangeIso_one`. -/
@[simp]
theorem eqToHom_comp_projModelVariableChangeIso_hom_eq_id_iff {C : VariableChange R}
    (h : C • W = W) :
    eqToHom (congrArg projModel h.symm) ≫ (W.projModelVariableChangeIso C).hom = 𝟙 W.projModel ↔
      C = 1 := by
  rw [← eqToHom_comp_projModelVariableChangeIso_hom_inj h (one_smul _ W),
    projModelVariableChangeIso_one, eqToIso.hom, eqToHom_trans, eqToHom_refl]

end WeierstrassCurve

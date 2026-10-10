/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Morphism
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange

/-!
# The addition morphism commutes with pointed cartesian morphisms of Weierstrass models

Let `W` and `W'` be elliptic Weierstrass curves over commutative rings `R` and `R'`. This file
shows that the Bosma–Lenstra addition morphisms `E ×_S E ⟶ E` of their projective models are
compatible with every morphism `F : projModel W ⟶ projModel W'` that carries the zero section to
the zero section and makes `projModel W` the base change of `projModel W'` along a morphism
`ψ : Spec R ⟶ Spec R'`. No hypothesis relates `W` to `W'`: the morphism `F` alone determines the
comparison.

This is what makes the addition morphism independent of the local Weierstrass equation chosen for
an elliptic curve over a scheme: two local models over the same affine open differ by a pointed
isomorphism over the base, and the restriction of a local model to a smaller affine open is a
pointed cartesian morphism.

Over the same base, a pointed isomorphism is induced by a change of variables
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), and the addition
morphism commutes with those (`WeierstrassCurve.additionMorphism_projModelVariableChangeIso_hom`).
In general, `F` factors as a pointed isomorphism `projModel W ≅ projModel (W'.map φ)` over `Spec R`,
with `Spec φ = ψ`, followed by the base change morphism `projModel (W'.map φ) ⟶ projModel W'`,
and the addition morphism commutes with base change
(`WeierstrassCurve.additionMorphism_projModelBaseChange`).

## Main results

* `WeierstrassCurve.additionMorphism_comp_hom_of_iso`: a pointed isomorphism of projective
  Weierstrass models over `Spec R` commutes with the addition morphisms.
* `WeierstrassCurve.additionMorphism_comp_of_isPullback`: a pointed cartesian morphism of
  projective Weierstrass models commutes with the addition morphisms.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1–2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

/-- **The addition morphism commutes with pointed isomorphisms.** An isomorphism
`e : projModel W ≅ projModel W'` of projective models of elliptic Weierstrass curves over `R`, over
`Spec R` and carrying the zero section to the zero section, carries the addition morphism of `W` to
that of `W'`. -/
theorem additionMorphism_comp_hom_of_iso {R : Type u} [CommRing R] {W W' : WeierstrassCurve R}
    [W.IsElliptic] [W'.IsElliptic] (e : W.projModel ≅ W'.projModel)
    (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) :
    W.additionMorphism ≫ e.hom = pullback.map _ _ _ _ e.hom e.hom (𝟙 _) (by simp [he])
      (by simp [he]) ≫ W'.additionMorphism := by
  -- `e` is induced by a change of variables `C` with `C • W' = W`
  obtain ⟨C, rfl, hC⟩ :=
    (existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0).exists
  rw [eqToHom_refl, Category.id_comp] at hC
  simp only [hC]
  exact W'.additionMorphism_projModelVariableChangeIso_hom C

/-- **The addition morphism commutes with pointed cartesian morphisms.** Let
`F : projModel W ⟶ projModel W'` be a morphism of projective models of elliptic Weierstrass curves
over `R` and `R'`, lying over `ψ : Spec R ⟶ Spec R'`, such that the square formed by `F`, the
structure morphisms and `ψ` is a pullback square, and carrying the zero section to the zero
section. Then `F` carries the addition morphism of `W` to that of `W'`. -/
theorem additionMorphism_comp_of_isPullback {R R' : Type u} [CommRing R] [CommRing R']
    {W : WeierstrassCurve R} {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic]
    {F : W.projModel ⟶ W'.projModel} {ψ : Spec (.of R) ⟶ Spec (.of R')}
    (hF : IsPullback F W.projModelOver W'.projModelOver ψ)
    (h0 : W.projModelZero ≫ F = ψ ≫ W'.projModelZero) :
    W.additionMorphism ≫ F =
      pullback.map _ _ _ _ F F ψ hF.w.symm hF.w.symm ≫ W'.additionMorphism := by
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
  conv_lhs => rw [← hF', ← Category.assoc, additionMorphism_comp_hom_of_iso e he h0',
    Category.assoc, additionMorphism_projModelBaseChange, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [hF']

end WeierstrassCurve

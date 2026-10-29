/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.VariableChange.Basic

/-!
# The `j`-invariant is an invariant of pointed projective Weierstrass models

The `j`-invariant `WeierstrassCurve.j` of an elliptic Weierstrass curve is defined from its
coefficients. This file shows that it depends only on the projective model with its zero section:
two elliptic Weierstrass curves over `R` whose projective models are isomorphic over `Spec R`,
compatibly with the zero sections, have the same `j`-invariant
(`WeierstrassCurve.j_eq_of_iso`). More generally, a morphism `projModel W ⟶ projModel W'` which
makes `projModel W` the base change of `projModel W'` along `Spec φ`, compatibly with the zero
sections, carries the `j`-invariant of `W'` to that of `W`: `φ W'.j = W.j`
(`WeierstrassCurve.j_eq_of_isPullback`).

Over the same base, a pointed isomorphism is induced by a change of variables
(`WeierstrassCurve.existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom`), and the
`j`-invariant is invariant under those (`WeierstrassCurve.variableChange_j`). A pointed base change
square factors as a pointed isomorphism over `Spec R` followed by the base change morphism
`projModel (W'.map φ) ⟶ projModel W'`, and `(W'.map φ).j = φ W'.j` (`WeierstrassCurve.map_j`).
These are the comparisons that make the `j`-invariant of an elliptic curve over a scheme, defined
from local Weierstrass equations, independent of the equations chosen.

## Main results

* `WeierstrassCurve.j_eq_of_iso`: a pointed isomorphism of projective models over `Spec R`
  preserves the `j`-invariant.
* `WeierstrassCurve.j_eq_of_isPullback`: a pointed base change square of projective models over
  `Spec φ` carries the `j`-invariant of its target to that of its source.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2 and 8.2.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

/-- **The `j`-invariant of a pointed projective model.** If the projective models of two elliptic
Weierstrass curves over `R` are isomorphic over `Spec R` by an isomorphism carrying the zero
section to the zero section, the two curves have the same `j`-invariant. -/
theorem j_eq_of_iso {R : Type u} [CommRing R] {W W' : WeierstrassCurve R} [W.IsElliptic]
    [W'.IsElliptic] (e : W.projModel ≅ W'.projModel)
    (he : e.hom ≫ W'.projModelOver = W.projModelOver)
    (h0 : W.projModelZero ≫ e.hom = W'.projModelZero) : W.j = W'.j := by
  -- `e` is induced by a change of variables `C` with `C • W' = W`
  obtain ⟨C, rfl, -⟩ := (existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0).exists
  exact variableChange_j W' C

/-- **The `j`-invariant along a pointed base change square.** Let `F : projModel W ⟶ projModel W'`
be a morphism of projective models of elliptic Weierstrass curves over `R` and `R'`, lying over
`Spec φ` for a ring homomorphism `φ : R' →+* R`, such that the square formed by `F`, the structure
morphisms and `Spec φ` is a pullback square, and carrying the zero section to the zero section.
Then `φ` carries the `j`-invariant of `W'` to that of `W`. -/
theorem j_eq_of_isPullback {R R' : Type u} [CommRing R] [CommRing R'] {W : WeierstrassCurve R}
    {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic] {F : W.projModel ⟶ W'.projModel}
    {φ : R' →+* R}
    (hF : IsPullback F W.projModelOver W'.projModelOver (Spec.map (CommRingCat.ofHom φ)))
    (h0 : W.projModelZero ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ W'.projModelZero) :
    φ W'.j = W.j := by
  -- `F` is the composite of a pointed isomorphism `e` over `Spec R` with the base change morphism
  -- along `φ`
  have hB := W'.isPullback_projModelBaseChange φ
  let e := hF.isoIsPullback _ _ hB
  have he : e.hom ≫ (W'.map φ).projModelOver = W.projModelOver := hF.isoIsPullback_hom_snd _ _ hB
  have hF' : e.hom ≫ W'.projModelBaseChange φ = F := hF.isoIsPullback_hom_fst _ _ hB
  have h0' : W.projModelZero ≫ e.hom = (W'.map φ).projModelZero :=
    hB.hom_ext (by simp [hF', h0, projModelZero_projModelBaseChange]) (by simp [he])
  rw [← map_j, j_eq_of_iso e he h0']

end WeierstrassCurve

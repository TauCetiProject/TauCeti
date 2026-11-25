/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.CategoryTheory.Sites.QuotientSheaf

/-!
# The quotient sheaf of a pre-relation of schemes

Let `s t : R ⟶ U` be a pair of morphisms of schemes, a *pre-relation* on `U`: a point `r` of `R`
relates `t r` to `s r`. The *quotient sheaf* `U/R` is the fppf sheafification of the presheaf
coequaliser `T ↦ U(T)/R(T)` (Stacks, Definition 39.20.1 (02VG)). It is the instance
`J := Scheme.fppfTopology` of the quotient sheaf `TauCeti.CategoryTheory.quotientSheaf J s t` of a
pre-relation on a subcanonical site, whose API applies to it directly: the projection
`quotientSheaf.π : h_U ⟶ U/R` is the coequaliser of `h_R ⇉ h_U` in fppf sheaves
(`TauCeti.CategoryTheory.quotientSheaf.isColimit`), is fppf locally surjective
(`TauCeti.CategoryTheory.quotientSheaf.isLocallySurjective_π`), and has kernel pair `h_R ⇉ h_U`
when `(t, s)` is an equivalence relation (`TauCeti.CategoryTheory.quotientSheaf.kernelPair`;
Stacks, Lemma 39.20.4 (045Y), together with the injectivity of `R ⟶ U × U`).

Mathlib's type-valued sheafification for the big fppf site of `Scheme.{u}` produces sheaves of
`Type (u + 1)`, since the site is a large category. The quotient sheaf is therefore a sheaf of
`Type (u + 1)`, and the representable sheaves are the universe-lifted ones
`Scheme.fppfTopology.uliftYoneda`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.quotientSheaf s t`: the fppf sheafification `U/R` of the
  presheaf quotient.

## References

* [Stacks Project, Definition 39.20.1](https://stacks.math.columbia.edu/tag/02VG)
* [Stacks Project, Lemma 39.20.4](https://stacks.math.columbia.edu/tag/045Y)
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {R U : Scheme.{u}} (s t : R ⟶ U)

/-- The quotient sheaf `U/R` of a pre-relation `s t : R ⟶ U` of schemes: the fppf sheafification
of the presheaf quotient `T ↦ U(T)/R(T)` (Stacks, Definition 39.20.1 (02VG)), the instance
`J := Scheme.fppfTopology` of `TauCeti.CategoryTheory.quotientSheaf`. It is a sheaf of
`Type (u + 1)`, where Mathlib's sheafification for the big fppf site lands. -/
noncomputable abbrev quotientSheaf : Sheaf Scheme.fppfTopology.{u} (Type (u + 1)) :=
  TauCeti.CategoryTheory.quotientSheaf.{u + 1} Scheme.fppfTopology s t

end TauCeti.AlgebraicGeometry.Spaces

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Isogeny
public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Adjoint
import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central

/-!
# Isogenies identify adjoint forms

An isogeny between semisimple affine groups in characteristic zero induces a canonical
isomorphism between their represented center quotients. Thus the adjoint form is independent
of the representative in an isogeny class. The comparison commutes with the quotient
projections, is uniquely determined by that equation, and respects identity and composition.

For the coordinate arrow `f : H ⟶ K`, compose `f` with the center-quotient inclusion of `H`.
The composite is an isogeny, hence central in characteristic zero. Since the center quotient
of `H` is adjoint, the existing central-isogeny comparison gives the isomorphism.
No centrality hypothesis on the given isogeny or splitting hypothesis on the groups is needed.

The construction follows the represented-quotient comparison in
`Semisimple.Center.Isogeny`, using the centrality theorem from `Isogeny.Central`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, adjoint groups and isogenies.
* T. A. Springer, *Linear Algebraic Groups*, §9.6.
-/

public section

open CategoryTheory

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H K L : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- An isogeny of semisimple affine groups in characteristic zero canonically identifies
their represented center quotients, which are their adjoint forms. -/
noncomputable def centerQuotientIsoOfIsIsogeny
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (f : H.obj ⟶ K.obj) (hf : CommHopfAlgCat.IsIsogeny f) :
    hH.reductive.centerQuotient.obj ≅ hK.reductive.centerQuotient.obj := by
  exact hK.centerQuotientIsoOfIsCentralIsogeny (hH.reductive.centerQuotientι ≫ f)
    ((hH.isCentralIsogeny_centerQuotientι.isIsogeny.comp hf).isCentralIsogeny_of_charZero
      hK.geometricallyConnected)
    ((adjointSemisimpleCommHopfAlgProperty_iff _).mp hH.adjointSemisimple_centerQuotient)

/-- The comparison between adjoint forms intertwines the isogeny and the quotient
projections. This equation characterizes its forward coordinate morphism. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsIsogeny_hom_comp
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (f : H.obj ⟶ K.obj) (hf : CommHopfAlgCat.IsIsogeny f) :
    (hH.centerQuotientIsoOfIsIsogeny hK f hf).hom ≫ hK.reductive.centerQuotientι =
      hH.reductive.centerQuotientι ≫ f := by
  simp [centerQuotientIsoOfIsIsogeny]

/-- The inverse comparison also intertwines the quotient projections and the isogeny. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsIsogeny_inv_comp
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (f : H.obj ⟶ K.obj) (hf : CommHopfAlgCat.IsIsogeny f) :
    (hH.centerQuotientIsoOfIsIsogeny hK f hf).inv ≫ hH.reductive.centerQuotientι ≫ f =
      hK.reductive.centerQuotientι := by
  rw [← hH.centerQuotientIsoOfIsIsogeny_hom_comp hK f hf,
    Iso.inv_hom_id_assoc]

/-- The adjoint-form comparison is uniquely determined by its compatibility with the
quotient projections. -/
theorem centerQuotientIsoOfIsIsogeny_hom_unique
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (f : H.obj ⟶ K.obj) (hf : CommHopfAlgCat.IsIsogeny f)
    (g : hH.reductive.centerQuotient.obj ⟶ hK.reductive.centerQuotient.obj)
    (hg : g ≫ hK.reductive.centerQuotientι = hH.reductive.centerQuotientι ≫ f) :
    g = (hH.centerQuotientIsoOfIsIsogeny hK f hf).hom := by
  apply hK.centerQuotientIsoOfIsCentralIsogeny_hom_unique
  exact hg

/-- The identity isogeny induces the identity comparison of adjoint forms. -/
@[simp]
theorem centerQuotientIsoOfIsIsogeny_id
    (hH : semisimpleCommHopfAlgProperty k H) :
    hH.centerQuotientIsoOfIsIsogeny hH (𝟙 H.obj) (CommHopfAlgCat.isIsogeny_id H.obj) =
      Iso.refl hH.reductive.centerQuotient.obj := by
  apply Iso.ext
  symm
  apply hH.centerQuotientIsoOfIsIsogeny_hom_unique
  simp

/-- Composing the comparisons of adjoint forms gives the comparison for the composite
isogeny. -/
@[simp]
theorem centerQuotientIsoOfIsIsogeny_trans
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (hL : semisimpleCommHopfAlgProperty k L)
    (f : H.obj ⟶ K.obj) (g : K.obj ⟶ L.obj)
    (hf : CommHopfAlgCat.IsIsogeny f) (hg : CommHopfAlgCat.IsIsogeny g) :
    (hH.centerQuotientIsoOfIsIsogeny hK f hf).trans
        (hK.centerQuotientIsoOfIsIsogeny hL g hg) =
      hH.centerQuotientIsoOfIsIsogeny hL (f ≫ g) (hf.comp hg) := by
  apply Iso.ext
  apply hH.centerQuotientIsoOfIsIsogeny_hom_unique
  simp

/-- Composing the forward coordinate morphisms gives the comparison for the composite
isogeny. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsIsogeny_hom_comp_hom
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (hL : semisimpleCommHopfAlgProperty k L)
    (f : H.obj ⟶ K.obj) (g : K.obj ⟶ L.obj)
    (hf : CommHopfAlgCat.IsIsogeny f) (hg : CommHopfAlgCat.IsIsogeny g) :
    (hH.centerQuotientIsoOfIsIsogeny hK f hf).hom ≫
        (hK.centerQuotientIsoOfIsIsogeny hL g hg).hom =
      (hH.centerQuotientIsoOfIsIsogeny hL (f ≫ g) (hf.comp hg)).hom :=
  congrArg Iso.hom (hH.centerQuotientIsoOfIsIsogeny_trans hK hL f g hf hg)

/-- Composing the inverse coordinate morphisms gives the inverse comparison for the
composite isogeny. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsIsogeny_inv_comp_inv
    (hH : semisimpleCommHopfAlgProperty k H)
    (hK : semisimpleCommHopfAlgProperty k K)
    (hL : semisimpleCommHopfAlgProperty k L)
    (f : H.obj ⟶ K.obj) (g : K.obj ⟶ L.obj)
    (hf : CommHopfAlgCat.IsIsogeny f) (hg : CommHopfAlgCat.IsIsogeny g) :
    (hK.centerQuotientIsoOfIsIsogeny hL g hg).inv ≫
        (hH.centerQuotientIsoOfIsIsogeny hK f hf).inv =
      (hH.centerQuotientIsoOfIsIsogeny hL (f ≫ g) (hf.comp hg)).inv :=
  congrArg Iso.inv (hH.centerQuotientIsoOfIsIsogeny_trans hK hL f g hf hg)

end TauCeti.semisimpleCommHopfAlgProperty

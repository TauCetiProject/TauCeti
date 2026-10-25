/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.RepresentableQuotient
public import TauCeti.Algebra.AlgebraicGroup.Center.Functoriality

/-!
# Recognizing adjoint quotients by central isogenies

A central isogeny from a semisimple affine group to a group with trivial
scheme-theoretic center identifies the target canonically with the represented quotient of
the source by its full center. The comparison commutes with the quotient projection and is
unique with that property.

All results hold over any field, including when the central kernel is nonreduced. The target
need not be assumed semisimple: faithful flatness and triviality of its center suffice.
The kernel calculation is `kernelHopfIdeal_eq_centerDefiningIdeal_of_injective`; coordinate
exactness is `coinvariants_kernelHopfIdeal_eq_range`. The represented quotient and its
factorization are those of `Reductive.CenterQuotient`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21, adjoint groups and central isogenies.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {G : FiniteTypeCommHopfAlgCat.{u, u} k}
  (hG : semisimpleCommHopfAlgProperty k G)
  {H : _root_.CommHopfAlgCat.{u} k}

/-- The target of a central isogeny from a semisimple group to a centerless group is
canonically isomorphic to its represented center quotient. The coordinate arrow goes from
the target's coordinate algebra to the quotient's coordinate algebra. -/
noncomputable def centerQuotientIsoOfIsCentralIsogeny (f : H ⟶ G.obj)
    (hf : CommHopfAlgCat.IsCentralIsogeny f)
    (hH : CommHopfAlgCat.centerDefiningIdeal H = HopfIdeal.augmentation k H) :
    H ≅ hG.reductive.centerQuotient.obj := by
  let _ := hG.reductive.isIso_liftCenterQuotient_of_faithfullyFlat f hf.faithfullyFlat
    (CommHopfAlgCat.kernelHopfIdeal_eq_centerDefiningIdeal_of_injective f hf.injective
      hf.isCentral_kernelHopfIdeal hH)
  exact asIso (hG.reductive.liftCenterQuotient f
    (CommHopfAlgCat.kernelHopfIdeal_eq_centerDefiningIdeal_of_injective f hf.injective
      hf.isCentral_kernelHopfIdeal hH).le)

/-- The canonical comparison recovers the given central isogeny after the center-quotient
projection. This equation characterizes it uniquely. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsCentralIsogeny_hom_comp (f : H ⟶ G.obj)
    (hf : CommHopfAlgCat.IsCentralIsogeny f)
    (hH : CommHopfAlgCat.centerDefiningIdeal H = HopfIdeal.augmentation k H) :
    (hG.centerQuotientIsoOfIsCentralIsogeny f hf hH).hom ≫ hG.reductive.centerQuotientι = f := by
  simp [centerQuotientIsoOfIsCentralIsogeny]

/-- The inverse comparison intertwines the center quotient with the given isogeny. -/
@[reassoc (attr := simp)]
theorem centerQuotientIsoOfIsCentralIsogeny_inv_comp (f : H ⟶ G.obj)
    (hf : CommHopfAlgCat.IsCentralIsogeny f)
    (hH : CommHopfAlgCat.centerDefiningIdeal H = HopfIdeal.augmentation k H) :
    (hG.centerQuotientIsoOfIsCentralIsogeny f hf hH).inv ≫ f = hG.reductive.centerQuotientι :=
  (hG.centerQuotientIsoOfIsCentralIsogeny f hf hH).inv_comp_eq.mpr
    (hG.centerQuotientIsoOfIsCentralIsogeny_hom_comp f hf hH).symm

/-- The comparison with the represented center quotient is the unique coordinate morphism
compatible with the two quotient projections. -/
theorem centerQuotientIsoOfIsCentralIsogeny_hom_unique (f : H ⟶ G.obj)
    (hf : CommHopfAlgCat.IsCentralIsogeny f)
    (hH : CommHopfAlgCat.centerDefiningIdeal H = HopfIdeal.augmentation k H)
    (g : H ⟶ hG.reductive.centerQuotient.obj) (hg : g ≫ hG.reductive.centerQuotientι = f) :
    g = (hG.centerQuotientIsoOfIsCentralIsogeny f hf hH).hom := by
  simpa only [centerQuotientIsoOfIsCentralIsogeny, asIso_hom] using
    hG.reductive.liftCenterQuotient_unique f
      (CommHopfAlgCat.kernelHopfIdeal_eq_centerDefiningIdeal_of_injective f hf.injective
        hf.isCentral_kernelHopfIdeal hH).le g hg

end TauCeti.semisimpleCommHopfAlgProperty

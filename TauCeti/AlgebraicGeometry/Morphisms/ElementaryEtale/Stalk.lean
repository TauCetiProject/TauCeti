/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.ElementaryEtale.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Pointwise
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Stalk

/-!
# Finite local models of quasi-finite points

A quasi-finite point of a morphism locally of finite presentation admits an étale
change of source and target for which the horizontal morphism and its map on the
chosen stalks are both finite. Étaleness at the original point is equivalent to
étaleness at the new point. Thus the new stalk map is a finite local homomorphism
to which local algebra can be applied, without changing the étaleness problem.

Finiteness of the morphism alone would not suffice: localization of a finite
algebra at a prime need not remain finite over the local base. The elementary
étale construction gives a singleton fibre, which is precisely the extra input
to `Scheme.Hom.finite_stalkMap_of_unique_preimage`.

Normality, regularity, dimension, and codimension-one unramifiedness can be
transported separately using the étale stalk and étale square APIs. None is
assumed for the construction of the finite local model itself.

## References

* Stacks Project, Lemma 37.41.1 (02LK), elementary étale localization.
* Stacks Project, proof of Lemma 58.21.4 (0BMB), reduction to a finite local homomorphism.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A quasi-finite point has an étale-local model with a finite map on stalks.
The horizontal map in the model is finite as well, and it is étale at the chosen
point exactly when the original morphism is étale at the original point.

Unlike the stalk map of an arbitrary finite morphism, the new stalk map is finite:
the elementary étale neighbourhood isolates the chosen point in its fibre. -/
theorem exists_etale_square_finite_stalkMap (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {x : X} (hx : f.QuasiFiniteAt x) :
    ∃ (X' Y' : Scheme.{u}) (e : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y') (x' : X'),
      Etale e ∧ Etale b ∧ e x' = x ∧ e ≫ f = f' ≫ b ∧
        IsFinite f' ∧ (f'.stalkMap x').hom.Finite ∧
        ((∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f)) ↔
          ∃ U' : X'.Opens, x' ∈ U' ∧ Etale (U'.ι ≫ f')) := by
  obtain ⟨Y', b, y', hb, _, _, V, v, hfin, hvx, hvy, _, huniq⟩ :=
    f.exists_elementaryEtale_finite_of_isolated hx
  let e : V.toScheme ⟶ X := V.ι ≫ pullback.fst f b
  let f' : V.toScheme ⟶ Y' := V.ι ≫ pullback.snd f b
  have he : Etale e := inferInstance
  have hw : e ≫ f = f' ≫ b := by
    simp only [e, f', Category.assoc, pullback.condition]
  have hstalk : (f'.stalkMap v).hom.Finite := by
    apply f'.finite_stalkMap_of_unique_preimage v
    intro z hz
    exact huniq z (hz.trans hvy)
  refine ⟨V.toScheme, Y', e, b, f', v, he, hb, hvx, hw, hfin, hstalk, ?_⟩
  rw [← hvx]
  exact exists_etale_iff_of_etale_square f f' e b hw v

end AlgebraicGeometry.Scheme.Hom

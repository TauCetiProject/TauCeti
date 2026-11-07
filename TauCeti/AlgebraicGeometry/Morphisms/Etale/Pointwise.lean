/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Étaleness at a point under étale changes of source and target

In a commutative square whose vertical maps are étale, étaleness of the horizontal
maps at corresponding points is equivalent. The square need not be cartesian and
neither vertical map need be surjective. The bottom horizontal map is assumed locally
of finite presentation, as required for descent from its stalk to a neighbourhood.

This permits replacing a quasi-finite point by a finite local model when proving
purity of the branch locus. The descent direction uses
`Scheme.Hom.exists_etale_of_etale_comp`, while the ascent direction restricts the
square to an étale neighbourhood and cancels the unramified target map.

## References

* Stacks Project, Lemma 58.21.4 (0BMB), reduction by étale neighbourhoods.
* Stacks Project, Lemma 35.31.1 (036W), étale locality on the source.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}}

/-- In a commutative square with étale vertical maps, the horizontal maps are étale
at corresponding points simultaneously. No cartesian or surjectivity hypothesis is needed. -/
theorem exists_etale_iff_of_etale_square
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X' ⟶ X) (b : Y' ⟶ Y)
    [LocallyOfFinitePresentation f] [Etale e] [Etale b]
    (w : e ≫ f = f' ≫ b) (x' : X') :
    (∃ U : X.Opens, e x' ∈ U ∧ Etale (U.ι ≫ f)) ↔
      (∃ U' : X'.Opens, x' ∈ U' ∧ Etale (U'.ι ≫ f')) := by
  constructor
  · rintro ⟨U, hxU, _⟩
    refine ⟨e ⁻¹ᵁ U, hxU, ?_⟩
    have hcomp : ((e ⁻¹ᵁ U).ι ≫ f') ≫ b = (e ∣_ U) ≫ U.ι ≫ f := by
      rw [Category.assoc, ← w, morphismRestrict_ι_assoc]
    have : Etale (((e ⁻¹ᵁ U).ι ≫ f') ≫ b) := by
      rw [hcomp]
      infer_instance
    exact Etale.of_comp _ b
  · rintro ⟨U', hxU', _⟩
    have hcomp : (U'.ι ≫ e) ≫ f = (U'.ι ≫ f') ≫ b := by
      simp only [Category.assoc, w]
    have : Etale ((U'.ι ≫ e) ≫ f) := by
      rw [hcomp]
      infer_instance
    exact exists_etale_of_etale_comp (U'.ι ≫ e) f ⟨x', hxU'⟩
      (Flat.stalkMap _ _)

end AlgebraicGeometry.Scheme.Hom

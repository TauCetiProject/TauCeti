/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Stalk
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Codimension-one unramifiedness under étale localization

Consider a commutative square with horizontal maps `f' : X' ⟶ Y'` and `f : X ⟶ Y`,
source map `e : X' ⟶ X` étale, and target map `b : Y' ⟶ Y` formally unramified.
If `f` is locally of finite type, then `f'` is unramified at `x'` exactly when `f` is
unramified at `e x'`. If `X` is locally Noetherian, the same equivalence holds for
unramifiedness at every codimension-one generization of these points.

In particular, the codimension-one hypothesis in purity of the branch locus is unchanged
by étale base change, even after restricting the base change to an open neighbourhood of
the chosen point. No purity theorem or normality hypothesis is needed for this transport.

The argument uses descent of formal unramifiedness along flat local homomorphisms,
preservation of local dimension under étale morphisms, and lifting of generizations along
flat morphisms.

## References

* Stacks Project, Lemma 58.21.4 (0BMB), the reduction by elementary étale neighbourhoods.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y X' Y' : Scheme.{u}}

/-- Unramifiedness at every codimension-one generization of a point is invariant under an
étale change of the source in a commutative square whose target map is formally unramified.
This applies to open parts of étale base changes, not just to the whole fibre product. -/
theorem formallyUnramified_stalk_codimOne_iff_of_etale_square
    (f : X ⟶ Y) (f' : X' ⟶ Y') (e : X' ⟶ X) (b : Y' ⟶ Y)
    [LocallyOfFiniteType f] [Etale e] [FormallyUnramified b] [IsLocallyNoetherian X]
    (w : e ≫ f = f' ≫ b) (x' : X') :
    (∀ x : X, x ⤳ e x' → ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified) ↔
    (∀ z : X', z ⤳ x' → ringKrullDim (X'.presheaf.stalk z) = 1 →
      (f'.stalkMap z).hom.FormallyUnramified) := by
  constructor
  · intro h z hz hdim
    apply (formallyUnramified_stalkMap_iff_of_flat_square f f' e b w z).mpr
    apply h (e z) (hz.map e.continuous)
    rwa [e.ringKrullDim_stalk_eq_of_etale z]
  · intro h x hx hdim
    -- Lift the generization through the chosen point, rather than merely through the cover.
    obtain ⟨z, hz, rfl⟩ := Flat.generalizingMap e hx
    apply (formallyUnramified_stalkMap_iff_of_flat_square f f' e b w z).mp
    apply h z hz
    rwa [← e.ringKrullDim_stalk_eq_of_etale z]

/-- The codimension-one unramifiedness hypothesis at a point is unchanged by étale base
change, with no surjectivity assumption on the base morphism. -/
theorem formallyUnramified_stalk_codimOne_iff_etale_baseChange
    (f : X ⟶ Y) (b : Y' ⟶ Y) [LocallyOfFiniteType f] [Etale b]
    [IsLocallyNoetherian X] (z : (pullback f b : Scheme.{u})) :
    (∀ x : X, x ⤳ pullback.fst f b z → ringKrullDim (X.presheaf.stalk x) = 1 →
      (f.stalkMap x).hom.FormallyUnramified) ↔
    (∀ x : (pullback f b : Scheme.{u}), x ⤳ z → ringKrullDim ((pullback f b).presheaf.stalk x) = 1 →
      ((pullback.snd f b).stalkMap x).hom.FormallyUnramified) :=
  formallyUnramified_stalk_codimOne_iff_of_etale_square f (pullback.snd f b)
    (pullback.fst f b) b pullback.condition z

end AlgebraicGeometry.Scheme.Hom

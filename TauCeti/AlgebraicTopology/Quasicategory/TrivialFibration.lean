/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalEquivalence
public import TauCeti.AlgebraicTopology.Quasicategory.CategoricalFibration
public import TauCeti.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import TauCeti.AlgebraicTopology.SimplicialSet.TrivialFibration

/-!
# Trivial fibrations of quasicategories

A trivial fibration of simplicial sets is a map `p : X ⟶ Y` with the right lifting property with
respect to every monomorphism, `(monomorphisms SSet).rlp p`. This file compares trivial
fibrations with the categorical notions of maps of quasicategories: categorical fibrations,
essential surjectivity and categorical equivalences.

A trivial fibration is a categorical fibration (`SSet.CategoricalFibration.of_rlp_monomorphisms`):
it lifts inner horns, and through every vertex `x₀` of `X` it has a section `s`, obtained by
lifting the identity of `Y` against the inclusion of the vertex `p x₀`.
The section carries the equivalences out of `p x₀` to equivalences out of `x₀` lifting them.

**A trivial fibration between quasicategories is a categorical equivalence**
(`SSet.QCat.IsCategoricalEquivalence.of_rlp_monomorphisms`). A section `s` of `p` is a
quasi-inverse: `s ≫ p` is the identity of `Y`, and the identity of `X` and `p ≫ s` agree after
composing with `p`, so they are joined by a homotopy `X ⊗ Δ[1] ⟶ X` over `Y`. This homotopy is an
edge of the functor quasicategory `Fun(X, X)`. Its component at a vertex `x` lies over the
degenerate edge at `p x`, and a trivial fibration is a right fibration, which reflects
equivalences, so every component is an equivalence. Since equivalences of functors are detected
pointwise (`SSet.Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt`), the homotopy is an
equivalence of `Fun(X, X)`, which gives the invertible `2`-morphism from `𝟙 X` to `p ≫ s` in the
bicategory of quasicategories.

Conversely, the characterization of categorical equivalences as the fully faithful and
essentially surjective maps rests on the fact that a categorical fibration between quasicategories
that is fully faithful and essentially surjective is a trivial fibration. Its first step, lifting
vertices, holds for every essentially surjective categorical fibration to a quasicategory
(`SSet.CategoricalFibration.surjective_app_zero_of_essSurj`, in
`TauCeti.AlgebraicTopology.Quasicategory.CategoricalFibration`). Lifting the boundaries of the
higher simplices uses that the maps of right mapping spaces are weak equivalences, and is not
proved here.

## Main results

* `SSet.QCat.IsCategoricalEquivalence.of_rlp_monomorphisms`: a trivial fibration between
  quasicategories is a categorical equivalence.

## References

* J. Lurie, *Kerodon*, §4.5 (equivalences of ∞-categories) and §4.6.2 (fully faithful and
  essentially surjective functors).
* J. Lurie, *Higher Topos Theory*, §1.2.10 and §2.4.6.
-/

public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed Limits
  MorphismProperty Opposite Simplicial

namespace SSet

namespace QCat

variable {X Y : QCat.{u}}

/-- **A trivial fibration between quasicategories is a categorical equivalence.** -/
theorem IsCategoricalEquivalence.of_rlp_monomorphisms {p : X ⟶ Y}
    (hp : (monomorphisms SSet.{u}).rlp p.hom) : IsCategoricalEquivalence p := by
  -- A section `s` of `p` is a quasi-inverse: `s ≫ p` is the identity, and a homotopy over `Y` from
  -- the identity of `X` to `p ≫ s` is an equivalence of `Fun(X, X)`, since its components lie over
  -- identities.
  have := X.property
  have := (rlp_monomorphisms_iff.1 hp).1
  have := isSplitEpi_of_rlp_monomorphisms hp
  have hs : section_ p.hom ≫ p.hom = 𝟙 _ := IsSplitEpi.id p.hom
  let s : Y ⟶ X := ObjectProperty.homMk (section_ p.hom)
  obtain ⟨H, hH⟩ := exists_homotopy_of_rlp_monomorphisms hp (𝟙 X.obj) (p.hom ≫ section_ p.hom)
    (by simp [hs])
  -- The component of `H` at `x` lies over the degenerate edge at `p x`, so it is an equivalence.
  have hα : ((ihomEdgeEquiv _ _).symm H).IsEquivalence := by
    refine (Edge.isEquivalence_iff_forall_isEquivalence_map_evalAt _).2 fun x ↦ ?_
    rw [← Edge.isEquivalence_map_iff_of_rightFibration p.hom]
    refine (Edge.isEquivalence_iff_of_edge_eq ?_).1 (Edge.isEquivalence_id (p.hom.app _ x))
    rw [Edge.id_edge, σ_zero_eq_yonedaEquiv_const]
    simp [← yonedaEquiv_comp, hH]
  -- The identities and composites of `1`-morphisms in the bicategory of quasicategories are those
  -- of the full subcategory `QCat` of `SSet` only up to unfolding, so `simp` does not see them:
  -- the maps underlying `𝟙 X` and `p ≫ s` are `𝟙 X.obj` and `p.hom ≫ section_ p.hom` by `rfl`.
  obtain ⟨η⟩ := nonempty_iso_of_isEquivalence (f := 𝟙 X) (g := p ≫ s)
    ((Edge.isEquivalence_ofEq_iff (e := (ihomEdgeEquiv _ _).symm H) rfl rfl).2 hα)
  have hε : s ≫ p = 𝟙 Y := by
    -- As above, the map underlying `s ≫ p` is `section_ p.hom ≫ p.hom` by definition.
    ext : 1
    exact hs
  exact (isCategoricalEquivalence_iff_exists_equivalence p).2
    ⟨.mkOfAdjointifyCounit η (eqToIso hε), rfl⟩

end QCat

end SSet

/-
Copyright (c) 2026 Tau Ceti contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic

/-!
# Restriction in positive Tate degrees

`TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.Basic` supplies restriction in
degree `0`, in degree `-1`, and in every degree at most `-2`. This file supplies the positive
degrees, so that a restriction map

```text
tateCohomology M r ⟶ tateCohomology (Rep.res H.subtype M) r
```

is now available in every integer degree `r`.

In degrees `≥ 1` the Tate complex is the complex of inhomogeneous cochains, so restriction is the
ordinary restriction of group cohomology, transported through Mathlib's comparison
`TateCohomology.isoGroupCohomology`. On a cochain this is the formula already used by
`TauCeti.groupCohomology.map`: a cochain on `H` is pulled back to a cochain on `G` by
`g ↦ f ∘ g` and composed with the identity on the restricted coefficient module.

## Main definitions

* `TauCeti.TateCohomology.posRes`: restriction in Tate degree `n + 1`, for `n : ℕ`.

## Main results

* `TauCeti.TateCohomology.posRes_comp_isoGroupCohomology_hom`: positive-degree Tate restriction is
  the ordinary cohomological restriction `TauCeti.groupCohomology.map` along `H.subtype`, read
  through Mathlib's comparison `TateCohomology.isoGroupCohomology`.

## Remaining work

Restriction in positive degrees is not yet shown transitive along a tower of subgroups, nor
compatible with a group isomorphism carrying the subgroup onto its image. Both are the two
properties restriction has in every other degree
(`TauCeti.TateCohomology.negSuccRes_trans`, `TauCeti.TateCohomology.map_comp_negSuccRes`), and
Tate's theorem needs them in order to be applied to a fundamental class restricted to a subgroup.
The obstacle is the same one that appears in the negative degrees: `Rep.res` in Mathlib does not
compose, so the composite of two restrictions is only related to the single restriction from `G`
to `K` through the comparison morphism `TauCeti.Subgroup.congrOfMapEq` of the restricted
isomorphism, and the two presentations of the restricted coefficient module must be matched with
`TauCeti.Rep.isIntertwiningMap_res_res`.

## References

* E. Artin and J. Tate, *Class Field Theory*, Chapter IV, §6 and Chapter XIV, §4.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory Rep Representation

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep.{u} R G)
  (H : Subgroup G)

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- **Restriction to a subgroup in Tate degree `n + 1`, for `n : ℕ`.** In positive degrees the
Tate complex is the complex of inhomogeneous cochains, so this is the ordinary restriction of
group cohomology `TauCeti.groupCohomology.map` along `H.subtype`, transported through Mathlib's
comparison `TateCohomology.isoGroupCohomology`. -/
def posRes (n : ℕ) :
    tateCohomology M ((n + 1 : ℕ)) ⟶ tateCohomology (Rep.res H.subtype M) ((n + 1 : ℕ)) :=
  (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app M ≫
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1) ≫
    (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).inv.app
      (Rep.res H.subtype M)

/-- **In positive degrees Tate restriction is the ordinary cohomological restriction** along
`H.subtype`, read through Mathlib's comparison `TateCohomology.isoGroupCohomology`. -/
@[reassoc]
theorem posRes_comp_isoGroupCohomology_hom (n : ℕ) :
    posRes M H n ≫
        (_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).hom.app
          (Rep.res H.subtype M) =
      (_root_.TateCohomology.isoGroupCohomology (G := G) (n + 1)).hom.app M ≫
        groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1) := by
  -- The comparison maps are components of natural isomorphisms between semireducible functors,
  -- so the goal cannot be rewritten: `groupCohomology.map` lands in `groupCohomology`, while the
  -- components of `isoGroupCohomology` land in the objects of `groupCohomology.functor`, and the
  -- two agree only by unfolding that semireducible `def`. The goal is closed instead by cancelling
  -- the comparison isomorphism against its own inverse, as in
  -- `TauCeti.TateCohomology.negSuccRes_comp_negSuccIso_hom`.
  simp only [posRes]
  exact (Iso.eq_comp_inv ((_root_.TateCohomology.isoGroupCohomology (G := H) (n + 1)).app
    (Rep.res H.subtype M))).1 (by rfl)

end TauCeti.TateCohomology

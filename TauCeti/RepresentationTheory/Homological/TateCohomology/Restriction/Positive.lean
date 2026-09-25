/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prime Agent
-/
module

public import TauCeti.Algebra.Group.Subgroup.Map
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
* `TauCeti.TateCohomology.posRes_trans`: positive-degree Tate restriction is transitive along a
  tower of subgroups, the counterpart of `TauCeti.TateCohomology.negSuccRes_trans`.

## Remaining work

Restriction in positive degrees is not yet shown compatible with a group isomorphism carrying the
subgroup onto its image, the positive-degree counterpart of
`TauCeti.TateCohomology.map_comp_negSuccRes`, nor natural in the coefficient module. Corestriction
in positive degrees is also still missing, and the roadmap's
`cor ∘ res = [G:H]` needs it.

The tower case required one structural observation that is worth recording, because it is not
obvious from the statement of the theorem. Mathlib's `Rep.res` does **not** compose: for
`K ≤ H ≤ G` the composite `Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M)` is not
definitionally `Rep.res K.subtype M`, and the two have different carrier types (`↥(K.subgroupOf H)`
versus `↥K`), so that equality cannot even be stated as an equation of `Rep`s. The composite is
therefore related to the single restriction only through the map along
`Subgroup.subgroupOfEquivOfLe hKH` built from `TauCeti.Subgroup.subtype_comp_subgroupOfEquivOfLe`
and `TauCeti.Rep.isIntertwiningMap_res_res`, which is why the statement of `posRes_trans` carries
that middle term. Cancelling the three comparison isomorphisms in one pass is not possible: the
helper `posRes_cancel_comparison` exists because the comparison isomorphisms must be typed with
`TauCeti.groupCohomology` rather than with `(TauCeti.groupCohomology.functor _ _ _).obj _`, the two
not being definitionally equal at `.instances` transparency.

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

omit [Fintype G] in
@[reassoc]
private theorem map_subgroupOf_trans {K H : Subgroup G} (hKH : K ≤ H) (n : ℕ) :
    groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1) ≫
      groupCohomology.map (K.subgroupOf H).subtype
        (𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) (n + 1) ≫
      groupCohomology.map (A := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
        (B := Rep.res K.subtype M) ((Subgroup.subgroupOfEquivOfLe hKH).symm)
        (Rep.isIntertwiningMap_res_res M
          (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes (n + 1) =
    groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype M)) (n + 1) := by
  have h₁ := groupCohomology.map_comp
    (A := M) (B := Rep.res H.subtype M)
    (C := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
    (f := H.subtype) (g := (K.subgroupOf H).subtype)
    (φ := 𝟙 (Rep.res H.subtype M))
    (ψ := 𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) (n + 1)
  have h₃ := groupCohomology.map_comp
    (A := M) (B := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
    (C := Rep.res K.subtype M)
    (f := H.subtype.comp (K.subgroupOf H).subtype)
    (g := (Subgroup.subgroupOfEquivOfLe hKH).symm)
    (φ := (Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M)))
    (ψ := (Rep.isIntertwiningMap_res_res M
    (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes) (n + 1)
  rw [← Category.assoc, h₁.symm]
  have h₁' :
      groupCohomology.map (H.subtype.comp (K.subgroupOf H).subtype)
          ((Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M))) (n + 1) =
        groupCohomology.map (H.subtype.comp (K.subgroupOf H).subtype)
          ((Rep.resFunctor (K.subgroupOf H).subtype).map (𝟙 (Rep.res H.subtype M)) ≫
            𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) (n + 1) :=
    groupCohomology.map_congr rfl (by ext x; simp) (n + 1)
  rw [h₁'.symm, h₃.symm]
  have hg : (H.subtype.comp (K.subgroupOf H).subtype).comp
      (Subgroup.subgroupOfEquivOfLe hKH).symm = K.subtype := by
    rw [← Subgroup.subtype_comp_subgroupOfEquivOfLe hKH]
    ext x
    simp
  exact groupCohomology.map_congr hg (by ext x; simp) (n + 1)



private theorem posRes_cancel_comparison {K H : Subgroup G} (hKH : K ≤ H) (n : ℕ)
    (iG : tateCohomology M ((n + 1 : ℕ)) ≅ groupCohomology M (n + 1))
    (iH : tateCohomology (Rep.res H.subtype M) ((n + 1 : ℕ)) ≅
      groupCohomology (Rep.res H.subtype M) (n + 1))
    (iKs : tateCohomology (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
        ((n + 1 : ℕ)) ≅
      groupCohomology (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M)) (n + 1))
    (hkey : groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1) ≫
        (groupCohomology.map (K.subgroupOf H).subtype
            (𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) (n + 1) ≫
          groupCohomology.map (A := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
            (B := Rep.res K.subtype M) ((Subgroup.subgroupOfEquivOfLe hKH).symm)
            (Rep.isIntertwiningMap_res_res M
              (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes (n + 1)) =
      groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype M)) (n + 1)) :
    (iG.hom ≫
        (groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) (n + 1) ≫ iH.inv)) ≫
        ((iH.hom ≫
            (groupCohomology.map (K.subgroupOf H).subtype
              (𝟙 (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))) (n + 1) ≫ iKs.inv)) ≫
          (iKs.hom ≫
            groupCohomology.map (A := Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M))
              (B := Rep.res K.subtype M) ((Subgroup.subgroupOfEquivOfLe hKH).symm)
              (Rep.isIntertwiningMap_res_res M
                (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH)).ofRes (n + 1))) =
      iG.hom ≫ groupCohomology.map K.subtype (𝟙 (Rep.res K.subtype M)) (n + 1) := by
  simp only [Category.assoc]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, hkey]

/-- **Tate restriction in positive degrees is transitive along a tower of subgroups** `K ≤ H ≤ G`:
restricting from `G` to `H` and then from `H` to `K` is restriction from `G` to `K`, once
`K.subgroupOf H` is identified with `K` by the Tate map along `Subgroup.subgroupOfEquivOfLe hKH`.
This is the positive-degree counterpart of `TauCeti.TateCohomology.negSuccRes_trans`. -/
@[reassoc]
theorem posRes_trans {K H : Subgroup G} (hKH : K ≤ H) (n : ℕ) :
    posRes M H n ≫ posRes (Rep.res H.subtype M) (K.subgroupOf H) n ≫
        map (e := Subgroup.subgroupOfEquivOfLe hKH) (φ := LinearMap.id)
          (Rep.isIntertwiningMap_res_res M (Subgroup.subtype_comp_subgroupOfEquivOfLe hKH))
          ((n + 1 : ℕ)) = posRes M K n := by
  rw [← cancel_mono
    ((_root_.TateCohomology.isoGroupCohomology (G := K) (n + 1)).hom.app
      (Rep.res K.subtype M))]
  simp only [Category.assoc]
  rw [map_comp_isoGroupCohomology_hom]
  simp only [posRes_comp_isoGroupCohomology_hom]
  exact posRes_cancel_comparison M hKH n
    ((_root_.TateCohomology.isoGroupCohomology (n + 1)).app M)
    ((_root_.TateCohomology.isoGroupCohomology (G := ↥H) (n + 1)).app (Rep.res H.subtype M))
    ((_root_.TateCohomology.isoGroupCohomology (G := ↥(K.subgroupOf H)) (n + 1)).app
      (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype M)))
    (map_subgroupOf_trans M hKH n)

end TauCeti.TateCohomology

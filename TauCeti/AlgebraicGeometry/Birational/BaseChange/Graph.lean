/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.FlatBaseChange
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Dominance and graph of the base change of a rational map

Consider cartesian squares `X' = X ×_S S'` and `Y' = Y ×_S S'` along `p : S' ⟶ S`, with
projections `πX : X' ⟶ X` and `πY : Y' ⟶ Y`, and an `S`-partial map `f : X ⤏ Y` defined on `V`.
Its base change `f' = AlgebraicGeometry.Scheme.PartialMap.baseChange`, defined on `V' = πX⁻¹(V)`,
is the base change of the morphism `f_V : V ⟶ Y` along `πY`: the square with `πX ∣_ V`, `f'_{V'}`,
`f_V` and `πY` is cartesian. This file draws two consequences, which for a field extension
`K'/K` say that `f_{K'}` is dominant when `f` is and `X` is geometrically irreducible, and that,
when `X` is Noetherian, the closure of the relative graph of `f_{K'}` in `X_{K'} ×_{K'} Y_{K'}` is
the base change of the closure of the relative graph of `f` in `X ×_K Y`.

* *Dominance.* When `p` is universally open (for instance `Spec K' ⟶ Spec K`), `πY` is an open map
  and the base change of the dominant `f_V` is dominant
  (`AlgebraicGeometry.IsDominant.of_isPullback_of_isOpenMap`). When moreover `X'` is
  preirreducible, `X` is nonempty and `πX` is dominant, so that the composite `f ∘ πX` is defined,
  the characterization of the base change
  (`AlgebraicGeometry.Scheme.RationalMap.existsUnique_compHom_eq_comp`) shows that every
  `S'`-rational map `f'` with `πY ∘ f' = f ∘ πX` is dominant.
* *Graph.* The relative graph `γ_f = (ι_V, f_V) : V ⟶ X ×_S Y`
  (`TauCeti.AlgebraicGeometry.opensGraph`) base changes to `γ_{f'} : V' ⟶ X' ×_{S'} Y'` along the
  natural map `X' ×_{S'} Y' ⟶ X ×_S Y`, which is itself a base change of `πX`
  (`CategoryTheory.IsPullback.pullback_map_fst`), hence of `p`. When `p` is flat and
  `γ_f` is quasi-compact, flat base change of scheme-theoretic images
  (`AlgebraicGeometry.Scheme.Hom.ker_eq_comap_of_isPullback_of_flat`) shows that the ideal sheaf of
  the graph closure of `f'` is the pullback of that of `f`: `Γ_{f'} = (Γ_f)_{S'}` as closed
  subschemes of `X' ×_{S'} Y' = (X ×_S Y) ×_S S'`. Here `Γ_f` is the scheme-theoretic closure of
  the relative graph `γ_f` in `X ×_S Y`, not `AlgebraicGeometry.Scheme.RationalMap.graph`, which is
  the graph closure in the absolute product `X × Y`.

## Main results

* `AlgebraicGeometry.Scheme.PartialMap.isPullback_baseChange`: the base change of a partial map is
  a base change of its representative.
* `AlgebraicGeometry.Scheme.PartialMap.isDominant_baseChange_hom` and
  `AlgebraicGeometry.Scheme.RationalMap.isDominant_of_compHom_eq_comp`: dominance of the base change
  along a universally open morphism.
* `AlgebraicGeometry.Scheme.PartialMap.isPullback_opensGraph_baseChange` and
  `AlgebraicGeometry.Scheme.PartialMap.ker_opensGraph_baseChange`: the graph of the base change is
  the base change of the graph, and so is its graph closure, along a flat `p`.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme

variable {X Y X' Y' S S' : Scheme.{u}} {πX : X' ⟶ X} {sX' : X' ⟶ S'} {sX : X ⟶ S}
  {πY : Y' ⟶ Y} {sY' : Y' ⟶ S'} {sY : Y ⟶ S} {p : S' ⟶ S}
  (hX : IsPullback πX sX' sX p) (hY : IsPullback πY sY' sY p)

section PartialMap

variable (f : X.PartialMap Y) [f.IsOver sX sY] (hd : Dense (πX ⁻¹ᵁ f.domain : Set X'))

/-- **The base change of a partial map is a base change of its representative.** For
`X' = X ×_S S'` and `Y' = Y ×_S S'`, the square formed by `πX ∣_ V`, the base change
`f'_{V'} : V' ⟶ Y'` on `V' = πX⁻¹(V)`, the representative `f_V : V ⟶ Y` and `πY` is cartesian. -/
theorem PartialMap.isPullback_baseChange :
    IsPullback (πX ∣_ f.domain) (f.baseChange hY πX sX' hX.w hd).hom f.hom πY := by
  refine IsPullback.of_bot ?_ (f.baseChange_hom_fst hY πX sX' hX.w hd).symm hY
  convert (isPullback_morphismRestrict πX f.domain).paste_vert hX using 1
  · exact f.baseChange_hom_snd hY πX sX' hX.w hd
  · exact f.over sX sY

/-- **Dominance of the base change.** Along a universally open `p : S' ⟶ S` (for instance
`Spec K' ⟶ Spec K` for a field extension), the base change of a partial map with dominant
representative has dominant representative. -/
theorem PartialMap.isDominant_baseChange_hom [IsDominant f.hom] [UniversallyOpen p] :
    IsDominant (f.baseChange hY πX sX' hX.w hd).hom := by
  have : UniversallyOpen πY := MorphismProperty.of_isPullback hY.flip inferInstance
  exact IsDominant.of_isPullback_of_isOpenMap (f.isPullback_baseChange hX hY hd) πY.isOpenMap

end PartialMap

include hX hY in
/-- **The base change of a dominant rational map is dominant.** Let `X' = X ×_S S'` and
`Y' = Y ×_S S'` along a universally open `p : S' ⟶ S`, with `X'` preirreducible and `πX`
dominant (as for a field extension and geometrically irreducible `X`). If `f : X ⤏ Y` is a dominant
`S`-rational map, then the `S'`-rational map `f'` with `πY ∘ f' = f ∘ πX` is dominant. -/
theorem RationalMap.isDominant_of_compHom_eq_comp [PreirreducibleSpace X'] [Nonempty X]
    [IsDominant πX] [UniversallyOpen p] (f : X ⤏ Y) [f.IsOver sX sY] [f.IsDominant]
    (f' : X' ⤏ Y') [f'.IsOver sX' sY'] (hf' : f'.compHom πY = πX.toRationalMap.comp f) :
    f'.IsDominant := by
  obtain ⟨g, _, rfl⟩ := f.exists_partialMap_over sX sY
  have hd := πX.dense_preimage_of_isDominant g.dense_domain.nonempty
  have : IsDominant g.hom := g.isDominant_toRationalMap_iff.mp inferInstance
  have : IsDominant (g.baseChange hY πX sX' hX.w hd).hom := g.isDominant_baseChange_hom hX hY hd
  rw [eq_of_compHom_eq_of_isPullback hY (sX' := sX')
    (hf'.trans (g.baseChange_toRationalMap_compHom hY πX sX' hX.w hd).symm)]
  infer_instance

section Graph

variable (f : X.PartialMap Y) [f.IsOver sX sY] (hd : Dense (πX ⁻¹ᵁ f.domain : Set X'))

/-- **The graph of the base change is the base change of the graph.** The graph
`γ_{f'} : V' ⟶ X' ×_{S'} Y'` of the base change `f'` of `f` is the base change of the graph
`γ_f : V ⟶ X ×_S Y` along the natural map `X' ×_{S'} Y' ⟶ X ×_S Y`. -/
theorem PartialMap.isPullback_opensGraph_baseChange :
    IsPullback (πX ∣_ f.domain)
      (opensGraph sX' sY' (πX ⁻¹ᵁ f.domain) (f.baseChange hY πX sX' hX.w hd).hom
        (f.baseChange_hom_snd hY πX sX' hX.w hd))
      (opensGraph sX sY f.domain f.hom (f.over sX sY))
      (pullback.map sX' sY' sX sY πX πY p hX.w.symm hY.w.symm) := by
  refine IsPullback.of_bot ?_ ?_ (hY.flip.pullback_map_fst hX.w.symm)
  · rw [opensGraph_fst]
    convert isPullback_morphismRestrict πX f.domain using 1
    exact opensGraph_fst ..
  · apply pullback.hom_ext
    · simpa using (opensGraph_fst_assoc ..).symm
    · simp only [Category.assoc, opensGraph_snd, pullback.lift_snd]
      exact ((opensGraph_snd_assoc ..).trans (f.baseChange_hom_fst hY πX sX' hX.w hd)).symm

/-- **The graph closure of the base change is the base change of the graph closure.** Along a
flat `p : S' ⟶ S` (for instance a field extension), when the graph `γ_f` is quasi-compact (for
instance when `X` is Noetherian), the ideal sheaf of the graph closure `Γ_{f'}` of the base
change in `X' ×_{S'} Y'` is the pullback of the ideal sheaf of `Γ_f` along
`X' ×_{S'} Y' ⟶ X ×_S Y`. -/
theorem PartialMap.ker_opensGraph_baseChange [Flat p]
    [QuasiCompact (opensGraph sX sY f.domain f.hom (f.over sX sY))] :
    (opensGraph sX' sY' (πX ⁻¹ᵁ f.domain) (f.baseChange hY πX sX' hX.w hd).hom
        (f.baseChange_hom_snd hY πX sX' hX.w hd)).ker =
      (opensGraph sX sY f.domain f.hom (f.over sX sY)).ker.comap
        (pullback.map sX' sY' sX sY πX πY p hX.w.symm hY.w.symm) := by
  have : Flat πX := MorphismProperty.of_isPullback hX.flip inferInstance
  have : Flat (pullback.map sX' sY' sX sY πX πY p hX.w.symm hY.w.symm) :=
    MorphismProperty.of_isPullback (hY.flip.pullback_map_fst hX.w.symm).flip inferInstance
  exact Hom.ker_eq_comap_of_isPullback_of_flat _ (f.isPullback_opensGraph_baseChange hX hY hd)

end Graph

end AlgebraicGeometry.Scheme

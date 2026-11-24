/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.GraphClosure

/-!
# The graph of a rational map

For a rational map `f : X ⤏ Y` with representative `(V, g)` (Mathlib's
`Scheme.RationalMap.representative`), the *graph* `Γ_f` is the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y`, and its *projections* `π_1 : Γ_f → X` and `π_2 : Γ_f → Y` are the
closed immersion `Γ_f → X × Y` followed by the projections of the product. The map `γ_f` factors
through `Γ_f`, with `π_1 ∘ γ_f = ι_V` and `π_2 ∘ γ_f = g`.

This is Tau Ceti's graph closure `TauCeti.AlgebraicGeometry.graphClosure` over the terminal
scheme: `X × Y` is the fibre product `X ×_{Spec ℤ} Y` (Mathlib's `prodIsoPullback` identifies it
with the categorical product), and the definitions below are abbreviations, so the graph closure
API applies to them. For instance, `TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureFst` and
`TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureSnd` give `π_1 ∘ γ_f = ι_V` and
`π_2 ∘ γ_f = g`, and `TauCeti.AlgebraicGeometry.isIso_graphClosureFst_restrict` shows that `π_1`
is an isomorphism over `V` when `Y` is separated and `V → X` is quasi-compact.

When `γ_f` is quasi-compact (for instance when `X` is a Noetherian topological space, or when
`V → X` is quasi-compact and `Y` is quasi-separated), the scheme-theoretic image API applies.
Mathlib's instances make the factorization `V → Γ_f` quasi-compact and dominant. Tau Ceti's
`Scheme.Hom.range_imageι` (in `TauCeti/AlgebraicGeometry/SchemeTheoreticImage/Basic.lean`) shows
that `Γ_f` is supported on the closure of the image of `V`, and Tau Ceti's
`Scheme.Hom.isIntegral_image` (same file) gives that `Γ_f` is integral when `X` is integral.

For `X` reduced, `Γ_f` does not depend on the representative: the graph of any partial map
representing `f` has the same kernel as `γ_f`. If moreover `Y` is separated and `f` is a rational
map over a separated base `S`, then `γ_f` factors through the closed subscheme `X ×_S Y` of
`X × Y`, and `Γ_f` is the graph closure over `S` of the representative of `f` on its domain of
definition. The graph closure API then gives the properties of the first projection: `π_1` is
proper when `Y` is proper over `S`, an isomorphism over the domain of definition of `f` when the
inclusion of that domain is quasi-compact, and a modification when both hold. Over a field `K`,
with `X` irreducible and `X` and `Y` locally of finite type over `K`, `Γ_f` has the dimension of
`X`.

For any rational map `f` over a base `S` (with no reducedness or separatedness hypotheses), `π_2`
is surjective when `f` is dominant and `X` is proper over `S`: the graph closure over `S` of the
restriction of the representative of `f` to a dense open on which it is over `S` maps into `Γ_f`
over `Y`.

## Main definitions

* `AlgebraicGeometry.Scheme.RationalMap.graphLift`: the morphism `γ_f = (ι_V, g) : V → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graph`: the graph `Γ_f`.
* `AlgebraicGeometry.Scheme.RationalMap.graphι`: the closed immersion `Γ_f → X × Y`.
* `AlgebraicGeometry.Scheme.RationalMap.graphFst`, `AlgebraicGeometry.Scheme.RationalMap.graphSnd`:
  the projections `π_1` and `π_2`.
* `AlgebraicGeometry.Scheme.RationalMap.toGraph`: the factorization `V → Γ_f` of `γ_f`.
* `AlgebraicGeometry.Scheme.RationalMap.graphIsoGraphClosure`: for an `S`-rational map from a
  reduced scheme to a separated scheme, with `S` separated, the isomorphism of `Γ_f` with the graph
  closure in `X ×_S Y` of the representative of `f` on its domain of definition.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isIntegral_graph`: the graph of a rational map out of an
  integral scheme is integral when `γ_f` is quasi-compact, for instance when `X` is Noetherian.
* `AlgebraicGeometry.Scheme.RationalMap.ker_opensGraph_eq_ker_graphLift`: independence of the
  representative.
* `AlgebraicGeometry.Scheme.RationalMap.isProper_graphFst`,
  `AlgebraicGeometry.Scheme.RationalMap.isIso_graphFst_restrict` and
  `AlgebraicGeometry.Scheme.RationalMap.isModification_graphFst`: for `X` reduced and `f` over a
  separated base `S`, `π_1` is proper when `Y` is proper over `S`, an isomorphism over the domain
  of definition of `f` when `Y` is separated and the inclusion of that domain is quasi-compact,
  and a modification when `Y` is proper over `S` and that inclusion is quasi-compact.
* `AlgebraicGeometry.Scheme.RationalMap.surjective_graphSnd`: `π_2` is surjective for dominant `f`
  over a base `S` over which `X` is proper.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalKrullDim_graph`: over a field `K`, for `X`
  reduced and irreducible, `Y` separated, and `X` and `Y` locally of finite type over `K`, `Γ_f`
  has the dimension of `X`.

## References

* [T.-C. Dinh and N. Sibony, *Une borne supérieure pour l'entropie topologique d'une application
  rationnelle*, Ann. of Math. 161 (2005)](https://arxiv.org/abs/math/0303271), the graph of a
  rational map and its projections.
-/

public section

open CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {X Y S : Scheme.{u}} (f : X ⤏ Y)

/-- The morphism `γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`, with
`X × Y` the fibre product over the terminal scheme. -/
abbrev graphLift :
    f.representative.domain.toScheme ⟶ pullback (terminal.from X) (terminal.from Y) :=
  opensGraph (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The graph `Γ_f` of a rational map `f : X ⤏ Y`: the scheme-theoretic image of
`γ_f = (ι_V, g) : V → X × Y` for the representative `(V, g)` of `f`, that is, the graph closure
of `g` over the terminal scheme. -/
abbrev graph : Scheme.{u} :=
  graphClosure (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The closed immersion of the graph `Γ_f` into `X × Y`. -/
abbrev graphι : graph f ⟶ pullback (terminal.from X) (terminal.from Y) :=
  (graphLift f).imageι

/-- The first projection `π_1 : Γ_f → X` of the graph. -/
abbrev graphFst : graph f ⟶ X :=
  graphClosureFst (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The second projection `π_2 : Γ_f → Y` of the graph. -/
abbrev graphSnd : graph f ⟶ Y :=
  graphClosureSnd (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- The factorization `V → Γ_f` of `γ_f` through the graph. -/
abbrev toGraph : f.representative.domain.toScheme ⟶ graph f :=
  toGraphClosure (terminal.from X) (terminal.from Y) f.representative.domain f.representative.hom
    (terminal.hom_ext _ _)

/-- Out of a Noetherian space, `γ_f` is quasi-compact: its source is an open subspace of a
Noetherian space. -/
instance quasiCompact_graphLift [NoetherianSpace X] : QuasiCompact (graphLift f) :=
  have : NoetherianSpace f.representative.domain.toScheme :=
    NoetherianSpace.set (f.representative.domain : Set X)
  quasiCompact_of_noetherianSpace_source _

/-- The graph of a rational map out of an integral scheme is integral when `γ_f` is
quasi-compact. -/
instance isIntegral_graph [IsIntegral X] [QuasiCompact (graphLift f)] : IsIntegral (graph f) :=
  have : Nonempty f.representative.domain :=
    f.representative.dense_domain.nonempty.to_subtype
  inferInstance

section Representative

variable [IsReduced X]

/-- **Independence of the representative.** For `X` reduced, the graph of every partial map `g`
representing `f` has the same kernel as `γ_f`, so the same scheme-theoretic image `Γ_f`. -/
theorem ker_opensGraph_eq_ker_graphLift (g : X.PartialMap Y) (hg : g.toRationalMap = f) :
    (opensGraph (terminal.from X) (terminal.from Y) g.domain g.hom
      (terminal.hom_ext _ _)).ker = (graphLift f).ker := by
  -- `g` and the representative of `f` agree on a dense open `W`, and restricting a graph to a
  -- dense open does not change its kernel
  obtain ⟨W, hW, hWg, hWf, e⟩ :=
    PartialMap.toRationalMap_eq_iff.mp (hg.trans f.toRationalMap_representative.symm)
  rw [graphLift, ← ker_opensGraph_homOfLE_comp hW hWg, ← ker_opensGraph_homOfLE_comp hW hWf]
  rw [PartialMap.restrict_hom, PartialMap.restrict_hom] at e
  congr 2

end Representative

section Base

variable (sX : X ⟶ S) (sY : Y ⟶ S)

/-- The morphism `X ×_S Y → X × Y`, a closed immersion when `S` is separated. -/
private def pullbackToProd :
    pullback sX sY ⟶ pullback (terminal.from X) (terminal.from Y) :=
  pullback.mapDesc sX sY (terminal.from S) ≫
    (pullback.congrHom (terminal.hom_ext _ _) (terminal.hom_ext _ _)).hom

private instance [S.IsSeparated] : IsClosedImmersion (pullbackToProd sX sY) := by
  unfold pullbackToProd
  infer_instance

@[reassoc (attr := simp)]
private theorem pullbackToProd_fst :
    pullbackToProd sX sY ≫ pullback.fst _ _ = pullback.fst sX sY := by
  simp [pullbackToProd]

@[reassoc (attr := simp)]
private theorem pullbackToProd_snd :
    pullbackToProd sX sY ≫ pullback.snd _ _ = pullback.snd sX sY := by
  simp [pullbackToProd]

/-- **The second projection of the graph of a dominant rational map is surjective** when `X` is
proper over a base `S` over which `f` is defined. -/
theorem surjective_graphSnd [f.IsOver sX sY] [IsProper sX] [f.IsDominant] :
    Surjective (graphSnd f) := by
  -- restrict the representative of `f` to a dense open `U` on which it is over `S`
  have : f.representative.toRationalMap.IsOver sX sY := by
    rwa [f.toRationalMap_representative]
  obtain ⟨U, hU, hUV, _⟩ := f.representative.exists_restrict_isOver sX sY
  set g := f.representative.restrict U hU hUV
  set h := opensGraph sX sY g.domain g.hom (g.over sX sY)
  have hgV : g.domain ≤ f.representative.domain := hUV
  -- the graph closure of `g` over `S` maps to `Γ_f` over `Y`
  have e : h ≫ pullbackToProd sX sY = X.homOfLE hgV ≫ graphLift f := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackToProd_fst, opensGraph_fst, Category.assoc, opensGraph_fst,
        Scheme.homOfLE_ι]
    · rw [Category.assoc, pullbackToProd_snd, opensGraph_snd, Category.assoc, opensGraph_snd]
      rfl
  have H : (graphι f).ker ≤ (h.imageι ≫ pullbackToProd sX sY).ker := by
    rw [Scheme.Hom.ker_comp, IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι,
      ← Scheme.Hom.ker_comp, e]
    exact Scheme.Hom.le_ker_comp _ _
  have e' : IsClosedImmersion.lift _ _ H ≫ graphSnd f =
      graphClosureSnd sX sY g.domain g.hom (g.over sX sY) := by
    rw [graphSnd, graphClosureSnd_def, graphClosureSnd_def, ← Category.assoc,
      IsClosedImmersion.lift_fac, Category.assoc, pullbackToProd_snd]
  suffices Surjective (graphClosureSnd sX sY g.domain g.hom (g.over sX sY)) by
    rw [← e'] at this
    exact Surjective.of_comp (IsClosedImmersion.lift _ _ H) _
  -- the range of the second projection is closed and contains the dense range of `g`
  refine ⟨Set.range_eq_univ.mp ?_⟩
  rw [← (Scheme.Hom.isClosedMap _).isClosed_range.closure_eq, ← Set.univ_subset_iff,
    ← g.hom.denseRange.closure_range]
  refine closure_mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨_, congr($(toGraphClosure_graphClosureSnd sX sY _ _ (g.over sX sY)) x)⟩

variable [IsReduced X] [Y.IsSeparated] [S.IsSeparated] [f.IsOver sX sY]

private theorem ker_imageι_comp_pullbackToProd :
    ((opensGraph sX sY f.toPartialMap.domain f.toPartialMap.hom
      (f.toPartialMap.over sX sY)).imageι ≫ pullbackToProd sX sY).ker = (graphι f).ker := by
  rw [Scheme.Hom.ker_comp, IdealSheafData.ker_subschemeι, ← Scheme.Hom.ker_comp,
    IdealSheafData.ker_subschemeι, ← ker_opensGraph_eq_ker_graphLift f f.toPartialMap
      f.toRationalMap_toPartialMap]
  congr 1
  apply pullback.hom_ext <;> simp

/-- **The graph lies in `X ×_S Y`.** For `X` reduced, `Y` and `S` separated and an `S`-rational
map `f : X ⤏ Y`, the graph `Γ_f ⊆ X × Y` is isomorphic to the graph closure in `X ×_S Y` of the
representative of `f` on its domain of definition, compatibly with the projections. -/
def graphIsoGraphClosure :
    graph f ≅ graphClosure sX sY f.toPartialMap.domain f.toPartialMap.hom
      (f.toPartialMap.over sX sY) :=
  have := IsClosedImmersion.isIso_lift _ _ (ker_imageι_comp_pullbackToProd f sX sY)
  asIso (IsClosedImmersion.lift _ (graphι f) (ker_imageι_comp_pullbackToProd f sX sY).le)

/-- The isomorphism `graphIsoGraphClosure` is compatible with the first projections. -/
@[reassoc (attr := simp)]
theorem graphIsoGraphClosure_hom_graphClosureFst :
    (graphIsoGraphClosure f sX sY).hom ≫ graphClosureFst sX sY f.toPartialMap.domain
      f.toPartialMap.hom (f.toPartialMap.over sX sY) = graphFst f := by
  rw [graphClosureFst_def, ← pullbackToProd_fst, ← Category.assoc _ (pullbackToProd sX sY),
    graphIsoGraphClosure, asIso_hom, IsClosedImmersion.lift_fac_assoc]
  exact (graphClosureFst_def _ _ _ _ _).symm

/-- The isomorphism `graphIsoGraphClosure` is compatible with the second projections. -/
@[reassoc (attr := simp)]
theorem graphIsoGraphClosure_hom_graphClosureSnd :
    (graphIsoGraphClosure f sX sY).hom ≫ graphClosureSnd sX sY f.toPartialMap.domain
      f.toPartialMap.hom (f.toPartialMap.over sX sY) = graphSnd f := by
  rw [graphClosureSnd_def, ← pullbackToProd_snd, ← Category.assoc _ (pullbackToProd sX sY),
    graphIsoGraphClosure, asIso_hom, IsClosedImmersion.lift_fac_assoc]
  exact (graphClosureSnd_def _ _ _ _ _).symm

end Base

section Projections

variable [IsReduced X]

/-- **The first projection of the graph is proper** when `Y` is proper over a separated base `S`
over which `f` is defined. -/
theorem isProper_graphFst (sX : X ⟶ S) (sY : Y ⟶ S) [S.IsSeparated] [f.IsOver sX sY]
    [IsProper sY] : IsProper (graphFst f) := by
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from sY]; infer_instance⟩
  rw [← graphIsoGraphClosure_hom_graphClosureFst f sX sY]
  infer_instance

/-- **The first projection of the graph is an isomorphism over the domain of definition** of
`f`, for `X` reduced, `Y` separated and the inclusion of the domain quasi-compact (for instance
when `X` is locally Noetherian). -/
instance isIso_graphFst_restrict [Y.IsSeparated] [QuasiCompact f.domain.ι] :
    IsIso (graphFst f ∣_ f.domain) := by
  -- the domain of `f.toPartialMap` is `f.domain` by definition
  have : QuasiCompact f.toPartialMap.domain.ι := ‹QuasiCompact f.domain.ι›
  have : f.IsOver (terminal.from X) (terminal.from Y) :=
    ⟨⟨f.representative, inferInstance, f.toRationalMap_representative⟩⟩
  rw [← graphIsoGraphClosure_hom_graphClosureFst f (terminal.from X) (terminal.from Y),
    morphismRestrict_comp]
  have h : IsIso (graphClosureFst (terminal.from X) (terminal.from Y) f.toPartialMap.domain
      f.toPartialMap.hom (f.toPartialMap.over _ _) ∣_ f.toPartialMap.domain) := inferInstance
  -- `h` is about the restriction over `f.toPartialMap.domain`, which is `f.domain` by definition
  exact IsIso.comp_isIso' (isPullback_morphismRestrict _ _).isIso_fst_of_isIso h

/-- **The first projection of the graph is a modification** when `Y` is proper over a separated
base `S` over which `f` is defined and the inclusion of the domain of definition of `f` is
quasi-compact: it is proper, and an isomorphism over that dense open. -/
theorem isModification_graphFst (sX : X ⟶ S) (sY : Y ⟶ S) [S.IsSeparated] [f.IsOver sX sY]
    [IsProper sY] [QuasiCompact f.domain.ι] : IsModification (graphFst f) := by
  have : Y.IsSeparated := ⟨by rw [← terminal.comp_from sY]; infer_instance⟩
  -- the domain of `f.toPartialMap` is `f.domain` by definition
  have : QuasiCompact f.toPartialMap.domain.ι := ‹QuasiCompact f.domain.ι›
  have := isModification_graphClosureFst (hg := f.toPartialMap.over sX sY) f.dense_domain
  rw [← graphIsoGraphClosure_hom_graphClosureFst f sX sY]
  infer_instance

/-- **The dimension of the graph.** Over a field `K`, for `X` reduced and irreducible, `Y`
separated and `f : X ⤏ Y` a `K`-rational map with `X` and `Y` locally of finite type over `K`,
the graph `Γ_f` has the topological Krull dimension of `X`. -/
theorem topologicalKrullDim_graph [Y.IsSeparated] {K : Type u} [Field K]
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) [IrreducibleSpace X] [f.IsOver sX sY]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] :
    topologicalKrullDim (graph f) = topologicalKrullDim X := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have : Nonempty f.toPartialMap.domain := f.dense_domain.nonempty.to_subtype
  rw [← topologicalKrullDim_graphClosure (f.toPartialMap.over sX sY)]
  exact IsHomeomorph.topologicalKrullDim_eq _
    (graphIsoGraphClosure f sX sY).hom.homeomorph.isHomeomorph

end Projections

end AlgebraicGeometry.Scheme.RationalMap

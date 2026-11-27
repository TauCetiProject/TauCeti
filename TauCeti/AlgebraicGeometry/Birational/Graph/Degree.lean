/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Composition
public import TauCeti.AlgebraicGeometry.Birational.Graph.Basic
public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Birationality
public import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# The topological degree of the second projection of a graph

Let `f : X ⤏ Y` be a rational map from a reduced scheme to a separated scheme, with graph
`Γ_f ⊆ X × Y` and projections `π_1 : Γ_f → X`, `π_2 : Γ_f → Y`. Where `π_1` lands in the domain of
definition `U` of `f`, `π_2` is `π_1` followed by the representative `f_U` of `f`. As rational
maps, `π_2 = f ∘ π_1`.

For `X` and `Y` integral, `π_1` is an isomorphism over `U`, so it induces an isomorphism of
function fields and has topological degree `1`. If `f` is dominant, so is `π_2`, and by
multiplicativity of the topological degree `π_2` has topological degree `e(f)`: its function-field
map is `f^*` followed by the isomorphism `π_1^* : K(X) → K(Γ_f)`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.comp_graphSnd_eq_of_comp_graphFst`: a morphism into
  `Γ_f` whose composite with `π_1` lands in the domain of definition of `f` has composite with
  `π_2` given by `f` on that domain.
* `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_graphSnd`: `π_2 = f ∘ π_1` as rational maps.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_graphFst`: `π_1` has topological
  degree `1`.
* `AlgebraicGeometry.Scheme.RationalMap.topologicalDegree_graphSnd`: for `f` dominant, `π_2` has
  topological degree `e(f)`.
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.RationalMap

universe u

variable {X Y : Scheme.{u}} (f : X ⤏ Y)

section Reduced

variable [IsReduced X] [Y.IsSeparated] [QuasiCompact f.domain.ι]

/-- For `X` reduced, `Y` separated and the inclusion of the domain of definition `U` of `f`
quasi-compact, let `a : T ⟶ Γ_f` be a morphism with `π_1 ∘ a` landing in `U`, through
`b : T ⟶ U`. Then `π_2 ∘ a` is `f_U ∘ b`, for the representative `f_U` of `f` on `U`. -/
theorem comp_graphSnd_eq_of_comp_graphFst {T : Scheme.{u}} (a : T ⟶ graph f)
    (b : T ⟶ f.toPartialMap.domain.toScheme) (h : b ≫ f.toPartialMap.domain.ι = a ≫ graphFst f) :
    a ≫ graphSnd f = b ≫ f.toPartialMap.hom := by
  have : QuasiCompact f.toPartialMap.domain.ι := by rwa [f.toPartialMap_domain]
  have : f.IsOver (terminal.from X) (terminal.from Y) :=
    ⟨⟨f.representative, inferInstance, f.toRationalMap_representative⟩⟩
  set e := graphIsoGraphClosure f (terminal.from X) (terminal.from Y)
  set p := graphClosureFst (terminal.from X) (terminal.from Y) f.toPartialMap.domain
    f.toPartialMap.hom (f.toPartialMap.over _ _)
  set q := graphClosureSnd (terminal.from X) (terminal.from Y) f.toPartialMap.domain
    f.toPartialMap.hom (f.toPartialMap.over _ _)
  have hc : (a ≫ e.hom) ≫ p = b ≫ f.toPartialMap.domain.ι := by
    rw [Category.assoc, graphIsoGraphClosure_hom_graphClosureFst]
    exact h.symm
  -- `a ≫ e.hom` lands in the preimage of the domain of definition
  have hr : Set.range (a ≫ e.hom).base ⊆ Set.range (p ⁻¹ᵁ f.toPartialMap.domain).ι.base := by
    rintro _ ⟨t, rfl⟩
    rw [Opens.range_ι, SetLike.mem_coe, Hom.mem_preimage, ← Hom.comp_apply, hc, Hom.comp_apply]
    exact (b t).property
  set c := IsOpenImmersion.lift (p ⁻¹ᵁ f.toPartialMap.domain).ι (a ≫ e.hom) hr
  have hb : c ≫ (p ∣_ f.toPartialMap.domain) = b := by
    rw [← cancel_mono f.toPartialMap.domain.ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, hc]
  have hq : (p ∣_ f.toPartialMap.domain) ≫ f.toPartialMap.hom =
      (p ⁻¹ᵁ f.toPartialMap.domain).ι ≫ q :=
    graphClosureFst_restrict_comp
  calc a ≫ graphSnd f = (a ≫ e.hom) ≫ q := by
        rw [Category.assoc, graphIsoGraphClosure_hom_graphClosureSnd]
    _ = c ≫ (p ⁻¹ᵁ f.toPartialMap.domain).ι ≫ q := by rw [IsOpenImmersion.lift_fac_assoc]
    _ = b ≫ f.toPartialMap.hom := by rw [← hq, ← Category.assoc, hb]

/-- The first projection `π_1 : Γ_f → X` is dominant: it maps the factorization of `γ_f` through
`Γ_f` onto the dense domain of the representative of `f`. -/
instance isDominant_graphFst : IsDominant (graphFst f) := by
  have := Opens.isDominant_ι f.representative.dense_domain
  have : IsDominant (toGraph f ≫ graphFst f) := by
    rw [toGraphClosure_graphClosureFst]
    infer_instance
  exact IsDominant.of_comp (toGraph f) (graphFst f)

/-- **The second projection is `f` after the first**: `π_2 = f ∘ π_1` as rational maps, for `X`
reduced, `Γ_f` integral (for instance `X` integral and Noetherian), `Y` separated and the
inclusion of the domain of definition of `f` quasi-compact. -/
theorem toRationalMap_graphSnd [IsIntegral (graph f)] [Nonempty X] :
    (graphSnd f).toRationalMap = (graphFst f).toRationalMap.comp f := by
  calc (graphSnd f).toRationalMap
      = ((graphFst f).toPartialMap.comp f.toPartialMap).toRationalMap := by
        symm
        rw [PartialMap.toRationalMap_eq_iff]
        have : ((graphFst f).toPartialMap.comp f.toPartialMap).IsOver (terminal.from _)
            (terminal.from Y) := ⟨terminal.hom_ext _ _⟩
        refine (PartialMap.equiv_toPartialMap_iff_of_isSeparated (terminal.from _)
          (terminal.from Y) (terminal.hom_ext _ _)).2 ?_
        rw [← PartialMap.compDomainRestrict_hom]
        refine (comp_graphSnd_eq_of_comp_graphFst f _ _ ?_).symm
        rw [PartialMap.compDomainRestrict_ι]
        simp only [Hom.toPartialMap_hom, Scheme.topIso_hom]
        exact Scheme.homOfLE_ι_assoc _ _ _
    _ = (graphFst f).toRationalMap.comp f.toPartialMap.toRationalMap :=
        (toRationalMap_comp _ _).symm
    _ = (graphFst f).toRationalMap.comp f := by rw [f.toRationalMap_toPartialMap]

end Reduced

section Integral

variable [IsIntegral X] [IsIntegral (graph f)] [Y.IsSeparated] [QuasiCompact f.domain.ι]

/-- **The first projection has topological degree one**: `π_1 : Γ_f → X` is an isomorphism over
the dense domain of definition of `f`, so `π_1^* : K(X) → K(Γ_f)` is an isomorphism. -/
@[simp]
theorem topologicalDegree_graphFst : (graphFst f).toRationalMap.topologicalDegree = 1 := by
  have : Nonempty X := IsIntegral.nonempty
  have : Nonempty f.domain := f.dense_domain.nonempty.to_subtype
  have := (graphFst f).isIso_functionFieldMap_of_isOpenImmersion_morphismRestrict f.domain
  rw [topologicalDegree_eq_one_iff_isIso, Hom.functionFieldMap_toRationalMap]
  infer_instance

variable [IsIntegral Y] [f.IsDominant]

/-- **The second projection of the graph of a dominant rational map is dominant**: it is `f`
after the dominant `π_1`, as rational maps. -/
instance isDominant_graphSnd : IsDominant (graphSnd f) := by
  have : Nonempty X := IsIntegral.nonempty
  have h : (graphSnd f).toRationalMap.IsDominant := by
    rw [toRationalMap_graphSnd]
    infer_instance
  rw [Hom.toRationalMap, PartialMap.isDominant_toRationalMap_iff, Hom.toPartialMap_hom] at h
  exact IsDominant.of_comp (H := h) _ _

/-- **The topological degree of the second projection.** For a dominant rational map `f : X ⤏ Y` of
integral schemes, with `Γ_f` integral, `Y` separated and the inclusion of the domain of
definition quasi-compact, the second projection `π_2 : Γ_f → Y` has topological degree `e(f)`. -/
@[simp]
theorem topologicalDegree_graphSnd :
    (graphSnd f).toRationalMap.topologicalDegree = f.topologicalDegree := by
  have : Nonempty X := IsIntegral.nonempty
  rw [topologicalDegree_congr (toRationalMap_graphSnd f), topologicalDegree_comp,
    topologicalDegree_graphFst, one_mul]

end Integral

end AlgebraicGeometry.Scheme.RationalMap

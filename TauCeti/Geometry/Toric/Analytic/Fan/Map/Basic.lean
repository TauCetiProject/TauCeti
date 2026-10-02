/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Subfan.Basic

/-!
# Toric maps of analytic realizations

A morphism of fans `f : FanHom Φ Ψ` carries every cone `σ` of `Φ` into a cone `υ` of `Ψ`.
Precomposition of characters with the lattice map of `f` sends the dual semigroup of `υ` to the
dual semigroup of `σ`, and pulling complex points back along this map of semigroups gives a
continuous map from the affine analytic chart of `σ` to the affine analytic chart of `υ`. Viewed in
the analytic realization of `Ψ`, these chart maps do not depend on the target cone `υ`, and they
commute with the face maps of the source fan. They therefore glue to a continuous map
`FanHom.analyticMap` between the analytic realizations of two regular fans, the analytic
counterpart of the morphism of toric schemes `TauCeti.Toric.FanHom.algebraicMap`.

On the chart of a cone `σ` the glued map is the chart map into the chart of the least target cone
`TauCeti.Toric.FanHom.leastCone`, or equivalently into the chart of any target cone containing the
image of `σ`. The construction is functorial: the identity morphism of a fan induces the identity,
and a composite of fan morphisms induces the composite map. The inclusion of an open subfan
induces the open-subfan map `TauCeti.Toric.Fan.subfanAnalyticMap`.

## Main declarations

* `TauCeti.Toric.FanHom.analyticChartMap`: the map of affine analytic charts induced by a fan
  morphism and a target cone containing the image of the source cone.
* `TauCeti.Toric.FanHom.analyticMap`: the continuous map of analytic realizations induced by a
  morphism of regular fans.
* `TauCeti.Toric.FanHom.analyticMap_analyticAffineChartι`: its chart formula.
* `TauCeti.Toric.FanHom.analyticMap_id` and `TauCeti.Toric.FanHom.analyticMap_comp`: its
  functoriality.
* `TauCeti.Toric.FanHom.analyticMap_subfanInclusion`: the inclusion of an open subfan induces the
  open-subfan map.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory

namespace TauCeti.Toric.FanHom

universe u

variable {N N' N'' V V' V'' : Type u} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''} {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''}
  (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)

/-! ### Chart maps -/

/-- The map from the affine analytic chart of a cone `σ` of `Φ` to the affine analytic chart of a
cone `υ` of `Ψ` into which the fan morphism carries `σ`: complex points are pulled back along the
map of dual semigroups induced by the fan morphism. -/
noncomputable def analyticChartMap {σ : Φ.cones} {υ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V')) :
    (Φ.analyticAffineChartDiagram hΦ).obj σ ⟶ (Ψ.analyticAffineChartDiagram hΨ).obj υ :=
  letI := affinePointTopology
    (Φ.analyticChartGenerators σ ((Fan.isRegular_iff.mp hΦ) σ.1 σ.2)).2
  letI := affinePointTopology
    (Ψ.analyticChartGenerators υ ((Fan.isRegular_iff.mp hΨ) υ.1 υ.2)).2
  TopCat.ofHom ⟨AffineSemigroupComplexPoint.comap
    (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice h),
    AffineSemigroupComplexPoint.continuous_comap _ _ _⟩

/-- The chart map pulls a complex point back along the map of dual semigroups. -/
@[simp]
theorem analyticChartMap_apply {σ : Φ.cones} {υ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V'))
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    (f.analyticChartMap hΦ hΨ h x : AffineSemigroupComplexPoint (dualSemigroup Ψ.lattice υ.1)) =
      AffineSemigroupComplexPoint.comap
        (dualSemigroupMap Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice h) x :=
  (rfl)

/-- Restricting to a face of the source cone and then mapping is mapping from the face. -/
@[reassoc]
theorem map_comp_analyticChartMap {τ σ : Φ.cones} {υ : Ψ.cones} (hτσ : τ ⟶ σ)
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V')) :
    (Φ.analyticAffineChartDiagram hΦ).map hτσ ≫ f.analyticChartMap hΦ hΨ h =
      f.analyticChartMap hΦ hΨ (h.mono_left (SetLike.coe_subset_coe.mpr (leOfHom hτσ))) := by
  ext x : 1
  rw [TopCat.comp_app, analyticChartMap_apply, analyticChartMap_apply,
    Fan.analyticAffineChartDiagram_map_apply]
  refine (AffineSemigroupComplexPoint.comap_comap _ _ _).trans
    (congrArg (AffineSemigroupComplexPoint.comap · _) ?_)
  ext m n
  simp

/-- Mapping into a target cone and then restricting to a larger target cone is mapping into the
larger cone. -/
@[reassoc]
theorem analyticChartMap_comp_map {σ : Φ.cones} {κ υ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (κ.1 : Set V')) (hκυ : κ ⟶ υ) :
    f.analyticChartMap hΦ hΨ h ≫ (Ψ.analyticAffineChartDiagram hΨ).map hκυ =
      f.analyticChartMap hΦ hΨ (h.mono_right (SetLike.coe_subset_coe.mpr (leOfHom hκυ))) := by
  ext x : 1
  rw [TopCat.comp_app, Fan.analyticAffineChartDiagram_map_apply, analyticChartMap_apply,
    analyticChartMap_apply]
  refine (AffineSemigroupComplexPoint.comap_comap _ _ _).trans
    (congrArg (AffineSemigroupComplexPoint.comap · _) ?_)
  ext m n
  simp

/-- In the analytic realization of the target fan, the chart map does not depend on the target
cone into which the source cone is carried. -/
theorem analyticChartMap_comp_analyticAffineChartι {σ : Φ.cones} {υ υ' : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V'))
    (h' : Set.MapsTo f.realMap (σ.1 : Set V) (υ'.1 : Set V')) :
    f.analyticChartMap hΦ hΨ h ≫ Ψ.analyticAffineChartι hΨ υ =
      f.analyticChartMap hΦ hΨ h' ≫ Ψ.analyticAffineChartι hΨ υ' := by
  -- Both composites factor through the chart of the intersection cone `υ ⊓ υ'`.
  have hκ : Set.MapsTo f.realMap (σ.1 : Set V) ((υ ⊓ υ').1 : Set V') := h.inter h'
  rw [← f.analyticChartMap_comp_map hΦ hΨ hκ (homOfLE inf_le_left),
    ← f.analyticChartMap_comp_map hΦ hΨ hκ (homOfLE inf_le_right), Category.assoc,
    Category.assoc, Fan.analyticAffineChartDiagram_map_comp_analyticAffineChartι,
    Fan.analyticAffineChartDiagram_map_comp_analyticAffineChartι]

/-- Points of two charts of the source fan with the same image in its realization have the same
image, after the chart maps, in the realization of the target fan. -/
private theorem analyticAffineChartι_analyticChartMap_eq_of_eq {σ τ : Φ.cones} {υ υ' : Ψ.cones}
    (hσ : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V'))
    (hτ : Set.MapsTo f.realMap (τ.1 : Set V) (υ'.1 : Set V'))
    {x : (Φ.analyticAffineChartDiagram hΦ).obj σ} {y : (Φ.analyticAffineChartDiagram hΦ).obj τ}
    (h : Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y) :
    Ψ.analyticAffineChartι hΨ υ (f.analyticChartMap hΦ hΨ hσ x) =
      Ψ.analyticAffineChartι hΨ υ' (f.analyticChartMap hΦ hΨ hτ y) := by
  -- Both points come from a point `z` of the chart of `σ ⊓ τ`, and both sides are the chart map
  -- of `z` into the chart of `υ`, seen in the target realization.
  obtain ⟨z, rfl, rfl⟩ := (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).mp h
  have hz : Set.MapsTo f.realMap ((σ ⊓ τ).1 : Set V) (υ.1 : Set V') :=
    hσ.mono_left (SetLike.coe_subset_coe.mpr inf_le_left)
  rw [Fan.analyticOverlapLeft_def, Fan.analyticOverlapRight_def]
  have hzσ := ConcreteCategory.congr_hom ((f.map_comp_analyticChartMap_assoc hΦ hΨ
    (homOfLE inf_le_left) hσ (Ψ.analyticAffineChartι hΨ υ)).trans
      (f.analyticChartMap_comp_analyticAffineChartι hΦ hΨ _ hz)) z
  have hzτ := ConcreteCategory.congr_hom ((f.map_comp_analyticChartMap_assoc hΦ hΨ
    (homOfLE inf_le_right) hτ (Ψ.analyticAffineChartι hΨ υ')).trans
      (f.analyticChartMap_comp_analyticAffineChartι hΦ hΨ _ hz)) z
  exact hzσ.trans hzτ.symm

/-! ### The glued map -/

/-- The continuous map between the analytic realizations of two regular fans induced by a fan
morphism, glued from the chart maps into the charts of the least target cones. -/
noncomputable def analyticMap : Φ.analyticRealization hΦ ⟶ Ψ.analyticRealization hΨ :=
  Limits.Multicoequalizer.desc (Φ.analyticGlueData hΦ).diagram (Ψ.analyticRealization hΨ)
    (fun σ ↦ f.analyticChartMap hΦ hΨ (υ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩)
      (f.mapsTo_leastCone σ.2) ≫
      Ψ.analyticAffineChartι hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) (by
    rintro ⟨σ, τ⟩
    ext x
    let D := Φ.analyticGlueData hΦ
    -- The glue condition, restated on the chart inclusions; the cones are typed as cones of the
    -- fan so that `analyticAffineChartι_def` applies.
    have hglue : ∀ (σ τ : Φ.cones) (x : D.V (σ, τ)),
        Φ.analyticAffineChartι hΦ σ (D.f σ τ x) =
          Φ.analyticAffineChartι hΦ τ (D.f τ σ (D.t σ τ x)) := fun σ τ x ↦ by
      rw [Fan.analyticAffineChartι_def, Fan.analyticAffineChartι_def]
      exact (ConcreteCategory.congr_hom (D.glue_condition σ τ) x).symm
    rw [GlueData.diagram_fst, GlueData.diagram_snd]
    exact f.analyticAffineChartι_analyticChartMap_eq_of_eq hΦ hΨ _ _ (hglue σ τ x))

/-- On the chart of a cone `σ`, the glued map is the chart map into the chart of any target cone
`υ` into which the fan morphism carries `σ`. -/
@[reassoc]
theorem analyticAffineChartι_comp_analyticMap {σ : Φ.cones} {υ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V')) :
    Φ.analyticAffineChartι hΦ σ ≫ f.analyticMap hΦ hΨ =
      f.analyticChartMap hΦ hΨ h ≫ Ψ.analyticAffineChartι hΨ υ := by
  rw [Fan.analyticAffineChartι_def, analyticMap]
  exact (Limits.Multicoequalizer.π_desc _ _ _ _ _).trans
    (f.analyticChartMap_comp_analyticAffineChartι hΦ hΨ _ h)

/-- On a point of the chart of a cone `σ`, the glued map is the chart map into the chart of any
target cone `υ` into which the fan morphism carries `σ`. -/
theorem analyticMap_analyticAffineChartι_of_mapsTo {σ : Φ.cones} {υ : Ψ.cones}
    (h : Set.MapsTo f.realMap (σ.1 : Set V) (υ.1 : Set V'))
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    f.analyticMap hΦ hΨ (Φ.analyticAffineChartι hΦ σ x) =
      Ψ.analyticAffineChartι hΨ υ (f.analyticChartMap hΦ hΨ h x) :=
  ConcreteCategory.congr_hom (f.analyticAffineChartι_comp_analyticMap hΦ hΨ h) x

/-- On a point of the chart of a cone `σ`, the glued map is the chart map into the chart of the
least target cone `TauCeti.Toric.FanHom.leastCone`. This is the analytic counterpart of
`TauCeti.Toric.FanHom.affineToricChartι_comp_algebraicMap`. -/
@[simp]
theorem analyticMap_analyticAffineChartι (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram hΦ).obj σ) :
    f.analyticMap hΦ hΨ (Φ.analyticAffineChartι hΦ σ x) =
      Ψ.analyticAffineChartι hΨ ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
        (f.analyticChartMap hΦ hΨ (υ := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩)
          (f.mapsTo_leastCone σ.2) x) :=
  f.analyticMap_analyticAffineChartι_of_mapsTo hΦ hΨ _ x

/-! ### Functoriality -/

/-- The identity morphism of a regular fan induces the identity of its analytic realization. -/
@[simp]
theorem analyticMap_id : (FanHom.id Φ).analyticMap hΦ hΦ = 𝟙 (Φ.analyticRealization hΦ) := by
  refine Φ.analyticRealization_hom_ext hΦ fun σ ↦ ?_
  rw [(FanHom.id Φ).analyticAffineChartι_comp_analyticMap hΦ hΦ (υ := σ)
      (by rw [id_realMap]; exact Set.mapsTo_id _),
    Category.comp_id]
  -- The identity fan morphism pulls a complex point back along the identity of its dual
  -- semigroup.
  conv_rhs => rw [← Category.id_comp (Φ.analyticAffineChartι hΦ σ)]
  congr 1
  ext x : 1
  rw [analyticChartMap_apply, TopCat.id_app]
  refine (congrArg (AffineSemigroupComplexPoint.comap · _) ?_).trans
    (congrFun AffineSemigroupComplexPoint.comap_id _)
  ext m n
  simp

/-- A composite of morphisms of regular fans induces the composite of the analytic maps. -/
theorem analyticMap_comp (g : FanHom Ψ Ω) (hΩ : Ω.IsRegular) :
    (g.comp f).analyticMap hΦ hΩ = f.analyticMap hΦ hΨ ≫ g.analyticMap hΨ hΩ := by
  refine Φ.analyticRealization_hom_ext hΦ fun σ ↦ ?_
  let τ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  let υ : Ω.cones := ⟨g.leastCone τ.2, g.leastCone_mem τ.2⟩
  rw [(g.comp f).analyticAffineChartι_comp_analyticMap hΦ hΩ (σ := σ) (υ := υ)
      (by rw [comp_realMap, LinearMap.coe_comp]
          exact (g.mapsTo_leastCone τ.2).comp (f.mapsTo_leastCone σ.2)),
    f.analyticAffineChartι_comp_analyticMap_assoc hΦ hΨ (υ := τ) (f.mapsTo_leastCone σ.2),
    g.analyticAffineChartι_comp_analyticMap hΨ hΩ (σ := τ) (υ := υ) (g.mapsTo_leastCone τ.2),
    ← Category.assoc]
  -- Pulling back along the composite of the lattice maps is pulling back along each in turn.
  congr 1
  ext x : 1
  rw [TopCat.comp_app, analyticChartMap_apply, analyticChartMap_apply, analyticChartMap_apply]
  refine (congrArg (AffineSemigroupComplexPoint.comap · _) ?_).trans
    (AffineSemigroupComplexPoint.comap_comap _ _ _).symm
  ext m n
  simp

/-- The inclusion of an open subfan induces the open-subfan map of analytic realizations. -/
theorem analyticMap_subfanInclusion (S : Set (PointedCone ℝ V)) (hS : S ⊆ Φ.cones)
    (hface : ∀ ⦃σ τ⦄, σ ∈ S → τ.IsFaceOf σ → τ ∈ S) :
    (Φ.subfanInclusion S hS hface).analyticMap (hΦ.subfan S hS hface) hΦ =
      Φ.subfanAnalyticMap hΦ S hS hface := by
  refine (Φ.subfan S hS hface).analyticRealization_hom_ext (hΦ.subfan S hS hface)
    fun σ ↦ ?_
  rw [Fan.analyticAffineChartι_comp_subfanAnalyticMap,
    (Φ.subfanInclusion S hS hface).analyticAffineChartι_comp_analyticMap _ hΦ
      (υ := ⟨σ.1, hS (by simpa only [Fan.subfan_cones] using σ.2)⟩)
      (by rw [Fan.subfanInclusion_realMap]; exact Set.mapsTo_id _)]
  -- The inclusion of a subfan pulls a complex point back along the identity of its dual
  -- semigroup, which is the chart comparison on points.
  congr 1
  ext x : 1
  rw [analyticChartMap_apply]
  refine (congrArg (AffineSemigroupComplexPoint.comap · _) ?_).trans
    ((congrFun AffineSemigroupComplexPoint.comap_id _).trans
      (Φ.subfanAnalyticChartMap_apply hΦ S hS hface σ x).symm)
  ext m n
  simp

end TauCeti.Toric.FanHom

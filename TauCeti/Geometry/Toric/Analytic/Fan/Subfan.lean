/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData

/-!
# Analytic realizations of open subfans

A face-closed collection of cones in a finite regular fan determines an open subspace of the
fan's analytic realization.  The canonical map is obtained by gluing the identity maps on the
selected affine charts.  It is an open embedding, and its image is precisely the union of those
charts in the ambient realization.

This is the analytic counterpart of the open immersion associated to a subfan of an algebraic
toric variety.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
* The injectivity, range, and open-embedding development adapts the algebraic formalization in
  `TauCeti.Geometry.Toric.Algebraic.Fan.SubfanScheme`.
-/

public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Phi : Fan i) (S : Set (PointedCone ℝ V)) (hS : S ⊆ Phi.cones)
  (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)

/-- The identity map from the affine chart of a subfan cone to the chart of an ambient cone with
the same underlying cone. The ambient cone is generalized so that the identification with
`subfanCone` enters only through `coe_subfanCone`. -/
private noncomputable def subfanAnalyticChartMapAux (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) (c : Phi.cones)
    (hc : (c : PointedCone ℝ V) = sigma) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
      (hPhi.subfan S hS hface)).obj sigma ⟶ (Phi.analyticAffineChartDiagram hPhi).obj c := by
  obtain ⟨c, hcmem⟩ := c
  dsimp only at hc
  subst hc
  rw [analyticAffineChartDiagram_obj, analyticAffineChartDiagram_obj]
  unfold analyticAffineChart
  rw [subfan_lattice Phi S hS hface]
  let gsource := analyticChartGenerators (Phi.subfan S hS hface) sigma
    ((isRegular_iff.mp (hPhi.subfan S hS hface)) sigma.1 sigma.2)
  let gtarget := analyticChartGenerators Phi ⟨sigma.1, hcmem⟩
    ((isRegular_iff.mp hPhi) sigma.1 hcmem)
  let T := AffineSemigroupComplexPoint (dualSemigroup Phi.lattice sigma.1)
  refine @TopCat.ofHom T T (affinePointTopology gsource.2)
    (affinePointTopology gtarget.2)
      (@ContinuousMap.mk T T (affinePointTopology gsource.2)
        (affinePointTopology gtarget.2) id ?_)
  rw [affinePointTopology_eq gsource.2 gtarget.2]
  exact @continuous_id T (affinePointTopology gtarget.2)

private noncomputable def subfanAnalyticChartMapInvAux (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) (c : Phi.cones)
    (hc : (c : PointedCone ℝ V) = sigma) :
    (Phi.analyticAffineChartDiagram hPhi).obj c ⟶
      ((Phi.subfan S hS hface).analyticAffineChartDiagram
        (hPhi.subfan S hS hface)).obj sigma := by
  obtain ⟨c, hcmem⟩ := c
  dsimp only at hc
  subst hc
  rw [analyticAffineChartDiagram_obj, analyticAffineChartDiagram_obj]
  unfold analyticAffineChart
  rw [subfan_lattice Phi S hS hface]
  let gtarget := analyticChartGenerators (Phi.subfan S hS hface) sigma
    ((isRegular_iff.mp (hPhi.subfan S hS hface)) sigma.1 sigma.2)
  let gsource := analyticChartGenerators Phi ⟨sigma.1, hcmem⟩
    ((isRegular_iff.mp hPhi) sigma.1 hcmem)
  let T := AffineSemigroupComplexPoint (dualSemigroup Phi.lattice sigma.1)
  refine @TopCat.ofHom T T (affinePointTopology gsource.2)
    (affinePointTopology gtarget.2)
      (@ContinuousMap.mk T T (affinePointTopology gsource.2)
        (affinePointTopology gtarget.2) id ?_)
  rw [affinePointTopology_eq gsource.2 gtarget.2]
  exact @continuous_id T (affinePointTopology gtarget.2)

private noncomputable def subfanAnalyticChartIsoAux (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) (c : Phi.cones)
    (hc : (c : PointedCone ℝ V) = sigma) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
      (hPhi.subfan S hS hface)).obj sigma ≅ (Phi.analyticAffineChartDiagram hPhi).obj c where
  hom := Phi.subfanAnalyticChartMapAux S hS hface hPhi sigma c hc
  inv := Phi.subfanAnalyticChartMapInvAux S hS hface hPhi sigma c hc
  hom_inv_id := by
    obtain ⟨c, hcmem⟩ := c
    dsimp only at hc
    subst hc
    exact TopCat.ext fun _ ↦ rfl
  inv_hom_id := by
    obtain ⟨c, hcmem⟩ := c
    dsimp only at hc
    subst hc
    exact TopCat.ext fun _ ↦ rfl

/-- The affine chart of a subfan cone maps identically to the corresponding chart of the
ambient fan. -/
noncomputable def subfanAnalyticChartMap (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
      (hPhi.subfan S hS hface)).obj sigma ⟶
      (Phi.analyticAffineChartDiagram hPhi).obj
        (Phi.subfanCone S hS hface sigma) :=
  Phi.subfanAnalyticChartMapAux S hS hface hPhi sigma _ (Phi.coe_subfanCone S hS hface sigma)

/-- The affine chart of a subfan is canonically isomorphic to the corresponding ambient chart. -/
noncomputable def subfanAnalyticChartIso (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
      (hPhi.subfan S hS hface)).obj sigma ≅
      (Phi.analyticAffineChartDiagram hPhi).obj (Phi.subfanCone S hS hface sigma) where
  hom := Phi.subfanAnalyticChartMap S hS hface hPhi sigma
  inv := (Phi.subfanAnalyticChartIsoAux S hS hface hPhi sigma _
    (Phi.coe_subfanCone S hS hface sigma)).inv
  hom_inv_id := (Phi.subfanAnalyticChartIsoAux S hS hface hPhi sigma _
    (Phi.coe_subfanCone S hS hface sigma)).hom_inv_id
  inv_hom_id := (Phi.subfanAnalyticChartIsoAux S hS hface hPhi sigma _
    (Phi.coe_subfanCone S hS hface sigma)).inv_hom_id

/-- The forward map of the chart isomorphism is the chart identification. -/
@[simp]
theorem subfanAnalyticChartIso_hom (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    (Phi.subfanAnalyticChartIso S hS hface hPhi sigma).hom =
      Phi.subfanAnalyticChartMap S hS hface hPhi sigma :=
  (rfl)

/-- The identity map from a subfan chart to its ambient chart is an open embedding. -/
theorem isOpenEmbedding_subfanAnalyticChartMap (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    IsOpenEmbedding (Phi.subfanAnalyticChartMap S hS hface hPhi sigma) :=
  (TopCat.homeoOfIso (Phi.subfanAnalyticChartIso S hS hface hPhi sigma)).isOpenEmbedding

private theorem analyticFaceMap_comp_subfanAnalyticChartMapAux (hPhi : Phi.IsRegular)
    {tau sigma : (Phi.subfan S hS hface).cones} (f : tau ⟶ sigma) (c d : Phi.cones)
    (hc : (c : PointedCone ℝ V) = tau) (hd : (d : PointedCone ℝ V) = sigma) (hcd : c ≤ d) :
    (Phi.subfan S hS hface).analyticFaceMap
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) tau.1 tau.2)
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) sigma.1 sigma.2) f ≫
      Phi.subfanAnalyticChartMapAux S hS hface hPhi sigma d hd =
    Phi.subfanAnalyticChartMapAux S hS hface hPhi tau c hc ≫
      Phi.analyticFaceMap ((isRegular_iff.mp hPhi) c.1 c.2) ((isRegular_iff.mp hPhi) d.1 d.2)
        (homOfLE hcd) := by
  obtain ⟨c, hcmem⟩ := c
  obtain ⟨d, hdmem⟩ := d
  dsimp only at hc hd
  subst hc hd
  apply TopCat.ext
  intro x
  erw [TopCat.comp_app, TopCat.comp_app]
  unfold subfanAnalyticChartMapAux
  erw [analyticFaceMap_apply]
  rw [subfan_lattice Phi S hS hface]
  erw [Phi.analyticFaceMap_apply]
  rfl

/-- The identity maps from subfan charts to ambient charts commute with face maps. -/
@[reassoc]
theorem analyticFaceMap_comp_subfanAnalyticChartMap (hPhi : Phi.IsRegular)
    {tau sigma : (Phi.subfan S hS hface).cones} (f : tau ⟶ sigma) :
    (Phi.subfan S hS hface).analyticFaceMap
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) tau.1 tau.2)
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) sigma.1 sigma.2) f ≫
      Phi.subfanAnalyticChartMap S hS hface hPhi sigma =
    Phi.subfanAnalyticChartMap S hS hface hPhi tau ≫
      Phi.analyticFaceMap
        ((isRegular_iff.mp hPhi) _ (Phi.subfanCone S hS hface tau).2)
        ((isRegular_iff.mp hPhi) _ (Phi.subfanCone S hS hface sigma).2)
        (homOfLE ((Phi.subfanCone_le_subfanCone S hS hface).2 (leOfHom f))) :=
  Phi.analyticFaceMap_comp_subfanAnalyticChartMapAux S hS hface hPhi f _ _ _ _ _

/-- The identity maps from subfan charts to ambient charts form a natural transformation of
affine-chart diagrams. -/
@[reassoc]
theorem analyticAffineChartDiagram_map_comp_subfanAnalyticChartMap (hPhi : Phi.IsRegular)
    {tau sigma : (Phi.subfan S hS hface).cones} (f : tau ⟶ sigma) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
        (hPhi.subfan S hS hface)).map f ≫
      Phi.subfanAnalyticChartMap S hS hface hPhi sigma =
    Phi.subfanAnalyticChartMap S hS hface hPhi tau ≫
      (Phi.analyticAffineChartDiagram hPhi).map
        (homOfLE ((Phi.subfanCone_le_subfanCone S hS hface).2 (leOfHom f))) := by
  rw [(Phi.subfan S hS hface).analyticAffineChartDiagram_map,
    Phi.analyticAffineChartDiagram_map]
  exact Phi.analyticFaceMap_comp_subfanAnalyticChartMap S hS hface hPhi f

/-- A face map in the subfan followed by the corresponding ambient chart inclusion is the
ambient chart inclusion at the smaller cone. -/
@[reassoc]
theorem analyticFaceMap_comp_subfanAnalyticChartMap_comp_analyticAffineChartι
    (hPhi : Phi.IsRegular) {tau sigma : (Phi.subfan S hS hface).cones} (f : tau ⟶ sigma) :
    (Phi.subfan S hS hface).analyticFaceMap
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) tau.1 tau.2)
        ((isRegular_iff.mp (hPhi.subfan S hS hface)) sigma.1 sigma.2) f ≫
      Phi.subfanAnalyticChartMap S hS hface hPhi sigma ≫
      Phi.analyticAffineChartι hPhi
        (Phi.subfanCone S hS hface sigma) =
    Phi.subfanAnalyticChartMap S hS hface hPhi tau ≫
      Phi.analyticAffineChartι hPhi
        (Phi.subfanCone S hS hface tau) := by
  calc
    _ = Phi.subfanAnalyticChartMap S hS hface hPhi tau ≫
        Phi.analyticFaceMap
          ((isRegular_iff.mp hPhi) _ (Phi.subfanCone S hS hface tau).2)
          ((isRegular_iff.mp hPhi) _ (Phi.subfanCone S hS hface sigma).2)
          (homOfLE ((Phi.subfanCone_le_subfanCone S hS hface).2 (leOfHom f))) ≫
        Phi.analyticAffineChartι hPhi (Phi.subfanCone S hS hface sigma) :=
      Phi.analyticFaceMap_comp_subfanAnalyticChartMap_assoc S hS hface hPhi f _
    _ = _ := by
      have h := Phi.analyticFaceMap_comp_analyticAffineChartι hPhi
        (τ := Phi.subfanCone S hS hface tau)
        (σ := Phi.subfanCone S hS hface sigma)
        (homOfLE ((Phi.subfanCone_le_subfanCone S hS hface).2 (leOfHom f)))
      convert congrArg
        (fun g ↦ Phi.subfanAnalyticChartMap S hS hface hPhi tau ≫ g) h using 1
      all_goals rfl

private noncomputable def subfanAnalyticChartCoconeMap (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    ((Phi.subfan S hS hface).analyticAffineChartDiagram
      (hPhi.subfan S hS hface)).obj sigma ⟶ Phi.analyticRealization hPhi :=
  Phi.subfanAnalyticChartMap S hS hface hPhi sigma ≫
    Phi.analyticAffineChartι hPhi
      (Phi.subfanCone S hS hface sigma)

private theorem subfanAnalyticChartCoconeMap_compatible (hPhi : Phi.IsRegular)
    (sigma tau : (Phi.subfan S hS hface).cones) :
    ((Phi.subfan S hS hface).analyticGlueData (hPhi.subfan S hS hface)).f sigma tau ≫
        Phi.subfanAnalyticChartCoconeMap S hS hface hPhi sigma =
      (((Phi.subfan S hS hface).analyticGlueData (hPhi.subfan S hS hface)).t sigma tau ≫
        ((Phi.subfan S hS hface).analyticGlueData (hPhi.subfan S hS hface)).f tau sigma) ≫
        Phi.subfanAnalyticChartCoconeMap S hS hface hPhi tau := by
  let Omega := Phi.subfan S hS hface
  let hOmega := hPhi.subfan S hS hface
  apply TopCat.ext
  intro x
  obtain ⟨z, hz⟩ := (Omega.mem_analyticOverlapOpens hOmega sigma tau x.1).1 x.2
  have hx : x = ⟨Omega.analyticOverlapLeft hOmega sigma tau z,
      Omega.analyticOverlapLeft_mem hOmega sigma tau z⟩ :=
    Subtype.ext hz.symm
  rw [hx]
  -- The gluing-data projections are wrapped in `TopCat.GlueData.mk'`; restate their action on
  -- this represented overlap point before applying the public overlap-transition equation.
  rw [(Phi.subfan S hS hface).analyticGlueData_f (hPhi.subfan S hS hface) sigma tau,
    (Phi.subfan S hS hface).analyticGlueData_t (hPhi.subfan S hS hface) sigma tau,
    (Phi.subfan S hS hface).analyticGlueData_f (hPhi.subfan S hS hface) tau sigma]
  erw [TopCat.comp_app, TopCat.comp_app, TopCat.comp_app, TopCat.comp_app]
  erw [TopCat.comp_app
    ((Phi.subfan S hS hface).analyticOverlapTransition
      (hPhi.subfan S hS hface) sigma tau ≫
        ((Phi.subfan S hS hface).analyticOverlapOpens
          (hPhi.subfan S hS hface) tau sigma).inclusion')
    (Phi.subfanAnalyticChartCoconeMap S hS hface hPhi tau)]
  erw [TopCat.comp_app
    ((Phi.subfan S hS hface).analyticOverlapTransition
      (hPhi.subfan S hS hface) sigma tau)
    ((Phi.subfan S hS hface).analyticOverlapOpens
      (hPhi.subfan S hS hface) tau sigma).inclusion']
  erw [(Phi.subfan S hS hface).analyticOverlapTransition_apply
    (hPhi.subfan S hS hface)]
  change Phi.subfanAnalyticChartCoconeMap S hS hface hPhi sigma
      (Omega.analyticOverlapLeft hOmega sigma tau z) =
    Phi.subfanAnalyticChartCoconeMap S hS hface hPhi tau
      ((Omega.analyticOverlapHomeomorph hOmega sigma tau
        ⟨Omega.analyticOverlapLeft hOmega sigma tau z,
          Omega.analyticOverlapLeft_mem hOmega sigma tau z⟩).1)
  rw [Omega.analyticOverlapHomeomorph_apply]
  have hleft := ConcreteCategory.congr_hom
    (Phi.analyticFaceMap_comp_subfanAnalyticChartMap_comp_analyticAffineChartι
      S hS hface hPhi (homOfLE inf_le_left : sigma ⊓ tau ⟶ sigma)) z
  have hright := ConcreteCategory.congr_hom
    (Phi.analyticFaceMap_comp_subfanAnalyticChartMap_comp_analyticAffineChartι
      S hS hface hPhi (homOfLE inf_le_right : sigma ⊓ tau ⟶ tau)) z
  erw [TopCat.comp_app, TopCat.comp_app] at hleft hright
  unfold subfanAnalyticChartCoconeMap
  erw [TopCat.comp_app, TopCat.comp_app, TopCat.comp_app, TopCat.comp_app]
  erw [TopCat.comp_app
    (Phi.subfanAnalyticChartMap S hS hface hPhi tau)
    (Phi.analyticAffineChartι hPhi (Phi.subfanCone S hS hface tau))]
  have hcoe :
      ((⟨Omega.analyticOverlapRight hOmega sigma tau z,
          Omega.analyticOverlapRight_mem hOmega sigma tau z⟩ :
        Omega.analyticOverlapOpens hOmega tau sigma).1) =
        Omega.analyticOverlapRight hOmega sigma tau z :=
    rfl
  rw [hcoe]
  rw [Omega.analyticOverlapLeft_def, Omega.analyticOverlapRight_def,
    Omega.analyticAffineChartDiagram_map]
  exact hleft.trans hright.symm

/-- The canonical map from the analytic realization of a face-closed subfan to the analytic
realization of the ambient fan. On every selected affine chart it is the identity map followed by
the ambient chart inclusion. -/
noncomputable def subfanAnalyticMap (hPhi : Phi.IsRegular) :
    (Phi.subfan S hS hface).analyticRealization (hPhi.subfan S hS hface) ⟶
      Phi.analyticRealization hPhi :=
  Multicoequalizer.desc _ _
    (Phi.subfanAnalyticChartCoconeMap S hS hface hPhi)
    (by
      rintro ⟨sigma, tau⟩
      exact Phi.subfanAnalyticChartCoconeMap_compatible S hS hface hPhi sigma tau)

/-- On every affine chart, the map of analytic realizations induced by a subfan inclusion is the
identity onto the corresponding ambient chart. -/
@[reassoc (attr := simp)]
theorem analyticAffineChartι_comp_subfanAnalyticMap (hPhi : Phi.IsRegular)
    (sigma : (Phi.subfan S hS hface).cones) :
    (Phi.subfan S hS hface).analyticAffineChartι
        (hPhi.subfan S hS hface) sigma ≫
      Phi.subfanAnalyticMap S hS hface hPhi =
    Phi.subfanAnalyticChartMap S hS hface hPhi sigma ≫
      Phi.analyticAffineChartι hPhi (Phi.subfanCone S hS hface sigma) := by
  rw [analyticAffineChartι_def]
  apply Multicoequalizer.π_desc

/-- A subfan face map, applied to a point pulled back along a chart identification, is carried by
the chart identification to the corresponding ambient face map. -/
private theorem subfanAnalyticChartMap_map_inv_apply (hPhi : Phi.IsRegular)
    {tau sigma : (Phi.subfan S hS hface).cones} (f : tau ⟶ sigma) (c : Phi.cones)
    (hc : (c : PointedCone ℝ V) = tau) (hcs : c ≤ Phi.subfanCone S hS hface sigma)
    (z : (Phi.analyticAffineChartDiagram hPhi).obj c) :
    Phi.subfanAnalyticChartMap S hS hface hPhi sigma
        (((Phi.subfan S hS hface).analyticAffineChartDiagram (hPhi.subfan S hS hface)).map f
          ((Phi.subfanAnalyticChartIsoAux S hS hface hPhi tau c hc).inv z)) =
      (Phi.analyticAffineChartDiagram hPhi).map (homOfLE hcs) z := by
  have hnat := ConcreteCategory.congr_hom
    (Phi.analyticFaceMap_comp_subfanAnalyticChartMapAux S hS hface hPhi f c _ hc
      (Phi.coe_subfanCone S hS hface sigma) hcs)
    ((Phi.subfanAnalyticChartIsoAux S hS hface hPhi tau c hc).inv z)
  rw [(Phi.subfan S hS hface).analyticAffineChartDiagram_map, Phi.analyticAffineChartDiagram_map]
  exact hnat.trans (congrArg _
    (TopCat.inv_hom_id_apply (Phi.subfanAnalyticChartIsoAux S hS hface hPhi tau c hc) z))

/-- The analytic realization map induced by a subfan inclusion is injective. -/
theorem subfanAnalyticMap_injective (hPhi : Phi.IsRegular) :
    Function.Injective (Phi.subfanAnalyticMap S hS hface hPhi) := by
  intro x y hxy
  obtain ⟨sigma, a, rfl⟩ :=
    (Phi.subfan S hS hface).exists_analyticAffineChartι_apply_eq
      (hPhi.subfan S hS hface) x
  obtain ⟨tau, b, rfl⟩ :=
    (Phi.subfan S hS hface).exists_analyticAffineChartι_apply_eq
      (hPhi.subfan S hS hface) y
  rw [← TopCat.comp_app, ← TopCat.comp_app,
    Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface,
    Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface,
    TopCat.comp_app, TopCat.comp_app] at hxy
  apply ((Phi.subfan S hS hface).analyticAffineChartι_eq_analyticAffineChartι_iff
    (hPhi.subfan S hS hface) a b).2
  obtain ⟨z, hza, hzb⟩ :=
    (Phi.analyticAffineChartι_eq_analyticAffineChartι_iff hPhi
      (σ := Phi.subfanCone S hS hface sigma)
      (τ := Phi.subfanCone S hS hface tau)
      (Phi.subfanAnalyticChartMap S hS hface hPhi sigma a)
      (Phi.subfanAnalyticChartMap S hS hface hPhi tau b)).1 hxy
  have hc : ((Phi.subfanCone S hS hface sigma ⊓ Phi.subfanCone S hS hface tau : Phi.cones) :
      PointedCone ℝ V) = (sigma ⊓ tau : (Phi.subfan S hS hface).cones) := by
    rw [← subfanCone_inf, coe_subfanCone]
  refine ⟨(Phi.subfanAnalyticChartIsoAux S hS hface hPhi (sigma ⊓ tau) _ hc).inv z, ?_, ?_⟩
  · apply (Phi.isOpenEmbedding_subfanAnalyticChartMap S hS hface hPhi sigma).injective
    rw [analyticOverlapLeft_def] at hza ⊢
    exact (Phi.subfanAnalyticChartMap_map_inv_apply S hS hface hPhi
      (homOfLE inf_le_left : sigma ⊓ tau ⟶ sigma) _ hc inf_le_left z).trans hza
  · apply (Phi.isOpenEmbedding_subfanAnalyticChartMap S hS hface hPhi tau).injective
    rw [analyticOverlapRight_def] at hzb ⊢
    exact (Phi.subfanAnalyticChartMap_map_inv_apply S hS hface hPhi
      (homOfLE inf_le_right : sigma ⊓ tau ⟶ tau) _ hc inf_le_right z).trans hzb

/-- The image of a subfan's analytic realization is the union of its affine charts in the
ambient analytic realization. -/
theorem range_subfanAnalyticMap (hPhi : Phi.IsRegular) :
    Set.range (Phi.subfanAnalyticMap S hS hface hPhi) =
      ⋃ sigma : (Phi.subfan S hS hface).cones,
        Set.range (Phi.analyticAffineChartι hPhi
          (Phi.subfanCone S hS hface sigma)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨sigma, z, rfl⟩ :=
      (Phi.subfan S hS hface).exists_analyticAffineChartι_apply_eq
        (hPhi.subfan S hS hface) y
    refine Set.mem_iUnion.mpr ⟨sigma,
      ⟨Phi.subfanAnalyticChartMap S hS hface hPhi sigma z, ?_⟩⟩
    simpa only [TopCat.comp_app] using
      (ConcreteCategory.congr_hom
        (Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface hPhi sigma) z).symm
  · intro hx
    obtain ⟨sigma, z, rfl⟩ := Set.mem_iUnion.mp hx
    let w := (Phi.subfanAnalyticChartIso S hS hface hPhi sigma).inv z
    refine ⟨(Phi.subfan S hS hface).analyticAffineChartι
      (hPhi.subfan S hS hface) sigma w, ?_⟩
    calc
      _ = Phi.analyticAffineChartι hPhi (Phi.subfanCone S hS hface sigma)
          (Phi.subfanAnalyticChartMap S hS hface hPhi sigma w) := by
        simpa only [TopCat.comp_app] using ConcreteCategory.congr_hom
          (Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface hPhi sigma) w
      _ = _ := congrArg (Phi.analyticAffineChartι hPhi
        (Phi.subfanCone S hS hface sigma))
          (TopCat.inv_hom_id_apply
            (Phi.subfanAnalyticChartIso S hS hface hPhi sigma) z)

/-- The analytic realization map induced by a face-closed subfan is open onto the ambient
analytic realization. -/
theorem isOpenMap_subfanAnalyticMap (hPhi : Phi.IsRegular) :
    IsOpenMap (Phi.subfanAnalyticMap S hS hface hPhi) := by
  intro s hs
  let Omega := Phi.subfan S hS hface
  let hOmega := hPhi.subfan S hS hface
  have himage :
      Phi.subfanAnalyticMap S hS hface hPhi '' s =
        ⋃ sigma : Omega.cones,
          Phi.analyticAffineChartι hPhi (Phi.subfanCone S hS hface sigma) ''
            (Phi.subfanAnalyticChartMap S hS hface hPhi sigma ''
              (Omega.analyticAffineChartι hOmega sigma ⁻¹' s)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨sigma, z, rfl⟩ := Omega.exists_analyticAffineChartι_apply_eq hOmega y
      refine Set.mem_iUnion.mpr ⟨sigma,
        ⟨Phi.subfanAnalyticChartMap S hS hface hPhi sigma z,
          ⟨z, hy, rfl⟩, ?_⟩⟩
      simpa only [TopCat.comp_app] using
        (ConcreteCategory.congr_hom
          (Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface hPhi sigma) z).symm
    · intro hx
      obtain ⟨sigma, z, ⟨w, hw, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨Omega.analyticAffineChartι hOmega sigma w, hw, ?_⟩
      simpa only [TopCat.comp_app] using
        ConcreteCategory.congr_hom
          (Phi.analyticAffineChartι_comp_subfanAnalyticMap S hS hface hPhi sigma) w
  rw [himage]
  apply isOpen_iUnion
  intro sigma
  apply (Phi.isOpenEmbedding_analyticAffineChartι hPhi
    (Phi.subfanCone S hS hface sigma)).isOpenMap
  apply (Phi.isOpenEmbedding_subfanAnalyticChartMap S hS hface hPhi sigma).isOpenMap
  exact hs.preimage (Omega.analyticAffineChartι hOmega sigma).hom.continuous

/-- A face-closed subfan embeds as the open union of its affine charts in the ambient analytic
realization. -/
theorem isOpenEmbedding_subfanAnalyticMap (hPhi : Phi.IsRegular) :
    IsOpenEmbedding (Phi.subfanAnalyticMap S hS hface hPhi) :=
  .of_continuous_injective_isOpenMap
    (Phi.subfanAnalyticMap S hS hface hPhi).hom.continuous
    (Phi.subfanAnalyticMap_injective S hS hface hPhi)
    (Phi.isOpenMap_subfanAnalyticMap S hS hface hPhi)

end TauCeti.Toric.Fan

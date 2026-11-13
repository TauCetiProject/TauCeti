/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Dolbeault
public import TauCeti.Topology.Sheaves.Cech.DegreeOne
public import TauCeti.Topology.Sheaves.Cech.Functoriality

/-!
# Coordinate discs are acyclic for the holomorphic structure sheaf

On a Riemann surface `X`, the sheaf cohomology `H¹(W, 𝒪)` of the holomorphic structure sheaf
vanishes on every coordinate disc `W`, the inverse image `e.source ∩ e ⁻¹' D` of a disc
`D ⊆ e.target` under a holomorphic chart `e`. Such discs form a neighbourhood basis of every point,
so on a compact Riemann surface every open cover is refined by a finite cover by opens `U i` with
`H¹(U i, 𝒪) = 0`. These are the covers to which the degree one Leray comparison applies
(`TauCeti.Topology.homologyCechComplexIsoHOne`): the first Čech cohomology of such a cover is
`H¹(X, 𝒪)`, and the refinement maps between two such covers are isomorphisms in degree one
(`TauCeti.Topology.isIso_homologyMap_cechComplexMap_one`).

The vanishing on plane discs,
`TauCeti.isZero_cechCohomology_one_holomorphicStructureSheafModules_eball`, is proved from the
Dolbeault lemma for the cover-colimit Čech cohomology with complex vector space
coefficients. It is carried to a coordinate disc by the general fact that the vanishing of
Čech `H¹(Y, 𝒪)` is invariant under biholomorphisms (precomposition with a biholomorphism `W ≃ₜ Y`
identifies the structure sheaf of `Y` with the pushforward of that of `W`, and Čech cohomology
transports along homeomorphisms by `TopCat.Hom.epi_cechCohomologyPullback`), and then passed to
sheaf cohomology by `CategoryTheory.Sheaf.subsingleton_H'_one_of_isZero_cechCohomology_moduleCat`.

## Main results

* `Homeomorph.subsingleton_H'_one_holomorphicStructureSheafModules_of_homeomorph`: an open `W` of a
  complex manifold biholomorphic to a complex manifold `Y` with Čech `H¹(Y, 𝒪) = 0` has
  `H¹(W, 𝒪) = 0`.
* `TauCeti.subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball`: `H¹(W, 𝒪) = 0` for a
  coordinate disc `W` of a Riemann surface.
* `TauCeti.exists_mem_subset_subsingleton_H'_one_holomorphicStructureSheafModules`: such opens form
  a neighbourhood basis of every point.
* `TauCeti.exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules`: on a compact
  Riemann surface, every open cover is refined by a finite cover by such opens.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §12 (Leray's theorem for covers with vanishing `H¹` on their members) and Theorem 13.4
  (`H¹(X, 𝒪) = 0` for discs).
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti

section Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]
  {W : Opens (TopCat.of X)} (φ : W ≃ₜ Y)

namespace holomorphicStructureSheafModules

/-- The homeomorphism `φ` as a morphism of topological spaces. -/
private abbrev homeoHom : (Opens.toTopCat (TopCat.of X)).obj W ⟶ TopCat.of Y :=
  TopCat.ofHom ⟨φ, φ.continuous⟩

/-- The image in `X` of the inverse image under `φ` of an open subset `V` of `Y`. -/
private abbrev preimageOpens (V : Opens Y) : Opens (TopCat.of X) :=
  W.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map (homeoHom φ)).obj V)

private lemma preimageOpens_le (V : Opens Y) : preimageOpens φ V ≤ W := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

/-- A point of `preimageOpens φ V` is sent by `φ` into `V`. -/
private def toOpens {V : Opens Y} (x : preimageOpens φ V) : V :=
  ⟨φ (Opens.inclusion (preimageOpens_le φ V) x), by
    obtain ⟨a, ha, h⟩ := x.2
    have hx : Opens.inclusion (preimageOpens_le φ V) x = a := Subtype.ext h.symm
    rwa [hx]⟩

/-- A point of `V` is sent by `φ.symm` into `preimageOpens φ V`. -/
private def ofOpens {V : Opens Y} (y : V) : preimageOpens φ V :=
  ⟨(φ.symm y).1, φ.symm y, ((φ.apply_symm_apply y).symm ▸ y.2 : φ (φ.symm y) ∈ V), rfl⟩

private lemma toOpens_ofOpens {V : Opens Y} (y : V) : toOpens φ (ofOpens φ y) = y :=
  Subtype.ext (by simp [toOpens, ofOpens, Opens.inclusion])

private lemma ofOpens_toOpens {V : Opens Y} (x : preimageOpens φ V) :
    ofOpens φ (toOpens φ x) = x :=
  Subtype.ext (by simp [toOpens, ofOpens, Opens.inclusion])

variable {φ}

private lemma contMDiff_toOpens (hφ : ContMDiff I J ω φ) (V : Opens Y) :
    ContMDiff I J ω (toOpens φ (V := V)) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact hφ.comp (contMDiff_inclusion (preimageOpens_le φ V))

private lemma contMDiff_ofOpens (hφ' : ContMDiff J I ω φ.symm) (V : Opens Y) :
    ContMDiff J I ω (ofOpens φ (V := V)) := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact (contMDiff_subtype_val.comp (hφ'.comp contMDiff_subtype_val) :
    ContMDiff J I ω fun y : V ↦ (φ.symm y : X))

variable (hφ : ContMDiff I J ω φ) (hφ' : ContMDiff J I ω φ.symm)

/-- Precomposition with `φ` identifies the holomorphic functions on an open subset `V` of `Y` with
the holomorphic functions on its inverse image. -/
private def sectionsEquiv (V : Opens Y) :
    (holomorphicStructureSheafModules J Y).obj.obj (op V) ≃ₗ[ℂ]
      (holomorphicStructureSheafModules I X).obj.obj (op (preimageOpens φ V)) where
  toFun g := ofContMDiff (fun x ↦ g (toOpens φ x)) ((contMDiff g).comp (contMDiff_toOpens hφ V))
  invFun g :=
    ofContMDiff (fun y ↦ g (ofOpens φ y)) ((contMDiff g).comp (contMDiff_ofOpens hφ' V))
  map_add' g g' := by ext; simp
  map_smul' c g := by ext; simp
  left_inv g := by ext; simp [toOpens_ofOpens]
  right_inv g := by ext; simp [ofOpens_toOpens]

private lemma sectionsEquiv_apply (V : Opens Y)
    (g : (holomorphicStructureSheafModules J Y).obj.obj (op V)) (x : preimageOpens φ V) :
    sectionsEquiv hφ hφ' V g x = g (toOpens φ x) :=
  ofContMDiff_apply _ _ x

/-- The holomorphic structure sheaf of `Y` is the pushforward along `φ` of the restriction to `W`
of the holomorphic structure sheaf of `X`. -/
private def pushforwardIso : (holomorphicStructureSheafModules J Y).obj ≅
    (TopCat.Presheaf.pushforward (ModuleCat ℂ) (homeoHom φ)).obj
      (W.isOpenEmbedding.isOpenMap.functor.op ⋙ (holomorphicStructureSheafModules I X).obj) :=
  NatIso.ofComponents (fun V ↦ (sectionsEquiv hφ hφ' V.unop).toModuleIso) fun _ ↦ by
    ext g : 2
    apply holomorphicStructureSheafModules.ext
    intro x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
      ModuleCat.hom_ofHom, LinearEquiv.coe_coe, TopCat.Presheaf.pushforward_obj_map,
      Functor.comp_map, Functor.op_map]
    -- both sides evaluate `g` at the image of `x` under `φ`
    exact (sectionsEquiv_apply hφ hφ' _ _ x).trans <| (map_apply J Y _ g _).trans <|
      (congrArg g (Subtype.ext rfl)).trans <|
        (sectionsEquiv_apply hφ hφ' _ g _).symm.trans (map_apply I X _ _ x).symm

end holomorphicStructureSheafModules

open holomorphicStructureSheafModules in
/-- **Vanishing of `H¹(𝒪)` transports along biholomorphisms.** Let `W` be an open subset of a
complex manifold `X` and `φ : W ≃ₜ Y` a homeomorphism onto a complex manifold `Y`, holomorphic
with holomorphic inverse. If the structure sheaf of `Y` has vanishing degree one Čech cohomology,
then the sheaf cohomology `H¹(W, 𝒪)` of the structure sheaf of `X` vanishes. -/
theorem _root_.Homeomorph.subsingleton_H'_one_holomorphicStructureSheafModules_of_homeomorph
    (hφ : ContMDiff I J ω φ) (hφ' : ContMDiff J I ω φ.symm)
    (h : IsZero ((Topology.cechCohomology (TopCat.of Y) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules J Y).obj)) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules I X)) 1 W) :=
  have := TopCat.Hom.epi_cechCohomologyPullback (homeoHom φ) 1 (pushforwardIso hφ hφ').hom
    φ.isInducing φ.surjective
  Sheaf.subsingleton_H'_one_of_isZero_cechCohomology_moduleCat _ W
    (h.of_epi (TopCat.Hom.cechCohomologyPullback (homeoHom φ) 1 (pushforwardIso hφ hφ').hom))

end Homeomorph

section Chart

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

/-- **Coordinate discs are acyclic.** On a Riemann surface `X`, let `e` be a holomorphic chart and
`D = eball c R`, `R ≤ ∞`, a disc contained in its target. Then the coordinate disc
`e.source ∩ e ⁻¹' D`, biholomorphic to `D` through `e`, has `H¹(e.source ∩ e ⁻¹' D, 𝒪) = 0`. -/
theorem subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X) {c : ℂ}
    {R : ENNReal} (hR : Metric.eball c R ⊆ e.target) :
    Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X)) 1
      ⟨e.source ∩ e ⁻¹' Metric.eball c R, e.isOpen_inter_preimage Metric.isOpen_eball⟩) := by
  let D : Opens ℂ := ⟨Metric.eball c R, Metric.isOpen_eball⟩
  have hD : e '' (e.source ∩ e ⁻¹' D) = D := by
    rw [Set.image_inter_preimage, e.image_source_eq_target]
    exact Set.inter_eq_right.2 hR
  let φ := e.homeomorphOfImageSubsetSource Set.inter_subset_left hD
  have he₁ : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source :=
    ((contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero).contMDiffOn e.open_source
  have he₂ : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target :=
    ((contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero).contMDiffOn
      e.open_target
  refine φ.subsingleton_H'_one_holomorphicStructureSheafModules_of_homeomorph (Y := D) ?_ ?_
    (isZero_cechCohomology_one_holomorphicStructureSheafModules_eball c R)
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact he₁.comp_contMDiff contMDiff_subtype_val fun x ↦ x.2.1
  · rw [← ContMDiff.subtypeVal_comp_iff]
    exact he₂.comp_contMDiff contMDiff_subtype_val fun y ↦ hR y.2

/-- **Acyclic neighbourhoods.** Every neighbourhood of a point `x` of a Riemann surface contains an
open neighbourhood `W` of `x` with `H¹(W, 𝒪) = 0`, namely a coordinate disc centred at `x`. -/
theorem exists_mem_subset_subsingleton_H'_one_holomorphicStructureSheafModules (x : X)
    {N : Set X} (hN : N ∈ 𝓝 x) :
    ∃ W : Opens (TopCat.of X), x ∈ W ∧ (W : Set X) ⊆ N ∧
      Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
        (holomorphicStructureSheafModules 𝓘(ℂ) X)) 1 W) := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hT : e '' (e.source ∩ N) ∈ 𝓝 (e x) :=
    e.image_mem_nhds hx (Filter.inter_mem (e.open_source.mem_nhds hx) hN)
  obtain ⟨R, hR, hRT⟩ := EMetric.mem_nhds_iff.1 hT
  have hRe : Metric.eball (e x) R ⊆ e.target :=
    hRT.trans ((Set.image_mono Set.inter_subset_left).trans e.image_source_eq_target.subset)
  refine ⟨⟨e.source ∩ e ⁻¹' Metric.eball (e x) R, e.isOpen_inter_preimage Metric.isOpen_eball⟩,
    ⟨hx, Metric.mem_eball_self hR⟩, ?_,
    subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
      (IsManifold.chart_mem_maximalAtlas x) hRe⟩
  rintro y ⟨hy, hyR⟩
  obtain ⟨z, ⟨hz, hzN⟩, hzy⟩ := hRT hyR
  rwa [← e.injOn hz hy hzy]

/-- **Finite acyclic covers.** On a compact Riemann surface, every open cover `V` is refined by a
finite open cover `U` whose members have `H¹(U i, 𝒪) = 0`. Such a cover computes `H¹(X, 𝒪)` by the
degree one Leray comparison `TauCeti.Topology.homologyCechComplexIsoHOne`. -/
theorem exists_finite_cover_subsingleton_H'_one_holomorphicStructureSheafModules
    [CompactSpace X] {κ : Type*} (V : κ → Opens (TopCat.of X)) (hV : IsOpenCover V) :
    ∃ (ι : Type) (_ : Finite ι) (U : ι → Opens (TopCat.of X)), ⨆ i, U i = ⊤ ∧
      (∀ i, ∃ k, U i ≤ V k) ∧ ∀ i,
        Subsingleton (Sheaf.H' ((sheafCompose _ (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
          (holomorphicStructureSheafModules 𝓘(ℂ) X)) 1 (U i)) := by
  choose k hk using hV.exists_mem
  choose W hxW hWV hW using fun x ↦
    exists_mem_subset_subsingleton_H'_one_holomorphicStructureSheafModules x
      ((V (k x)).isOpen.mem_nhds (hk x))
  have hWc : IsOpenCover W := .mk <| eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨s, hs⟩ := hWc.exists_finite_of_compactSpace
  exact ⟨s, inferInstance, fun i ↦ W i.1, hs.iSup_eq_top, fun i ↦ ⟨k i.1, hWV i.1⟩,
    fun i ↦ hW i.1⟩

end Chart

end TauCeti

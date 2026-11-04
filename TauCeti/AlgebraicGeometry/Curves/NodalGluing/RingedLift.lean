/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.HolomorphicLift
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.IntrinsicNodes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Connected
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Lifting ringed isomorphisms of nodal curves

An analytic isomorphism of normalizations respecting the flag pairs descends to an isomorphism
of the holomorphic sheafed spaces of the glued curves (`Iso.sheafedSpaceIso`). This file proves
the converse: an isomorphism of these sheafed spaces whose section maps fix the constants comes
from a unique analytic nodal isomorphism. Descent and lifting are mutually inverse, so actual
nodal isomorphisms are exactly the `ℂ`-linear isomorphisms of the ringed glued curves.
The section maps of such an isomorphism are evaluation at image points
(`quotientSheafSectionsEquiv_app_apply`, in the ringed descent file).

* `Iso.ofSheafedSpaceIso` constructs the nodal isomorphism. Nodes are preserved because they are
  recognized by their stalks (`mem_nodeSet_iff_of_isIso_stalkMap`), so the underlying
  homeomorphism lifts to the normalizations (`liftHomeomorph`). A chart coordinate at an image
  point off the flags is a section downstairs, and its pullback is the chart written after the
  lift, so the lift is holomorphic off the flags; `Iso.ofHolomorphicLift` removes the flag
  singularities.
* `Iso.sheafedSpaceIso_ofSheafedSpaceIso` and `Iso.ofSheafedSpaceIso_sheafedSpaceIso`: descent
  and lifting are mutually inverse, including on the maps of sections.
* `existsUnique_iso_sheafedSpaceIso_eq_iff`: an isomorphism of the sheafed spaces is induced by a
  unique nodal isomorphism exactly when its section maps fix the constants.

The constants hypothesis cannot be dropped. The sheaves are sheaves of commutative rings, and
composing with complex conjugation turns an antiholomorphic identification of two curves into an
isomorphism of their sheafed spaces which fixes only the real constants.

No compactness, connectedness or finiteness of the set of components is assumed. Self-nodes and
interchanges of the two branches of a node are allowed.

## References

* Hans Grauert and Reinhold Remmert, *Coherent Analytic Sheaves* (Grundlehren der
  mathematischen Wissenschaften 265, Springer, 1984), Chapter 1, §1, for `ℂ`-ringed spaces and
  the values of pulled-back sections.
* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for normalization and actual nodal isomorphisms.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Set Topology
open scoped Manifold ContDiff

namespace TauCeti.NodalGluing

open holomorphicStructureSheaf

variable {ι Flag : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace ℂ (X i)] [∀ i, IsManifold 𝓘(ℂ) 1 (X i)]
  [∀ i, T2Space (X i)] [Finite Flag] {d : FlagPairData ι Flag X}
  {ι' Flag' : Type} {X' : ι' → Type} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace ℂ (X' i)] [∀ i, IsManifold 𝓘(ℂ) 1 (X' i)]
  [∀ i, T2Space (X' i)] [Finite Flag'] {d' : FlagPairData ι' Flag' X'}

/-- The homeomorphism of glued curves underlying an isomorphism of nodal sheafed spaces. -/
private def baseHomeomorph (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d') :
    GluedCurve d ≃ₜ GluedCurve d' :=
  TopCat.homeoOfIso ((SheafedSpace.forget CommRingCat).mapIso φ)

omit [∀ i, IsManifold 𝓘(ℂ) 1 (X i)] [∀ i, T2Space (X i)] [Finite Flag]
  [∀ i, IsManifold 𝓘(ℂ) 1 (X' i)] [∀ i, T2Space (X' i)] [Finite Flag'] in
private theorem baseHomeomorph_apply (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d')
    (z : GluedCurve d) : baseHomeomorph φ z = φ.hom.hom.base z := (rfl)

/-- An isomorphism of nodal sheafed spaces maps nodes exactly to nodes. -/
private theorem baseHomeomorph_mem_nodeSet_iff (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d')
    (z : GluedCurve d) : baseHomeomorph φ z ∈ nodeSet d' ↔ z ∈ nodeSet d :=
  mem_nodeSet_iff_of_isIso_stalkMap d φ.hom z

omit [∀ i, IsManifold 𝓘(ℂ) 1 (X i)] [∀ i, T2Space (X i)] in
/-- Flag points of a complex curve have small neighbourhoods with connected punctures. -/
private theorem exists_mem_nhds_isConnected (x : Σ i, X i) (U : Set (Σ i, X i)) (hU : U ∈ 𝓝 x) :
    ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}) :=
  exists_mem_nhds_subset_isConnected_sdiff_singleton (E := ℂ)
    (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) x hU

/-- Near a point off the flags, the chart coordinate is a section of the nodal structure sheaf:
the chart source minus the flags is an open set on which the quotient map is injective. -/
private theorem exists_chartAt_section {y : Σ i, X i} (hy : y ∉ flagPointSet d) :
    ∃ (U : Opens (GluedCurve d)) (g : (sheafedSpace 𝓘(ℂ) d).presheaf.obj (op U)),
      Quotient.mk _ y ∈ U ∧ ∀ (p : Σ i, X i) (hp : Quotient.mk (gluedRelSetoid d) p ∈ U),
        (quotientSheafSectionsEquiv 𝓘(ℂ) _ U g).1 ⟨p, hp⟩ = chartAt ℂ y p := by
  set S : Set (Σ i, X i) := (chartAt ℂ y).source ∩ (flagPointSet d)ᶜ
  have hSopen : IsOpen S :=
    (chartAt ℂ y).open_source.inter (flagPointSet_finite d).isClosed.isOpen_compl
  -- No point of `S` is identified with another point, so `S` is saturated.
  have hsat : Quotient.mk (gluedRelSetoid d) ⁻¹' (Quotient.mk _ '' S) = S := by
    refine Set.Subset.antisymm ?_ (Set.subset_preimage_image _ _)
    rintro p ⟨q, hq, hqp⟩
    rwa [← eq_of_mk_eq_of_notMem_flagPointSet hq.2 hqp]
  rw [← hsat] at hSopen
  let U : Opens (GluedCurve d) :=
    ⟨Quotient.mk _ '' S, isQuotientMap_quotient_mk'.isOpen_preimage.mp hSopen⟩
  have hmemU (p : Σ i, X i) : Quotient.mk _ p ∈ U ↔ p ∈ S := by
    rw [← SetLike.mem_coe, Opens.coe_mk, ← Set.mem_preimage, hsat]
  let χ : (holomorphicStructureSheaf 𝓘(ℂ) (Σ i, X i)).obj.obj
      (op ((Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj U)) :=
    ofMDifferentiable (fun p ↦ chartAt ℂ y p.1) fun p ↦
      ((mdifferentiableAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)
        ((hmemU p.1).mp p.2).1).comp p
        (contMDiff_subtype_val (n := 1).mdifferentiable one_ne_zero p))
  have hχ : χ ∈ quotientSectionSubring 𝓘(ℂ) (gluedRelSetoid d) U := by
    rw [quotientSectionSubring_eq_top_of_injOn]
    · trivial
    · intro p hp q _ hpq
      exact eq_of_mk_eq_of_notMem_flagPointSet ((hmemU p).mp hp).2 hpq
  refine ⟨U, (quotientSheafSectionsEquiv 𝓘(ℂ) _ U).symm ⟨χ, hχ⟩,
    (hmemU y).mpr ⟨mem_chart_source ℂ y, hy⟩, fun p hp ↦ ?_⟩
  rw [RingEquiv.apply_symm_apply]
  exact ofMDifferentiable_apply (fun p : (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj U ↦
    chartAt ℂ y p.1) _ ⟨p, hp⟩

/-- The normalization lift of an isomorphism of nodal sheafed spaces fixing the constants is
holomorphic away from the flag points: a chart coordinate at the image point is a section of
the target sheaf, and its pullback is the chart written after the lift. -/
private theorem mdifferentiableOn_liftHomeomorph (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d')
    (hφ : ∀ (U : Opens (GluedCurve d')) (c : ℂ),
      (φ.hom.hom.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((sheafedSpace 𝓘(ℂ) d).presheaf.obj
          (op ((Opens.map φ.hom.hom.base).obj U))) c) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (liftHomeomorph (baseHomeomorph φ)
      (baseHomeomorph_mem_nodeSet_iff φ) (fun x _ ↦ exists_mem_nhds_isConnected x)
      (fun x _ ↦ exists_mem_nhds_isConnected x)) (flagPointSet d)ᶜ := by
  set L := liftHomeomorph (baseHomeomorph φ) (baseHomeomorph_mem_nodeSet_iff φ)
    (fun x _ ↦ exists_mem_nhds_isConnected x) (fun x _ ↦ exists_mem_nhds_isConnected x)
  have hL (p : Σ i, X i) : Quotient.mk (gluedRelSetoid d') (L p) =
      φ.hom.hom.base (Quotient.mk (gluedRelSetoid d) p) := mk_liftHomeomorph p
  intro x hx
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  obtain ⟨U, g, hyU, hg⟩ := exists_chartAt_section (d := d')
    ((liftHomeomorph_mem_flagPointSet_iff x).not.mpr hx)
  -- The pullback of the chart coordinate is the chart written after the lift.
  have hxU : x ∈ (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj
      ((Opens.map φ.hom.hom.base).obj U) := by
    rw [Opens.mem_map, Opens.mem_map, TopCat.quotientMk_apply, ← hL]
    exact hyU
  have hdiff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun p : (Opens.map (TopCat.quotientMk
      (gluedRelSetoid d))).obj ((Opens.map φ.hom.hom.base).obj U) ↦ chartAt ℂ (L x) (L p.1))
      ⟨x, hxU⟩ :=
    (holomorphicStructureSheaf.contMDiff _).contMDiffAt.congr_of_eventuallyEq
      (.of_forall fun p ↦ ((quotientSheafSectionsEquiv_app_apply φ.hom hφ U g p (L p.1)
        (hL p.1)).trans (hg _ _)).symm)
  rw [mdifferentiableAt_iff_target, extChartAt_coe, modelWithCornersSelf_coe]
  exact ⟨L.continuous.continuousAt,
    ((contMDiffAt_subtype_iff (x := ⟨x, hxU⟩)).mp hdiff).mdifferentiableAt (by simp)⟩

namespace Iso

/-- **Lifting ringed isomorphisms of nodal curves.** An isomorphism of the holomorphic sheafed
spaces of two nodal curves whose section maps fix the constants is induced by an analytic
isomorphism of the normalizations respecting the flag pairs
(`sheafedSpaceIso_ofSheafedSpaceIso`). -/
def ofSheafedSpaceIso (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d')
    (hφ : ∀ (U : Opens (GluedCurve d')) (c : ℂ),
      (φ.hom.hom.c.app (op U)).hom (algebraMap ℂ _ c) =
        algebraMap ℂ ((sheafedSpace 𝓘(ℂ) d).presheaf.obj
          (op ((Opens.map φ.hom.hom.base).obj U))) c) : Iso 𝓘(ℂ) ω d d' :=
  ofHolomorphicLift (mdifferentiableOn_liftHomeomorph φ hφ)

variable {φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d'}
  {hφ : ∀ (U : Opens (GluedCurve d')) (c : ℂ),
    (φ.hom.hom.c.app (op U)).hom (algebraMap ℂ _ c) =
      algebraMap ℂ ((sheafedSpace 𝓘(ℂ) d).presheaf.obj
        (op ((Opens.map φ.hom.hom.base).obj U))) c}

/-- The lifted isomorphism covers the map of glued curves underlying `φ`. -/
@[simp]
theorem mk_ofSheafedSpaceIso (x : Σ i, X i) :
    Quotient.mk (gluedRelSetoid d') (ofSheafedSpaceIso φ hφ x) =
      φ.hom.hom.base (Quotient.mk (gluedRelSetoid d) x) := by
  rw [ofSheafedSpaceIso, coe_ofHolomorphicLift, mk_liftHomeomorph, baseHomeomorph_apply]

/-- The lifted isomorphism descends to the map of glued curves underlying `φ`. -/
@[simp]
theorem gluedCurveHomeomorph_ofSheafedSpaceIso (z : GluedCurve d) :
    (ofSheafedSpaceIso φ hφ).gluedCurveHomeomorph z = φ.hom.hom.base z := by
  rw [ofSheafedSpaceIso, gluedCurveHomeomorph_ofHolomorphicLift, baseHomeomorph_apply]

/-- **Descent undoes lifting.** The lifted isomorphism induces the forward map of `φ`,
including its maps on holomorphic sections. -/
@[simp]
theorem sheafedSpaceHom_ofSheafedSpaceIso :
    (ofSheafedSpaceIso φ hφ).sheafedSpaceHom = φ.hom := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext_of_app (TopCat.ext fun z ↦ ?_) fun U ↦ ?_
  · rw [sheafedSpaceHom_hom_base_apply]
    exact gluedCurveHomeomorph_ofSheafedSpaceIso (φ := φ) (hφ := hφ) z
  · apply sheafedSpace_sectionMap_ext
    intro g x
    refine ((sheafedSpace_map_apply 𝓘(ℂ) d _ _ x).trans
      (pullbackSection_apply _ U g _)).trans ?_
    rw [quotientSheafSectionsEquiv_app_apply φ.hom hφ U g x _
      (mk_ofSheafedSpaceIso (φ := φ) (hφ := hφ) x.1)]

/-- **Descent undoes lifting.** The lifted isomorphism induces `φ` itself. -/
@[simp]
theorem sheafedSpaceIso_ofSheafedSpaceIso :
    (ofSheafedSpaceIso φ hφ).sheafedSpaceIso = φ :=
  CategoryTheory.Iso.ext ((sheafedSpaceIso_hom _).trans sheafedSpaceHom_ofSheafedSpaceIso)

/-- **Lifting undoes descent.** Lifting the ringed descent of a nodal isomorphism recovers that
isomorphism. -/
@[simp]
theorem ofSheafedSpaceIso_sheafedSpaceIso (e : Iso 𝓘(ℂ) ω d d') :
    ofSheafedSpaceIso e.sheafedSpaceIso e.sheafedSpaceIso_hom_app_algebraMap = e := by
  refine Iso.ext fun x ↦ ?_
  rw [ofSheafedSpaceIso, coe_ofHolomorphicLift]
  refine congrFun (eq_liftHomeomorph (h := baseHomeomorph e.sheafedSpaceIso) e.continuous
    fun y ↦ ?_).symm x
  rw [baseHomeomorph_apply, sheafedSpaceIso_hom, sheafedSpaceHom_hom_base_apply,
    gluedCurveHomeomorph_mk]

end Iso

/-- An isomorphism of the holomorphic sheafed spaces of two nodal curves is induced by a unique
analytic nodal isomorphism exactly when its section maps fix the constants. -/
theorem existsUnique_iso_sheafedSpaceIso_eq_iff (φ : sheafedSpace 𝓘(ℂ) d ≅ sheafedSpace 𝓘(ℂ) d') :
    (∃! e : Iso 𝓘(ℂ) ω d d', e.sheafedSpaceIso = φ) ↔
      ∀ (U : Opens (GluedCurve d')) (c : ℂ),
        (φ.hom.hom.c.app (op U)).hom (algebraMap ℂ _ c) =
          algebraMap ℂ ((sheafedSpace 𝓘(ℂ) d).presheaf.obj
            (op ((Opens.map φ.hom.hom.base).obj U))) c := by
  constructor
  · rintro ⟨e, rfl, -⟩
    exact e.sheafedSpaceIso_hom_app_algebraMap
  · intro hφ
    refine ⟨Iso.ofSheafedSpaceIso φ hφ, Iso.sheafedSpaceIso_ofSheafedSpaceIso, ?_⟩
    rintro e rfl
    exact (Iso.ofSheafedSpaceIso_sheafedSpaceIso e).symm

end TauCeti.NodalGluing

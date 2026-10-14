/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.AffineFunctions

/-!
# Recovering an affine morphism from its function algebra

For an affine morphism `p : V ⟶ X`, the relative spectrum of the actual function algebra
`p_* 𝒪_V` is canonically isomorphic to `V`, over `X`. On an affine open `U` of `X`, the
isomorphism is the usual affine identification of `p⁻¹ U` with the spectrum of its regular
functions. These identifications glue and are natural in morphisms over the base.

The resulting `relativeSpecCounit` is the geometric counit for the correspondence between
quasi-coherent algebras and affine morphisms. No affineness assumption on the base is needed.

## References

* The Stacks Project, Tag 01LL (relative spectrum).
* The local isomorphism argument follows Mathlib's
  `Scheme.AffineZariskiSite.isColimitCocone` in
  `Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski`.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace TauCeti

universe u

noncomputable section

variable {X V W : Scheme.{u}} (p : V ⟶ X) [IsAffineHom p]

/-- The affine chart of the relative spectrum of `p_* 𝒪_V`, mapped to `V` using the
identification of its sections with regular functions on `p⁻¹ U`. -/
private def functionChart (U : X.AffineZariskiSite) :
    Spec (CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1)) ⟶ V :=
  Spec.map (p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)) ≫
    (U.2.preimage p).fromSpec

private lemma functionChart_naturality {U U' : X.AffineZariskiSite} (h : U ⟶ U') :
    p.pushforwardStructureAlgebra.relativeSpecGluingData.functor.map h ≫
      functionChart p U' = functionChart p U := by
  -- Explicit section-ring endpoints let ordinary rewriting use `Spec.map_comp_assoc`.
  let r : CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U'.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) :=
    p.pushforwardStructureAlgebra.sectionsPresheaf.map ((toOpensFunctor X).map h).op
  let k : CommRingCat.of Γ(V, p ⁻¹ᵁ U.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) :=
    p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)
  let k' : CommRingCat.of Γ(V, p ⁻¹ᵁ U'.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U'.1) :=
    p.pushforwardStructureAlgebraPresheafIso.inv.app (op U'.1)
  let s : CommRingCat.of Γ(V, p ⁻¹ᵁ U'.1) ⟶ CommRingCat.of Γ(V, p ⁻¹ᵁ U.1) :=
    V.presheaf.map ((TopologicalSpace.Opens.map p.base).map ((toOpensFunctor X).map h)).op
  have hring : k' ≫ r = s ≫ k :=
    (p.pushforwardStructureAlgebraPresheafIso.inv.naturality
      ((toOpensFunctor X).map h).op).symm
  have hchart : Spec.map r ≫ (Spec.map k' ≫ (U'.2.preimage p).fromSpec) =
      Spec.map k ≫ (U.2.preimage p).fromSpec := by
    rw [← Spec.map_comp_assoc, hring, Spec.map_comp_assoc]
    exact congrArg (Spec.map k ≫ ·)
      ((U'.2.preimage p).map_fromSpec (U.2.preimage p)
        ((TopologicalSpace.Opens.map p.base).map ((toOpensFunctor X).map h)).op)
  exact (congrArg (· ≫ functionChart p U')
    (p.pushforwardStructureAlgebra.relativeSpecGluingData_functor_map h)).trans hchart

/-- The canonical map from the relative spectrum of an affine morphism's function algebra
back to its source, obtained by gluing the affine identifications on inverse images. -/
def _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsToScheme :
    p.pushforwardStructureAlgebra.relativeSpec ⟶ V :=
  colimit.desc _ {
    pt := V
    ι := {
      app := functionChart p
      naturality := fun _ _ h ↦ by
        exact (functionChart_naturality p h).trans (Category.comp_id _).symm } }

/-- On each affine open of the base, recovery from the function algebra is the ordinary
affine chart map on its inverse image. -/
@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecCover_f_relativeSpecFunctionsToScheme
    (U : X.AffineZariskiSite) :
    p.pushforwardStructureAlgebra.relativeSpecCover.f U ≫ p.relativeSpecFunctionsToScheme =
      Spec.map (p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)) ≫
        (U.2.preimage p).fromSpec :=
  colimit.ι_desc _ _

/-- Recovery from the function algebra respects the structure morphism to the base. -/
@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsToScheme_comp :
    p.relativeSpecFunctionsToScheme ≫ p =
      p.pushforwardStructureAlgebra.relativeSpecToBase := by
  apply p.pushforwardStructureAlgebra.relativeSpec_hom_ext
  intro U
  rw [Scheme.Hom.relativeSpecCover_f_relativeSpecFunctionsToScheme_assoc]
  have hring :
      p.pushforwardStructureAlgebra.toSectionsPresheaf.app (op U.1) ≫
        p.pushforwardStructureAlgebraPresheafIso.hom.app (op U.1) =
      p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl := by
    have h := NatTrans.congr_app
      p.pushforwardStructureAlgebra_toSectionsPresheaf_comp (op U.1)
    rw [NatTrans.comp_app] at h
    exact h.trans (Scheme.Hom.app_eq_appLE p)
  have hinv : p.appLE U.1 (p ⁻¹ᵁ U.1) le_rfl ≫
      p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1) =
      p.pushforwardStructureAlgebra.toSectionsPresheaf.app (op U.1) := by
    rw [← hring]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hspec := congrArg (fun f ↦ Spec.map f ≫ U.2.fromSpec) hinv
  simp only [Spec.map_comp_assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec p U.2 (U.2.preimage p) le_rfl] at hspec
  exact (Category.assoc _ _ _).trans
    (hspec.trans (p.pushforwardStructureAlgebra.relativeSpecCover_f_relativeSpecToBase U).symm)

/-- The affine chart of the function algebra is the affine inverse image of the base chart. -/
private def functionChartIso (U : X.AffineZariskiSite) :
    Spec (CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1)) ≅ (p ⁻¹ᵁ U.1 : Scheme) :=
  Scheme.Spec.mapIso (p.pushforwardStructureAlgebraPresheafIso.app (op U.1)).symm.op ≪≫
    (U.2.preimage p).isoSpec.symm

private lemma functionChartIso_hom_ι (U : X.AffineZariskiSite) :
    (functionChartIso p U).hom ≫ (p ⁻¹ᵁ U.1).ι =
      p.pushforwardStructureAlgebra.relativeSpecCover.f U ≫ p.relativeSpecFunctionsToScheme := by
  dsimp only [functionChartIso, Iso.trans, Functor.mapIso, Iso.op, Iso.symm, Iso.app,
    Scheme.Spec_map]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  exact (p.relativeSpecCover_f_relativeSpecFunctionsToScheme U).symm

/-- An affine scheme over a base is recovered from its actual algebra of regular functions. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isIso_relativeSpecFunctionsToScheme :
    IsIso p.relativeSpecFunctionsToScheme := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    (V.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite ↦ p ⁻¹ᵁ U.1)
      (p.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)))).mpr
    fun (U : X.AffineZariskiSite) ↦ ?_
  -- Check recovery over `p⁻¹ U`, using the same affine chart on both sides.
  let a : Spec (CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1)) ⟶
      p.pushforwardStructureAlgebra.relativeSpec :=
    p.pushforwardStructureAlgebra.relativeSpecCover.f U
  have : IsOpenImmersion a :=
    CommMon.isOpenImmersion_relativeSpecCover_f p.pushforwardStructureAlgebra U
  have hr : Set.range (pullback.fst p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι) =
      Set.range a := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι,
      ← Scheme.Hom.coe_preimage, ← Scheme.Hom.comp_preimage,
      Scheme.Hom.relativeSpecFunctionsToScheme_comp]
    exact congrArg (fun q : p.pushforwardStructureAlgebra.relativeSpec.Opens ↦ q.1)
      (p.pushforwardStructureAlgebra.relativeSpecToBase_preimage U)
  let e := IsOpenImmersion.isoOfRangeEq
    (pullback.fst p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι) a hr
  have he : e.hom ≫ (functionChartIso p U).hom =
      pullback.snd p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι := by
    have hchart : (functionChartIso p U).hom ≫ (p ⁻¹ᵁ U.1).ι =
        a ≫ p.relativeSpecFunctionsToScheme := functionChartIso_hom_ι p U
    rw [← cancel_mono (p ⁻¹ᵁ U.1).ι, Category.assoc, hchart, ← Category.assoc]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact pullback.condition
  -- The local recovery map is the composite of two canonical affine isomorphisms.
  have : IsIso (pullback.snd p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι) := by
    rw [← he]
    infer_instance
  exact this

variable {p} {q : W ⟶ X} [IsAffineHom q]

omit [IsAffineHom p] [IsAffineHom q] in
private lemma functionChart_ring_naturality (g : V ⟶ W) (h : g ≫ q = p)
    (U : X.AffineZariskiSite) (i : p ⁻¹ᵁ U.1 ≤ g ⁻¹ᵁ (q ⁻¹ᵁ U.1)) :
    q.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1) ≫
      CommRingCat.ofHom
        (CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U.1).toRingHom =
      g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i ≫
        p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1) := by
  rw [Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app,
    Scheme.Hom.pushforwardStructureAlgebraPresheafIso_inv_app]
  apply ConcreteCategory.hom_ext
  intro x
  -- The iso components retain presheaf-object coercions; `CommRingCat.comp_apply`
  -- and `hom_comp` do not match them at rewriting transparency. `change` identifies
  -- these presentations before evaluating the maps on the section rings.
  change CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U.1
    ((q.pushforwardStructureAlgebraSectionsRingEquiv U.1).symm x) =
    (p.pushforwardStructureAlgebraSectionsRingEquiv U.1).symm
    (g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i x)
  rw [Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
    RingEquiv.apply_symm_apply]

/-- Recovery of an affine morphism from its function algebra is natural in scheme morphisms
over the base. -/
@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsToScheme_naturality
    (g : V ⟶ W) (h : g ≫ q = p) :
    CommMon.relativeSpecMap (Scheme.Hom.pushforwardStructureAlgebraMap g h) ≫
        q.relativeSpecFunctionsToScheme = p.relativeSpecFunctionsToScheme ≫ g := by
  apply p.pushforwardStructureAlgebra.relativeSpec_hom_ext
  intro U
  let i : p ⁻¹ᵁ U.1 ≤ g ⁻¹ᵁ (q ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, h]
  let fU : CommRingCat.of Γ(q.pushforwardStructureAlgebra.X, U.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) := CommRingCat.ofHom
    (CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U.1).toRingHom
  let kP : CommRingCat.of Γ(V, p ⁻¹ᵁ U.1) ⟶
      CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1) :=
    p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)
  let kQ : CommRingCat.of Γ(W, q ⁻¹ᵁ U.1) ⟶
      CommRingCat.of Γ(q.pushforwardStructureAlgebra.X, U.1) :=
    q.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)
  -- Prove the chart identity at explicit spectrum sources: rewriting in the original
  -- goal retains opaque cover-object accessors that prevent ordinary `rw` and `simp`.
  suffices hchart : Spec.map fU ≫ (Spec.map kQ ≫ (U.2.preimage q).fromSpec) =
      (Spec.map kP ≫ (U.2.preimage p).fromSpec) ≫ g by
    exact (CommMon.relativeSpecCover_f_relativeSpecMap_assoc
      (Scheme.Hom.pushforwardStructureAlgebraMap g h) U _).trans
      ((congrArg (Spec.map fU ≫ ·)
        (q.relativeSpecCover_f_relativeSpecFunctionsToScheme U)).trans
        (hchart.trans (p.relativeSpecCover_f_relativeSpecFunctionsToScheme_assoc U g).symm))
  have hring : kQ ≫ fU = g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i ≫ kP :=
    functionChart_ring_naturality g h U i
  have hspec : Spec.map (g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i) ≫
      (U.2.preimage q).fromSpec = (U.2.preimage p).fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g (U.2.preimage q) (U.2.preimage p) i
  rw [← Spec.map_comp_assoc, hring]
  simp only [Spec.map_comp_assoc, hspec, Category.assoc]

/-- The inverse form of `Scheme.Hom.relativeSpecFunctionsToScheme_naturality`: a scheme morphism
over the base is, through the identifications with the relative spectra of the function
algebras, the relative spectrum of pullback of functions. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Hom.inv_relativeSpecFunctionsToScheme_naturality
    (g : V ⟶ W) (h : g ≫ q = p) :
    g ≫ inv q.relativeSpecFunctionsToScheme = inv p.relativeSpecFunctionsToScheme ≫
      CommMon.relativeSpecMap (Scheme.Hom.pushforwardStructureAlgebraMap g h) := by
  rw [IsIso.comp_inv_eq, Category.assoc, Scheme.Hom.relativeSpecFunctionsToScheme_naturality,
    IsIso.inv_hom_id_assoc]

variable (p)

/-- The canonical isomorphism recovering an affine scheme over `X` from its function algebra.
Its forward map is the gluing of the ordinary affine identifications on inverse images. -/
def _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsIso :
    p.pushforwardStructureAlgebra.relativeSpec ≅ V :=
  asIso p.relativeSpecFunctionsToScheme

/-- The forward recovery isomorphism is the canonical map glued from affine charts. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsIso_hom :
    p.relativeSpecFunctionsIso.hom = p.relativeSpecFunctionsToScheme :=
  (rfl)

/-- The inverse recovery map is the categorical inverse of the canonical affine recovery. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.relativeSpecFunctionsIso_inv :
    p.relativeSpecFunctionsIso.inv = inv p.relativeSpecFunctionsToScheme :=
  (rfl)

namespace AlgebraicGeometry

/-- The geometric counit: an affine scheme over `X` is naturally the relative spectrum of
its actual quasi-coherent algebra of regular functions. -/
def relativeSpecCounit (X : Scheme.{u}) :
    affineFunctions X ⋙ relativeSpec X ≅ 𝟭 (AffineSchemeOver X) :=
  NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk V.hom.relativeSpecFunctionsIso
      V.hom.relativeSpecFunctionsToScheme_comp)
    (fun {V W} g ↦ by
      apply MorphismProperty.Over.Hom.ext
      -- `rw [MorphismProperty.Comma.comp_left]` rejects this goal at implicit
      -- transparency: `@IsAffineHom` is not accepted as a `MorphismProperty Scheme`.
      -- `change` identifies these presentations before comparing the scheme maps.
      change CommMon.relativeSpecMap
          (Scheme.Hom.pushforwardStructureAlgebraMap g.left (MorphismProperty.Over.w g)) ≫
            W.hom.relativeSpecFunctionsIso.hom =
        V.hom.relativeSpecFunctionsIso.hom ≫ g.left
      rw [Scheme.Hom.relativeSpecFunctionsIso_hom, Scheme.Hom.relativeSpecFunctionsIso_hom]
      exact Scheme.Hom.relativeSpecFunctionsToScheme_naturality g.left
        (MorphismProperty.Over.w g))

/-- The counit on underlying schemes is the canonical recovery map from the function algebra. -/
@[simp]
lemma relativeSpecCounit_hom_app_left (V : AffineSchemeOver X) :
    ((relativeSpecCounit X).hom.app V).left = V.hom.relativeSpecFunctionsToScheme :=
  (rfl)

/-- On underlying schemes, the inverse counit is the inverse of the canonical recovery map. -/
@[simp]
lemma relativeSpecCounit_inv_app_left (V : AffineSchemeOver X) :
    ((relativeSpecCounit X).inv.app V).left = inv V.hom.relativeSpecFunctionsToScheme :=
  (rfl)

end AlgebraicGeometry

end

end TauCeti

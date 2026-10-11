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
  -- The gluing diagram is the spectrum of the sections presheaf on affine opens.
  change Spec.map (p.pushforwardStructureAlgebra.sectionsPresheaf.map
      ((toOpensFunctor X).map h).op) ≫ _ = _
  dsimp only [functionChart]
  erw [← Spec.map_comp_assoc, ← p.pushforwardStructureAlgebraPresheafIso.inv.naturality]
  erw [Spec.map_comp_assoc]
  exact congrArg (Spec.map (p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)) ≫ ·)
    ((U'.2.preimage p).map_fromSpec (U.2.preimage p)
      ((TopologicalSpace.Opens.map p.base).map ((toOpensFunctor X).map h)).op)

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
  erw [Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec p U.2 (U.2.preimage p) le_rfl,
    ← Spec.map_comp_assoc,
    CommMon.relativeSpecCover_f_relativeSpecToBase]
  congr 2
  apply (cancel_mono (p.pushforwardStructureAlgebraPresheafIso.hom.app (op U.1))).mp
  have h := NatTrans.congr_app
    p.pushforwardStructureAlgebra_toSectionsPresheaf_comp (op U.1)
  rw [NatTrans.comp_app] at h
  erw [Category.assoc, Iso.inv_hom_id_app, Scheme.Hom.appLE_eq_app]
  exact (Category.comp_id _).trans h.symm

/-- An affine scheme over a base is recovered from its actual algebra of regular functions. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isIso_relativeSpecFunctionsToScheme :
    IsIso p.relativeSpecFunctionsToScheme := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
    (V.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite ↦ p ⁻¹ᵁ U.1)
      (p.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)))).mpr fun U ↦ ?_
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
  let q : Spec (CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1)) ⟶ (p ⁻¹ᵁ U.1 : Scheme) :=
    Spec.map (p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1)) ≫
      (U.2.preimage p).isoSpec.inv
  have : IsIso q := by
    -- Specify the component isomorphisms: instance search does not identify the
    -- sections-presheaf objects with the explicitly typed section rings above.
    have : IsIso (Spec.map (p.pushforwardStructureAlgebraPresheafIso.inv.app (op U.1))) :=
      inferInstanceAs (IsIso (Scheme.Spec.mapIso
        (p.pushforwardStructureAlgebraPresheafIso.app (op U.1)).symm.op).hom)
    exact @IsIso.comp_isIso Scheme _ _ _ _ _ _ this
      (inferInstanceAs (IsIso (U.2.preimage p).isoSpec.inv))
  have hq : q ≫ (p ⁻¹ᵁ U.1).ι = a ≫ p.relativeSpecFunctionsToScheme := by
    exact (Category.assoc _ _ _).trans
      (p.relativeSpecCover_f_relativeSpecFunctionsToScheme U).symm
  have he : e.hom ≫ q =
      pullback.snd p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι := by
    rw [← cancel_mono (p ⁻¹ᵁ U.1).ι, Category.assoc, hq, ← Category.assoc]
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact pullback.condition
  -- The local recovery map is the composite of two canonical affine isomorphisms.
  have : IsIso (pullback.snd p.relativeSpecFunctionsToScheme (p ⁻¹ᵁ U.1).ι) :=
    he ▸ inferInstanceAs (IsIso (e.hom ≫ q))
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
  -- Evaluate the bundled ring maps to use the public section-ring formula.
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
  let aP : Spec (CommRingCat.of Γ(p.pushforwardStructureAlgebra.X, U.1)) ⟶
      p.pushforwardStructureAlgebra.relativeSpec :=
    p.pushforwardStructureAlgebra.relativeSpecCover.f U
  let φ := CommMon.relativeSpecMap (Scheme.Hom.pushforwardStructureAlgebraMap g h)
  -- Explicit chart sources avoid rewriting through the opaque open-cover object accessor.
  exact calc
    aP ≫ (φ ≫ q.relativeSpecFunctionsToScheme) =
        Spec.map fU ≫ (Spec.map kQ ≫ (U.2.preimage q).fromSpec) :=
      (CommMon.relativeSpecCover_f_relativeSpecMap_assoc
        (Scheme.Hom.pushforwardStructureAlgebraMap g h) U _).trans
        (congrArg (Spec.map fU ≫ ·)
          (q.relativeSpecCover_f_relativeSpecFunctionsToScheme U))
    _ = Spec.map (kQ ≫ fU) ≫ (U.2.preimage q).fromSpec :=
      (Spec.map_comp_assoc _ _ _).symm
    _ = Spec.map (g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i ≫ kP) ≫
        (U.2.preimage q).fromSpec :=
      congrArg (fun r ↦ Spec.map r ≫ (U.2.preimage q).fromSpec)
        (functionChart_ring_naturality g h U i)
    _ = Spec.map kP ≫
        (Spec.map (g.appLE (q ⁻¹ᵁ U.1) (p ⁻¹ᵁ U.1) i) ≫ (U.2.preimage q).fromSpec) :=
      Spec.map_comp_assoc _ _ _
    _ = Spec.map kP ≫ ((U.2.preimage p).fromSpec ≫ g) :=
      congrArg (Spec.map kP ≫ ·)
        (IsAffineOpen.SpecMap_appLE_fromSpec g (U.2.preimage q) (U.2.preimage p) i)
    _ = aP ≫ (p.relativeSpecFunctionsToScheme ≫ g) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) (p.relativeSpecCover_f_relativeSpecFunctionsToScheme U).symm).trans
          (Category.assoc _ _ _))

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
      -- Both functors act on over-morphisms by their underlying scheme maps.
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

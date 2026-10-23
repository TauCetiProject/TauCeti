/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Counit
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra
public import TauCeti.AlgebraicGeometry.RelativeSpec.Unit
public import TauCeti.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# The universal property of relative Spec

Let `A` be a quasi-coherent commutative algebra on a scheme `X` and let `q : T ⟶ X` be an
arbitrary scheme over `X`. Morphisms `T ⟶ Spec_X A` over `X` correspond to morphisms of
`𝒪_X`-algebras `A ⟶ q_* 𝒪_T` (`CommMon.relativeSpecHomEquiv`). This is the functor-of-points
description of relative Spec; no affineness, quasi-compactness or separation hypothesis on `q` is
needed.

A morphism `t : T ⟶ Spec_X A` over `X` pulls back regular functions, which gives the algebra map
`A ≅ p_* 𝒪_{Spec_X A} ⟶ q_* 𝒪_T`. Conversely, an algebra map `φ : A ⟶ q_* 𝒪_T` induces, over
each affine open `U` of `X`, a ring map `Γ(A.X, U) ⟶ Γ(T, q⁻¹ U)` and hence a morphism
`q⁻¹ U ⟶ Spec Γ(A.X, U)` into the chart of `Spec_X A` over `U`. These charts are compatible with
restriction and glue to `CommMon.relativeSpecLift φ`, along the cover of `T` by the inverse images
of the affine opens of `X`. Both constructions are natural in `T` and in `A`.

Composing with the adjunction between pullback and pushforward of algebras gives the universal
property in pullback form: morphisms `T ⟶ Spec_X A` over `X` correspond to morphisms of
`𝒪_T`-algebras `q^* A ⟶ 𝒪_T` (`TauCeti.AlgebraicGeometry.relativeSpecPullbackHomEquiv`).

## Main declarations

* `CategoryTheory.CommMon.relativeSpecLift`: the morphism `T ⟶ Spec_X A` induced by an algebra
  map `A ⟶ q_* 𝒪_T`, characterized on charts by `CommMon.ι_relativeSpecLift`;
* `CategoryTheory.CommMon.relativeSpecHomEquiv`: the bijection between morphisms over `X` and
  algebra maps;
* `CategoryTheory.CommMon.relativeSpecLift_comp_pushforwardStructureAlgebraMap`,
  `CategoryTheory.CommMon.relativeSpecLift_comp` and
  `CategoryTheory.CommMon.relativeSpecHomEquiv_comp_relativeSpecMap`: naturality in the test
  scheme and in the algebra;
* `TauCeti.AlgebraicGeometry.relativeSpecHomIso X`: the bijection as a natural isomorphism of
  functors of quasi-coherent algebras and schemes over `X` (whose target uses the function-algebra
  functor `TauCeti.AlgebraicGeometry.overFunctions X`), with components
  `CommMon.relativeSpecHomEquiv`;
* `TauCeti.AlgebraicGeometry.relativeSpecPullbackHomEquiv`: the bijection between morphisms over
  `X` and algebra maps `q^* A ⟶ 𝒪_T`, natural in the algebra.

## References

* The Stacks Project, Tag 01LQ (relative spectrum as a functor).
* The gluing of the charts follows Mathlib's `AlgebraicGeometry.Scheme.Hom.toNormalization`, which
  glues maps into the relative normalization along the same pulled-back directed affine cover.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.AffineZariskiSite

namespace CategoryTheory.CommMon

universe u

noncomputable section

variable {X T : Scheme.{u}} {A : CommMon X.Modules} [A.X.IsQuasicoherent] {q : T ⟶ X}

/-- The ring maps on sections over the opens of `X` induced by an algebra map `A ⟶ q_* 𝒪_T`,
landing in the regular functions on inverse images. -/
private abbrev sectionsToPreimage (φ : A ⟶ q.pushforwardStructureAlgebra) :
    A.sectionsPresheaf ⟶ (TopologicalSpace.Opens.map q.base).op ⋙ T.presheaf :=
  sectionsPresheafMap φ ≫ q.pushforwardStructureAlgebraPresheafIso.hom

/-- The ring map `Γ(A.X, U) ⟶ Γ(T, q⁻¹ U)` induced by an algebra map `A ⟶ q_* 𝒪_T`. -/
private def liftSections (φ : A ⟶ q.pushforwardStructureAlgebra) (U : X.AffineZariskiSite) :
    CommRingCat.of Γ(A.X, U.toOpens) ⟶ Γ(T, q ⁻¹ᵁ U.toOpens) :=
  (sectionsToPreimage φ).app (op U.toOpens)

/-- The chart `Spec Γ(A.X, U) ⟶ Spec_X A` over an affine open `U`, with its source stated as the
spectrum of the section ring. -/
private def chart (A : CommMon X.Modules) [A.X.IsQuasicoherent] (U : X.AffineZariskiSite) :
    Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ A.relativeSpec :=
  A.relativeSpecCover.f U

/-- The chart of the lift over an affine open `U` of `X`. -/
private def liftChart (φ : A ⟶ q.pushforwardStructureAlgebra) (U : X.AffineZariskiSite) :
    (q ⁻¹ᵁ U.toOpens).toScheme ⟶ A.relativeSpec :=
  (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (liftSections φ U) ≫ chart A U

private lemma liftChart_compat (φ : A ⟶ q.pushforwardStructureAlgebra)
    {U V : X.AffineZariskiSite} (i : U ⟶ V) (hle : q ⁻¹ᵁ U.toOpens ≤ q ⁻¹ᵁ V.toOpens) :
    T.homOfLE hle ≫ liftChart φ V = liftChart φ U := by
  let r : CommRingCat.of Γ(A.X, V.toOpens) ⟶ CommRingCat.of Γ(A.X, U.toOpens) :=
    A.sectionsPresheaf.map ((toOpensFunctor X).map i).op
  let ψU := liftSections φ U
  let ψV := liftSections φ V
  let s : Γ(T, q ⁻¹ᵁ V.toOpens) ⟶ Γ(T, q ⁻¹ᵁ U.toOpens) := T.presheaf.map (homOfLE hle).op
  let fU := chart A U
  let fV := chart A V
  -- The charts of `Spec_X A` are glued along the spectra of the restriction maps of `A`.
  have hι : Spec.map r ≫ fV = fU := by
    have := colimit.w A.relativeSpecGluingData.functor i
    rw [A.relativeSpecGluingData_functor_map] at this
    exact this
  -- Naturality is elaborated at the explicit inclusion before matching the typed endpoints.
  have hring : ψV ≫ s = r ≫ ψU := by
    have := (sectionsToPreimage φ).naturality ((toOpensFunctor X).map i).op
    exact this.symm
  have hspec : (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map s =
      T.homOfLE hle ≫ (q ⁻¹ᵁ V.toOpens).toSpecΓ :=
    Scheme.Opens.toSpecΓ_SpecMap_presheaf_map _ _ hle
  calc T.homOfLE hle ≫ (q ⁻¹ᵁ V.toOpens).toSpecΓ ≫ Spec.map ψV ≫ fV
      = ((q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map s) ≫ Spec.map ψV ≫ fV := by
        rw [hspec, Category.assoc]
    _ = (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (ψV ≫ s) ≫ fV := by
        rw [Spec.map_comp, Category.assoc, Category.assoc]
    _ = (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU ≫ Spec.map r ≫ fV := by
        rw [hring, Spec.map_comp, Category.assoc]
    _ = (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map ψU ≫ fU := by rw [hι]

open TauCeti.AlgebraicGeometry.Scheme.AffineZariskiSite in
private lemma glue_compat (φ : A ⟶ q.pushforwardStructureAlgebra)
    {U V : ((directedCover X).pullback₁ q).I₀} (i : U ⟶ V) :
    Scheme.Cover.trans ((directedCover X).pullback₁ q) i ≫
        (pullbackRestrictIsoRestrict q (toOpens V)).hom ≫ liftChart φ V =
      (pullbackRestrictIsoRestrict q (toOpens U)).hom ≫ liftChart φ U := by
  have hle := q.preimage_mono ((toOpensFunctor X).map i).le
  have hc := liftChart_compat φ (U := U) (V := V) i hle
  exact (directedCover_pullback₁_trans_pullbackRestrictIsoRestrict_hom_assoc q i
    (liftChart φ V)).trans ((Category.assoc _ _ _).trans (congrArg _ hc))

/-- The morphism `T ⟶ Spec_X A` over `X` induced by a morphism of `𝒪_X`-algebras
`φ : A ⟶ q_* 𝒪_T`. Over an affine open `U` of `X`, it maps `q⁻¹ U` to the chart `Spec Γ(A.X, U)`
by the spectrum of the ring map `Γ(A.X, U) ⟶ Γ(T, q⁻¹ U)` induced by `φ`
(`CommMon.ι_relativeSpecLift`). -/
def relativeSpecLift (φ : A ⟶ q.pushforwardStructureAlgebra) : T ⟶ A.relativeSpec :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected ((directedCover X).pullback₁ q)
    (fun U ↦ (pullbackRestrictIsoRestrict q U.toOpens).hom ≫ liftChart φ U)
    (glue_compat φ)

@[reassoc]
private lemma ι_relativeSpecLift_liftChart (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite) :
    (q ⁻¹ᵁ U.toOpens).ι ≫ relativeSpecLift φ = liftChart φ U := by
  rw [← cancel_epi (pullbackRestrictIsoRestrict q U.toOpens).hom, ← Category.assoc,
    pullbackRestrictIsoRestrict_hom_ι]
  exact Scheme.OpenCover.map_glueMorphismsOfLocallyDirected ((directedCover X).pullback₁ q) _
    (glue_compat φ) (U : ((directedCover X).pullback₁ q).I₀)

omit [A.X.IsQuasicoherent] in
private lemma sectionsToPreimage_structure (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.Opens) :
    A.toSectionsPresheaf.app (op U) ≫ (sectionsToPreimage φ).app (op U) = q.app U := by
  have h := NatTrans.congr_app (CommMon.toSectionsPresheaf_comp_sectionsPresheafMap φ) (op U)
  have h2 := NatTrans.congr_app q.pushforwardStructureAlgebra_toSectionsPresheaf_comp (op U)
  rw [NatTrans.comp_app] at h h2
  rw [NatTrans.comp_app, ← Category.assoc, h, h2]

private lemma liftChart_relativeSpecToBase (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite) :
    liftChart φ U ≫ A.relativeSpecToBase = (q ⁻¹ᵁ U.toOpens).ι ≫ q := by
  -- Explicit section-ring endpoints keep the rewrites below type-correct.
  let ι := chart A U
  let a : Γ(X, U.toOpens) ⟶ CommRingCat.of Γ(A.X, U.toOpens) :=
    A.toSectionsPresheaf.app (op U.toOpens)
  have hU : IsAffineOpen U.toOpens := U.2
  have hι : ι ≫ A.relativeSpecToBase = Spec.map a ≫ hU.fromSpec :=
    A.relativeSpecCover_f_relativeSpecToBase U
  have hring : a ≫ liftSections φ U = q.app U.toOpens :=
    sectionsToPreimage_structure φ U.toOpens
  calc (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (liftSections φ U) ≫ ι ≫ A.relativeSpecToBase
      = (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫ Spec.map (a ≫ liftSections φ U) ≫ hU.fromSpec := by
        rw [hι, Spec.map_comp_assoc]
    _ = (q ⁻¹ᵁ U.toOpens).ι ≫ q := by
        rw [hring, Scheme.Opens.toSpecΓ_naturality_assoc, IsAffineOpen.toSpecΓ_fromSpec,
          morphismRestrict_ι]

/-- The lift is a morphism over `X`. -/
@[reassoc (attr := simp)]
lemma relativeSpecLift_relativeSpecToBase (φ : A ⟶ q.pushforwardStructureAlgebra) :
    relativeSpecLift φ ≫ A.relativeSpecToBase = q := by
  refine Scheme.Cover.hom_ext (T.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite ↦
    q ⁻¹ᵁ U.toOpens) (q.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))) _ _ fun U ↦ ?_
  exact (ι_relativeSpecLift_liftChart_assoc φ U _).trans (liftChart_relativeSpecToBase φ U)

private lemma relativeSpecLift_appLE (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite)
    (e : q ⁻¹ᵁ U.toOpens ≤ relativeSpecLift φ ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ U.toOpens)) :
    (relativeSpecLift φ).appLE (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) (q ⁻¹ᵁ U.toOpens) e =
      (chart A U).appLE _ ⊤ (A.top_le_preimage_relativeSpecToBase U) ≫
        (Scheme.ΓSpecIso (CommRingCat.of Γ(A.X, U.toOpens))).hom ≫ liftSections φ U := by
  let W := q ⁻¹ᵁ U.toOpens
  let P := A.relativeSpecToBase ⁻¹ᵁ U.toOpens
  let ι := chart A U
  have hι : ⊤ ≤ ι ⁻¹ᵁ P := A.top_le_preimage_relativeSpecToBase U
  have hcomp : ∀ {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of Γ(A.X, U.toOpens))),
      ⊤ ≤ (f ≫ ι) ⁻¹ᵁ P :=
    fun f x _ ↦ hι (Set.mem_univ (f x))
  -- Transport `appLE` along an equality of morphisms; its inclusion argument depends on them.
  have hcongr : ∀ (f g : W.toScheme ⟶ A.relativeSpec) (_ : f = g) (e₁ : ⊤ ≤ f ⁻¹ᵁ P)
      (e₂ : ⊤ ≤ g ⁻¹ᵁ P), f.appLE P ⊤ e₁ = g.appLE P ⊤ e₂ := by
    rintro f _ rfl _ _
    rfl
  have hW : W.ι.appLE W ⊤ (by simp) = W.topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  have hspec : (Spec.map (liftSections φ U) ≫ ι).appLE P ⊤ (hcomp _) ≫
      (Scheme.ΓSpecIso Γ(T, W)).hom =
      (ι.appLE P ⊤ hι ≫ (Scheme.ΓSpecIso _).hom) ≫ liftSections φ U :=
    Scheme.Hom.appLE_ΓSpecIso_hom_naturality ι (liftSections φ U) rfl hι _
  have htop : W.toSpecΓ.appLE ⊤ ⊤ le_top = (Scheme.ΓSpecIso Γ(T, W)).hom ≫ W.topIso.inv :=
    (Scheme.Hom.appLE_eq_app W.toSpecΓ (U := ⊤)).trans (Scheme.Opens.toSpecΓ_appTop W)
  -- Compose with the inclusion `q⁻¹ U ⟶ T`, where the lift is the chart map.
  rw [← cancel_mono W.topIso.inv, ← hW, Scheme.Hom.appLE_comp_appLE,
    hcongr _ _ (ι_relativeSpecLift_liftChart φ U) _
      (hcomp (W.toSpecΓ ≫ Spec.map (liftSections φ U)))]
  have h1 : (liftChart φ U).appLE P ⊤ (hcomp (W.toSpecΓ ≫ Spec.map (liftSections φ U))) =
      (Spec.map (liftSections φ U) ≫ ι).appLE P ⊤ (hcomp _) ≫ W.toSpecΓ.appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [h1, htop, hW, reassoc_of% hspec]
  exact congrArg (ι.appLE P ⊤ hι ≫ ·) (Category.assoc _ _ _).symm

omit [A.X.IsQuasicoherent] in
private lemma liftSections_apply (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite) (x : Γ(A.X, U.toOpens)) :
    liftSections φ U x =
      q.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens (sectionsAlgHom φ U.toOpens x) := by
  rw [liftSections, NatTrans.comp_app, sectionsPresheafMap_app,
    Scheme.Hom.pushforwardStructureAlgebraPresheafIso_hom_app]
  rfl

omit [A.X.IsQuasicoherent] in
private lemma liftSections_comp {T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : A ⟶ q.pushforwardStructureAlgebra) (U : X.AffineZariskiSite) :
    liftSections (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g rfl) U =
      liftSections φ U ≫
        g.appLE (q ⁻¹ᵁ U.toOpens) ((g ≫ q) ⁻¹ᵁ U.toOpens) (Scheme.Hom.comp_preimage g q _).le := by
  ext x
  rw [liftSections_apply, CommRingCat.comp_apply, liftSections_apply, sectionsAlgHom_comp,
    AlgHom.comp_apply, Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply,
    RingEquiv.apply_symm_apply]

/-- On the inverse image of an affine open `U` of `X`, the lift is the spectrum of the ring map
`Γ(A.X, U) ⟶ Γ(T, q⁻¹ U)` induced by `φ`, followed by the chart of `Spec_X A` over `U`. -/
@[reassoc (attr := simp)]
lemma ι_relativeSpecLift (φ : A ⟶ q.pushforwardStructureAlgebra) (U : X.AffineZariskiSite) :
    (q ⁻¹ᵁ U.toOpens).ι ≫ relativeSpecLift φ =
      (q ⁻¹ᵁ U.toOpens).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom ((q.pushforwardStructureAlgebraSectionsRingEquiv
          U.toOpens).toRingHom.comp (sectionsAlgHom φ U.toOpens).toRingHom)) ≫
        A.relativeSpecCover.f U := by
  have h : liftSections φ U = CommRingCat.ofHom ((q.pushforwardStructureAlgebraSectionsRingEquiv
      U.toOpens).toRingHom.comp (sectionsAlgHom φ U.toOpens).toRingHom) := by
    ext x
    exact liftSections_apply φ U x
  rw [ι_relativeSpecLift_liftChart, liftChart, h]
  rfl

variable {T' : Scheme.{u}} {q' : T' ⟶ X}

/-- The lift is natural in the test scheme: precomposing it with `g : T' ⟶ T` over `X`
corresponds to composing the algebra map with pullback of regular functions along `g`. -/
lemma relativeSpecLift_comp_pushforwardStructureAlgebraMap (g : T' ⟶ T) (hg : g ≫ q = q')
    (φ : A ⟶ q.pushforwardStructureAlgebra) :
    relativeSpecLift (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g hg) =
      g ≫ relativeSpecLift φ := by
  subst hg
  refine Scheme.Cover.hom_ext (T'.openCoverOfIsOpenCover (fun U : X.AffineZariskiSite ↦
    (g ≫ q) ⁻¹ᵁ U.toOpens) ((g ≫ q).iSup_preimage_eq_top (iSup_affineOpens_eq_top X))) _ _
    fun (U : X.AffineZariskiSite) ↦ ?_
  let r := g.resLE (q ⁻¹ᵁ U.toOpens) ((g ≫ q) ⁻¹ᵁ U.toOpens) (Scheme.Hom.comp_preimage g q _).le
  have h1 : liftChart (φ ≫ Scheme.Hom.pushforwardStructureAlgebraMap g rfl) U =
      r ≫ liftChart φ U := by
    unfold liftChart
    rw [liftSections_comp, Spec.map_comp_assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  have h2 : r ≫ liftChart φ U = ((g ≫ q) ⁻¹ᵁ U.toOpens).ι ≫ g ≫ relativeSpecLift φ := by
    rw [← ι_relativeSpecLift_liftChart, Scheme.Hom.resLE_comp_ι_assoc]
  exact (ι_relativeSpecLift_liftChart _ U).trans (h1.trans h2)

/-- On sections over the inverse image of an affine open `U` of `X`, the lift sends a function
on `Spec_X A`, read as a section of `A` over `U` through its chart, to its image under `φ`. -/
lemma relativeSpecLift_appLE_apply (φ : A ⟶ q.pushforwardStructureAlgebra)
    (U : X.AffineZariskiSite)
    (e : q ⁻¹ᵁ U.toOpens ≤ relativeSpecLift φ ⁻¹ᵁ (A.relativeSpecToBase ⁻¹ᵁ U.toOpens))
    (y : Γ(A.relativeSpecToBase.pushforwardStructureAlgebra.X, U.toOpens)) :
    (relativeSpecLift φ).appLE (A.relativeSpecToBase ⁻¹ᵁ U.toOpens) (q ⁻¹ᵁ U.toOpens) e
        (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens y) =
      q.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens (sectionsAlgHom φ U.toOpens
        (A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv U y)) :=
  (congr($(relativeSpecLift_appLE φ U e)
    (A.relativeSpecToBase.pushforwardStructureAlgebraSectionsRingEquiv U.toOpens y)).trans
    (congrArg (liftSections φ U)
      (A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv_apply U y).symm)).trans
    (liftSections_apply φ U _)

/-- The algebra map recovered from the lift of `φ` is `φ`: pulling back regular functions along
`CommMon.relativeSpecLift φ` and identifying `A` with the functions on `Spec_X A` gives `φ`. -/
@[simp]
lemma relativeSpecPushforwardIso_inv_pushforwardStructureAlgebraMap_relativeSpecLift
    (φ : A ⟶ q.pushforwardStructureAlgebra) :
    A.relativeSpecPushforwardIso.inv ≫ Scheme.Hom.pushforwardStructureAlgebraMap
      (relativeSpecLift φ) (relativeSpecLift_relativeSpecToBase φ) = φ := by
  refine hom_ext_of_isAffineOpen fun V hV ↦ AlgHom.ext fun x ↦ ?_
  let U : X.AffineZariskiSite := ⟨V, hV⟩
  let y := sectionsAlgHom A.relativeSpecPushforwardIso.inv V x
  have hy : A.relativeSpecCoverFunctionAlgebraSectionsRingEquiv U y = x := by
    rw [← sectionsAlgHom_relativeSpecPushforwardIso_hom_apply, ← AlgHom.comp_apply,
      ← sectionsAlgHom_comp, Iso.inv_hom_id, sectionsAlgHom_id, AlgHom.id_apply]
  rw [sectionsAlgHom_comp, AlgHom.comp_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply]
  have h := relativeSpecLift_appLE_apply φ U (by
      rw [← Scheme.Hom.comp_preimage, relativeSpecLift_relativeSpecToBase]) y
  rw [hy] at h
  exact (congrArg _ h).trans (RingEquiv.symm_apply_apply _ _)

/-- The lift of the identification of `A` with the functions on `Spec_X A` is the identity. -/
private lemma relativeSpecLift_relativeSpecPushforwardIso_inv :
    relativeSpecLift A.relativeSpecPushforwardIso.inv = 𝟙 A.relativeSpec := by
  let m := relativeSpecLift A.relativeSpecPushforwardIso.inv
  have hm : m ≫ A.relativeSpecToBase = A.relativeSpecToBase :=
    relativeSpecLift_relativeSpecToBase _
  -- `m` induces the identity on functions, and affine schemes over `X` are recovered from their
  -- function algebras.
  have h1 : Scheme.Hom.pushforwardStructureAlgebraMap m hm = 𝟙 _ := by
    rw [← cancel_epi A.relativeSpecPushforwardIso.inv, Category.comp_id]
    exact relativeSpecPushforwardIso_inv_pushforwardStructureAlgebraMap_relativeSpecLift _
  have h2 := Scheme.Hom.relativeSpecFunctionsToScheme_naturality m hm
  rw [h1, relativeSpecMap_id, Category.id_comp] at h2
  rw [← cancel_epi A.relativeSpecToBase.relativeSpecFunctionsToScheme, Category.comp_id]
  exact h2.symm

/-- A morphism over `X` is the lift of its own algebra map. -/
@[simp]
lemma relativeSpecLift_relativeSpecPushforwardIso_inv_comp (t : T ⟶ A.relativeSpec)
    (h : t ≫ A.relativeSpecToBase = q) :
    relativeSpecLift (A.relativeSpecPushforwardIso.inv ≫
      Scheme.Hom.pushforwardStructureAlgebraMap t h) = t := by
  subst h
  exact (relativeSpecLift_comp_pushforwardStructureAlgebraMap t rfl _).trans ((congrArg (t ≫ ·)
    relativeSpecLift_relativeSpecPushforwardIso_inv).trans (Category.comp_id t))

variable (A q) in
/-- **The universal property of relative Spec.** Morphisms `T ⟶ Spec_X A` over `X` correspond
to morphisms of `𝒪_X`-algebras `A ⟶ q_* 𝒪_T`. A morphism `t` gives pullback of regular functions
along `t`, after identifying `A` with the functions on `Spec_X A`; conversely an algebra map
gives `CommMon.relativeSpecLift`. No hypothesis on `q` is needed. -/
def relativeSpecHomEquiv :
    {t : T ⟶ A.relativeSpec // t ≫ A.relativeSpecToBase = q} ≃
      (A ⟶ q.pushforwardStructureAlgebra) where
  toFun t := A.relativeSpecPushforwardIso.inv ≫ Scheme.Hom.pushforwardStructureAlgebraMap t.1 t.2
  invFun φ := ⟨relativeSpecLift φ, relativeSpecLift_relativeSpecToBase φ⟩
  left_inv t := Subtype.ext (relativeSpecLift_relativeSpecPushforwardIso_inv_comp t.1 t.2)
  right_inv := relativeSpecPushforwardIso_inv_pushforwardStructureAlgebraMap_relativeSpecLift

/-- The algebra map of a morphism over `X` is pullback of regular functions along it. -/
@[simp]
lemma relativeSpecHomEquiv_apply
    (t : {t : T ⟶ A.relativeSpec // t ≫ A.relativeSpecToBase = q}) :
    A.relativeSpecHomEquiv q t =
      A.relativeSpecPushforwardIso.inv ≫ Scheme.Hom.pushforwardStructureAlgebraMap t.1 t.2 :=
  (rfl)

/-- The morphism over `X` of an algebra map is its lift. -/
@[simp]
lemma relativeSpecHomEquiv_symm_apply_coe (φ : A ⟶ q.pushforwardStructureAlgebra) :
    ((A.relativeSpecHomEquiv q).symm φ).1 = relativeSpecLift φ :=
  (rfl)

variable {B : CommMon X.Modules} [B.X.IsQuasicoherent]

/-- The lift is natural in the algebra: precomposing the algebra map with `f : B ⟶ A`
corresponds to composing with the relative-spectrum map of `f`. -/
lemma relativeSpecLift_comp (f : B ⟶ A) (φ : A ⟶ q.pushforwardStructureAlgebra) :
    relativeSpecLift (f ≫ φ) = relativeSpecLift φ ≫ relativeSpecMap f := by
  have hB : (relativeSpecLift φ ≫ relativeSpecMap f) ≫ B.relativeSpecToBase = q := by simp
  have h := (B.relativeSpecHomEquiv q).symm_apply_apply ⟨_, hB⟩
  refine (congrArg Subtype.val (congrArg (B.relativeSpecHomEquiv q).symm ?_)).trans
    (congrArg Subtype.val h)
  have hc := Scheme.Hom.pushforwardStructureAlgebraMap_comp (relativeSpecLift φ)
    (relativeSpecMap f) (relativeSpecLift_relativeSpecToBase φ)
    (relativeSpecMap_relativeSpecToBase f)
  rw [relativeSpecHomEquiv_apply]
  dsimp only
  rw [hc, Iso.eq_inv_comp, ← Category.assoc, ← relativeSpecPushforwardIso_hom_naturality,
    Category.assoc]
  exact congrArg _ ((Iso.inv_comp_eq _).mp
    (relativeSpecPushforwardIso_inv_pushforwardStructureAlgebraMap_relativeSpecLift φ)).symm

/-- The bijection `CommMon.relativeSpecHomEquiv` is natural in the algebra: composing with the
relative-spectrum map of `f : B ⟶ A` corresponds to precomposing the algebra map with `f`. -/
lemma relativeSpecHomEquiv_comp_relativeSpecMap (f : B ⟶ A)
    (t : {t : T ⟶ A.relativeSpec // t ≫ A.relativeSpecToBase = q}) :
    B.relativeSpecHomEquiv q ⟨t.1 ≫ relativeSpecMap f, by
        rw [Category.assoc, relativeSpecMap_relativeSpecToBase, t.2]⟩ =
      f ≫ A.relativeSpecHomEquiv q t := by
  rw [← Equiv.eq_symm_apply]
  refine Subtype.ext ?_
  rw [relativeSpecHomEquiv_symm_apply_coe, relativeSpecLift_comp, relativeSpecHomEquiv_apply,
    relativeSpecLift_relativeSpecPushforwardIso_inv_comp]

end

end CategoryTheory.CommMon

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X : Scheme.{u}} in
/-- `CommMon.relativeSpecHomEquiv` with morphisms over `X` read in `Over X`. -/
private def relativeSpecOverHomEquiv (A : QuasicoherentAlgebra X) (T : Over X) :
    (T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((relativeSpec X).obj (op A))) ≃
      (A.obj ⟶ T.hom.pushforwardStructureAlgebra) where
  toFun g := A.obj.relativeSpecHomEquiv T.hom ⟨g.left, Over.w g⟩
  invFun φ := Over.homMk (CommMon.relativeSpecLift φ)
    (CommMon.relativeSpecLift_relativeSpecToBase φ)
  left_inv g := Over.OverMorphism.ext
    (CommMon.relativeSpecLift_relativeSpecPushforwardIso_inv_comp g.left (Over.w g))
  right_inv :=
    CommMon.relativeSpecPushforwardIso_inv_pushforwardStructureAlgebraMap_relativeSpecLift

variable {X : Scheme.{u}} in
private lemma relativeSpecOverHomEquiv_comp (A : QuasicoherentAlgebra X) {T' T : Over X}
    (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverHomEquiv A T' (g ≫ t) =
      relativeSpecOverHomEquiv A T t ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g) :=
  (congrArg _ (Scheme.Hom.pushforwardStructureAlgebraMap_comp g.left t.left (Over.w g)
    (Over.w t))).trans (Category.assoc _ _ _).symm

variable {X : Scheme.{u}} in
private lemma relativeSpecOverHomEquiv_comp_relativeSpecMap {A B : QuasicoherentAlgebra X}
    (f : B ⟶ A) {T : Over X}
    (t : T ⟶ (MorphismProperty.Over.forget _ _ X).obj ((relativeSpec X).obj (op A))) :
    relativeSpecOverHomEquiv B T
        (t ≫ (MorphismProperty.Over.forget _ _ X).map ((relativeSpec X).map f.op)) =
      f.hom ≫ relativeSpecOverHomEquiv A T t := by
  exact CommMon.relativeSpecHomEquiv_comp_relativeSpecMap f.hom ⟨t.left, Over.w t⟩

/-- **The functor-of-points universal property of relative Spec**, natural in the algebra `A`
and in the scheme `T` over `X`: morphisms `T ⟶ Spec_X A` over `X` correspond to morphisms of
`𝒪_X`-algebras `A ⟶ q_* 𝒪_T`. Its components are `CommMon.relativeSpecHomEquiv`. -/
def relativeSpecHomIso (X : Scheme.{u}) :
    relativeSpec X ⋙ MorphismProperty.Over.forget _ _ X ⋙ yoneda ≅
      (ObjectProperty.ι _ : QuasicoherentAlgebra X ⥤ CommMon X.Modules).op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (overFunctions X) :=
  NatIso.ofComponents (fun A ↦ NatIso.ofComponents (fun T ↦
    (relativeSpecOverHomEquiv A.unop T.unop).toIso)
    (fun g ↦ by ext t; exact relativeSpecOverHomEquiv_comp _ g.unop t))
    (fun f ↦ by ext T t; exact relativeSpecOverHomEquiv_comp_relativeSpecMap f.unop t)

variable {X : Scheme.{u}}

/-- The components of `relativeSpecHomIso` are `CommMon.relativeSpecHomEquiv`. -/
lemma relativeSpecHomIso_hom_app_app (A : (QuasicoherentAlgebra X)ᵒᵖ) (T : (Over X)ᵒᵖ)
    (t : T.unop ⟶ (MorphismProperty.Over.forget _ _ X).obj ((relativeSpec X).obj A)) :
    ((relativeSpecHomIso X).hom.app A).app T t =
      A.unop.obj.relativeSpecHomEquiv T.unop.hom ⟨t.left, Over.w t⟩ :=
  (rfl)

/-- The inverse components of `relativeSpecHomIso` are given by `CommMon.relativeSpecLift`. -/
lemma relativeSpecHomIso_inv_app_app (A : (QuasicoherentAlgebra X)ᵒᵖ) (T : (Over X)ᵒᵖ)
    (φ : A.unop.obj ⟶ T.unop.hom.pushforwardStructureAlgebra) :
    ((relativeSpecHomIso X).inv.app A).app T φ =
      Over.homMk (CommMon.relativeSpecLift φ) (CommMon.relativeSpecLift_relativeSpecToBase φ) :=
  (rfl)

variable {T : Scheme.{u}}

/-- **The universal property of relative Spec, in pullback form.** For a quasicoherent algebra
`A` on `X` and a scheme `q : T ⟶ X`, morphisms `T ⟶ Spec_X A` over `X` correspond to morphisms
of `𝒪_T`-algebras `q^* A ⟶ 𝒪_T`. It is `CommMon.relativeSpecHomEquiv` followed by the
adjunction between pullback and pushforward of algebras,
`QuasicoherentAlgebra.pullbackHomEquiv`. -/
def relativeSpecPullbackHomEquiv (A : QuasicoherentAlgebra X) (q : T ⟶ X) :
    {t : T ⟶ A.obj.relativeSpec // t ≫ A.obj.relativeSpecToBase = q} ≃
      (((QuasicoherentAlgebra.pullback q).obj A).obj ⟶ CommMon.trivial T.Modules) :=
  (A.obj.relativeSpecHomEquiv q).trans
    (QuasicoherentAlgebra.pullbackHomEquiv q A (CommMon.trivial T.Modules)).symm

/-- The algebra map `q^* A ⟶ 𝒪_T` of a morphism over `X` is the transpose of its pullback of
regular functions `A ⟶ q_* 𝒪_T`. -/
@[simp]
lemma relativeSpecPullbackHomEquiv_apply (A : QuasicoherentAlgebra X) (q : T ⟶ X)
    (t : {t : T ⟶ A.obj.relativeSpec // t ≫ A.obj.relativeSpecToBase = q}) :
    relativeSpecPullbackHomEquiv A q t =
      (QuasicoherentAlgebra.pullbackHomEquiv q A _).symm (A.obj.relativeSpecHomEquiv q t) :=
  (rfl)

/-- The morphism over `X` of an algebra map `q^* A ⟶ 𝒪_T` is the lift of its transpose
`A ⟶ q_* 𝒪_T`. -/
@[simp]
lemma relativeSpecPullbackHomEquiv_symm_apply_coe (A : QuasicoherentAlgebra X) (q : T ⟶ X)
    (φ : ((QuasicoherentAlgebra.pullback q).obj A).obj ⟶ CommMon.trivial T.Modules) :
    ((relativeSpecPullbackHomEquiv A q).symm φ).1 =
      CommMon.relativeSpecLift (QuasicoherentAlgebra.pullbackHomEquiv q A _ φ) :=
  (rfl)

/-- The pullback form of the universal property is natural in the algebra: precomposing an
algebra map `q^* A ⟶ 𝒪_T` with the pullback of `a : B ⟶ A` corresponds to composing with the
relative-spectrum map of `a`. -/
lemma relativeSpecPullbackHomEquiv_symm_pullback_map_comp {B A : QuasicoherentAlgebra X}
    (a : B ⟶ A) (q : T ⟶ X)
    (φ : ((QuasicoherentAlgebra.pullback q).obj A).obj ⟶ CommMon.trivial T.Modules) :
    ((relativeSpecPullbackHomEquiv B q).symm
        (((QuasicoherentAlgebra.pullback q).map a).hom ≫ φ)).1 =
      ((relativeSpecPullbackHomEquiv A q).symm φ).1 ≫ CommMon.relativeSpecMap a.hom := by
  rw [relativeSpecPullbackHomEquiv_symm_apply_coe, relativeSpecPullbackHomEquiv_symm_apply_coe,
    QuasicoherentAlgebra.pullbackHomEquiv_naturality_left]
  exact CommMon.relativeSpecLift_comp a.hom _

end

end TauCeti.AlgebraicGeometry

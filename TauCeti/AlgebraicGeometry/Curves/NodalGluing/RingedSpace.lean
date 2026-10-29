/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.Iso
public import TauCeti.AlgebraicGeometry.Curves.NodalGluing.StructureSheaf
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import TauCeti.Geometry.RingedSpace.PresheafedSpace.Basic

/-!
# Ringed descent of nodal isomorphisms

The normalization quotient, equipped with its sheaf of matching holomorphic functions, is a
locally ringed space. Its stalks are the holomorphic branch rings off the nodes and the
branch-pair local rings at the nodes.

An analytic isomorphism of normalizations respecting the flag pairs descends to an isomorphism
of these locally ringed spaces. Pullback is precomposition upstairs; in particular it retains
branch interchanges. Identity and composition agree with those of normalization isomorphisms.
This equips actual nodal isomorphisms with their maps on the structure sheaves, in addition to
their underlying homeomorphisms.

## References

* Joel W. Robbin and Dietmar A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 8 (2006), 611–699, for normalization and actual nodal isomorphisms.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped Manifold ContDiff

namespace TauCeti.NodalGluing

open holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  {ι : Type} {Flag : Type*} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
  [∀ i, ChartedSpace H (X i)] (d : FlagPairData ι Flag X)

/-- The normalization quotient with the sheaf of matching holomorphic functions. The
abbreviation retains the existing quotient as the carrier and its existing sheaf as the presheaf. -/
abbrev sheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (GluedCurve d)
  presheaf := (quotientSheaf I (gluedRelSetoid d)).presheaf
  IsSheaf := (quotientSheaf I (gluedRelSetoid d)).property

/-- Restriction in the nodal sheafed space evaluates by inclusion upstairs. -/
@[simp]
theorem sheafedSpace_map_apply {U V : (Opens (GluedCurve d))ᵒᵖ} (h : U ⟶ V)
    (g : (sheafedSpace I d).presheaf.obj U)
    (x : (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj V.unop) :
    (quotientSheafSectionsEquiv I (gluedRelSetoid d) V.unop
      (((sheafedSpace I d).presheaf.map h).hom g)).1 x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d) U.unop g).1
        (Opens.inclusion (leOfHom ((Opens.map (TopCat.quotientMk
          (gluedRelSetoid d))).map h.unop)) x) := by
  exact (congrArg
    (fun f : (holomorphicStructureSheaf I (Σ i, X i)).obj.obj
      (op ((Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj V.unop)) ↦ f x)
    (quotientSheaf_map_val I (gluedRelSetoid d) h.unop g)).trans (map_apply _ _ _)

-- These evaluation lemmas handle categorical composition at the boundary. Their explicit
-- equalities can be composed without unfolding sheaf projections in the descent proofs.
-- Composite evaluation formulas stay out of simp: their left sides reduce by hom_comp.
/-- Restricting after a section map evaluates that map at the included point upstairs. -/
private theorem sheafedSpace_comp_map_apply {R : CommRingCat}
    {U V : (Opens (GluedCurve d))ᵒᵖ} (f : R ⟶ (sheafedSpace I d).presheaf.obj U)
    (h : U ⟶ V) (g : R)
    (x : (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj V.unop) :
    (quotientSheafSectionsEquiv I (gluedRelSetoid d) V.unop
      ((f ≫ (sheafedSpace I d).presheaf.map h).hom g)).1 x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d) U.unop (f.hom g)).1
        (Opens.inclusion (leOfHom ((Opens.map (TopCat.quotientMk
          (gluedRelSetoid d))).map h.unop)) x) := by
  exact sheafedSpace_map_apply I d h (f.hom g) x

/-- Maps into nodal sections agree when their values agree upstairs. -/
@[ext]
theorem sheafedSpace_sectionMap_ext {R : CommRingCat} {U : Opens (GluedCurve d)}
    {f g : R ⟶ (sheafedSpace I d).presheaf.obj (op U)}
    (h : ∀ a x, (quotientSheafSectionsEquiv I (gluedRelSetoid d) U (f.hom a)).1 x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d) U (g.hom a)).1 x) : f = g := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact quotientSheaf_ext I (gluedRelSetoid d) (h a)

/-- Stalks of the normalization quotient are local rings, including at its nodes. -/
instance isLocalRing_quotientStalk [Finite Flag] [∀ i, T2Space (X i)] (z : GluedCurve d) :
    IsLocalRing ((quotientSheaf I (gluedRelSetoid d)).presheaf.stalk z) := by
  induction z using Quotient.inductionOn with | _ x => ?_
  by_cases hx : x ∈ flagPointSet d
  · obtain ⟨f, hx⟩ := (mem_nodeSet d (Quotient.mk _ x)).mp (by
      rw [← Set.mem_preimage, preimage_nodeSet]
      exact hx)
    rw [← hx]
    exact (quotientStalkToNodeEquiv I d f).symm.isLocalRing
  · exact (quotientStalkBranchEquiv I d hx).symm.isLocalRing

/-- The locally ringed space of a nodal normalization quotient. This uses its existing
holomorphic quotient sheaf, with no hypersurface presentation. -/
abbrev locallyRingedSpace [Finite Flag] [∀ i, T2Space (X i)] : LocallyRingedSpace where
  toSheafedSpace := sheafedSpace I d
  isLocalRing := isLocalRing_quotientStalk I d

variable {I d}
  {ι' : Type} {Flag' : Type*} {X' : ι' → Type} [∀ i, TopologicalSpace (X' i)]
  [∀ i, ChartedSpace H (X' i)] {d' : FlagPairData ι' Flag' X'}
  {ι'' : Type} {Flag'' : Type*} {X'' : ι'' → Type} [∀ i, TopologicalSpace (X'' i)]
  [∀ i, ChartedSpace H (X'' i)] {d'' : FlagPairData ι'' Flag'' X''}

namespace Iso

/-- Pullback of matching holomorphic sections by a normalization isomorphism. -/
def pullbackSection (e : Iso I ω d d') (U : Opens (GluedCurve d')) :
    (quotientSheaf I (gluedRelSetoid d')).obj.obj (op U) →+*
      (quotientSheaf I (gluedRelSetoid d)).obj.obj
        (op ((Opens.map (TopCat.ofHom
          ⟨e.gluedCurveHomeomorph, e.gluedCurveHomeomorph.continuous⟩)).obj U)) := by
  let V := (Opens.map (TopCat.ofHom
    ⟨e.gluedCurveHomeomorph, e.gluedCurveHomeomorph.continuous⟩)).obj U
  let W := (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj V
  let W' := (Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj U
  have hW : W = (Opens.map (TopCat.ofHom
      ⟨e, e.toDiffeomorph.contMDiff.continuous⟩)).obj W' := by
    ext x
    exact (congrArg (fun z ↦ z ∈ U) (e.gluedCurveHomeomorph_mk x)).to_iff
  let p := ((holomorphicStructureSheaf I (Σ i, X i)).obj.map (eqToHom hW).op).hom.comp
    ((precomp I _ e e.toDiffeomorph.contMDiff (op W')).comp
      ((quotientSheafι I (gluedRelSetoid d')).hom.app (op U)).hom)
  have hp (g) (x : W) : p g x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d') U g).1
        ⟨e x.1, by
          rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
          exact x.2⟩ :=
    (map_apply _ _ _).trans
      (precomp_apply I _ e e.toDiffeomorph.contMDiff
        (op ((Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj U))
        (((quotientSheafι I (gluedRelSetoid d')).hom.app (op U)).hom g)
        ⟨x.1, by
          exact (congrArg (fun z ↦ z ∈ U) (e.gluedCurveHomeomorph_mk x.1)).to_iff.mp x.2⟩
        |>.trans (congrArg (fun f ↦ f ⟨e x.1, by
          rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
          exact x.2⟩) (quotientSheafι_app_apply I _ U g)))
  exact (quotientSheafSectionsEquiv I (gluedRelSetoid d) V).symm.toRingHom.comp
    (p.codRestrict (quotientSectionSubring I (gluedRelSetoid d) V) (by
      intro g
      rw [mem_quotientSectionSubring]
      intro x y hx hy hxy
      have hm := ((mem_quotientSectionSubring I _ U _).mp
        (quotientSheafSectionsEquiv I (gluedRelSetoid d') U g).2) (e x) (e y)
        ((congrArg (fun z ↦ z ∈ U) (e.gluedCurveHomeomorph_mk x)).to_iff.mp hx)
        ((congrArg (fun z ↦ z ∈ U) (e.gluedCurveHomeomorph_mk y)).to_iff.mp hy)
        ((gluedRelSetoid_r d' _ _).mpr
          ((e.gluedRel_apply_iff x y).mpr ((gluedRelSetoid_r d _ _).mp hxy)))
      exact (hp g ⟨x, hx⟩).trans (hm.trans (hp g ⟨y, hy⟩).symm)))

/-- Pullback evaluates by precomposition on the normalization. -/
@[simp]
theorem pullbackSection_apply (e : Iso I ω d d') (U : Opens (GluedCurve d'))
    (g : (quotientSheaf I (gluedRelSetoid d')).obj.obj (op U))
    (x : (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj
      ((Opens.map (TopCat.ofHom
        ⟨e.gluedCurveHomeomorph, e.gluedCurveHomeomorph.continuous⟩)).obj U)) :
    (quotientSheafSectionsEquiv I (gluedRelSetoid d) _ (e.pullbackSection U g)).1 x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d') U g).1
        ⟨e x.1, by
          rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
          exact x.2⟩ := by
  dsimp only [pullbackSection, RingHom.comp_apply, RingHom.codRestrict_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.apply_symm_apply, RingHom.codRestrict_apply]
  exact (map_apply _ _ _).trans
      (precomp_apply I _ e e.toDiffeomorph.contMDiff
        (op ((Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj U))
        (((quotientSheafι I (gluedRelSetoid d')).hom.app (op U)).hom g)
        ⟨x.1, by
          exact (congrArg (fun z ↦ z ∈ U) (e.gluedCurveHomeomorph_mk x.1)).to_iff.mp x.2⟩
        |>.trans (congrArg (fun f ↦ f ⟨e x.1, by
          rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
          exact x.2⟩) (quotientSheafι_app_apply I _ U g)))

/-- Pullback after a section map evaluates the map at the image on the normalization. -/
private theorem pullbackSection_comp_apply (e : Iso I ω d d') (U : Opens (GluedCurve d'))
    {R : CommRingCat} (f : R ⟶ (sheafedSpace I d').presheaf.obj (op U)) (g : R)
    (x : (Opens.map (TopCat.quotientMk (gluedRelSetoid d))).obj
      ((Opens.map (TopCat.ofHom
        ⟨e.gluedCurveHomeomorph, e.gluedCurveHomeomorph.continuous⟩)).obj U)) :
    (quotientSheafSectionsEquiv I (gluedRelSetoid d) _
      ((f ≫ CommRingCat.ofHom (e.pullbackSection U)).hom g)).1 x =
      (quotientSheafSectionsEquiv I (gluedRelSetoid d') U (f.hom g)).1
        ⟨e x.1, by
          rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
          exact x.2⟩ := by
  exact pullbackSection_apply e U (f.hom g) x

/-- An actual normalization isomorphism descends with its holomorphic structure-sheaf map.
The abbreviation lets the domains of its section maps compute as inverse images downstairs. -/
abbrev sheafedSpaceHom (e : Iso I ω d d') : sheafedSpace I d ⟶ sheafedSpace I d' :=
  InducedCategory.homMk
    { base := (TopCat.ofHom ⟨e.gluedCurveHomeomorph, e.gluedCurveHomeomorph.continuous⟩)
      c :=
        { app := fun U ↦ CommRingCat.ofHom (e.pullbackSection U.unop)
          naturality := by
            intro U V h
            apply sheafedSpace_sectionMap_ext
            intro g x
            let p := (quotientSheafι I (gluedRelSetoid d')).hom ≫
              Functor.whiskerLeft (Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).op
                (homOfContMDiff I _ e e.toDiffeomorph.contMDiff).hom
            have hx : e x.1 ∈
                (Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj V.unop := by
              rw [Opens.mem_map, TopCat.quotientMk_apply, ← e.gluedCurveHomeomorph_mk]
              exact x.2
            have hp (A : (Opens (GluedCurve d'))ᵒᵖ) (a)
                (y : (Opens.map (TopCat.ofHom
                  ⟨e, e.toDiffeomorph.contMDiff.continuous⟩)).obj
                    ((Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj A.unop)) :
                toFun I _ _ ((p.app A).hom a) y =
                  (quotientSheafSectionsEquiv I (gluedRelSetoid d') A.unop a).1
                    ⟨e y.1, y.2⟩ := by
              have ha := congrArg
                (fun k ↦ ((quotientSheafι I (gluedRelSetoid d')).hom.app A) ≫ k)
                (homOfContMDiff_app I _ e e.toDiffeomorph.contMDiff
                  ((Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).op.obj A))
              exact (congrArg (fun k ↦ toFun I _ _ (k.hom a) y) ha).trans
                ((precomp_apply I _ e e.toDiffeomorph.contMDiff _
                (((quotientSheafι I (gluedRelSetoid d')).hom.app A).hom a) y).trans
                  (congrArg (fun f ↦ f ⟨e y.1, y.2⟩)
                    (quotientSheafι_app_apply I _ A.unop a)))
            have hn := congrArg (fun k ↦ toFun I _
              (op ((Opens.map (TopCat.ofHom
                ⟨e, e.toDiffeomorph.contMDiff.continuous⟩)).obj
                  ((Opens.map (TopCat.quotientMk (gluedRelSetoid d'))).obj V.unop)))
              (k.hom g) ⟨x.1, hx⟩) (p.naturality h)
            exact (pullbackSection_comp_apply e V.unop _ g x).trans
              ((hp V _ ⟨x.1, hx⟩).symm.trans (hn.trans
                ((map_apply _ _ _).trans ((hp U g _).trans
                  ((pullbackSection_apply e U.unop g _).symm.trans
                    (sheafedSpace_comp_map_apply I d _ _ g x).symm))))) } }

/-- The map on sections in ringed descent is normalization pullback. -/
@[simp]
theorem sheafedSpaceHom_app (e : Iso I ω d d') (U : Opens (GluedCurve d')) :
    e.sheafedSpaceHom.hom.c.app (op U) = CommRingCat.ofHom (e.pullbackSection U) := (rfl)

-- Existing projection simp rules already normalize this formula.
/-- The descended map on points is the quotient homeomorphism. -/
theorem sheafedSpaceHom_hom_base_apply (e : Iso I ω d d') (z : GluedCurve d) :
    e.sheafedSpaceHom.hom.base z = e.gluedCurveHomeomorph z := (rfl)

-- Keep base equalities opaque: the sectionwise extensionality theorem transports along
-- them, and expanding their proofs forces elaboration through the quotient's ring structures.
private theorem sheafedSpaceHom_refl_base :
    (Iso.refl I ω d).sheafedSpaceHom.hom.base =
      (𝟙 (sheafedSpace I d) : sheafedSpace I d ⟶ sheafedSpace I d).hom.base := by
  simp only [sheafedSpaceHom, InducedCategory.homMk_hom,
    SheafedSpace.id_hom_base, gluedCurveHomeomorph_refl]
  rfl

private theorem sheafedSpaceHom_trans_base (e : Iso I ω d d') (e' : Iso I ω d' d'') :
    (e.trans e').sheafedSpaceHom.hom.base =
      (e.sheafedSpaceHom ≫ e'.sheafedSpaceHom).hom.base := by
  rw [SheafedSpace.comp_hom_base]
  simp only [sheafedSpaceHom, InducedCategory.homMk_hom, gluedCurveHomeomorph_trans]
  rfl

/-- Ringed descent preserves the identity. -/
@[simp]
theorem sheafedSpaceHom_refl : (Iso.refl I ω d).sheafedSpaceHom = 𝟙 (sheafedSpace I d) := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext_of_app sheafedSpaceHom_refl_base fun U ↦ ?_
  rw [sheafedSpaceHom_app, SheafedSpace.id_hom_c_app]
  apply sheafedSpace_sectionMap_ext
  intro g x
  exact (sheafedSpace_comp_map_apply I d _ _ g x).trans
    ((pullbackSection_apply (Iso.refl I ω d) U g _).trans
      (congrArg ((quotientSheafSectionsEquiv I (gluedRelSetoid d) U g).1)
        (Subtype.ext (refl_apply _))))

/-- Ringed descent preserves composition, including the maps on holomorphic sections. -/
@[simp]
theorem sheafedSpaceHom_trans (e : Iso I ω d d') (e' : Iso I ω d' d'') :
    (e.trans e').sheafedSpaceHom = e.sheafedSpaceHom ≫ e'.sheafedSpaceHom := by
  apply InducedCategory.hom_ext
  refine PresheafedSpace.ext_of_app (e.sheafedSpaceHom_trans_base e') fun U ↦ ?_
  rw [sheafedSpaceHom_app, SheafedSpace.comp_hom_c_app, sheafedSpaceHom_app]
  simp only [SheafedSpace.comp_hom_base]
  apply sheafedSpace_sectionMap_ext
  intro g x
  exact (sheafedSpace_comp_map_apply I d _ _ g x).trans
    ((pullbackSection_apply (e.trans e') U g _).trans
      ((congrArg ((quotientSheafSectionsEquiv I (gluedRelSetoid d'') U g).1)
        (Subtype.ext (trans_apply e e' _))).trans
        ((pullbackSection_apply e' U g _).symm.trans
          (pullbackSection_comp_apply e
            ((Opens.map e'.sheafedSpaceHom.hom.base).obj U) _ g x).symm)))

/-- An analytic normalization isomorphism respecting the node pairs descends to an isomorphism
of the holomorphic sheafed spaces. -/
def sheafedSpaceIso (e : Iso I ω d d') : sheafedSpace I d ≅ sheafedSpace I d' where
  hom := e.sheafedSpaceHom
  inv := e.symm.sheafedSpaceHom
  hom_inv_id := by rw [← sheafedSpaceHom_trans, self_trans_symm, sheafedSpaceHom_refl]
  inv_hom_id := by rw [← sheafedSpaceHom_trans, symm_trans_self, sheafedSpaceHom_refl]

/-- The forward map of the descended isomorphism is normalization pullback. -/
@[simp]
theorem sheafedSpaceIso_hom (e : Iso I ω d d') :
    e.sheafedSpaceIso.hom = e.sheafedSpaceHom := (rfl)

/-- The inverse map is the descent of the inverse normalization isomorphism. -/
@[simp]
theorem sheafedSpaceIso_inv (e : Iso I ω d d') :
    e.sheafedSpaceIso.inv = e.symm.sheafedSpaceHom := (rfl)

/-- Reversing normalization reverses its descended sheafed-space isomorphism. -/
@[simp]
theorem sheafedSpaceIso_symm (e : Iso I ω d d') :
    e.symm.sheafedSpaceIso = e.sheafedSpaceIso.symm := by
  apply CategoryTheory.Iso.ext
  rfl

/-- Descent of the identity is the identity sheafed-space isomorphism. -/
@[simp]
theorem sheafedSpaceIso_refl :
    (Iso.refl I ω d).sheafedSpaceIso = CategoryTheory.Iso.refl (sheafedSpace I d) := by
  apply CategoryTheory.Iso.ext
  exact sheafedSpaceHom_refl

/-- Sheafed-space descent preserves composition of normalization isomorphisms. -/
@[simp]
theorem sheafedSpaceIso_trans (e : Iso I ω d d') (e' : Iso I ω d' d'') :
    (e.trans e').sheafedSpaceIso = e.sheafedSpaceIso ≪≫ e'.sheafedSpaceIso := by
  apply CategoryTheory.Iso.ext
  exact sheafedSpaceHom_trans e e'

variable [Finite Flag] [Finite Flag'] [∀ i, T2Space (X i)] [∀ i, T2Space (X' i)]

/-- Ringed descent is an isomorphism of locally ringed spaces: its maps on stalks are local,
also at nodes and when the two branches are interchanged. -/
def locallyRingedSpaceIso (e : Iso I ω d d') : locallyRingedSpace I d ≅ locallyRingedSpace I d' :=
  LocallyRingedSpace.isoOfSheafedSpaceIso e.sheafedSpaceIso

/-- Forgetting locality recovers the constructed sheaf map. -/
@[simp]
theorem locallyRingedSpaceIso_hom_toHom (e : Iso I ω d d') :
    e.locallyRingedSpaceIso.hom.toHom = e.sheafedSpaceHom.hom := (rfl)

-- Existing projection simp rules already normalize this formula.
/-- The descended locally ringed map on points is the quotient homeomorphism. -/
theorem locallyRingedSpaceIso_hom_base_apply (e : Iso I ω d d') (z : GluedCurve d) :
    e.locallyRingedSpaceIso.hom.base z = e.gluedCurveHomeomorph z := (rfl)

/-- The inverse locally ringed map is induced by the inverse normalization isomorphism. -/
@[simp]
theorem locallyRingedSpaceIso_inv_toHom (e : Iso I ω d d') :
    e.locallyRingedSpaceIso.inv.toHom = e.symm.sheafedSpaceHom.hom := (rfl)

/-- Reversing the normalization isomorphism reverses the descended locally ringed isomorphism. -/
@[simp]
theorem locallyRingedSpaceIso_symm (e : Iso I ω d d') :
    e.symm.locallyRingedSpaceIso = e.locallyRingedSpaceIso.symm := by
  apply CategoryTheory.Iso.ext
  apply LocallyRingedSpace.Hom.ext'
  simp only [locallyRingedSpaceIso_hom_toHom, CategoryTheory.Iso.symm_hom,
    locallyRingedSpaceIso_inv_toHom]

/-- Ringed descent of the identity is the identity locally ringed isomorphism. -/
@[simp]
theorem locallyRingedSpaceIso_refl :
    (Iso.refl I ω d).locallyRingedSpaceIso = CategoryTheory.Iso.refl (locallyRingedSpace I d) := by
  apply CategoryTheory.Iso.ext
  apply LocallyRingedSpace.Hom.ext'
  simpa only [locallyRingedSpaceIso_hom_toHom, CategoryTheory.Iso.refl_hom,
    LocallyRingedSpace.id_toHom, SheafedSpace.id_hom] using
    congrArg (fun f ↦ f.hom) (sheafedSpaceHom_refl (I := I) (d := d))

/-- Ringed descent composes as the actual normalization isomorphisms do. -/
@[simp]
theorem locallyRingedSpaceIso_trans [Finite Flag''] [∀ i, T2Space (X'' i)]
    (e : Iso I ω d d') (e' : Iso I ω d' d'') :
    (e.trans e').locallyRingedSpaceIso = e.locallyRingedSpaceIso ≪≫ e'.locallyRingedSpaceIso := by
  apply CategoryTheory.Iso.ext
  apply LocallyRingedSpace.Hom.ext'
  simpa only [CategoryTheory.Iso.trans_hom, LocallyRingedSpace.comp_toHom,
    locallyRingedSpaceIso_hom_toHom, ← InducedCategory.comp_hom] using
    congrArg (fun f ↦ f.hom) (e.sheafedSpaceHom_trans e')

end Iso

end TauCeti.NodalGluing

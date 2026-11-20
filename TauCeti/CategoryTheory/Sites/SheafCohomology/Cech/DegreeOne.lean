/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cokernel
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Injective
import Mathlib.Algebra.Category.Grp.AB

/-!
# Degree-one Leray comparison for a covering of a site

Memberwise first-cohomology vanishing makes the degree-zero Čech quotient map surjective.
The actual complex cokernel of the injective embedding then embeds into the Čech complex of
the quotient sheaf and has the same degree-zero cohomology. Both first-cohomology groups are
therefore cokernels of the same map on global sections.

This is the degree-one part of Leray's comparison, shared by the all-degree dimension shift
and the open-cover API. It follows the degree-one argument in O. Forster,
*Lectures on Riemann Surfaces*, GTM 81, applied to sites using injective Čech acyclicity.
-/

public section
noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {ι : Type v} (U : ι → C) {T : C} (hT : IsTerminal T) (hU : J.CoversTop U)

/-- The actual complex cokernel, used in place of `Č(Q)`. -/
abbrev lerayOneCokerSeq
    (F : Sheaf J AddCommGrpCat.{v}) :=
  ShortComplex.cokernelSequence (cechInjectiveCokernelSequence U F).f

/-- The complex cokernel injects into the Čech complex of the quotient sheaf. -/
def lerayOneCokerToQuotient
    (F : Sheaf J AddCommGrpCat.{v}) :
    (lerayOneCokerSeq U F).X₃ ⟶ (cechInjectiveCokernelSequence U F).X₃ :=
  cokernel.desc _ (cechInjectiveCokernelSequence U F).g (cechInjectiveCokernelSequence U F).zero

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- The map to the Čech complex of the quotient is the descent of the Čech quotient map. -/
lemma lerayOneCokerToQuotient_def (F : Sheaf J AddCommGrpCat.{v}) :
    lerayOneCokerToQuotient U F =
      cokernel.desc _ (cechInjectiveCokernelSequence U F).g
        (cechInjectiveCokernelSequence U F).zero :=
  (rfl)

private instance lerayOneCokerToQuotient_mono
    (F : Sheaf J AddCommGrpCat.{v}) :
    Mono (lerayOneCokerToQuotient U F) :=
  (cechInjectiveCokernelSequence_exact U F).mono_cokernelDesc

/-- Memberwise `H¹` vanishing makes the degree-zero map onto. -/
private lemma epi_lerayOneSeq_g_zero
    (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) : Epi ((cechInjectiveCokernelSequence U F).g.f 0) := by
  -- The mapped short-complex projection is definitionally the Čech map of the quotient.
  change Epi (((cechComplexFunctor U).map (cokernel.π (Injective.ι F)).hom).f 0)
  rw [cechComplexFunctor_map_f]
  have h (a : Fin (0 + 1) → ι) :
      Epi ((cokernel.π (Injective.ι F)).hom.app (op (∏ᶜ fun j ↦ U (a j)))) := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    apply _root_.CategoryTheory.Sheaf.H'.g_hom_app_surjective
      (injectiveCokernelSequence_shortExact F)
    have := hF (a 0)
    let e := ((F.cohomologyPresheaf 1).mapIso
      (productUniqueIso (fun j : Fin 1 ↦ U (a j))).op).addCommGroupIsoToAddEquiv
    exact e.symm.injective.subsingleton
  let α : Discrete.functor (fun a : Fin 1 → ι ↦
      (Injective.under F).obj.obj (op (∏ᶜ fun j ↦ U (a j)))) ⟶
      Discrete.functor (fun a : Fin 1 → ι ↦
        (cokernel (Injective.ι F)).obj.obj (op (∏ᶜ fun j ↦ U (a j)))) :=
    Discrete.natTrans fun a ↦ (cokernel.π (Injective.ι F)).hom.app
      (op (∏ᶜ fun j ↦ U (a.as j)))
  have (a : Discrete (Fin 1 → ι)) : Epi (α.app a) := h a.as
  have : Epi α := NatTrans.epi_of_epi_app α
  -- The product map in degree zero is the limit map of the discrete diagram α;
  -- `Pi.map` is defined using this limit, with no separate comparison morphism.
  change Epi (lim.map α)
  exact Functor.map_epi _ _

/-- The cokernel comparison is an isomorphism in degree zero. -/
private lemma isIso_lerayOneCokerToQuotient_zero
    (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) : IsIso ((lerayOneCokerToQuotient U F).f 0) := by
  have hcomp : (lerayOneCokerSeq U F).g.f 0 ≫ (lerayOneCokerToQuotient U F).f 0 =
      (cechInjectiveCokernelSequence U F).g.f 0 := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg
      (fun f : (cechInjectiveCokernelSequence U F).X₂ ⟶ (cechInjectiveCokernelSequence U F).X₃ ↦
        f.f 0)
      (cokernel.π_desc (cechInjectiveCokernelSequence U F).f (cechInjectiveCokernelSequence U F).g
        (cechInjectiveCokernelSequence U F).zero)
  have hE := epi_lerayOneSeq_g_zero U F hF
  -- Supply the degree-zero epimorphism explicitly: the short-complex and evaluated
  -- Čech presentations have semireducible object types, beyond instance-search transparency.
  have : Epi ((lerayOneCokerToQuotient U F).f 0) :=
    @epi_of_epi_fac _ _ _ _ _ _ _ _ hE hcomp
  have : Mono ((lerayOneCokerToQuotient U F).f 0) := by
    have : Mono (lerayOneCokerToQuotient U F) := lerayOneCokerToQuotient_mono U F
    infer_instance
  exact isIso_of_mono_of_epi _

/-- The zero cohomology of the complex cokernel is the global sections of `Q`. -/
def lerayOneZeroIso (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (lerayOneCokerSeq U F).X₃.homology 0 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} (cokernel (Injective.ι F)) 0) := by
  have : IsIso ((lerayOneCokerToQuotient U F).f 0) :=
    isIso_lerayOneCokerToQuotient_zero U F hF
  have := CochainComplex.isIso_homologyMap_zero_of_mono (lerayOneCokerToQuotient U F)
  exact asIso (HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0) ≪≫
    homologyZeroCechIso U hT hU (cokernel (Injective.ι F))

/-- The zero-degree comparison is induced by the map from the complex cokernel to the
Čech complex of the quotient sheaf, followed by its global-sections identification. -/
lemma lerayOneZeroIso_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (lerayOneZeroIso U hT hU F hF).hom =
      HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0 ≫
        (homologyZeroCechIso U hT hU (cokernel (Injective.ι F))).hom := by
  simp only [lerayOneZeroIso, Iso.trans_hom, asIso_hom]

/-- The degree-zero identification takes the cokernel projection to the global-sections map. -/
@[reassoc]
private lemma homologyMap_comp_lerayOneZeroIso_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    HomologicalComplex.homologyMap (lerayOneCokerSeq U F).g 0 ≫
        (lerayOneZeroIso U hT hU F hF).hom =
      (homologyZeroCechIso U hT hU (Injective.under F)).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map (cokernel.π (Injective.ι F)) 0) := by
  simp only [lerayOneZeroIso, Iso.trans_hom, asIso_hom,
    ← HomologicalComplex.homologyMap_comp_assoc]
  -- These abbreviations expose the chosen cokernel projection and its universal desc.
  rw [show (lerayOneCokerSeq U F).g ≫ lerayOneCokerToQuotient U F =
      (cechInjectiveCokernelSequence U F).g from cokernel.π_desc _ _ _]
  exact homologyMap_comp_homologyZeroCechIso_hom U hT hU (cokernel.π (Injective.ι F))

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- The Čech connecting map is onto because the injective sheaf has no Čech cohomology in
positive degrees. -/
lemma epi_lerayOneCokerSeq_δ
    (F : Sheaf J AddCommGrpCat.{v}) :
    Epi ((cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 (by simp)) :=
  (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).epi_δ 0 1 _
    (exactAt_cechComplexFunctor_obj_obj_of_injective U (Injective.under F) 0).isZero_homology

/-- **Degree-one Leray comparison.** Vanishing of first cohomology on the individual members
of a family covering the terminal object suffices to identify Čech and sheaf first cohomology.
No acyclicity of higher products is assumed. -/
def homologyCechComplexIsoHOne (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{v} F 1) := by
  have := epi_lerayOneCokerSeq_δ U F
  have : Epi (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
      (injectiveCokernelSequence_shortExact F) 0 1 rfl)) :=
    (AddCommGrpCat.epi_iff_surjective _).2 (_root_.CategoryTheory.Sheaf.H.δ_surjective
      (injectiveCokernelSequence_shortExact F) 0 1 rfl inferInstance)
  have hEC := (cokernelSequence_shortExact
    (cechInjectiveCokernelSequence U F).f).homology_exact₃ 0 1 (by simp)
  have hEH := _root_.CategoryTheory.Sheaf.H.longSequence_exact₃'
    (injectiveCokernelSequence_shortExact F) 0 1 rfl
  exact CokernelCofork.mapIsoOfIsColimit hEC.gIsCokernel hEH.gIsCokernel
    (Arrow.isoMk (homologyZeroCechIso U hT hU (Injective.under F))
      (lerayOneZeroIso U hT hU F hF) (homologyMap_comp_lerayOneZeroIso_hom U hT hU F hF).symm)

/-- The comparison intertwines the two connecting maps. -/
@[reassoc]
lemma lerayOneCokerSeq_δ_comp_iso_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 (by simp) ≫
        (homologyCechComplexIsoHOne U hT hU F hF).hom =
      (lerayOneZeroIso U hT hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
  simp only [homologyCechComplexIsoHOne, CokernelCofork.mapIsoOfIsColimit_hom]
  conv_lhs =>
    arg 1
    rw [← CokernelCofork.π_ofπ
      (HomologicalComplex.homologyMap (lerayOneCokerSeq U F).g 0)
      ((cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 (by simp))
      ((cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).comp_δ 0 1 (by simp))]
  rw [CokernelCofork.π_mapOfIsColimit]
  -- `Arrow.isoMk` stores the chosen zero-degree comparison as its right component,
  -- and `CokernelCofork.ofπ` stores the connecting map as its projection.
  rfl

/-- If the Čech injective sequence is short exact, the memberwise degree-one comparison
also intertwines its connecting map with the sheaf connecting map. -/
@[reassoc]
lemma δ_comp_homologyCechComplexIsoHOne_hom (F : Sheaf J AddCommGrpCat.{v})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hS : (cechInjectiveCokernelSequence U F).ShortExact) :
    hS.δ 0 1 rfl ≫ (homologyCechComplexIsoHOne U hT hU F hF).hom =
      (homologyZeroCechIso U hT hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
  have h01 : (ComplexShape.up ℕ).Rel 0 1 := by simp
  let φ : lerayOneCokerSeq U F ⟶ cechInjectiveCokernelSequence U F :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := lerayOneCokerToQuotient U F
      comm₁₂ := by
        -- Expose the identical first two objects of the mapped and cokernel sequences;
        -- rewriting cannot match identity composition through their semireducible projections.
        change 𝟙 _ ≫ (cechInjectiveCokernelSequence U F).f =
          (cechInjectiveCokernelSequence U F).f ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        -- The second object agrees in the two sequences by their definitions.
        change 𝟙 _ ≫ (cechInjectiveCokernelSequence U F).g =
          cokernel.π (cechInjectiveCokernelSequence U F).f ≫
            cokernel.desc (cechInjectiveCokernelSequence U F).f
              (cechInjectiveCokernelSequence U F).g (cechInjectiveCokernelSequence U F).zero
        rw [Category.id_comp, cokernel.π_desc] }
  have hd := HomologicalComplex.HomologySequence.δ_naturality φ
    (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f) hS 0 1 h01
  have hid : HomologicalComplex.homologyMap φ.τ₁ 1 =
      𝟙 ((lerayOneCokerSeq U F).X₁.homology 1) :=
    HomologicalComplex.homologyMap_id _ _
  -- Use typed congruence rather than rewriting through the semireducible objects
  -- stored in the two short complexes. Both first components are the original Čech complex.
  have hd' : (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 h01 =
      HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0 ≫ hS.δ 0 1 rfl := by
    have hi := congrArg (fun f : (lerayOneCokerSeq U F).X₁.homology 1 ⟶
        (lerayOneCokerSeq U F).X₁.homology 1 ↦
      (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 h01 ≫ f) hid
    exact (hi.trans (Category.comp_id _)).symm.trans hd
  have : IsIso ((lerayOneCokerToQuotient U F).f 0) :=
    isIso_lerayOneCokerToQuotient_zero U F hF
  have := CochainComplex.isIso_homologyMap_zero_of_mono (lerayOneCokerToQuotient U F)
  apply (cancel_epi (HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0)).mp
  rw [← Category.assoc, ← hd']
  exact (lerayOneCokerSeq_δ_comp_iso_hom U hT hU F hF).trans
    (by simp only [lerayOneZeroIso_hom, Category.assoc])

end TauCeti.CategoryTheory

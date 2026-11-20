/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.DegreeZero
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Cokernel
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Injective
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Degree-one Leray comparison for a covering of a site

Memberwise first-cohomology vanishing makes the degree-zero Čech quotient map surjective.
The actual complex cokernel of the injective embedding then embeds into the Čech complex of
the quotient sheaf and has the same degree-zero cohomology. Both first-cohomology groups are
therefore cokernels of the same map on global sections.

This is the degree-one part of Leray's comparison, shared by the all-degree dimension shift
and the open-cover API. The comparison is natural in the coefficient sheaf and compatible
with refinements between memberwise acyclic coverings. For module coefficients, it also gives
vanishing of fixed-cover Čech first cohomology from vanishing sheaf first cohomology.
It follows the degree-one argument in O. Forster,
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

section Naturality

variable {κ : Type v} (V : κ → C)
  {F G : Sheaf J AddCommGrpCat.{v}}

/-- Any map of the left exact Čech sequences induces a map of their actual cokernel sequences. -/
private def lerayOneCokerSeqHom
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G) :
    lerayOneCokerSeq U F ⟶ lerayOneCokerSeq V G where
  τ₁ := φ.τ₁
  τ₂ := φ.τ₂
  τ₃ := cokernel.map (cechInjectiveCokernelSequence U F).f (cechInjectiveCokernelSequence V G).f
    φ.τ₁ φ.τ₂ φ.comm₁₂
  comm₁₂ := φ.comm₁₂
  comm₂₃ := (cokernel.π_desc _ _ _).symm

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- The cokernel-to-quotient comparisons commute with a map of Čech sequences. -/
private lemma lerayOneCokerSeqHom_comp_toQuotient
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G) :
    (lerayOneCokerSeqHom U V φ).τ₃ ≫ lerayOneCokerToQuotient V G =
      lerayOneCokerToQuotient U F ≫ φ.τ₃ := by
  rw [lerayOneCokerToQuotient_def, lerayOneCokerToQuotient_def]
  exact cokernel.map_desc _ _ _ _ _ _ _ _ _ φ.comm₂₃ φ.comm₁₂

/-- The degree-zero identification is natural whenever the global-sections comparison is. -/
@[reassoc]
private lemma lerayOneCokerSeqHom_comp_zeroIso (hU : J.CoversTop U) (hV : J.CoversTop V)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G)
    (g : cokernel (Injective.ι F) ⟶ cokernel (Injective.ι G))
    (hφ : HomologicalComplex.homologyMap φ.τ₃ 0 ≫
        (homologyZeroCechIso V hT hV (cokernel (Injective.ι G))).hom =
      (homologyZeroCechIso U hT hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0)) :
    HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
        (lerayOneZeroIso V hT hV G hG).hom =
      (lerayOneZeroIso U hT hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  simp only [lerayOneZeroIso_hom]
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    lerayOneCokerSeqHom_comp_toQuotient, HomologicalComplex.homologyMap_comp, Category.assoc]
  exact (_ ≫= hφ).trans (Category.assoc _ _ _).symm

/-- Naturality of the degree-one comparison follows from the two long exact sequences. -/
private lemma lerayOneIso_naturality
    (hU : J.CoversTop U) (hV : J.CoversTop V)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G)
    (m : injectiveCokernelSequence F ⟶ injectiveCokernelSequence G)
    (hφ : HomologicalComplex.homologyMap φ.τ₃ 0 ≫
        (homologyZeroCechIso V hT hV (cokernel (Injective.ι G))).hom =
      (homologyZeroCechIso U hT hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₃ 0)) :
    HomologicalComplex.homologyMap φ.τ₁ 1 ≫ (homologyCechComplexIsoHOne V hT hV G hG).hom =
      (homologyCechComplexIsoHOne U hT hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₁ 1) := by
  have h01 : (ComplexShape.up ℕ).Rel 0 1 := by simp
  let dU : (lerayOneCokerSeq U F).X₃.homology 0 ⟶
      ((cechComplexFunctor U).obj F.obj).homology 1 :=
    (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f).δ 0 1 h01
  let dV : (lerayOneCokerSeq V G).X₃.homology 0 ⟶
      ((cechComplexFunctor V).obj G.obj).homology 1 :=
    (cokernelSequence_shortExact (cechInjectiveCokernelSequence V G).f).δ 0 1 h01
  have : Epi dU := epi_lerayOneCokerSeq_δ U F
  have hd : dU ≫ HomologicalComplex.homologyMap φ.τ₁ 1 =
      HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫ dV :=
    HomologicalComplex.HomologySequence.δ_naturality
      (lerayOneCokerSeqHom U V φ)
      (cokernelSequence_shortExact (cechInjectiveCokernelSequence U F).f)
      (cokernelSequence_shortExact (cechInjectiveCokernelSequence V G).f) 0 1 h01
  have hdU : dU ≫ (homologyCechComplexIsoHOne U hT hU F hF).hom =
      (lerayOneZeroIso U hT hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom U hT hU F hF
  have hdV : dV ≫ (homologyCechComplexIsoHOne V hT hV G hG).hom =
      (lerayOneZeroIso V hT hV G hG).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact G) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom V hT hV G hG
  have hδ : AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₃ 0) ≫
      AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
        (injectiveCokernelSequence_shortExact G) 0 1 rfl) =
      AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
        (injectiveCokernelSequence_shortExact F) 0 1 rfl) ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₁ 1) := by
    ext x
    exact _root_.CategoryTheory.Sheaf.H.δ_naturality 0 1 rfl
      (injectiveCokernelSequence_shortExact F) (injectiveCokernelSequence_shortExact G) m x
  apply (cancel_epi dU).mp
  rw [← Category.assoc, hd, Category.assoc, hdV, ← Category.assoc,
    lerayOneCokerSeqHom_comp_zeroIso U hT V hU hV hF hG φ m.τ₃ hφ, Category.assoc,
    hδ, ← Category.assoc, ← hdU, Category.assoc]

/-- Degree-one Leray comparison is natural in the coefficient sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoHOne_hom
    (hU : J.CoversTop U) (f : F ⟶ G)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (U i))) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
        (homologyCechComplexIsoHOne U hT hU G hG).hom =
      (homologyCechComplexIsoHOne U hT hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f 1) := by
  simpa only [cechInjectiveCokernelSequenceMap_τ₁, injectiveCokernelSequenceMap_τ₁] using
    lerayOneIso_naturality U hT U hU hU hF hG (cechInjectiveCokernelSequenceMap U f)
      (injectiveCokernelSequenceMap f)
      (by
        rw [cechInjectiveCokernelSequenceMap_τ₃]
        exact homologyMap_comp_homologyZeroCechIso_hom U hT hU
          (injectiveCokernelSequenceMap f).τ₃)

/-- Degree-one Leray comparison commutes with the actual map induced by a cover refinement. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom
    (hU : J.CoversTop U) (hV : J.CoversTop V)
    (F : Sheaf J AddCommGrpCat.{v})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫
        (homologyCechComplexIsoHOne U hT hU F hFU).hom =
      (homologyCechComplexIsoHOne V hT hV F hFV).hom := by
  have h := lerayOneIso_naturality V hT U hV hU hFV hFU
    (cechInjectiveCokernelSequenceRefinement U V F φ) (𝟙 (injectiveCokernelSequence F))
    (by
      simpa only [cechInjectiveCokernelSequenceRefinement_τ₁,
        cechInjectiveCokernelSequenceRefinement_τ₃, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using
        homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom U hT hU V hV
          (cokernel (Injective.ι F)) φ)
  simpa only [cechInjectiveCokernelSequenceRefinement_τ₁,
    cechInjectiveCokernelSequenceRefinement_τ₃, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using h

/-- A refinement between memberwise `H¹`-acyclic covers induces an isomorphism on `H¹`. -/
theorem isIso_homologyMap_cechComplexMap_one
    (hU : J.CoversTop U) (hV : J.CoversTop V)
    (F : Sheaf J AddCommGrpCat.{v})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    IsIso (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1) := by
  have h := homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom U terminalIsTerminal V
    hU hV F hFU hFV φ
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

end Naturality

end TauCeti.CategoryTheory

namespace CategoryTheory.Sheaf

open TauCeti.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [EnoughInjectives (Sheaf J AddCommGrpCat.{v})]
  [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] {R : Type v} [Ring R]
  [J.HasSheafCompose (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})]
  (F : Sheaf J (ModuleCat.{v} R))

/-- **Leray covers have the cohomology of the sheaf.** Let `F` be a sheaf of modules whose
underlying sheaf of abelian groups has `H¹(F) = 0`. A covering family whose members `U i`
have `H¹(U i, F) = 0` has vanishing first Čech cohomology, with module coefficients. -/
theorem isZero_homology_one_cechComplex_of_subsingleton_H {ι : Type v}
    (U : ι → C) (hU : J.CoversTop U)
    (hF : ∀ i, Subsingleton (Sheaf.H'
      ((sheafCompose _ (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).obj F) 1 (U i)))
    (h : Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})).obj F) 1)) :
    IsZero (((cechComplexFunctor U).obj F.obj).homology 1) := by
  let G : ModuleCat.{v} R ⥤ AddCommGrpCat.{v} := forget₂ _ _
  let FAb := (sheafCompose J G).obj F
  have hFAb : FAb.obj = F.obj ⋙ G := rfl
  have hAb : IsZero (((cechComplexFunctor U).obj FAb.obj).homology 1) :=
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (Sheaf.H FAb 1))).of_iso
      (TauCeti.CategoryTheory.homologyCechComplexIsoHOne U terminalIsTerminal hU FAb hF)
  rw [hFAb] at hAb
  -- forgetting the module structure commutes with forming the Čech complex and its homology
  have hG : IsZero (G.obj (((cechComplexFunctor U).obj F.obj).homology 1)) :=
    hAb.of_iso (((((cechComplexFunctor U).obj F.obj).sc 1).mapHomologyIso G).symm ≪≫
      HomologicalComplex.homologyMapIso ((cechComplexFunctorMapIso U G).app F.obj) 1)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact hG.eq_of_src _ _

end CategoryTheory.Sheaf

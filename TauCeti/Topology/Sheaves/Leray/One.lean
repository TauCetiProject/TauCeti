/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Topology.Sheaves.Leray.Basic
public import TauCeti.Topology.Sheaves.Flasque.Basic
import Mathlib.Algebra.Category.Grp.AB
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.CategoryTheory.Limits.Lattice
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact

/-!
# Leray comparison in degree one

For a finite open cover, vanishing of `H¹(Uᵢ,F)` on the individual members suffices to compare
Čech `H¹` with sheaf `H¹`. Acyclicity of finite intersections in positive degrees is not needed.

Embed `F` into an injective sheaf `I` with quotient `Q`. The Čech sequence is left exact in every
degree, and the map `Č⁰(I) → Č⁰(Q)` is onto by the memberwise vanishing. Its complex cokernel `R`
therefore embeds into `Č(Q)` and agrees in degree zero. Consequently `H⁰(R) ≅ H⁰(Q)`, and the
long exact sequence for `0 → Č(F) → Č(I) → R → 0` identifies both degree-one groups as the
cokernel of the same global-sections map.

## Main results

* `homologyCechComplexIsoHOne`: the comparison assuming memberwise `H¹` vanishing.
* `homologyCechComplexIsoH_one_eq_homologyCechComplexIsoHOne`: agreement with all-degree Leray.
* `homologyMap_comp_homologyCechComplexIsoHOne_hom`: naturality in the coefficient sheaf.
* `homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom`: refinement compatibility.
* `isIso_homologyMap_cechComplexMap_one`: refinement maps between such covers are isomorphisms.

The existing `cechComplexHomologyMap_eq` makes these maps independent of the refinement morphism.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, degree-one Leray comparison.
-/

public section
noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Čech cochains preserve the kernel in the injective cokernel sequence. -/
private lemma lerayOneSeq_exact (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (cechSeq U F).Exact := by
  apply (injectiveCokernelSequence_shortExact F).exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ AddCommGrpCat.{u} ⋙ cechComplexFunctor U) inferInstance inferInstance

/-- The first Čech map is injective. -/
private instance lerayOneSeq_mono (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (cechSeq U F).f := by
  exact Functor.map_mono (sheafToPresheaf _ AddCommGrpCat.{u} ⋙ cechComplexFunctor U)
    (Injective.ι F)

/-- The actual complex cokernel, used in place of `Č(Q)`. -/
private abbrev lerayOneCokerSeq
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.cokernelSequence (cechSeq U F).f

/-- The complex cokernel injects into the Čech complex of the quotient sheaf. -/
private def lerayOneCokerToQuotient
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (lerayOneCokerSeq U F).X₃ ⟶ (cechSeq U F).X₃ :=
  cokernel.desc _ (cechSeq U F).g (cechSeq U F).zero

private instance lerayOneCokerToQuotient_mono
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (lerayOneCokerToQuotient U F) :=
  (lerayOneSeq_exact U F).mono_cokernelDesc

/-- Memberwise `H¹` vanishing makes the degree-zero map onto. -/
private lemma epi_lerayOneSeq_g_zero
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) : Epi ((cechSeq U F).g.f 0) := by
  -- The mapped short-complex projection is definitionally the Čech map of the quotient.
  change Epi (((cechComplexFunctor U).map (cokernel.π (Injective.ι F)).hom).f 0)
  rw [cechComplexFunctor_map_f]
  have h (a : Fin (0 + 1) → ι) :
      Epi ((cokernel.π (Injective.ι F)).hom.app (op (∏ᶜ fun j ↦ U (a j)))) := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    apply _root_.CategoryTheory.Sheaf.H'.g_hom_app_surjective
      (injectiveCokernelSequence_shortExact F)
    have heq : (∏ᶜ fun j : Fin 1 ↦ U (a j)) = U (a 0) := by
      classical
      simp [CompleteLattice.finite_product_eq_finset_image_inf, Finset.univ_unique]
    rw [heq]
    exact hF (a 0)
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
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) : IsIso ((lerayOneCokerToQuotient U F).f 0) := by
  have hcomp : (lerayOneCokerSeq U F).g.f 0 ≫ (lerayOneCokerToQuotient U F).f 0 =
      (cechSeq U F).g.f 0 := by
    rw [← HomologicalComplex.comp_f]
    exact congrArg (fun f : (cechSeq U F).X₂ ⟶ (cechSeq U F).X₃ ↦ f.f 0)
      (cokernel.π_desc (cechSeq U F).f (cechSeq U F).g (cechSeq U F).zero)
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
private def lerayOneZeroIso (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (lerayOneCokerSeq U F).X₃.homology 0 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} (cokernel (Injective.ι F)) 0) := by
  have : IsIso ((lerayOneCokerToQuotient U F).f 0) :=
    isIso_lerayOneCokerToQuotient_zero U F hF
  have := CochainComplex.isIso_homologyMap_zero_of_mono (lerayOneCokerToQuotient U F)
  exact asIso (HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0) ≪≫
    homologyZeroCechIso U hU (cokernel (Injective.ι F))

/-- The degree-zero identification takes the cokernel projection to the global-sections map. -/
@[reassoc]
private lemma homologyMap_comp_lerayOneZeroIso_hom (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    HomologicalComplex.homologyMap (lerayOneCokerSeq U F).g 0 ≫
        (lerayOneZeroIso U hU F hF).hom =
      (homologyZeroCechIso U hU (Injective.under F)).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map (cokernel.π (Injective.ι F)) 0) := by
  simp only [lerayOneZeroIso, Iso.trans_hom, asIso_hom,
    ← HomologicalComplex.homologyMap_comp_assoc]
  -- These abbreviations expose the chosen cokernel projection and its universal desc.
  rw [show (lerayOneCokerSeq U F).g ≫ lerayOneCokerToQuotient U F = (cechSeq U F).g from
    cokernel.π_desc _ _ _]
  exact homologyMap_comp_homologyZeroCechIso_hom U hU (cokernel.π (Injective.ι F))

/-- The Čech connecting map is onto because the injective sheaf is flasque. -/
private lemma epi_lerayOneCokerSeq_δ [Finite ι] (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Epi ((cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 (by simp)) := by
  have : QuasiIso (cechAugmentation U isTerminalTop (Injective.under F).obj) :=
    TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque (Injective.under F) U hU
  apply (cokernelSequence_shortExact (cechSeq U F).f).epi_δ
  exact ((exactAt_iff_of_quasiIsoAt
    (cechAugmentation U isTerminalTop (Injective.under F).obj) 1).mp
    (CochainComplex.exactAt_succ_single_obj _ 0)).isZero_homology

/-- **Degree-one Leray comparison.** Vanishing of `H¹(Uᵢ,F)` on the members of a finite open
cover suffices for `H¹(U,F) ≅ H¹(X,F)`; no acyclicity of intersections is assumed. -/
def homologyCechComplexIsoHOne [Finite ι] (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 1) := by
  have := epi_lerayOneCokerSeq_δ U hU F
  have : Epi (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
      (injectiveCokernelSequence_shortExact F) 0 1 rfl)) :=
    (AddCommGrpCat.epi_iff_surjective _).2 (_root_.CategoryTheory.Sheaf.H.δ_surjective
      (injectiveCokernelSequence_shortExact F) 0 1 rfl inferInstance)
  have hEC := (cokernelSequence_shortExact (cechSeq U F).f).homology_exact₃ 0 1 (by simp)
  have hEH := _root_.CategoryTheory.Sheaf.H.longSequence_exact₃'
    (injectiveCokernelSequence_shortExact F) 0 1 rfl
  exact CokernelCofork.mapIsoOfIsColimit hEC.gIsCokernel hEH.gIsCokernel
    (Arrow.isoMk (homologyZeroCechIso U hU (Injective.under F))
      (lerayOneZeroIso U hU F hF) (homologyMap_comp_lerayOneZeroIso_hom U hU F hF).symm)

/-- The comparison intertwines the two connecting maps. -/
@[reassoc]
private lemma lerayOneCokerSeq_δ_comp_iso_hom [Finite ι] (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    (cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 (by simp) ≫
        (homologyCechComplexIsoHOne U hU F hF).hom =
      (lerayOneZeroIso U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
  simp only [homologyCechComplexIsoHOne, CokernelCofork.mapIsoOfIsColimit_hom]
  conv_lhs =>
    arg 1
    rw [← CokernelCofork.π_ofπ
      (HomologicalComplex.homologyMap (lerayOneCokerSeq U F).g 0)
      ((cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 (by simp))
      ((cokernelSequence_shortExact (cechSeq U F).f).comp_δ 0 1 (by simp))]
  rw [CokernelCofork.π_mapOfIsColimit]
  -- `Arrow.isoMk` stores the chosen zero-degree comparison as its right component,
  -- and `CokernelCofork.ofπ` stores the connecting map as its projection.
  rfl

/-- With the all-degree Leray hypotheses, the degree-one comparison agrees with the
existing all-degree comparison. The memberwise vanishing witness may be chosen independently. -/
lemma homologyCechComplexIsoH_one_eq_homologyCechComplexIsoHOne [Finite ι]
    (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hF₁ : ∀ i, Subsingleton (F.H' 1 (U i))) :
    homologyCechComplexIsoH U hU F hF 1 = homologyCechComplexIsoHOne U hU F hF₁ := by
  have h01 : (ComplexShape.up ℕ).Rel 0 1 := by simp
  have hS : (cechSeq U F).ShortExact :=
    shortExact_map_cechComplexFunctor U
      ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})) fun m a ↦
        _root_.CategoryTheory.Sheaf.H'.shortExact_map_sheafSections
          (injectiveCokernelSequence_shortExact F) _
          (CompleteLattice.finite_product_of_forall_finset_inf
            (p := fun W ↦ Subsingleton (F.H' 1 W)) U (fun t ht ↦ hF t ht 0) a)
  let φ : lerayOneCokerSeq U F ⟶ cechSeq U F :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := lerayOneCokerToQuotient U F
      comm₁₂ := by
        -- Expose the identical first two objects of the mapped and cokernel sequences;
        -- rewriting cannot match identity composition through their semireducible projections.
        change 𝟙 _ ≫ (cechSeq U F).f = (cechSeq U F).f ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        -- The second object agrees in the two sequences by their definitions.
        change 𝟙 _ ≫ (cechSeq U F).g =
          cokernel.π (cechSeq U F).f ≫
            cokernel.desc (cechSeq U F).f (cechSeq U F).g (cechSeq U F).zero
        rw [Category.id_comp, cokernel.π_desc] }
  have hd := HomologicalComplex.HomologySequence.δ_naturality φ
    (cokernelSequence_shortExact (cechSeq U F).f) hS 0 1 h01
  have : Epi ((cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01) :=
    epi_lerayOneCokerSeq_δ U hU F
  have hid : HomologicalComplex.homologyMap φ.τ₁ 1 =
      𝟙 ((lerayOneCokerSeq U F).X₁.homology 1) :=
    HomologicalComplex.homologyMap_id _ _
  -- Use typed congruence rather than rewriting through the semireducible objects
  -- stored in the two short complexes. Both first components are the original Čech complex.
  have hd' : (cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01 =
      HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0 ≫ hS.δ 0 1 rfl := by
    have hi := congrArg (fun f : (lerayOneCokerSeq U F).X₁.homology 1 ⟶
        (lerayOneCokerSeq U F).X₁.homology 1 ↦
      (cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01 ≫ f) hid
    exact (hi.trans (Category.comp_id _)).symm.trans hd
  apply Iso.ext
  apply (cancel_epi ((cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01)).mp
  rw [lerayOneCokerSeq_δ_comp_iso_hom]
  calc
    (cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01 ≫
        (homologyCechComplexIsoH U hU F hF 1).hom =
        HomologicalComplex.homologyMap (lerayOneCokerToQuotient U F) 0 ≫
          (hS.δ 0 1 rfl ≫ (homologyCechComplexIsoH U hU F hF 1).hom) := by
      exact (congrArg (fun f : (lerayOneCokerSeq U F).X₃.homology 0 ⟶
          ((cechComplexFunctor U).obj F.obj).homology 1 ↦
        f ≫ (homologyCechComplexIsoH U hU F hF 1).hom) hd').trans (Category.assoc _ _ _)
    _ = (lerayOneZeroIso U hU F hF₁).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
      rw [δ_comp_homologyCechComplexIsoH_one_hom]
      simp only [lerayOneZeroIso, Iso.trans_hom, asIso_hom, Category.assoc]

section Naturality

variable {κ : Type u} (V : κ → Opens X)
  {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Any map of the left exact Čech sequences induces a map of their actual cokernel sequences. -/
private def lerayOneCokerSeqHom (φ : cechSeq U F ⟶ cechSeq V G) :
    lerayOneCokerSeq U F ⟶ lerayOneCokerSeq V G where
  τ₁ := φ.τ₁
  τ₂ := φ.τ₂
  τ₃ := cokernel.map (cechSeq U F).f (cechSeq V G).f φ.τ₁ φ.τ₂ φ.comm₁₂.symm
  comm₁₂ := φ.comm₁₂
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The cokernel-to-quotient comparisons commute with a map of Čech sequences. -/
private lemma lerayOneCokerSeqHom_comp_toQuotient (φ : cechSeq U F ⟶ cechSeq V G) :
    (lerayOneCokerSeqHom U V φ).τ₃ ≫ lerayOneCokerToQuotient V G =
      lerayOneCokerToQuotient U F ≫ φ.τ₃ := by
  exact cokernel.map_desc _ _ _ _ _ _ _ _ _ φ.comm₁₂.symm φ.comm₂₃.symm

/-- The degree-zero identification is natural whenever the global-sections comparison is. -/
@[reassoc]
private lemma lerayOneCokerSeqHom_comp_zeroIso (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechSeq U F ⟶ cechSeq V G)
    (g : cokernel (Injective.ι F) ⟶ cokernel (Injective.ι G))
    (hφ : HomologicalComplex.homologyMap φ.τ₃ 0 ≫
        (homologyZeroCechIso V hV (cokernel (Injective.ι G))).hom =
      (homologyZeroCechIso U hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0)) :
    HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
        (lerayOneZeroIso V hV G hG).hom =
      (lerayOneZeroIso U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  simp only [lerayOneZeroIso, Iso.trans_hom, asIso_hom]
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    lerayOneCokerSeqHom_comp_toQuotient, HomologicalComplex.homologyMap_comp, Category.assoc, hφ]
  simp only [Category.assoc]

/-- Naturality of the degree-one comparison follows from the two long exact sequences. -/
private lemma lerayOneIso_naturality [Finite ι] [Finite κ]
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechSeq U F ⟶ cechSeq V G)
    (m : injectiveCokernelSequence F ⟶ injectiveCokernelSequence G)
    (hφ : HomologicalComplex.homologyMap φ.τ₃ 0 ≫
        (homologyZeroCechIso V hV (cokernel (Injective.ι G))).hom =
      (homologyZeroCechIso U hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₃ 0)) :
    HomologicalComplex.homologyMap φ.τ₁ 1 ≫ (homologyCechComplexIsoHOne V hV G hG).hom =
      (homologyCechComplexIsoHOne U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₁ 1) := by
  have h01 : (ComplexShape.up ℕ).Rel 0 1 := by simp
  let dU : (lerayOneCokerSeq U F).X₃.homology 0 ⟶
      ((cechComplexFunctor U).obj F.obj).homology 1 :=
    (cokernelSequence_shortExact (cechSeq U F).f).δ 0 1 h01
  let dV : (lerayOneCokerSeq V G).X₃.homology 0 ⟶
      ((cechComplexFunctor V).obj G.obj).homology 1 :=
    (cokernelSequence_shortExact (cechSeq V G).f).δ 0 1 h01
  have : Epi dU := epi_lerayOneCokerSeq_δ U hU F
  have hd : dU ≫ HomologicalComplex.homologyMap φ.τ₁ 1 =
      HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫ dV :=
    HomologicalComplex.HomologySequence.δ_naturality
      (lerayOneCokerSeqHom U V φ) (cokernelSequence_shortExact (cechSeq U F).f)
      (cokernelSequence_shortExact (cechSeq V G).f) 0 1 h01
  have hdU : dU ≫ (homologyCechComplexIsoHOne U hU F hF).hom =
      (lerayOneZeroIso U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom U hU F hF
  have hdV : dV ≫ (homologyCechComplexIsoHOne V hV G hG).hom =
      (lerayOneZeroIso V hV G hG).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact G) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom V hV G hG
  apply (cancel_epi dU).mp
  calc
    dU ≫ (HomologicalComplex.homologyMap φ.τ₁ 1 ≫
        (homologyCechComplexIsoHOne V hV G hG).hom) =
        HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
          (dV ≫ (homologyCechComplexIsoHOne V hV G hG).hom) := by
      rw [← Category.assoc, hd, Category.assoc]
    _ = HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
        ((lerayOneZeroIso V hV G hG).hom ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
            (injectiveCokernelSequence_shortExact G) 0 1 rfl)) := by rw [hdV]
    _ = (lerayOneZeroIso U hU F hF).hom ≫
        (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₃ 0) ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
            (injectiveCokernelSequence_shortExact G) 0 1 rfl)) := by
      rw [← Category.assoc,
        lerayOneCokerSeqHom_comp_zeroIso U V hU hV hF hG φ m.τ₃ hφ, Category.assoc]
    _ = (lerayOneZeroIso U hU F hF).hom ≫
        (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) ≫
            AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₁ 1)) := by
      congr 1
      ext x
      exact _root_.CategoryTheory.Sheaf.H.δ_naturality 0 1 rfl
        (injectiveCokernelSequence_shortExact F) (injectiveCokernelSequence_shortExact G) m x
    _ = dU ≫ ((homologyCechComplexIsoHOne U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₁ 1)) := by
      rw [← Category.assoc, ← hdU, Category.assoc]

/-- Degree-one Leray comparison is natural in the coefficient sheaf. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoHOne_hom [Finite ι]
    (hU : ⨆ i, U i = ⊤) (f : F ⟶ G)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (U i))) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
        (homologyCechComplexIsoHOne U hU G hG).hom =
      (homologyCechComplexIsoHOne U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f 1) := by
  simpa only [cechSeqMap_τ₁, injectiveCokernelSequenceMap_τ₁] using
    lerayOneIso_naturality U U hU hU hF hG (cechSeqMap U f) (injectiveCokernelSequenceMap f)
      (by
        rw [cechSeqMap_τ₃]
        exact homologyMap_comp_homologyZeroCechIso_hom U hU
          (injectiveCokernelSequenceMap f).τ₃)

/-- A cover refinement induces a map of the left exact Čech sequences. -/
private def lerayOneSeqRefinement
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    cechSeq V F ⟶ cechSeq U F where
  τ₁ := cechComplexMap F.obj φ
  τ₂ := cechComplexMap (Injective.under F).obj φ
  τ₃ := cechComplexMap (cokernel (Injective.ι F)).obj φ
  comm₁₂ := (cechComplexMap_naturality F.obj (Injective.ι F).hom φ).symm
  comm₂₃ := (cechComplexMap_naturality (Injective.under F).obj
    (cokernel.π (Injective.ι F)).hom φ).symm

/-- Degree-one Leray comparison commutes with the actual map induced by a cover refinement. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom
    [Finite ι] [Finite κ] (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫
        (homologyCechComplexIsoHOne U hU F hFU).hom =
      (homologyCechComplexIsoHOne V hV F hFV).hom := by
  have h := lerayOneIso_naturality V U hV hU hFV hFU
    (lerayOneSeqRefinement U V F φ) (𝟙 (injectiveCokernelSequence F))
    (by
      simpa only [lerayOneSeqRefinement, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using
        homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom U hU V hV
          (cokernel (Injective.ι F)) φ)
  simpa only [lerayOneSeqRefinement, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using h

/-- A refinement between memberwise `H¹`-acyclic finite covers induces an isomorphism on `H¹`. -/
theorem isIso_homologyMap_cechComplexMap_one
    [Finite ι] [Finite κ] (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    IsIso (HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1) := by
  have h := homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom U V hU hV F hFU hFV φ
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

end Naturality

end TauCeti.Topology

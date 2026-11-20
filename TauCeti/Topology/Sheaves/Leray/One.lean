/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Topology.Sheaves.Leray.Basic
import Mathlib.Algebra.Category.Grp.AB
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Leray comparison in degree one

For an open cover, vanishing of `H¹(Uᵢ,F)` on the individual members suffices to compare
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

/-- **Degree-one Leray comparison.** Vanishing of `H¹(Uᵢ,F)` on the members of an open
cover suffices for `H¹(U,F) ≅ H¹(X,F)`; no acyclicity of intersections is assumed. -/
def homologyCechComplexIsoHOne (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 1) :=
  CategoryTheory.homologyCechComplexIsoHOne U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF

/-- With the all-degree Leray hypotheses, the degree-one comparison agrees with the
existing all-degree comparison. The memberwise vanishing witness may be chosen independently. -/
lemma homologyCechComplexIsoH_one_eq_homologyCechComplexIsoHOne
    (hU : ⨆ i, U i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hF₁ : ∀ i, Subsingleton (F.H' 1 (U i))) :
    homologyCechComplexIsoH U hU F hF 1 = homologyCechComplexIsoHOne U hU F hF₁ := by
  rw [homologyCechComplexIsoH_def U hU F hF (fun _ a k ↦
    CompleteLattice.finite_product_of_forall_finset_inf
      (p := fun W ↦ Subsingleton (F.H' (k + 1) W)) U (fun t ht ↦ hF t ht k) a)]
  exact CategoryTheory.homologyCechComplexIsoH_one U isTerminalTop
    ((Opens.coversTop_iff X U).2 hU) F _ hF₁

section Naturality

variable {κ : Type u} (V : κ → Opens X)
  {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

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

/-- The cokernel-to-quotient comparisons commute with a map of Čech sequences. -/
private lemma lerayOneCokerSeqHom_comp_toQuotient
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G) :
    (lerayOneCokerSeqHom U V φ).τ₃ ≫ lerayOneCokerToQuotient V G =
      lerayOneCokerToQuotient U F ≫ φ.τ₃ := by
  rw [lerayOneCokerToQuotient_def, lerayOneCokerToQuotient_def]
  exact cokernel.map_desc _ _ _ _ _ _ _ _ _ φ.comm₂₃ φ.comm₁₂

/-- The degree-zero identification is natural whenever the global-sections comparison is. -/
@[reassoc]
private lemma lerayOneCokerSeqHom_comp_zeroIso (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G)
    (g : cokernel (Injective.ι F) ⟶ cokernel (Injective.ι G))
    (hφ : HomologicalComplex.homologyMap φ.τ₃ 0 ≫
        (homologyZeroCechIso V hV (cokernel (Injective.ι G))).hom =
      (homologyZeroCechIso U hU (cokernel (Injective.ι F))).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0)) :
    HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
        (lerayOneZeroIso V isTerminalTop ((Opens.coversTop_iff X V).2 hV) G hG).hom =
      (lerayOneZeroIso U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  simp only [homologyZeroCechIso_def] at hφ
  simp only [lerayOneZeroIso_hom]
  rw [← HomologicalComplex.homologyMap_comp_assoc,
    lerayOneCokerSeqHom_comp_toQuotient, HomologicalComplex.homologyMap_comp, Category.assoc]
  exact (_ ≫= hφ).trans (Category.assoc _ _ _).symm

/-- Naturality of the degree-one comparison follows from the two long exact sequences. -/
private lemma lerayOneIso_naturality
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (V i)))
    (φ : cechInjectiveCokernelSequence U F ⟶ cechInjectiveCokernelSequence V G)
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
  have hdU : dU ≫ (homologyCechComplexIsoHOne U hU F hF).hom =
      (lerayOneZeroIso U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF
  have hdV : dV ≫ (homologyCechComplexIsoHOne V hV G hG).hom =
      (lerayOneZeroIso V isTerminalTop ((Opens.coversTop_iff X V).2 hV) G hG).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact G) 0 1 rfl) :=
    lerayOneCokerSeq_δ_comp_iso_hom V isTerminalTop ((Opens.coversTop_iff X V).2 hV) G hG
  apply (cancel_epi dU).mp
  calc
    dU ≫ (HomologicalComplex.homologyMap φ.τ₁ 1 ≫
        (homologyCechComplexIsoHOne V hV G hG).hom) =
        HomologicalComplex.homologyMap (lerayOneCokerSeqHom U V φ).τ₃ 0 ≫
          ((lerayOneZeroIso V isTerminalTop ((Opens.coversTop_iff X V).2 hV) G hG).hom ≫
            AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
              (injectiveCokernelSequence_shortExact G) 0 1 rfl)) := by
      rw [← Category.assoc, hd, Category.assoc, hdV]
    _ = (lerayOneZeroIso U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF).hom ≫
        (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map m.τ₃ 0) ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
            (injectiveCokernelSequence_shortExact G) 0 1 rfl)) := by
      rw [← Category.assoc,
        lerayOneCokerSeqHom_comp_zeroIso U V hU hV hF hG φ m.τ₃ hφ, Category.assoc]
    _ = (lerayOneZeroIso U isTerminalTop ((Opens.coversTop_iff X U).2 hU) F hF).hom ≫
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
theorem homologyMap_comp_homologyCechComplexIsoHOne_hom
    (hU : ⨆ i, U i = ⊤) (f : F ⟶ G)
    (hF : ∀ i, Subsingleton (F.H' 1 (U i))) (hG : ∀ i, Subsingleton (G.H' 1 (U i))) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
        (homologyCechComplexIsoHOne U hU G hG).hom =
      (homologyCechComplexIsoHOne U hU F hF).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f 1) := by
  simpa only [cechInjectiveCokernelSequenceMap_τ₁, injectiveCokernelSequenceMap_τ₁] using
    lerayOneIso_naturality U U hU hU hF hG (cechInjectiveCokernelSequenceMap U f)
      (injectiveCokernelSequenceMap f)
      (by
        rw [cechInjectiveCokernelSequenceMap_τ₃]
        exact homologyMap_comp_homologyZeroCechIso_hom U hU
          (injectiveCokernelSequenceMap f).τ₃)

/-- Degree-one Leray comparison commutes with the actual map induced by a cover refinement. -/
@[reassoc]
theorem homologyMap_cechComplexMap_comp_homologyCechComplexIsoHOne_hom
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hFU : ∀ i, Subsingleton (F.H' 1 (U i))) (hFV : ∀ i, Subsingleton (F.H' 1 (V i)))
    (φ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ V) :
    HomologicalComplex.homologyMap (cechComplexMap F.obj φ) 1 ≫
        (homologyCechComplexIsoHOne U hU F hFU).hom =
      (homologyCechComplexIsoHOne V hV F hFV).hom := by
  have h := lerayOneIso_naturality V U hV hU hFV hFU
    (cechInjectiveCokernelSequenceRefinement U V F φ) (𝟙 (injectiveCokernelSequence F))
    (by
      simpa only [cechInjectiveCokernelSequenceRefinement_τ₁,
        cechInjectiveCokernelSequenceRefinement_τ₃, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using
        homologyMap_cechComplexMap_comp_homologyZeroCechIso_hom U hU V hV
          (cokernel (Injective.ι F)) φ)
  simpa only [cechInjectiveCokernelSequenceRefinement_τ₁,
    cechInjectiveCokernelSequenceRefinement_τ₃, ShortComplex.id_τ₁, ShortComplex.id_τ₃,
        _root_.CategoryTheory.Sheaf.H.ofHom_map_id, Category.comp_id] using h

/-- A refinement between memberwise `H¹`-acyclic covers induces an isomorphism on `H¹`. -/
theorem isIso_homologyMap_cechComplexMap_one
    (hU : ⨆ i, U i = ⊤) (hV : ⨆ i, V i = ⊤)
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

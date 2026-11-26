/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.Algebra.Homology.Ext.Map.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.Preadditive
public import TauCeti.CategoryTheory.Sites.SheafCohomology.AcyclicResolution
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sheaf cohomology along an equivalence of sites

An equivalence of categories `e : C ≌ D`, compatible with Grothendieck topologies `J` on `C` and
`K` on `D`, induces Mathlib's equivalence `e.sheafCongr J K` of categories of abelian sheaves,
sending a sheaf `F` on `C` to the sheaf `V ↦ F(e.inverse V)` on `D`. This file shows that sheaf
cohomology is invariant under this transport: the cohomology of the transported sheaf at `V` is
the cohomology of `F` at `e.inverse V`.

The comparison applies whenever `e.inverse` is a dense subsite. Its direction transports a sheaf
from `C` to `D` and identifies its cohomology over `V : D` with the original sheaf's cohomology
over `e.inverse.obj V`.

## Main declarations

* `TauCeti.CategoryTheory.sheafCongrInverseFreeYonedaIso`: the transport back of the free abelian
  sheaf on `V` is the free abelian sheaf on `e.inverse V`.
* `TauCeti.CategoryTheory.cohomologyPresheafEvaluationIsoSheafCongr`: the comparison, natural in
  the coefficient sheaf.
* `TauCeti.CategoryTheory.cohomologyPresheafObjIsoSheafCongr`: the comparison
  `Hⁿ(V, e_* F) ≅ Hⁿ(e.inverse V, F)` for a single sheaf `F`.

Both directions of the site-equivalence comparison preserve resolution cocycle classes.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.CategoryTheory

universe v u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]

private def sheafCongrInverseFreeYonedaCorepresentation (V : D) :
    ((sheafSections J AddCommGrpCat.{v}).obj (op (e.inverse.obj V)) ⋙
        forget AddCommGrpCat).CorepresentableBy
      ((e.sheafCongr J K AddCommGrpCat.{v}).inverse.obj ((freeYonedaSheafFunctor K).obj V)) where
  homEquiv :=
    ((e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction.homEquiv _ _).trans
      (freeYonedaSheafSectionsEquiv K V _).toEquiv
  homEquiv_comp g f := by
    let adj := (e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction
    exact (congrArg (freeYonedaSheafSectionsEquiv K V _)
      (adj.homEquiv_naturality_right f g)).trans
      (freeYonedaSheafSectionsEquiv_naturality_right K _
        ((e.sheafCongr J K AddCommGrpCat.{v}).functor.map g))

/-- Transporting the free abelian sheaf on `V : D` back along `e.sheafCongr J K` gives the free
abelian sheaf on `e.inverse.obj V`. -/
def sheafCongrInverseFreeYonedaIso (V : D) :
    (e.sheafCongr J K AddCommGrpCat.{v}).inverse.obj ((freeYonedaSheafFunctor K).obj V) ≅
      (freeYonedaSheafFunctor J).obj (e.inverse.obj V) :=
  (sheafCongrInverseFreeYonedaCorepresentation J K e V).uniqueUpToIso
    (freeYonedaSheafCorepresentableBy J (e.inverse.obj V))

variable [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] [HasExt.{v} (Sheaf K AddCommGrpCat.{v})]

/-- Sheaf cohomology is invariant under an equivalence of sites: the cohomology at `V : D` of the
sheaf transported along `e.sheafCongr J K` is the cohomology of the original sheaf at
`e.inverse.obj V`, naturally in the coefficient sheaf. -/
def cohomologyPresheafEvaluationIsoSheafCongr (n : ℕ) (V : D) :
    (e.sheafCongr J K AddCommGrpCat.{v}).functor ⋙
        _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor K n ⋙
          (evaluation Dᵒᵖ AddCommGrpCat.{v}).obj (op V) ≅
      _root_.CategoryTheory.Sheaf.cohomologyPresheafFunctor J n ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op (e.inverse.obj V)) := by
  rw [cohomologyPresheafFunctor_eq, cohomologyPresheafFunctor_eq]
  -- These explicit functors expose Mathlib's generic Equivalence.inverse_additive instance.
  let adj : (e.sheafCongr J K AddCommGrpCat.{v}).inverse ⊣
      (e.sheafCongr J K AddCommGrpCat.{v}).functor :=
    (e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction
  exact NatIso.ofComponents (fun F ↦ (adj.extEquiv (n := n)).symm.toAddCommGrpIso)
      (by
        intro F G f
        ext x
        exact adj.extEquiv_symm_naturality_right₀ x f) ≪≫
    (Abelian.extFunctor n).mapIso (sheafCongrInverseFreeYonedaIso J K e V).symm.op

/-- Sheaf cohomology is invariant under an equivalence of sites: the cohomology at `V : D` of the
sheaf transported along `e.sheafCongr J K` is the cohomology of the original sheaf at
`e.inverse.obj V`. -/
def cohomologyPresheafObjIsoSheafCongr (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (V : D) :
    _root_.CategoryTheory.Sheaf.H'.{v} ((e.sheafCongr J K AddCommGrpCat.{v}).functor.obj F) n V ≅
      _root_.CategoryTheory.Sheaf.H'.{v} F n (e.inverse.obj V) :=
  (cohomologyPresheafEvaluationIsoSheafCongr J K e n V).app F

/-! ### Resolution-class normalization under the native equivalence -/

open CochainComplex CategoryTheory.Abelian

omit [HasExt (Sheaf J AddCommGrpCat.{v})] [HasExt (Sheaf K AddCommGrpCat.{v})] in
/-- The inverse free-Yoneda comparison preserves the represented section. -/
lemma sheafCongrInverseFreeYonedaIso_evaluation (V : D)
    (F : Sheaf J AddCommGrpCat.{v})
    (f : (freeYonedaSheafFunctor J).obj (e.inverse.obj V) ⟶ F) :
    freeYonedaSheafSectionsEquiv K V
      ((e.sheafCongr J K AddCommGrpCat.{v}).functor.obj F)
      (((e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction).homEquiv _ _
        ((sheafCongrInverseFreeYonedaIso J K
          e V).hom ≫ f)) =
      freeYonedaSheafSectionsEquiv J (e.inverse.obj V) F f := by
  let c := sheafCongrInverseFreeYonedaCorepresentation J K e V
  let c' := freeYonedaSheafCorepresentableBy J (e.inverse.obj V)
  -- The inverse free-Yoneda map represents the identity section in the two corepresentations.
  change c.homEquiv (c.homEquiv.symm (c'.homEquiv (𝟙 _)) ≫ f) = _
  rw [c.homEquiv_comp, Equiv.apply_symm_apply]
  exact (c'.homEquiv_eq f).symm.trans
    (freeYonedaSheafCorepresentableBy_homEquiv J _ f)

variable {F : Sheaf J AddCommGrpCat.{v}}
  (L : CochainComplex (Sheaf J AddCommGrpCat.{v}) ℕ)
  (ι : F ⟶ L.X 0) [Mono ι] (hι : ι ≫ L.d 0 1 = 0)
  (hι' : (ShortComplex.mk ι (L.d 0 1) hι).Exact) (hL : ∀ j, L.ExactAt (j + 1))
/-- Site equivalence preserves the cohomology class of a resolution cocycle. -/
lemma cohomologyPresheafEvaluationIsoSheafCongr_resolutionClass (V : D) {n : ℕ}
    (s : (L.X n).obj.obj (op (e.inverse.obj V)))
    (hs : (L.d n (n + 1)).hom.app (op (e.inverse.obj V)) s = 0) :
    (cohomologyPresheafEvaluationIsoSheafCongr J K
      e n V).hom.app F
      (Sheaf.H'.resolutionClass ((e.sheafCongr J K AddCommGrpCat.{v}).functor.map ι)
        (map_augmentation_comp_d (e.sheafCongr J K AddCommGrpCat.{v}).functor hι)
        (map_augmentation_exact (e.sheafCongr J K AddCommGrpCat.{v}).functor hι')
        (map_exactAt_succ (e.sheafCongr J K AddCommGrpCat.{v}).functor hL) V s hs) =
      Sheaf.H'.resolutionClass ι hι hι' hL (e.inverse.obj V) s hs := by
  let E := (e.sheafCongr J K AddCommGrpCat.{v}).functor
  let adj := (e.sheafCongr J K AddCommGrpCat.{v}).symm.toAdjunction
  let ξ := sheafCongrInverseFreeYonedaIso J K e V
  let c := (freeYonedaSheafSectionsEquiv J (e.inverse.obj V) (L.X n)).symm s
  let KE : CochainComplex _ ℕ := (E.mapHomologicalComplex (.up ℕ)).obj L
  let cE := (freeYonedaSheafSectionsEquiv K V (KE.X n)).symm s
  have hc : c ≫ L.d n (n + 1) = 0 := by
    simp only [c, freeYonedaSheafSectionsEquiv_symm_naturality_right, hs, map_zero]
  have hcE : cE ≫ KE.d n (n + 1) = 0 := by
    dsimp only [cE]
    -- `s` is a section of `L.X n` at `e.inverse.obj V`, used here as a section of
    -- `KE.X n = E.obj (L.X n)` at `V`; the carriers agree only after unfolding `sheafCongr`, so
    -- `rw` cannot match the free-Yoneda naturality lemma.
    erw [freeYonedaSheafSectionsEquiv_symm_naturality_right, hs, map_zero]
  have hforward : adj.extEquiv ((Ext.mk₀ ξ.hom).comp
        (L.extMk ι hι hι' hL c hc) (zero_add n)) =
      KE.extMk (E.map ι) (map_augmentation_comp_d E hι)
        (map_augmentation_exact E hι') (map_exactAt_succ E hL) cE hcE := by
    rw [CochainComplex.mk₀_comp_extMk, extEquiv_extMk]
    congr 1
    apply (freeYonedaSheafSectionsEquiv K V (KE.X n)).injective
    have hv := sheafCongrInverseFreeYonedaIso_evaluation J K e V (L.X n) c
    dsimp only [c, cE, KE, E, adj, ξ, Functor.mapHomologicalComplex_obj_X] at hv ⊢
    -- The same carrier identification: the section equivalence for `E.obj (L.X n)` at `V` is
    -- applied to `s`, typed at `L.X n` and `e.inverse.obj V`, so only `erw` can cancel it.
    erw [AddEquiv.apply_symm_apply] at hv ⊢
    exact hv
  have hm := Sheaf.H'.resolutionClass_def (K := KE) (E.map ι)
    (map_augmentation_comp_d E hι) (map_augmentation_exact E hι')
    (map_exactAt_succ E hL) V s hs
  rw [Sheaf.H'.resolutionClass_def]
  rw [hm]
  -- The evaluated comparison is inverse adjunction on Ext followed by the free-Yoneda iso.
  dsimp only [cohomologyPresheafEvaluationIsoSheafCongr]
  change (Ext.mk₀ ξ.inv).comp
    (adj.extEquiv.symm (KE.extMk (E.map ι) (map_augmentation_comp_d E hι)
      (map_augmentation_exact E hι') (map_exactAt_succ E hL) cE hcE))
    (zero_add n) = L.extMk ι hι hι' hL c hc
  rw [← hforward, AddEquiv.symm_apply_apply, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, ξ.inv_hom_id, Ext.mk₀_id_comp]

/-- The inverse comparison sends an actual resolution class to its transported class. -/
lemma cohomologyPresheafEvaluationIsoSheafCongr_inv_resolutionClass
    (V : D) {n : ℕ} (s : (L.X n).obj.obj (op (e.inverse.obj V)))
    (hs : (L.d n (n + 1)).hom.app (op (e.inverse.obj V)) s = 0) :
    let E := (e.sheafCongr J K AddCommGrpCat.{v}).functor
    (cohomologyPresheafEvaluationIsoSheafCongr J K e n V).inv.app F
      (Sheaf.H'.resolutionClass ι hι hι' hL (e.inverse.obj V) s hs) =
    Sheaf.H'.resolutionClass (E.map ι) (map_augmentation_comp_d E hι)
      (map_augmentation_exact E hι') (map_exactAt_succ E hL) V s hs := by
  let q := (cohomologyPresheafEvaluationIsoSheafCongr J K e n V).app F
  have h := congrArg (fun x ↦ q.inv x)
    (cohomologyPresheafEvaluationIsoSheafCongr_resolutionClass J K e L ι hι hι' hL V s hs)
  exact h.symm.trans (Iso.hom_inv_id_apply q _)


end

end TauCeti.CategoryTheory

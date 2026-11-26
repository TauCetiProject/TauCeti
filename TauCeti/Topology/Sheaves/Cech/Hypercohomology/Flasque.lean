/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.CategoryTheory.Sites.Homology
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Total.BoundedBelow
public import TauCeti.Topology.Sheaves.Cech.Flasque
public import TauCeti.Topology.Sheaves.Cech.Hypercohomology.Augmentation

/-!
# Bounded-below flasque complexes compute Čech hypercohomology

For every finite open cover the total Čech augmentation of a bounded-below
complex of flasque sheaves of modules is a quasi-isomorphism. On compact spaces
the cohomology of its global sections identifies with the existing cover-colimit
Čech hypercohomology, compatibly with every point-neighborhood cover.

The native sheaf-complex interface uses Mathlib's conversion of complexes of
functors into functors of complexes; it retains the actual caller coefficient
complexes in the total Čech construction.

The Stacks Project, Cohomology of Sheaves, §20.25, Lemma 20.25.1
([tag 08BN](https://stacks.math.columbia.edu/tag/08BN)), uses the same augmentation
for bounded-below injective complexes. Here the finite-cover extension to flasque
terms uses `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque_moduleCat`.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [Ring R]
  (P : (Opens X)ᵒᵖ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)

/-- A bounded-below presheaf of complexes whose terms are flasque sheaves has
a quasi-isomorphic augmentation for every finite open cover. -/
theorem quasiIso_cechTotalComplexAugmentation_of_isFlasque
    (b : ℤ) (hP : ∀ U q, q < b → IsZero ((P.obj U).X q))
    (hsheaf : ∀ q, Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (P ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) q))
    (hflasque : ∀ q, TopCat.Presheaf.IsFlasque
      (P ⋙ HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.up ℤ) q))
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (cechTotalComplexAugmentation U isTerminalTop P) := by
  apply quasiIso_cechTotalComplexAugmentation (U := U) (hT := isTerminalTop) (P := P) b hP
  intro q
  let F : X.Sheaf (ModuleCat.{u} R) := ⟨_, hsheaf q⟩
  have : F.presheaf.IsFlasque := hflasque q
  exact TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque_moduleCat F U hU.iSup_eq_top

end TauCeti.Topology

namespace CochainComplex

variable {X : TopCat.{u}} {R : Type u} [Ring R]

private lemma isZero_sheafPresheaf_obj_X
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℤ) (q : ℤ)
    (h : IsZero (K.X q)) (U : (Opens X)ᵒᵖ) :
    IsZero ((K.sheafPresheaf.obj U).X q) := by
  rw [HomologicalComplex.sheafPresheaf_obj]
  exact ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj U).map_isZero h

/-- The finite-cover total Čech comparison for a native bounded-below complex
of flasque sheaves of modules. -/
theorem quasiIso_cechTotalComplexAugmentation_of_isFlasque_moduleCat
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℤ)
    (b : ℤ) [K.IsStrictlyGE b]
    (hflasque : ∀ q, (K.X q).presheaf.IsFlasque)
    {ι : Type u} [Finite ι] (U : ι → Opens X) (hU : IsOpenCover U) :
    QuasiIso (cechTotalComplexAugmentation U isTerminalTop K.sheafPresheaf) :=
  TauCeti.Topology.quasiIso_cechTotalComplexAugmentation_of_isFlasque
    K.sheafPresheaf b
    (fun V q h ↦ isZero_sheafPresheaf_obj_X K q (K.isZero_of_isStrictlyGE b q h) V)
    (fun q ↦ by rw [HomologicalComplex.sheafPresheaf_comp_eval]; exact (K.X q).property)
    (fun q ↦ by rw [HomologicalComplex.sheafPresheaf_comp_eval]; exact hflasque q) U hU

/-- On a compact space, the section cohomology of a native bounded-below complex
of flasque sheaves is canonically its existing cover-colimit Čech hypercohomology. -/
def cechHypercohomologyIsoOfFlasque [CompactSpace X]
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℤ)
    (b : ℤ) [K.IsStrictlyGE b]
    (hflasque : ∀ q, (K.X q).presheaf.IsFlasque) (n : ℤ) :
    (K.sheafPresheaf.obj (op ⊤)).homology n ≅
      (TauCeti.Topology.cechHypercohomology X (ModuleCat.{u} R) n).obj K.sheafPresheaf := by
  have := TauCeti.Topology.isIso_cechHypercohomologyAugmentation_of_finite
    K.sheafPresheaf n fun ι _ U hU ↦ by
      have := quasiIso_cechTotalComplexAugmentation_of_isFlasque_moduleCat K b hflasque U hU
      infer_instance
  exact asIso (TauCeti.Topology.cechHypercohomologyAugmentation K.sheafPresheaf n)

/-- The native sheaf-complex comparison respects every point-cover structure map. -/
@[reassoc]
lemma cechHypercohomologyIsoOfFlasque_hom [CompactSpace X]
    (K : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℤ)
    (b : ℤ) [K.IsStrictlyGE b]
    (hflasque : ∀ q, (K.X q).presheaf.IsFlasque) (n : ℤ)
    (W : TauCeti.Topology.PointOpenCover X) :
    (cechHypercohomologyIsoOfFlasque K b hflasque n).hom =
      HomologicalComplex.homologyMap
          (cechTotalComplexAugmentation W.opens isTerminalTop K.sheafPresheaf) n ≫
        (cechHypercohomologyι TauCeti.Topology.PointOpenCover.toFormalCoproduct
          (fun _ _ h ↦ h) n W).app K.sheafPresheaf := by
  rw [cechHypercohomologyIsoOfFlasque]
  exact (TauCeti.Topology.homologyMap_cechTotalComplexAugmentation_comp_ι
    K.sheafPresheaf n W).symm

/-- The native flasque comparison commutes with maps of sheaf complexes.
The two complexes may have different strict lower bounds. -/
@[reassoc]
lemma cechHypercohomologyIsoOfFlasque_naturality [CompactSpace X]
    (K L : CochainComplex (X.Sheaf (ModuleCat.{u} R)) ℤ)
    (bK bL : ℤ) [K.IsStrictlyGE bK] [L.IsStrictlyGE bL]
    (hK : ∀ q, (K.X q).presheaf.IsFlasque) (hL : ∀ q, (L.X q).presheaf.IsFlasque)
    (f : K ⟶ L) (n : ℤ) :
    (cechHypercohomologyIsoOfFlasque K bK hK n).hom ≫
        (TauCeti.Topology.cechHypercohomology X (ModuleCat.{u} R) n).map
          (((Opens.grothendieckTopology X).complexToPresheaf _ _).map f) =
      HomologicalComplex.homologyMap
          ((((Opens.grothendieckTopology X).complexToPresheaf _ _).map f).app (op ⊤)) n ≫
        (cechHypercohomologyIsoOfFlasque L bL hL n).hom := by
  rw [cechHypercohomologyIsoOfFlasque, cechHypercohomologyIsoOfFlasque]
  exact TauCeti.Topology.cechHypercohomologyAugmentation_naturality _ n
    (((Opens.grothendieckTopology X).complexToPresheaf _ _).map f)

end CochainComplex

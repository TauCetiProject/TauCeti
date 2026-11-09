/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Coefficients
public import TauCeti.Topology.Sheaves.Cech.Cofinal
public import TauCeti.Topology.Sheaves.Flasque.Basic

/-!
# Flasque sheaves of modules have no higher Čech cohomology on compact spaces

Let `R` be a ring and `F` a flasque sheaf of `R`-modules on a topological space `X`. For every
finite open cover `U` of `X` the augmented Čech complex `0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is
exact. This is `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque` for the underlying flasque
sheaf of abelian groups, transported along the forgetful functor, which commutes with Čech
complexes (`TauCeti.CategoryTheory.cechComplexFunctorMapIso`) and detects exactness.

On a compact space the finite covers are cofinal among all open covers
(`TauCeti.Topology.finiteCechCohomologyIso`), so the cover-colimit Čech cohomology of `F` vanishes
in every positive degree. No separation axiom is assumed. Together with the long exact sequence of
Čech cohomology, this makes flasque sheaves available for dimension shifting in the comparison of
Čech cohomology with derived-functor cohomology on compact Hausdorff spaces.

## Main results

* `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque_moduleCat`: a flasque sheaf of modules has
  an exact augmented Čech complex for every finite open cover.
* `TauCeti.Topology.isZero_cechCohomology_succ_of_isFlasque`: on a compact space, a flasque sheaf
  of modules has zero Čech cohomology in every positive degree.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.4.3.
* The Stacks Project, Cohomology of Sheaves, Lemma 20.11.4 (tag 01EW), and §20.15 (tag 09UY).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {R : Type u} [Ring R] (F : X.Sheaf (ModuleCat.{u} R))
  [F.presheaf.IsFlasque]

/-- A flasque sheaf of modules has an exact augmented Čech complex for every finite open cover:
`0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact. -/
theorem quasiIso_cechAugmentation_of_isFlasque_moduleCat {ι : Type u} [Finite ι]
    (U : ι → Opens X) (hU : ⨆ i, U i = ⊤) :
    QuasiIso (cechAugmentation U isTerminalTop F.presheaf) := by
  let G := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  have : (TopCat.Sheaf.presheaf ((sheafCompose _ G).obj F)).IsFlasque :=
    TopCat.Presheaf.isFlasque_comp F.presheaf (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  have hG := (quasiIso_cechAugmentation_iff U isTerminalTop _).1
    (quasiIso_cechAugmentation_of_isFlasque ((sheafCompose _ G).obj F) U hU)
  refine (quasiIso_cechAugmentation_iff U isTerminalTop _).2
    ⟨TauCeti.Topology.isSheafFor_ofArrows_of_iSup_eq_top U hU F, fun n ↦ ?_⟩
  -- the forgetful functor carries the Čech complex of `F` to that of its underlying sheaf of
  -- abelian groups, and detects exactness
  have h := (hG.2 n).of_iso ((cechComplexFunctorMapIso U G).app F.presheaf).symm
  exact (ShortComplex.exact_map_iff_of_faithful _ G).1 h

end TopCat.Sheaf

namespace TauCeti.Topology

variable {X : TopCat.{u}} [CompactSpace X] {R : Type u} [Ring R]

/-- **Flasque sheaves have no higher Čech cohomology on a compact space.** On a compact space `X`,
the cover-colimit Čech cohomology of a flasque sheaf of modules vanishes in every positive degree.
No separation axiom is assumed. -/
theorem isZero_cechCohomology_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) (n + 1)).obj F.obj) :=
  (isZero_cechCohomology_obj_succ_of_quasiIso FiniteOpenCover.toFormalCoproduct
    (fun _ _ h ↦ h) n isTerminalTop F.obj fun W ↦
      TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque_moduleCat F W.opens W.isOpenCover).of_iso
    ((finiteCechCohomologyIso X (ModuleCat.{u} R) (n + 1)).app F.obj).symm

end TauCeti.Topology

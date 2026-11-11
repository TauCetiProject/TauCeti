/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Sites.Abelian
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.LongExactSequence
public import TauCeti.Topology.Sheaves.Cech.LocallyZero

/-!
# Sheafification invariance of Čech cohomology

On a compact normal space, a morphism of module presheaves which becomes an isomorphism
on sheafification induces an isomorphism on cover-colimit Čech cohomology, provided both
presheaves have zero value on the empty open. In particular, the canonical map from such
a presheaf to its sheafification induces an isomorphism in every degree.

The comparison is the map induced by the coefficient morphism, so it is natural and
commutes with every fixed-cover structure map. The empty-value hypothesis is essential:
Čech complexes include empty intersections, which can detect a nonzero empty-open value
even when the sheafification is zero.

The proof uses locally-zero vanishing and the long exact coefficient sequence, applied
to the kernel and cokernel of the coefficient morphism. This is the sheafification step
in the shrinking argument of the Stacks Project, Cohomology of Sheaves, Lemma 20.16.2
(tag 09V2).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} [CompactSpace X] [NormalSpace X] {R : Type u} [Ring R]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{u} R)]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective (ModuleCat.{u} R)]
  {P Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R}

/-- A sheafification equivalence between module presheaves with zero empty-open value
induces an isomorphism on Čech cohomology on a compact normal space. The map is the
canonical map on Čech cohomology induced by the coefficient morphism. -/
theorem isIso_cechCohomology_map_of_isIso_sheafification (α : P ⟶ Q)
    (hP : IsZero (P.obj (op ⊥))) (hQ : IsZero (Q.obj (op ⊥)))
    [IsIso ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map α)]
    (n : ℕ) : IsIso ((cechCohomology X (ModuleCat.{u} R) n).map α) := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)
  let E := PointOpenCover.toFormalCoproduct (X := X)
  have hE : ∀ ⦃U V : PointOpenCover X⦄, U ≤ V → Nonempty (E V ⟶ E U) :=
    fun _ _ h ↦ h
  have hK₀ : IsZero ((kernel α).obj (op ⊥)) :=
    IsZero.of_mono ((kernel.ι α).app (op ⊥)) hP
  have hC₀ : IsZero ((cokernel α).obj (op ⊥)) :=
    IsZero.of_epi ((cokernel.π α).app (op ⊥)) hQ
  have hK : IsZero (F.obj (kernel α)) :=
    (isZero_kernel_of_mono (F.map α)).of_iso (PreservesKernel.iso F α)
  have hC : IsZero (F.obj (cokernel α)) :=
    (isZero_cokernel_of_epi (F.map α)).of_iso (PreservesCokernel.iso F α)
  have hKH (m : ℕ) : IsZero ((cechCohomology X (ModuleCat.{u} R) m).obj (kernel α)) :=
    isZero_cechCohomology_obj_of_isZero_sheafify _ hK₀
      (Functor.map_isZero (sheafToPresheaf _ _) hK) m
  have hCH (m : ℕ) : IsZero ((cechCohomology X (ModuleCat.{u} R) m).obj (cokernel α)) :=
    isZero_cechCohomology_obj_of_isZero_sheafify _ hC₀
      (Functor.map_isZero (sheafToPresheaf _ _) hC) m
  -- Factor through the coimage and image, keeping the actual kernel and cokernel of α.
  let S : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk (kernel.ι α) (Abelian.coimage.π α) (by simp)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι α) }
  have hS' (U : PointOpenCover X) :
      (S.map (cechComplexFunctor U.opens)).ShortExact :=
    hS.map_of_exact (cechComplexFunctor U.opens)
  have : IsIso ((cechCohomology X (ModuleCat.{u} R) n).map (Abelian.coimage.π α)) :=
    TauCeti.CategoryTheory.isIso_cechCohomology_map_g_of_isZero E hE hS' hKH n
  let T : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk (Abelian.image.ι α) (cokernel.π α) (by simp)
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel (cokernel.π α) }
  have hT' (U : PointOpenCover X) :
      (T.map (cechComplexFunctor U.opens)).ShortExact :=
    hT.map_of_exact (cechComplexFunctor U.opens)
  have : IsIso ((cechCohomology X (ModuleCat.{u} R) n).map (Abelian.image.ι α)) :=
    TauCeti.CategoryTheory.isIso_cechCohomology_map_f_of_isZero E hE hT' hCH n
  rw [← Abelian.coimage_image_factorisation α, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- On a compact normal space, sheafification preserves the Čech cohomology of a module
presheaf with zero empty-open value. This asserts invertibility of the map induced by
the sheafification unit, not merely existence of an abstract isomorphism. -/
theorem isIso_cechCohomology_map_toSheafify (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)
    (hP : IsZero (P.obj (op ⊥))) (n : ℕ) :
    IsIso ((cechCohomology X (ModuleCat.{u} R) n).map
      (toSheafify (Opens.grothendieckTopology X) P)) := by
  have : IsIso ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).map
      (toSheafify (Opens.grothendieckTopology X) P)) := by
    rw [← sheafificationAdjunction_unit_app]
    infer_instance
  exact isIso_cechCohomology_map_of_isIso_sheafification _ hP
    ((isZero_zero _).of_iso ((isZero_zero _).isoIsTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty
        ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)).obj P)
        rfl)).symm) n

end TauCeti.Topology

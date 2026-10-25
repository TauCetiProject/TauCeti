/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AlmostSplit.Basic
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
import TauCeti.CategoryTheory.Preadditive.Radical.Approximation
import TauCeti.RepresentationTheory.Quiver.AuslanderReiten.Quiver
import TauCeti.RepresentationTheory.Quiver.Representation.KrullSchmidt

/-!
# Left almost-split morphisms for quivers of finite representation type

Every pointwise finite-dimensional indecomposable representation of a finite quiver of finite
representation type admits a left almost-split morphism in the finite-dimensional full
subcategory. Bases of the radical spaces to representatives of the finitely many indecomposable
classes give a finite-dimensional target. Krull–Schmidt then gives factorization for every
finite-dimensional test target.

These maps supply the left lifting property used to construct almost-split sequences starting
at non-injective indecomposables. The theorem includes injective sources, whose left almost-split
maps need not be monomorphisms. It asserts neither minimality nor cokernel completion.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, V.1.
* The right-hand construction: `TauCeti.QuiverRep.exists_isRightAlmostSplit`.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- Over a quiver of finite representation type, every finite-dimensional indecomposable
admits a left almost-split morphism in the finite-dimensional full subcategory. This also
includes injective sources; the morphism need not be a monomorphism. -/
theorem exists_isLeftAlmostSplit (h : IsFiniteRepType.{u, v, w, t} k Q)
    (Y : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))
    (hiY : Indecomposable Y.obj) :
    ∃ (E : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))
      (f : Y ⟶ E), IsLeftAlmostSplit f := by
  classical
  let V := IrreducibleMorphismQuiver k (IsFinDim.{u, v, w, t} k Q)
  have : Finite V := (finite_irreducibleMorphismQuiver_iff k Q).mpr h
  let := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let X (i : Fin (Fintype.card V)) := (e.symm i).representative
  have hX i : IsFinDim k Q (X i) := (e.symm i).representative_property.1
  have (i : Fin (Fintype.card V)) : FiniteDimensional k (Y.obj ⟶ X i) :=
    finiteDimensional_hom Y.property (hX i)
  have : IsLocalRing (End Y.obj) := (indecomposable_iff_isLocalRing_end Y.property).mp hiY
  -- Bases of the finitely many radical spaces give one finite-dimensional target.
  obtain ⟨n, f, hf, hfactor⟩ :=
    exists_jacobsonRadical_biproduct_left_factorization (k := k) Y.obj X
  let Z (j : Σ i, Fin (n i)) := X j.1
  let E : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) :=
    ⟨⨁ Z, isFinDim_biproduct Z (fun j ↦ hX j.1)⟩
  let F : Y ⟶ E := ObjectProperty.homMk f
  let I := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  refine ⟨E, F, isLeftAlmostSplit_iff.mpr ⟨?_, fun W g hg ↦ ?_⟩⟩
  · exact fun hs ↦ (mem_jacobsonRadical_iff_not_isSplitMono.mp hf)
      ((I.isSplitMono_iff F).mpr hs)
  · have hrad : g.hom ∈ jacobsonRadical Y.obj W.obj :=
      mem_jacobsonRadical_iff_not_isSplitMono.mpr
        (fun hs ↦ hg ((I.isSplitMono_iff g).mp hs))
    -- Decompose the test target, factor each component, and assemble by the biproduct property.
    obtain ⟨m, P, hiP, hP, ⟨d⟩⟩ := exists_indecomposable_iso_biproduct W.obj W.property
    have factors (j : Fin m) : ∃ a : E.obj ⟶ P j, f ≫ a =
        g.hom ≫ d.hom ≫ biproduct.π P j := by
      let c := IrreducibleMorphismQuiver.representativeIso k (hP j) (hiP j)
      let i := e (IrreducibleMorphismQuiver.of k (hP j) (hiP j))
      let hc : X i ≅ P j :=
        eqToIso (congrArg IrreducibleMorphismQuiver.representative (e.symm_apply_apply _)) ≪≫ c
      obtain ⟨a, ha⟩ := hfactor i (g.hom ≫ d.hom ≫ biproduct.π P j ≫ hc.inv)
        (comp_mem_jacobsonRadical_right hrad _)
      refine ⟨a ≫ hc.hom, ?_⟩
      rw [← Category.assoc, ha]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    choose a ha using factors
    refine ⟨ObjectProperty.homMk (biproduct.lift a ≫ d.inv), ?_⟩
    apply ObjectProperty.hom_ext
    have hlift : f ≫ biproduct.lift a = g.hom ≫ d.hom := by
      apply biproduct.hom_ext
      intro j
      simpa only [Category.assoc, biproduct.lift_π] using ha j
    simp only [ObjectProperty.FullSubcategory.comp_hom, F, ObjectProperty.homMk_hom]
    rw [← Category.assoc, hlift]
    simp

end TauCeti.QuiverRep

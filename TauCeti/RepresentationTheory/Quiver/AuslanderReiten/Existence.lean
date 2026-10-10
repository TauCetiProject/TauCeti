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
# Right almost-split morphisms for quivers of finite representation type

Every finite-dimensional indecomposable representation of a finite quiver of finite
representation type receives a right almost-split morphism in the finite-dimensional
subcategory. Its source is finite-dimensional: assemble bases of the radical spaces from
one representative of every indecomposable class. Krull–Schmidt then gives factorization
for every finite-dimensional source.

The lifting property is stated in the finite-dimensional full subcategory. No claim is made
about infinite-dimensional sources, or about right minimality. Removing redundant summands
and taking a kernel are the further steps needed to construct an almost-split sequence.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, V.1.
-/

public section

namespace TauCeti.QuiverRep

open CategoryTheory CategoryTheory.Limits

universe u v w t

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q] [Finite Q]

/-- Over a quiver of finite representation type, every finite-dimensional indecomposable
admits a right almost-split morphism in the finite-dimensional full subcategory. This also
includes projective targets; the morphism need not be an epimorphism. -/
theorem exists_isRightAlmostSplit (h : IsFiniteRepType.{u, v, w, t} k Q)
    (Y : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))
    (hiY : Indecomposable Y.obj) :
    ∃ (E : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q))
      (f : E ⟶ Y), IsRightAlmostSplit f := by
  classical
  let V := irreducibleMorphismQuiver.{u, v, w, t} k Q
  have : Finite V := (finite_irreducibleMorphismQuiver_iff k Q).mpr h
  let := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let X (i : Fin (Fintype.card V)) := (e.symm i).representative
  have hX i : IsFinDim k Q (X i) := (e.symm i).representative_property.1
  have (i : Fin (Fintype.card V)) : FiniteDimensional k (X i ⟶ Y.obj) :=
    finiteDimensional_hom (hX i) Y.property
  have : IsLocalRing (End Y.obj) := (indecomposable_iff_isLocalRing_end Y.property).mp hiY
  -- Bases of the finitely many radical spaces give one finite-dimensional source.
  obtain ⟨n, f, hf, hfactor⟩ := exists_radical_biproduct_factorization (k := k) X Y.obj
  let Z (j : Σ i, Fin (n i)) := X j.1
  let E : ObjectProperty.FullSubcategory (IsFinDim.{u, v, w, t} k Q) :=
    ⟨⨁ Z, isFinDim_biproduct Z (fun j ↦ hX j.1)⟩
  let F : E ⟶ Y := ObjectProperty.homMk f
  let I := ObjectProperty.ι (IsFinDim.{u, v, w, t} k Q)
  refine ⟨E, F, isRightAlmostSplit_iff.mpr ⟨?_, fun W g hg ↦ ?_⟩⟩
  · exact fun hs ↦ (mem_jacobsonRadical_iff_not_isSplitEpi.mp hf)
      ((I.isSplitEpi_iff F).mpr hs)
  · have hrad : g.hom ∈ jacobsonRadical W.obj Y.obj :=
      mem_jacobsonRadical_iff_not_isSplitEpi.mpr
        (fun hs ↦ hg ((I.isSplitEpi_iff g).mp hs))
    -- Decompose the test source, factor each summand, and assemble by the biproduct property.
    obtain ⟨m, P, hiP, hP, ⟨d⟩⟩ := exists_indecomposable_iso_biproduct W.obj W.property
    have factors (j : Fin m) : ∃ a : P j ⟶ E.obj, a ≫ f =
        biproduct.ι P j ≫ d.inv ≫ g.hom := by
      let c := irreducibleMorphismQuiver.representativeIso (hP j) (hiP j)
      let i := e (irreducibleMorphismQuiver.of (hP j) (hiP j))
      have hc : X i ≅ P j := by
        simpa only [X, i, Equiv.symm_apply_apply] using c
      obtain ⟨a, ha⟩ := hfactor i (hc.hom ≫ biproduct.ι P j ≫ d.inv ≫ g.hom)
        (by simpa only [Category.assoc] using
          comp_mem_jacobsonRadical_left (hc.hom ≫ biproduct.ι P j ≫ d.inv) hrad)
      exact ⟨hc.inv ≫ a, by simp [Category.assoc, ha]⟩
    choose a ha using factors
    refine ⟨ObjectProperty.homMk (d.hom ≫ biproduct.desc a), ?_⟩
    apply ObjectProperty.hom_ext
    have hdesc : biproduct.desc a ≫ f = d.inv ≫ g.hom := by
      apply biproduct.hom_ext'
      intro j
      simpa only [biproduct.ι_desc_assoc] using ha j
    simp only [ObjectProperty.FullSubcategory.comp_hom,
      F, ObjectProperty.homMk_hom, Category.assoc, hdesc, Iso.hom_inv_id_assoc]

end TauCeti.QuiverRep

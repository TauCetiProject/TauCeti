/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.FieldTheory.IntermediateField.FilteredColimit
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Limits.Descent
import TauCeti.AlgebraicGeometry.Descent.Proper
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Finite subextensions as fields of definition for schemes

Let `L / K` be algebraic. Every finite-type scheme over `L` is the base change of a
finitely presented scheme over a finite intermediate field. Properties satisfying fpqc descent
can be retained on the model. In particular, a smooth proper scheme over `L` has a smooth proper
model over a finite intermediate field. Neither extension is required to be separable.

The spectrum of `L` is the inverse limit of the spectra of its finite intermediate fields, by
the native filtered-colimit presentation. General finite-presentation descent supplies a model.
Every field extension is faithfully flat, so fpqc descent recovers its properties.

## Main results

* `AlgebraicGeometry.Scheme.Hom.exists_isPullback_over_finiteSubextension`: finite subextension
  models for finite-type schemes.
* `AlgebraicGeometry.Scheme.Hom.exists_isPullback_over_finiteSubextension_of_descendsAlong`:
  the model retains any property satisfying fpqc descent.
* `AlgebraicGeometry.Scheme.Hom.exists_isPullback_over_finiteSubextension_of_smooth_isProper`:
  smooth proper schemes have smooth proper models.

## References

* The Stacks Project, Lemma 32.10.1, tag [01ZM](https://stacks.math.columbia.edu/tag/01ZM).
-/

public section

open CategoryTheory Limits Opposite
open TauCeti.IntermediateField

universe u

namespace AlgebraicGeometry

variable {L : Type u} [Field L]

/-- A finite-type scheme over an algebraic extension of `K` is the base change of a finitely
presented scheme over a finite intermediate field. Quasi-separatedness and local finite
presentation of the source are derived from the Noetherian field base. -/
theorem Scheme.Hom.exists_isPullback_over_finiteSubextension
    {X : Scheme.{u}} (f : X ⟶ Spec (.of L)) (K : Type*) [Field K] [Algebra K L]
    [Algebra.IsAlgebraic K L] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (E : FiniteSubextension K L) (Y : Scheme.{u}) (g : Y ⟶ Spec (.of E.val))
      (_ : LocallyOfFinitePresentation g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (a : X ⟶ Y), IsPullback a f g (Spec.map (CommRingCat.ofHom (algebraMap E.val L))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hfp : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let D := (finiteSubextensionDiagram K L).op ⋙ Scheme.Spec
  let c : Cone D := (Scheme.Spec.mapCone (finiteSubextensionCocone K L).op).extend
    (Spec.map (eqToHom (finiteSubextensionCocone_pt K L)))
  have hc : IsLimit c :=
    (isLimitOfPreserves Scheme.Spec
      (isColimitFiniteSubextensionCocone (K := K) (L := L)).op).extendIso _
  have hobj (i : (FiniteSubextension K L)ᵒᵖ) : D.obj i = Spec (.of i.unop.val) := by
    simp only [D, Functor.comp_obj, Functor.op_obj, finiteSubextensionDiagram_obj]
    rfl
  have (i : (FiniteSubextension K L)ᵒᵖ) : IsAffine (D.obj i) := by
    rw [hobj]
    infer_instance
  have {i j : (FiniteSubextension K L)ᵒᵖ} (t : i ⟶ j) : IsAffineHom (D.map t) :=
    isAffineHom_of_isAffine _
  let i : (FiniteSubextension K L)ᵒᵖ := .op ⟨⊥, inferInstance⟩
  have : CompactSpace (D.obj i) := inferInstance
  have : QuasiSeparatedSpace (D.obj i) := inferInstance
  -- The cone was extended to `Spec L`; these annotations identify its point with that base.
  have : LocallyOfFinitePresentation
      (show X ⟶ c.pt from f) := hfp
  have : QuasiCompact
      (show X ⟶ c.pt from f) := ‹QuasiCompact f›
  have : QuasiSeparated
      (show X ⟶ c.pt from f) := inferInstanceAs (QuasiSeparated f)
  obtain ⟨E, Y, g, hfp, hqc, hqs, a, ha⟩ :=
    hc.exists_isPullback_of_finitePresentation i f
  let g' := g ≫ eqToHom (hobj E)
  have hleg : c.π.app E ≫ eqToHom (hobj E) =
      Spec.map (CommRingCat.ofHom (algebraMap E.unop.val L)) := by
    dsimp [c]
    have h := congrArg (fun f ↦ Spec.map f)
      (finiteSubextensionCocone_ι_app K L E.unop)
    simpa only [Spec.map_comp, Spec.map_eqToHom, Category.assoc] using h
  refine ⟨E.unop, Y, g', inferInstance, inferInstance, inferInstance, a, ?_⟩
  exact ha.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso (hobj E))
    (by simp) (by simp) (by simp [g']) (by simpa using hleg)

/-- A finite subextension model retains any property satisfying fpqc descent, since extending
one field to another is faithfully flat. -/
theorem Scheme.Hom.exists_isPullback_over_finiteSubextension_of_descendsAlong
    {X : Scheme.{u}} (f : X ⟶ Spec (.of L)) (K : Type*) [Field K] [Algebra K L]
    [Algebra.IsAlgebraic K L] [LocallyOfFiniteType f] [QuasiCompact f]
    (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (hf : P f) :
    ∃ (E : FiniteSubextension K L) (Y : Scheme.{u}) (g : Y ⟶ Spec (.of E.val))
      (_ : LocallyOfFinitePresentation g) (_ : QuasiCompact g) (_ : QuasiSeparated g)
      (a : X ⟶ Y), IsPullback a f g (Spec.map (CommRingCat.ofHom (algebraMap E.val L))) ∧
        P g := by
  obtain ⟨E, Y, g, hfp, hqc, hqs, a, ha⟩ := f.exists_isPullback_over_finiteSubextension K
  have hcover : Flat (Spec.map (CommRingCat.ofHom (algebraMap E.val L))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap E.val L))) := by
    apply (flat_and_surjective_SpecMap_iff _).mpr
    -- Forget the bundled commutative-ring morphism before applying the algebra-map criterion.
    change (algebraMap E.val L).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  refine ⟨E, Y, g, hfp, hqc, hqs, a, ha, ?_⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ha.flip
    ⟨⟨hcover.2, hcover.1⟩, inferInstance⟩ hf

/-- A smooth proper scheme over an algebraic extension of `K` has a smooth proper model over
a finite intermediate field. Finite presentation and quasi-compactness are derived. -/
theorem Scheme.Hom.exists_isPullback_over_finiteSubextension_of_smooth_isProper
    {X : Scheme.{u}} (f : X ⟶ Spec (.of L)) (K : Type*) [Field K] [Algebra K L]
    [Algebra.IsAlgebraic K L] [Smooth f] [IsProper f] :
    ∃ (E : FiniteSubextension K L) (Y : Scheme.{u}) (g : Y ⟶ Spec (.of E.val))
      (a : X ⟶ Y), IsPullback a f g (Spec.map (CommRingCat.ofHom (algebraMap E.val L))) ∧
        Smooth g ∧ IsProper g := by
  have : MorphismProperty.DescendsAlong (@Smooth.{u} ⊓ @IsProper)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    MorphismProperty.DescendsAlong.inf (P := @Smooth) (W := @IsProper)
  obtain ⟨E, Y, g, _, _, _, a, ha, hp⟩ :=
    f.exists_isPullback_over_finiteSubextension_of_descendsAlong K
      (@Smooth ⊓ @IsProper) ⟨inferInstance, inferInstance⟩
  exact ⟨E, Y, g, a, ha, hp⟩

end AlgebraicGeometry

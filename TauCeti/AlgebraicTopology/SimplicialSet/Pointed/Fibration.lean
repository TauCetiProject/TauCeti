/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Kan fibrations of based mapping simplicial sets

The based mapping simplicial set preserves Kan fibrations in its target. In particular,
based maps into a Kan complex form a Kan complex, and simplicial loops preserve Kan complexes.
These are point-set lifting statements, independent of a stable model structure.

The proof uses the unpointed pullback-hom fibration for the inclusion of the basepoint.
Lifting against this map retains the prescribed basepoint, rather than merely lifting
in the unpointed mapping simplicial set.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial homotopy theory*, Chapter I.
-/

public section

open CategoryTheory CategoryTheory.ConcreteCategory MonoidalCategory MonoidalClosed Limits
  HomotopicalAlgebra
open scoped Simplicial

universe u

namespace TauCeti.PointedSSet

open SSet.modelCategoryQuillen

variable {X E B : PointedSSet.{u}}

/-- The based mapping simplicial set preserves Kan fibrations in the target. -/
instance fibration_ihom_map (X : PointedSSet.{u}) (p : E ⟶ B) [Fibration p.right] :
    Fibration ((PointedSSet.ihom X).map p).right := by
  -- Expose the subcomplex carriers of the based mapping objects for the lifting square.
  dsimp only [PointedSSet.ihom]
  -- The unpointed corner map imposes both the target map and the fixed basepoint.
  have : Mono X.hom := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  let Q := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom X.hom p.right
  -- Normalize the bifunctor presentation to its unpointed internal-hom objects.
  dsimp only [MonoidalClosed.internalHom] at Q
  have : Fibration Q.π := SSet.fibration_pullbackObjObjπ Q
  have hfst : Q.π ≫ Q.fst = (MonoidalClosed.pre X.hom).app E.right := Q.π_fst
  have hsnd : Q.π ≫ Q.snd = (CategoryTheory.ihom X.right).map p.right := Q.π_snd
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A D i hi
  have hQ : HasLiftingProperty i Q.π :=
    (SSet.modelCategoryQuillen.fibration_iff Q.π).1 inferInstance i hi
  constructor
  intro a b sq
  let b' : D ⟶ Q.pt := Q.isPullback.lift (pointRestriction E D)
    (b ≫ (basedMaps X B).ι) (by
      exact (pointRestriction_comp_ihom_map p D).trans
        ((b ≫= basedMaps_ι_comp_pre X B).trans (comp_pointRestriction B b)).symm)
  have sq' : CommSq (a ≫ (basedMaps X E).ι) i Q.π b' := by
    constructor
    apply Q.hom_ext
    · simpa only [Category.assoc, hfst, b', IsPullback.lift_fst] using
        ((a ≫= basedMaps_ι_comp_pre X E).trans (comp_pointRestriction E a)).trans
          (comp_pointRestriction E i).symm
    · simpa only [Category.assoc, hsnd, b', IsPullback.lift_snd] using
        (a ≫= (ihom_map_right_comp_ι X p).symm).trans
          (sq.w =≫ (basedMaps X B).ι)
  have : sq'.HasLift := hQ.sq_hasLift sq'
  -- The first corner equation says that the unpointed lift is still based.
  let l := sq'.lift
  have hl : SSet.Subcomplex.range l ≤ basedMaps X E := by
    rw [range_le_basedMaps_iff]
    have h := sq'.fac_right =≫ Q.fst
    simpa only [Category.assoc, hfst, l, b', IsPullback.lift_fst] using h
  refine ⟨⟨SSet.Subcomplex.lift l hl, ?_, ?_⟩⟩
  · apply (cancel_mono (basedMaps X E).ι).1
    simpa only [Category.assoc, SSet.Subcomplex.lift_ι] using sq'.fac_left
  · apply (cancel_mono (basedMaps X B).ι).1
    have h := sq'.fac_right =≫ Q.snd
    have hlp : l ≫ (CategoryTheory.ihom X.right).map p.right = b ≫ (basedMaps X B).ι := by
      simpa only [Category.assoc, hsnd, l, b', IsPullback.lift_snd] using h
    exact (Category.assoc _ _ _).trans
      ((SSet.Subcomplex.lift l hl ≫= ihom_map_right_comp_ι X p).trans
        ((Category.assoc _ _ _).symm.trans ((SSet.Subcomplex.lift_ι l hl =≫ _).trans hlp)))

/-- Based maps into a Kan complex form a Kan complex, with no hypothesis on the source. -/
instance kanComplex_ihom (X E : PointedSSet.{u}) [SSet.KanComplex E.right] :
    SSet.KanComplex ((PointedSSet.ihom X).obj E).right := by
  have : Mono X.hom := SSet.stdSimplex.isTerminalObj₀.mono_from X.hom
  have hf : Fibration (SSet.stdSimplex.isTerminalObj₀.from (basedMaps X E).toSSet) := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    exact MorphismProperty.of_isPullback (basedMaps_isPullback X E)
      ((SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance)
  exact (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).2 hf

end TauCeti.PointedSSet

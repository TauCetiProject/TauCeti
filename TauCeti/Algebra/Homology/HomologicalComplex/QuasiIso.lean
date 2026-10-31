/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import TauCeti.Algebra.Homology.HomologySequenceLemmas
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Homology.ShortComplex.Colimit

/-!
# Stability of monomorphic quasi-isomorphisms

Monomorphic quasi-isomorphisms of complexes in an abelian category are stable under
pushouts. If filtered colimits are exact, they are also stable under transfinite
composition. These closure properties allow cell attachments by monomorphic
quasi-isomorphisms in the construction of injective resolutions of unbounded complexes.

The pushout assertion uses the acyclicity of the cokernel and the canonical
isomorphism between the cokernels of parallel arrows of a pushout square.
The colimit assertion uses preservation of homology by exact colimits; it applies
to quasi-isomorphisms without a monomorphism hypothesis. The filtered-colimit
instances combine with Mathlib's generic transfinite-composition instance, so no
separate transfinite induction is needed here.

## References

* J. Lurie, *Higher Algebra*, §1.3.5, Proposition 1.3.5.3.

The proofs use Mathlib's cokernel comparison for pushouts and transfinite-composition
API, and Tau Ceti's homology-sequence and exact-colimit comparisons.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w w' u v

namespace CategoryTheory.IsPushout

variable {C I : Type*} [Category* C] [Abelian C] {c : ComplexShape I}
  {A B D E : HomologicalComplex C c} {f : A ⟶ B} {g : A ⟶ D}
  {i : B ⟶ E} {j : D ⟶ E}

/-- Pushing out a monomorphic quasi-isomorphism gives a quasi-isomorphism.
The resulting map is also monomorphic, by stability of monomorphisms under pushout
in an abelian category. -/
lemma quasiIso_inr_of_mono (sq : IsPushout f g i j) [Mono f] [QuasiIso f] :
    QuasiIso j := by
  have : Mono j := Abelian.mono_inr_of_isColimit _ _ sq.isColimit
  have hIso : IsIso (cokernel.map f j g i sq.w) := isIso_cokernel_map_of_isPushout sq
  let e := asIso (cokernel.map f j g i sq.w)
  have h := (TauCeti.cokernelSequence_shortExact f).quasiIso_f_iff.mp ‹QuasiIso f›
  apply (TauCeti.cokernelSequence_shortExact j).quasiIso_f_iff.mpr
  intro n
  exact (h n).of_iso e

end CategoryTheory.IsPushout

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {I : Type*} (c : ComplexShape I)

/-- Monomorphic quasi-isomorphisms are stable under pushout, without any exactness
assumption on infinite colimits. -/
instance : (MorphismProperty.monomorphisms (HomologicalComplex C c) ⊓
    quasiIso C c).IsStableUnderCobaseChange where
  of_isPushout sq hf := by
    have : Mono _ := hf.1
    have : QuasiIso _ := hf.2
    exact ⟨Abelian.mono_inr_of_isColimit _ _ sq.flip.isColimit, sq.flip.quasiIso_inr_of_mono⟩

/-- Quasi-isomorphisms are stable under colimits of any shape for which colimits
in the coefficient category exist and are exact. -/
instance {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] :
    (quasiIso C c).IsStableUnderColimitsOfShape J where
  condition F G s t hs ht f hf φ hφ := by
    rw [mem_quasiIso_iff, _root_.quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := homologyFunctor C c n
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := MorphismProperty.isomorphisms C)
      (F ⋙ H) (G ⋙ H) (H.mapCocone s) (H.mapCocone t)
      (isColimitOfPreserves H hs) (isColimitOfPreserves H ht)
      (Functor.whiskerRight f H)
      (fun j ↦ by
        have : QuasiIso (f.app j) := hf j
        exact (inferInstance : IsIso (homologyMap (f.app j) n)))
      (H.map φ) (fun j ↦ by simpa using congrArg H.map (hφ j))

/-- Under AB5, quasi-isomorphisms are stable under filtered colimits. -/
instance [HasFilteredColimitsOfSize.{w', w} C] [AB5OfSize.{w', w} C] :
    MorphismProperty.IsStableUnderFilteredColimits.{w', w} (quasiIso C c) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

/-- Monomorphic quasi-isomorphisms are stable under any existing exact colimits
in the coefficient category. -/
instance {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
    [HasExactColimitsOfShape J C] :
    (MorphismProperty.monomorphisms (HomologicalComplex C c) ⊓
      quasiIso C c).IsStableUnderColimitsOfShape J where
  condition F G s t hs ht f hf φ hφ := by
    refine ⟨?_, MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := quasiIso C c) F G s t hs ht f (fun j ↦ (hf j).2) φ hφ⟩
    apply mono_of_mono_f
    intro n
    let H := eval C c n
    exact MorphismProperty.IsStableUnderColimitsOfShape.condition
      (W := MorphismProperty.monomorphisms C)
      (F ⋙ H) (G ⋙ H) (H.mapCocone s) (H.mapCocone t)
      (isColimitOfPreserves H hs) (isColimitOfPreserves H ht)
      (Functor.whiskerRight f H)
      (fun j ↦ by
        have : Mono (f.app j) := (hf j).1
        exact (inferInstance : Mono ((f.app j).f n)))
      (H.map φ) (fun j ↦ by simpa using congrArg H.map (hφ j))

/-- Under AB5, monomorphic quasi-isomorphisms are stable under filtered colimits. -/
instance [HasFilteredColimitsOfSize.{w', w} C] [AB5OfSize.{w', w} C] :
    MorphismProperty.IsStableUnderFilteredColimits.{w', w}
      (MorphismProperty.monomorphisms (HomologicalComplex C c) ⊓ quasiIso C c) where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

end HomologicalComplex

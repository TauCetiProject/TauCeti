/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# The degreewise exact structure on homological complexes

Let `E` be a Quillen exact structure on an additive category `C` and let `c` be a complex shape.
The category `HomologicalComplex C c` carries the **degreewise exact structure**
`E.homologicalComplex c`: a short complex of complexes is a conflation when it is a conflation
of `E` in every degree. No limits or colimits are assumed in `C`: the kernels, cokernels,
pushouts and pullbacks that the axioms require are those supplied degreewise by `E`, assembled
into complexes by Mathlib's degreewise (co)limits in `HomologicalComplex C c`.

Specializing `E` to the split exact structure `ExactStructure.split C` gives the
**componentwise split** exact structure `(ExactStructure.split C).homologicalComplex c`, whose
conflations are the short complexes of complexes that split in every degree, though not
necessarily compatibly with the differentials (by `homologicalComplex_conflation_iff` and
`ExactStructure.split_conflation`). These are the short exact sequences studied in Mathlib's
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`. For cochain complexes, and for
the `n`-periodic complexes indexed by `ComplexShape.up (ZMod n)`, it is the exact structure for
which Keller shows the category of complexes to be Frobenius, with the homotopy category as its
stable category; that comparison is not part of this file.

## Main definitions

* `TauCeti.ExactStructure.homologicalComplex`: the degreewise exact structure on
  `HomologicalComplex C c`.

## Main results

* `TauCeti.isKernelCokernelPair_of_eval`: a short complex of complexes which is a
  kernel–cokernel pair in every degree is a kernel–cokernel pair.
* `TauCeti.hasColimit_span_comp_eval` and `TauCeti.hasLimit_cospan_comp_eval`: degreewise
  pushouts and pullbacks assemble into pushouts and pullbacks of complexes, which the evaluation
  functors then preserve.
* `TauCeti.ExactStructure.homologicalComplex_conflation_iff`,
  `TauCeti.ExactStructure.homologicalComplex_isInflation_iff` and
  `TauCeti.ExactStructure.homologicalComplex_isDeflation_iff`: conflations, inflations and
  deflations are detected degreewise.
* `TauCeti.ExactStructure.isConflationExact_eval_homologicalComplex`: the evaluation functors
  preserve conflations.
* `TauCeti.ExactStructure.IsConflationExact.mapHomologicalComplex`: a conflation-exact functor
  induces a conflation-exact functor on complexes.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 9 (the exact structure on chain complexes given
  by the degreewise conflations).
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379--417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u u'

variable {C : Type u} [Category.{v} C] {ι : Type u'} {c : ComplexShape ι}

/-- The category of homological complexes in a preadditive category with binary biproducts has
binary biproducts, computed degreewise. -/
instance [Preadditive C] [HasBinaryBiproducts C] : HasBinaryBiproducts (HomologicalComplex C c) :=
  ⟨fun _ _ => inferInstance⟩

/-- A short complex of homological complexes which is a kernel–cokernel pair in every degree is
a kernel–cokernel pair: kernels and cokernels in `HomologicalComplex C c` may be computed
degreewise. -/
theorem isKernelCokernelPair_of_eval [HasZeroMorphisms C]
    (S : ShortComplex (HomologicalComplex C c))
    (h : ∀ i, IsKernelCokernelPair (S.map (HomologicalComplex.eval C c i))) :
    IsKernelCokernelPair S where
  nonempty_fIsKernel := ⟨HomologicalComplex.isLimitOfEval _ _ fun i =>
    (isLimitMapConeForkEquiv' (HomologicalComplex.eval C c i) S.zero).symm (h i).fIsKernel⟩
  nonempty_gIsCokernel := ⟨HomologicalComplex.isColimitOfEval _ _ fun i =>
    (isColimitMapCoconeCoforkEquiv' (HomologicalComplex.eval C c i) S.zero).symm
      (h i).gIsCokernel⟩

/-- A span of complexes having a pushout in every degree has a pushout in complexes, computed
degreewise. -/
theorem hasColimit_span_comp_eval [HasZeroMorphisms C] {K L M : HomologicalComplex C c}
    {f : K ⟶ L} {g : K ⟶ M} (h : ∀ i, HasPushout (f.f i) (g.f i)) (i : ι) :
    HasColimit (span f g ⋙ HomologicalComplex.eval C c i) :=
  have := h i
  hasColimit_of_iso (F := span (f.f i) (g.f i)) (spanCompIso (HomologicalComplex.eval C c i) f g)

/-- A cospan of complexes having a pullback in every degree has a pullback in complexes, computed
degreewise. -/
theorem hasLimit_cospan_comp_eval [HasZeroMorphisms C] {K L M : HomologicalComplex C c}
    {f : K ⟶ M} {g : L ⟶ M} (h : ∀ i, HasPullback (f.f i) (g.f i)) (i : ι) :
    HasLimit (cospan f g ⋙ HomologicalComplex.eval C c i) :=
  have := h i
  hasLimit_of_iso (F := cospan (f.f i) (g.f i))
    (cospanCompIso (HomologicalComplex.eval C c i) f g).symm

namespace ExactStructure

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] (E : ExactStructure C)
  (c : ComplexShape ι)

/-- The degreewise conflation class on homological complexes. -/
private def homologicalComplexConflationClass : ConflationClass (HomologicalComplex C c) where
  Conflation S := ∀ i, E.Conflation (S.map (HomologicalComplex.eval C c i))
  isKernelCokernelPair S hS :=
    isKernelCokernelPair_of_eval S fun i => E.isKernelCokernelPair _ (hS i)
  isClosedUnderIsomorphisms :=
    { of_iso := fun e hS i =>
        E.conflation_of_iso ((HomologicalComplex.eval C c i).mapShortComplex.mapIso e) (hS i) }

variable {E c}

/-- A morphism of complexes which is an inflation in every degree is the first map of a
degreewise conflation, whose second map is its cokernel in `HomologicalComplex C c`. -/
private theorem homologicalComplexConflationClass_isInflation_iff
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (homologicalComplexConflationClass E c).IsInflation f ↔ ∀ i, E.IsInflation (f.f i) := by
  simp only [ConflationClass.isInflation_iff]
  constructor
  · rintro ⟨M, p, zero, hS⟩ i
    exact ⟨M.X i, p.f i, by rw [← HomologicalComplex.comp_f, zero, HomologicalComplex.zero_f],
      hS i⟩
  · intro hf
    -- In each degree the conflation witnessing the inflation provides a cokernel, so `f` has a
    -- cokernel in complexes which every evaluation functor preserves.
    have : ∀ i, HasColimit (parallelPair f 0 ⋙ HomologicalComplex.eval C c i) := by
      intro i
      obtain ⟨M, p, zero, hS⟩ := hf i
      have : HasCokernel (f.f i) :=
        ⟨⟨⟨_, (E.isKernelCokernelPair _ hS).gIsCokernel⟩⟩⟩
      exact hasColimit_of_iso (F := parallelPair (f.f i) 0) (diagramIsoParallelPair _ ≪≫
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    refine ⟨cokernel f, cokernel.π f, cokernel.condition f, fun i => ?_⟩
    have hπ : IsColimit (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) :=
      cokernelIsCokernel f
    exact E.conflation_of_isColimit_of_isInflation
      ((isColimitMapCoconeCoforkEquiv' (HomologicalComplex.eval C c i) (cokernel.condition f))
        (isColimitOfPreserves (HomologicalComplex.eval C c i) hπ))
      ((ConflationClass.isInflation_iff _ _).2 (hf i))

/-- A morphism of complexes which is a deflation in every degree is the second map of a
degreewise conflation, whose first map is its kernel in `HomologicalComplex C c`. -/
private theorem homologicalComplexConflationClass_isDeflation_iff
    {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (homologicalComplexConflationClass E c).IsDeflation f ↔ ∀ i, E.IsDeflation (f.f i) := by
  simp only [ConflationClass.isDeflation_iff]
  constructor
  · rintro ⟨M, p, zero, hS⟩ i
    exact ⟨M.X i, p.f i, by rw [← HomologicalComplex.comp_f, zero, HomologicalComplex.zero_f],
      hS i⟩
  · intro hf
    -- In each degree the conflation witnessing the deflation provides a kernel, so `f` has a
    -- kernel in complexes which every evaluation functor preserves.
    have : ∀ i, HasLimit (parallelPair f 0 ⋙ HomologicalComplex.eval C c i) := by
      intro i
      obtain ⟨M, p, zero, hS⟩ := hf i
      have : HasKernel (f.f i) :=
        ⟨⟨⟨_, (E.isKernelCokernelPair _ hS).fIsKernel⟩⟩⟩
      exact hasLimit_of_iso (F := parallelPair (f.f i) 0)
        (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) ≪≫
          (diagramIsoParallelPair (parallelPair f 0 ⋙ HomologicalComplex.eval C c i)).symm)
    refine ⟨kernel f, kernel.ι f, kernel.condition f, fun i => ?_⟩
    have hι : IsLimit (KernelFork.ofι (kernel.ι f) (kernel.condition f)) := kernelIsKernel f
    exact E.conflation_of_isLimit_of_isDeflation
      ((isLimitMapConeForkEquiv' (HomologicalComplex.eval C c i) (kernel.condition f))
        (isLimitOfPreserves (HomologicalComplex.eval C c i) hι))
      ((ConflationClass.isDeflation_iff _ _).2 (hf i))

variable (E c)

/-- **The degreewise exact structure on homological complexes.** A short complex of complexes
is a conflation when it is a conflation of `E` in every degree. -/
noncomputable def homologicalComplex : ExactStructure (HomologicalComplex C c) where
  toConflationClass := homologicalComplexConflationClass E c
  isInflation_id K := (homologicalComplexConflationClass_isInflation_iff _).2 fun i => by
    simpa using E.isInflation_id (K.X i)
  isDeflation_id K := (homologicalComplexConflationClass_isDeflation_iff _).2 fun i => by
    simpa using E.isDeflation_id (K.X i)
  isInflation_comp f g hf hg := (homologicalComplexConflationClass_isInflation_iff _).2 fun i => by
    simpa using E.isInflation_comp _ _
      ((homologicalComplexConflationClass_isInflation_iff f).1 hf i)
      ((homologicalComplexConflationClass_isInflation_iff g).1 hg i)
  isDeflation_comp f g hf hg := (homologicalComplexConflationClass_isDeflation_iff _).2 fun i => by
    simpa using E.isDeflation_comp _ _
      ((homologicalComplexConflationClass_isDeflation_iff f).1 hf i)
      ((homologicalComplexConflationClass_isDeflation_iff g).1 hg i)
  hasPushouts_inflations :=
    { hasPushout := fun g hf => by
        have hf' := (homologicalComplexConflationClass_isInflation_iff _).1 hf
        have := hasColimit_span_comp_eval fun i =>
          E.hasPushouts_inflations.hasPushout (g.f i) (hf' i)
        infer_instance }
  isStableUnderCobaseChange_inflations :=
    { of_isPushout := fun {_ _ _ _ f g _ _} sq hf => by
        have hf' := (homologicalComplexConflationClass_isInflation_iff f).1 hf
        have := hasColimit_span_comp_eval fun i =>
          have := E.hasPushouts_inflations.hasPushout (g.f i) (hf' i)
          hasPushout_symmetry (f.f i) (g.f i)
        exact (homologicalComplexConflationClass_isInflation_iff _).2 fun i =>
          E.isStableUnderCobaseChange_inflations.of_isPushout
            (sq.map (HomologicalComplex.eval C c i)) (hf' i) }
  hasPullbacks_deflations :=
    { hasPullback := fun g hf => by
        have hf' := (homologicalComplexConflationClass_isDeflation_iff _).1 hf
        have := hasLimit_cospan_comp_eval fun i =>
          E.hasPullbacks_deflations.hasPullback (g.f i) (hf' i)
        infer_instance }
  isStableUnderBaseChange_deflations :=
    { of_isPullback := fun {_ _ _ _ f g _ _} sq hg => by
        have hg' := (homologicalComplexConflationClass_isDeflation_iff g).1 hg
        have := hasLimit_cospan_comp_eval fun i =>
          E.hasPullbacks_deflations.hasPullback (f.f i) (hg' i)
        exact (homologicalComplexConflationClass_isDeflation_iff _).2 fun i =>
          E.isStableUnderBaseChange_deflations.of_isPullback
            (sq.map (HomologicalComplex.eval C c i)) (hg' i) }

/-- A short complex of complexes is a conflation for the degreewise exact structure exactly when
it is a conflation in every degree. -/
@[simp]
theorem homologicalComplex_conflation_iff (S : ShortComplex (HomologicalComplex C c)) :
    (E.homologicalComplex c).Conflation S ↔
      ∀ i, E.Conflation (S.map (HomologicalComplex.eval C c i)) :=
  Iff.rfl

/-- A morphism of complexes is an inflation for the degreewise exact structure exactly when it
is an inflation in every degree. -/
@[simp]
theorem homologicalComplex_isInflation_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (E.homologicalComplex c).IsInflation f ↔ ∀ i, E.IsInflation (f.f i) :=
  homologicalComplexConflationClass_isInflation_iff f

/-- A morphism of complexes is a deflation for the degreewise exact structure exactly when it
is a deflation in every degree. -/
@[simp]
theorem homologicalComplex_isDeflation_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (E.homologicalComplex c).IsDeflation f ↔ ∀ i, E.IsDeflation (f.f i) :=
  homologicalComplexConflationClass_isDeflation_iff f

/-- Evaluation in a fixed degree preserves conflations of the degreewise exact structure. -/
theorem isConflationExact_eval_homologicalComplex (i : ι) :
    (E.homologicalComplex c).IsConflationExact E (HomologicalComplex.eval C c i) :=
  ⟨fun hS => hS i⟩

namespace IsConflationExact

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  {E} {E' : ExactStructure D} {F : C ⥤ D} [F.Additive]

/-- A conflation-exact functor induces, degreewise, a conflation-exact functor between the
degreewise exact structures on complexes. -/
theorem mapHomologicalComplex (hF : E.IsConflationExact E' F) :
    (E.homologicalComplex c).IsConflationExact (E'.homologicalComplex c)
      (F.mapHomologicalComplex c) :=
  ⟨fun hS i => hF.map_conflation (hS i)⟩

end IsConflationExact

end ExactStructure

end TauCeti

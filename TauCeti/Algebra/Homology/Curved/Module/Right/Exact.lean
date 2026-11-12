/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Abelian
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# The graded-split exact structure on curved right modules

A short complex of closed maps is a conflation when it splits after forgetting the
differentials. The graded forgetful functor preserves finite limits and colimits and reflects
isomorphisms, so these sequences are kernel-cokernel pairs. Its preservation of pushouts and
pullbacks transfers the Quillen axioms from the split exact structure on graded right modules.

These splittings are graded right-linear maps; they need not be closed maps. Thus this exact
structure records the underlying graded-module splittings used to identify its relatively
projective and injective objects with the contractible curved modules.

## References

* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Exact`: the inflation and
  deflation recognition arguments adapt its componentwise exact-structure construction.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

private def gradedSplitConflationClass : ConflationClass
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) where
  Conflation S :=
    (ExactStructure.split _).Conflation (S.map (forgetDifferential (h := h)))
  isKernelCokernelPair S hS := by
    let F := forgetDifferential (h := h)
    let : ReflectsLimit (parallelPair S.g 0) F :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    let : ReflectsColimit (parallelPair S.f 0) F :=
      reflectsColimit_of_reflectsIsomorphisms _ _
    have hpair := (ExactStructure.split _).isKernelCokernelPair (S.map F) hS
    exact
      ⟨⟨isLimitOfReflects F ((isLimitMapConeForkEquiv' F S.zero).symm hpair.fIsKernel)⟩,
        ⟨isColimitOfReflects F
          ((isColimitMapCoconeCoforkEquiv' F S.zero).symm hpair.gIsCokernel)⟩⟩
  isClosedUnderIsomorphisms :=
    { of_iso := fun e hS ↦
        (ExactStructure.split _).conflation_of_iso
          ((forgetDifferential (h := h)).mapShortComplex.mapIso e) hS }

private theorem gradedSplitConflationClass_isInflation_iff
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) :
    (gradedSplitConflationClass (h := h)).IsInflation f ↔
      (ExactStructure.split _).IsInflation ((forgetDifferential (h := h)).map f) := by
  rw [ConflationClass.isInflation_iff]
  constructor
  · rintro ⟨Z, p, hp, hS⟩
    exact (ExactStructure.split _).isInflation_f hS
  · intro hf
    refine ⟨cokernel f, cokernel.π f, cokernel.condition f, ?_⟩
    exact (ExactStructure.split _).conflation_of_isColimit_of_isInflation
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel f) (forgetDifferential (h := h))) hf

private theorem gradedSplitConflationClass_isDeflation_iff
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) :
    (gradedSplitConflationClass (h := h)).IsDeflation f ↔
      (ExactStructure.split _).IsDeflation ((forgetDifferential (h := h)).map f) := by
  rw [ConflationClass.isDeflation_iff]
  constructor
  · rintro ⟨Z, i, hi, hS⟩
    exact (ExactStructure.split _).isDeflation_g hS
  · intro hf
    refine ⟨kernel f, kernel.ι f, kernel.condition f, ?_⟩
    exact (ExactStructure.split _).conflation_of_isLimit_of_isDeflation
      (KernelFork.mapIsLimit _ (kernelIsKernel f) (forgetDifferential (h := h))) hf

/-- The exact structure whose conflations split as short complexes of graded right modules. -/
noncomputable def gradedSplitExact : ExactStructure
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) where
  toConflationClass := gradedSplitConflationClass
  isInflation_id M := by
    apply (gradedSplitConflationClass_isInflation_iff _).mpr
    rw [(forgetDifferential (h := h)).map_id M]
    exact (ExactStructure.split _).isInflation_id _
  isDeflation_id M := by
    apply (gradedSplitConflationClass_isDeflation_iff _).mpr
    rw [(forgetDifferential (h := h)).map_id M]
    exact (ExactStructure.split _).isDeflation_id _
  isInflation_comp f g hf hg := by
    rw [gradedSplitConflationClass_isInflation_iff] at hf hg ⊢
    rw [Functor.map_comp]
    exact (ExactStructure.split _).isInflation_comp _ _ hf hg
  isDeflation_comp f g hf hg := by
    rw [gradedSplitConflationClass_isDeflation_iff] at hf hg ⊢
    rw [Functor.map_comp]
    exact (ExactStructure.split _).isDeflation_comp _ _ hf hg
  hasPushouts_inflations := { hasPushout := fun _ _ ↦ inferInstance }
  isStableUnderCobaseChange_inflations :=
    { of_isPushout := fun {_ _ _ _ _ _ _ _} sq hf ↦
        (gradedSplitConflationClass_isInflation_iff _).mpr
          ((ExactStructure.split _).isStableUnderCobaseChange_inflations.of_isPushout
            (sq.map (forgetDifferential (h := h)))
            ((gradedSplitConflationClass_isInflation_iff _).mp hf)) }
  hasPullbacks_deflations := { hasPullback := fun _ _ ↦ inferInstance }
  isStableUnderBaseChange_deflations :=
    { of_isPullback := fun {_ _ _ _ _ _ _ _} sq hg ↦
        (gradedSplitConflationClass_isDeflation_iff _).mpr
          ((ExactStructure.split _).isStableUnderBaseChange_deflations.of_isPullback
            (sq.map (forgetDifferential (h := h)))
            ((gradedSplitConflationClass_isDeflation_iff _).mp hg)) }

/-- A graded-split conflation is exactly a split sequence after forgetting the differentials. -/
@[simp]
theorem gradedSplitExact_conflation_iff
    (S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))) :
    (gradedSplitExact (h := h)).Conflation S ↔
      (ExactStructure.split _).Conflation (S.map (forgetDifferential (h := h))) :=
  Iff.rfl

/-- An inflation is recognized by the underlying graded split inflation. -/
@[simp]
theorem gradedSplitExact_isInflation_iff
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) :
    (gradedSplitExact (h := h)).IsInflation f ↔
      (ExactStructure.split _).IsInflation ((forgetDifferential (h := h)).map f) :=
  gradedSplitConflationClass_isInflation_iff f

/-- A deflation is recognized by the underlying graded split deflation. -/
@[simp]
theorem gradedSplitExact_isDeflation_iff
    {M N : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)}
    (f : M ⟶ N) :
    (gradedSplitExact (h := h)).IsDeflation f ↔
      (ExactStructure.split _).IsDeflation ((forgetDifferential (h := h)).map f) :=
  gradedSplitConflationClass_isDeflation_iff f

/-- Forgetting the differential preserves graded-split conflations. -/
theorem forgetDifferential_isConflationExact :
    (gradedSplitExact (h := h)).IsConflationExact (ExactStructure.split _)
      (forgetDifferential (h := h)) where
  map_conflation {S} hS := (gradedSplitExact_conflation_iff S).mp hS

end TauCeti.CurvedDGRightModuleCat

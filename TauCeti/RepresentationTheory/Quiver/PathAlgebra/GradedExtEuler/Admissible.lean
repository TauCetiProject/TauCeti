/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedSimple
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Quotient
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Shift
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport

/-!
# Graded Euler admissibility of quiver vertex simples

For a finite quiver with finitely many arrows, the first-arrow
resolution of a vertex simple has finitely generated projective terms. Against a finite
graded module, their shifted Hom spaces have finite Laurent support. The resolution
therefore makes the vertex simple Euler-admissible.

Over a finite-dimensional path algebra, the same resolutions show that every finite graded module
has projective dimension at most one in the graded category, so its graded Ext groups vanish from
cohomological degree two on.

This is the finiteness step needed before computing the graded Ringel form from the
first-arrow resolution. The resolution follows Assem--Simson--Skowroński,
*Elements of the Representation Theory of Associative Algebras I*, Chapter III,
Sections 2--3; the q-Euler convention follows Dancso--Licata, *Koszul algebras and
flow lattices*, Section 2.2.
-/

public section

namespace TauCeti.PathAlgebra

open CategoryTheory

universe u v w t

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]
  [∀ a b : Q, Finite (a ⟶ b)]
  [HasExt.{t} (GradedModuleCat.{max u v w} (integerGrade k Q))]

/-- The shifted projective sum in the first-arrow resolution is Euler-admissible against
every finite-dimensional graded target. -/
theorem isGradedEulerAdmissible_gradedArrowSum (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedArrowSum k Q i) Y := by
  let _ := integerGradedAlgebra k Q
  let hF (a : (j : Q) × (i ⟶ j)) :
      Module.Finite (pathAlgebra k Q) ((gradedVertexProjective k Q a.1).shiftObj 1) :=
    (gradedFiniteProjectiveModules_iff.1
      (gradedFiniteProjectiveModules_shiftObj
        (gradedFiniteProjectiveModules_gradedVertexProjective k Q a.1) 1)).1
  let _ : Module.Finite (pathAlgebra k Q) (gradedArrowSum k Q i) := inferInstance
  exact isGradedEulerAdmissible_of_projective k _ _ Y
    ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj _ Y).of_equiv
      fun j ↦ (GradedModuleCat.homShiftPowEquiv (integerGrade k Q) _ Y j).symm)

omit [∀ a b : Q, Finite (a ⟶ b)] in
/-- A graded vertex projective is Euler-admissible against every finite-dimensional
graded target, even when the path algebra itself is infinite-dimensional. -/
theorem isGradedEulerAdmissible_gradedVertexProjective (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexProjective k Q i) Y := by
  let _ := integerGradedAlgebra k Q
  let _ : Module.Finite (pathAlgebra k Q) (gradedVertexProjective k Q i) :=
    (gradedFiniteProjectiveModules_iff.1
      (gradedFiniteProjectiveModules_gradedVertexProjective k Q i)).1
  exact isGradedEulerAdmissible_of_projective k _ _ Y
    ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj _ Y).of_equiv
      fun j ↦ (GradedModuleCat.homShiftPowEquiv (integerGrade k Q) _ Y j).symm)

/-- A graded vertex simple of a finite quiver is Euler-admissible
against every finite-dimensional graded target. The first-arrow resolution bounds its
cohomological Ext support, while finite generation of the projectives bounds the
internal support. -/
theorem isGradedEulerAdmissible_gradedVertexSimple (i : Q)
    (Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k Y] :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimple k Q i) Y := by
  have hA : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimpleResolution k Q i).X₁ Y := by
    simpa only [gradedVertexSimpleResolution_def] using
      isGradedEulerAdmissible_gradedArrowSum k Q i Y
  have hP : IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (integerGrade k Q))
      (gradedVertexSimpleResolution k Q i).X₂ Y := by
    simpa only [gradedVertexSimpleResolution_def] using
      isGradedEulerAdmissible_gradedVertexProjective k Q i Y
  simpa only [gradedVertexSimpleResolution_def] using
    hA.of_shortExact₃' (shortExact_gradedVertexSimpleResolution k Q i) hP

open CategoryTheory.Limits in
omit [∀ a b : Q, Finite (a ⟶ b)] in
/-- **A finite graded module over a finite-dimensional path algebra has projective dimension at
most one in the graded category.** Equivalently, its graded Ext groups into any target vanish from
cohomological degree two on, uniformly in the internal degree. -/
theorem isGradedExtBoundedBy_two_of_finite_source [FiniteDimensional k (pathAlgebra k Q)]
    (X Y : GradedModuleCat.{max u v w} (integerGrade k Q)) [Module.Finite k X] :
    IsGradedExtBoundedBy.{t} (GradedModuleCat.shift (integerGrade k Q)) X Y 2 := by
  classical
  let _ := integerGradedAlgebra k Q
  have : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  have : ∀ i j : Q, Finite (i ⟶ j) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  -- Induct along a graded composition series: a simple factor is a shifted vertex simple, whose
  -- first-arrow resolution has length one.
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hX : IsZero X
    · have : Projective X := hX.projective
      exact ⟨fun _ hn j ↦
        (isExtBoundedBy_one_of_projective.{t} X
          (((GradedModuleCat.shift (integerGrade k Q)) ^ j).functor.obj Y)).subsingleton
            (by omega)⟩
    by_cases hs : Simple X
    · obtain ⟨i, d, ⟨e⟩⟩ :=
        (isExhaustiveGradedSimpleFamily_iff _).mp
          (isExhaustiveGradedSimpleFamily_gradedVertexSimple k Q)
          ⟨X, gradedFiniteModules_iff.mpr inferInstance⟩ hs
      let _ := hasProjectiveDimensionLT_two_gradedVertexSimple k Q i
      have hb : IsGradedExtBoundedBy.{t}
          (GradedModuleCat.shift (integerGrade k Q)) (gradedVertexSimple k Q i) Y 2 :=
        ⟨fun n hn j ↦ HasProjectiveDimensionLT.subsingleton
          (gradedVertexSimple k Q i) 2 n hn _⟩
      exact (hb.shiftObj d).of_iso e.symm (Iso.refl Y)
    obtain ⟨Z, i, hi, hZ, hC, _, hdimZ, hdimC⟩ :=
      X.exists_mono_cokernel_finrank_lt hX hs
    have : Module.Finite k Z := hZ
    have : Module.Finite k (GradedModuleCat.cokernelObj i) := hC
    have hZA : Module.Finite (pathAlgebra k Q) Z :=
      Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) Z
    have hCA : Module.Finite (pathAlgebra k Q) (GradedModuleCat.cokernelObj i) :=
      Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) _
    let S := ShortComplex.mk i (GradedModuleCat.cokernelπ i) (by simp)
    have hS : S.ShortExact :=
      { exact := GradedModuleCat.exact_iff.mpr (LinearMap.exact_map_mkQ_range i.hom)
        mono_f := hi
        epi_g := (GradedModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
    simpa only [max_self] using (ih _ (hn ▸ hdimZ) Z hZA rfl).of_shortExact₂' hS
      (ih _ (hn ▸ hdimC) (GradedModuleCat.cokernelObj i) hCA rfl)

end TauCeti.PathAlgebra

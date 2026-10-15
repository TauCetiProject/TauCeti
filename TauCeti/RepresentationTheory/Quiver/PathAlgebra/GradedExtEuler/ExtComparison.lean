/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.ForgetGrading
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Dimension

/-!
# Graded and ungraded Ext over a path algebra

For finite-dimensional modules over a finite-dimensional path algebra, forgetting the grading
identifies ungraded Ext with the direct sum of graded Ext over all internal degrees. In degree zero
this is the homogeneous decomposition of an ungraded module map. Both graded and ungraded Ext
vanish above degree one because a path algebra of a finite acyclic quiver is hereditary. Equality
of the degree-one dimensions then follows from the specialization at `q = 1` of the graded Euler
characteristic.

The comparison predicate only asks for the existence of a linear equivalence in each
cohomological degree. Accordingly, the degree-one equivalence below is chosen from equality of
finite dimensions; no compatibility with connecting maps is asserted.

## Main results

* `TauCeti.PathAlgebra.isGradedExtBoundedBy_two_of_finite_source`: graded Ext from a finite
  graded source vanishes in cohomological degrees at least two.
* `TauCeti.PathAlgebra.gradedExtZeroForgetEquiv`: the direct sum of degree-zero graded Ext groups
  is canonically equivalent to ungraded degree-zero Ext.
* `TauCeti.PathAlgebra.isGradedExtComparison_forget`: the graded Ext groups assemble into the Ext
  groups of the underlying ungraded modules.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for hereditary path algebras and graded modules.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for homogeneous
  decomposition of maps between finite-dimensional graded modules.
-/

public section

noncomputable section

open scoped DirectSum

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped ModuleCat

universe u v

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]
  [HasExt.{max u v} (GradedModuleCat.{max u v} (integerGrade k Q))]

/-- **A finite graded module over a finite-dimensional path algebra has projective dimension at
most one in the graded category.** Equivalently, its graded Ext groups into any target vanish from
cohomological degree two on, uniformly in the internal degree.

The proof reduces along a graded composition series to shifted vertex simples, whose first-arrow
resolutions have length one. -/
theorem isGradedExtBoundedBy_two_of_finite_source
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q))
    [Module.Finite k X] :
    IsGradedExtBoundedBy.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y 2 := by
  classical
  let _ := integerGradedAlgebra k Q
  have : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  have : ∀ i j : Q, Finite (i ⟶ j) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  induction hn : Module.finrank k X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    by_cases hX : IsZero X
    · have : Projective X := hX.projective
      exact ⟨fun _ hn j ↦
        (isExtBoundedBy_one_of_projective.{max u v} X
          (((GradedModuleCat.shift (integerGrade k Q)) ^ j).functor.obj Y)).subsingleton
            (by omega)⟩
    by_cases hs : Simple X
    · obtain ⟨i, d, ⟨e⟩⟩ :=
        (isExhaustiveGradedSimpleFamily_iff _).mp
          (isExhaustiveGradedSimpleFamily_gradedVertexSimple k Q)
          ⟨X, gradedFiniteModules_iff.mpr inferInstance⟩ hs
      let _ := hasProjectiveDimensionLT_two_gradedVertexSimple k Q i
      have hb : IsGradedExtBoundedBy.{max u v}
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

/-- Regard an `A`-linear map between graded modules as a morphism of the underlying module
objects. The two induced `k`-actions agree by the scalar-tower law. -/
private def linearMapForgetEquiv
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q)) :
    (X →ₗ[pathAlgebra k Q] Y) ≃ₗ[k]
      (GradedModuleCat.toModuleCat.obj X ⟶ GradedModuleCat.toModuleCat.obj Y) where
  toFun := ModuleCat.ofHom
  invFun := ModuleCat.Hom.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c f := by
    apply ModuleCat.hom_ext
    ext x
    change c • f x = algebraMap k (pathAlgebra k Q) c • f x
    exact (algebraMap_smul (pathAlgebra k Q) c (f x)).symm

/-- **Degree-zero graded Ext assembles canonically into ungraded degree-zero Ext.** The
equivalence decomposes an ungraded module map into its finitely many homogeneous parts. -/
def gradedExtZeroForgetEquiv
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q))
    [Module.Finite k X] [Module.Finite k Y] :
    (⨁ j : ℤ, GradedExt.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y 0 j) ≃ₗ[k]
      Ext.{max u v} (GradedModuleCat.toModuleCat.obj X)
        (GradedModuleCat.toModuleCat.obj Y) 0 := by
  let _ := integerGradedAlgebra k Q
  exact (DirectSum.congrLinearEquiv fun j ↦
      (Ext.linearEquiv₀ (R := k)).trans
        (GradedModuleCat.homShiftPowEquiv (integerGrade k Q) X Y j)).trans
    ((GradedModuleCat.homShiftDirectSumEquiv X Y).trans
      ((linearMapForgetEquiv k Q X Y).trans
          (Ext.linearEquiv₀ (R := k) (X := GradedModuleCat.toModuleCat.obj X)
            (Y := GradedModuleCat.toModuleCat.obj Y)).symm))

/-- In cohomological degree one, the sum of the graded Ext dimensions equals the ungraded Ext
dimension after forgetting the grading. -/
private theorem finrank_directSum_gradedExt_one_eq_ext_one
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q))
    [Module.Finite k X] [Module.Finite k Y] :
    Module.finrank k
        (⨁ j : ℤ, GradedExt.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y 1 j) =
      Module.finrank k
        (Ext.{max u v} (GradedModuleCat.toModuleCat.obj X)
          (GradedModuleCat.toModuleCat.obj Y) 1) := by
  let _ := integerGradedAlgebra k Q
  have hA : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  have hB : Module.Finite (pathAlgebra k Q) Y :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) Y
  let _ : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj X) := hA
  let _ : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj Y) := hB
  have : Module.Finite k (GradedModuleCat.toModuleCat.obj X) :=
    Module.Finite.trans (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj X)
  have : Module.Finite k (GradedModuleCat.toModuleCat.obj Y) :=
    Module.Finite.trans (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj Y)
  have hg := (isGradedEulerAdmissibleOn_gradedFiniteModules k Q).isGradedEulerAdmissible
    (gradedFiniteModules_iff.mpr hA) (gradedFiniteModules_iff.mpr hB)
  have hu : IsEulerAdmissible.{max u v} k (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y) :=
    (isEulerAdmissibleOn_isFG_pathAlgebra k Q).isEulerAdmissible
    ((ModuleCat.isFG_iff _).mpr hA) ((ModuleCat.isFG_iff _).mpr hB)
  have hgb := isGradedExtBoundedBy_two_of_finite_source k Q X Y
  have hQ : Quiver.IsAcyclic Q :=
    isAcyclic_of_module_finite_pathAlgebra k Q inferInstance
  let _ : ∀ i j : Q, Finite (i ⟶ j) := fun i j ↦
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance i j
  have hub : IsExtBoundedBy.{max u v} (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y) 2 :=
    ⟨fun n hn ↦ by
      let _ := hasProjectiveDimensionLT_two_pathAlgebra_of_finiteDimensional k Q hQ
        (GradedModuleCat.toModuleCat.obj X)
      exact HasProjectiveDimensionLT.subsingleton _ 2 n hn _⟩
  have heuler := laurentEval_one_gradedExtEuler_eq_extEuler k Q X Y hg hu
  rw [gradedExtEuler_eq k _ hg hgb, extEuler_eq k hu hub] at heuler
  simp only [truncatedGradedExtEuler_succ, truncatedGradedExtEuler_zero, zero_add, pow_zero,
    one_smul, pow_one, neg_smul, map_add, map_neg,
    gradedExtDimension_eq_targetShiftGradedDimension,
    laurentEval_one_targetShiftGradedDimension, truncatedExtEuler_succ,
    truncatedExtEuler_zero, one_mul, neg_one_mul] at heuler
  have hzero := (gradedExtZeroForgetEquiv k Q X Y).finrank_eq
  omega

/-- **Forgetting the grading compares graded and ungraded Ext over a path algebra.** In every
cohomological degree, ungraded Ext is linearly equivalent to the direct sum over all internal
degrees of graded Ext. -/
theorem isGradedExtComparison_forget
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q))
    [Module.Finite k X] [Module.Finite k Y] :
    IsGradedExtComparison.{max u v, max u v} k
      (GradedModuleCat.shift (integerGrade k Q)) X Y
      (GradedModuleCat.toModuleCat.obj X) (GradedModuleCat.toModuleCat.obj Y) := by
  let _ := integerGradedAlgebra k Q
  have hA : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  have hB : Module.Finite (pathAlgebra k Q) Y :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) Y
  let _ : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj X) := hA
  let _ : Module.Finite (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj Y) := hB
  have : Module.Finite k (GradedModuleCat.toModuleCat.obj X) :=
    Module.Finite.trans (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj X)
  have : Module.Finite k (GradedModuleCat.toModuleCat.obj Y) :=
    Module.Finite.trans (pathAlgebra k Q) (GradedModuleCat.toModuleCat.obj Y)
  have hg := (isGradedEulerAdmissibleOn_gradedFiniteModules k Q).isGradedEulerAdmissible
    (gradedFiniteModules_iff.mpr hA) (gradedFiniteModules_iff.mpr hB)
  have hu : IsEulerAdmissible.{max u v} k (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y) :=
    (isEulerAdmissibleOn_isFG_pathAlgebra k Q).isEulerAdmissible
    ((ModuleCat.isFG_iff _).mpr hA) ((ModuleCat.isFG_iff _).mpr hB)
  have hgb := isGradedExtBoundedBy_two_of_finite_source k Q X Y
  have hQ : Quiver.IsAcyclic Q :=
    isAcyclic_of_module_finite_pathAlgebra k Q inferInstance
  let _ : ∀ i j : Q, Finite (i ⟶ j) := fun i j ↦
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance i j
  have hub : IsExtBoundedBy.{max u v} (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y) 2 :=
    ⟨fun n hn ↦ by
      let _ := hasProjectiveDimensionLT_two_pathAlgebra_of_finiteDimensional k Q hQ
        (GradedModuleCat.toModuleCat.obj X)
      exact HasProjectiveDimensionLT.subsingleton _ 2 n hn _⟩
  refine ⟨fun n ↦ ⟨?_⟩⟩
  cases n with
  | zero => exact gradedExtZeroForgetEquiv k Q X Y
  | succ n =>
      cases n with
      | zero =>
          have := (hg.internallyFinite.finiteLaurentSupport 1).finiteDimensional_directSum
          have := hu.isExtFinite.finiteDimensional 1
          exact LinearEquiv.ofFinrankEq _ _
            (finrank_directSum_gradedExt_one_eq_ext_one k Q X Y)
      | succ n =>
          letI (j : ℤ) : Subsingleton
              (GradedExt.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y (n + 2) j) :=
            hgb.subsingleton (by omega) j
          letI : Subsingleton
              (Ext.{max u v} (GradedModuleCat.toModuleCat.obj X)
                (GradedModuleCat.toModuleCat.obj Y) (n + 2)) :=
            hub.subsingleton (by omega)
          exact LinearEquiv.ofSubsingleton _ _

end TauCeti.PathAlgebra

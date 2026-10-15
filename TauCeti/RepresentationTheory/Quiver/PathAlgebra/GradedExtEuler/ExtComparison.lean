/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.Basic
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.ExtZero
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.ForgetGrading
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Dimension

/-!
# Graded and ungraded Ext over a path algebra

For finite-dimensional modules over a finite-dimensional path algebra, forgetting the grading
identifies ungraded Ext with the direct sum of graded Ext over all internal degrees. In degree zero
this is the homogeneous decomposition `TauCeti.GradedModuleCat.gradedExtZeroForgetEquiv` of an
ungraded module map. Both graded and ungraded Ext vanish above degree one because a path algebra of
a finite acyclic quiver is hereditary. Equality of the degree-one dimensions then follows from the
specialization at `q = 1` of the graded Euler characteristic.

The comparison predicate only asks for the existence of a linear equivalence in each
cohomological degree. Accordingly, the degree-one equivalence below is chosen from equality of
finite dimensions; no compatibility with connecting maps is asserted.

## Main results

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

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat

universe u v

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]
  [HasExt.{max u v} (GradedModuleCat.{max u v} (integerGrade k Q))]

omit [HasExt (GradedModuleCat (integerGrade k Q))] in
/-- Ungraded Ext out of a finite-dimensional module over a finite-dimensional path algebra
vanishes from cohomological degree two on. -/
private theorem isExtBoundedBy_two_of_finiteDimensional
    (M N : ModuleCat.{max u v} (pathAlgebra k Q)) [FiniteDimensional k M] :
    IsExtBoundedBy.{max u v} M N 2 := by
  have : ∀ i j : Q, Finite (i ⟶ j) :=
    finite_hom_of_module_finite_pathAlgebra k Q inferInstance
  let _ := hasProjectiveDimensionLT_two_pathAlgebra_of_finiteDimensional k Q
    (isAcyclic_of_module_finite_pathAlgebra k Q inferInstance) M
  exact ⟨fun n hn ↦ HasProjectiveDimensionLT.subsingleton M 2 n hn N⟩

/-- In cohomological degree one, the sum of the graded Ext dimensions equals the ungraded Ext
dimension after forgetting the grading. -/
private theorem finrank_directSum_gradedExt_one_eq_ext_one
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q)) [Module.Finite k X] [Module.Finite k Y]
    [Module.Finite (pathAlgebra k Q) X] [FiniteDimensional k (GradedModuleCat.toModuleCat.obj X)]
    (hg : IsGradedEulerAdmissible.{max u v} k (GradedModuleCat.shift (integerGrade k Q)) X Y)
    (hu : IsEulerAdmissible.{max u v} k (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y)) :
    Module.finrank k
        (⨁ j : ℤ, GradedExt.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y 1 j) =
      Module.finrank k
        (Ext.{max u v} (GradedModuleCat.toModuleCat.obj X)
          (GradedModuleCat.toModuleCat.obj Y) 1) := by
  let _ := integerGradedAlgebra k Q
  have heuler := laurentEval_one_gradedExtEuler_eq_extEuler k Q X Y hg hu
  rw [gradedExtEuler_eq k _ hg (isGradedExtBoundedBy_two_of_finite_source k Q X Y),
    extEuler_eq k hu (isExtBoundedBy_two_of_finiteDimensional k Q _ _)] at heuler
  simp only [truncatedGradedExtEuler_succ, truncatedGradedExtEuler_zero, zero_add, pow_zero,
    one_smul, pow_one, neg_smul, map_add, map_neg,
    gradedExtDimension_eq_targetShiftGradedDimension,
    laurentEval_one_targetShiftGradedDimension, truncatedExtEuler_succ,
    truncatedExtEuler_zero, one_mul, neg_one_mul] at heuler
  have hzero := (GradedModuleCat.gradedExtZeroForgetEquiv.{max u v, max u v}
    (k := k) (integerGrade k Q) X Y).finrank_eq
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
  have hg := (isGradedEulerAdmissibleOn_gradedFiniteModules k Q).isGradedEulerAdmissible
    (gradedFiniteModules_iff.mpr hA) (gradedFiniteModules_iff.mpr hB)
  have hu : IsEulerAdmissible.{max u v} k (GradedModuleCat.toModuleCat.obj X)
      (GradedModuleCat.toModuleCat.obj Y) :=
    (isEulerAdmissibleOn_isFG_pathAlgebra k Q).isEulerAdmissible
    ((ModuleCat.isFG_iff _).mpr hA) ((ModuleCat.isFG_iff _).mpr hB)
  refine ⟨fun n ↦ ⟨?_⟩⟩
  cases n with
  | zero => exact GradedModuleCat.gradedExtZeroForgetEquiv (integerGrade k Q) X Y
  | succ n =>
      cases n with
      | zero =>
          have := (hg.internallyFinite.finiteLaurentSupport 1).finiteDimensional_directSum
          have := hu.isExtFinite.finiteDimensional 1
          exact LinearEquiv.ofFinrankEq _ _
            (finrank_directSum_gradedExt_one_eq_ext_one k Q X Y hg hu)
      | succ n =>
          letI (j : ℤ) : Subsingleton
              (GradedExt.{max u v} (GradedModuleCat.shift (integerGrade k Q)) X Y (n + 2) j) :=
            (isGradedExtBoundedBy_two_of_finite_source k Q X Y).subsingleton (by omega) j
          letI : Subsingleton
              (Ext.{max u v} (GradedModuleCat.toModuleCat.obj X)
                (GradedModuleCat.toModuleCat.obj Y) (n + 2)) :=
            (isExtBoundedBy_two_of_finiteDimensional k Q _ _).subsingleton (by omega)
          exact LinearEquiv.ofSubsingleton _ _

end TauCeti.PathAlgebra

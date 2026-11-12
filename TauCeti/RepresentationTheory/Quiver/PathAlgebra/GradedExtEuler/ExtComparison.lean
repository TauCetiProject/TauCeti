/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.ForgetGrading.Comparison
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# Graded and ungraded Ext over a path algebra

For finite-dimensional modules over a finite-dimensional path algebra with its path-length
grading, forgetting the grading identifies ungraded Ext with the direct sum of graded Ext over all
internal degrees. The identification is the natural comparison
`TauCeti.GradedModuleCat.gradedExtForgetEquiv`, which is compatible with the connecting maps of
both long exact Ext sequences; a finite-dimensional path algebra is Noetherian and a
finite-dimensional module over it is finitely generated.

## Main results

* `TauCeti.PathAlgebra.isGradedExtComparison_forget`: the graded Ext groups assemble into the Ext
  groups of the underlying ungraded modules.
-/

public section

namespace TauCeti.PathAlgebra

open CategoryTheory CategoryTheory.Abelian

universe u v

variable (k : Type (max u v)) (Q : Type u) [Field k] [Quiver.{v} Q]
  [Finite Q] [FiniteDimensional k (pathAlgebra k Q)]
  [HasExt.{max u v} (GradedModuleCat.{max u v} (integerGrade k Q))]

/-- **Forgetting the grading compares graded and ungraded Ext over a path algebra.** In every
cohomological degree, ungraded Ext is linearly equivalent to the direct sum over all internal
degrees of graded Ext. -/
theorem isGradedExtComparison_forget
    (X Y : GradedModuleCat.{max u v} (integerGrade k Q)) [Module.Finite k X] :
    IsGradedExtComparison.{max u v, max u v} k
      (GradedModuleCat.shift (integerGrade k Q)) X Y
      (GradedModuleCat.toModuleCat.obj X) (GradedModuleCat.toModuleCat.obj Y) := by
  let _ := integerGradedAlgebra k Q
  have : IsNoetherianRing (pathAlgebra k Q) := isNoetherian_of_tower k inferInstance
  have : Module.Finite (pathAlgebra k Q) X :=
    Module.Finite.of_restrictScalars_finite k (pathAlgebra k Q) X
  exact GradedModuleCat.isGradedExtComparison_toModuleCat X Y

end TauCeti.PathAlgebra

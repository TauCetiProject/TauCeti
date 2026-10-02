/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.GeneralLinearGroup
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the determinant in the module topology

On a finite free module, the determinant of an endomorphism is a polynomial in its matrix
coordinates. The module topology on the endomorphism algebra makes the change to matrix
coordinates continuous, so the determinant is continuous without choosing a norm on the module.
-/

public section

namespace TauCeti

namespace LinearMap

variable {K V : Type*} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V]

/-- The determinant is continuous on the endomorphism algebra with its module topology. -/
@[continuity, fun_prop]
theorem continuous_det_moduleTopology :
    Continuous (fun f : Module.End K V => LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis K V
  have hm : Continuous (fun f : Module.End K V => LinearMap.toMatrix b b f) :=
    IsModuleTopology.continuous_of_linearMap (LinearMap.toMatrixAlgEquiv b).toLinearMap
  convert Continuous.matrix_det hm using 1
  funext f
  exact (LinearMap.det_toMatrix b f).symm

end LinearMap

end TauCeti

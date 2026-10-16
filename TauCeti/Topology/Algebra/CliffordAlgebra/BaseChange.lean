/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.BaseChange
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Continuous scalar extension for Clifford point groups

For a continuous homomorphism of commutative rings carrying topologies `K → L`, with `2`
invertible in `K`, the canonical map from a Clifford algebra over `K` to the Clifford algebra of
the scalar-extended quadratic space over `L` is continuous in the module topologies. Its
restrictions to the Lipschitz and Spin groups are therefore continuous as well.

This supplies the topological compatibility needed to compare Clifford point groups over a global
field with their localizations.

## Main results

* `CliffordAlgebra.continuous_ofBaseChangeAux`: the canonical Clifford-algebra map is continuous.
* `CliffordAlgebra.continuous_lipschitzGroupBaseChange`: scalar extension on Lipschitz groups is
  continuous.
* `CliffordAlgebra.continuous_spinGroupBaseChange`: scalar extension on Spin groups is continuous.
-/

public section

open scoped TensorProduct

namespace CliffordAlgebra

universe u v w

variable {K : Type u} {L : Type v} {V : Type w}
  [CommRing K] [CommRing L] [Algebra K L]
  [TopologicalSpace K] [TopologicalSpace L]
  [AddCommGroup V] [Module K V] [Invertible (2 : K)]

/-- The canonical map to the Clifford algebra of a scalar extension is continuous for the module
topologies when the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_ofBaseChangeAux (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (ofBaseChangeAux L Q) := by
  let F : CliffordAlgebra Q →ₛₗ[algebraMap K L] CliffordAlgebra (Q.baseChange L) :=
    { (ofBaseChangeAux L Q).toLinearMap with
      map_smul' := fun c x =>
        (map_smul (ofBaseChangeAux L Q) c x).trans
          (IsScalarTower.algebraMap_smul L c (ofBaseChangeAux L Q x)).symm }
  let _ : ContinuousAdd (CliffordAlgebra (Q.baseChange L)) :=
    IsModuleTopology.toContinuousAdd L _
  exact IsModuleTopology.continuous_of_linearMapₛₗ hKL F

/-- Extension of scalars is continuous on Lipschitz groups when the scalar homomorphism is
continuous. -/
@[fun_prop]
theorem continuous_lipschitzGroupBaseChange (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (lipschitzGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  have hUnits : Continuous (Units.map (ofBaseChangeAux L Q).toMonoidHom) :=
    (continuous_ofBaseChangeAux hKL Q).units_map _
  exact (hUnits.comp continuous_subtype_val).congr fun x => by
    apply Units.ext
    exact (coe_lipschitzGroupBaseChange_apply (A := L) Q x).symm

/-- Extension of scalars is continuous on Spin groups when the scalar homomorphism is continuous. -/
@[fun_prop]
theorem continuous_spinGroupBaseChange (hKL : Continuous (algebraMap K L))
    (Q : QuadraticForm K V) : Continuous (spinGroupBaseChange (A := L) Q) := by
  apply continuous_induced_rng.mpr
  exact ((continuous_ofBaseChangeAux hKL Q).comp continuous_subtype_val).congr fun x =>
    (coe_spinGroupBaseChange_apply (A := L) Q x).symm

end CliffordAlgebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Complexification
public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic

/-!
# Continuity of complex conjugation on a complexified Clifford algebra

For a real quadratic form `Q`, complex conjugation `CliffordAlgebra.complexConj` of the
coefficients of the complexified Clifford algebra `Cℓ(ℂ ⊗ V, Q_ℂ)` is conjugate-linear, hence
continuous for the module topology.

## Main results

* `CliffordAlgebra.continuous_complexConj`: complex conjugation of the coefficients is continuous.
-/

public section

namespace CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Complex conjugation of the coefficients of a complexified Clifford algebra is continuous for
the module topology, being conjugate-linear (`CliffordAlgebra.complexConj_smul`). -/
@[fun_prop]
theorem continuous_complexConj (Q : QuadraticForm ℝ V) : Continuous (complexConj Q) :=
  IsModuleTopology.continuous_of_linearMapₛₗ Complex.continuous_conj
    ({ toFun := complexConj Q
       map_add' := map_add (complexConj Q)
       map_smul' := complexConj_smul Q } :
      CliffordAlgebra (Q.baseChange ℂ) →ₛₗ[starRingEnd ℂ] CliffordAlgebra (Q.baseChange ℂ))

end CliffordAlgebra

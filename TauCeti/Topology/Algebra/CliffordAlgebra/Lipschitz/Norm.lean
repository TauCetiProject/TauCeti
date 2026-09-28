/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.CliffordAlgebra.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.ReverseNorm
import Mathlib.Topology.Algebra.Group.Units

/-!
# Continuity of the Clifford norm

The reverse Clifford norm on the Lipschitz group is continuous over a complete normed field.
Its scalar value is recovered from `reverse x * x` through the closed embedding of the field
into the finite-dimensional Clifford algebra. The inverse coordinate of the unit-valued norm
is continuous by the homomorphism law. This is the local topological input for studying the
spinor norm through the Clifford norm.
-/

public section

namespace CliffordAlgebra

open TauCeti Topology

variable {K V : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [Invertible (2 : K)] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (Q : QuadraticForm K V)

/-- The reverse Clifford norm is continuous on the Lipschitz group. -/
@[fun_prop]
theorem continuous_cliffordNorm : Continuous (cliffordNorm Q) := by
  have hscalar : Continuous (fun x : lipschitzGroup Q => (cliffordNorm Q x : K)) := by
    apply (isClosedEmbedding_algebraMap Q).isEmbedding.continuous_iff.mpr
    have hval : Continuous (fun x : lipschitzGroup Q =>
        (((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) :=
      Units.continuous_val.comp continuous_subtype_val
    convert ((continuous_reverse Q).comp hval).mul hval using 1
    funext x
    exact (reverse_mul_self_eq_algebraMap_cliffordNorm x).symm
  exact Continuous.of_coeHom_comp hscalar

end CliffordAlgebra

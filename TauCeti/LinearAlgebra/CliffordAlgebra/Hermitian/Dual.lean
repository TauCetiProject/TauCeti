/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian.Complex

/-!
# The positive metric on the reverse-dual Clifford module

The algebraic reverse-dual action is `(a · φ)(s) = φ (ρ (reverse a) s)`. For a
finite-dimensional Hermitian Clifford module, its dual carries the positive Hermitian form
`InnerProductSpace.dualMetric`. This file proves that this action is compatible with that
form and the conjugate-linear Clifford adjoint `CliffordAlgebra.conjStar`.

Riesz duality identifies the transpose action with the adjoint of `ρ (reverse a)`, not
with the adjoint of `ρ a`. Thus algebraic reverse duality and Hermitian adjunction remain
distinct. On real vectors, the dual action is skew-Hermitian, just as the original action.
The statements include the zero module and do not require irreducibility or a nonzero rank.

The metric is the Riesz-transported positive dual metric, with no choice of a basis and no
new global inner product or star instance.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

open CliffordAlgebra InnerProductSpace
open scoped TensorProduct

namespace AlgHom

variable {V S : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  (ρ : CliffordAlgebra (Q.baseChange ℂ) →ₐ[ℂ] Module.End ℂ S)

/-- Real Clifford vectors act skew-Hermitianly on the positive dual metric whenever they do
on the original module. -/
theorem dualMetric_cliffordReverseDual_ι_left
    (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
    (v : V) (φ ψ : Module.Dual ℂ S) :
    dualMetric ℂ S (ρ.cliffordReverseDual (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) φ) ψ =
      -dualMetric ℂ S φ (ρ.cliffordReverseDual (ι (Q.baseChange ℂ) (1 ⊗ₜ v)) ψ) := by
  rw [cliffordReverseDual_ι, LinearMap.dualMetric_dualMap_left, hρ]
  simp [LinearMap.dualMap_def]

/-- The reverse-dual Clifford module is a representation of the conjugate-linear Clifford
adjoint for its positive dual metric. The hypothesis can be checked just on real vectors. -/
theorem dualMetric_cliffordReverseDual_left
    (hρ : ∀ v : V, (ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v))).adjoint =
      -ρ (ι (Q.baseChange ℂ) (1 ⊗ₜ v)))
    (a : CliffordAlgebra (Q.baseChange ℂ)) (φ ψ : Module.Dual ℂ S) :
    dualMetric ℂ S (ρ.cliffordReverseDual a φ) ψ =
      dualMetric ℂ S φ (ρ.cliffordReverseDual (conjStar Q a) ψ) :=
  sesqForm_map_eq_map_conjStar ρ.cliffordReverseDual (dualMetric ℂ S)
    (ρ.dualMetric_cliffordReverseDual_ι_left hρ) a φ ψ

end AlgHom

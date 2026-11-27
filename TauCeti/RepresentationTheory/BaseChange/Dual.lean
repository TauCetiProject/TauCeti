/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Dual.BaseChange
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Scalar extension of dual representations

Compatibility between the scalar extension of the dual of a representation and the dual of the
scalar-extended representation, mediated by `TauCeti.Module.Dual.baseChangeEvaluation` (and
`TauCeti.Module.Dual.baseChangeEvaluationEquiv` for finite projective modules).

## Main results

* `Representation.dual_baseChange_baseChangeEvaluation`: `TauCeti.Module.Dual.baseChangeEvaluation`
  intertwines `(ρ.dual).baseChange A` with `(ρ.baseChange A).dual`.
* `Representation.dual_baseChange_baseChangeEvaluationEquiv`: the same intertwining identity for
  `TauCeti.Module.Dual.baseChangeEvaluationEquiv` when the module is finite projective.
-/

public section

open scoped TensorProduct

namespace Representation

/-- Scalar-extended evaluation intertwines the base change of the dual representation with the
dual of the base-changed representation. -/
theorem dual_baseChange_baseChangeEvaluation
    {R A G M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Group G]
    [AddCommMonoid M] [Module R M]
    (ρ : Representation R G M) (g : G) (ψ : A ⊗[R] Module.Dual R M) :
    (ρ.baseChange A).dual g (TauCeti.Module.Dual.baseChangeEvaluation ψ) =
      TauCeti.Module.Dual.baseChangeEvaluation ((ρ.dual.baseChange A) g ψ) := by
  induction ψ using TensorProduct.inductionOn with
  | tmul s φ =>
    apply LinearMap.ext; intro z
    induction z using TensorProduct.inductionOn with
    | tmul t v =>
      simp [TauCeti.Module.Dual.baseChangeEvaluation_tmul, dual_apply,
        Module.Dual.transpose_apply, LinearMap.baseChange_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On a finite projective module, `TauCeti.Module.Dual.baseChangeEvaluationEquiv` intertwines
the base change of the dual representation with the dual of the base-changed representation. -/
theorem dual_baseChange_baseChangeEvaluationEquiv
    {R A G M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [Group G]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (ρ : Representation R G M) (g : G) (ψ : A ⊗[R] Module.Dual R M) :
    (ρ.baseChange A).dual g (TauCeti.Module.Dual.baseChangeEvaluationEquiv ψ) =
      TauCeti.Module.Dual.baseChangeEvaluationEquiv ((ρ.dual.baseChange A) g ψ) := by
  simpa only [TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply] using
    ρ.dual_baseChange_baseChangeEvaluation g ψ

end Representation

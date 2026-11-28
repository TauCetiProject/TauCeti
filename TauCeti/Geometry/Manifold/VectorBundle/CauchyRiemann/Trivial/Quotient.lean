/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
import TauCeti.Geometry.Manifold.Algebra.Quotient.Tangent

/-!
# `∂bar` on functions over a quotient `ℂ ⧸ Λ`

Let `Λ` be a discrete subgroup of `ℂ`, so that `ℂ ⧸ Λ` is a complex manifold whose tangent spaces
are all `ℂ`. For a function `σ` on `ℂ ⧸ Λ`, `∂bar σ` at the class of `z` is the conjugate
Wirtinger derivative of its lift `σ ∘ (↑)` at `z`
(`TauCeti.SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_quotientMk_apply`).
-/

public section

open scoped Manifold

namespace TauCeti

variable {Λ : AddSubgroup ℂ} [DiscreteTopology Λ]

/-- `∂bar` of a function on `ℂ ⧸ Λ`, at the class of `z`, is the conjugate Wirtinger derivative
of its lift to `ℂ` at `z`. -/
theorem SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_quotientMk_apply
    (σ : ℂ ⧸ Λ → ℂ) (z v : ℂ) :
    (ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction σ z v =
      conjWirtingerDeriv (fun w : ℂ ↦ σ w) z v := by
  have hJ : (ofComplexManifold ℂ (ℂ ⧸ Λ)) (z : ℂ ⧸ Λ) v = Complex.I * v :=
    ofComplexManifold_apply _ v
  refine ((ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction_apply σ (z : ℂ ⧸ Λ) v).trans ?_
  rw [hJ, AddSubgroup.mvfderiv_quotientMk_apply, AddSubgroup.mvfderiv_quotientMk_apply,
    conjWirtingerDeriv_apply]
  simp [Complex.real_smul]
  ring

end TauCeti

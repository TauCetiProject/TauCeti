/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Domain-defined perturbations of partial linear maps

Adding a linear map defined on the domain of a partial map preserves that domain.

## Provenance

Adapted from the Apache-2.0 Spectra formalization
(`Spectra/Operator/KatoRellich.lean`, commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`; copyright (c) 2026
Spectra Formalization Project), through the Kitware DKPS formalization.
-/

public section

namespace LinearPMap

section Algebraic

variable {R E F : Type*} [Ring R]
variable [AddCommGroup E] [AddCommGroup F] [Module R E] [Module R F]

/-- Add a map defined on `dom A` to `A`, keeping the domain unchanged. -/
def perturb (A : E →ₗ.[R] F) (V : A.domain →ₗ[R] F) : E →ₗ.[R] F where
  domain := A.domain
  toFun := A.toFun + V

/-- Perturbing leaves the domain alone — that is the point of `perturb`, and
what lets a perturbed operator be compared with the original on the nose. -/
@[simp] theorem perturb_domain (A : E →ₗ.[R] F) (V : A.domain →ₗ[R] F) :
    (perturb A V).domain = A.domain := (rfl)
/-- The perturbed map acts by `A + V` pointwise on the shared domain. -/
@[simp] theorem perturb_apply (A : E →ₗ.[R] F) (V : A.domain →ₗ[R] F)
    (ψ : A.domain) :
    perturb A V ⟨(ψ : E), (perturb_domain A V).symm ▸ ψ.property⟩ = A ψ + V ψ := by
  rfl

end Algebraic

end LinearPMap

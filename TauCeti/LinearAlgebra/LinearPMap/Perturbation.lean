/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Domain-defined perturbations of partial linear maps

Adding a (semi)linear map defined on the domain of a partial (semi)linear map
`A : E →ₛₗ.[σ] F` gives a partial map `A.perturb V` with the same domain, acting by
`A x + V x`. Unlike Mathlib's `f +ᵥ A`, the perturbation `V : A.domain →ₛₗ[σ] F` need only
be defined on the domain of `A`.

## Provenance

Adapted from the Apache-2.0 Spectra formalization
(`Spectra/Operator/KatoRellich.lean`, commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`; copyright (c) 2026
Spectra Formalization Project), through the Kitware DKPS formalization.
-/

public section

namespace LinearPMap

section Algebraic

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S}
variable [AddCommGroup E] [AddCommGroup F] [Module R E] [Module S F]

/-- Add a map defined on `dom A` to `A`, keeping the domain unchanged. -/
def perturb (A : E →ₛₗ.[σ] F) (V : A.domain →ₛₗ[σ] F) : E →ₛₗ.[σ] F where
  domain := A.domain
  toFun := A.toFun + V

/-- Perturbing leaves the domain alone — that is the point of `perturb`, and
what lets a perturbed operator be compared with the original on the nose. -/
@[simp] theorem perturb_domain (A : E →ₛₗ.[σ] F) (V : A.domain →ₛₗ[σ] F) :
    (perturb A V).domain = A.domain := (rfl)

/-- The perturbed map acts by `A + V` pointwise on the shared domain. -/
@[simp] theorem perturb_apply (A : E →ₛₗ.[σ] F) (V : A.domain →ₛₗ[σ] F)
    (x : (perturb A V).domain) :
    perturb A V x = A ⟨x, perturb_domain A V ▸ x.2⟩ + V ⟨x, perturb_domain A V ▸ x.2⟩ := by
  rfl

end Algebraic

end LinearPMap

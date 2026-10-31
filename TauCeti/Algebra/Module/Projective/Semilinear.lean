/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective

/-!
# Lifting semilinear maps out of a projective module

Let `σ : R →+* S` be a ring homomorphism, `P` a projective `R`-module and `F : M → N` a
surjective `S`-linear map. Then every `σ`-semilinear map `P → N` lifts through `F` to a
`σ`-semilinear map `P → M`. This is Mathlib's lifting property
`Module.projective_lifting_property` applied to `M` and `N` with scalars restricted along `σ`,
since a `σ`-semilinear map out of `P` is an `R`-linear map into the restricted module.

It is the form of the lifting property used to show that extension of scalars along a ring
homomorphism of possibly noncommutative rings preserves projectivity: an `S`-linear map out of
`S ⊗_R P` is the same as a `σ`-semilinear map out of `P`.

## Main results

* `Module.projective_lifting_property_semilinear`: semilinear maps out of a projective module lift
  along surjective linear maps.
-/

public section

namespace Module

variable {R S : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  {P : Type*} [AddCommMonoid P] [Module R P]
  {M N : Type*} [AddCommMonoid M] [Module S M] [AddCommMonoid N] [Module S N]

/-- **The lifting property of a projective module, for semilinear maps.** If `P` is a projective
`R`-module and `F : M →ₗ[S] N` is surjective, then every `σ`-semilinear map `g : P → N` factors
as `F ∘ h` for a `σ`-semilinear map `h : P → M`. -/
theorem projective_lifting_property_semilinear [Module.Projective R P] (F : M →ₗ[S] N)
    (hF : Function.Surjective F) (g : P →ₛₗ[σ] N) : ∃ h : P →ₛₗ[σ] M, F.comp h = g := by
  -- Restrict the scalars of `M` and `N` along `σ`, so that `F` and `g` become `R`-linear.
  let : Module R M := Module.compHom M σ
  let : Module R N := Module.compHom N σ
  obtain ⟨h, hh⟩ := projective_lifting_property
    ({ F.toAddMonoidHom with map_smul' := fun r m ↦ F.map_smul (σ r) m } : M →ₗ[R] N)
    ({ g.toAddMonoidHom with map_smul' := g.map_smulₛₗ } : P →ₗ[R] N) hF
  exact ⟨{ h.toAddMonoidHom with map_smul' := h.map_smul },
    LinearMap.ext fun p ↦ LinearMap.congr_fun hh p⟩

end Module

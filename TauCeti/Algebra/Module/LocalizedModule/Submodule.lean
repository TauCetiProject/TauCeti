/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Basic

/-!
# Fractions in submodules over a localization

Let `A` be the localization of `R` at `S`, and `f : M → M'` a localization map at `S` into an
`A`-module. Every element of `S` acts invertibly on an `A`-submodule `L` of `M'`, so a fraction
`f x / s` lies in `L` exactly when its numerator `f x` does.

## Main results

* `IsLocalizedModule.mk'_mem_iff`: a fraction `f x / s` lies in a submodule over the localization
  exactly when `f x` does.
-/

public section

/-- Let `A` be the localization of `R` at `S`, and `f : M → M'` a localization map at `S` into an
`A`-module. Then `f x / s` lies in an `A`-submodule `L` of `M'` exactly when `f x` does. -/
theorem IsLocalizedModule.mk'_mem_iff {R : Type*} [CommSemiring R] {S : Submonoid R}
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    {M M' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] [Module A M']
    [IsScalarTower R A M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] {L : Submodule A M'}
    {x : M} {s : S} : IsLocalizedModule.mk' f x s ∈ L ↔ f x ∈ L := by
  rw [← IsLocalization.smul_mem_iff (s := s), IsLocalizedModule.mk'_cancel']

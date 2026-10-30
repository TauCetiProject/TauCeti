/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.SerreClass

/-!
# Examples for the Serre class of almost zero modules

These examples test the Serre class of almost zero modules and its isomorphisms modulo the class:

* an extension of almost zero modules is almost zero;
* the inclusion `m → V` is an isomorphism modulo almost zero modules for every setup; for the zero
  setup of `ℤ` it is the inclusion `0 → ℤ`, which is not an isomorphism, so isomorphisms modulo
  almost zero modules are more than isomorphisms;
* multiplication by `2` on `ℤ` is not an isomorphism modulo almost zero modules for the classical
  setup;
* linear maps out of or into `V ⧸ m` form almost zero modules, while `ℤ →ₗ[ℤ] ℤ` is not almost
  zero for the classical setup.
-/

open CategoryTheory TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V]

/-! ### The Serre class -/

-- An extension of almost zero modules is almost zero.
example (S : BasicSetup V) {X : ShortComplex (ModuleCat V)} (hX : X.ShortExact)
    (h₁ : S.almostZero X.X₁) (h₃ : S.almostZero X.X₃) : S.almostZero X.X₂ :=
  S.almostZero.prop_X₂_of_shortExact hX h₁ h₃

/-! ### Isomorphisms modulo almost zero modules -/

-- The inclusion `m → V` is an isomorphism modulo almost zero modules.
example (S : BasicSetup V) : S.almostZero.isoModSerre (ModuleCat.ofHom S.ideal.subtype) :=
  (S.isAlmostIso_iff_isoModSerre _).mp S.isAlmostIso_subtype

-- For the zero setup of `ℤ`, the inclusion `0 → ℤ` is an isomorphism modulo almost zero
-- modules, but not an isomorphism.
example : (zero ℤ).almostZero.isoModSerre (ModuleCat.ofHom (zero ℤ).ideal.subtype) := by
  simp

example : ¬ IsIso (ModuleCat.ofHom (zero ℤ).ideal.subtype) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := h 1
  have hx0 : (x : ℤ) = 0 := by simpa only [zero_ideal, Ideal.mem_bot] using x.2
  simp [hx0] at hx

-- Multiplication by `2` on `ℤ` is not an isomorphism modulo almost zero modules for the classical
-- setup.
example : ¬ (classical ℤ).almostZero.isoModSerre
    (ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ))) := by
  rw [← isAlmostIso_iff_isoModSerre, ModuleCat.hom_ofHom, isAlmostIso_classical_iff]
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := h (1 : ℤ)
  -- `hx` is `LinearMap.mulLeft ℤ 2 x = 1` on the carrier of `ModuleCat.of ℤ ℤ`, which is `ℤ`.
  have hx' : (2 : ℤ) * x = 1 := hx
  omega

/-! ### Linear maps and almost zero modules -/

-- Linear maps out of and into `V ⧸ m` form almost zero modules.
example (S : BasicSetup V) (N : Type*) [AddCommGroup N] [Module V N] :
    S.IsAlmostZero ((V ⧸ S.ideal) →ₗ[V] N) :=
  S.isAlmostZero_quotient.linearMap_of_domain N

example (S : BasicSetup V) (N : Type*) [AddCommGroup N] [Module V N] :
    S.IsAlmostZero (N →ₗ[V] (V ⧸ S.ideal)) :=
  S.isAlmostZero_quotient.linearMap_of_codomain N

-- `ℤ →ₗ[ℤ] ℤ` is not almost zero for the classical setup: it contains the identity.
example : ¬ (classical ℤ).IsAlmostZero (ℤ →ₗ[ℤ] ℤ) := by
  rw [isAlmostZero_classical_iff]
  intro h
  have := congrArg (fun f : ℤ →ₗ[ℤ] ℤ ↦ f 1) (Subsingleton.elim LinearMap.id 0)
  simp at this

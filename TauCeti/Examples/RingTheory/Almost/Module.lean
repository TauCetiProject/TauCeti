/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Module

/-!
# Examples of almost modules

These examples test the category of almost modules and the almostification functor `M ↦ M^a`:

* for every setup, the almostification of `V ⧸ m` is zero, the inclusion `m → V` becomes an
  isomorphism, and the quotient map `V → V ⧸ m` almostifies to zero;
* for the zero setup every almost module is zero; for the zero setup of `ℤ` the inclusion `0 → ℤ`
  becomes an isomorphism, although it is not one;
* for the classical setup almostification is an equivalence, the almostification of `ℤ` is nonzero,
  and multiplication by `2` on `ℤ` stays a monomorphism but not an epimorphism.
-/

open CategoryTheory Limits TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type} [CommRing V]

/-! ### Every setup -/

-- The almostification of `V ⧸ m` is zero.
example (S : BasicSetup V) : IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal))) :=
  (isZero_toAlmost_obj_iff S _).mpr S.isAlmostZero_quotient

-- The inclusion `m → V` becomes an isomorphism of almost modules.
example (S : BasicSetup V) : IsIso ((toAlmost S).map (ModuleCat.ofHom S.ideal.subtype)) :=
  (isIso_toAlmost_map_iff S _).mpr S.isAlmostIso_subtype

-- The quotient map `V → V ⧸ m` almostifies to zero: its image is almost zero.
example (S : BasicSetup V) :
    (toAlmost S).map (ModuleCat.ofHom S.ideal.mkQ) = 0 := by
  rw [toAlmost_map_eq_zero_iff]
  exact S.isAlmostZero_quotient.of_injective (Submodule.injective_subtype _)

/-! ### The zero setup -/

-- Every almost module over the zero setup is zero.
example (M : Module (zero V)) : IsZero M :=
  Module.isZero_of_zero M

-- For the zero setup of `ℤ`, the inclusion `0 → ℤ` becomes an isomorphism, although it is not one.
example : IsIso ((toAlmost (zero ℤ)).map (ModuleCat.ofHom (zero ℤ).ideal.subtype)) :=
  (isIso_toAlmost_map_iff _ _).mpr (isAlmostIso_zero _)

example : ¬ IsIso (ModuleCat.ofHom (zero ℤ).ideal.subtype) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  rintro ⟨-, h⟩
  obtain ⟨x, hx⟩ := h 1
  have hx0 : (x : ℤ) = 0 := by simpa only [zero_ideal, Ideal.mem_bot] using x.2
  simp [hx0] at hx

/-! ### The classical setup -/

-- For the classical setup, almostification is an equivalence of categories.
example : (toAlmost (classical V)).IsEquivalence :=
  inferInstance

example : (Module.classicalEquiv (V := V)).functor = toAlmost (classical V) :=
  Module.classicalEquiv_functor

-- The almostification of `ℤ` for the classical setup is nonzero.
example : ¬ IsZero ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  rw [isZero_toAlmost_obj_iff, isAlmostZero_classical_iff]
  intro h
  exact one_ne_zero (Subsingleton.elim (1 : ℤ) 0)

-- Multiplication by `2` on `ℤ` almostifies to a monomorphism but not to an epimorphism for the
-- classical setup.
example : Mono ((toAlmost (classical ℤ)).map (ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ)))) := by
  rw [mono_toAlmost_map_iff, isAlmostZero_classical_iff, ModuleCat.hom_ofHom,
    LinearMap.ker_eq_bot.mpr (mul_right_injective₀ two_ne_zero)]
  infer_instance

example :
    ¬ Epi ((toAlmost (classical ℤ)).map (ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ)))) := by
  rw [epi_toAlmost_map_iff, isAlmostZero_classical_iff]
  intro h
  have h1 := Subsingleton.elim (Submodule.Quotient.mk (1 : ℤ) :
    ℤ ⧸ LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))) 0
  rw [Submodule.Quotient.mk_eq_zero] at h1
  obtain ⟨x, hx⟩ := h1
  -- `hx` is `LinearMap.mulLeft ℤ 2 x = 1` on the carrier of `ModuleCat.of ℤ ℤ`, which is `ℤ`.
  have hx' : (2 : ℤ) * x = 1 := hx
  omega

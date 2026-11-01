/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Module
import TauCeti.RingTheory.Almost.ValuationRing
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal

/-!
# Examples for the category of almost modules

These examples test `TauCeti.Almost.Module` and the almostification functor `toAlmost`:

* for the setup of `𝓞_ℂ_[p]`, the almostification of the residue field is zero, while that of
  `𝓞_ℂ_[p] ⧸ (p)` is not;
* for every setup, the almostification of `V ⧸ m` is zero, the inclusion `m → V` becomes an
  isomorphism, and Hom-types of almost modules are `V`-modules;
* for the classical setup, almostification is an equivalence, and the almostification of `ℤ` is
  nonzero;
* for the zero setup, every almost module is zero, although `ℤ` is not;
* multiplication by `2` on `ℤ` becomes a monomorphism but not an epimorphism for the classical
  setup;
* every exact functor out of `ModuleCat ℤ` factors exactly through almostification for the
  classical setup, while the identity functor does not for the zero setup.
-/

open CategoryTheory Limits IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V]

/-! ### Every setup -/

-- The almostification of `V ⧸ m` is zero.
example (S : BasicSetup V) : IsZero ((toAlmost S).obj (ModuleCat.of V (V ⧸ S.ideal))) :=
  (isZero_toAlmost_obj_iff _).mpr S.isAlmostZero_quotient

-- The inclusion `m → V` becomes an isomorphism of almost modules.
example (S : BasicSetup V) : IsIso ((toAlmost S).map (ModuleCat.ofHom S.ideal.subtype)) :=
  (isIso_toAlmost_map_iff _).mpr S.isAlmostIso_subtype

-- Hom-types of almost modules are `V`-modules, and almostification is `V`-linear.
noncomputable example (S : BasicSetup V) (X Y : Module S) : _root_.Module V (X ⟶ Y) :=
  inferInstance

example (S : BasicSetup V) : (toAlmost S).Linear V := inferInstance

/-! ### The integers of `ℂ_p` -/

section PadicComplex

variable (p : ℕ) [Fact p.Prime]

-- The almostification of the residue field of `𝓞_ℂ_[p]` is zero, while that of `𝓞_ℂ_[p] ⧸ (p)`
-- is not.
example : IsZero ((toAlmost (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p))).obj
    (ModuleCat.of 𝓞_ℂ_[p] (ResidueField 𝓞_ℂ_[p]))) := by
  simp

example : ¬ IsZero ((toAlmost (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p))).obj
    (ModuleCat.of 𝓞_ℂ_[p] (𝓞_ℂ_[p] ⧸ Ideal.span {(p : 𝓞_ℂ_[p])}))) := by
  refine (isZero_toAlmost_obj_iff _).not.mpr
    ((ofValuationRing_isAlmostZero_quotient_span_singleton_iff _).not.mpr
      ((mem_maximalIdeal _).mp (TauCeti.PadicComplexInt.natCast_mem_maximalIdeal p)))

end PadicComplex

/-! ### The classical and zero setups -/

-- For the classical setup, almostification is an equivalence of categories.
example : (toAlmost (classical V)).IsEquivalence := inferInstance

-- The almostification of `ℤ` is nonzero for the classical setup.
example : ¬ IsZero ((toAlmost (classical ℤ)).obj (ModuleCat.of ℤ ℤ)) := by
  refine (isZero_toAlmost_obj_iff _).not.mpr (isAlmostZero_classical_iff.not.mpr ?_)
  exact fun h ↦ zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

-- For the zero setup, every almost module is zero: it is the almostification of a module, and
-- every module is almost zero.
example (X : Module (zero V)) : IsZero X :=
  ((isZero_toAlmost_obj_iff _).mpr isAlmostZero_zero).of_iso
    ((toAlmost (zero V)).objObjPreimageIso X).symm

-- The ring `ℤ` itself is not a zero module, so the zero setup changes it.
example : ¬ IsZero (ModuleCat.of ℤ ℤ) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  exact fun h ↦ zero_ne_one (Subsingleton.elim (0 : ℤ) 1)

/-! ### Monomorphisms and epimorphisms -/

-- Multiplication by `2` on `ℤ` almostifies to a monomorphism but not to an epimorphism for the
-- classical setup: its kernel is zero, while its cokernel `ℤ ⧸ 2ℤ` is nonzero.
example : Mono ((toAlmost (classical ℤ)).map (ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ)))) := by
  rw [mono_toAlmost_map_iff, isAlmostZero_classical_iff, ModuleCat.hom_ofHom,
    LinearMap.ker_eq_bot.mpr (mul_right_injective₀ two_ne_zero)]
  infer_instance

example : ¬ Epi ((toAlmost (classical ℤ)).map
    (ModuleCat.ofHom (LinearMap.mulLeft ℤ (2 : ℤ)))) := by
  rw [epi_toAlmost_map_iff, isAlmostZero_classical_iff, ModuleCat.hom_ofHom]
  intro h
  have h1 : Submodule.Quotient.mk (p := LinearMap.range (LinearMap.mulLeft ℤ (2 : ℤ))) (1 : ℤ) =
      Submodule.Quotient.mk 0 := Subsingleton.elim _ _
  rw [Submodule.Quotient.eq, sub_zero] at h1
  obtain ⟨x, hx⟩ := h1
  rw [LinearMap.mulLeft_apply] at hx
  omega

/-! ### Exact functors -/

-- A functor out of almost modules is left exact iff its composite with almostification is.
example {E : Type*} [Category E] [Abelian E] (S : BasicSetup V) (G : Module S ⥤ E) :
    PreservesFiniteLimits (toAlmost S ⋙ G) ↔ PreservesFiniteLimits G :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits_comp_iff _ S.almostZero G

-- For the classical setup, every exact functor out of `ModuleCat ℤ` factors exactly through
-- almostification: the only almost zero modules are zero.
example (F : ModuleCat.{0} ℤ ⥤ₑ ModuleCat.{0} ℤ) :
    (ObjectProperty.SerreClassLocalization.whiskeringLeft (toAlmost (classical ℤ))
      (classical ℤ).almostZero (ModuleCat.{0} ℤ)).essImage F := by
  have := F.property.1
  refine (mem_essImage_whiskeringLeft_toAlmost_iff _ _ F).mpr fun M hM ↦ ?_
  have : Subsingleton M := isAlmostZero_classical_iff.mp hM
  exact F.obj.map_isZero (ModuleCat.isZero_of_subsingleton M)

-- For the zero setup, the identity functor of `ModuleCat ℤ` does not factor exactly through
-- almostification: it does not kill the almost zero module `ℤ`.
example : ¬ (ObjectProperty.SerreClassLocalization.whiskeringLeft (toAlmost (zero ℤ))
    (zero ℤ).almostZero (ModuleCat.{0} ℤ)).essImage (ExactFunctor.of (𝟭 (ModuleCat.{0} ℤ))) := by
  rw [mem_essImage_whiskeringLeft_toAlmost_iff]
  intro h
  exact zero_ne_one (@Subsingleton.elim ℤ
    (ModuleCat.isZero_iff_subsingleton.mp (h (ModuleCat.of ℤ ℤ) isAlmostZero_zero)) 0 1)

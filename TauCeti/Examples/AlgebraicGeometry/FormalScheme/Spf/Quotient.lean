/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.Quotient
public import TauCeti.RingTheory.Huber.Padic.Basic

/-!
# Quotient thickenings of formal spectra: examples

The nonreduced discrete ring `ℤ/4` has ideals of definition `(2)` and `(2)² = 0`.
The coefficient `2` vanishes in the first quotient, but survives as a nonzero square-zero
coefficient in the second. These examples also check quotient inclusions over a field,
the zero ring, and the nondiscrete ring of `p`-adic integers.
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open TauCeti TauCeti.FormalScheme TauCeti.FormalScheme.Spf

namespace TauCeti.Examples.FormalScheme.Spf

section SquareZero

/-- The discrete topology used for the square-zero coefficient computation. -/
local instance zmodFourTopology : TopologicalSpace (ZMod 4) := ⊥
local instance : DiscreteTopology (ZMod 4) := ⟨rfl⟩

/-- The square-zero ideal `(2)` defines the discrete topology on `ℤ/4`. -/
theorem isAdic_span_two : IsAdic (Ideal.span {(2 : ZMod 4)}) := by
  rw [isAdic_iff]
  refine ⟨fun _ ↦ isOpen_discrete _, fun U hU ↦ ⟨2, ?_⟩⟩
  have hsq : (Ideal.span {(2 : ZMod 4)}) ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot]
    decide
  rw [hsq]
  simpa using mem_of_mem_nhds hU

/-- At level zero, the image of the global coefficient `2` vanishes. -/
theorem quotientSheaf_square_zero :
    have := (IsAdicRing.ideal_spec (ZMod 4)).2.2
    (quotientSheafGlobalSectionsIso isAdic_span_two).hom
      ((fromSpecQuotient isAdic_span_two).c.app (op ⊤)
        ((globalSectionsIso (IsAdicRing.ideal_spec (ZMod 4)).2.1).inv 2)) = 0 := by
  intro
  have h := ConcreteCategory.congr_hom (fromSpecQuotient_globalSections isAdic_span_two) 2
  exact h.trans (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)))

/-- At level one, the same coefficient survives in the square-zero thickening. -/
theorem quotientSheaf_square_nonzero :
    have := (IsAdicRing.ideal_spec (ZMod 4)).2.2
    (quotientSheafGlobalSectionsIso (is_bot_adic_iff.mpr inferInstance :
      IsAdic (⊥ : Ideal (ZMod 4)))).hom
      ((fromSpecQuotient (is_bot_adic_iff.mpr inferInstance : IsAdic (⊥ : Ideal (ZMod 4)))).c.app
        (op ⊤) ((globalSectionsIso (IsAdicRing.ideal_spec (ZMod 4)).2.1).inv 2)) ≠ 0 := by
  intro
  have h := ConcreteCategory.congr_hom (fromSpecQuotient_globalSections
    (is_bot_adic_iff.mpr inferInstance : IsAdic (⊥ : Ideal (ZMod 4)))) 2
  intro hzero
  have hmem : (2 : ZMod 4) ∈ (⊥ : Ideal (ZMod 4)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp (h.symm.trans hzero)
  exact (by decide : (2 : ZMod 4) ≠ 0) hmem

-- The square-zero thickening is a homeomorphism, but not an isomorphism of locally ringed spaces.
example : ¬ IsIso (fromSpecQuotient isAdic_span_two) := by
  rw [fromSpecQuotient_isIso_iff, Ideal.span_singleton_eq_bot]
  decide

-- The transition from level one to level zero agrees with the actual quotient map of schemes.
example :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom
      (Ideal.Quotient.factor (bot_le : (⊥ : Ideal (ZMod 4)) ≤ Ideal.span {2}))) ≫
        fromSpecQuotient (is_bot_adic_iff.mpr inferInstance) = fromSpecQuotient isAdic_span_two :=
  fromSpecQuotient_naturality _ _ bot_le

end SquareZero

section Discrete

variable (k : Type*) [Field k] [TopologicalSpace k] [DiscreteTopology k]

-- Quotient inclusion at the zero ideal also applies to a field.
example : Mono (fromSpecQuotient (is_bot_adic_iff.mpr inferInstance : IsAdic (⊥ : Ideal k))) :=
  inferInstance

end Discrete

section Zero

/-- The discrete topology on the zero ring. -/
local instance zmodOneTopology : TopologicalSpace (ZMod 1) := ⊥
local instance : DiscreteTopology (ZMod 1) := ⟨rfl⟩

-- The zero ring gives an empty source and target, with no nontriviality assumption.
example : IsHomeomorph (fromSpecQuotient (is_bot_adic_iff.mpr inferInstance :
    IsAdic (⊥ : Ideal (ZMod 1)))).base :=
  fromSpecQuotient_isHomeomorph _

end Zero

section Padic

variable (p : ℕ) [Fact p.Prime]

local instance : IsAdicRing ℤ_[p] :=
  ⟨IsLocalRing.maximalIdeal ℤ_[p],
    by rw [PadicInt.maximalIdeal_eq_span_p]; exact Submodule.fg_span_singleton _,
    Huber.PadicInt.isAdic_maximalIdeal, inferInstance⟩

-- The maps of all infinitesimal neighbourhoods of `Spf ℤ_p` are surjective on stalks.
example (n : ℕ) (q : PrimeSpectrum (ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p] ^ (n + 1))) :
    Function.Surjective ((fromSpecQuotient
      (is_ideal_adic_pow Huber.PadicInt.isAdic_maximalIdeal n.succ_pos)).stalkMap q) :=
  fromSpecQuotient_stalk_surjective _ q

end Padic

end TauCeti.Examples.FormalScheme.Spf

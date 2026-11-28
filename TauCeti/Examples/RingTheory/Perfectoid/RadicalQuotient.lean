/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.Integral.RadicalQuotient

/-!
# Checks for quotients of perfect rings of characteristic `p`

* The unit ideal is radical, and its quotient is the zero ring, which is integral perfectoid.
* The zero ideal of a perfect ring is radical, and its quotient recovers the ring.
* A ring homomorphism from `R ⧸ I` to an integral perfectoid ring kills `√I`, and the target need
  not be assumed to have characteristic `p`.
* A ring homomorphism from `R ⧸ (f)` to an integral perfectoid ring kills every `p ^ n`-th root
  of `f`; the quotient by the Frobenius-root ideal of `1` is the zero ring.
-/

open TauCeti TauCeti.Perfectoid

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] [PerfectRing R p]

/-! ### The unit and zero ideals -/

-- The quotient by the unit ideal is the zero ring, which is integral perfectoid although it does
-- not have characteristic `p`.
example : IsIntegralPerfectoid p (R ⧸ (⊤ : Ideal R)) :=
  isIntegralPerfectoid_quotient_iff_isRadical.mpr fun _ _ ↦ Submodule.mem_top

-- The zero ideal of a perfect ring is radical, since a perfect ring is reduced.
example : IsIntegralPerfectoid p (R ⧸ (⊥ : Ideal R)) :=
  have := isReduced_of_perfectRing R p
  isIntegralPerfectoid_quotient_iff_isRadical.mpr Ideal.isRadical_bot

/-! ### The universal property -/

-- A ring homomorphism from `R ⧸ I` to an integral perfectoid ring kills every element of `R` with
-- a power in `I`.
example (I : Ideal R) (T : Type*) [CommRing T] [IsIntegralPerfectoid p T] (f : R ⧸ I →+* T)
    {x : R} {n : ℕ} (hx : x ^ n ∈ I) : f (Ideal.Quotient.mk I x) = 0 := by
  obtain ⟨g, rfl⟩ := (bijective_comp_factor_radical (p := p)
    (by rw [CharP.cast_eq_zero]; exact zero_mem I) T).2 f
  rw [RingHom.comp_apply, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr (⟨n, hx⟩ : x ∈ I.radical), map_zero]

/-! ### Frobenius-root ideals -/

-- The Frobenius-root ideal of `1` is the unit ideal, so its quotient is the zero ring.
example : Subsingleton (R ⧸ frobeniusRootIdeal R p 1) :=
  Ideal.Quotient.subsingleton_iff.mpr frobeniusRootIdeal_one

-- The quotient by the Frobenius-root ideal of any `f` is integral perfectoid, `f = 1` included.
example : IsIntegralPerfectoid p (R ⧸ frobeniusRootIdeal R p 1) := inferInstance

-- Killing `f` in an integral perfectoid ring kills all its `p ^ n`-th roots.
example (f : R) (T : Type*) [CommRing T] [IsIntegralPerfectoid p T] (g : R ⧸ Ideal.span {f} →+* T)
    (n : ℕ) : g (Ideal.Quotient.mk _ ((iterateFrobeniusEquiv R p n).symm f)) = 0 := by
  obtain ⟨h, rfl⟩ := (bijective_comp_factor_frobeniusRootIdeal f T).2 g
  rw [RingHom.comp_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr
    (iterateFrobeniusEquiv_symm_mem_frobeniusRootIdeal f n), map_zero]

end TauCeti.Examples

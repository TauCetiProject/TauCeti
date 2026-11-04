/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.CohenMacaulay.Ring
import TauCeti.RingTheory.CohenMacaulay.TrivSqZeroExt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Data.ZMod.Basic

/-!
# Tests for Cohen–Macaulay rings

Fields, integers and finite-variable polynomial rings are Cohen–Macaulay. The zero ring is
allowed, as are nonreduced Artinian rings such as `ℤ/4`. In contrast, adjoining square-zero
residue-field torsion to a positive-dimensional local ring destroys Cohen–Macaulayness.
-/

open TauCeti.Ring

universe u v

example (k : Type u) [Field k] : IsCohenMacaulay k := inferInstance

example : IsCohenMacaulay ℤ := inferInstance

example (k : Type u) [Field k] (n : ℕ) : IsCohenMacaulay (MvPolynomial (Fin n) k) :=
  inferInstance

example : IsCohenMacaulay (ZMod 1) := IsCohenMacaulay.of_krullDimLE_zero

example : IsCohenMacaulay (ZMod 4) := IsCohenMacaulay.of_krullDimLE_zero

-- The maximal-ideal criterion constructs the global predicate; no local-ring hypothesis on R.
example (R : Type u) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.IsCohenMacaulay (Localization.AtPrime m) (Localization.AtPrime m)) :
    IsCohenMacaulay R := isCohenMacaulay_iff_forall_isMaximal.mpr h

-- The localization result works with an arbitrary carrier, not just `Localization M`.
example (R : Type u) [CommRing R] [IsCohenMacaulay R] (M : Submonoid R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization M S] : IsCohenMacaulay S :=
  IsCohenMacaulay.of_isLocalization M S

-- For example, the positive-dimensional base may be a DVR. The extension has depth zero,
-- but the same positive dimension as the base, so it is not Cohen–Macaulay.
example (R : Type u) [CommRing R] [IsLocalRing R] (hR : ringKrullDim R ≠ 0) :
    ¬ IsCohenMacaulay (TrivSqZeroExt R (R ⧸ IsLocalRing.maximalIdeal R)) := by
  intro h
  have := h
  exact TrivSqZeroExt.not_isCohenMacaulay
    (IsLocalRing.depth_eq_zero_iff_nontrivial_linearMap.mpr inferInstance) hR
    (isCohenMacaulay_iff_of_isLocalRing.mp h)

-- Noetherianity is part of the predicate, rather than a standing assumption on the caller.
example (R : Type u) [CommRing R] (hR : ¬ IsNoetherianRing R) : ¬ IsCohenMacaulay R :=
  fun h ↦ hR h.toIsNoetherian

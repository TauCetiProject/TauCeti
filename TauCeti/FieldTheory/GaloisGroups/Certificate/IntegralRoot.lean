/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Certificate.Evidence

import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral roots of the quintic resolvent sextic

The quintic resolvent sextic is monic over `ℤ`, so each of its rational roots is integral. This
identifies the rational root condition used in the Galois-theoretic resolvent criterion with the
integral root evidence carried by `TauCeti.HasSexticRoot`.

## Main results

* `TauCeti.exists_hasSexticRoot_iff`: a separable integral resolvent sextic has a rational root
  exactly when it has the integral root required by resolvent evidence.
-/

public section

open Polynomial

namespace TauCeti

/-- **Rational roots of a separable resolvent sextic are exactly its certificate roots.** Since
the resolvent sextic is monic over `ℤ`, the integral root theorem shows that every rational root
is an integer. Thus a separable rational resolvent has a root precisely when the integral evidence
predicate `HasSexticRoot` has a witness. -/
theorem exists_hasSexticRoot_iff (f : ℤ[X]) :
    (∃ a : ℤ, HasSexticRoot f a) ↔
      (∃ a : ℚ, ((resolventSextic f).map (Int.castRingHom ℚ)).IsRoot a) ∧
        ((resolventSextic f).map (Int.castRingHom ℚ)).Separable := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨a, ha.isRoot.map⟩, ha.separable_map_rat⟩
  · rintro ⟨⟨a, ha⟩, hsep⟩
    have haeval : aeval a (resolventSextic f) = 0 := by
      rwa [aeval_def, algebraMap_int_eq, ← eval_map]
    obtain ⟨a, rfl⟩ := isInteger_of_is_root_of_monic (monic_resolventSextic f) haeval
    refine ⟨a, HasSexticRoot.mk (ha.of_map (RingHom.injective_int _)) ?_⟩
    exact (monic_resolventSextic f).discr_ne_zero_iff_separable_map ℚ |>.mpr hsep

end TauCeti

end

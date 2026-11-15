/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.UniversallyCatenary
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import TauCeti.RingTheory.CohenMacaulay.Catenary
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay

/-!
# Regular rings are universally catenary

Regular rings are Cohen–Macaulay, so they are catenary
(`TauCeti.Excellence.isCatenary_of_forall_isCohenMacaulay`). Since a polynomial ring in finitely
many variables over a regular ring is again regular, regular rings are moreover universally
catenary; in particular fields and `ℤ` are universally catenary, and every algebra of finite type
over a field is catenary.

## Main results

* `IsRegularRing.isCatenary` and `IsRegularRing.isUniversallyCatenary`: regular rings are catenary,
  and even universally catenary.

## References

* [Stacks Project, Lemma 10.105.9](https://stacks.math.columbia.edu/tag/00NM)
-/

public section

universe u

open TauCeti.Excellence

namespace IsRegularRing

variable {R : Type u} [CommRing R] [IsRegularRing R]

/-- A regular ring is catenary: its local rings are regular, hence Cohen–Macaulay. -/
instance isCatenary : IsCatenary R :=
  isCatenary_of_forall_isCohenMacaulay fun _ _ ↦ TauCeti.IsRegularLocalRing.isCohenMacaulay

/-- **Regular rings are universally catenary.** A polynomial ring in finitely many variables over a
regular ring is regular, hence catenary. This is the case of Stacks, Lemma 10.105.9 (00NM) for
regular rings, which are Cohen–Macaulay. -/
instance isUniversallyCatenary : IsUniversallyCatenary R :=
  isUniversallyCatenary_iff_mvPolynomial.2 ⟨inferInstance, fun _ ↦ inferInstance⟩

end IsRegularRing

/-- Every field is universally catenary. -/
example (k : Type u) [Field k] : IsUniversallyCatenary k := inferInstance

/-- The integers are universally catenary. -/
example : IsUniversallyCatenary ℤ := inferInstance

/-- A polynomial ring in finitely many variables over a field is catenary. -/
example (k : Type u) [Field k] (n : ℕ) : IsCatenary (MvPolynomial (Fin n) k) := inferInstance

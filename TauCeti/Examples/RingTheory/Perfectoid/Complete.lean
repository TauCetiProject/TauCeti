/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Perfectoid.Complete
import TauCeti.RingTheory.Perfectoid.IsAlgClosed
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for `p`-adic completeness of perfectoid power-bounded rings

The completeness instance applies to the completed algebraic closure of `ℚₚ` and to products
of perfectoid rings. It also applies in equal characteristic, where the ideal `(p)` is zero.
Neither invertibility nor regularity of `p` in the ambient ring is needed.
-/

open TauCeti.Huber TauCeti.Perfectoid

namespace TauCeti.Examples

variable (p : ℕ) [Fact p.Prime]

example : IsAdicComplete (Ideal.span {(p : powerBoundedSubring ℂ_[p])})
    (powerBoundedSubring ℂ_[p]) := by
  have := isPerfectoidTateRing_of_isAlgClosed (PadicComplex.norm_p_lt_one p)
  infer_instance

section Product

variable (R S : Type*) [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]
  [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S]
  [IsTateRing S] [CompleteSpace S] [T2Space S]
  [IsPerfectoidTateRing p R] [IsPerfectoidTateRing p S]

-- In particular this covers products whose factors have different characteristics.
example : IsAdicComplete (Ideal.span {(p : powerBoundedSubring (R × S))})
    (powerBoundedSubring (R × S)) := inferInstance

-- The equal-characteristic specialization agrees with completeness for the zero ideal.
example [CharP R p] : Ideal.span {(p : powerBoundedSubring R)} = ⊥ := by
  have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
  simp only [hp, Ideal.span_singleton_eq_bot]

end Product

end TauCeti.Examples

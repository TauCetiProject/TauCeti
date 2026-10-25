/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# Converse Möbius inversion

Mathlib's `IncidenceAlgebra.moebius_inversion_bot` recovers `f` from its lower sums
`g x = ∑_{y ≤ x} f y` as `f x = ∑_{y ≤ x} μ(y, x) g y`. This file proves the converse direction:
summing the Möbius transform `x ↦ ∑_{z ≤ x} μ(z, x) g z` over the lower set of `x` gives back
`g x`.

## Main results

* `IncidenceAlgebra.sum_Iic_sum_Iic_mu_mul` — `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`.
-/

public section

open Finset

namespace IncidenceAlgebra

variable {𝕜 α : Type*} [NonAssocRing 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [LocallyFiniteOrderBot α] [DecidableEq α]

/-- *Converse Möbius inversion*: the lower sums of the Möbius transform
`y ↦ ∑_{z ≤ y} μ(z, y) g z` of `g` recover `g`, `∑_{y ≤ x} ∑_{z ≤ y} μ(z, y) g z = g x`. -/
theorem sum_Iic_sum_Iic_mu_mul (g : α → 𝕜) (x : α) :
    ∑ y ∈ Iic x, ∑ z ∈ Iic y, mu 𝕜 z y * g z = g x := by
  rw [sum_comm' (t' := Iic x) (s' := fun z => Icc z x) fun y z => by
    simp only [mem_Iic, mem_Icc]
    exact ⟨fun h => ⟨⟨h.2, h.1⟩, h.2.trans h.1⟩, fun h => ⟨h.1.2, h.1.1⟩⟩]
  simp [← sum_mul, sum_Icc_mu_right]

end IncidenceAlgebra

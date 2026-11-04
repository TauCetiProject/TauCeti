/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Data.Set.Finite.Range

/-!
# Orbit-invariant functions on finite unions of torsors

Let `P i` be torsors under a group `H`, indexed by `i : ι`. A function `d` on the union
`Σ i, P i` that is constant on each orbit has at most one value per orbit, so it has finitely
many values when `ι` is finite. The main source of such functions is the residue of an
equivariant degree: if translating by `h` shifts `d` by `δ h` for a homomorphism `δ : H →+ D`,
then `d` modulo the range of `δ` is constant on orbits.

## Main results

* `TauCeti.AddTorsor.finite_range_sigma_of_forall_vadd_eq`: an orbit-invariant function on a
  finite union of torsors has finite range.
-/

public section

namespace TauCeti.AddTorsor

open Set

variable {H ι D : Type*} [AddGroup H] {P : ι → Type*} [∀ i, AddTorsor H (P i)]

/-- A function that is constant on each orbit of a finite union of torsors has finitely many
values. -/
theorem finite_range_sigma_of_forall_vadd_eq [Finite ι] {d : (Σ i, P i) → D}
    (hd : ∀ i (h : H) (p : P i), d ⟨i, h +ᵥ p⟩ = d ⟨i, p⟩) : (range d).Finite := by
  let r := fun i => Classical.arbitrary (P i)
  refine (finite_range fun i => d ⟨i, r i⟩).subset ?_
  rintro _ ⟨⟨i, p⟩, rfl⟩
  exact ⟨i, by rw [← vsub_vadd p (r i), hd]⟩

end TauCeti.AddTorsor

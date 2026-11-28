/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.AsAlgebraHom

/-!
# Monoid-algebra actions on submodules over a smaller ring

A linear combination of translates with coefficients in a subsemiring preserves integrality
provided that each translate in its support is integral. This works even when the integral
vectors are not a submodule over the full coefficient ring.
-/

public section

namespace Representation

/-- A monoid-algebra element with coefficients in `S` carries `x` into `L` if every translate
indexed by its support belongs to `L`. No stability outside this support is required. -/
theorem asAlgebraHom_apply_mem_of_coeff_mem
    {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) {S : Subsemiring k} (L : Submodule S V)
    {a : MonoidAlgebra k G} {x : V} (ha : ∀ g ∈ a.coeff.support, a.coeff g ∈ S)
    (hx : ∀ g ∈ a.coeff.support, ρ g x ∈ L) : ρ.asAlgebraHom a x ∈ L := by
  rw [ρ.asAlgebraHom_apply, Finsupp.sum]
  exact L.sum_mem fun g hg ↦ L.smul_mem (⟨a.coeff g, ha g hg⟩ : S) (hx g hg)

end Representation

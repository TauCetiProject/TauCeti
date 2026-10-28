/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Invariant Lie subalgebras under automorphisms

An automorphism `σ` of a Lie algebra `L` *normalises* a Lie subalgebra `H` when
`H.map σ = H`. This file records that the inverse normalises `H` too, and identifies the
inverse of Mathlib's `LieEquiv.ofSubalgebras` restriction with the corresponding restriction of
the inverse automorphism.

Nothing here involves weights, nilpotence, or any hypothesis on the base ring beyond
commutativity. What the automorphism does to the root spaces of `H` is in
`TauCeti/Algebra/Lie/Weights/Automorphism.lean`.

## Main results

* `LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg`: an automorphism acting by `-1` on a
  subalgebra normalises it.
* `LieSubalgebra.map_eq_self_of_mem`: an automorphism mapping a subalgebra into itself in both
  directions normalises it.
* `LieSubalgebra.map_eq_self_of_involutive`: an involutive automorphism mapping a subalgebra into
  itself normalises it.
* `LieSubalgebra.map_symm_eq_self_of_map_eq_self`: the inverse of a normalising automorphism
  normalises the subalgebra as well.
* `TauCeti.ofSubalgebras_symm`: restricting the inverse gives the inverse of Mathlib's restriction.
-/

public section

universe u v

section Restrict

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]
  {H : LieSubalgebra R L}

variable (e : LieEquiv R L L) (he : H.map e = H)

namespace LieSubalgebra

/-- An automorphism that maps a Lie subalgebra `H` into itself in both directions normalises `H`. -/
theorem map_eq_self_of_mem (h_mem : ∀ x ∈ H, e x ∈ H) (h_symm : ∀ x ∈ H, e.symm x ∈ H) :
    H.map e = H := by
  ext x
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact h_mem y hy,
    fun hx ↦ ⟨e.symm x, h_symm x hx, e.apply_symm_apply x⟩⟩

/-- An involutive automorphism that maps a Lie subalgebra `H` into itself normalises `H`. -/
theorem map_eq_self_of_involutive (h_inv : Function.Involutive e) (h_mem : ∀ x ∈ H, e x ∈ H) :
    H.map e = H :=
  map_eq_self_of_mem e h_mem fun x hx ↦ by
    rw [e.symm_apply_eq.mpr (h_inv x).symm]
    exact h_mem x hx

/-- An automorphism acting by `-1` on a subalgebra normalises it, since a subalgebra is closed
under negation. -/
theorem map_eq_self_of_forall_mem_apply_eq_neg (hneg : ∀ y ∈ H, e y = -y) : H.map e = H :=
  map_eq_self_of_mem e (fun y hy ↦ hneg y hy ▸ neg_mem hy) fun y hy ↦ by
    rw [e.symm_apply_eq.mpr (by rw [hneg (-y) (neg_mem hy), neg_neg])]
    exact neg_mem hy

include he in
/-- The inverse of a normalising automorphism normalises `H` as well. -/
theorem map_symm_eq_self_of_map_eq_self : H.map e.symm = H := by
  apply LieSubalgebra.toSubmodule_injective
  apply (Submodule.map_symm_eq_iff e.toLinearEquiv).2
  exact congrArg (fun A : LieSubalgebra R L => (A : Submodule R L)) he

end LieSubalgebra

namespace TauCeti

include he in
/-- The inverse of the restriction of a normalising automorphism is the restriction of the inverse
automorphism. -/
theorem ofSubalgebras_symm :
    (e.ofSubalgebras H H he).symm =
      e.symm.ofSubalgebras H H (LieSubalgebra.map_symm_eq_self_of_map_eq_self e he) :=
  LieEquiv.ext fun _ => rfl

end TauCeti

end Restrict

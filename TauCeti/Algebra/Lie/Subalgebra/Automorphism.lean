/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Subalgebra

/-!
# Lie subalgebras under equivalences and automorphisms

A Lie algebra equivalence `e : L₁ ≃ₗ⁅R⁆ L₂` maps a Lie subalgebra `H` of `L₁` onto a Lie
subalgebra `K` of `L₂` when `H.map e = K`. This file records that the inverse then maps `K` onto
`H`, and identifies the inverse of Mathlib's `LieEquiv.ofSubalgebras` restriction with the
corresponding restriction of the inverse equivalence.

An automorphism `σ` of a Lie algebra `L` *normalises* a Lie subalgebra `H` when `H.map σ = H`.
The file gives criteria for this: an involutive automorphism mapping `H` into itself, or one acting
by `-1` on `H`, normalises it.

Nothing here involves weights, nilpotence, or any hypothesis on the base ring beyond
commutativity. What a normalising automorphism does to the root spaces of `H` is in
`TauCeti/Algebra/Lie/Weights/Automorphism.lean`.

## Main results

* `LieSubalgebra.map_eq_of_mem`: an equivalence mapping `H` into `K`, whose inverse maps `K` into
  `H`, maps `H` onto `K`.
* `LieSubalgebra.map_symm_eq_iff`: the inverse of an equivalence maps `K` onto `H` exactly when
  the equivalence maps `H` onto `K`.
* `LieEquiv.ofSubalgebras_symm`: restricting the inverse gives the inverse of Mathlib's
  restriction.
* `LieSubalgebra.map_eq_self_of_involutive`: an involutive automorphism mapping a subalgebra into
  itself normalises it.
* `LieSubalgebra.map_eq_self_of_forall_mem_apply_eq_neg`: an automorphism acting by `-1` on a
  subalgebra normalises it.
-/

public section

variable {R : Type*} [CommRing R]

section Equiv

variable {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  (e : L₁ ≃ₗ⁅R⁆ L₂) {H : LieSubalgebra R L₁} {K : LieSubalgebra R L₂}

namespace LieSubalgebra

/-- A Lie algebra equivalence that maps `H` into `K`, and whose inverse maps `K` into `H`, maps
`H` onto `K`. -/
theorem map_eq_of_mem (h_mem : ∀ x ∈ H, e x ∈ K) (h_symm : ∀ y ∈ K, e.symm y ∈ H) :
    H.map e = K :=
  le_antisymm (map_le_iff_le_comap.2 h_mem) fun y hy ↦
    ⟨e.symm y, h_symm y hy, e.apply_symm_apply y⟩

/-- The inverse of a Lie algebra equivalence maps `K` onto `H` exactly when the equivalence maps
`H` onto `K`. -/
theorem map_symm_eq_iff : K.map e.symm = H ↔ H.map e = K := by
  constructor <;> rintro rfl <;> ext <;> simp

end LieSubalgebra

namespace LieEquiv

/-- The inverse of the restriction of a Lie algebra equivalence to subalgebras is the restriction
of the inverse equivalence. -/
theorem ofSubalgebras_symm (h : H.map e = K) :
    (e.ofSubalgebras H K h).symm =
      e.symm.ofSubalgebras K H ((LieSubalgebra.map_symm_eq_iff e).2 h) :=
  LieEquiv.ext fun _ ↦ Subtype.ext (by simp)

end LieEquiv

end Equiv

section Automorphism

variable {L : Type*} [LieRing L] [LieAlgebra R L] (σ : L ≃ₗ⁅R⁆ L) {H : LieSubalgebra R L}

namespace LieSubalgebra

/-- An involutive automorphism that maps a Lie subalgebra `H` into itself normalises `H`. -/
theorem map_eq_self_of_involutive (h_inv : Function.Involutive σ) (h_mem : ∀ x ∈ H, σ x ∈ H) :
    H.map σ = H :=
  map_eq_of_mem σ h_mem fun x hx ↦ by
    rw [σ.symm_apply_eq.mpr (h_inv x).symm]
    exact h_mem x hx

/-- An automorphism acting by `-1` on a subalgebra normalises it, since a subalgebra is closed
under negation. -/
theorem map_eq_self_of_forall_mem_apply_eq_neg (hneg : ∀ y ∈ H, σ y = -y) : H.map σ = H :=
  map_eq_of_mem σ (fun y hy ↦ hneg y hy ▸ neg_mem hy) fun y hy ↦ by
    rw [σ.symm_apply_eq.mpr (by rw [hneg (-y) (neg_mem hy), neg_neg])]
    exact neg_mem hy

end LieSubalgebra

end Automorphism

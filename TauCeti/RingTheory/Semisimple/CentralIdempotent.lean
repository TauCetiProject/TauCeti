/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix
public import TauCeti.RingTheory.CentralIdempotent

/-!
# Semisimple rings with no nontrivial central idempotents

A nonzero semisimple ring whose only central idempotents are `0` and `1` is simple
(`IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset`). By the Wedderburn–Artin
theorem it is a product of `n` matrix rings over division rings, which has `2 ^ n` central
idempotents (`TauCeti.card_centralIdempotents_pi_of_isSimpleRing`); so `n = 1`.

## Main results

* `IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset`: a nontrivial semisimple
  ring whose central idempotents are `0` and `1` is simple.
-/

public section

open TauCeti

/-- **Semisimple rings without nontrivial central idempotents are simple.** A nontrivial
semisimple ring `R` whose central idempotents are among `0` and `1` is simple: a Wedderburn–Artin
presentation of `R` as a product of `n` matrix rings over division rings has `2 ^ n` central
idempotents, so `n = 1`. -/
theorem IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset {R : Type*} [Ring R]
    [IsSemisimpleRing R] [Nontrivial R] (h : centralIdempotents R ⊆ {0, 1}) :
    IsSimpleRing R := by
  obtain ⟨n, D, d, _, _, hd, ⟨φ⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing ℤ R
  have : ∀ i, Nonempty (Fin (d i)) := fun i ↦ ⟨⟨0, NeZero.pos (d i)⟩⟩
  have h01 : centralIdempotents R = {0, 1} :=
    h.antisymm (by simp [Set.insert_subset_iff, zero_mem_centralIdempotents,
      one_mem_centralIdempotents])
  have hcard := RingEquiv.card_centralIdempotents_congr φ.toRingEquiv
  rw [card_centralIdempotents_pi_of_isSimpleRing, Nat.card_fin, h01, Nat.card_coe_set_eq,
    Set.ncard_pair zero_ne_one] at hcard
  obtain rfl : n = 1 := Nat.pow_right_injective le_rfl (by simpa using hcard.symm)
  exact IsSimpleRing.of_ringEquiv (φ.toRingEquiv.trans (RingEquiv.piUnique _)).symm inferInstance

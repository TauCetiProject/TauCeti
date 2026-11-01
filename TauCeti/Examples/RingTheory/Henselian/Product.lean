/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Product
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.ZMod.LocalRing

/-!
# Checks for products of henselian pairs

Products of the Artinian local ring `ℤ/4ℤ` give finite and infinite henselian
pairs with nonzero defining ideals. The empty product is allowed, and a bad
factor cannot be hidden among good factors.
-/

public section

open Polynomial IsLocalRing

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : IsLocalRing (ZMod 4) := inferInstanceAs (IsLocalRing (ZMod (2 ^ 2)))

-- The maximal ideal in ℤ/4ℤ is nonzero; these are not just zero-ideal pairs.
example : (2 : ZMod 4) ∈ maximalIdeal (ZMod 4) ∧ (2 : ZMod 4) ≠ 0 := by
  constructor
  · rw [mem_maximalIdeal, mem_nonunits_iff]
    exact (ZMod.isUnit_iff_coprime 2 4).not.mpr (by decide)
  · decide

-- A finite disconnected base, with genuine nilpotent defining ideals.
example : HenselianRing (Fin 2 → ZMod 4)
    (Ideal.pi fun _ ↦ maximalIdeal (ZMod 4)) := inferInstance

-- Infinite products require neither Noetherianity nor a finite index set.
example : HenselianRing (ℕ → ZMod 4)
    (Ideal.pi fun _ ↦ maximalIdeal (ZMod 4)) := inferInstance

-- The empty product is the zero ring and is henselian at its unique ideal.
example : HenselianRing (PEmpty → ℤ) (Ideal.pi fun _ ↦ ⊤) := by
  have : ∀ i : PEmpty, HenselianRing ℤ (⊤ : Ideal ℤ) := fun i ↦ nomatch i
  exact (Ideal.henselianRing_pi_iff _).2 this

-- In the infinite product, the simple root 0 of X²-X-2 modulo the product ideal
-- lifts to a root in that ideal (coordinatewise, the lift is 2).
example : ∃ a : ℕ → ZMod 4,
    (X ^ 2 - X - C (2 : ℕ → ZMod 4)).IsRoot a ∧
      a ∈ Ideal.pi (fun _ : ℕ ↦ maximalIdeal (ZMod 4)) := by
  let I : Ideal (ℕ → ZMod 4) := Ideal.pi fun _ ↦ maximalIdeal (ZMod 4)
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (I := I)
    (X ^ 2 - X - C (2 : ℕ → ZMod 4))
    (by monicity; norm_num) 0
    (by
      intro i
      simp only [eval_sub, eval_pow, eval_X, eval_C, zero_pow (by decide : 2 ≠ 0),
        sub_zero, zero_sub, Pi.neg_apply, Pi.ofNat_apply]
      rw [Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff]
      exact (ZMod.isUnit_iff_coprime 2 4).not.mpr (by decide))
    (by simp [derivative_sub])
  exact ⟨a, ha, by simpa using haI⟩

-- The zero ideal is henselian even in ℤ, but the ideal (5) is not: it is not
-- contained in the Jacobson radical. A product with this bad factor is rejected.
example : ¬ HenselianRing (Fin 2 → ℤ)
    (Ideal.pi fun i ↦ if i = 0 then ⊥ else Ideal.span {(5 : ℤ)}) := by
  intro h
  have hbad := (Ideal.henselianRing_pi_iff _).1 h 1
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] at hbad
  have h5 : (5 : ℤ) ∈ Ideal.jacobson ⊥ := hbad.jac (Ideal.subset_span (by simp))
  have hu := Ideal.mem_jacobson_bot.1 h5 1
  norm_num [Int.isUnit_iff] at hu

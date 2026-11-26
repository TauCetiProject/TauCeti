/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.BigOperators.ModEq

/-!
# The power-sum congruence of Voronoi

At a multiple `F` of the character's level, the Voronoi floor sum arises from permuting
all residues modulo `F` and expanding the powers of their representatives modulo `F²`.
The coefficients use the original character at its own modulus: they do not vanish at the
additional nonunits of `ZMod F` unless the original character vanishes there.

The congruence is the power-sum step of `New.OddPart.voronoi_congruence` in
`grh/src/Lib/Cyclotomic/Voronoi.lean` of [grh-lean](https://github.com/lsernau/grh-lean) at
`72fead102f663d5c7a407964a13dc0cf9d977207`. Here the multiplier can act by an arbitrary
character value, not only by `1`.
-/

public section

open Finset

namespace DirichletCharacter

/-- Let `F` be a multiple of the level of `χ` and let `c` be prime to `F`. Modulo `F²`,
`(χ(c)c^(e+1) − 1)` times the character-weighted power sum of degree `e+1` equals
`(e+1)χ(c)c^e F` times the character-weighted floor sum of degree `e`. The character
values in both sums are taken at the original level. -/
theorem sq_dvd_mul_sum_pow_sub_floor_sum {R : Type*} [CommRing R] {N F c : ℕ}
    (χ : DirichletCharacter R N) (hNF : N ∣ F) (hc : c.Coprime F) (e : ℕ) :
    (F : R) ^ 2 ∣
      (χ c * c ^ (e + 1) - 1) * (∑ t ∈ range F, χ t * (t : R) ^ (e + 1)) -
        (e + 1 : R) * χ c * c ^ e * F *
          (∑ t ∈ range F, χ t * (t : R) ^ e * (c * t / F : ℕ)) := by
  have hr (t : ℕ) : χ (c * t % F : ℕ) = χ c * χ t := by
    have hcast : ((c * t % F : ℕ) : ZMod N) = ((c * t : ℕ) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff' ..).mpr (Nat.mod_mod_of_dvd _ hNF)
    rw [hcast, Nat.cast_mul, map_mul]
  have hperm := hc.sum_range_mul_mod (fun t ↦ χ t * (t : R) ^ (e + 1))
  rw [sub_one_mul]
  nth_rw 2 [← hperm]
  simp only [mul_sum, ← sum_sub_distrib]
  refine Finset.dvd_sum fun t _ ↦ ?_
  let a := c * t % F
  let b := c * t / F
  have hab : ((c : R) * t) = (a : R) + (F : R) * b := by
    simpa only [Nat.cast_mul, Nat.cast_add] using
      congrArg (fun n : ℕ ↦ (n : R)) (Nat.mod_add_div (c * t) F).symm
  have h₁ := sq_dvd_add_pow_sub_sub ((F : R) * (b : R)) (a : R) (e + 1)
  have h₂ := sub_dvd_pow_sub_pow ((c : R) * t) (a : R) e
  have hd : (F : R) ∣ (c : R) * t - (a : R) := ⟨b, by linear_combination hab⟩
  obtain ⟨v, hv⟩ := hd.trans h₂
  obtain ⟨w, hw⟩ := h₁
  refine ⟨χ c * χ t * ((b : R) ^ 2 * w - (e + 1 : R) * b * v), ?_⟩
  rw [hr]
  rw [← hab] at hw
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hw hv ⊢
  -- The linear term can use either representative modulo `F`, since it already carries `F`.
  linear_combination χ c * χ t * (hw - (e + 1 : R) * b * F * hv)

end DirichletCharacter

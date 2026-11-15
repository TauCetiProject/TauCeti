/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Pow

/-!
# Examples of profinite powers

This file computes profinite powering in the cyclic group `Multiplicative (ZMod 6)`. A profinite
power only depends on the exponent modulo six. The idempotent `zHat.idem 2`, which selects the
`2`-adic component of a profinite integer, reduces to `3` modulo six: it is `1` modulo two and
`0` modulo three. Consequently, powering by this idempotent sends `x` to `x ^ 3`, the `2`-primary
part of `x`.

The computation illustrates simultaneously the finite-level projections of the profinite
integers and extraction of prime parts by their idempotents.

## Main results

* `Multiplicative.zpowHat_eq_pow_val_toZMod_six`: profinite powers in `Multiplicative (ZMod 6)` are
  ordinary powers by the residue modulo six.
* `Multiplicative.zpowHat_idem_two_eq_cube_zmod_six`: the `2`-primary part of `x` is `x ^ 3`.
-/

public section

open TauCeti
open scoped TauCeti.zHat

namespace Multiplicative

/-- In the cyclic group `Multiplicative (ZMod 6)`, a profinite power is the ordinary power by
the exponent's residue modulo six. -/
theorem zpowHat_eq_pow_val_toZMod_six (x : Multiplicative (ZMod 6))
    (a : Additive zHat.{u}) :
      x ^ᶻ a = x ^ (zHat.toZMod (⟨6, by norm_num⟩ : ℕ+) a).val := by
  have hcard : Nat.card (Multiplicative (ZMod 6)) = 6 := by simp
  have hn : (⟨Nat.card (Multiplicative (ZMod 6)), Nat.card_pos⟩ : ℕ+) =
      (⟨6, by norm_num⟩ : ℕ+) := by
    apply PNat.coe_injective
    exact hcard
  convert zpowHat_eq_pow_val_toZMod_natCard x a using 1
  rw [hn]

/-- In `Multiplicative (ZMod 6)`, profinite powering by the `2`-adic idempotent extracts the
`2`-primary component: it is the ordinary cube. -/
@[simp]
theorem zpowHat_idem_two_eq_cube_zmod_six (x : Multiplicative (ZMod 6)) :
    x ^ᶻ zHat.idem.{u} 2 = x ^ 3 := by
  rw [zpowHat_eq_pow_val_toZMod_six]
  congr 1
  let y : ZMod 6 := zHat.toZMod (⟨6, by norm_num⟩ : ℕ+) (zHat.idem.{u} 2)
  -- The goal is `(zHat.toZMod 6 (zHat.idem 2)).val = 3`; folding it into the local definition `y`
  -- (a definitional restatement) lets the final `omega` see the same atom `y.val` as `h2`, `h3`.
  change y.val = 3
  have h2 : (ZMod.cast y : ZMod 2) = 1 := by
    convert
      (zHat.cast_toZMod (m := (2 : ℕ+)) (n := (6 : ℕ+)) (by norm_num)
          (zHat.idem.{u} 2)).trans
        (zHat.toZMod_idem_of_dvd_pow (ℓ := 2) (n := (2 : ℕ+)) (k := 1) (by norm_num)) using 1 <;>
      rfl
  have h3 : (ZMod.cast y : ZMod 3) = 0 := by
    convert
      (zHat.cast_toZMod (m := (3 : ℕ+)) (n := (6 : ℕ+)) (by norm_num)
          (zHat.idem.{u} 2)).trans
        (zHat.toZMod_idem_of_not_dvd (ℓ := 2) (n := (3 : ℕ+)) (by norm_num)) using 1 <;>
      rfl
  have hylt : y.val < 6 := y.val_lt
  rw [ZMod.cast_eq_val, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff'] at h2
  rw [ZMod.cast_eq_val, ← Nat.cast_zero, ZMod.natCast_eq_natCast_iff'] at h3
  omega

end Multiplicative

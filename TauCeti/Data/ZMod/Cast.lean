/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Successive reductions modulo divisors

For `n ∣ m ∣ d`, reducing a class modulo `d` first modulo `m` and then modulo `n` is reducing it
modulo `n` directly (`ZMod.cast_cast_of_dvd`, the pointwise form of Mathlib's
`ZMod.castHom_comp`). Consequently the classes modulo `d` above the classes modulo `m` lying over
`a : ZMod n` are exactly the classes modulo `d` lying over `a`
(`ZMod.preimage_cast_setOf_cast_eq`).
-/

public section

namespace ZMod

/-- Reducing modulo `m` and then modulo `n ∣ m` is reducing modulo `n`. -/
theorem cast_cast_of_dvd {n m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) (b : ZMod d) :
    (cast (cast b : ZMod m) : ZMod n) = cast b :=
  DFunLike.congr_fun (castHom_comp hm hd) b

/-- For `n ∣ m ∣ d`, the classes modulo `d` whose reduction modulo `m` lies over `a : ZMod n` are
the classes modulo `d` lying over `a`. -/
theorem preimage_cast_setOf_cast_eq {n m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) (a : ZMod n) :
    (fun b : ZMod d ↦ (cast b : ZMod m)) ⁻¹' {b | (cast b : ZMod n) = a} =
      {b | (cast b : ZMod n) = a} := by
  ext b
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, cast_cast_of_dvd hm hd]

end ZMod

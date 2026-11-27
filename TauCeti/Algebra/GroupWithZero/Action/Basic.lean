/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Set.Operations
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Actions of groups with zero

The scalar rescaling identity `TauCeti.div_mul_smul_smul_cancel_left` cancels a nonzero factor
in the denominator against a scalar action, including when the remaining denominator is zero.
If `t` is the preimage of `s` under scaling by a nonzero `r`, then `s` is the preimage of `t` under
scaling by `r⁻¹` (`TauCeti.eq_preimage_inv_smul_of_eq_preimage_smul₀`).

Rescaling a pair `(d, v)` by a nonzero factor does not change its velocity `d⁻¹ • v`
(`Prod.inv_fst_smul_snd_smul`).
-/

public section

namespace TauCeti

/-- Rescaling `k • v` by `a / (k * b)` is rescaling `v` by `a / b`. -/
theorem div_mul_smul_smul_cancel_left {K M : Type*} [GroupWithZero K] [MulAction K M]
    {k : K} (hk : k ≠ 0) (a b : K) (v : M) :
    (a / (k * b)) • k • v = (a / b) • v := by
  rw [smul_smul, div_mul_eq_div_div_swap, div_mul_cancel₀ _ hk]

open scoped Pointwise in
/-- If `t` is the preimage of `s` under scaling by a nonzero element `r` of a group with zero, then
`s` is the preimage of `t` under scaling by `r⁻¹`. -/
theorem eq_preimage_inv_smul_of_eq_preimage_smul₀ {G₀ X : Type*} [GroupWithZero G₀]
    [MulAction G₀ X] {r : G₀} (hr : r ≠ 0) {s t : Set X} (h : t = (r • ·) ⁻¹' s) :
    s = (r⁻¹ • ·) ⁻¹' t := by
  rw [h, Set.preimage_smul_inv₀ hr, Set.preimage_smul₀ hr, smul_inv_smul₀ hr]

end TauCeti

/-- Rescaling a pair `(d, v)` by a nonzero factor does not change the velocity `d⁻¹ • v`. -/
theorem Prod.inv_fst_smul_snd_smul {R M : Type*} [GroupWithZero R] [MulAction R M] {a : R}
    (ha : a ≠ 0) (z : R × M) : (a • z).1⁻¹ • (a • z).2 = z.1⁻¹ • z.2 := by
  rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_inv_rev, mul_smul, inv_smul_smul₀ ha]

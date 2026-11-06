/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Order.Interval.Set.Infinite

/-!
# The additive circle is infinite

For a positive period `p` in an ordered additive group, the quotient map `𝕜 → AddCircle p` is
injective on every half-open interval `[a, a + p)`; no archimedean hypothesis is needed. If `𝕜` is
moreover densely ordered, these intervals are infinite, so `AddCircle p` is infinite. In particular
the unit circle `UnitAddCircle` is infinite.

## Main results

* `AddCircle.injOn_coe_Ico`: the quotient map is injective on `[a, a + p)`.
* `AddCircle.infinite`: `AddCircle p` is infinite, as an instance.
-/

public section

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] {p : 𝕜}
  [hp : Fact (0 < p)]

/-- The quotient map `𝕜 → AddCircle p` is injective on every half-open interval `[a, a + p)`.
Unlike `AddCircle.coe_eq_coe_iff_of_mem_Ico`, this needs no archimedean hypothesis. -/
theorem injOn_coe_Ico (a : 𝕜) : Set.InjOn ((↑) : 𝕜 → AddCircle p) (Set.Ico a (a + p)) := by
  -- If `m • p = x - y` for `x, y ∈ [a, a + p)`, then `x - y < p`, so `m < 1`.
  have key {x y : 𝕜} {m : ℤ} (hx : x ∈ Set.Ico a (a + p)) (hy : y ∈ Set.Ico a (a + p))
      (h : m • p = x - y) : m < 1 := by
    rw [← zsmul_lt_zsmul_iff_left hp.out, h, one_zsmul, sub_lt_iff_lt_add']
    exact hx.2.trans_le (add_le_add_left hy.1 p)
  intro x hx y hy hxy
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff p).1 <| (coe_sub p x y).trans <| sub_eq_zero.2 hxy
  have h₁ := key hx hy hn
  have h₂ := key hy hx (by rw [neg_zsmul, hn, neg_sub])
  rw [← sub_eq_zero, ← hn, show n = 0 by omega, zero_zsmul]

/-- The additive circle of a positive period in a densely ordered additive group is infinite,
since the quotient map is injective on the infinite interval `[0, p)`. -/
instance infinite [DenselyOrdered 𝕜] : Infinite (AddCircle p) :=
  have := (Set.Ico_infinite (lt_add_of_pos_right 0 hp.out)).to_subtype
  Infinite.of_injective _ (injOn_coe_Ico 0).injective

end AddCircle

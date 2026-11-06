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

For a positive period `p` in a densely ordered additive group, the quotient map is injective on
the half-open interval `[0, p)`, which is infinite, so `AddCircle p` is infinite. No archimedean
hypothesis is needed. In particular the unit circle `UnitAddCircle` is infinite.

## Main results

* `AddCircle.infinite`: `AddCircle p` is infinite, as an instance.
-/

public section

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
  {p : 𝕜} [hp : Fact (0 < p)]

/-- The additive circle of a positive period in a densely ordered additive group is infinite,
since the quotient map is injective on the infinite interval `[0, p)`. -/
instance infinite : Infinite (AddCircle p) :=
  have := (Set.Ico_infinite hp.out).to_subtype
  Infinite.of_injective (fun x : Set.Ico 0 p ↦ (x : AddCircle p)) fun x y hxy ↦ Subtype.ext <| by
    obtain ⟨n, hn⟩ := (coe_eq_zero_iff p).1 <| (coe_sub p x y).trans <| sub_eq_zero.2 hxy
    have h₁ : (-1 : ℤ) < n := by
      rw [← zsmul_lt_zsmul_iff_left hp.out, hn, neg_one_zsmul, neg_lt_sub_iff_lt_add]
      exact y.2.2.trans_le (le_add_of_nonneg_right x.2.1)
    have h₂ : n < 1 := by
      rw [← zsmul_lt_zsmul_iff_left hp.out, hn, one_zsmul, sub_lt_iff_lt_add]
      exact x.2.2.trans_le (le_add_of_nonneg_right y.2.1)
    rw [← sub_eq_zero, ← hn, show n = 0 by omega, zero_zsmul]

end AddCircle

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2

/-!
# Brackets in the coordinates of an `sl₂` triple and a central element

For an `sl₂` triple `(h, e, f)` and a central element `z` of a Lie algebra, the bracket of two
combinations `a h + b e + c f + d z` and `a' h + b' e + c' f + d' z` is

`(b c' - c b') h + 2 (a b' - b a') e - 2 (a c' - c a') f`.

This is the bracket of `𝔤𝔩₂ = 𝔰𝔩₂ ⊕ 𝔷` in the coordinates of a triple and the centre, so a linear
map out of `𝔤𝔩₂` sending such a basis to elements obeying the same relations is a Lie algebra
homomorphism.

## Main results

* `IsSl2Triple.lie_smul_add_smul_add_smul_add_smul`: the bracket formula above.
-/

public section

variable {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] {h e f : L}

namespace IsSl2Triple

/-- The bracket of two combinations `a h + b e + c f + d z` of an `sl₂` triple and a central element
`z`, in the coordinates of the triple. -/
theorem lie_smul_add_smul_add_smul_add_smul (t : IsSl2Triple h e f) {z : L}
    (hz : ∀ x : L, ⁅z, x⁆ = 0) (a b c d a' b' c' d' : K) :
    ⁅a • h + b • e + c • f + d • z, a' • h + b' • e + c' • f + d' • z⁆ =
      (b * c' - c * b') • h + (2 * (a * b' - b * a')) • e + (-(2 * (a * c' - c * a'))) • f := by
  have hfe : ⁅f, e⁆ = -h := by rw [← lie_skew, t.lie_e_f]
  have hhe : ⁅h, e⁆ = (2 : K) • e := t.lie_h_e_smul K
  have hhf : ⁅h, f⁆ = -((2 : K) • f) := t.lie_lie_smul_f K
  have heh : ⁅e, h⁆ = -((2 : K) • e) := by rw [← lie_skew, hhe]
  have hfh : ⁅f, h⁆ = (2 : K) • f := by rw [← lie_skew, hhf, neg_neg]
  have hz' : ∀ x : L, ⁅x, z⁆ = 0 := fun x ↦ by rw [← lie_skew, hz, neg_zero]
  simp only [lie_add, add_lie, lie_smul, smul_lie, lie_self, t.lie_e_f, hfe, hhe, hhf, heh, hfh, hz,
    hz', smul_zero, add_zero, zero_add, smul_neg, smul_smul]
  module

end IsSl2Triple

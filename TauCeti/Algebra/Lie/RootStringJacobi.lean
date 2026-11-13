/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Lie.Basic

/-!
# Root-string Jacobi identity for doubly-laced chains in Lie rings

In the derivation of Steinberg's doubly-laced Chevalley commutator relations from universal
enveloping algebra normal-ordering formulas, let `x, y, z, w` correspond to root vectors for
`α, β, α + β, 2α + β` satisfying `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and `⁅y, z⁆ = 0`.
Applying the Jacobi identity to `y`, `x`, and `z` yields `2 • (d • ⁅y, w⁆) = 0`, so in any
additively torsion-free Lie ring the scaled bracket `d • ⁅y, w⁆` vanishes automatically without a
separate root-datum hypothesis excluding `β + (2α + β) = 2(α + β)`.

## Main results

* `TauCeti.zsmul_lie_eq_zero_of_zsmul_lie_eq_two_mul_zsmul`: in an additively torsion-free Lie ring,
  `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and `⁅y, z⁆ = 0` force `d • ⁅y, w⁆ = 0`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §25.
-/

public section

namespace TauCeti

section LieRing

variable {L : Type*} [LieRing L] [IsAddTorsionFree L]

/-- In an additively torsion-free Lie ring, if `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and
`⁅y, z⁆ = 0`, the Jacobi identity forces `d • ⁅y, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_zsmul_lie_eq_two_mul_zsmul {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w) (hyz : ⁅y, z⁆ = 0) :
    d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (2 : ℤ)) (by decide)).mp ?_
  calc (2 : ℤ) • (d • ⁅y, w⁆) = c • ⁅y, ⁅x, z⁆⁆ := by
        rw [← mul_zsmul, ← lie_zsmul, ← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + c • ⁅x, ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add]
    _ = 0 := by rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_zero]; simp

end LieRing

end TauCeti

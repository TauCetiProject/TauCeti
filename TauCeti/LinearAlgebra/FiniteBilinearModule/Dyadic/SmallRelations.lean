/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.Classification
public import TauCeti.LinearAlgebra.FiniteBilinearModule.Dyadic.RankTwo.Basic
import Mathlib.Tactic.Ring

/-!
# The small-exponent dyadic relations

Multiplying a cyclic coefficient by five leaves its quadratic form of order two unchanged
up to isometry. For bilinear forms, all odd cyclic coefficients of order two give the
same form, the polar forms of `u^{(2)}(2)` and `v^{(2)}(2)` agree, and multiplication by
five leaves a cyclic form of order four unchanged. These are Nikulin's exceptional
small-exponent relations. The rank-two assertion concerns only the polar forms; the
quadratic forms of `u` and `v` at order two differ.

The cyclic bilinear coefficient-congruence construction also applies at every exponent.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*,
  Proposition 1.8.2(i), (j).
-/

public section

namespace TauCeti.FiniteQuadraticModule

/-- Multiplication by five preserves the quadratic cyclic form of order two.
This is Nikulin's relation 1.8.2(i) for odd coefficients; the same identity holds for
the degenerate extension with an even coefficient. -/
noncomputable def dyadicCyclicOneIsometryFiveMul (θ : ℤ) :
    Isometry (dyadicCyclic 1 θ) (dyadicCyclic 1 (5 * θ)) :=
  Classical.choice <| by
    rw [nonempty_isometry_dyadicCyclic_iff]
    refine ⟨1, ?_⟩
    -- The unit `1` has integer representative `1`; its doubled denominator is `4`.
    rw [show (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 by decide]
    change (θ : ZMod 4) = ((5 * θ * (1 : ℤ) ^ 2 : ℤ) : ZMod 4)
    -- Reducing the integer cast modulo four identifies the coefficient `5` with `1`.
    rw [one_pow, mul_one, Int.cast_mul, Int.cast_ofNat,
      show (5 : ZMod 4) = 1 by decide, one_mul]

/-- The dyadic rank-two generators at exponent one have isometric polar pairings,
as in Nikulin's relation 1.8.2(j). -/
noncomputable def dyadicUOneBilinearIsometryDyadicVOne :
    FiniteBilinearModule.Isometry (dyadicU 1).toFiniteBilinearModule
      (dyadicV 1).toFiniteBilinearModule := by
  let g : FiniteBilinearModule.Hom (dyadicU 1).toFiniteBilinearModule
      (dyadicV 1).toFiniteBilinearModule :=
    { toAddMonoidHom := AddMonoidHom.id (ZMod 2 × ZMod 2)
      map_pairing' := fun x y ↦ by
        -- Both bundled carriers are the coordinate group `(ℤ/2)²`.
        change (dyadicV 1).toFiniteBilinearModule.pairing x y =
          (dyadicU 1).toFiniteBilinearModule.pairing x y
        erw [dyadicV_pairing, dyadicU_pairing]
        -- The diagonal terms vanish because `2 = 0` in the coordinate ring `ZMod 2`.
        simp only [show (2 : ZMod (2 ^ 1)) = 0 by decide, zero_mul, zero_add, add_zero] }
  exact g.toIsometry (by exact Function.bijective_id)

/-- The bilinear isometry between the order-two rank-two generators fixes the coordinates. -/
@[simp]
theorem dyadicUOneBilinearIsometryDyadicVOne_apply (x : ZMod 2 × ZMod 2) :
    dyadicUOneBilinearIsometryDyadicVOne x = x := by
  unfold dyadicUOneBilinearIsometryDyadicVOne
  erw [FiniteBilinearModule.Hom.toIsometry_apply,
    ← FiniteBilinearModule.Hom.coe_toAddMonoidHom, AddMonoidHom.id_apply]

end TauCeti.FiniteQuadraticModule

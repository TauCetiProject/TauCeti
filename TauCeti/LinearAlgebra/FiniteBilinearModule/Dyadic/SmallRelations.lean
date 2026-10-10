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
    rw [show (1 : (ZMod (2 ^ 1))ˣ).val.val = 1 by decide]
    change (θ : ZMod 4) = ((5 * θ * (1 : ℤ) ^ 2 : ℤ) : ZMod 4)
    rw [one_pow, mul_one, Int.cast_mul, Int.cast_ofNat,
      show (5 : ZMod 4) = 1 by decide, one_mul]

/-- All odd cyclic coefficients give isometric bilinear forms of order two,
as in Nikulin's relation 1.8.2(j). -/
noncomputable def dyadicCyclicOneBilinearIsometry {θ η : ℤ} (hθ : Odd θ) (hη : Odd η) :
    FiniteBilinearModule.Isometry (dyadicCyclic 1 θ).toFiniteBilinearModule
      (dyadicCyclic 1 η).toFiniteBilinearModule := by
  apply dyadicCyclicBilinearIsometryOfModEq
  change θ ≡ η [ZMOD 2]
  obtain ⟨a, rfl⟩ := hθ
  obtain ⟨b, rfl⟩ := hη
  exact Int.modEq_iff_dvd.mpr ⟨b - a, by ring⟩

/-- Multiplication by five preserves the cyclic bilinear form of order four.
This is Nikulin's relation 1.8.2(j) for odd coefficients, and also holds for even ones. -/
noncomputable def dyadicCyclicTwoBilinearIsometryFiveMul (θ : ℤ) :
    FiniteBilinearModule.Isometry (dyadicCyclic 2 θ).toFiniteBilinearModule
      (dyadicCyclic 2 (5 * θ)).toFiniteBilinearModule := by
  apply dyadicCyclicBilinearIsometryOfModEq
  change θ ≡ 5 * θ [ZMOD 4]
  exact Int.modEq_iff_dvd.mpr ⟨θ, by ring⟩

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
        simp only [show (2 : ZMod (2 ^ 1)) = 0 by decide, zero_mul, zero_add, add_zero] }
  exact g.toIsometry (by exact Function.bijective_id)

end TauCeti.FiniteQuadraticModule

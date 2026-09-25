/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.Basic

/-!
# The Pin group inside the Lipschitz group

The Pin group is the subgroup of the Lipschitz group whose elements have unit Clifford norm.
This file packages its inclusion into the Lipschitz group, the vector generators with norm `-1`,
and the Spin inclusion used when transporting norms and actions along those maps.
-/

public section

universe u v

namespace CliffordAlgebra

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  (Q : QuadraticForm R M)

variable {Q}

/-- A vector of norm `-1` lies in the Pin group. The sign is Mathlib's convention: `star` is the
reversal composed with the grade involution, so the unitarity condition reads `-Q v = 1`. -/
theorem ι_mem_pinGroup {v : M} (hv : Q v = -1) : ι Q v ∈ pinGroup Q := by
  let : Invertible (Q v) := ⟨-1, by rw [hv]; ring, by rw [hv]; ring⟩
  have hsq : ι Q v * ι Q v = -1 := by rw [ι_sq_scalar, hv, map_neg, map_one]
  refine ⟨⟨unitι Q v, unitι_mem_lipschitzGroup v, coe_unitι v⟩, ?_, ?_⟩
  · rw [star_ι, neg_mul, hsq, neg_neg]
  · rw [star_ι, mul_neg, hsq, neg_neg]

variable (Q)

/-- The Pin group includes into the Lipschitz group. -/
def pinToLipschitz : pinGroup Q →* lipschitzGroup Q where
  toFun x := ⟨pinGroup.toUnits x, pinGroup.units_mem_lipschitzGroup x.2⟩
  map_one' := Subtype.ext (map_one (pinGroup.toUnits (Q := Q)))
  map_mul' x y := Subtype.ext (map_mul (pinGroup.toUnits (Q := Q)) x y)

@[simp]
theorem coe_pinToLipschitz_apply (x : pinGroup Q) :
    ((pinToLipschitz Q x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      (x : CliffordAlgebra Q) := by
  rw [pinToLipschitz]
  rfl

/-- The spin group sits inside the Pin group. -/
def spinToPin : spinGroup Q →* pinGroup Q :=
  Submonoid.inclusion fun _ hx => spinGroup.mem_pin hx

variable {Q}

@[simp]
theorem coe_spinToPin_apply (x : spinGroup Q) :
    ((spinToPin Q x : pinGroup Q) : CliffordAlgebra Q) = (x : CliffordAlgebra Q) := by
  rw [spinToPin]
  rfl

end CliffordAlgebra

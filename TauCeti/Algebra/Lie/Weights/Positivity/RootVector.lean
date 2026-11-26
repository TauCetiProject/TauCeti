/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Positivity
public import TauCeti.Algebra.Lie.Weights.Sl2System

/-!
# Positivity of the Killing pairing of normalised root vectors

For a normalised family `x` of root vectors (`TauCeti.IsSl2System`), the Killing pairing
`B(x α, x (-α)) = 2 / ⟨α, α⟩` (`TauCeti.IsSl2System.killingForm_root_neg_eq`) is a positive
rational number, because `⟨α, α⟩` is (`TauCeti.exists_pos_rat_invForm_root_self`). Over `ℂ` this
is what makes the Hermitian Killing form of the compact conjugation positive on root vectors.

## Main results

* `TauCeti.IsSl2System.exists_pos_rat_killingForm_rootVector_neg`: `B(x α, x (-α))` is a positive
  rational number.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **The Killing pairing of normalised opposite root vectors is a positive rational**: it is
`2 / ⟨α, α⟩` (`TauCeti.IsSl2System.killingForm_root_neg_eq`). -/
theorem IsSl2System.exists_pos_rat_killingForm_rootVector_neg {x : Weight K H L → L}
    (hx : IsSl2System x) {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ q : ℚ, 0 < q ∧ killingForm K L (x α) (x (-α)) = (q : K) := by
  obtain ⟨q, hq, hqα⟩ := exists_pos_rat_invForm_root_self hα
  rw [invForm_apply_apply] at hqα
  refine ⟨2 * q⁻¹, by positivity, ?_⟩
  rw [hx.killingForm_root_neg_eq α hα]
  have h : α ((cartanEquivDual H).symm α) = (q : K) := by simpa using hqα
  rw [h]
  push_cast
  ring

end TauCeti

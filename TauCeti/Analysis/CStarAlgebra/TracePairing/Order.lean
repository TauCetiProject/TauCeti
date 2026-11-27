/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Order

/-!
# Trace pairings and the order of `K₀`

Let `τ` be a positive tracial functional on a C⋆-algebra `A` and `τ_*` its pairing with the
projection `K₀`-group (`TauCeti.PositiveTracialFunctional.kZeroPairing`).

* `τ_*` is nonnegative on the positive cone `K₀(A)⁺`, the classes of matrix projections
  (`TauCeti.PositiveTracialFunctional.kZeroPairing_nonneg_of_mem_positiveCone`).
* For unital `A`, the order unit `[1_A]` pairs to `τ(1)`
  (`TauCeti.PositiveTracialFunctional.kZeroPairing_orderUnit`), and the scale, the classes of
  projections of `A` itself, pairs into `[0, τ(1)]`
  (`TauCeti.PositiveTracialFunctional.kZeroPairing_le_of_mem_scale`). So a positive tracial
  functional with `τ(1) = 1`, a tracial state, induces a state of the ordered group
  `(K₀(A), K₀(A)⁺, [1_A])`: a homomorphism to `ℝ`, nonnegative on the cone, with value `1` at
  the order unit.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §6.3 and §6.9.
-/

public section

namespace TauCeti

namespace PositiveTracialFunctional

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : PositiveTracialFunctional A)

/-- **Positivity on the cone.** The trace pairing is nonnegative on the positive cone of
`K₀(A)`. -/
theorem kZeroPairing_nonneg_of_mem_positiveCone {x : ProjectionKZero A}
    (hx : x ∈ ProjectionKZero.positiveCone A) : 0 ≤ τ.kZeroPairing x := by
  obtain ⟨k, p, hp, rfl⟩ := ProjectionKZero.mem_positiveCone_iff_exists_mk.1 hx
  exact τ.kZeroPairing_of_mk_nonneg hp

end NonUnital

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : PositiveTracialFunctional A)

/-- The order unit `[1_A]` pairs to `τ(1)`. -/
@[simp]
theorem kZeroPairing_orderUnit : τ.kZeroPairing (ProjectionKZero.orderUnit A) = (τ 1).re := by
  rw [ProjectionKZero.orderUnit_def, kZeroPairing_of_mk_one, Nat.cast_one, one_mul]

/-- The scale pairs below the order unit: `τ_* [p] ≤ τ(1)` for a projection `p` of `A`. -/
theorem kZeroPairing_le_of_mem_scale {x : ProjectionKZero A}
    (hx : x ∈ ProjectionKZero.scale A) : τ.kZeroPairing x ≤ (τ 1).re := by
  have h := τ.kZeroPairing_nonneg_of_mem_positiveCone
    (ProjectionKZero.sub_mem_positiveCone_of_mem_scale hx)
  rwa [map_sub, kZeroPairing_orderUnit, sub_nonneg] at h

end Unital

end PositiveTracialFunctional

end TauCeti

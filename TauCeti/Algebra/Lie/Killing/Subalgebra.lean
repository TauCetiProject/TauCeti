/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Killing
import Mathlib.LinearAlgebra.PID

/-!
# The Killing form of a subalgebra stable under brackets with the ambient algebra

Let `K` be a Lie subalgebra of a Lie algebra `L` that is finite and free over a principal ideal
domain, and suppose that `⁅x, y⁆ ∈ K` for every `x ∈ K` and every `y ∈ L`, that is, `K` is an
ideal. Then the Killing form of `K` is the restriction of the Killing form of `L`: for `x, y ∈ K`
the operator `ad x ∘ ad y` of `L` takes values in `K`, so its trace on `L` is the trace of its
restriction to `K` (`LinearMap.trace_restrict_eq_of_forall_mem`). This is Mathlib's
`LieIdeal.killingForm_eq`, stated for a subalgebra rather than an ideal, so that it applies to
Lie algebras such as `𝔰𝔩 n R` that are defined as subalgebras. The nested form compares the
Killing forms of two subalgebras `K ≤ K'` when `⁅K, K'⁆ ⊆ K`, for instance the special and the
full indefinite unitary Lie algebras.

## Main results

* `LieSubalgebra.killingForm_eq_of_lie_mem`: `κ_K(x, y) = κ_L(x, y)` when `⁅K, L⁆ ⊆ K`.
* `LieSubalgebra.killingForm_inclusion_eq`: `κ_K(x, y) = κ_K'(x, y)` when `K ≤ K'` and
  `⁅K, K'⁆ ⊆ K`.
-/

public section

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [LieRing L]
  [LieAlgebra R L]

/-- **The Killing form of a subalgebra absorbing brackets with the ambient algebra** is the
restriction of the Killing form of the ambient algebra. -/
theorem killingForm_eq_of_lie_mem [Module.Free R L] [Module.Finite R L] (K : LieSubalgebra R L)
    (hK : ∀ x ∈ K, ∀ y : L, ⁅x, y⁆ ∈ K) (x y : K) :
    killingForm R K x y = killingForm R L x y := by
  have hf : ∀ z, (LieAlgebra.ad R L x ∘ₗ LieAlgebra.ad R L y) z ∈ K.toSubmodule :=
    fun z ↦ hK _ x.property _
  have hres : (LieAlgebra.ad R L x ∘ₗ LieAlgebra.ad R L y).restrict (p := K.toSubmodule)
      (q := K.toSubmodule) (fun z _ ↦ hf z) = LieAlgebra.ad R K x ∘ₗ LieAlgebra.ad R K y := by
    -- The carrier of `K.toSubmodule` is that of `K`, and the bracket of `K` is that of `L`.
    ext z
    rfl
  rw [killingForm_apply_apply, killingForm_apply_apply,
    ← LinearMap.trace_restrict_eq_of_forall_mem _ _ hf]
  exact congrArg (LinearMap.trace R K) hres

/-- **The Killing forms of nested subalgebras** `K ≤ K'` agree on `K` when `⁅K, K'⁆ ⊆ K`. -/
theorem killingForm_inclusion_eq {K K' : LieSubalgebra R L} [Module.Free R K'] [Module.Finite R K']
    (h : K ≤ K') (hK : ∀ x ∈ K, ∀ y ∈ K', ⁅x, y⁆ ∈ K) (x y : K) :
    killingForm R K x y = killingForm R K' (inclusion h x) (inclusion h y) := by
  rw [← LieAlgebra.killingForm_of_equiv_apply (equivOfLe h)]
  exact killingForm_eq_of_lie_mem (ofLe h) (fun a ha b ↦ (mem_ofLe h _).mpr <|
    hK _ ((mem_ofLe h a).mp ha) _ b.property) _ _

end LieSubalgebra

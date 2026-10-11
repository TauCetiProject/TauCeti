/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.KyFan
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# The Ky Fan and nuclear seminorms

For linear maps `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the Ky Fan
`k`-sum `A.kyFanSum k = σ₀(A) + ⋯ + σₖ₋₁(A)` of the `k` largest singular values is subadditive
(`LinearMap.kyFanSum_add_le`), absolutely homogeneous (`LinearMap.kyFanSum_smul`) and invariant
under isometric changes of coordinates. It is therefore a unitarily invariant seminorm, the
**Ky Fan `k`-seminorm**. The sum of all singular values is the **nuclear seminorm** (the trace
norm); it is the Ky Fan `k`-seminorm for every `k` at least the rank of `A`.

These are the seminorms through which Fan dominance
(`TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le`) is stated: Ky Fan domination is
domination in every Ky Fan seminorm.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm.kyFan`: the Ky Fan `k`-seminorm `A ↦ A.kyFanSum k`.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear`: the nuclear seminorm, the sum of all singular
  values.
* `TauCeti.UnitarilyInvariantSeminorm.nuclear_apply`: `N₁(A) = ∑ᵢ σᵢ(A)`.
* `LinearMap.kyFanSum_eq_nuclear`: the Ky Fan sums stabilize at the nuclear seminorm from the
  rank on.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
-/

public section

open Module

variable (𝕜 E F : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

namespace TauCeti.UnitarilyInvariantSeminorm

/-- The **Ky Fan `k`-seminorm** `A ↦ σ₀(A) + ⋯ + σₖ₋₁(A)`, the sum of the `k` largest singular
values, as a unitarily invariant seminorm. -/
noncomputable def kyFan (k : ℕ) : UnitarilyInvariantSeminorm 𝕜 E F where
  toSeminorm := .of (fun A ↦ A.kyFanSum k) (fun A B ↦ A.kyFanSum_add_le B k)
    (fun c A ↦ A.kyFanSum_smul c k)
  map_linearIsometryEquiv_comp_comp' U V A := by
    -- Mathlib has no `apply` lemma for `Seminorm.of`; its coercion is the given function by
    -- definition.
    change (_ : E →ₗ[𝕜] F).kyFanSum k = A.kyFanSum k
    simp

/-- The **nuclear seminorm** (trace norm) `A ↦ ∑ᵢ σᵢ(A)`, the sum of all singular values, as a
unitarily invariant seminorm. It is the Ky Fan `k`-seminorm for `k = finrank 𝕜 E`, beyond which
all singular values vanish. -/
noncomputable def nuclear : UnitarilyInvariantSeminorm 𝕜 E F :=
  kyFan 𝕜 E F (finrank 𝕜 E)

variable {𝕜 E F}

/-- The `k`-th Ky Fan seminorm evaluates to the sum `σ₀(A) + ⋯ + σₖ₋₁(A)` of the `k` largest
singular values. -/
@[simp]
theorem kyFan_apply (k : ℕ) (A : E →ₗ[𝕜] F) : kyFan 𝕜 E F k A = A.kyFanSum k :=
  (rfl)

/-- The nuclear seminorm is the sum of all singular values. -/
@[simp]
theorem nuclear_apply (A : E →ₗ[𝕜] F) : nuclear 𝕜 E F A = A.singularValues.sum fun _ s ↦ s := by
  rw [nuclear, kyFan_apply, LinearMap.kyFanSum_def, Finsupp.sum_of_support_subset _
    (A.support_singularValues ▸ Finset.range_subset_range.mpr A.finrank_range_le) _
    fun _ _ ↦ rfl]

end TauCeti.UnitarilyInvariantSeminorm

namespace LinearMap

variable {𝕜 E F}

/-- From the rank on, the Ky Fan sums are the nuclear seminorm: if `rank A ≤ k`, then
`σ₀(A) + ⋯ + σₖ₋₁(A) = ∑ᵢ σᵢ(A)`. -/
theorem kyFanSum_eq_nuclear (A : E →ₗ[𝕜] F) {k : ℕ} (hk : finrank 𝕜 (range A) ≤ k) :
    A.kyFanSum k = TauCeti.UnitarilyInvariantSeminorm.nuclear 𝕜 E F A := by
  rw [TauCeti.UnitarilyInvariantSeminorm.nuclear_apply, Finsupp.sum, support_singularValues,
    ← kyFanSum_def, ← A.kyFanSum_min_finrank_range k, min_eq_right hk]

end LinearMap

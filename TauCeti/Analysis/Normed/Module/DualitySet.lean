/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The duality set of a vector in a normed space

For a vector `x` of a normed space `E` over `𝕜 = ℝ` or `ℂ`, the **(normalized) duality set**

`J(x) = {x' ∈ E' | x' x = ‖x‖² ∧ ‖x'‖ = ‖x‖}`

collects the continuous linear functionals that realize the norm of `x` in the sharpest possible
way. The set-valued map `x ↦ J(x)` is the *duality map* of `E`. On a Hilbert space `J(x)` is the
singleton `{⟪x, ·⟫}`, and in general it is the tool through which inner-product arguments
(`⟪A x, x⟫ ≤ 0`, say) are transported to Banach spaces; the main consumer is the duality-map
characterization of dissipative operators in semigroup theory.

The Hahn--Banach theorem makes every `J(x)` nonempty (`dualitySet_nonempty`), and the norm
condition can be weakened to an inequality (`mem_dualitySet_iff_norm_le`), which is how members
are usually produced: rescale a norming functional of norm at most one (`smul_mem_dualitySet`).

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Definition II.3.13 (the duality set).
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Section 4 (the duality set `F(x)`).
-/

public section

namespace TauCeti

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **(normalized) duality set** `J(x)` of a vector `x` in a normed space: the continuous
linear functionals `x'` with `x' x = ‖x‖²` and `‖x'‖ = ‖x‖`. -/
def dualitySet (x : E) : Set (StrongDual 𝕜 E) :=
  {f | f x = (‖x‖ : 𝕜) ^ 2 ∧ ‖f‖ = ‖x‖}

variable {𝕜}

/-- Membership in the duality set unfolds to its two defining conditions. -/
@[simp]
theorem mem_dualitySet_iff {x : E} {f : StrongDual 𝕜 E} :
    f ∈ dualitySet 𝕜 x ↔ f x = (‖x‖ : 𝕜) ^ 2 ∧ ‖f‖ = ‖x‖ :=
  Iff.rfl

/-- In the definition of the duality set the norm condition may be weakened to `‖x'‖ ≤ ‖x‖`:
the reverse inequality is forced by `x' x = ‖x‖²`. -/
theorem mem_dualitySet_iff_norm_le {x : E} {f : StrongDual 𝕜 E} :
    f ∈ dualitySet 𝕜 x ↔ f x = (‖x‖ : 𝕜) ^ 2 ∧ ‖f‖ ≤ ‖x‖ := by
  refine ⟨fun h => ⟨h.1, h.2.le⟩, fun ⟨hfx, hle⟩ => ⟨hfx, le_antisymm hle ?_⟩⟩
  rcases (norm_nonneg x).eq_or_lt with hx | hx
  · rw [← hx]
    exact norm_nonneg f
  · have h := f.le_opNorm x
    rw [hfx, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at h
    exact le_of_mul_le_mul_right h hx

/-- Rescaling a norming functional: if `‖g‖ ≤ 1` and `g x = ‖x‖`, then `‖x‖ • g` lies in the
duality set of `x`. -/
theorem smul_mem_dualitySet {x : E} {g : StrongDual 𝕜 E} (hg : ‖g‖ ≤ 1)
    (hgx : g x = ‖x‖) : (‖x‖ : 𝕜) • g ∈ dualitySet 𝕜 x := by
  refine mem_dualitySet_iff_norm_le.mpr ⟨by simp [hgx, sq], ?_⟩
  rw [norm_smul, RCLike.norm_ofReal, abs_norm]
  exact mul_le_of_le_one_right (norm_nonneg x) hg

variable (𝕜) in
/-- **The duality set is nonempty**, by the Hahn--Banach theorem. -/
theorem dualitySet_nonempty (x : E) : (dualitySet 𝕜 x).Nonempty := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' 𝕜 x
  exact ⟨_, smul_mem_dualitySet hg hgx⟩

/-- The duality set of the zero vector consists of the zero functional alone. -/
@[simp]
theorem dualitySet_zero : dualitySet 𝕜 (0 : E) = {0} := by
  ext f
  simp

end TauCeti

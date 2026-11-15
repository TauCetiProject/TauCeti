/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.GeometryOfNumbers
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Minkowski's linear forms theorem

Let `n ≥ 1`, let `A` be an invertible real `n × n` matrix, read as `n` linear forms
`x ↦ ∑ⱼ Aᵢⱼ xⱼ` in `n` variables, and let `a₀, …, aₙ₋₁ ≥ 0` with `∏ᵢ aᵢ ≥ |det A|`. Minkowski's
linear forms theorem says that some nonzero integer vector `z` has `|∑ⱼ Aᵢⱼ zⱼ| ≤ aᵢ` for every
`i`. All the inequalities are non-strict, including when `∏ᵢ aᵢ = |det A|`. The hypothesis
`n ≥ 1` cannot be dropped: for `n = 0` both `det A` and `∏ᵢ aᵢ` are `1`, but the only integer
vector is zero. The theorem is the basic tool for producing small values of linear forms at
integer points, as in Dirichlet's approximation theorem.

The region `{x | ∀ i, |(A *ᵥ x) i| ≤ aᵢ}` is compact, convex and symmetric about the origin, and
has volume `2 ^ n * (∏ᵢ aᵢ) / |det A| ≥ 2 ^ n` by `Matrix.volume_setOf_forall_abs_mulVec_le`.
Minkowski's convex body theorem for the integer lattice
(`MeasureTheory.exists_ne_zero_int_vec_mem_of_two_pow_le_volume`) gives the integer point.

## Main results

* `Matrix.exists_ne_zero_int_abs_sum_mul_le`: Minkowski's linear forms theorem, for a matrix
  indexed by a nonempty finite type.

## References

* J.-H. Evertse, *Diophantine approximation, Chapter 2: Geometry of numbers*, §2.2,
  Corollary 2.6 and its proof, printed p.20:
  <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public section

open MeasureTheory Set

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Minkowski's linear forms theorem.** Let `A` be an invertible real square matrix indexed by
a nonempty finite type `ι`, and let `a i ≥ 0` be bounds whose product is at least `|det A|`. Then
some nonzero integer vector `z` satisfies `|∑ j, A i j * z j| ≤ a i` for every `i`. -/
theorem exists_ne_zero_int_abs_sum_mul_le [Nonempty ι] (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    {a : ι → ℝ} (ha : 0 ≤ a) (h : |A.det| ≤ ∏ i, a i) :
    ∃ z : ι → ℤ, z ≠ 0 ∧ ∀ i, |∑ j, A i j * z j| ≤ a i := by
  set S := {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| ≤ a i}
  have hS : S = toLin' A ⁻¹' Icc (-a) a := by
    ext x
    simp [S, abs_le, Pi.le_def, forall_and]
  have hsymm : ∀ x ∈ S, -x ∈ S := fun x hx i ↦ by simpa [mulVec_neg] using hx i
  have hconv : Convex ℝ S := hS ▸ (convex_Icc _ _).linear_preimage (toLin' A)
  -- `A` is invertible, so `S` is the preimage of a compact box under a homeomorphism.
  have hcpt : IsCompact S := hS ▸
    (((toLin' A).equivOfDetNeZero (by rwa [LinearMap.det_toLin'])).toContinuousLinearEquiv
      |>.toHomeomorph.isCompact_preimage).2 isCompact_Icc
  have hvol : 2 ^ Fintype.card ι ≤ volume S := by
    rw [A.volume_setOf_forall_abs_mulVec_le hA ha, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_pow zero_le_two]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (abs_pos.2 hA)]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  obtain ⟨z, hz0, hzS⟩ := exists_ne_zero_int_vec_mem_of_two_pow_le_volume hsymm hconv hcpt hvol
  exact ⟨z, hz0, fun i ↦ by simpa only [mulVec_apply_eq_sum] using hzS i⟩

end Matrix

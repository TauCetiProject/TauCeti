/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Operator.OrthogonalSum
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The zero-compression projection averaging estimate

Let `P i` be pairwise orthogonal orthogonal projections and `T i` bounded operators of
norm at most `C`. If `(1 - P i) * T i * (1 - P i) = 0`, then
`‖∑ i ∈ s, T i‖ ≤ 2 * √s.card * C`. Consequently their average has norm at most
`2 * C / √s.card`. The empty average is zero. The operators `T i` need not be self-adjoint.

This is the Hilbert-space estimate used in Powers averaging for reduced group C⋆-algebras.
The two summands in `T i = P i * T i + (1 - P i) * T i * P i` have, respectively,
orthogonal ranges and orthogonal adjoint ranges. The projections may be arbitrary
bounded operators satisfying the projection laws; they need not lie in the C⋆-algebra
being averaged.

## References

Pierre de la Harpe, *On simplicity of reduced C⋆-algebras of groups*,
arXiv:math/0509450, proof of Theorem 14, pp. 10–11. Here the projection estimate is
stated for arbitrary bounded operators, rather than only conjugates of one operator.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 H ι : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Left multiplication by mutually orthogonal projections makes a uniformly bounded
operator family have a sum bounded by `√s.card * C`. -/
theorem norm_sum_mul_le_sqrt_card_mul_of_isStarProjection
    (P T : ι → H →L[𝕜] H) (s : Finset ι)
    (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : (s : Set ι).Pairwise fun i j ↦ P i * P j = 0)
    {C : ℝ} (hbound : ∀ i ∈ s, ‖T i‖ ≤ C) :
    ‖∑ i ∈ s, P i * T i‖ ≤ Real.sqrt s.card * C := by
  apply norm_sum_le_sqrt_card_mul_of_orthogonal
  · intro i hi j hj hij x y
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← adjoint_inner_right,
      ← star_eq_adjoint, (hP i hi).isSelfAdjoint.star_eq, ← mul_apply_eq_comp,
      horth hi hj hij]
    simp
  · intro i hi
    calc ‖P i * T i‖ ≤ ‖P i‖ * ‖T i‖ := norm_mul_le _ _
      _ ≤ 1 * ‖T i‖ := mul_le_mul_of_nonneg_right ((hP i hi).norm_le _) (norm_nonneg _)
      _ ≤ C := by simpa using hbound i hi

/-- **The Powers projection estimate.** A family of operators whose compressions to the
complements of mutually orthogonal projections vanish has sum of norm at most
`2 * √s.card * C`. There is no self-adjointness hypothesis on `T`. -/
theorem norm_sum_le_two_mul_sqrt_card_mul_of_compression_eq_zero
    (P T : ι → H →L[𝕜] H) (s : Finset ι)
    (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : (s : Set ι).Pairwise fun i j ↦ P i * P j = 0)
    (hzero : ∀ i ∈ s, (1 - P i) * T i * (1 - P i) = 0)
    {C : ℝ} (hbound : ∀ i ∈ s, ‖T i‖ ≤ C) :
    ‖∑ i ∈ s, T i‖ ≤ 2 * Real.sqrt s.card * C := by
  have hleft := norm_sum_mul_le_sqrt_card_mul_of_isStarProjection P T s hP horth hbound
  have hright : ‖∑ i ∈ s, (1 - P i) * T i * P i‖ ≤ Real.sqrt s.card * C := by
    have hstar : star (∑ i ∈ s, (1 - P i) * T i * P i) =
        ∑ i ∈ s, P i * (star (T i) * (1 - P i)) := by
      simp only [star_sum, star_mul, star_sub, star_one]
      exact Finset.sum_congr rfl fun i hi ↦ by rw [(hP i hi).isSelfAdjoint.star_eq]
    rw [← norm_star, hstar]
    apply norm_sum_mul_le_sqrt_card_mul_of_isStarProjection P
      (fun i ↦ star (T i) * (1 - P i)) s hP horth
    intro i hi
    calc ‖star (T i) * (1 - P i)‖ ≤ ‖star (T i)‖ * ‖1 - P i‖ := norm_mul_le _ _
      _ ≤ ‖star (T i)‖ * 1 :=
        mul_le_mul_of_nonneg_left ((hP i hi).one_sub.norm_le _) (norm_nonneg _)
      _ ≤ C := by rw [mul_one, norm_star (T i)]; exact hbound i hi
  have hdecomp : ∑ i ∈ s, T i =
      (∑ i ∈ s, P i * T i) + ∑ i ∈ s, (1 - P i) * T i * P i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hz := hzero i hi
    rw [mul_sub, mul_one, sub_eq_zero] at hz
    calc T i = P i * T i + (1 - P i) * T i := by noncomm_ring
      _ = P i * T i + (1 - P i) * T i * P i := by rw [← hz]
  rw [hdecomp]
  exact (norm_add_le _ _).trans (by nlinarith)

/-- Averaging `N` operators with the zero-compression property gives the bound
`2 * C / √N`. For the empty family both sides are zero. -/
theorem norm_average_le_two_mul_div_sqrt_card_of_compression_eq_zero
    (P T : ι → H →L[𝕜] H) (s : Finset ι)
    (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : (s : Set ι).Pairwise fun i j ↦ P i * P j = 0)
    (hzero : ∀ i ∈ s, (1 - P i) * T i * (1 - P i) = 0)
    {C : ℝ} (hbound : ∀ i ∈ s, ‖T i‖ ≤ C) :
    ‖(s.card : 𝕜)⁻¹ • ∑ i ∈ s, T i‖ ≤ 2 * C / Real.sqrt s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hsq := Real.sq_sqrt hc.le
  have hpos := Real.sqrt_pos.mpr hc
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  calc (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, T i‖
      ≤ (s.card : ℝ)⁻¹ * (2 * Real.sqrt s.card * C) :=
        mul_le_mul_of_nonneg_left
          (norm_sum_le_two_mul_sqrt_card_mul_of_compression_eq_zero P T s hP horth hzero hbound)
          (inv_nonneg.mpr hc.le)
    _ = 2 * C / Real.sqrt s.card := by
      field_simp [ne_of_gt hc, ne_of_gt hpos]
      nlinarith only [congrArg (fun a : ℝ ↦ a * C) hsq]

/-- A unitary-conjugate average satisfies the Powers bound whenever its compressions
to the complements of mutually orthogonal projections vanish. In particular the
bound applies to non-self-adjoint operators. -/
theorem norm_average_unitary_conj_le_two_mul_div_sqrt_card_of_compression_eq_zero
    (x : H →L[𝕜] H) (U : ι → unitary (H →L[𝕜] H))
    (P : ι → H →L[𝕜] H) (s : Finset ι)
    (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : (s : Set ι).Pairwise fun i j ↦ P i * P j = 0)
    (hzero : ∀ i ∈ s,
      (1 - P i) * ((U i : H →L[𝕜] H) * x * star (U i : H →L[𝕜] H)) * (1 - P i) = 0) :
    ‖(s.card : 𝕜)⁻¹ • ∑ i ∈ s, (U i : H →L[𝕜] H) * x * star (U i : H →L[𝕜] H)‖ ≤
      2 * ‖x‖ / Real.sqrt s.card := by
  apply norm_average_le_two_mul_div_sqrt_card_of_compression_eq_zero P
    (fun i ↦ (U i : H →L[𝕜] H) * x * star (U i : H →L[𝕜] H)) s hP horth hzero
  intro i _
  exact le_of_eq (by
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul])

end ContinuousLinearMap

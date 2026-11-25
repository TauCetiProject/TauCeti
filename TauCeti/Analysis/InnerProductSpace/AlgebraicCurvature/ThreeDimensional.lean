/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Cone
public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Reaction.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Fin.Tuple.Reflection
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Extension
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.Basic

/-!
# Algebraic curvature tensors in dimension three

On a three-dimensional real inner product space `V`, the curvature operator
`R = curvatureEndomorphism r` of a pair-antisymmetric four-tensor `r` and its Ricci contraction
determine each other's positivity. The space of bivectors `⋀² V` is three-dimensional, and every
plane in it is `e ∧ V` for a unit vector `e`: for the unit normal `ω₃` of the plane, the skew map
`u ↦ u ⌟ ω₃` of the odd-dimensional space `V` has a kernel, and a unit `e` in it makes `e ∧ V`
orthogonal to `ω₃`. In an orthonormal basis `e, b₁, b₂` the trace of `R` on `e ∧ V` is
`r(e, b₁, e, b₁) + r(e, b₂, e, b₂) = Ric(e, e)`. Hence the sums `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫` over
orthonormal pairs of bivectors are exactly the values `Ric(e, e)` on unit vectors. So the curvature
operator is 2-nonnegative exactly when the Ricci contraction is nonnegative, and 2-positive exactly
when it is positive definite. In particular the 2-nonnegative cone and the nonnegative-Ricci cone
coincide in dimension three.

The second result is the dimension-three identity. An orthonormal basis `b` of `V` gives the
orthonormal basis `b 1 ∧ b 2`, `b 2 ∧ b 0`, `b 0 ∧ b 1` of `⋀² V`, and in it the curvature
operator of a bivector-symmetric four-tensor has the matrix

`⟪R (b (i + 1) ∧ b (i + 2)), b (j + 1) ∧ b (j + 2)⟫ = (Scal / 2) δᵢⱼ - Ric(b i, b j)`,

so `R` is determined by the Ricci contraction. When `b` diagonalizes `Ric` with eigenvalues
`ρ₀, ρ₁, ρ₂`, the operator is diagonal with eigenvalues `(Scal / 2) - ρᵢ`.

The third result is Hamilton's computation of the reaction term on the boundary of the
nonnegative-Ricci cone. For an algebraic curvature tensor `r` and an orthonormal basis
`b₀, b₁, b₂` with `Ric(b₀, b₀) = 0`,

`Ric(Q(r))(b₀, b₀) = (Ric(b₁, b₁) - Ric(b₂, b₂))² + 4 Ric(b₁, b₂)²`,

where `Q = reactionTensor`. So `Ric(Q(r))(e, e) ≥ 0` at every null vector `e` of the Ricci
contraction. For a tensor with nonnegative Ricci curvature these null vectors are where it meets
the boundary of the nonnegative-Ricci cone, so this is the boundary inequality on which the
invariance of that cone under the reaction equation `R' = Q(R)`, and of nonnegative Ricci curvature
under the three-dimensional Ricci flow, rests.

## Main results

All in the namespace `TauCeti.FourTensor`:

* `IsBivectorSymmetric.inner_curvatureEndomorphism_ιMulti_two_add_one_add_two`: the matrix of the
  curvature operator in the bivector basis of an orthonormal basis is `(Scal / 2) I - Ric`.
* `exists_norm_eq_one_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm` and
  `exists_orthonormal_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm`: the sums over
  orthonormal pairs of bivectors are the Ricci curvatures of unit vectors.
* `forall_inner_curvatureEndomorphism_add_inner_nonneg_iff_forall_ricci_nonneg_of_antisymm` and
  `forall_inner_curvatureEndomorphism_add_inner_pos_iff_forall_ricci_pos_of_antisymm`:
  2-nonnegativity and 2-positivity of the curvature operator in terms of the Ricci contraction.
* `twoNonnegCurvatureOperatorCone_eq_nonnegRicciCone`: the two cones agree.
* `IsAlgebraicCurvature.ricci_reactionTensor_apply_self_of_ricci_apply_self_eq_zero` and
  `IsAlgebraicCurvature.ricci_reactionTensor_apply_self_nonneg_of_ricci_apply_self_eq_zero`:
  Hamilton's formula and inequality for the reaction term at a null vector of the Ricci
  contraction.

## References

* R. S. Hamilton, *Three-manifolds with positive Ricci curvature*, J. Differential Geom. 17
  (1982), 255–306.
* R. S. Hamilton, *Four-manifolds with positive curvature operator*, J. Differential Geom. 24
  (1986), 153–179.
* P. Topping, *Lectures on the Ricci flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Chapter 9.
-/

public section

open Module
open scoped RealInnerProductSpace

noncomputable section

namespace TauCeti.FourTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The curvature operator in a bivector basis -/

/-- **The dimension-three identity.** For a bivector-symmetric four-tensor `r` on a space with an
orthonormal basis `b` indexed by `Fin 3`, the matrix of the curvature operator in the orthonormal
bivector basis `b 1 ∧ b 2, b 2 ∧ b 0, b 0 ∧ b 1` (see
`OrthonormalBasis.orthonormal_ιMulti_two_add_one_add_two`) is `(Scal / 2) I - Ric`:
`⟪R (b (i + 1) ∧ b (i + 2)), b (j + 1) ∧ b (j + 2)⟫ = (Scal / 2) ⟪b i, b j⟫ - Ric(b i, b j)`. -/
theorem IsBivectorSymmetric.inner_curvatureEndomorphism_ιMulti_two_add_one_add_two
    {r : FourTensor V} (hr : IsBivectorSymmetric r) (b : OrthonormalBasis (Fin 3) ℝ V)
    (i j : Fin 3) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![b (i + 1), b (i + 2)]),
        exteriorPower.ιMulti ℝ 2 ![b (j + 1), b (j + 2)]⟫ =
      scalar r / 2 * ⟪b i, b j⟫ - ricci r (b i) (b j) := by
  have h₁ (x z w : V) : r ![x, x, z, w] = 0 :=
    CharZero.eq_neg_self_iff.mp (hr.antisymm_first x x z w)
  have h₂ (u v z : V) : r ![u, v, z, z] = 0 :=
    CharZero.eq_neg_self_iff.mp (hr.antisymm_last u v z z)
  rw [hr.inner_curvatureEndomorphism_ιMulti, scalar_apply_orthonormalBasis b,
    ricci_apply_orthonormalBasis b, b.inner_eq_ite]
  -- After expanding the traces, each of the nine entries is a linear identity between the
  -- components `r(b p, b q, b s, b t)`, closed by the pair symmetries listed below: the first six
  -- identify the sectional components `r(b p, b q, b p, b q)` with their transposes, the remaining
  -- ones match the off-diagonal entries with the mixed Ricci components.
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, h₁, h₂] <;>
    linarith [hr.antisymm_first (b 0) (b 1) (b 0) (b 1), hr.antisymm_first (b 0) (b 2) (b 0) (b 2),
      hr.antisymm_first (b 1) (b 2) (b 1) (b 2), hr.antisymm_last (b 1) (b 0) (b 0) (b 1),
      hr.antisymm_last (b 2) (b 0) (b 0) (b 2), hr.antisymm_last (b 2) (b 1) (b 1) (b 2),
      hr.swap_pairs (b 1) (b 2) (b 2) (b 0), hr.antisymm_last (b 2) (b 0) (b 1) (b 2),
      hr.swap_pairs (b 1) (b 2) (b 0) (b 1), hr.antisymm_first (b 0) (b 1) (b 1) (b 2),
      hr.swap_pairs (b 2) (b 1) (b 2) (b 0), hr.antisymm_last (b 2) (b 0) (b 2) (b 1),
      hr.swap_pairs (b 2) (b 0) (b 0) (b 1), hr.antisymm_last (b 0) (b 1) (b 2) (b 0),
      hr.swap_pairs (b 1) (b 2) (b 1) (b 0), hr.antisymm_first (b 1) (b 0) (b 1) (b 2),
      hr.swap_pairs (b 0) (b 2) (b 0) (b 1)]

/-! ### Ricci curvature and pairs of bivectors -/

omit [FiniteDimensional ℝ V] in
/-- The vectors of an orthonormal basis indexed by `Fin 3`, listed as `![b 0, b 1, b 2]`, are
orthonormal. -/
private theorem orthonormal_vecCons_orthonormalBasis (b : OrthonormalBasis (Fin 3) ℝ V) :
    Orthonormal ℝ ![b 0, b 1, b 2] := by
  have h := b.orthonormal
  -- `FinVec.etaExpand ⇑b` unfolds to `![b 0, b 1, b 2]`.
  rwa [← FinVec.etaExpand_eq ⇑b] at h

/-- In an orthonormal basis `b₀, b₁, b₂` of a three-dimensional space, the Ricci curvature of `b₀`
is the sum of the values of the curvature operator on `b₀ ∧ b₁` and `b₀ ∧ b₂`. -/
private theorem inner_add_inner_eq_ricci_of_antisymm {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) (b : OrthonormalBasis (Fin 3) ℝ V) :
    ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![b 0, b 1]),
        exteriorPower.ιMulti ℝ 2 ![b 0, b 1]⟫ +
      ⟪curvatureEndomorphism r (exteriorPower.ιMulti ℝ 2 ![b 0, b 2]),
        exteriorPower.ιMulti ℝ 2 ![b 0, b 2]⟫ = ricci r (b 0) (b 0) := by
  have hself : r ![b 0, b 0, b 0, b 0] = 0 := by linarith [h₁ (b 0) (b 0) (b 0) (b 0)]
  have hswap (j : Fin 3) : r ![b j, b 0, b j, b 0] = r ![b 0, b j, b 0, b j] := by
    rw [h₁, h₂, neg_neg]
  rw [ricci_apply_orthonormalBasis b, Fin.sum_univ_three, hself, hswap 1, hswap 2,
    inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂,
    inner_curvatureEndomorphism_ιMulti_of_antisymm h₁ h₂, zero_add]

/-- In dimension three, the Ricci curvature `Ric(e, e)` of every unit vector `e` is the sum
`⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫` of the curvature operator over some orthonormal pair of bivectors. -/
theorem exists_orthonormal_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm
    (hV : finrank ℝ V = 3) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) {e : V} (he : ‖e‖ = 1) :
    ∃ ω₁ ω₂ : ⋀[ℝ]^2 V, Orthonormal ℝ ![ω₁, ω₂] ∧
      ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫ = ricci r e e := by
  obtain ⟨b, rfl⟩ := exists_orthonormalBasis_fin_apply_zero_eq (n := 2) hV he
  exact ⟨_, _, exteriorPower.orthonormal_ιMulti_two_of_orthonormal
    (orthonormal_vecCons_orthonormalBasis b), inner_add_inner_eq_ricci_of_antisymm h₁ h₂ b⟩

/-- In dimension three, the sum `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫` of the curvature operator over an
orthonormal pair of bivectors is the Ricci curvature `Ric(e, e)` of some unit vector `e`. -/
theorem exists_norm_eq_one_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm
    (hV : finrank ℝ V = 3) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) {ω₁ ω₂ : ⋀[ℝ]^2 V}
    (hω : Orthonormal ℝ ![ω₁, ω₂]) :
    ∃ e : V, ‖e‖ = 1 ∧
      ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫ = ricci r e e := by
  classical
  -- The trace of `R` is the sum of its diagonal values on any orthonormal triple of bivectors.
  have h₃ : finrank ℝ (⋀[ℝ]^2 V) = Fintype.card (Fin 3) := by
    rw [exteriorPower.finrank_eq, hV]; rfl
  have htrace {x y z : ⋀[ℝ]^2 V} (h : Orthonormal ℝ ![x, y, z]) :
      LinearMap.trace ℝ _ (curvatureEndomorphism r) = ⟪curvatureEndomorphism r x, x⟫ +
        ⟪curvatureEndomorphism r y, y⟫ + ⟪curvatureEndomorphism r z, z⟫ := by
    let B := (basisOfOrthonormalOfCardEqFinrank h h₃.symm).toOrthonormalBasis
      (by rwa [coe_basisOfOrthonormalOfCardEqFinrank])
    rw [LinearMap.trace_eq_sum_inner _ B, Fin.sum_univ_three]
    simp [B, real_inner_comm]
  -- A unit bivector `ω₃` orthogonal to `ω₁` and `ω₂`.
  obtain ⟨ω₃, hω₃, hω₃o⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    ({ω₁, ω₂} : Finset (⋀[ℝ]^2 V)) (by rw [h₃]; exact Finset.card_le_two.trans_lt (by simp))
  -- The skew map `u ↦ u ⌟ ω₃` of the odd-dimensional space `V` kills some unit vector, which
  -- starts an orthonormal basis `b` of `V`; then `b₀ ∧ b₁` and `b₀ ∧ b₂` are orthogonal to `ω₃`.
  obtain ⟨u, hu₀, hu⟩ := exists_ne_zero_apply_eq_zero_of_skew_of_odd_finrank
    (f := twoVectorContraction ω₃) (inner_twoVectorContraction_apply_left _) (by rw [hV]; decide)
  obtain ⟨b, hbu⟩ := exists_orthonormalBasis_fin_apply_zero_eq (n := 2) hV
    (show ‖‖u‖⁻¹ • u‖ = 1 by simpa using norm_smul_inv_norm (𝕜 := ℝ) hu₀)
  have hb₃ : twoVectorContraction ω₃ (b 0) = 0 := by simp [hbu, hu]
  have hperp (j : Fin 3) : ⟪ω₃, exteriorPower.ιMulti ℝ 2 ![b 0, b j]⟫ = 0 := by
    rw [← inner_twoVectorContraction_apply, hb₃, inner_zero_left]
  -- Computing the trace of `R` in the orthonormal triples `ω₃, ω₁, ω₂` and
  -- `ω₃, b₀ ∧ b₁, b₀ ∧ b₂`, the common term `⟪R ω₃, ω₃⟫` cancels.
  have h₁₂ : Orthonormal ℝ ![ω₃, ω₁, ω₂] := by
    refine orthonormal_vecCons_iff.mpr ⟨hω₃, fun i ↦ ?_, hω⟩
    rw [real_inner_comm]
    fin_cases i <;> exact hω₃o _ (by simp)
  have h₀ : Orthonormal ℝ ![ω₃, exteriorPower.ιMulti ℝ 2 ![b 0, b 1],
      exteriorPower.ιMulti ℝ 2 ![b 0, b 2]] :=
    orthonormal_vecCons_iff.mpr ⟨hω₃, fun i ↦ by fin_cases i <;> exact hperp _,
      exteriorPower.orthonormal_ιMulti_two_of_orthonormal
        (orthonormal_vecCons_orthonormalBasis b)⟩
  have htr := (htrace h₁₂).symm.trans (htrace h₀)
  refine ⟨b 0, b.orthonormal.1 0, ?_⟩
  rw [← inner_add_inner_eq_ricci_of_antisymm h₁ h₂ b]
  linarith

/-! ### 2-nonnegativity and 2-positivity -/

/-- In dimension three, the curvature operator of a pair-antisymmetric four-tensor is
2-nonnegative, `⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ ≥ 0` for every orthonormal pair of bivectors, exactly
when its Ricci contraction is nonnegative. -/
theorem forall_inner_curvatureEndomorphism_add_inner_nonneg_iff_forall_ricci_nonneg_of_antisymm
    (hV : finrank ℝ V = 3) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    (∀ ω₁ ω₂ : ⋀[ℝ]^2 V, Orthonormal ℝ ![ω₁, ω₂] →
      0 ≤ ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫) ↔
      ∀ u : V, 0 ≤ ricci r u u := by
  refine ⟨fun h u ↦ ?_, fun h ω₁ ω₂ hω ↦ ?_⟩
  · rcases eq_or_ne u 0 with rfl | hu
    · simp
    obtain ⟨ω₁, ω₂, hω, he⟩ :=
      exists_orthonormal_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm hV h₁ h₂
        (show ‖‖u‖⁻¹ • u‖ = 1 by simpa using norm_smul_inv_norm (𝕜 := ℝ) hu)
    rw [ricci_apply_self_eq_norm_sq_mul r u, ← he]
    exact mul_nonneg (sq_nonneg _) (h ω₁ ω₂ hω)
  · obtain ⟨e, -, he⟩ :=
      exists_norm_eq_one_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm hV h₁ h₂ hω
    exact he ▸ h e

/-- In dimension three, the curvature operator of a pair-antisymmetric four-tensor is 2-positive,
`⟪R ω₁, ω₁⟫ + ⟪R ω₂, ω₂⟫ > 0` for every orthonormal pair of bivectors, exactly when its Ricci
contraction is positive definite. -/
theorem forall_inner_curvatureEndomorphism_add_inner_pos_iff_forall_ricci_pos_of_antisymm
    (hV : finrank ℝ V = 3) {r : FourTensor V}
    (h₁ : ∀ u v z w, r ![u, v, z, w] = -r ![v, u, z, w])
    (h₂ : ∀ u v z w, r ![u, v, z, w] = -r ![u, v, w, z]) :
    (∀ ω₁ ω₂ : ⋀[ℝ]^2 V, Orthonormal ℝ ![ω₁, ω₂] →
      0 < ⟪curvatureEndomorphism r ω₁, ω₁⟫ + ⟪curvatureEndomorphism r ω₂, ω₂⟫) ↔
      ∀ u : V, u ≠ 0 → 0 < ricci r u u := by
  refine ⟨fun h u hu ↦ ?_, fun h ω₁ ω₂ hω ↦ ?_⟩
  · obtain ⟨ω₁, ω₂, hω, he⟩ :=
      exists_orthonormal_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm hV h₁ h₂
        (show ‖‖u‖⁻¹ • u‖ = 1 by simpa using norm_smul_inv_norm (𝕜 := ℝ) hu)
    rw [ricci_apply_self_eq_norm_sq_mul r u, ← he]
    exact mul_pos (pow_pos (norm_pos_iff.mpr hu) 2) (h ω₁ ω₂ hω)
  · obtain ⟨e, he₁, he⟩ :=
      exists_norm_eq_one_inner_curvatureEndomorphism_add_inner_eq_ricci_of_antisymm hV h₁ h₂ hω
    exact he ▸ h e (norm_ne_zero_iff.mp (he₁.trans_ne one_ne_zero))

/-- In dimension three, an algebraic curvature tensor has 2-nonnegative curvature operator exactly
when it has nonnegative Ricci curvature. -/
theorem twoNonnegCurvatureOperatorCone_eq_nonnegRicciCone (hV : finrank ℝ V = 3) :
    twoNonnegCurvatureOperatorCone V = nonnegRicciCone V := by
  ext r
  have hR := mem_algebraicCurvatureSubmodule.mp r.property
  rw [mem_twoNonnegCurvatureOperatorCone, mem_nonnegRicciCone,
    forall_inner_curvatureEndomorphism_add_inner_nonneg_iff_forall_ricci_nonneg_of_antisymm hV
      hR.antisymm_first hR.antisymm_last]

/-! ### The reaction term at a null vector of the Ricci contraction -/

/-- **Hamilton's formula.** For an algebraic curvature tensor `r` and an orthonormal basis
`b₀, b₁, b₂` of a three-dimensional space with `Ric(b₀, b₀) = 0`, the Ricci contraction of the
reaction term `Q(r)` at `b₀` is
`Ric(Q(r))(b₀, b₀) = (Ric(b₁, b₁) - Ric(b₂, b₂))² + 4 Ric(b₁, b₂)²`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor_apply_self_of_ricci_apply_self_eq_zero
    {r : FourTensor V} (hr : IsAlgebraicCurvature r) (b : OrthonormalBasis (Fin 3) ℝ V)
    (h₀ : ricci r (b 0) (b 0) = 0) :
    ricci (FourTensor.reactionTensor r) (b 0) (b 0) =
      (ricci r (b 1) (b 1) - ricci r (b 2) (b 2)) ^ 2 + 4 * ricci r (b 1) (b 2) ^ 2 := by
  have hz₁ (x z w : V) : r ![x, x, z, w] = 0 := by linarith [hr.antisymm_first x x z w]
  have hz₂ (u v x : V) : r ![u, v, x, x] = 0 := by linarith [hr.antisymm_last u v x x]
  -- Expand every Ricci value into the components `r(bᵢ, bⱼ, bₖ, bₗ)` and bring these to the
  -- three sectional components `r(bᵢ, bⱼ, bᵢ, bⱼ)`, `i < j`, and `r(b₀, b₁, b₀, b₂)`.
  rw [hr.ricci_reactionTensor_apply_orthonormalBasis b]
  simp only [ricci_apply_orthonormalBasis b, Fin.sum_univ_three, hz₁, hz₂] at h₀ ⊢
  rw [hr.swap_first_last (b 1) (b 0) (b 1) (b 0), hr.swap_first_last (b 2) (b 0) (b 2) (b 0),
    hr.swap_first_last (b 1) (b 0) (b 2) (b 0), hr.swap_first_last (b 2) (b 0) (b 1) (b 0),
    hr.swap_first_last (b 2) (b 1) (b 2) (b 1), hr.swap_pairs (b 0) (b 2) (b 0) (b 1)] at *
  linear_combination (r ![b 0, b 1, b 0, b 1] + r ![b 0, b 2, b 0, b 2] +
    2 * r ![b 1, b 2, b 1, b 2]) * h₀

/-- **Hamilton's inequality.** In dimension three, at every null vector `e` of the Ricci
contraction of an algebraic curvature tensor `r`, the reaction term has nonnegative Ricci
curvature: `Ric(Q(r))(e, e) ≥ 0`. -/
theorem IsAlgebraicCurvature.ricci_reactionTensor_apply_self_nonneg_of_ricci_apply_self_eq_zero
    (hV : finrank ℝ V = 3) {r : FourTensor V} (hr : IsAlgebraicCurvature r) {e : V}
    (he : ricci r e e = 0) : 0 ≤ ricci (FourTensor.reactionTensor r) e e := by
  rcases eq_or_ne e 0 with rfl | he₀
  · simp
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_fin_apply_zero_eq (n := 2) hV
    (show ‖‖e‖⁻¹ • e‖ = 1 by simpa using norm_smul_inv_norm (𝕜 := ℝ) he₀)
  have hb₀ : ricci r (b 0) (b 0) = 0 := by
    rw [ricci_apply_self_eq_norm_sq_mul r e] at he
    rw [hb]
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 (norm_ne_zero_iff.mpr he₀))
  rw [ricci_apply_self_eq_norm_sq_mul _ e, ← hb,
    hr.ricci_reactionTensor_apply_self_of_ricci_apply_self_eq_zero b hb₀]
  positivity

end TauCeti.FourTensor

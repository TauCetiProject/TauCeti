/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum

/-!
# Ordered-pair contractions on the exterior square

For an orthonormal basis `b`, the wedges `b i ∧ b j` indexed by all ordered pairs form a
redundant family: each increasing pair occurs twice, with opposite signs, and diagonal wedges
vanish. Consequently their rank-one operators sum to twice the identity on `Λ² E`.

This gives a trace formula using all ordered pairs instead of the increasing pairs indexing
Mathlib's `OrthonormalBasis.exteriorPower`. It applies to arbitrary endomorphisms, without a
self-adjointness assumption, and fixes the factor of two in curvature contractions.

Evaluated on a two-vector, the same identity gives its coordinates over all ordered pairs,
`∑ₚ ∑_q ⟪x, bₚ ∧ b_q⟫ • (bₚ ∧ b_q) = 2 • x` (`OrthonormalBasis.sum_sum_inner_smul_ιMulti_two`),
and the inner product `∑ₚ ∑_q ⟪x, bₚ ∧ b_q⟫ ⟪y, bₚ ∧ b_q⟫ = 2 ⟪x, y⟫`
(`OrthonormalBasis.sum_sum_inner_ιMulti_two_mul_inner_ιMulti_two`). Through the skew endomorphism
`A_X = TauCeti.twoVectorContraction X`, the latter says that the inner product of `⋀² E` is the
trace form `-½ tr (A_X A_Y)` of the orthogonal Lie algebra
(`TauCeti.trace_twoVectorContraction_mul_twoVectorContraction`).
-/

public section

open scoped RealInnerProductSpace
open Finset

noncomputable section

namespace OrthonormalBasis

open exteriorPower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- The rank-one operators associated to all ordered wedges of an orthonormal basis sum to
twice the identity on the exterior square. -/
theorem sum_rankOne_ιMulti_two (b : OrthonormalBasis ι ℝ E) :
    (∑ i, ∑ j, (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![b i, b j])
      (ιMulti ℝ 2 ![b i, b j])).toLinearMap) = (2 : ℝ) • LinearMap.id := by
  classical
  apply linearMap_ext_inner_ιMulti_two
  intro a c u v
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, sum_inner, real_inner_smul_left,
    LinearMap.smul_apply, LinearMap.id_apply, inner_ιMulti_two]
  have hp (x y : E) : (∑ i, ⟪b i, x⟫ * ⟪b i, y⟫) = ⟪x, y⟫ := by
    simpa only [real_inner_comm x] using b.sum_inner_mul_inner x y
  -- Expand the two Gram determinants and contract each factor by Parseval.
  simp_rw [sub_mul, mul_sub, sum_sub_distrib]
  simp_rw [mul_mul_mul_comm (⟪b _, _⟫) (⟪b _, _⟫) (⟪b _, _⟫) (⟪b _, _⟫)]
  simp_rw [← mul_sum, hp, ← sum_mul, hp]
  ring

/-- The sum of the diagonal coefficients of an endomorphism against all ordered basis wedges
is twice its trace. In contrast, the increasing wedges form an orthonormal basis and count
each diagonal coefficient once. -/
theorem sum_inner_ιMulti_two_eq_two_mul_trace (b : OrthonormalBasis ι ℝ E)
    (T : Module.End ℝ (⋀[ℝ]^2 E)) :
    (∑ i, ∑ j, ⟪T (ιMulti ℝ 2 ![b i, b j]), ιMulti ℝ 2 ![b i, b j]⟫) =
      2 * LinearMap.trace ℝ (⋀[ℝ]^2 E) T := by
  classical
  have h := congrArg (fun S : Module.End ℝ (⋀[ℝ]^2 E) ↦
    LinearMap.trace ℝ (⋀[ℝ]^2 E) (T ∘ₗ S)) (sum_rankOne_ιMulti_two b)
  have hc : T ∘ₗ (∑ i, ∑ j,
        (InnerProductSpace.rankOne ℝ (ιMulti ℝ 2 ![b i, b j])
          (ιMulti ℝ 2 ![b i, b j])).toLinearMap) =
      ∑ i, ∑ j, (InnerProductSpace.rankOne ℝ (T (ιMulti ℝ 2 ![b i, b j]))
        (ιMulti ℝ 2 ![b i, b j])).toLinearMap := by
    ext y
    simp
  rw [hc] at h
  simpa only [map_sum, InnerProductSpace.trace_rankOne,
    LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul,
    real_inner_comm] using h

/-- **Coordinates of a two-vector over all ordered pairs.** For an orthonormal basis `b` of `E`,
`∑ₚ ∑_q ⟪x, bₚ ∧ b_q⟫ • (bₚ ∧ b_q) = 2 • x`: each unordered pair `{p, q}` contributes twice. -/
theorem sum_sum_inner_smul_ιMulti_two (b : OrthonormalBasis ι ℝ E) (x : ⋀[ℝ]^2 E) :
    ∑ p, ∑ q, ⟪x, ιMulti ℝ 2 ![b p, b q]⟫ • ιMulti ℝ 2 ![b p, b q] = (2 : ℝ) • x := by
  simpa [LinearMap.sum_apply, InnerProductSpace.rankOne_apply, real_inner_comm] using
    LinearMap.congr_fun b.sum_rankOne_ιMulti_two x

/-- **The inner product of two-vectors in coordinates over all ordered pairs.** For an orthonormal
basis `b` of `E`, `∑ₚ ∑_q ⟪x, bₚ ∧ b_q⟫ ⟪y, bₚ ∧ b_q⟫ = 2 ⟪x, y⟫`. -/
theorem sum_sum_inner_ιMulti_two_mul_inner_ιMulti_two (b : OrthonormalBasis ι ℝ E)
    (x y : ⋀[ℝ]^2 E) :
    ∑ p, ∑ q, ⟪x, ιMulti ℝ 2 ![b p, b q]⟫ * ⟪y, ιMulti ℝ 2 ![b p, b q]⟫ = 2 * ⟪x, y⟫ := by
  have h := congrArg (⟪·, y⟫) (b.sum_sum_inner_smul_ιMulti_two x)
  simp only [sum_inner, real_inner_smul_left] at h
  rw [← h]
  simp only [real_inner_comm _ y]

end OrthonormalBasis

namespace TauCeti

open exteriorPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The inner product of bivectors is the trace form of `so(V)`**:
`tr (A_X A_Y) = -2 ⟪X, Y⟫`, that is `⟪X, Y⟫ = -½ tr (A_X A_Y)`. -/
theorem trace_twoVectorContraction_mul_twoVectorContraction (X Y : ⋀[ℝ]^2 V) :
    LinearMap.trace ℝ V (twoVectorContraction X * twoVectorContraction Y) = -2 * ⟪X, Y⟫ := by
  let b := stdOrthonormalBasis ℝ V
  have h := b.sum_sum_inner_ιMulti_two_mul_inner_ιMulti_two X Y
  simp only [← inner_twoVectorContraction_apply, b.real_sum_inner_mul_inner] at h
  have hp (p) : ⟪b p, (twoVectorContraction X * twoVectorContraction Y) (b p)⟫ =
      -⟪twoVectorContraction X (b p), twoVectorContraction Y (b p)⟫ := by
    rw [mul_apply_eq_comp, inner_twoVectorContraction_apply_left X (b p), neg_neg]
  rw [LinearMap.trace_eq_sum_inner _ b]
  simp only [hp, Finset.sum_neg_distrib, h]
  ring

end TauCeti

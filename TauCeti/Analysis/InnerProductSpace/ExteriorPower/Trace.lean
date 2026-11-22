/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BilinearForm.End
public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Ordered-pair contractions on the exterior square

For an orthonormal basis `b`, the wedges `b i ∧ b j` indexed by all ordered pairs form a
redundant family: each increasing pair occurs twice, with opposite signs, and diagonal wedges
vanish. Consequently their rank-one operators sum to twice the identity on `Λ² E`.

This gives trace formulas using all ordered pairs instead of the increasing pairs indexing
Mathlib's `OrthonormalBasis.exteriorPower`, both for arbitrary endomorphisms (`LinearMap.trace`)
and for bilinear forms (`TauCeti.bilinFormTrace`), fixing the factor of two in curvature
contractions.
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

/-- Every bivector equals half the sum of its inner products against all ordered basis wedges
`b i ∧ b j`. -/
theorem sum_inner_smul_ιMulti_two (b : OrthonormalBasis ι ℝ E) (η : ⋀[ℝ]^2 E) :
    (∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], η⟫ • ιMulti ℝ 2 ![b i, b j]) = (2 : ℝ) • η := by
  simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
    LinearMap.congr_fun b.sum_rankOne_ιMulti_two η

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

/-- The sum of the diagonal values of a bilinear form on `⋀² E` against all ordered basis wedges
is twice its metric trace. -/
theorem sum_bilinForm_ιMulti_two (b : OrthonormalBasis ι ℝ E)
    (B : LinearMap.BilinForm ℝ (⋀[ℝ]^2 E)) :
    (∑ i, ∑ j, B (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) =
      2 * TauCeti.bilinFormTrace B := by
  simp_rw [← B.inner_bilinFormToEnd_left]
  rw [b.sum_inner_ιMulti_two_eq_two_mul_trace, B.trace_bilinFormToEnd]

end OrthonormalBasis

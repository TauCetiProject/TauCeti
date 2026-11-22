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

This gives trace and double-contraction formulas using all ordered pairs instead of the increasing
pairs indexing Mathlib's `OrthonormalBasis.exteriorPower`, both for arbitrary endomorphisms
(`LinearMap.trace`) and for bilinear forms (`TauCeti.bilinFormTrace`), as well as bilinear maps
(`OrthonormalBasis.sum_inner_mul_inner_smul_ιMulti_two`), fixing the factor of two in curvature
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
      (ιMulti ℝ 2 ![b i, b j])).toLinearMap) = (2 : ℝ) • LinearMap.id :=
  LinearMap.ext fun η ↦ by
    simpa only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply, LinearMap.smul_apply, LinearMap.id_apply] using
      b.sum_inner_smul_ιMulti_two η

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
theorem sum_bilinForm_ιMulti_two_eq_two_mul_bilinFormTrace (b : OrthonormalBasis ι ℝ E)
    (B : LinearMap.BilinForm ℝ (⋀[ℝ]^2 E)) :
    (∑ i, ∑ j, B (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b i, b j])) =
      2 * TauCeti.bilinFormTrace B := by
  simp_rw [← B.inner_bilinFormToEnd_left]
  rw [b.sum_inner_ιMulti_two_eq_two_mul_trace, B.trace_bilinFormToEnd]

/-- Contracting two linear functionals on `⋀² E` against an orthonormal basis `e` of `⋀² E`
equals half the sum of their products over all ordered wedges `b i ∧ b j` of an orthonormal basis
`b` of `E`. -/
theorem sum_apply_mul_eq_half_sum_ιMulti {ι' : Type*} [Fintype ι']
    (e : OrthonormalBasis ι' ℝ (⋀[ℝ]^2 E)) (b : OrthonormalBasis ι ℝ E)
    (f g : ⋀[ℝ]^2 E →ₗ[ℝ] ℝ) :
    (∑ α, f (e α) * g (e α)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, f (ιMulti ℝ 2 ![b i, b j]) * g (ιMulti ℝ 2 ![b i, b j]) := by
  have h2 := b.sum_bilinForm_ιMulti_two_eq_two_mul_bilinFormTrace ((LinearMap.mul ℝ ℝ).compl₁₂ f g)
  rw [TauCeti.bilinFormTrace_eq_sum _ e] at h2
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at h2
  rw [h2]
  ring

/-- Contracting a bilinear map `Φ` on `⋀² E` against all pairs of ordered basis wedges of an
orthonormal basis `b` scales `Φ x y` by `4`. -/
theorem sum_inner_mul_inner_smul_ιMulti_two {M : Type*} [AddCommGroup M] [Module ℝ M]
    (b : OrthonormalBasis ι ℝ E) (Φ : ⋀[ℝ]^2 E →ₗ[ℝ] ⋀[ℝ]^2 E →ₗ[ℝ] M) (x y : ⋀[ℝ]^2 E) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫) •
        Φ (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l])) =
      (4 : ℝ) • Φ x y := by
  have h :
      Φ (∑ i, ∑ j, ⟪ιMulti ℝ 2 ![b i, b j], x⟫ • ιMulti ℝ 2 ![b i, b j])
        (∑ k, ∑ l, ⟪ιMulti ℝ 2 ![b k, b l], y⟫ • ιMulti ℝ 2 ![b k, b l]) =
      ∑ i, ∑ j, ∑ k, ∑ l,
        (⟪ιMulti ℝ 2 ![b i, b j], x⟫ * ⟪ιMulti ℝ 2 ![b k, b l], y⟫) •
          Φ (ιMulti ℝ 2 ![b i, b j]) (ιMulti ℝ 2 ![b k, b l]) := by
    set Y := ∑ k, ∑ l, ⟪ιMulti ℝ 2 ![b k, b l], y⟫ • ιMulti ℝ 2 ![b k, b l]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Y, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [← h, b.sum_inner_smul_ιMulti_two, b.sum_inner_smul_ιMulti_two]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  norm_num

end OrthonormalBasis

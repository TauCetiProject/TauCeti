/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Normed.Lp.Weak
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import TauCeti.Analysis.InnerProductSpace.Gram.Factor
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Factoring finite families under weak quadratic domination

If every continuous linear functional has smaller squared coefficient sum on `x` than on `y`,
the coefficient map for `x` factors through that for `y` by a Euclidean contraction. Taking
the adjoint gives the corresponding identity between vector-valued finite sums. This is the
finite-dimensional factorization used in Gaussian comparison.

We also record `ContinuousLinearMap.weakTwo_dom_of_orthonormalBasis`, which dominates the weak-`ℓ²`
evaluations of `U ∘ x` under a bounded operator `U : E →L[𝕜] Y` from a finite-dimensional inner
product space by the scaled basis images `(W • U (b i), W • (I • U (b i)))ᵢ`.

The argument follows G. Pisier, *Factorization of Linear Operators and Geometry of Banach
Spaces*, §3, Lemma 3.5, using `ContinuousLinearMap.factorThru` for the contraction.
-/

public section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace TauCeti

variable {ι κ Y : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Weak quadratic domination of finite families gives a Euclidean contraction whose adjoint
transports the synthesis map for `y` to the synthesis map for `x`. No completeness assumption
on the ambient normed space is needed. -/
theorem exists_contraction_of_weakTwo_le (x : ι → Y) (y : κ → Y)
    (h : ∀ f : StrongDual ℝ Y, ∑ i, |f (x i)| ^ 2 ≤ ∑ j, |f (y j)| ^ 2) :
    ∃ D : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι, ‖D‖ ≤ 1 ∧
      ∀ a : EuclideanSpace ℝ ι, (∑ i, a i • x i) = ∑ j, (D.adjoint a) j • y j := by
  let T : StrongDual ℝ Y →L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ ℝ)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.apply ℝ ℝ (x i))
  let A : StrongDual ℝ Y →L[ℝ] EuclideanSpace ℝ κ :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ ↦ ℝ)).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun j ↦ ContinuousLinearMap.apply ℝ ℝ (y j))
  have hbound (f : StrongDual ℝ Y) : ‖T f‖ ≤ 1 * ‖A f‖ := by
    rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simpa [T, A, Real.norm_eq_abs] using h f
  refine ⟨T.factorThru A, ContinuousLinearMap.norm_factorThru_le zero_le_one hbound, ?_⟩
  intro a
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro f
  have hf := ContinuousLinearMap.factorThru_apply_apply ⟨1, hbound⟩ f
  have hadj := (T.factorThru A).adjoint_inner_left (A f) a
  rw [hf] at hadj
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, T, A, map_sum,
    mul_comm] using hadj.symm

end TauCeti

namespace ContinuousLinearMap

open TauCeti

/-- Every real continuous linear functional on `Y` is weakly square-dominated on `U ∘ x` by the
scaled basis image `(W • U (b i), W • (I • U (b i)))ᵢ`, where `W = weakLpNorm 2 x`. -/
theorem weakTwo_dom_of_orthonormalBasis {𝕜 ι κ E Y : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    (U : E →L[𝕜] Y) (b : OrthonormalBasis ι 𝕜 E) (x : κ → E) (f : StrongDual ℝ Y) :
    ∑ j, |f (U (x j))| ^ 2 ≤
      ∑ k, |f (Sum.elim (fun i ↦ weakLpNorm (𝕜 := 𝕜) 2 x • (U ∘ b) i)
        (fun i ↦ weakLpNorm (𝕜 := 𝕜) 2 x • ((RCLike.I : 𝕜) • (U ∘ b) i)) k)| ^ 2 := by
  set W := weakLpNorm (𝕜 := 𝕜) 2 x
  have hW : 0 ≤ W := apply_nonneg _ _
  let g : StrongDual 𝕜 Y := f.extendRCLike (𝕜 := 𝕜)
  have hre (v : Y) : |f v| ^ 2 ≤ ‖g v‖ ^ 2 := by
    rw [← f.re_extendRCLike_apply (𝕜 := 𝕜) v]
    exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
  have hnorm (v : Y) : ‖g v‖ ^ 2 = |f v| ^ 2 + |f ((RCLike.I : 𝕜) • v)| ^ 2 := by
    rw [RCLike.norm_sq_eq_def, f.re_extendRCLike_apply, f.im_extendRCLike_apply]
    simp [pow_two]
  have hweak := sum_norm_eval_rpow_le_weakLpNorm (𝕜 := 𝕜) 2 (by simp) x (g.comp U)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, comp_apply] at hweak
  calc
    ∑ j, |f (U (x j))| ^ 2 ≤ ∑ j, ‖g (U (x j))‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ hre _
    _ ≤ (W * ‖g.comp U‖) ^ 2 := hweak
    _ = W ^ 2 * ∑ i, ‖g (U (b i))‖ ^ 2 := by
      rw [mul_pow, ← b.sum_sq_norm_apply_eq_norm_sq (g.comp U)]
      simp_rw [ContinuousLinearMap.comp_apply]
    _ = ∑ k, |f (Sum.elim (fun i ↦ W • (U ∘ b) i)
          (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i)) k)| ^ 2 := by
      simp_rw [hnorm, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply,
        map_smul, smul_eq_mul, abs_mul, mul_pow, abs_of_nonneg hW, ← Finset.mul_sum,
        Finset.sum_add_distrib, mul_add]

end ContinuousLinearMap

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.LinearAlgebra.Dimension.LinearMap
import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# The `ℓ^p` product: coordinate bounds and components of indicators

Mathlib bounds each factor of `WithLp p (α × β)` by the whole (`WithLp.norm_fst_le` and
`WithLp.norm_snd_le`) and computes the norm exactly for `p = 1` and `p = 2`.  This file records
the opposite bound, valid for every exponent `1 ≤ p ≤ ∞`: the `ℓ^p` norm of a pair is at most the
sum of the norms of its two components.  For `p = 1` the bound is an identity for every pair.

It also records that taking a component of `WithLp p (α × β)` commutes with `Set.indicator`, as
Mathlib's `norm_indicator_eq_indicator_norm` does for the norm.

Finally, it bundles the componentwise action of two continuous linear maps `f` and `g` on
`WithLp p (α × β)` as a continuous linear map `f.withLpProdMap p g`, the continuous counterpart of
Mathlib's `LinearIsometry.withLpProdMap`. For `p = 2` and inner product spaces this is the
orthogonal block sum `f ⊕ g`. Its rank is the sum of the ranks of `f` and `g`, and for `p = 2` its
operator norm is the larger of the two operator norms.

## Main statements

* `WithLp.prod_norm_le_norm_fst_add_norm_snd` — the bound `‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖`.
* `TauCeti.snd_lt_one` — a unit vector in `E × ℝ` other than `(0, 1)` has last coordinate
  strictly less than `1`.
* `WithLp.fst_indicator`, `WithLp.snd_indicator` — a component of an indicator is the indicator
  of the component.
* `ContinuousLinearMap.withLpProdMap` — the block sum `f ⊕ g` on `WithLp p (α × β)`.
* `ContinuousLinearMap.rank_withLpProdMap` — `rank (f ⊕ g) = rank f + rank g`.
* `ContinuousLinearMap.norm_withLpProdMap` — `‖f ⊕ g‖ = max ‖f‖ ‖g‖` for `p = 2`.
-/

public section

open scoped ENNReal NNReal

universe u v

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {α β : Type*} [SeminormedAddCommGroup α]
  [SeminormedAddCommGroup β]

/-- The `ℓ^p` norm of a pair is at most the sum of the norms of its two components. -/
theorem _root_.WithLp.prod_norm_le_norm_fst_add_norm_snd (x : WithLp p (α × β)) :
    ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ :=
  calc ‖x‖ = ‖WithLp.idemFst x + WithLp.idemSnd x‖ :=
        congrArg norm ((DFunLike.congr_fun WithLp.idemFst_add_idemSnd x).trans
          (AddMonoid.End.one_apply x)).symm
    _ ≤ ‖WithLp.idemFst x‖ + ‖WithLp.idemSnd x‖ := norm_add_le _ _
    _ = ‖x.fst‖ + ‖x.snd‖ := by
        rw [WithLp.idemFst_apply, WithLp.idemSnd_apply, WithLp.norm_toLp_fst,
          WithLp.norm_toLp_snd]

section Real

variable {E : Type*} [NormedAddCommGroup E]

/-- A unit vector of `E × ℝ` other than the vertical one `(0, 1)` has height less than `1`. -/
theorem snd_lt_one {u : WithLp 2 (E × ℝ)} (hnorm : ‖u‖ = 1)
    (hu : u ≠ WithLp.toLp 2 (0, 1)) : u.snd < 1 := by
  have hle : u.snd ≤ 1 := (le_abs_self _).trans ((WithLp.norm_snd_le (x := u)).trans hnorm.le)
  refine hle.lt_of_ne fun h ↦ hu ((WithLp.ext_iff 2).2 (Prod.ext ?_ (by simpa using h)))
  have hsq := WithLp.prod_norm_sq_eq_of_L2 u
  rw [hnorm, h] at hsq
  simpa using hsq

end Real

section Indicator

variable {p : ℝ≥0∞} {ι α β : Type*} [AddCommGroup α] [AddCommGroup β] {s : Set ι}

/-- The first component of an indicator function is the indicator of the first components. -/
theorem _root_.WithLp.fst_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).fst = s.indicator (fun y => (f y).fst) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.fst) WithLp.zero_fst) x).symm

/-- The second component of an indicator function is the indicator of the second components. -/
theorem _root_.WithLp.snd_indicator (f : ι → WithLp p (α × β)) (x : ι) :
    (s.indicator f x).snd = s.indicator (fun y => (f y).snd) x :=
  (congr_fun (Set.indicator_comp_of_zero (g := WithLp.snd) WithLp.zero_snd) x).symm

end Indicator

end TauCeti

namespace ContinuousLinearMap

section Topological

variable (p : ℝ≥0∞) {𝕜 α β α' β' : Type*} [Semiring 𝕜]
  [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
  [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
  [TopologicalSpace α'] [AddCommGroup α'] [Module 𝕜 α']
  [TopologicalSpace β'] [AddCommGroup β'] [Module 𝕜 β']

/-- The `L^p` product of two continuous linear maps: the block sum `f ⊕ g`, acting componentwise
on `WithLp p (α × β)`. -/
def withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    WithLp p (α × β) →L[𝕜] WithLp p (α' × β') :=
  (WithLp.prodContinuousLinearEquiv p 𝕜 α' β').symm.toContinuousLinearMap ∘L f.prodMap g ∘L
    (WithLp.prodContinuousLinearEquiv p 𝕜 α β).toContinuousLinearMap

variable {p}

@[simp]
theorem withLpProdMap_apply (f : α →L[𝕜] α') (g : β →L[𝕜] β') (x : WithLp p (α × β)) :
    f.withLpProdMap p g x = WithLp.toLp p (f x.fst, g x.snd) :=
  (rfl)

@[simp]
theorem coe_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    (f.withLpProdMap p g : WithLp p (α × β) →ₗ[𝕜] WithLp p (α' × β')) =
      ((f : α →ₗ[𝕜] α').prodMap (g : β →ₗ[𝕜] β')).withLpMap p :=
  (rfl)

end Topological

/-- The rank of a block sum is the sum of the ranks of the blocks. -/
theorem rank_withLpProdMap {p : ℝ≥0∞} {𝕜 α β : Type*} {α' : Type u} {β' : Type v}
    [DivisionRing 𝕜] [TopologicalSpace α] [AddCommGroup α] [Module 𝕜 α]
    [TopologicalSpace β] [AddCommGroup β] [Module 𝕜 β]
    [TopologicalSpace α'] [AddCommGroup α'] [Module 𝕜 α']
    [TopologicalSpace β'] [AddCommGroup β'] [Module 𝕜 β'] (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    (f.withLpProdMap p g).rank = Cardinal.lift.{v} f.rank + Cardinal.lift.{u} g.rank := by
  -- Conjugating by the linear equivalences `WithLp.linearEquiv` does not change the range's rank.
  rw [← LinearMap.rank_prodMap, coe_withLpProdMap, LinearMap.rank, LinearMap.withLpMap,
    LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  exact LinearEquiv.rank_map_eq _ _

section Seminormed

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 α β α' β' : Type*} [Ring 𝕜]
  [SeminormedAddCommGroup α] [Module 𝕜 α] [SeminormedAddCommGroup β] [Module 𝕜 β]
  [SeminormedAddCommGroup α'] [Module 𝕜 α'] [SeminormedAddCommGroup β'] [Module 𝕜 β']

/-- The block sum of differences is the difference of the block sums. -/
theorem withLpProdMap_sub (f f' : α →L[𝕜] α') (g g' : β →L[𝕜] β') :
    (f - f').withLpProdMap p (g - g') = f.withLpProdMap p g - f'.withLpProdMap p g' := by
  ext x
  simp [← WithLp.toLp_sub]

end Seminormed

section L2

variable {𝕜 α β α' β' : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] [SeminormedAddCommGroup β] [NormedSpace 𝕜 β]
  [SeminormedAddCommGroup α'] [NormedSpace 𝕜 α'] [SeminormedAddCommGroup β'] [NormedSpace 𝕜 β']

/-- The operator norm of an `L²` block sum is the larger of the operator norms of the blocks. -/
theorem norm_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    ‖f.withLpProdMap 2 g‖ = max ‖f‖ ‖g‖ := by
  refine le_antisymm (opNorm_le_bound _ (by positivity) fun x ↦ ?_) (max_le ?_ ?_)
  · have h₁ : ‖f x.fst‖ ^ 2 ≤ max ‖f‖ ‖g‖ ^ 2 * ‖x.fst‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((f.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))) 2
    have h₂ : ‖g x.snd‖ ^ 2 ≤ max ‖f‖ ‖g‖ ^ 2 * ‖x.snd‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((g.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))) 2
    refine le_of_sq_le_sq ?_ (by positivity)
    rw [withLpProdMap_apply, WithLp.prod_norm_sq_eq_of_L2, mul_pow, WithLp.prod_norm_sq_eq_of_L2]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    linarith
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using (f.withLpProdMap 2 g).le_opNorm (WithLp.toLp 2 (x, 0))
  · refine opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
    simpa using (f.withLpProdMap 2 g).le_opNorm (WithLp.toLp 2 (0, x))

/-- The operator norm of an `L²` block sum is the larger of the operator norms of the blocks,
stated for `‖·‖₊`. -/
theorem nnnorm_withLpProdMap (f : α →L[𝕜] α') (g : β →L[𝕜] β') :
    ‖f.withLpProdMap 2 g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  NNReal.eq <| by simpa using norm_withLpProdMap f g

end L2

end ContinuousLinearMap

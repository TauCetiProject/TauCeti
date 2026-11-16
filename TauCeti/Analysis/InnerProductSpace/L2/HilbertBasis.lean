/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.MeasureTheory.Function.Lp.Basic

/-!
# Orthogonal decompositions of Hilbert-space-valued `L²` functions

Let `(α, μ)` be a measure space, `E` an inner product space over `𝕜` (`ℝ` or `ℂ`), and
`v : ι → E` an orthonormal family or `b : HilbertBasis ι 𝕜 E` an orthonormal basis of `E`. This
file develops the mode-by-mode orthogonal decomposition of the Bochner space `L²(μ; E)`:

* For any orthonormal family `v : ι → E` (in a complete `E`), a mode series `∑ᵢ g i • v i`
  converges in `L²(μ; E)` exactly when `∑ᵢ ‖g i‖² < ∞`, has squared norm `∑ᵢ ‖g i‖²`, and
  recovers `g j` under projection along `v j`
  (`Orthonormal.summable_compLp_toSpanSingleton_iff`,
  `Orthonormal.hasSum_norm_sq_tsum_compLp_toSpanSingleton`,
  `Orthonormal.compLp_innerSL_tsum_compLp_toSpanSingleton`).
* For a Hilbert basis `b : HilbertBasis ι 𝕜 E` (which already carries completeness of `E` via
  `b.repr`), every `f ∈ L²(μ; E)` expands unconditionally as the orthogonal series
  `f = ∑ᵢ ((innerSL 𝕜 (b i)).compLp f) • b i`
  (`HilbertBasis.hasSum_compLp_toSpanSingleton_innerSL`) and satisfies the `L²`-Parseval identity
  `‖f‖² = ∑ᵢ ‖⟪b i, f ·⟫‖²_{L²}` (`HilbertBasis.hasSum_norm_sq_compLp_innerSL`).

No separability of `E`, countability of `ι`, or `σ`-finiteness of `μ` is assumed: every
`L²(μ; E)` class has a strongly measurable representative whose range is separable, so all but
countably many basis vectors are pointwise orthogonal to it everywhere.

## Main declarations

* `MeasureTheory.Lp.inner_compLp_toSpanSingleton`: the `L²` inner product of two rank-one
  functions `x ↦ f x • v` and `x ↦ g x • w` is `⟪f, g⟫ * ⟪v, w⟫`.
* `MeasureTheory.Lp.inner_compLp_toSpanSingleton_left`: adjointness of `toSpanSingleton` and
  `innerSL` on `L²`.
* `MeasureTheory.Lp.compLp_innerSL_compLp_toSpanSingleton` and
  `MeasureTheory.Lp.compLpL_innerSL_comp_compLpL_toSpanSingleton`: projecting a rank-one `Lᵖ`
  function `x ↦ f x • w` along `v` scales `f` by `⟪v, w⟫`, for any `p : ℝ≥0∞`.
* `Orthonormal.summable_compLp_toSpanSingleton_iff`,
  `Orthonormal.hasSum_norm_sq_tsum_compLp_toSpanSingleton`,
  `Orthonormal.compLp_innerSL_tsum_compLp_toSpanSingleton`: orthogonal synthesis, Pythagoras, and
  coordinate extraction in `L²(μ; E)` along any orthonormal family.
* `HilbertBasis.ext_compLp_innerSL`: an `L²(μ; E)` function is determined by its scalar
  projections along a Hilbert basis.
* `HilbertBasis.hasSum_compLp_toSpanSingleton_innerSL`: orthogonal reconstruction in `L²(μ; E)`.
* `HilbertBasis.hasSum_norm_sq_compLp_innerSL`: Parseval's identity in `L²(μ; E)`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal InnerProductSpace

section RankOne

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `L²` inner product of two rank-one functions `x ↦ f x • v` and `x ↦ g x • w` factors as
`⟪f, g⟫ * ⟪v, w⟫`. -/
@[simp]
theorem inner_compLp_toSpanSingleton (v w : E) (f g : Lp 𝕜 2 μ) :
    ⟪(toSpanSingleton 𝕜 v).compLp f, (toSpanSingleton 𝕜 w).compLp g⟫_𝕜 =
      ⟪f, g⟫_𝕜 * ⟪v, w⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [(toSpanSingleton 𝕜 v).coeFn_compLp f,
    (toSpanSingleton 𝕜 w).coeFn_compLp g] with x hfx hgx
  rw [hfx, hgx, toSpanSingleton_apply, toSpanSingleton_apply, inner_smul_left, inner_smul_right,
    RCLike.inner_apply', mul_assoc]

/-- Adjointness of rank-one embedding and scalar projection on `L²`: pairing `x ↦ g x • v` with `f`
equals pairing `g` with `x ↦ ⟪v, f x⟫`. -/
theorem inner_compLp_toSpanSingleton_left (v : E) (g : Lp 𝕜 2 μ) (f : Lp E 2 μ) :
    ⟪(toSpanSingleton 𝕜 v).compLp g, f⟫_𝕜 = ⟪g, (innerSL 𝕜 v).compLp f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(toSpanSingleton 𝕜 v).coeFn_compLp g,
    (innerSL 𝕜 v).coeFn_compLp f] with x hgx hfx
  rw [hgx, hfx, toSpanSingleton_apply, innerSL_apply_apply, inner_smul_left, RCLike.inner_apply']

/-- Projecting a rank-one `Lᵖ` function `x ↦ f x • w` along `v` scales `f` by `⟪v, w⟫`, for any
exponent `p : ℝ≥0∞`. -/
@[simp]
theorem compLp_innerSL_compLp_toSpanSingleton {p : ℝ≥0∞} (v w : E) (f : Lp 𝕜 p μ) :
    (innerSL 𝕜 v).compLp ((toSpanSingleton 𝕜 w).compLp f) = ⟪v, w⟫_𝕜 • f := by
  have hcomp : (innerSL 𝕜 v).comp (toSpanSingleton 𝕜 w) =
      ⟪v, w⟫_𝕜 • ContinuousLinearMap.id 𝕜 𝕜 := by
    ext
    simp
  rw [← ContinuousLinearMap.comp_compLp, hcomp, ContinuousLinearMap.smul_compLp,
    ContinuousLinearMap.id_compLp]

/-- Operator-level projection identity on `Lᵖ`: composing `(innerSL 𝕜 v).compLpL p μ` with
`(toSpanSingleton 𝕜 w).compLpL p μ` is scaling by `⟪v, w⟫`. -/
@[simp]
theorem compLpL_innerSL_comp_compLpL_toSpanSingleton {p : ℝ≥0∞} [Fact (1 ≤ p)] (v w : E) :
    ((innerSL 𝕜 v).compLpL p μ).comp ((toSpanSingleton 𝕜 w).compLpL p μ) =
      ⟪v, w⟫_𝕜 • ContinuousLinearMap.id 𝕜 (Lp 𝕜 p μ) := by
  ext1 f
  exact compLp_innerSL_compLp_toSpanSingleton v w f

end MeasureTheory.Lp

end RankOne

namespace Orthonormal

variable {α ι 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct modes along an orthonormal family are orthogonal in `L²(μ; E)`. -/
theorem pairwise_inner_compLp_toSpanSingleton {v : ι → E} (hv : Orthonormal 𝕜 v)
    (g : ι → Lp 𝕜 2 μ) :
    Pairwise fun i j ↦
      ⟪(toSpanSingleton 𝕜 (v i)).compLp (g i), (toSpanSingleton 𝕜 (v j)).compLp (g j)⟫_𝕜 = 0 :=
  fun i j hij ↦ by
    dsimp only
    rw [Lp.inner_compLp_toSpanSingleton, hv.2 hij, mul_zero]

section CompleteSpace

variable [CompleteSpace E]

/-- **Orthogonal synthesis in `L²(μ; E)`.** Along an orthonormal family `v`, a mode series
`∑ᵢ g i • v i` converges in `L²(μ; E)` exactly when the squared `L²` norms `‖g i‖²` are
summable. -/
theorem summable_compLp_toSpanSingleton_iff {v : ι → E} (hv : Orthonormal 𝕜 v)
    (g : ι → Lp 𝕜 2 μ) :
    Summable (fun i ↦ (toSpanSingleton 𝕜 (v i)).compLp (g i)) ↔
      Summable (fun i ↦ ‖g i‖ ^ 2) := by
  let w : ι → Lp E 2 μ := fun i ↦ (toSpanSingleton 𝕜 (v i)).compLp (g i)
  have hw : OrthogonalFamily 𝕜 (fun i ↦ 𝕜 ∙ w i) (fun i ↦ (𝕜 ∙ w i).subtypeₗᵢ) :=
    TauCeti.orthogonalFamily_span_singleton_iff.mpr (hv.pairwise_inner_compLp_toSpanSingleton g)
  have hnorm : ∀ i, ‖(⟨w i, Submodule.mem_span_singleton_self (w i)⟩ : 𝕜 ∙ w i)‖ = ‖g i‖ :=
    fun i ↦ by simp [w, hv.1 i]
  have hiff := hw.summable_iff_norm_sq_summable
    (fun i ↦ (⟨w i, Submodule.mem_span_singleton_self (w i)⟩ : 𝕜 ∙ w i))
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, hnorm] using hiff

/-- **Pythagoras for an orthogonal synthesis in `L²(μ; E)`.** If `∑ᵢ ‖g i‖² < ∞`, the squared norm
of `∑' i, g i • v i` along an orthonormal family `v` is `∑' i, ‖g i‖²`. -/
theorem hasSum_norm_sq_tsum_compLp_toSpanSingleton {v : ι → E} (hv : Orthonormal 𝕜 v)
    {g : ι → Lp 𝕜 2 μ} (hg : Summable fun i ↦ ‖g i‖ ^ 2) :
    HasSum (fun i ↦ ‖g i‖ ^ 2) (‖∑' i, (toSpanSingleton 𝕜 (v i)).compLp (g i)‖ ^ 2) := by
  have hsum := ((hv.summable_compLp_toSpanSingleton_iff g).mpr hg).hasSum
  have h := TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
    (hv.pairwise_inner_compLp_toSpanSingleton g) hsum
  simpa only [ContinuousLinearMap.norm_compLp_toSpanSingleton, hv.1, mul_one] using h

/-- **Coordinate extraction for an orthogonal synthesis in `L²(μ; E)`.** Projecting
`∑' i, g i • v i` along `v j` recovers `g j`. -/
theorem compLp_innerSL_tsum_compLp_toSpanSingleton {v : ι → E} (hv : Orthonormal 𝕜 v)
    {g : ι → Lp 𝕜 2 μ} (hg : Summable fun i ↦ ‖g i‖ ^ 2) (j : ι) :
    (innerSL 𝕜 (v j)).compLp (∑' i, (toSpanSingleton 𝕜 (v i)).compLp (g i)) = g j := by
  have hsum := ((innerSL 𝕜 (v j)).compLpL 2 μ).hasSum
    ((hv.summable_compLp_toSpanSingleton_iff g).mpr hg).hasSum
  have hv1 : ⟪v j, v j⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv.1 j]
    simp
  have hsingle : HasSum (fun i ↦ (innerSL 𝕜 (v j)).compLp
      ((toSpanSingleton 𝕜 (v i)).compLp (g i))) (g j) := by
    have h0 := hasSum_single (f := fun i ↦ (innerSL 𝕜 (v j)).compLp
      ((toSpanSingleton 𝕜 (v i)).compLp (g i))) j fun i hij ↦ by
      rw [Lp.compLp_innerSL_compLp_toSpanSingleton, hv.2 hij.symm, zero_smul]
    rwa [Lp.compLp_innerSL_compLp_toSpanSingleton, hv1, one_smul] at h0
  exact hsum.unique hsingle

end CompleteSpace

end Orthonormal

namespace HilbertBasis

variable {α ι 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct modes along a Hilbert basis are orthogonal in `L²(μ; E)`. -/
theorem pairwise_inner_compLp_toSpanSingleton (b : HilbertBasis ι 𝕜 E) (g : ι → Lp 𝕜 2 μ) :
    Pairwise fun i j ↦
      ⟪(toSpanSingleton 𝕜 (b i)).compLp (g i), (toSpanSingleton 𝕜 (b j)).compLp (g j)⟫_𝕜 = 0 :=
  b.orthonormal.pairwise_inner_compLp_toSpanSingleton g

/-- **Extensionality by Hilbert-basis projections in `L²(μ; E)`.** Two `L²(μ; E)` functions whose
scalar projections along every element of a Hilbert basis agree are equal. No separability of `E`
or countability of `ι` is required. -/
theorem ext_compLp_innerSL (b : HilbertBasis ι 𝕜 E) {f g : Lp E 2 μ}
    (h : ∀ i, (innerSL 𝕜 (b i)).compLp f = (innerSL 𝕜 (b i)).compLp g) : f = g := by
  suffices h0 : f - g = 0 from sub_eq_zero.mp h0
  set r : Lp E 2 μ := f - g
  have hr : ∀ i, (innerSL 𝕜 (b i)).compLp r = 0 := fun i ↦ by
    rw [← ContinuousLinearMap.compLpL_apply (p := 2) (μ := μ), map_sub]
    exact sub_eq_zero.2 (h i)
  -- Replace `r` by a strongly measurable representative `φ`, whose range is separable.
  have hmeas := Lp.aestronglyMeasurable r
  set φ : α → E := hmeas.mk r
  have hφ : StronglyMeasurable φ := hmeas.stronglyMeasurable_mk
  have hrφ : r =ᵐ[μ] φ := hmeas.ae_eq_mk
  obtain ⟨D, hDcount, hDrange⟩ := hφ.isSeparable_range
  -- Only countably many basis vectors pair nontrivially with the countable dense set `D`.
  let S : Set ι := ⋃ y ∈ D, Function.support fun i ↦ ‖⟪b i, y⟫_𝕜‖ ^ 2
  have hScount : S.Countable :=
    hDcount.biUnion fun y _ ↦ (b.summable_norm_sq_inner y).countable_support
  -- Every basis vector outside `S` is orthogonal to the entire range of `φ`.
  have hout : ∀ i ∉ S, ∀ x, ⟪b i, φ x⟫_𝕜 = 0 := by
    intro i hi x
    have hD0 : ∀ y ∈ D, ⟪b i, y⟫_𝕜 = 0 := by
      intro y hy
      by_contra hne
      exact hi (Set.mem_biUnion hy (by simp [hne]))
    have hcl : Set.range φ ⊆ {y : E | ⟪b i, y⟫_𝕜 = 0} :=
      hDrange.trans <| closure_minimal (fun y hy ↦ hD0 y hy)
        (isClosed_eq (innerSL 𝕜 (b i)).continuous continuous_const)
    exact hcl ⟨x, rfl⟩
  -- For the countably many indices in `S`, the projection vanishes a.e., hence jointly a.e.
  have hin : ∀ᵐ x ∂μ, ∀ i ∈ S, ⟪b i, φ x⟫_𝕜 = 0 := by
    have : Countable S := hScount.to_subtype
    have hall : ∀ i : S, ∀ᵐ x ∂μ, ⟪b (i : ι), φ x⟫_𝕜 = 0 := fun i ↦ by
      have h0 : ⇑((innerSL 𝕜 (b (i : ι))).compLp r) =ᵐ[μ] (0 : α → 𝕜) := by
        rw [hr i]
        exact Lp.coeFn_zero 𝕜 2 μ
      filter_upwards [(innerSL 𝕜 (b (i : ι))).coeFn_compLp r, h0, hrφ] with x h1 h2 h4
      rw [← h4, ← innerSL_apply_apply 𝕜 (b (i : ι)), ← h1, h2]
      rfl
    filter_upwards [ae_all_iff.mpr hall] with x hx i hi
    exact hx ⟨i, hi⟩
  apply Lp.ext
  filter_upwards [hrφ, hin, Lp.coeFn_zero E 2 μ] with x hrx hxin h0
  rw [hrx, h0]
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, b.repr_apply_apply, Pi.zero_apply, inner_zero_right]
  by_cases hi : i ∈ S
  · exact hxin i hi
  · exact hout i hi x

/-- **Orthogonal synthesis in `L²(μ; E)`.** A mode series `∑ᵢ g i • b i` converges in `L²(μ; E)`
exactly when the squared `L²` norms `‖g i‖²` are summable. -/
theorem summable_compLp_toSpanSingleton_iff (b : HilbertBasis ι 𝕜 E) (g : ι → Lp 𝕜 2 μ) :
    Summable (fun i ↦ (toSpanSingleton 𝕜 (b i)).compLp (g i)) ↔
      Summable (fun i ↦ ‖g i‖ ^ 2) := by
  have : CompleteSpace E :=
    (b.repr.isometry.isUniformInducing.completeSpace_congr b.repr.surjective).2 inferInstance
  exact b.orthonormal.summable_compLp_toSpanSingleton_iff g

/-- **Pythagoras for an orthogonal synthesis in `L²(μ; E)`.** If `∑ᵢ ‖g i‖² < ∞`, the squared norm
of `∑' i, g i • b i` is `∑' i, ‖g i‖²`. -/
theorem hasSum_norm_sq_tsum_compLp_toSpanSingleton (b : HilbertBasis ι 𝕜 E) {g : ι → Lp 𝕜 2 μ}
    (hg : Summable fun i ↦ ‖g i‖ ^ 2) :
    HasSum (fun i ↦ ‖g i‖ ^ 2)
      (‖∑' i, (toSpanSingleton 𝕜 (b i)).compLp (g i)‖ ^ 2) := by
  have : CompleteSpace E :=
    (b.repr.isometry.isUniformInducing.completeSpace_congr b.repr.surjective).2 inferInstance
  exact b.orthonormal.hasSum_norm_sq_tsum_compLp_toSpanSingleton hg

/-- **Coordinate extraction for an orthogonal synthesis in `L²(μ; E)`.** Projecting
`∑' i, g i • b i` along `b j` recovers `g j`. -/
theorem compLp_innerSL_tsum_compLp_toSpanSingleton (b : HilbertBasis ι 𝕜 E) {g : ι → Lp 𝕜 2 μ}
    (hg : Summable fun i ↦ ‖g i‖ ^ 2) (j : ι) :
    (innerSL 𝕜 (b j)).compLp (∑' i, (toSpanSingleton 𝕜 (b i)).compLp (g i)) = g j := by
  have : CompleteSpace E :=
    (b.repr.isometry.isUniformInducing.completeSpace_congr b.repr.surjective).2 inferInstance
  exact b.orthonormal.compLp_innerSL_tsum_compLp_toSpanSingleton hg j

/-- **Orthogonal reconstruction in `L²(μ; E)`.** Every `f ∈ L²(μ; E)` is the unconditional sum of
its mode projections `x ↦ ⟪b i, f x⟫ • b i`. -/
theorem hasSum_compLp_toSpanSingleton_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ (toSpanSingleton 𝕜 (b i)).compLp ((innerSL 𝕜 (b i)).compLp f)) f := by
  let g : ι → Lp 𝕜 2 μ := fun i ↦ (innerSL 𝕜 (b i)).compLp f
  let v : ι → Lp E 2 μ := fun i ↦ (toSpanSingleton 𝕜 (b i)).compLp (g i)
  -- Bessel's inequality for finite partial sums: `f - ∑ i ∈ s, v i` is orthogonal
  -- to `∑ i ∈ s, v i`.
  have hsq : Summable fun i ↦ ‖g i‖ ^ 2 := by
    refine summable_of_sum_le (c := ‖f‖ ^ 2) (fun i ↦ sq_nonneg _) fun s ↦ ?_
    have horth : ⟪∑ i ∈ s, v i, f - ∑ i ∈ s, v i⟫_𝕜 = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      have hb1 : ⟪b i, b i⟫_𝕜 = 1 := by
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
        simp
      rw [inner_sub_right, inner_sum, Finset.sum_eq_single i
        (fun j _ hji ↦ b.pairwise_inner_compLp_toSpanSingleton g hji.symm)
        (fun hni ↦ absurd hi hni)]
      simp only [v, Lp.inner_compLp_toSpanSingleton_left,
        Lp.compLp_innerSL_compLp_toSpanSingleton, hb1, one_smul, g, sub_self]
    have hpyth : ‖f‖ ^ 2 = ‖∑ i ∈ s, v i‖ ^ 2 + ‖f - ∑ i ∈ s, v i‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (∑ i ∈ s, v i)
        (f - ∑ i ∈ s, v i) horth
      simpa only [add_sub_cancel, ← sq] using h
    have hsum_sq : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖g i‖ ^ 2 := by
      rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
        ((b.pairwise_inner_compLp_toSpanSingleton g).set_pairwise _)]
      exact Finset.sum_congr rfl fun i _ ↦ by simp [b.orthonormal.1 i]
    linarith [sq_nonneg ‖f - ∑ i ∈ s, v i‖]
  have hsum : HasSum v (∑' i, v i) := ((b.summable_compLp_toSpanSingleton_iff g).mpr hsq).hasSum
  have heq : ∑' i, v i = f := b.ext_compLp_innerSL fun j ↦
    b.compLp_innerSL_tsum_compLp_toSpanSingleton hsq j
  rwa [heq] at hsum

/-- **Parseval's identity in `L²(μ; E)`.** The squared `L²` norms of the scalar projections of `f`
along a Hilbert basis sum to `‖f‖²`. -/
theorem hasSum_norm_sq_compLp_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ ‖(innerSL 𝕜 (b i)).compLp f‖ ^ 2) (‖f‖ ^ 2) := by
  have h := TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
    (b.pairwise_inner_compLp_toSpanSingleton fun i ↦ (innerSL 𝕜 (b i)).compLp f)
    (b.hasSum_compLp_toSpanSingleton_innerSL f)
  simpa only [ContinuousLinearMap.norm_compLp_toSpanSingleton, b.orthonormal.1, mul_one] using h

end HilbertBasis

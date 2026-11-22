/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Basic
import TauCeti.Analysis.InnerProductSpace.Parseval
import TauCeti.MeasureTheory.Function.Lp.Basic
import TauCeti.MeasureTheory.Function.Lp.RankOne

/-!
# Orthogonal decompositions of Hilbert-space-valued `L²` functions

For a measure space `(α, μ)`, an inner product space `E` over `𝕜` (`ℝ` or `ℂ`), and an orthonormal
family `v : ι → E` or Hilbert basis `b : HilbertBasis ι 𝕜 E`, this file develops mode-by-mode
orthogonal decomposition in `L²(μ; E)` without separability of `E`, countability of `ι`, or
`σ`-finiteness of `μ`.

## Main declarations

* `MeasureTheory.Lp.inner_compLp_toSpanSingleton`,
  `MeasureTheory.Lp.inner_compLp_toSpanSingleton_left`: inner products and adjointness of rank-one
  functions `x ↦ f x • v` in `L²`.
* `Orthonormal.pairwise_inner_compLp_toSpanSingleton_eq_zero`,
  `Orthonormal.summable_compLp_toSpanSingleton_iff`,
  `Orthonormal.hasSum_norm_sq_tsum_compLp_toSpanSingleton`,
  `Orthonormal.compLp_innerSL_tsum_compLp_toSpanSingleton`: orthogonal synthesis, Pythagoras, and
  coordinate extraction along any orthonormal family.
* `HilbertBasis.ext_compLp_innerSL`: extensionality by Hilbert-basis projections in `L²(μ; E)`.
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

end MeasureTheory.Lp

end RankOne

namespace Orthonormal

variable {α ι 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct modes along an orthonormal family are orthogonal in `L²(μ; E)`. -/
theorem pairwise_inner_compLp_toSpanSingleton_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v)
    (g : ι → Lp 𝕜 2 μ) :
    Pairwise fun i j ↦
      ⟪(toSpanSingleton 𝕜 (v i)).compLp (g i), (toSpanSingleton 𝕜 (v j)).compLp (g j)⟫_𝕜 = 0 :=
  fun _ _ hij ↦ by dsimp only; rw [Lp.inner_compLp_toSpanSingleton, hv.2 hij, mul_zero]

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
    TauCeti.orthogonalFamily_span_singleton_iff.mpr
      (hv.pairwise_inner_compLp_toSpanSingleton_eq_zero g)
  have hnorm : ∀ i, ‖(⟨w i, Submodule.mem_span_singleton_self (w i)⟩ : 𝕜 ∙ w i)‖ = ‖g i‖ :=
    fun i ↦ by simp [w, hv.1 i]
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, hnorm] using
    hw.summable_iff_norm_sq_summable
      (fun i ↦ (⟨w i, Submodule.mem_span_singleton_self (w i)⟩ : 𝕜 ∙ w i))

/-- **Pythagoras for an orthogonal synthesis in `L²(μ; E)`.** If `∑ᵢ ‖g i‖² < ∞`, the squared norm
of `∑' i, g i • v i` along an orthonormal family `v` is `∑' i, ‖g i‖²`. -/
theorem hasSum_norm_sq_tsum_compLp_toSpanSingleton {v : ι → E} (hv : Orthonormal 𝕜 v)
    {g : ι → Lp 𝕜 2 μ} (hg : Summable fun i ↦ ‖g i‖ ^ 2) :
    HasSum (fun i ↦ ‖g i‖ ^ 2) (‖∑' i, (toSpanSingleton 𝕜 (v i)).compLp (g i)‖ ^ 2) := by
  simpa only [norm_compLp_toSpanSingleton, hv.1, mul_one] using
    TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
      (hv.pairwise_inner_compLp_toSpanSingleton_eq_zero g)
      ((hv.summable_compLp_toSpanSingleton_iff g).mpr hg).hasSum

/-- **Coordinate extraction for an orthogonal synthesis in `L²(μ; E)`.** Projecting
`∑' i, g i • v i` along `v j` recovers `g j`. -/
theorem compLp_innerSL_tsum_compLp_toSpanSingleton {v : ι → E} (hv : Orthonormal 𝕜 v)
    {g : ι → Lp 𝕜 2 μ} (hg : Summable fun i ↦ ‖g i‖ ^ 2) (j : ι) :
    (innerSL 𝕜 (v j)).compLp (∑' i, (toSpanSingleton 𝕜 (v i)).compLp (g i)) = g j := by
  have hsum := ((innerSL 𝕜 (v j)).compLpL 2 μ).hasSum
    ((hv.summable_compLp_toSpanSingleton_iff g).mpr hg).hasSum
  have h0 := hasSum_single (f := fun i ↦ (innerSL 𝕜 (v j)).compLp
    ((toSpanSingleton 𝕜 (v i)).compLp (g i))) j fun i hij ↦ by
    rw [Lp.compLp_innerSL_compLp_toSpanSingleton, hv.2 hij.symm, zero_smul]
  rw [Lp.compLp_innerSL_compLp_toSpanSingleton, inner_self_eq_norm_sq_to_K, hv.1 j] at h0
  exact hsum.unique (by simpa using h0)

end CompleteSpace

end Orthonormal

namespace HilbertBasis

variable {α ι 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Extensionality by Hilbert-basis projections in `L²(μ; E)`.** Two `L²(μ; E)` functions whose
scalar projections along every element of a Hilbert basis agree are equal. No separability of `E`
or countability of `ι` is required. -/
theorem ext_compLp_innerSL (b : HilbertBasis ι 𝕜 E) {f g : Lp E 2 μ}
    (h : ∀ i, (innerSL 𝕜 (b i)).compLp f = (innerSL 𝕜 (b i)).compLp g) : f = g := by
  suffices h0 : f - g = 0 from sub_eq_zero.mp h0
  set r : Lp E 2 μ := f - g
  have hr : ∀ i, (innerSL 𝕜 (b i)).compLp r = 0 := fun i ↦ by
    rw [← compLpL_apply (p := 2) (μ := μ), map_sub]; exact sub_eq_zero.2 (h i)
  have hmeas := Lp.aestronglyMeasurable r
  set φ : α → E := hmeas.mk r
  obtain ⟨D, hDcount, hDrange⟩ := hmeas.stronglyMeasurable_mk.isSeparable_range
  let S : Set ι := ⋃ y ∈ D, Function.support fun i ↦ ⟪b i, y⟫_𝕜
  have hScount : S.Countable :=
    hDcount.biUnion fun y _ ↦ b.orthonormal.countable_support_inner_left y
  have hout : ∀ i ∉ S, ∀ x, ⟪b i, φ x⟫_𝕜 = 0 := fun i hi x ↦
    (hDrange.trans <| closure_minimal (fun y hy ↦ by
      by_contra hne
      exact hi (Set.mem_biUnion hy hne))
      (isClosed_eq (innerSL 𝕜 (b i)).continuous continuous_const)) ⟨x, rfl⟩
  have hin : ∀ᵐ x ∂μ, ∀ i ∈ S, ⟪b i, φ x⟫_𝕜 = 0 := by
    have : Countable S := hScount.to_subtype
    have hall : ∀ i : S, ∀ᵐ x ∂μ, ⟪b (i : ι), φ x⟫_𝕜 = 0 := fun i ↦ by
      filter_upwards [(innerSL 𝕜 (b (i : ι))).coeFn_compLp r,
        hr i ▸ Lp.coeFn_zero 𝕜 2 μ, hmeas.ae_eq_mk] with x h1 h2 h4
      dsimp only [φ]
      rw [← h4, ← innerSL_apply_apply 𝕜 (b (i : ι)), ← h1, h2]; rfl
    filter_upwards [ae_all_iff.mpr hall] with x hx i hi using hx ⟨i, hi⟩
  apply Lp.ext
  filter_upwards [hmeas.ae_eq_mk, hin, Lp.coeFn_zero E 2 μ] with x hrx hxin h0
  rw [hrx, h0]
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, b.repr_apply_apply, Pi.zero_apply, inner_zero_right]
  exact (em (i ∈ S)).elim (hxin i) (fun hi ↦ hout i hi x)

/-- **Orthogonal reconstruction in `L²(μ; E)`.** Every `f ∈ L²(μ; E)` is the unconditional sum of
its mode projections `x ↦ ⟪b i, f x⟫ • b i`. -/
theorem hasSum_compLp_toSpanSingleton_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ (toSpanSingleton 𝕜 (b i)).compLp ((innerSL 𝕜 (b i)).compLp f)) f := by
  have := b.completeSpace
  let g : ι → Lp 𝕜 2 μ := fun i ↦ (innerSL 𝕜 (b i)).compLp f
  let v : ι → Lp E 2 μ := fun i ↦ (toSpanSingleton 𝕜 (b i)).compLp (g i)
  have hsq : Summable fun i ↦ ‖g i‖ ^ 2 := by
    refine summable_of_sum_le (c := ‖f‖ ^ 2) (fun _ ↦ sq_nonneg _) fun s ↦ ?_
    have hae : ∀ᵐ x ∂μ, ∑ i ∈ s, ‖g i x‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
      have hall : ∀ i : s, ∀ᵐ x ∂μ, g i x = ⟪b i, f x⟫_𝕜 := fun i ↦ by
        filter_upwards [(innerSL 𝕜 (b (i : ι))).coeFn_compLp f] with x hx
        simpa only [g, innerSL_apply_apply] using hx
      filter_upwards [ae_all_iff.mpr hall] with x hx
      calc ∑ i ∈ s, ‖g i x‖ ^ 2
          = ∑ i ∈ s, ‖⟪b i, f x⟫_𝕜‖ ^ 2 :=
            Finset.sum_congr rfl fun i hi ↦ by rw [hx ⟨i, hi⟩]
        _ ≤ ‖f x‖ ^ 2 := b.orthonormal.sum_inner_products_le (f x)
    have hint : Integrable (fun x ↦ ∑ i ∈ s, ‖g i x‖ ^ 2) μ :=
      integrable_finsetSum s fun i _ ↦ (Lp.memLp (g i)).norm.integrable_sq
    calc ∑ i ∈ s, ‖g i‖ ^ 2
        = ∑ i ∈ s, ∫ x, ‖g i x‖ ^ 2 ∂μ := by simp_rw [Lp.integral_norm_sq_eq_norm_sq]
      _ = ∫ x, ∑ i ∈ s, ‖g i x‖ ^ 2 ∂μ :=
          (integral_finsetSum s fun i _ ↦ (Lp.memLp (g i)).norm.integrable_sq).symm
      _ ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_mono_ae hint (Lp.memLp f).norm.integrable_sq hae
      _ = ‖f‖ ^ 2 := Lp.integral_norm_sq_eq_norm_sq f
  have hsum : HasSum v (∑' i, v i) :=
    ((b.orthonormal.summable_compLp_toSpanSingleton_iff g).mpr hsq).hasSum
  rwa [b.ext_compLp_innerSL fun j ↦
    b.orthonormal.compLp_innerSL_tsum_compLp_toSpanSingleton hsq j] at hsum

/-- **Parseval's identity in `L²(μ; E)`.** The squared `L²` norms of the scalar projections of `f`
along a Hilbert basis sum to `‖f‖²`. -/
theorem hasSum_norm_sq_compLp_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ ‖(innerSL 𝕜 (b i)).compLp f‖ ^ 2) (‖f‖ ^ 2) := by
  simpa only [norm_compLp_toSpanSingleton, b.orthonormal.1, mul_one] using
    TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
      (b.orthonormal.pairwise_inner_compLp_toSpanSingleton_eq_zero
        fun i ↦ (innerSL 𝕜 (b i)).compLp f)
      (b.hasSum_compLp_toSpanSingleton_innerSL f)

end HilbertBasis

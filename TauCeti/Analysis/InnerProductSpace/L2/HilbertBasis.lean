/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.InnerProductSpace.OrthogonalFamily
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Orthogonal decompositions of Hilbert-space-valued `L²` functions

Let `(α, μ)` be a measure space, `E` a Hilbert space over `𝕜` (`ℝ` or `ℂ`), and
`b : HilbertBasis ι 𝕜 E` an orthonormal basis of `E`. This file develops the mode-by-mode
orthogonal decomposition of the Bochner space `L²(μ; E)` along `b`:

* Every `f ∈ L²(μ; E)` expands unconditionally as the orthogonal series
  `f = ∑ᵢ ((innerSL 𝕜 (b i)).compLpL 2 μ f) • b i`
  (`HilbertBasis.hasSum_compLpL_toSpanSingleton_innerSL`),
* Its norm satisfies the `L²`-Parseval identity `‖f‖² = ∑ᵢ ‖⟪b i, f ·⟫‖²_{L²}`
  (`HilbertBasis.hasSum_norm_sq_compLpL_innerSL`),
* Conversely, any family `g : ι → L²(μ; 𝕜)` with `∑ᵢ ‖g i‖² < ∞` synthesizes a unique
  `f = ∑ᵢ g i • b i ∈ L²(μ; E)` with coordinates `g j` and `‖f‖² = ∑ᵢ ‖g i‖²`
  (`HilbertBasis.summable_compLpL_toSpanSingleton_iff`,
  `HilbertBasis.compLpL_innerSL_tsum_compLpL_toSpanSingleton`).

No separability of `E`, countability of `ι`, or `σ`-finiteness of `μ` is assumed: every
`L²(μ; E)` class has a strongly measurable representative whose range is separable, so all but
countably many basis vectors are pointwise orthogonal to it everywhere.

## Main declarations

* `MeasureTheory.Lp.inner_compLpL_toSpanSingleton`: the `L²` inner product of two rank-one
  functions `x ↦ f x • v` and `x ↦ g x • w` is `⟪f, g⟫ * ⟪v, w⟫`.
* `MeasureTheory.Lp.norm_compLpL_toSpanSingleton`: the `L²` norm of `x ↦ f x • v` is
  `‖f‖ * ‖v‖`.
* `MeasureTheory.Lp.inner_compLpL_toSpanSingleton_left`: adjointness of `toSpanSingleton` and
  `innerSL` on `L²`.
* `HilbertBasis.ext_compLpL_innerSL`: an `L²(μ; E)` function is determined by its scalar
  projections along a Hilbert basis.
* `HilbertBasis.summable_compLpL_toSpanSingleton_iff`: orthogonal synthesis in `L²(μ; E)`.
* `HilbertBasis.hasSum_compLpL_toSpanSingleton_innerSL`: orthogonal reconstruction in `L²(μ; E)`.
* `HilbertBasis.hasSum_norm_sq_compLpL_innerSL`: Parseval's identity in `L²(μ; E)`.
-/

public section

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace

section RankOne

namespace MeasureTheory.Lp

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The `L²` inner product of two rank-one functions `x ↦ f x • v` and `x ↦ g x • w` factors as
`⟪f, g⟫ * ⟪v, w⟫`. -/
theorem inner_compLpL_toSpanSingleton (v w : E) (f g : Lp 𝕜 2 μ) :
    ⟪(toSpanSingleton 𝕜 v).compLpL 2 μ f, (toSpanSingleton 𝕜 w).compLpL 2 μ g⟫_𝕜 =
      ⟪f, g⟫_𝕜 * ⟪v, w⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def, ← integral_mul_const]
  refine integral_congr_ae ?_
  filter_upwards [(toSpanSingleton 𝕜 v).coeFn_compLpL f,
    (toSpanSingleton 𝕜 w).coeFn_compLpL g] with x hfx hgx
  rw [hfx, hgx, toSpanSingleton_apply, toSpanSingleton_apply, inner_smul_left, inner_smul_right,
    RCLike.inner_apply', mul_assoc]

/-- The `L²` norm of `x ↦ f x • v` is `‖f‖ * ‖v‖`. -/
theorem norm_compLpL_toSpanSingleton (v : E) (f : Lp 𝕜 2 μ) :
    ‖(toSpanSingleton 𝕜 v).compLpL 2 μ f‖ = ‖f‖ * ‖v‖ := by
  have hsq : ‖(toSpanSingleton 𝕜 v).compLpL 2 μ f‖ ^ 2 = (‖f‖ * ‖v‖) ^ 2 := by
    have h := inner_compLpL_toSpanSingleton (μ := μ) v v f f
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h' : ‖(toSpanSingleton 𝕜 v).compLpL 2 μ f‖ ^ 2 = ‖f‖ ^ 2 * ‖v‖ ^ 2 := by
      exact_mod_cast h
    linarith [mul_pow ‖f‖ ‖v‖ 2]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- Adjointness of rank-one embedding and scalar projection on `L²`: pairing `x ↦ g x • v` with `f`
equals pairing `g` with `x ↦ ⟪v, f x⟫`. -/
theorem inner_compLpL_toSpanSingleton_left (v : E) (g : Lp 𝕜 2 μ) (f : Lp E 2 μ) :
    ⟪(toSpanSingleton 𝕜 v).compLpL 2 μ g, f⟫_𝕜 = ⟪g, (innerSL 𝕜 v).compLpL 2 μ f⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(toSpanSingleton 𝕜 v).coeFn_compLpL g,
    (innerSL 𝕜 v).coeFn_compLpL f] with x hgx hfx
  rw [hgx, hfx, toSpanSingleton_apply, innerSL_apply_apply, inner_smul_left, RCLike.inner_apply']

/-- Projecting a rank-one function `x ↦ f x • w` along `v` scales `f` by `⟪v, w⟫`. -/
@[simp]
theorem compLpL_innerSL_compLpL_toSpanSingleton (v w : E) (f : Lp 𝕜 2 μ) :
    (innerSL 𝕜 v).compLpL 2 μ ((toSpanSingleton 𝕜 w).compLpL 2 μ f) = ⟪v, w⟫_𝕜 • f := by
  apply Lp.ext
  filter_upwards [(innerSL 𝕜 v).coeFn_compLpL ((toSpanSingleton 𝕜 w).compLpL 2 μ f),
    (toSpanSingleton 𝕜 w).coeFn_compLpL f, Lp.coeFn_smul ⟪v, w⟫_𝕜 f] with x h1 h2 h3
  rw [h1, h2, h3, innerSL_apply_apply, toSpanSingleton_apply, Pi.smul_apply, smul_eq_mul,
    inner_smul_right, mul_comm]

end MeasureTheory.Lp

end RankOne

namespace HilbertBasis

variable {α ι 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct modes along a Hilbert basis are orthogonal in `L²(μ; E)`. -/
theorem pairwise_inner_compLpL_toSpanSingleton (b : HilbertBasis ι 𝕜 E) (g : ι → Lp 𝕜 2 μ) :
    Pairwise fun i j ↦
      ⟪(toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i),
        (toSpanSingleton 𝕜 (b j)).compLpL 2 μ (g j)⟫_𝕜 = 0 := fun i j hij ↦ by
  dsimp only
  rw [Lp.inner_compLpL_toSpanSingleton, b.orthonormal.2 hij, mul_zero]

/-- **Extensionality by Hilbert-basis projections in `L²(μ; E)`.** Two `L²(μ; E)` functions whose
scalar projections along every element of a Hilbert basis agree are equal. No separability of `E`
or countability of `ι` is required. -/
theorem ext_compLpL_innerSL (b : HilbertBasis ι 𝕜 E) {f g : Lp E 2 μ}
    (h : ∀ i, (innerSL 𝕜 (b i)).compLpL 2 μ f = (innerSL 𝕜 (b i)).compLpL 2 μ g) : f = g := by
  suffices h0 : f - g = 0 from sub_eq_zero.mp h0
  set r : Lp E 2 μ := f - g
  have hr : ∀ i, (innerSL 𝕜 (b i)).compLpL 2 μ r = 0 := fun i ↦ by
    simp only [r, map_sub, h i, sub_self]
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
      have h0 : ⇑((innerSL 𝕜 (b (i : ι))).compLpL 2 μ r) =ᵐ[μ] (0 : α → 𝕜) := by
        rw [hr i]
        exact Lp.coeFn_zero 𝕜 2 μ
      filter_upwards [(innerSL 𝕜 (b (i : ι))).coeFn_compLpL r, h0, hrφ] with x h1 h2 h4
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

section CompleteSpace

variable [CompleteSpace E]

/-- **Orthogonal synthesis in `L²(μ; E)`.** A mode series `∑ᵢ g i • b i` converges in `L²(μ; E)`
exactly when the squared `L²` norms `‖g i‖²` are summable. -/
theorem summable_compLpL_toSpanSingleton_iff (b : HilbertBasis ι 𝕜 E) (g : ι → Lp 𝕜 2 μ) :
    Summable (fun i ↦ (toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i)) ↔
      Summable (fun i ↦ ‖g i‖ ^ 2) := by
  let v : ι → Lp E 2 μ := fun i ↦ (toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i)
  have hv : OrthogonalFamily 𝕜 (fun i ↦ 𝕜 ∙ v i) (fun i ↦ (𝕜 ∙ v i).subtypeₗᵢ) :=
    TauCeti.orthogonalFamily_span_singleton_iff.mpr (b.pairwise_inner_compLpL_toSpanSingleton g)
  have hnorm : ∀ i, ‖(⟨v i, Submodule.mem_span_singleton_self (v i)⟩ : 𝕜 ∙ v i)‖ = ‖g i‖ :=
    fun i ↦ by simp [v, Lp.norm_compLpL_toSpanSingleton, b.orthonormal.1 i]
  have hiff := hv.summable_iff_norm_sq_summable
    (fun i ↦ (⟨v i, Submodule.mem_span_singleton_self (v i)⟩ : 𝕜 ∙ v i))
  simpa only [Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype, hnorm] using hiff

/-- **Pythagoras for an orthogonal synthesis in `L²(μ; E)`.** If `∑ᵢ ‖g i‖² < ∞`, the squared norm
of `∑' i, g i • b i` is `∑' i, ‖g i‖²`. -/
theorem hasSum_norm_sq_tsum_compLpL_toSpanSingleton (b : HilbertBasis ι 𝕜 E) {g : ι → Lp 𝕜 2 μ}
    (hg : Summable fun i ↦ ‖g i‖ ^ 2) :
    HasSum (fun i ↦ ‖g i‖ ^ 2)
      (‖∑' i, (toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i)‖ ^ 2) := by
  have hsum := ((b.summable_compLpL_toSpanSingleton_iff g).mpr hg).hasSum
  have h := TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
    (b.pairwise_inner_compLpL_toSpanSingleton g) hsum
  simpa only [Lp.norm_compLpL_toSpanSingleton, b.orthonormal.1, mul_one] using h

/-- **Coordinate extraction for an orthogonal synthesis in `L²(μ; E)`.** Projecting
`∑' i, g i • b i` along `b j` recovers `g j`. -/
theorem compLpL_innerSL_tsum_compLpL_toSpanSingleton (b : HilbertBasis ι 𝕜 E) {g : ι → Lp 𝕜 2 μ}
    (hg : Summable fun i ↦ ‖g i‖ ^ 2) (j : ι) :
    (innerSL 𝕜 (b j)).compLpL 2 μ (∑' i, (toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i)) = g j := by
  have hsum := ((innerSL 𝕜 (b j)).compLpL 2 μ).hasSum
    ((b.summable_compLpL_toSpanSingleton_iff g).mpr hg).hasSum
  have hb1 : ⟪b j, b j⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    simp
  have hsingle : HasSum (fun i ↦ (innerSL 𝕜 (b j)).compLpL 2 μ
      ((toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i))) (g j) := by
    have h0 := hasSum_single (f := fun i ↦ (innerSL 𝕜 (b j)).compLpL 2 μ
      ((toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i))) j fun i hij ↦ by
      rw [Lp.compLpL_innerSL_compLpL_toSpanSingleton, b.orthonormal.2 hij.symm, zero_smul]
    rwa [Lp.compLpL_innerSL_compLpL_toSpanSingleton, hb1, one_smul] at h0
  exact hsum.unique hsingle

/-- **Orthogonal reconstruction in `L²(μ; E)`.** Every `f ∈ L²(μ; E)` is the unconditional sum of
its mode projections `x ↦ ⟪b i, f x⟫ • b i`. -/
theorem hasSum_compLpL_toSpanSingleton_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ (toSpanSingleton 𝕜 (b i)).compLpL 2 μ ((innerSL 𝕜 (b i)).compLpL 2 μ f)) f := by
  let g : ι → Lp 𝕜 2 μ := fun i ↦ (innerSL 𝕜 (b i)).compLpL 2 μ f
  let v : ι → Lp E 2 μ := fun i ↦ (toSpanSingleton 𝕜 (b i)).compLpL 2 μ (g i)
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
        (fun j _ hji ↦ b.pairwise_inner_compLpL_toSpanSingleton g hji.symm)
        (fun hni ↦ absurd hi hni)]
      simp only [v, Lp.inner_compLpL_toSpanSingleton_left,
        Lp.compLpL_innerSL_compLpL_toSpanSingleton, hb1, one_smul, g, sub_self]
    have hpyth : ‖f‖ ^ 2 = ‖∑ i ∈ s, v i‖ ^ 2 + ‖f - ∑ i ∈ s, v i‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (∑ i ∈ s, v i)
        (f - ∑ i ∈ s, v i) horth
      simpa only [add_sub_cancel, ← sq] using h
    have hsum_sq : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖g i‖ ^ 2 := by
      rw [TauCeti.norm_sum_sq_eq_sum_norm_sq_of_pairwise_inner_eq_zero
        ((b.pairwise_inner_compLpL_toSpanSingleton g).set_pairwise _)]
      exact Finset.sum_congr rfl fun i _ ↦ by
        simp [Lp.norm_compLpL_toSpanSingleton, b.orthonormal.1 i]
    linarith [sq_nonneg ‖f - ∑ i ∈ s, v i‖]
  have hsum : HasSum v (∑' i, v i) := ((b.summable_compLpL_toSpanSingleton_iff g).mpr hsq).hasSum
  have heq : ∑' i, v i = f := b.ext_compLpL_innerSL fun j ↦
    b.compLpL_innerSL_tsum_compLpL_toSpanSingleton hsq j
  rwa [heq] at hsum

/-- **Parseval's identity in `L²(μ; E)`.** The squared `L²` norms of the scalar projections of `f`
along a Hilbert basis sum to `‖f‖²`. -/
theorem hasSum_norm_sq_compLpL_innerSL (b : HilbertBasis ι 𝕜 E) (f : Lp E 2 μ) :
    HasSum (fun i ↦ ‖(innerSL 𝕜 (b i)).compLpL 2 μ f‖ ^ 2) (‖f‖ ^ 2) := by
  have h := TauCeti.hasSum_norm_sq_of_pairwise_inner_eq_zero
    (b.pairwise_inner_compLpL_toSpanSingleton fun i ↦ (innerSL 𝕜 (b i)).compLpL 2 μ f)
    (b.hasSum_compLpL_toSpanSingleton_innerSL f)
  simpa only [Lp.norm_compLpL_toSpanSingleton, b.orthonormal.1, mul_one] using h

end CompleteSpace

end HilbertBasis

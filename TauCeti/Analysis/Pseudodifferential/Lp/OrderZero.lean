/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.CalderonVaillancourt
public import TauCeti.Analysis.Pseudodifferential.Lp.OffDiagonalKernel
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.StandardKernel
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Operator.Integral.Adjoint

/-!
# `Lᵖ` boundedness of uniform symbols of order zero

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold with constants independent of the position `x`
(`TauCeti.Symbol.IsUniform`), with values in operators between complex Hilbert spaces. This file
proves that for every `1 < p < ∞` its Kohn–Nirenberg quantization `Op(a)` is bounded in the `Lᵖ`
norm, `‖Op(a) u‖_p ≤ C ‖u‖_p`, and so extends to a bounded operator on `Lᵖ`. For `p = 2` this is
the Calderón–Vaillancourt theorem (`TauCeti.Symbol.exists_quantizeUniformOrderZeroLp`); for
`p ≠ 2` the operator is a Calderón–Zygmund operator.

## The argument

The Calderón–Zygmund theorem on an inner product space
(`ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow`) bounds an operator `T` on `L²` in
every `Lᵖ` norm, `1 < p < ∞`, once `T` and its adjoint are represented, off the support of their
argument, by kernels satisfying the size estimate `‖K(x, y)‖ ≤ C ‖x - y‖^(-n)` and a Hölder
smoothness estimate in the second variable. The ingredients are:

* the bounded extension `T` of `Op(a)` to `L²`, given by the Calderón–Vaillancourt theorem;
* the representation of `T f` by the off-diagonal kernel `K` of `a` away from the support of an
  `L²` function `f` with compact support (`TauCeti.Symbol.ae_apply_eq_integral_offDiagonalKernel`);
* the representation of the adjoint of `T` by the transposed kernel `(x, y) ↦ K(y, x)†`, which
  follows from that of `T` because `K` is bounded away from the diagonal
  (`ContinuousLinearMap.ae_adjoint_apply_eq_integral`);
* the size estimate of `K` and its smoothness estimates in each variable
  (`TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le`,
  `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_sub_right_le`,
  `TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_sub_left_le`); the smoothness of the
  transposed kernel in its second variable is the smoothness of `K` in its first.

## Main results

* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt`: **`Lᵖ`
  boundedness**, `‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`, for `1 < p < ∞`.
* `TauCeti.Symbol.exists_quantizeUniformOrderZeroLp_of_one_lt`: the bounded extension of `Op(a)` to
  `Lᵖ`, for `1 < p < ∞`.

## References

* E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993, Chapter VI, §2 and §5
  (`Lᵖ` boundedness of pseudodifferential operators of order zero via Calderón–Zygmund theory).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §3.
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal SchwartzMap ComplexConjugate InnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ}

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The off-diagonal kernel `K` of a uniform symbol of order `0` and its transposed adjoint
`(x, y) ↦ K(y, x)†`, as real-linear kernels, satisfy the hypotheses of the Calderón–Zygmund
theorem: both are strongly measurable, `K` satisfies the size estimate, and both satisfy the
smoothness estimate in the second variable with exponent `1 / 2`. -/
private theorem IsUniform.exists_calderonZygmund_offDiagonalKernel {a : Symbol n V W 0}
    (ha : a.IsUniform) :
    letI : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
    letI : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
    StronglyMeasurable (Function.uncurry fun x y ↦
      (offDiagonalKernel a x y).restrictScalars ℝ) ∧
    StronglyMeasurable (Function.uncurry fun x y ↦
      (ContinuousLinearMap.adjoint (offDiagonalKernel a y x)).restrictScalars ℝ) ∧
    ∃ C₀ C : ℝ≥0, (∀ x y : CoordinateSpace n, x ≠ y →
      ‖offDiagonalKernel a x y‖ ≤ C₀ * dist x y ^ (-(Module.finrank ℝ (CoordinateSpace n) : ℝ))) ∧
      (∀ x y y' : CoordinateSpace n, 2 * dist y y' < dist x y' →
        ‖(offDiagonalKernel a x y).restrictScalars ℝ -
            (offDiagonalKernel a x y').restrictScalars ℝ‖ ≤
          C * (dist y y' ^ (1 / 2 : ℝ) *
            dist x y' ^ (-(Module.finrank ℝ (CoordinateSpace n) + 1 / 2 : ℝ)))) ∧
      ∀ x y y' : CoordinateSpace n, 2 * dist y y' < dist x y' →
        ‖(ContinuousLinearMap.adjoint (offDiagonalKernel a y x)).restrictScalars ℝ -
            (ContinuousLinearMap.adjoint (offDiagonalKernel a y' x)).restrictScalars ℝ‖ ≤
          C * (dist y y' ^ (1 / 2 : ℝ) *
            dist x y' ^ (-(Module.finrank ℝ (CoordinateSpace n) + 1 / 2 : ℝ))) := by
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
  have hm := stronglyMeasurable_uncurry_offDiagonalKernel a
  refine ⟨(ContinuousLinearMap.restrictScalarsIsometry ℂ V W ℝ ℝ).continuous.comp_stronglyMeasurable
    hm, ((ContinuousLinearMap.restrictScalarsIsometry ℂ W V ℝ ℝ).continuous.comp
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := W)).continuous).comp_stronglyMeasurable
        (hm.comp_measurable measurable_swap), ?_⟩
  simp only [finrank_euclideanSpace_fin, dist_eq_norm, ← ContinuousLinearMap.restrictScalars_sub,
    ContinuousLinearMap.norm_restrictScalars, ← map_sub, LinearIsometryEquiv.norm_map]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- On `ℝ⁰` there are no pairs of distinct points.
    have h0 (x y y' : CoordinateSpace 0) (h : 2 * ‖y - y'‖ < ‖x - y'‖) : False := by
      rw [Subsingleton.elim x y', sub_self, norm_zero] at h
      exact absurd h (not_lt.2 (by positivity))
    exact ⟨0, 0, fun x y hxy ↦ absurd (Subsingleton.elim x y) hxy,
      fun x y y' h ↦ (h0 x y y' h).elim, fun x y y' h ↦ (h0 x y y' h).elim⟩
  have hn' : (0 : ℝ) < 0 + n := by simpa using hn
  obtain ⟨C₀, hC₀, hsize⟩ := ha.exists_norm_offDiagonalKernel_le hn'
  obtain ⟨C₁, hC₁, hright⟩ := ha.exists_norm_offDiagonalKernel_sub_right_le (δ := 1 / 2)
    (by norm_num) (by norm_num) (by positivity)
  obtain ⟨C₂, -, hleft⟩ := ha.exists_norm_offDiagonalKernel_sub_left_le (δ := 1 / 2)
    (by norm_num) (by norm_num) (by positivity)
  refine ⟨C₀.toNNReal, (max C₁ C₂).toNNReal, fun x y hxy ↦ ?_, fun x y y' h ↦ ?_,
    fun x y y' h ↦ ?_⟩
  · simpa [Real.coe_toNNReal _ hC₀] using hsize x y hxy
  · rw [Real.coe_toNNReal _ (hC₁.trans (le_max_left _ _)), ← mul_assoc]
    refine (hright x y y' h).trans ?_
    simp only [zero_add]
    gcongr
    exact le_max_left _ _
  · -- The smoothness of the transposed kernel in its second variable is the smoothness of `K` in
    -- its first variable.
    rw [norm_sub_rev x y'] at h ⊢
    rw [Real.coe_toNNReal _ (hC₁.trans (le_max_left _ _)), ← mul_assoc]
    refine (hleft y y' x h).trans ?_
    simp only [zero_add]
    gcongr
    exact le_max_right _ _

/-- **`Lᵖ` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
complex Hilbert spaces whose estimates are uniform in the position, and for every `1 < p < ∞`,
there is a constant `C` with `‖Op(a) u‖_p ≤ C ‖u‖_p` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt {a : Symbol n V W 0}
    (ha : a.IsUniform) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) p volume ≤
        ENNReal.ofReal C * eLpNorm u p volume := by
  obtain ⟨T, hT⟩ := a.exists_quantizeUniformOrderZeroLp ha
  have hrep (f : Lp V 2 (volume : Measure (CoordinateSpace n))) (s : Set (CoordinateSpace n))
      (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
      ∀ᵐ x, x ∉ s → T f x = ∫ y, offDiagonalKernel a x y (f y) :=
    ae_apply_eq_integral_offDiagonalKernel a ENNReal.ofNat_ne_top hT f hs hf
  -- The Calderón–Zygmund theorem is stated for real Hilbert spaces.
  let : InnerProductSpace ℝ V := InnerProductSpace.complexToReal
  let : InnerProductSpace ℝ W := InnerProductSpace.complexToReal
  obtain ⟨hkm, hkm', C₀, C, hsize, hk, hk'⟩ := ha.exists_calderonZygmund_offDiagonalKernel
  -- The adjoint of `T` is given by the transposed kernel `(x, y) ↦ K(y, x)†`, since `K` is bounded
  -- away from the diagonal.
  have hbdd : ∀ r > 0, ∃ M, ∀ x y : CoordinateSpace n, r ≤ dist x y →
      ‖offDiagonalKernel a x y‖ ≤ M := fun r hr ↦
    ⟨C₀ * r ^ (-(Module.finrank ℝ (CoordinateSpace n) : ℝ)), fun x y hxy ↦
      (hsize x y (dist_pos.1 (hr.trans_le hxy))).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr hxy (neg_nonpos.2 (Nat.cast_nonneg _))) C₀.property)⟩
  obtain ⟨D, hD⟩ := ContinuousLinearMap.exists_eLpNorm_le_of_norm_sub_le_mul_rpow
    (T.restrictScalars ℝ) hkm hkm' (by norm_num) (by norm_num)
    (fun x y hxy ↦ by simpa only [ContinuousLinearMap.norm_restrictScalars] using hsize x y hxy)
    (fun x y hxy ↦ by
      simpa only [ContinuousLinearMap.norm_restrictScalars, LinearIsometryEquiv.norm_map,
        dist_comm x y] using hsize y x hxy.symm)
    hk hk' hrep
    (fun f s hs hf ↦ by
      rw [L2.adjoint_restrictScalars]
      exact ContinuousLinearMap.ae_adjoint_apply_eq_integral T
        (stronglyMeasurable_uncurry_offDiagonalKernel a) hbdd hrep f hs hf)
    hp hp_top
  refine ⟨D, D.coe_nonneg, fun u ↦ ?_⟩
  have h := hD (u.toLp 2)
  rw [ENNReal.ofReal_coe_nnreal]
  rwa [ContinuousLinearMap.coe_restrictScalars', eLpNorm_congr_ae (hT u),
    eLpNorm_congr_ae (u.coeFn_toLp 2 volume)] at h

/-- **The bounded extension of `Op(a)` to `Lᵖ`.** For a symbol `a` of order `0` between complex
Hilbert spaces whose estimates are uniform in the position, and for every `1 < p < ∞`, there is a
bounded operator on `Lᵖ` which agrees with `Op(a)` on Schwartz functions. -/
theorem exists_quantizeUniformOrderZeroLp_of_one_lt (a : Symbol n V W 0) (ha : a.IsUniform)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ T : Lp V p (volume : Measure (CoordinateSpace n)) →L[ℂ] Lp W p volume,
      ∀ u : 𝓢(CoordinateSpace n, V),
        T (u.toLp p) =ᵐ[volume] quantizeSchwartzValue a.coefficient u := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_eLpNorm_quantizeSchwartzValue_le_of_one_lt hp hp_top
  set e := SchwartzMap.toLpCLM ℂ V p (volume : Measure (CoordinateSpace n))
  have hdense : DenseRange e := SchwartzMap.denseRange_toLpCLM hp_top
  have hbound : ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖(SchwartzMap.toLpCLM ℂ W p volume).comp (quantizeUniformCLM a ha) u‖ ≤ C * ‖e u‖ := by
    refine ⟨C, fun u ↦ ?_⟩
    simp only [ContinuousLinearMap.comp_apply, SchwartzMap.toLpCLM_apply, Lp.norm_def, e]
    rw [eLpNorm_congr_ae ((quantizeUniformCLM a ha u).coeFn_toLp p volume),
      eLpNorm_congr_ae (u.coeFn_toLp p volume), coe_quantizeUniformCLM,
      ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (u.memLp p).eLpNorm_ne_top) (hC u)
  refine ⟨((SchwartzMap.toLpCLM ℂ W p volume).comp
    (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm e.toLinearMap, fun u ↦ ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense hbound u
  simp only [e, SchwartzMap.toLpCLM_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply] at h
  rw [h, ← coe_quantizeUniformCLM a ha]
  exact (quantizeUniformCLM a ha u).coeFn_toLp p volume

end InnerProductSpace

end Symbol

end TauCeti

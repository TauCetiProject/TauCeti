/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OffDiagonalKernel
public import TauCeti.Analysis.Pseudodifferential.SchwartzMapping
public import TauCeti.Analysis.Pseudodifferential.Sobolev
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import TauCeti.Analysis.Fourier.ChangeOfVariables
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# `L²` boundedness of uniform symbols of order zero

Let `a` be a symbol of order `0` on `ℝⁿ` whose estimates
`‖∂_x^α ∂_ξ^β a(x, ξ)‖ ≤ C_{α,β} ⟨ξ⟩^(-|β|)` hold with constants independent of the position `x`
(`TauCeti.Symbol.IsUniform`). Then its Kohn–Nirenberg quantization `Op(a)` is bounded on `L²`:
there is a constant `C` with `‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`
(`TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`), so `Op(a)` extends to a
bounded operator on `L² = H^0` (`TauCeti.Symbol.quantizeUniformOrderZero`). No support condition
in the position is imposed. This is the `L²` theorem for the class `S^0_{1,0}` with uniform
estimates; it is the starting point for the Sobolev mapping properties of operators whose symbols
do not vanish at spatial infinity.

The hypothesis of uniformity cannot be dropped: the symbol `x` of multiplication by the
coordinate on `ℝ` has order `0` locally (`TauCeti.Symbol.ofSpatial`), but is not uniform
(`TauCeti.Symbol.not_isUniform_ofSpatial_smul`) and is unbounded on `L²`.

## Main declarations

* `TauCeti.Symbol.IsUniform.exists_eLpNorm_quantizeSchwartzValue_le`: the `L²` estimate on
  Schwartz functions, for complex Hilbert spaces `V`, `W`.
* `TauCeti.Symbol.quantizeUniformOrderZero`: the bounded extension `H^0(ℝⁿ; V) → H^0(ℝⁿ; W)`,
  with `TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`
  identifying its values on Schwartz functions, its norm bound
  `TauCeti.Symbol.norm_quantizeUniformOrderZero_le` and its linearity in the symbol.
* `TauCeti.Symbol.exists_quantizeUniformOrderZero`: the same extension for finite-dimensional
  complex normed `V` and `W`.

## Implementation notes

The proof localizes in the position with the translates `φ(· - z)`, `z ∈ ℝⁿ`, of a fixed bump
function `φ`, as a continuous partition: `∫ φ(x - z)² dz = ‖φ‖₂²` for every `x`, so
`‖φ‖₂² ‖f‖₂² = ∫ ‖φ(· - z) f‖₂² dz`. Let `ψ` be a second bump, equal to `1` near the support of
`φ`. Then

`φ(x - z) Op(a) u (x) = φ(x - z) Op(a) (ψ(· - z) u) (x) + φ(x - z) Op(a) ((1 - ψ(· - z)) u) (x)`.

* The first term is the quantization of the symbol `φ(x - z) a(x, ξ)`, which vanishes outside a
  translate of a fixed compact set. Translating back, the decay of its Fourier transform in the
  position is controlled by the uniform estimates of `a`, independently of `z`, so the
  compact-support estimate
  (`TauCeti.Symbol.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay`) bounds its
  `L²` norm by `C ‖ψ(· - z) u‖₂` with `C` independent of `z`.
* In the second term the input vanishes near the support of `φ(· - z)`, so it is given by the
  off-diagonal kernel of `Op(a)`
  (`TauCeti.Symbol.quantizeSchwartzValue_eq_integral_offDiagonalKernel`), which is bounded by
  `C ‖x - y‖^(-2N)` uniformly in `x`
  (`TauCeti.Symbol.IsUniform.exists_norm_offDiagonalKernel_le`). Away from the diagonal this is
  an integrable convolution kernel, and Schur's test (`TauCeti.eLpNorm_lintegral_mul_le`) bounds
  the term by `C ‖u‖₂`.

Integrating the squares of both bounds over `z` gives the estimate for compactly supported `u`,
and density of compactly supported Schwartz functions (`SchwartzMap.dense_hasCompactSupport`)
gives it for all Schwartz functions.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (3.1).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.11.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Metric Set Filter
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace ContDiff RealInnerProductSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ}

section Localization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

/-- The translate `(x, ξ) ↦ a(x + z, ξ)` of a symbol in the position. -/
private def translate (z : CoordinateSpace n) (a : Symbol n V W m) : Symbol n V W m where
  coefficient p := a.coefficient (p.1 + z, p.2)
  contDiff_coefficient :=
    a.contDiff_coefficient.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)
  exists_bound K hK α β := by
    obtain ⟨C, hC0, hC⟩ :=
      a.exists_bound ((· + z) '' K) (hK.image (continuous_id.add continuous_const)) α β
    exact ⟨C, hC0, fun x hx ξ ↦ by
      rw [mixedDeriv_comp_add_fst]
      exact hC _ ⟨x, hx, rfl⟩ ξ⟩

private theorem mixedDeriv_translate (z : CoordinateSpace n) (a : Symbol n V W m)
    (α β : List (Fin n)) (x ξ : CoordinateSpace n) :
    mixedDeriv α β (translate z a).coefficient x ξ = mixedDeriv α β a.coefficient (x + z) ξ :=
  mixedDeriv_comp_add_fst α β a.coefficient z x ξ

/-- The symbol `(x, ξ) ↦ φ(x) id` of multiplication by a smooth real function `φ`. -/
private def scalarCutoff (φ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ) : Symbol n W W 0 :=
  ofSpatial (fun x ↦ (φ x : ℂ) • ContinuousLinearMap.id ℂ W)
    ((Complex.ofRealCLM.contDiff.comp hφ).smul contDiff_const)

private theorem coefficient_scalarCutoff_comp (φ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    ((scalarCutoff φ hφ).comp a).coefficient p = (φ p.1 : ℂ) • a.coefficient p := by
  simp [scalarCutoff, coefficient_comp]

/-- The symbol `φ(x - z) a(x, ξ)`: the cutoff of `a` to a neighbourhood of `z`. -/
private def localize (φ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : CoordinateSpace n)
    (a : Symbol n V W m) : Symbol n V W (0 + m) :=
  (scalarCutoff (fun x ↦ φ (x - z)) (hφ.comp (contDiff_id.sub contDiff_const))).comp a

private theorem coefficient_localize (φ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (z : CoordinateSpace n) (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    (localize φ hφ z a).coefficient p = (φ (p.1 - z) : ℂ) • a.coefficient p :=
  coefficient_scalarCutoff_comp _ _ a p

private theorem hasCompactSpatialSupport_localize {φ : CoordinateSpace n → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (z : CoordinateSpace n)
    (a : Symbol n V W m) : (localize φ hφ z a).HasCompactSpatialSupport := by
  refine hasCompactSpatialSupport_iff.2 ⟨(· + z) '' tsupport φ, hφc.isCompact.image
    (continuous_id.add continuous_const), fun x hx ξ ↦ ?_⟩
  have hxz : x - z ∉ tsupport φ := fun h ↦ hx ⟨x - z, h, sub_add_cancel x z⟩
  rw [coefficient_localize, image_eq_zero_of_notMem_tsupport hxz, Complex.ofReal_zero, zero_smul]

/-- The quantization of the localized symbol is the localized quantization. -/
private theorem quantizeSchwartzValue_localize (φ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (z : CoordinateSpace n) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (localize φ hφ z a).coefficient u x =
      φ (x - z) • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeSchwartzValue_congr_left (b := (φ (x - z) : ℂ) • a.coefficient)
      (fun ξ ↦ coefficient_localize φ hφ z a (x, ξ)) u,
    quantizeSchwartzValue_smul_left, Complex.coe_smul]

/-- **Uniform decay of the localized symbols.** For a uniform symbol `a`, the Fourier transforms
in the position of the localized symbols `φ(x - z) a(x, ξ)` decay with a constant independent of
the center `z`. -/
private theorem IsUniform.exists_decay_localize {a : Symbol n V W m} (ha : a.IsUniform)
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (N : ℕ) :
    ∃ C₀, 0 ≤ C₀ ∧ ∀ z η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ (localize φ hφ z a).coefficient (x, ξ)) η‖ ≤
        C₀ * (1 + ‖ξ‖ ^ 2) ^ ((0 + m) / 2) := by
  set K : TopologicalSpace.Compacts (CoordinateSpace n) := ⟨tsupport φ, hφc⟩
  obtain ⟨t, C, hC, h⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le_sum_seminorm (V := V) (W := W) (m := 0 + m) K N
  set P : Symbol n W W 0 := scalarCutoff φ hφ
  choose CP hCP0 hCP using fun s r ↦ P.exists_bound K K.isCompact s r
  choose D hD0 hD using fun s r ↦ isUniform_iff.1 ha s r
  -- The constant of the Leibniz estimate for `P ∘ translate z a`, which does not depend on `z`.
  set M : List (Fin n) → ℝ := fun α ↦ (([] : List (Fin n)).sublists'.revzip.map fun r =>
    (α.sublists'.revzip.map fun s => CP s.1 r.1 * D s.2 r.2).sum).sum
  refine ⟨C * ∑ α ∈ t, max (M α) 0, mul_nonneg hC (Finset.sum_nonneg fun _ _ ↦ le_max_right _ _),
    fun z η ξ ↦ ?_⟩
  set c := P.comp (translate z a)
  have hc0 : ∀ x ∉ K, ∀ ξ, c.coefficient (x, ξ) = 0 := fun x hx ξ ↦ by
    rw [coefficient_scalarCutoff_comp, image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero,
      zero_smul]
  have hcc : c.coefficient = fun p ↦ (P.coefficient p).comp ((translate z a).coefficient p) :=
    funext (coefficient_comp P _)
  have hsem (α : List (Fin n)) : Symbol.seminorm K α [] c ≤ max (M α) 0 :=
    seminorm_le_bound K α [] c (le_max_right _ _) fun x hx ξ ↦ hcc ▸
      (norm_mixedDeriv_comp_le P.contDiff_coefficient (translate z a).contDiff_coefficient
        (fun s r ↦ hCP s r x hx ξ) (fun s r ↦ by rw [mixedDeriv_translate]; exact hD s r _ ξ)
        α []).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (rpow_weight_pos ξ _).le)
  have hslice : (fun x ↦ (localize φ hφ z a).coefficient (x, ξ)) =
      fun x ↦ c.coefficient (x - z, ξ) := by
    funext x
    rw [coefficient_localize, coefficient_scalarCutoff_comp]
    simp [translate]
  rw [hslice, norm_fourier_comp_sub (fun x ↦ c.coefficient (x, ξ))]
  refine (h c hc0 η ξ).trans ?_
  gcongr
  exact hsem _

end Localization

section Hilbert

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W 0}

/-- **The localized pieces are bounded on `L²`, uniformly in the center.** For a uniform symbol
`a` of order `0` and a smooth compactly supported `φ`, the operators `u ↦ φ(· - z) Op(a) u` are
bounded on `L²` with a constant independent of `z`. -/
private theorem IsUniform.exists_eLpNorm_smul_quantizeSchwartzValue_le (ha : a.IsUniform)
    {φ : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ C, 0 ≤ C ∧ ∀ (z : CoordinateSpace n) (u : 𝓢(CoordinateSpace n, V)),
      eLpNorm (fun x ↦ φ (x - z) • quantizeSchwartzValue a.coefficient u x) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨N, C₁, hC₁, hS⟩ :=
    exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_of_decay (V := V) (W := W) n (0 + 0) 0
  obtain ⟨C₀, hC₀, hdec⟩ := ha.exists_decay_localize hφ hφc N
  refine ⟨C₁ * C₀, mul_nonneg hC₁ hC₀, fun z u ↦ ?_⟩
  have hb := hasCompactSpatialSupport_localize hφ hφc z a
  have h := hS _ hb C₀ hC₀ (hdec z) u
  simp only [add_zero, sub_self, zero_div, Real.rpow_zero, Complex.ofReal_one, one_smul,
    SchwartzMap.fourier_coe] at h
  rw [(hb.integrable_quantizeSchwartzValue u).eLpNorm_fourier_two_eq
      (hb.memLp_quantizeSchwartzValue u 2),
    u.integrable.eLpNorm_fourier_two_eq (u.memLp 2)] at h
  rwa [funext (quantizeSchwartzValue_localize φ hφ z a u)] at h

/-! ### The off-diagonal part -/

/-- The bump function `φ₀`, equal to `1` on the unit ball and vanishing outside the ball of
radius `2`. -/
private def innerBump : ContDiffBump (0 : CoordinateSpace n) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump function `ψ₀`, equal to `1` on the ball of radius `3` and vanishing outside the ball
of radius `4`. -/
private def outerBump : ContDiffBump (0 : CoordinateSpace n) :=
  ⟨3, 4, by norm_num, by norm_num⟩

private theorem innerBump_rOut : (innerBump (n := n)).rOut = 2 := (rfl)

private theorem outerBump_rIn : (outerBump (n := n)).rIn = 3 := (rfl)

/-- The integrable majorant `C 2^(2N) (1 + ‖w‖)^(-2N)`, `N = n + 1`, of the off-diagonal kernel
at distance at least `1` from the diagonal. -/
private def kernelMajorant (C : ℝ) (w : CoordinateSpace n) : ℝ :=
  C * 2 ^ (2 * (n + 1)) * (1 + ‖w‖) ^ (-((2 * (n + 1) : ℕ) : ℝ))

private theorem integrable_kernelMajorant (C : ℝ) : Integrable (kernelMajorant (n := n) C) :=
  (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul _

private theorem continuous_kernelMajorant (C : ℝ) : Continuous (kernelMajorant (n := n) C) :=
  continuous_const.mul ((continuous_const.add continuous_norm).rpow_const fun w ↦
    Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg w)).ne')

/-- At distance `r ≥ 1` from the diagonal, `C r^(-2N)` is at most the kernel majorant. -/
private theorem div_pow_le_kernelMajorant {C : ℝ} (hC : 0 ≤ C) {w : CoordinateSpace n}
    (hw : 1 ≤ ‖w‖) : C / ‖w‖ ^ (2 * (n + 1)) ≤ kernelMajorant C w := by
  have hr : 0 < ‖w‖ := one_pos.trans_le hw
  rw [kernelMajorant, Real.rpow_neg (by positivity), Real.rpow_natCast, div_eq_mul_inv, mul_assoc]
  gcongr
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    ← mul_pow]
  gcongr
  linarith

/-- **The off-diagonal part.** Let `u` have compact support and let `x` lie within distance `2`
of `z`. The input `u - ψ₀(· - z) u` vanishes on the ball of radius `3` about `z`, so its
quantization at `x` is given by the off-diagonal kernel, whose bound
`C ‖x - y‖^(-2N)` gives `|Op(a) (u - ψ₀(· - z) u) (x)| ≤ ∫ k(x - y) |u(y)| dy` with the kernel
majorant `k`. -/
private theorem enorm_quantizeSchwartzValue_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x y, ‖offDiagonalKernel a x y‖ ≤ C / ‖x - y‖ ^ (2 * (n + 1)))
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) {z x : CoordinateSpace n}
    (hxz : ‖x - z‖ < 2) :
    ‖quantizeSchwartzValue a.coefficient
        (u - SchwartzMap.smulLeftCLM V (fun y ↦ outerBump (y - z)) u) x‖ₑ ≤
      ∫⁻ y, ENNReal.ofReal (kernelMajorant C (x - y)) * ‖u y‖ₑ := by
  set ψ : CoordinateSpace n → ℝ := fun y ↦ outerBump (y - z)
  have hψc : HasCompactSupport ψ :=
    outerBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z)
  have hψ : ψ.HasTemperateGrowth :=
    hψc.hasTemperateGrowth (outerBump.contDiff.comp (contDiff_id.sub contDiff_const))
  set v := u - SchwartzMap.smulLeftCLM V ψ u
  have hv (y : CoordinateSpace n) : v y = (1 - ψ y) • u y := by
    simp [v, SchwartzMap.smulLeftCLM_apply_apply hψ, sub_smul]
  have hv0 (y : CoordinateSpace n) (hy : ‖y - z‖ < 3) : v y = 0 := by
    have hψy : ψ y = 1 :=
      outerBump.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, outerBump_rIn]; exact hy.le)
    rw [hv, hψy, sub_self, zero_smul]
  have hvc : HasCompactSupport v := by
    refine hu.mono fun y hy ↦ ?_
    rw [Function.mem_support, hv] at hy
    exact Function.mem_support.2 (right_ne_zero_of_smul hy)
  have hxv : x ∉ tsupport v := notMem_tsupport_iff_eventuallyEq.2 <|
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_iff_norm.2 (by linarith)))
      fun y hy ↦ hv0 y (mem_ball_iff_norm.1 hy)
  rw [quantizeSchwartzValue_eq_integral_offDiagonalKernel a hvc hxv]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun y ↦ ?_)
  by_cases hy : ‖y - z‖ < 3
  · rw [hv0 y hy, map_zero, enorm_zero]
    positivity
  have hxy : 1 ≤ ‖x - y‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub y x z
    rw [norm_sub_rev y x] at this
    linarith
  have hψ01 : ‖1 - ψ y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [outerBump.nonneg (x := y - z), outerBump.le_one (x := y - z)]
  have hk0 : 0 ≤ kernelMajorant C (x - y) := by
    unfold kernelMajorant
    positivity
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖offDiagonalKernel a x y (v y)‖ ≤ ‖offDiagonalKernel a x y‖ * ‖v y‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C / ‖x - y‖ ^ (2 * (n + 1))) * ‖u y‖ := by
        rw [hv, norm_smul]
        gcongr
        · exact hC x y
        · exact mul_le_of_le_one_left (norm_nonneg _) hψ01
    _ ≤ kernelMajorant C (x - y) * ‖u y‖ := by
        gcongr
        exact div_pow_le_kernelMajorant hC0 hxy

private theorem eLpNorm_two_rpow_two {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {f : CoordinateSpace n → ε} (hf : AEStronglyMeasurable f) :
    eLpNorm f 2 volume ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero hf

/-- The off-diagonal majorant `G(x) = ∫ k(x - y) |u(y)| dy` is measurable. -/
private theorem measurable_lintegral_kernelMajorant {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ℝ) (u : 𝓢(CoordinateSpace n, E)) :
    Measurable fun x ↦ ∫⁻ y, ENNReal.ofReal (kernelMajorant C (x - y)) * ‖u y‖ₑ :=
  ((ENNReal.measurable_ofReal.comp ((continuous_kernelMajorant C).measurable.comp
    (measurable_fst.sub measurable_snd))).mul
      ((continuous_enorm.comp u.continuous).measurable.comp measurable_snd)).lintegral_prod_right'

/-- **Schur's test for the off-diagonal majorant**: `‖G‖₂ ≤ ‖k‖₁ ‖u‖₂` for
`G(x) = ∫ k(x - y) |u(y)| dy`, in squared form. -/
private theorem lintegral_rpow_two_lintegral_kernelMajorant_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (C : ℝ) (u : 𝓢(CoordinateSpace n, E)) :
    ∫⁻ x, (∫⁻ y, ENNReal.ofReal (kernelMajorant C (x - y)) * ‖u y‖ₑ) ^ (2 : ℝ) ≤
      (∫⁻ w, ENNReal.ofReal (kernelMajorant (n := n) C w)) ^ (2 : ℝ) *
        ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) := by
  have hu2 : Measurable fun y ↦ ‖u y‖ₑ := (continuous_enorm.comp u.continuous).measurable
  have hk : Measurable (Function.uncurry fun x y : CoordinateSpace n ↦
      ENNReal.ofReal (kernelMajorant C (x - y))) := ENNReal.measurable_ofReal.comp
    ((continuous_kernelMajorant C).measurable.comp (measurable_fst.sub measurable_snd))
  set A := ∫⁻ w, ENNReal.ofReal (kernelMajorant (n := n) C w)
  have hschur := TauCeti.eLpNorm_lintegral_mul_le hk.aemeasurable hu2.aemeasurable
    (p := 2) one_le_two (A := A) (B := A)
    (.of_forall fun x ↦ (lintegral_sub_left_eq_self
      (fun w ↦ ENNReal.ofReal (kernelMajorant C w)) x).le)
    (.of_forall fun y ↦ (lintegral_sub_right_eq_self
      (fun w ↦ ENNReal.ofReal (kernelMajorant C w)) y).le)
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num),
    eLpNorm_enorm _ u.continuous.aestronglyMeasurable] at hschur
  norm_num at hschur
  have h2 := ENNReal.rpow_le_rpow hschur zero_le_two
  rwa [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
    eLpNorm_two_rpow_two (measurable_lintegral_kernelMajorant C u).aestronglyMeasurable,
    eLpNorm_two_rpow_two u.continuous.aestronglyMeasurable] at h2

/-- **The pointwise splitting.** With `φ₀ = innerBump` and `ψ₀ = outerBump`,
`|φ₀(x - z) Op(a) u (x)|² ≤ 2 |φ₀(x - z) Op(a) (ψ₀(· - z) u) (x)|² + 2 |φ₀(x - z)|² G(x)²`,
where `G(x) = ∫ k(x - y) |u(y)| dy` bounds the off-diagonal part. -/
private theorem enorm_smul_quantizeSchwartzValue_rpow_two_le (ha : a.IsUniform) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x y, ‖offDiagonalKernel a x y‖ ≤ C / ‖x - y‖ ^ (2 * (n + 1)))
    {u : 𝓢(CoordinateSpace n, V)} (hu : HasCompactSupport u) (z x : CoordinateSpace n) :
    ‖innerBump (x - z) • quantizeSchwartzValue a.coefficient u x‖ₑ ^ (2 : ℝ) ≤
      2 * ‖innerBump (x - z) • quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ outerBump (y - z)) u) x‖ₑ ^ (2 : ℝ) +
      2 * (‖innerBump (x - z)‖ₑ ^ (2 : ℝ) *
        (∫⁻ y, ENNReal.ofReal (kernelMajorant C (x - y)) * ‖u y‖ₑ) ^ (2 : ℝ)) := by
  set w := SchwartzMap.smulLeftCLM V (fun y ↦ outerBump (y - z)) u
  set φ : CoordinateSpace n → ℝ := ⇑(innerBump (n := n))
  set G := ∫⁻ y, ENNReal.ofReal (kernelMajorant C (x - y)) * ‖u y‖ₑ
  have hsplit : quantizeSchwartzValue a.coefficient u x = quantizeSchwartzValue a.coefficient w x +
      quantizeSchwartzValue a.coefficient (u - w) x := by
    have h := DFunLike.congr_fun (map_add (quantizeUniformCLM a ha) w (u - w)) x
    rwa [add_sub_cancel, quantizeUniformCLM_apply, add_apply, quantizeUniformCLM_apply,
      quantizeUniformCLM_apply] at h
  have hoff : ‖φ (x - z) • quantizeSchwartzValue a.coefficient (u - w) x‖ₑ ≤ ‖φ (x - z)‖ₑ * G := by
    rw [enorm_smul]
    by_cases hxz : ‖x - z‖ < 2
    · gcongr
      exact enorm_quantizeSchwartzValue_sub_le hC0 hC hu hxz
    · rw [show φ (x - z) = 0 from innerBump.zero_of_le_dist
        (by rw [dist_zero_right, innerBump_rOut]; linarith), enorm_zero, zero_mul, zero_mul]
  calc ‖φ (x - z) • quantizeSchwartzValue a.coefficient u x‖ₑ ^ (2 : ℝ)
      ≤ (‖φ (x - z) • quantizeSchwartzValue a.coefficient w x‖ₑ + ‖φ (x - z)‖ₑ * G) ^
          (2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ zero_le_two
        rw [hsplit, smul_add]
        exact (enorm_add_le _ _).trans (add_le_add le_rfl hoff)
    _ ≤ 2 ^ ((2 : ℝ) - 1) * (‖φ (x - z) • quantizeSchwartzValue a.coefficient w x‖ₑ ^ (2 : ℝ) +
          (‖φ (x - z)‖ₑ * G) ^ (2 : ℝ)) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ one_le_two
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two]
        norm_num
        ring

/-! ### Integration over the centers -/

/-- The translates of `|φ|²` integrate to `‖φ‖₂²` at every point:
`∫ (∫ |φ(x - z)|² g(x) dx) dz = ‖φ‖₂² ∫ g`. -/
private theorem lintegral_lintegral_enorm_sub_rpow_mul {φ : CoordinateSpace n → ℝ}
    (hφ : Continuous φ) {g : CoordinateSpace n → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, ∫⁻ x, ‖φ (x - z)‖ₑ ^ (2 : ℝ) * g x = (∫⁻ y, ‖φ y‖ₑ ^ (2 : ℝ)) * ∫⁻ x, g x := by
  have hφm : Measurable fun y ↦ ‖φ y‖ₑ ^ (2 : ℝ) := hφ.measurable.enorm.pow_const _
  rw [lintegral_lintegral_swap ((hφm.comp (measurable_snd.sub measurable_fst)).mul
    (hg.comp measurable_snd)).aemeasurable]
  calc ∫⁻ x, ∫⁻ z, ‖φ (x - z)‖ₑ ^ (2 : ℝ) * g x = ∫⁻ x, (∫⁻ y, ‖φ y‖ₑ ^ (2 : ℝ)) * g x :=
        lintegral_congr fun x ↦ by
          rw [lintegral_mul_const (f := fun z ↦ ‖φ (x - z)‖ₑ ^ (2 : ℝ)) _
              (hφm.comp (measurable_const.sub measurable_id)),
            lintegral_sub_left_eq_self (fun y ↦ ‖φ y‖ₑ ^ (2 : ℝ)) x]
    _ = _ := lintegral_const_mul _ hg

private theorem lintegral_lintegral_enorm_smul_rpow {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {φ : CoordinateSpace n → ℝ} (hφ : Continuous φ)
    {f : CoordinateSpace n → E} (hf : Continuous f) :
    ∫⁻ z, ∫⁻ x, ‖φ (x - z) • f x‖ₑ ^ (2 : ℝ) =
      (∫⁻ y, ‖φ y‖ₑ ^ (2 : ℝ)) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
  simp_rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two]
  exact lintegral_lintegral_enorm_sub_rpow_mul hφ
    ((continuous_enorm.comp hf).measurable.pow_const _)

/-! ### The estimate -/

/-- **The `L²` estimate for compactly supported inputs**, in squared form: integrating the squares
of the bounds for the localized part and the off-diagonal part over the centers `z`. -/
private theorem IsUniform.exists_lintegral_le_of_hasCompactSupport (ha : a.IsUniform) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
      ∫⁻ x, ‖quantizeSchwartzValue a.coefficient u x‖ₑ ^ (2 : ℝ) ≤
        M * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) := by
  set φ : CoordinateSpace n → ℝ := ⇑(innerBump (n := n))
  set ψ : CoordinateSpace n → ℝ := ⇑(outerBump (n := n))
  have hφ : Continuous φ := innerBump.continuous
  have hψ : Continuous ψ := outerBump.continuous
  obtain ⟨CA, -, hCA⟩ := ha.exists_eLpNorm_smul_quantizeSchwartzValue_le (φ := φ)
    innerBump.contDiff innerBump.hasCompactSupport
  obtain ⟨CK, hCK0, hCK⟩ := ha.exists_norm_offDiagonalKernel_le (N := n + 1)
    (by push_cast; linarith)
  set A : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (kernelMajorant (n := n) CK w) with hAdef
  have hA : A ≠ ⊤ := by
    rw [hAdef, ← ofReal_integral_eq_lintegral_ofReal (integrable_kernelMajorant CK)
      (ae_of_all _ fun w ↦ by unfold kernelMajorant; positivity)]
    exact ENNReal.ofReal_ne_top
  set cφ := ∫⁻ y, ‖φ y‖ₑ ^ (2 : ℝ)
  set cψ := ∫⁻ y, ‖ψ y‖ₑ ^ (2 : ℝ)
  have hfin {χ : CoordinateSpace n → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
      ∫⁻ y, ‖χ y‖ₑ ^ (2 : ℝ) ≠ ⊤ := by
    rw [← eLpNorm_two_rpow_two hχ.aestronglyMeasurable]
    exact ENNReal.rpow_ne_top_of_nonneg zero_le_two
      (hχ.memLp_of_hasCompactSupport (p := 2) hχc).eLpNorm_ne_top
  have hcφ : cφ ≠ ⊤ := hfin hφ innerBump.hasCompactSupport
  have hcψ : cψ ≠ ⊤ := hfin hψ outerBump.hasCompactSupport
  have hcφ0 : cφ ≠ 0 := by
    refine (lt_of_lt_of_le ?_ (setLIntegral_le_lintegral (ball 0 1) _)).ne'
    rw [setLIntegral_congr_fun measurableSet_ball (g := fun _ ↦ 1) fun y hy ↦ by
      rw [show φ y = 1 from innerBump.one_of_mem_closedBall (ball_subset_closedBall hy),
        enorm_one, ENNReal.one_rpow], setLIntegral_one]
    exact measure_ball_pos volume 0 one_pos
  refine ⟨(2 * ENNReal.ofReal CA ^ (2 : ℝ) * cψ + 2 * cφ * A ^ (2 : ℝ)) / cφ,
    ENNReal.div_ne_top (by finiteness) hcφ0, fun u hu ↦ ?_⟩
  set F := quantizeSchwartzValue a.coefficient u
  have hF : Continuous F := a.continuous_quantizeSchwartzValue_coefficient u
  set G : CoordinateSpace n → ℝ≥0∞ :=
    fun x ↦ ∫⁻ y, ENNReal.ofReal (kernelMajorant CK (x - y)) * ‖u y‖ₑ
  have hG : Measurable G := measurable_lintegral_kernelMajorant CK u
  have hGsq := lintegral_rpow_two_lintegral_kernelMajorant_le CK u
  -- The localized parts are bounded uniformly in the center.
  have hloc (z : CoordinateSpace n) :
      ∫⁻ x, ‖φ (x - z) • quantizeSchwartzValue a.coefficient
          (SchwartzMap.smulLeftCLM V (fun y ↦ ψ (y - z)) u) x‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal CA ^ (2 : ℝ) * ∫⁻ x, ‖ψ (x - z) • u x‖ₑ ^ (2 : ℝ) := by
    set w := SchwartzMap.smulLeftCLM V (fun y ↦ ψ (y - z)) u
    have hψz : (fun y ↦ ψ (y - z)).HasTemperateGrowth :=
      (outerBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z)).hasTemperateGrowth
        (outerBump.contDiff.comp (contDiff_id.sub contDiff_const))
    have h := ENNReal.rpow_le_rpow (hCA z w) zero_le_two
    rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two,
      eLpNorm_two_rpow_two (f := fun x ↦ φ (x - z) • quantizeSchwartzValue a.coefficient w x)
        ((hφ.comp (continuous_id.sub continuous_const)).smul
          (a.continuous_quantizeSchwartzValue_coefficient w)).aestronglyMeasurable,
      eLpNorm_two_rpow_two w.continuous.aestronglyMeasurable] at h
    simpa only [w, SchwartzMap.smulLeftCLM_apply_apply hψz] using h
  have hmeasG (z : CoordinateSpace n) :
      Measurable fun x ↦ 2 * (‖φ (x - z)‖ₑ ^ (2 : ℝ) * G x ^ (2 : ℝ)) :=
    (((continuous_enorm.comp (hφ.comp (continuous_id.sub continuous_const))).measurable.pow_const
      _).mul (hG.pow_const _)).const_mul _
  have hmeasψ : Measurable fun z ↦ ∫⁻ x, ‖ψ (x - z) • u x‖ₑ ^ (2 : ℝ) :=
    Measurable.lintegral_prod_right'
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦ ‖ψ (p.2 - p.1) • u p.2‖ₑ ^ (2 : ℝ))
      ((continuous_enorm.comp ((hψ.comp (continuous_snd.sub continuous_fst)).smul
        (u.continuous.comp continuous_snd))).measurable.pow_const _)
  have hmeasφ : Measurable fun z ↦ ∫⁻ x, ‖φ (x - z)‖ₑ ^ (2 : ℝ) * G x ^ (2 : ℝ) :=
    Measurable.lintegral_prod_right'
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦
        ‖φ (p.2 - p.1)‖ₑ ^ (2 : ℝ) * G p.2 ^ (2 : ℝ))
      (((continuous_enorm.comp (hφ.comp (continuous_snd.sub continuous_fst))).measurable.pow_const
        _).mul ((hG.pow_const _).comp measurable_snd))
  refine (ENNReal.mul_le_mul_iff_right hcφ0 hcφ).1 ?_
  calc cφ * ∫⁻ x, ‖F x‖ₑ ^ (2 : ℝ) = ∫⁻ z, ∫⁻ x, ‖φ (x - z) • F x‖ₑ ^ (2 : ℝ) :=
        (lintegral_lintegral_enorm_smul_rpow hφ hF).symm
    _ ≤ ∫⁻ z, (2 * ENNReal.ofReal CA ^ (2 : ℝ) * (∫⁻ x, ‖ψ (x - z) • u x‖ₑ ^ (2 : ℝ)) +
          2 * ∫⁻ x, ‖φ (x - z)‖ₑ ^ (2 : ℝ) * G x ^ (2 : ℝ)) := by
        refine lintegral_mono fun z ↦ (lintegral_mono
          (enorm_smul_quantizeSchwartzValue_rpow_two_le ha hCK0 hCK hu z)).trans ?_
        rw [lintegral_add_right _ (hmeasG z), lintegral_const_mul' _ _ (by norm_num),
          lintegral_const_mul' _ _ (by norm_num), mul_assoc]
        gcongr
        exact hloc z
    _ = 2 * ENNReal.ofReal CA ^ (2 : ℝ) * (cψ * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ)) +
          2 * (cφ * ∫⁻ x, G x ^ (2 : ℝ)) := by
        rw [lintegral_add_left (hmeasψ.const_mul _), lintegral_const_mul _ hmeasψ,
          lintegral_const_mul _ hmeasφ, lintegral_lintegral_enorm_smul_rpow hψ u.continuous,
          lintegral_lintegral_enorm_sub_rpow_mul hφ (hG.pow_const _)]
    _ ≤ 2 * ENNReal.ofReal CA ^ (2 : ℝ) * (cψ * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ)) +
          2 * (cφ * (A ^ (2 : ℝ) * ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ))) := by
        gcongr
    _ = cφ * ((2 * ENNReal.ofReal CA ^ (2 : ℝ) * cψ + 2 * cφ * A ^ (2 : ℝ)) / cφ *
          ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ)) := by
        have hX (X I : ℝ≥0∞) : cφ * (X / cφ * I) = X * I := by
          rw [← mul_assoc, ENNReal.mul_div_cancel hcφ0 hcφ]
        rw [hX]
        ring

/-- **The `L²` estimate in `H^0` norms**, for all Schwartz functions: the estimate for compactly
supported inputs extends by density, both sides being continuous on Schwartz space. -/
private theorem IsUniform.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
    (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        C * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
  obtain ⟨M, hM, hMu⟩ := ha.exists_lintegral_le_of_hasCompactSupport
  refine ⟨(M ^ (2⁻¹ : ℝ)).toReal, ENNReal.toReal_nonneg, fun u ↦ ?_⟩
  have hcs : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        (M ^ (2⁻¹ : ℝ)).toReal * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖ := by
    intro u hu
    have h := hMu u hu
    rw [← eLpNorm_two_rpow_two
        (a.continuous_quantizeSchwartzValue_coefficient u).aestronglyMeasurable,
      ← eLpNorm_two_rpow_two u.continuous.aestronglyMeasurable] at h
    have h' : eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        M ^ (2⁻¹ : ℝ) * eLpNorm u 2 volume := by
      refine (ENNReal.rpow_le_rpow_iff (z := 2) two_pos).1 (h.trans_eq ?_)
      rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul]
      norm_num
    rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
      SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
      coe_quantizeUniformCLM, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hM)
      (u.memLp 2).eLpNorm_ne_top) h'
  have hclosed : IsClosed {u : 𝓢(CoordinateSpace n, V) |
      ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u)‖ ≤
        (M ^ (2⁻¹ : ℝ)).toReal * ‖SchwartzMap.toBesselPotentialSpaceCLM 0 2 u‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub := closure_minimal
    (s := {u : 𝓢(CoordinateSpace n, V) | HasCompactSupport (u : CoordinateSpace n → V)})
    (fun u hu ↦ hcs u hu) hclosed
  rw [(SchwartzMap.dense_hasCompactSupport (E := CoordinateSpace n) (F := V)).closure_eq] at hsub
  exact hsub (Set.mem_univ u)

/-- **`L²` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` whose
estimates are uniform in the position, there is a constant `C` with
`‖Op(a) u‖_{L²} ≤ C ‖u‖_{L²}` for every Schwartz function `u`. -/
theorem IsUniform.exists_eLpNorm_quantizeSchwartzValue_le (ha : a.IsUniform) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
        ENNReal.ofReal C * eLpNorm u 2 volume := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
  refine ⟨C, hC0, fun u ↦ ?_⟩
  have h := hC u
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM] at h
  have hfin : eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≠ ⊤ := by
    rw [← coe_quantizeUniformCLM a ha]
    exact ((quantizeUniformCLM a ha u).memLp 2).eLpNorm_ne_top
  calc eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume
      = ENNReal.ofReal (eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume).toReal :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (C * (eLpNorm u 2 volume).toReal) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal C * eLpNorm u 2 volume := by
        have hufin : eLpNorm u 2 volume ≠ ⊤ := (u.memLp 2).eLpNorm_ne_top
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_toReal hufin]

/-- **The bounded extension of `Op(a)` to `L²`**, for a uniform symbol `a` of order `0` between
complex Hilbert spaces, as an operator on the Bessel-potential space `H^0 = L²`. It extends the
quantization of Schwartz functions
(`TauCeti.Symbol.toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply`), and it is the
unique continuous linear map with this property (`BesselPotentialSpace.continuousLinearMap_ext`). -/
def quantizeUniformOrderZero (a : Symbol n V W 0) (ha : a.IsUniform) :
    H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W) :=
  ((SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := W) 0 2).comp
      (quantizeUniformCLM a ha)).toLinearMap.extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) 0 2).toLinearMap

/-- On Schwartz functions, the bounded extension of `Op(a)` is `Op(a)`. -/
theorem quantizeUniformOrderZero_toBesselPotentialSpaceCLM (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM 0 2 (quantizeUniformCLM a ha u) := by
  obtain ⟨C, -, hC⟩ := ha.exists_norm_toBesselPotentialSpaceCLM_quantizeUniformCLM_le
  exact LinearMap.extendOfNorm_eq
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) 0 ENNReal.ofNat_ne_top) ⟨C, hC⟩ u

/-- On a Schwartz function `u`, the bounded extension of `Op(a)` to `H^0` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`. -/
@[simp]
theorem toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeUniformOrderZero ha (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeUniformOrderZero_toBesselPotentialSpaceCLM,
    SchwartzMap.toDistr_toBesselPotentialSpaceCLM, SchwartzMap.coe_apply, coe_quantizeUniformCLM]

/-- The operator norm of the bounded extension of `Op(a)` is at most any constant of the `L²`
estimate on Schwartz functions. -/
theorem norm_quantizeUniformOrderZero_le (ha : a.IsUniform) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V), eLpNorm (quantizeSchwartzValue a.coefficient u) 2 volume ≤
      ENNReal.ofReal C * eLpNorm u 2 volume) :
    ‖a.quantizeUniformOrderZero ha‖ ≤ C := by
  refine LinearMap.opNorm_extendOfNorm_le
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM (p := 2) 0 ENNReal.ofNat_ne_top) hC0
    fun u ↦ ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.norm_toBesselPotentialSpaceCLM_zero,
    SchwartzMap.norm_toBesselPotentialSpaceCLM_zero, coe_quantizeUniformCLM,
    ← ENNReal.toReal_ofReal hC0, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (u.memLp 2).eLpNorm_ne_top) (hC u)

/-- The bounded extension of `Op(a)` is additive in the symbol. -/
theorem quantizeUniformOrderZero_add {b : Symbol n V W 0} (ha : a.IsUniform) (hb : b.IsUniform) :
    (a + b).quantizeUniformOrderZero (ha.add hb) =
      a.quantizeUniformOrderZero ha + b.quantizeUniformOrderZero hb :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ by
    rw [add_apply, quantizeUniformOrderZero_toBesselPotentialSpaceCLM,
      quantizeUniformOrderZero_toBesselPotentialSpaceCLM,
      quantizeUniformOrderZero_toBesselPotentialSpaceCLM, quantizeUniformCLM_add, add_apply,
      map_add]

/-- The bounded extension of `Op(a)` is homogeneous in the symbol. -/
theorem quantizeUniformOrderZero_smul (ha : a.IsUniform) (c : ℂ) :
    (c • a).quantizeUniformOrderZero (ha.smul c) = c • a.quantizeUniformOrderZero ha :=
  BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦ by
    rw [smul_apply, quantizeUniformOrderZero_toBesselPotentialSpaceCLM,
      quantizeUniformOrderZero_toBesselPotentialSpaceCLM, quantizeUniformCLM_smul, smul_apply,
      map_smul]

end Hilbert

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **`L²` boundedness of uniform symbols of order zero.** For a symbol `a` of order `0` between
finite-dimensional complex normed spaces whose estimates are uniform in the position, the
quantization `Op(a)` extends from Schwartz functions to a bounded operator
`H^0(ℝⁿ; V) → H^0(ℝⁿ; W)` on `L² = H^0`. No support condition in the position is imposed.

The norms of `V` and `W` need not come from inner products: isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` induce isomorphisms of the Bessel-potential spaces, and the operator is
`e₂⁻¹ ∘ Op(e₂ a e₁⁻¹) ∘ e₁` with the Hilbert-space operator
`TauCeti.Symbol.quantizeUniformOrderZero`. -/
theorem exists_quantizeUniformOrderZero (a : Symbol n V W 0) (ha : a.IsUniform) :
    ∃ T : H^{0}(CoordinateSpace n, V) →L[ℂ] H^{0}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM 0 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂
    (toDistr_quantizeUniformOrderZero_toBesselPotentialSpaceCLM_apply (ha.map _))⟩

end FiniteDimensional

end Symbol

end TauCeti

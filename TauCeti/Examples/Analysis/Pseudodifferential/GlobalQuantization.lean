/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
public import TauCeti.Analysis.Pseudodifferential.Recovery
public import TauCeti.Analysis.Pseudodifferential.Symbol.Differential
public import TauCeti.Analysis.Pseudodifferential.Frequency.Multiplier
import TauCeti.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Checks for symbol recovery, output support and changes of coordinates

Concrete computations testing the conventions of the full Euclidean quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`): how it
recovers the full symbol, how the position support of the symbol controls the support of the
output, which displacement kernel it has, and why a change of coordinates must transform the full
symbol and not only the principal one.

* **Spatial symbols.** For a smooth real function `χ`, the symbol `a(x, ξ) = χ(x)` quantizes to
  multiplication by `χ` (`quantizeSchwartzValue_ofSpatial_smul_id`), and testing on cut-off
  exponentials recovers `χ(x)`
  (`tendsto_quantizeSchwartzValue_ofSpatial_smul_id_cutoffExponential`). For a closed set `K`,
  the operator has output support in `K` exactly when `χ` vanishes outside `K`
  (`tsupport_quantizeSchwartzValue_ofSpatial_smul_id_subset_iff`). The constant symbol `1` is the
  case `χ = 1`, so the identity has output support in no closed proper subset
  (`not_tsupport_quantizeSchwartzValue_ofSpatial_one_subset`).
* **The displacement kernel of `1 + D_v`.** The symbol `1 + ⟪ξ, v⟫` (`onePlusInner v`) quantizes
  to `u - i ∂_v u` (`quantizeSchwartzValue_onePlusInner`). Its kernel, in the displacement
  variable `z = x - y`, is the tempered distribution `δ₀ - i ∂_v δ₀` (`displacementKernel v`):
  `Op(1 + ⟪ξ, v⟫) u (x)` is this distribution tested on `z ↦ u (x - z)`
  (`quantizeSchwartzValue_onePlusInner_eq_displacementKernel`). Its Fourier transform is the
  function `ζ ↦ 1 + ⟪2πζ, v⟫`, that is `1 + ⟪ξ, v⟫` in the angular frequency `ξ = 2πζ`
  (`fourier_displacementKernel`). Reversing the displacement sign gives the kernel of `-v`
  (`displacementKernel_neg_apply`), whose Fourier transform is `1 - ⟪ξ, v⟫`. On `ℝ` with `v = 1`,
  recovery at `ξ = 2` gives `3` (`tendsto_quantizeSchwartzValue_onePlusInner_two`), whereas the
  reversed sign would give `1 - 2 = -1` (`coefficient_onePlusInner_neg_two`).
* **The coordinate change `y = eˣ`.** On functions of `y > 0`, the operator with symbol `y² η²`
  is `y² D_y² = -y² ∂_y²`. Its principal symbol pulled back by the cotangent map of `y = eˣ` is
  `e^{2x} (e^{-x} ξ)² = ξ²`, but transporting the operator to `x` gives `-∂ₓ² + ∂ₓ`
  (`neg_exp_sq_mul_deriv_deriv_eq`), which sends `f(x) = x` to `1`, whereas `-∂ₓ²` sends it to `0`
  (`neg_deriv_deriv_add_deriv_ofReal`). On `ℝⁿ`, `-Δ + ∂_v` is the quantization of
  `‖ξ‖² + i ⟪ξ, v⟫` (`quantizeSchwartzValue_negLaplacian_add_ofInner`), and the difference
  `i ⟪ξ, v⟫` of the two full symbols is not smoothing for `v ≠ 0`
  (`not_isSmoothing_I_smul_ofInner`): equal principal symbols do not give a smoothing difference.
* **Square partitions.** Two equal cutoffs `χ₁ = χ₂ = 1 / √2` at a point form a square partition,
  `χ₁² + χ₂² = 1`, whereas their unsquared sum is `√2` (`inv_sqrt_two_sq_add_sq`).

## References

* R. Melrose, *Pseudodifferential operators on Euclidean space*, Chapter 2, MIT 18.199 (2008),
  §2.8, (2.75)–(2.77): recovery of the full symbol.
* R. Melrose, *Introduction to Microlocal Analysis*, §1.7 (Fourier injectivity) and §5.3
  (patching of local quantizations).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8
  (changes of coordinates).
-/

public section

noncomputable section

open Filter MeasureTheory Real SchwartzMap TemperedDistribution
open scoped ContDiff FourierTransform LineDeriv RealInnerProductSpace SchwartzMap Topology

namespace TauCeti.GlobalQuantizationExample

variable {n : ℕ}

/-! ### Spatial symbols -/

section Spatial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  {χ : CoordinateSpace n → ℝ} (hχ : ContDiff ℝ ∞ χ)

/-- The full quantization of the symbol `χ(x)` is multiplication by `χ`. -/
theorem quantizeSchwartzValue_ofSpatial_smul_id (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue
        (Symbol.ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
          (hχ.smul contDiff_const)).coefficient u x = χ x • u x := by
  rw [funext (Symbol.coefficient_ofSpatial _ _),
    quantizeSchwartzValue_comp_fst (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) u x,
    _root_.smul_apply, ContinuousLinearMap.id_apply]

/-- Testing the quantization of `χ(x)` on cut-off exponentials recovers `χ(x)`. -/
theorem tendsto_quantizeSchwartzValue_ofSpatial_smul_id_cutoffExponential
    (x ξ : CoordinateSpace n) {φ : 𝓢(CoordinateSpace n, ℂ)} (hφ : φ 0 = 1) (v : V) :
    Tendsto (fun ε ↦ Complex.exp (-(⟪x, ξ⟫ * Complex.I)) •
        quantizeSchwartzValue
          (Symbol.ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
            (hχ.smul contDiff_const)).coefficient (φ.cutoffExponential ε ξ v) x)
      (𝓝[≠] 0) (𝓝 (χ x • v)) := by
  simpa using Symbol.tendsto_quantizeSchwartzValue_cutoffExponential
    (Symbol.ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) (hχ.smul contDiff_const))
    x ξ hφ v

/-- **Output support of a spatial symbol.** For a closed set `K`, the quantization of `χ(x)` sends
every compactly supported Schwartz function to a function supported in `K` exactly when `χ`
vanishes outside `K`. -/
theorem tsupport_quantizeSchwartzValue_ofSpatial_smul_id_subset_iff [Nontrivial V]
    {K : Set (CoordinateSpace n)} (hK : IsClosed K) :
    (∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
        tsupport (quantizeSchwartzValue
          (Symbol.ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
            (hχ.smul contDiff_const)).coefficient u) ⊆ K) ↔
      ∀ x ∉ K, χ x = 0 := by
  rw [tsupport_quantizeSchwartzValue_subset_iff hK
    (fun x _ ↦ (Symbol.ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V)
      (hχ.smul contDiff_const)).continuous_coefficient_slice x)
    (fun x _ ↦ ⟨‖χ x • ContinuousLinearMap.id ℂ V‖, 0, fun ξ ↦ by simp⟩)]
  have hid : ContinuousLinearMap.id ℂ V ≠ 0 := by
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    exact fun h ↦ hw (by simpa using congr($h w))
  refine forall₂_congr fun x _ ↦ ?_
  simp only [Symbol.coefficient_ofSpatial, smul_eq_zero, hid, or_false, forall_const]

omit hχ in
/-- The constant symbol `1` is the spatial symbol of `χ = 1`: it has output support in no closed
proper subset. -/
theorem not_tsupport_quantizeSchwartzValue_ofSpatial_one_subset [Nontrivial V]
    {K : Set (CoordinateSpace n)} (hK : IsClosed K) (hKne : K ≠ Set.univ) :
    ¬∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u →
        tsupport (quantizeSchwartzValue
          (Symbol.ofSpatial (fun _ ↦ (1 : ℝ) • ContinuousLinearMap.id ℂ V)
            ((contDiff_const (c := (1 : ℝ))).smul contDiff_const)).coefficient u) ⊆ K := by
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem K).1 hKne
  exact fun h ↦ one_ne_zero
    ((tsupport_quantizeSchwartzValue_ofSpatial_smul_id_subset_iff (χ := fun _ ↦ (1 : ℝ))
      contDiff_const hK).1 h x hx)

end Spatial

/-! ### The displacement kernel of `1 + D_v` -/

section Displacement

/-- The symbol `1 + ⟪ξ, v⟫` of order `1`, the symbol of `1 + D_v = 1 - i ∂_v`. -/
def onePlusInner (v : CoordinateSpace n) : Symbol n ℂ ℂ 1 :=
  Symbol.inclusion zero_le_one (Symbol.const (ContinuousLinearMap.id ℂ ℂ)) + Symbol.ofInner v

@[simp]
theorem coefficient_onePlusInner (v : CoordinateSpace n)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (onePlusInner v).coefficient p = (1 + ((⟪p.2, v⟫ : ℝ) : ℂ)) • ContinuousLinearMap.id ℂ ℂ := by
  simp only [onePlusInner, Symbol.coefficient_add, Symbol.coefficient_inclusion,
    Symbol.coefficient_const, Symbol.coefficient_ofInner, Pi.add_apply]
  ext
  simp

/-- `1 + ⟪ξ, v⟫` quantizes to `u - i ∂_v u`. -/
theorem quantizeSchwartzValue_onePlusInner (v : CoordinateSpace n) (u : 𝓢(CoordinateSpace n, ℂ))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue (onePlusInner v).coefficient u x = u x - Complex.I * ∂_{v} u x := by
  rw [onePlusInner, Symbol.coefficient_add, Symbol.quantizeSchwartzValue_coefficient_add,
    Symbol.quantizeSchwartzValue_ofInner, Symbol.coefficient_inclusion]
  have h : (Symbol.const (ContinuousLinearMap.id ℂ ℂ) : Symbol n ℂ ℂ 0).coefficient =
      fun _ ↦ ContinuousLinearMap.id ℂ ℂ := funext (Symbol.coefficient_const _)
  rw [h, quantizeSchwartzValue_id, smul_eq_mul]
  ring

/-- The displacement kernel `δ₀ - i ∂_v δ₀` of `1 + D_v`. -/
def displacementKernel (v : CoordinateSpace n) : 𝓢'(CoordinateSpace n, ℂ) :=
  delta (0 : CoordinateSpace n) - Complex.I • ∂_{v} (delta (0 : CoordinateSpace n))

@[simp]
theorem displacementKernel_apply (v : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    displacementKernel v φ = φ 0 + Complex.I * ∂_{v} φ 0 := by
  simp [displacementKernel, sub_eq_add_neg]

/-- **The kernel of `1 + D_v`.** `Op(1 + ⟪ξ, v⟫) u (x)` is the displacement kernel `δ₀ - i ∂_v δ₀`
tested on `z ↦ u (x - z)`, the reflection `z ↦ u (-z)` of `u` translated by `x`. -/
theorem quantizeSchwartzValue_onePlusInner_eq_displacementKernel (v : CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (onePlusInner v).coefficient u x = displacementKernel v
      (compSubConstCLM ℂ x (compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) u)) := by
  rw [quantizeSchwartzValue_onePlusInner, displacementKernel_apply, lineDerivOp_compSubConstCLM]
  simp [lineDerivOp_compCLMOfContinuousLinearEquiv, LineDeriv.lineDerivOp_left_neg, sub_eq_add_neg]

/-- The angular-frequency slice `ζ ↦ 1 + ⟪2πζ, v⟫` of `1 + ⟪ξ, v⟫` has temperate growth. -/
theorem hasTemperateGrowth_one_add_inner (v : CoordinateSpace n) :
    (fun ζ : CoordinateSpace n ↦ 1 + ((⟪(2 * π) • ζ, v⟫ : ℝ) : ℂ)).HasTemperateGrowth := by
  fun_prop

/-- **The Fourier transform of the displacement kernel** is the function `ζ ↦ 1 + ⟪2πζ, v⟫`,
which is the symbol `1 + ⟪ξ, v⟫` in the angular frequency `ξ = 2πζ`. -/
theorem fourier_displacementKernel (v : CoordinateSpace n) :
    𝓕 (displacementKernel v) = (hasTemperateGrowth_one_add_inner v).toTemperedDistribution := by
  have hg : (fun ζ : CoordinateSpace n ↦ ((⟪ζ, v⟫ : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  ext g
  rw [displacementKernel, FourierTransform.fourier_sub, FourierTransform.fourier_smul,
    TemperedDistribution.fourier_lineDerivOp_eq, fourier_delta_zero]
  simp only [sub_apply, Measure.toTemperedDistribution_apply, smul_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul, Function.HasTemperateGrowth.toTemperedDistribution_apply]
  -- The first moment `⟪ζ, v⟫ g ζ` of the Schwartz function `g` is integrable.
  have hi : Integrable fun ζ : CoordinateSpace n ↦ ((⟪ζ, v⟫ : ℝ) : ℂ) * g ζ :=
    (SchwartzMap.smulLeftCLM ℂ _ g).integrable.congr
      (Eventually.of_forall fun ζ ↦ SchwartzMap.smulLeftCLM_apply_apply hg g ζ)
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub g.integrable ((hi.const_mul _).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun ζ ↦ ?_)
  simp only [real_inner_smul_left]
  push_cast
  linear_combination (-2 * π * (⟪ζ, v⟫ : ℂ) * g ζ) * Complex.I_sq

/-- **Reversing the displacement sign.** Testing the kernel of `-v` on `φ` is testing the kernel of
`v` on the reflection `z ↦ φ (-z)`, so reversing the displacement sign replaces `1 + ⟪ξ, v⟫` by
`1 - ⟪ξ, v⟫` (`fourier_displacementKernel` applied to `-v`). -/
theorem displacementKernel_neg_apply (v : CoordinateSpace n) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    displacementKernel (-v) φ =
      displacementKernel v (compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ) φ) := by
  simp [lineDerivOp_compCLMOfContinuousLinearEquiv, LineDeriv.lineDerivOp_left_neg]

/-- On `ℝ`, recovering the symbol `1 + ξ` at `ξ = 2` gives `3`. -/
theorem tendsto_quantizeSchwartzValue_onePlusInner_two (x : CoordinateSpace 1)
    {φ : 𝓢(CoordinateSpace 1, ℂ)} (hφ : φ 0 = 1) (w : ℂ) :
    Tendsto (fun ε ↦
        Complex.exp (-(⟪x, EuclideanSpace.single 0 2⟫ * Complex.I)) •
          quantizeSchwartzValue (onePlusInner (EuclideanSpace.single 0 1)).coefficient
            (φ.cutoffExponential ε (EuclideanSpace.single 0 2) w) x)
      (𝓝[≠] 0) (𝓝 (3 * w)) := by
  convert Symbol.tendsto_quantizeSchwartzValue_cutoffExponential
    (onePlusInner (EuclideanSpace.single 0 1)) x (EuclideanSpace.single 0 2) hφ w using 2
  simp [EuclideanSpace.inner_single_left]
  norm_num

/-- On `ℝ`, the reversed symbol `1 - ξ` of the kernel with reversed displacement sign takes the
value `-1` at `ξ = 2`. -/
theorem coefficient_onePlusInner_neg_two (x : CoordinateSpace 1) :
    (onePlusInner (-EuclideanSpace.single 0 1)).coefficient (x, EuclideanSpace.single 0 2) =
      (-1 : ℂ) • ContinuousLinearMap.id ℂ ℂ := by
  simp [EuclideanSpace.inner_single_left]
  norm_num

end Displacement

/-! ### The coordinate change `y = eˣ` -/

section Exp

/-- **Transporting `-y² ∂_y²` along `y = eˣ`.** For `g` twice continuously differentiable on
`y > 0` and `f = g ∘ exp`, the operator `-y² ∂_y² = y² D_y²`, whose symbol is `y² η²`, reads
`-∂ₓ² + ∂ₓ` in the coordinate `x`. Its principal part `-∂ₓ²` is the quantization of the pulled-back
principal symbol `e^{2x} (e^{-x} ξ)² = ξ²`; the first-order term `∂ₓ` is not. -/
theorem neg_exp_sq_mul_deriv_deriv_eq {g : ℝ → ℂ} (hg : ContDiffOn ℝ 2 g (Set.Ioi 0)) (x : ℝ) :
    -((Real.exp x ^ 2 : ℝ) : ℂ) * deriv (deriv g) (Real.exp x) =
      -deriv (deriv (g ∘ Real.exp)) x + deriv (g ∘ Real.exp) x := by
  have hopen : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hd : DifferentiableOn ℝ g (Set.Ioi 0) := hg.differentiableOn (by norm_num)
  have hd' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hopen).1 hg).2.2.differentiableOn (by norm_num)
  have hderiv : deriv (g ∘ Real.exp) = fun y ↦ (Real.exp y : ℂ) * deriv g (Real.exp y) := by
    funext y
    have hgy := (hd.differentiableAt (hopen.mem_nhds (Real.exp_pos y))).hasDerivAt
    rw [(hgy.scomp y (Real.hasDerivAt_exp y)).deriv, Complex.real_smul]
  have h2 : HasDerivAt (fun y ↦ (Real.exp y : ℂ) * deriv g (Real.exp y))
      ((Real.exp x : ℂ) * deriv g (Real.exp x) +
        (Real.exp x : ℂ) * ((Real.exp x : ℂ) * deriv (deriv g) (Real.exp x))) x := by
    have hgx := (hd'.differentiableAt (hopen.mem_nhds (Real.exp_pos x))).hasDerivAt
    have hc := hgx.scomp x (Real.hasDerivAt_exp x)
    rw [Complex.real_smul] at hc
    exact (Real.hasDerivAt_exp x).ofReal_comp.mul hc
  rw [hderiv, h2.deriv]
  push_cast
  ring

/-- On `f(x) = x`, the transported operator `-∂ₓ² + ∂ₓ` gives `1`, whereas `-∂ₓ²`, the quantization
of the pulled-back principal symbol `ξ²`, gives `0`. -/
theorem neg_deriv_deriv_add_deriv_ofReal (x : ℝ) :
    -deriv (deriv fun y : ℝ ↦ (y : ℂ)) x + deriv (fun y : ℝ ↦ (y : ℂ)) x = 1 ∧
      -deriv (deriv fun y : ℝ ↦ (y : ℂ)) x = 0 := by
  have h : deriv (fun y : ℝ ↦ (y : ℂ)) = fun _ ↦ 1 :=
    funext fun y ↦ (hasDerivAt_id y).ofReal_comp.deriv.trans (by simp)
  simp [h]

/-- `-Δ + ∂_v` is the quantization of the full symbol `‖ξ‖² + i ⟪ξ, v⟫`. -/
theorem quantizeSchwartzValue_negLaplacian_add_ofInner (v : CoordinateSpace n)
    (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue ((ClassicalSymbol.negLaplacian n ℂ).toSymbol +
        Symbol.inclusion one_le_two (Complex.I • Symbol.ofInner v)).coefficient u x =
      -Laplacian.laplacian u x + ∂_{v} u x := by
  rw [Symbol.coefficient_add, Symbol.quantizeSchwartzValue_coefficient_add,
    ClassicalSymbol.quantizeSchwartzValue_negLaplacian, Symbol.coefficient_inclusion,
    Symbol.coefficient_smul, quantizeSchwartzValue_smul_left, Symbol.quantizeSchwartzValue_ofInner,
    smul_smul]
  simp

/-- The difference `i ⟪ξ, v⟫` between the full symbol `‖ξ‖² + i ⟪ξ, v⟫` of the transported operator
and the pulled-back principal symbol `‖ξ‖²` is not smoothing for `v ≠ 0`: it has no order below
`1`. -/
theorem not_isSmoothing_I_smul_ofInner {v : CoordinateSpace n} (hv : v ≠ 0) :
    ¬(Complex.I • Symbol.ofInner v : Symbol n ℂ ℂ 1).IsSmoothing := by
  intro h
  obtain ⟨b, hb⟩ := Symbol.isSmoothing_iff.1 h 0
  refine Symbol.not_exists_coefficient_eq_ofInner_coefficient hv zero_lt_one
    ⟨-Complex.I • b, ?_⟩
  rw [Symbol.coefficient_smul, hb, Symbol.coefficient_smul, smul_smul]
  simp

end Exp

/-! ### Square partitions -/

/-- Two equal cutoffs `1 / √2` form a square partition, `(1 / √2)² + (1 / √2)² = 1`, whereas
their unsquared sum is `√2`. -/
theorem inv_sqrt_two_sq_add_sq :
    (√2)⁻¹ ^ 2 + (√2)⁻¹ ^ 2 = (1 : ℝ) ∧ (√2)⁻¹ + (√2)⁻¹ = √2 := by
  have h : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : (√2 : ℝ) ≠ 0 := by positivity
  constructor
  · rw [inv_pow, h]
    norm_num
  · field_simp
    linarith

end TauCeti.GlobalQuantizationExample

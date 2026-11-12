/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.RightQuantization
import TauCeti.Analysis.Fourier.Adjoint
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The adjoint of a quantization with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) with compact spatial support,
with values in operators between complex Hilbert spaces `V` and `W`. Its left quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`) has a
formal adjoint, which is again a left quantization: for the adjoint symbol

`a*(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2πθ) dθ)†`,

where `â(θ, ξ)` is the Fourier transform of the position slice `x ↦ a(x, ξ)` and `†` is the Hilbert
space adjoint, `∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a*) v⟫` for all Schwartz functions `u` and `v`. In angular
frequency the formula reads `a*(y, ξ) = (2π)⁻ⁿ ∫ exp(-i ⟪y, η⟫) â(η / 2π, ξ - η)† dη`. The adjoint
symbol has order `m`, with estimates uniform in the position, but in general not compact spatial
support.

## Main declarations

* `TauCeti.Symbol.adjoint a ha`: the adjoint symbol `a*`, a symbol of order `m`, with its formula
  `TauCeti.Symbol.coefficient_adjoint`.
* `TauCeti.Symbol.isUniform_adjoint`: `a*` satisfies the symbol estimates uniformly in the
  position.
* `TauCeti.Symbol.spatialDeriv_adjoint`, `TauCeti.Symbol.frequencyDeriv_adjoint`: derivatives
  commute with taking adjoint symbols, `∂ (a*) = (∂ a)*`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`: the quantization of `a*` is the
  formal adjoint of the quantization of `a`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_sub_smul_le`: the decay of
  `â(θ, ξ - sθ)` in `θ`, uniformly for bounded shifts `s`, with the continuity, integrability and
  growth bound of the integrand `exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ)`
  (`HasCompactSpatialSupport.continuous_fourierChar_smul_fourier_slice_sub_smul`,
  `HasCompactSpatialSupport.integrable_fourierChar_smul_fourier_slice_sub_smul`,
  `HasCompactSpatialSupport.exists_norm_integral_fourierChar_smul_fourier_slice_sub_smul_le`).

The asymptotic expansion `a* ∼ ∑_α (1 / α!) ∂_ξ^α D_x^α a†` of the adjoint symbol is in
`TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion`.

## Construction

The adjoint symbol is the left symbol `TauCeti.Symbol.ofRight` of the right quantization of the
pointwise adjoint `a(y, ξ)†`. The Fourier transform of `x ↦ a(x, ξ)†` at `θ` is `â(-θ, ξ)†`, so the
formula for `a*` follows from that of `ofRight` by the substitution `θ ↦ -θ`. The order, the
uniform estimates and the derivative rules are those of `ofRight`.

The adjoint identity is proved on the Fourier side. Plancherel's theorem and the formula
`𝓕 (Op(a) u) η = ∫ â(η - ζ, 2πζ) û(ζ) dζ`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`) give
`∫ ⟪Op(a) u, v⟫ = ∫∫ ⟪â(η - ζ, 2πζ) û(ζ), v̂(η)⟫ dζ dη`. Expanding `⟪u, Op(a*) v⟫` produces an
absolutely convergent triple integral over `y`, `η` and `θ`, and integrating out `y` first turns it
into the same double integral, after the substitution `ζ = η - θ`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.7.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped SchwartzMap RealInnerProductSpace ContDiff

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

/-! ### Fourier transforms of the position slices -/

section Slice

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- The decay of `â(θ, ξ - sθ)` for bounded shifts: for a symbol of order `m` with compact spatial
support and every `R`, `‖â(θ, ξ - sθ)‖ ≤ C (1 + ‖θ‖) ^ (-(n + 1)) ⟨ξ⟩ ^ m` for all `|s| ≤ R`, which
is integrable in `θ`. The decay of `â` in its first variable absorbs the growth of Peetre's
inequality in the shift `sθ`. The adjoint symbol uses the shift `s = 2π`. -/
theorem HasCompactSpatialSupport.exists_norm_fourier_slice_sub_smul_le
    (ha : a.HasCompactSpatialSupport) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ θ ξ : CoordinateSpace n,
      ‖𝓕 (fun x ↦ a.coefficient (x, ξ - s • θ)) θ‖ ≤
        C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
  set c := max R 1
  have hc : 1 ≤ c := le_max_right R 1
  set k := ⌈|m|⌉₊
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le (n + 1 + k)
  refine ⟨C₀ * 2 ^ (|m| / 2) * c ^ |m|, by positivity, fun s hs θ ξ ↦ ?_⟩
  set t := 1 + ‖θ‖
  have ht : 0 < t := by positivity
  have h1 : 1 ≤ t := le_add_of_nonneg_right (norm_nonneg θ)
  -- Peetre's inequality for the shift by `sθ`, whose size is at most that of `cθ`.
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub m (ξ - s • θ) ξ
  rw [sub_sub_cancel_left, norm_neg] at hpeetre
  have hshift : (1 + ‖s • θ‖ ^ 2) ^ (|m| / 2) ≤ (1 + ‖c • θ‖ ^ 2) ^ (|m| / 2) := by
    gcongr
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg (zero_le_one.trans hc)]
    gcongr
    exact hs.trans (le_max_left R 1)
  have hscale := one_add_norm_smul_sq_rpow_le hc |m| θ
  rw [abs_abs] at hscale
  -- The bracket `⟨θ⟩ ^ |m|` is at most `(1 + ‖θ‖) ^ k`.
  have hbr : (1 + ‖θ‖ ^ 2) ^ (|m| / 2) ≤ t ^ k := by
    calc (1 + ‖θ‖ ^ 2) ^ (|m| / 2) ≤ t ^ |m| :=
          one_add_norm_sq_rpow_le_one_add_norm_rpow θ (abs_nonneg m)
      _ ≤ t ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil _)
      _ = t ^ k := Real.rpow_natCast t k
  have hF := hdecay θ (ξ - s • θ)
  have hpow : t ^ (-((n : ℝ) + 1)) * t ^ (n + 1 + k) = t ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht, ← Real.rpow_natCast]
    push_cast
    ring_nf
  have hkey : t ^ (n + 1 + k) * ‖𝓕 (fun x ↦ a.coefficient (x, ξ - s • θ)) θ‖ ≤
      t ^ (n + 1 + k) * (C₀ * 2 ^ (|m| / 2) * c ^ |m| *
        (t ^ (-((n : ℝ) + 1)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) := by
    refine hF.trans ?_
    calc C₀ * (1 + ‖ξ - s • θ‖ ^ 2) ^ (m / 2)
        ≤ C₀ * (2 ^ (|m| / 2) * (c ^ |m| * t ^ k) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          gcongr
          refine hpeetre.trans ?_
          gcongr
          exact hshift.trans (hscale.trans (by gcongr))
      _ = C₀ * 2 ^ (|m| / 2) * c ^ |m| *
            ((t ^ (-((n : ℝ) + 1)) * t ^ (n + 1 + k)) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) := by
          rw [hpow]
          ring
      _ = _ := by ring
  exact le_of_mul_le_mul_left hkey (by positivity)

/-- The Fourier transform `â(g t, h t)` of a position slice is continuous along continuous maps
`g`, `h` into the dual position variable and the frequency. -/
private theorem HasCompactSpatialSupport.continuous_fourier_slice_comp
    (ha : a.HasCompactSpatialSupport) {X : Type*} [TopologicalSpace X]
    {g h : X → CoordinateSpace n} (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t ↦ 𝓕 (fun x ↦ a.coefficient (x, h t)) (g t) :=
  (ha.continuous_fourier_slice.comp (hg.prodMk hh) :)


/-- The integrand `exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ)` of the adjoint symbol, with the frequency shift
`2πθ` scaled to `sθ`, is continuous in `θ`. -/
theorem HasCompactSpatialSupport.continuous_fourierChar_smul_fourier_slice_sub_smul
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (x ξ : CoordinateSpace n) :
    Continuous fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, ξ - s • θ)) θ := by
  have h₁ : Continuous fun θ : CoordinateSpace n ↦ (𝐞 ⟪θ, x⟫ : ℂ) :=
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).subtype_val
  have h₂ : Continuous fun θ : CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, ξ - s • θ)) θ := by
    exact ha.continuous_fourier_slice_comp continuous_id (by fun_prop)
  exact h₁.smul h₂

/-- The integrand `exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ)` of the adjoint symbol, with the frequency shift
`2πθ` scaled to `sθ`, is integrable in `θ`. -/
theorem HasCompactSpatialSupport.integrable_fourierChar_smul_fourier_slice_sub_smul
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (x ξ : CoordinateSpace n) :
    Integrable fun θ : CoordinateSpace n ↦
      (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, ξ - s • θ)) θ := by
  simpa only [neg_smul, ← sub_eq_add_neg] using
    ha.integrable_fourierChar_smul_fourier_slice_add_smul (-s) x ξ

/-- The integral `∫ exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ) dθ`, whose adjoint is the adjoint symbol for
`s = 2π`, grows at most like `⟨ξ⟩ ^ m`, uniformly in the position and in the shifts `|s| ≤ R`. -/
theorem HasCompactSpatialSupport.exists_norm_integral_fourierChar_smul_fourier_slice_sub_smul_le
    (ha : a.HasCompactSpatialSupport) (R : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ξ : CoordinateSpace n,
      ‖∫ θ, (𝐞 ⟪θ, x⟫ : ℂ) • 𝓕 (fun y ↦ a.coefficient (y, ξ - s • θ)) θ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_sub_smul_le R
  set I := ∫ θ : CoordinateSpace n, (1 + ‖θ‖) ^ (-((n : ℝ) + 1))
  have hI : 0 ≤ I := integral_nonneg fun θ ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun s hs x ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le ((integrable_one_add_norm_rpow_neg_add_one.mul_const
    ((1 + ‖ξ‖ ^ 2) ^ (m / 2))).const_mul C) (.of_forall fun θ ↦ ?_)).trans_eq ?_
  · rw [norm_smul, Circle.norm_coe, one_mul]
    exact hC s hs θ ξ
  · rw [integral_const_mul, integral_mul_const]
    ring

end Slice

/-! ### The adjoint symbol -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

/-- **The adjoint symbol.** For a symbol `a` of order `m` with compact spatial support, the symbol
`a*(y, ξ) = (∫ exp(2πi ⟪θ, y⟫) â(θ, ξ - 2πθ) dθ)†` of order `m`, where `â(θ, ξ)` is the Fourier
transform of the position slice `x ↦ a(x, ξ)` at `θ` (`TauCeti.Symbol.coefficient_adjoint`). It is
the left symbol `TauCeti.Symbol.ofRight` of the right quantization of the pointwise adjoint
`a(y, ξ)†`. Its quantization is the formal adjoint of the quantization of `a`
(`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`). -/
def adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) : Symbol n W V m :=
  (a.map adjointRealCLM).ofRight (ha.map _)

theorem coefficient_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (y ξ : CoordinateSpace n) :
    (adjoint a ha).coefficient (y, ξ) = ContinuousLinearMap.adjoint
      (∫ θ, (𝐞 ⟪θ, y⟫ : ℂ) • 𝓕 (fun x ↦ a.coefficient (x, ξ - (2 * π) • θ)) θ) := by
  rw [adjoint, coefficient_ofRight, ← ContinuousLinearMap.integral_adjoint,
    ← integral_neg_eq_self]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  simp only [coefficient_map, adjointRealCLM_apply, Real.fourier_adjoint, map_smulₛₗ,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, inner_neg_left, neg_neg, smul_neg,
    ← sub_eq_add_neg]

variable {a : Symbol n V W m}

/-- The adjoint symbol satisfies its estimates uniformly in the position, although it need not
have compact spatial support. -/
@[simp]
theorem isUniform_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) :
    (adjoint a ha).IsUniform :=
  isUniform_ofRight _

/-- A position derivative of the adjoint symbol is the adjoint symbol of the position
derivative: `∂_{y_j} a* = (∂_{x_j} a)*`. -/
@[simp]
theorem spatialDeriv_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (j : Fin n) :
    spatialDeriv j (adjoint a ha) = adjoint (spatialDeriv j a) (ha.spatialDeriv j) := by
  rw [adjoint, adjoint, spatialDeriv_ofRight]
  congr 1
  exact spatialDeriv_map _ a j

/-- A frequency derivative of the adjoint symbol is the adjoint symbol of the frequency
derivative: `∂_{ξ_j} a* = (∂_{ξ_j} a)*`. -/
@[simp]
theorem frequencyDeriv_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport)
    (j : Fin n) :
    frequencyDeriv j (adjoint a ha) = adjoint (frequencyDeriv j a) (ha.frequencyDeriv j) := by
  rw [adjoint, adjoint, frequencyDeriv_ofRight]
  congr 1
  exact frequencyDeriv_map _ a j

/-! ### The adjoint identity -/


/-- The integrand `exp(2πi ⟪η - θ, y⟫) ⟪â(θ, 2π(η - θ)) u(y), v̂(η)⟫` of the triple integral
giving `∫ ⟪u, Op(a*) v⟫`. -/
private def adjointIntegrand (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (y η θ : CoordinateSpace n) : ℂ :=
  (𝐞 ⟪η - θ, y⟫ : ℂ) *
    inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (u y)) (𝓕 v η)

/-- The pairing `⟪u(y), Op(a*) v (y)⟫` as an iterated integral. -/
private theorem HasCompactSpatialSupport.inner_quantizeSchwartzValue_adjoint
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (y : CoordinateSpace n) :
    inner ℂ (u y) (quantizeSchwartzValue (adjoint a ha).coefficient v y) =
      ∫ η, ∫ θ, adjointIntegrand a u v y η θ := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.1 (isUniform_adjoint a ha) [] []
  have hbound : ∀ ξ, ‖(adjoint a ha).coefficient (y, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) :=
    fun ξ ↦ by simpa [mixedDeriv_nil_nil] using hC y ξ
  rw [quantizeSchwartzValue_def, ← integral_inner (integrable_quantizeSchwartzValue_integrand
    ((adjoint a ha).continuous_coefficient_slice y).aestronglyMeasurable hbound (𝓕 v))]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hint := ha.integrable_fourierChar_smul_fourier_slice_add_smul (-(2 * π)) y ((2 * π) • η)
  simp only [neg_smul, ← sub_eq_add_neg] at hint
  dsimp only
  rw [Circle.smul_def, inner_smul_right, coefficient_adjoint,
    ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.integral_apply hint]
  rw [← integral_inner_left (hint.apply_continuousLinearMap (u y)), ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun θ ↦ ?_)
  simp only [smul_apply, inner_smul_left, adjointIntegrand, ← mul_assoc,
    ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul,
    ← sub_eq_add_neg, ← inner_sub_left, smul_sub]

omit [CompleteSpace V] [CompleteSpace W] in
/-- The triple integrand is integrable: `â(θ, 2π(η - θ))` decays in `θ` and grows like `⟨η⟩ ^ m`,
which `u` and `v̂` absorb. -/
private theorem HasCompactSpatialSupport.integrable_adjointIntegrand
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    Integrable (fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
      adjointIntegrand a u v q.1 q.2.1 q.2.2) (volume.prod (volume.prod volume)) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_norm_fourier_slice_add_smul_le (-(2 * π))
  have hg : Integrable (fun z : CoordinateSpace n × CoordinateSpace n ↦
      (1 + ‖z.1‖ ^ 2) ^ (m / 2) * ‖𝓕 v z.1‖ * (1 + ‖z.2‖) ^ (-((n : ℝ) + 1)))
      (volume.prod volume) :=
    ((𝓕 v).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).mul_prod
      integrable_one_add_norm_rpow_neg_add_one
  have hcont : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
      adjointIntegrand a u v q.1 q.2.1 q.2.2 := by
    have h₁ : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
        (𝐞 ⟪q.2.1 - q.2.2, q.1⟫ : ℂ) :=
      (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
    have h₂ : Continuous fun q : CoordinateSpace n × (CoordinateSpace n × CoordinateSpace n) ↦
        𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (q.2.1 - q.2.2))) q.2.2 :=
      ha.continuous_fourier_slice_comp (by fun_prop) (by fun_prop)
    exact h₁.mul ((h₂.clm_apply (u.continuous.comp continuous_fst)).inner
      ((𝓕 v).continuous.comp (by fun_prop)))
  refine ((u.integrable.norm.mul_prod hg).const_mul (C * (2 * π) ^ |m|)).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  obtain ⟨y, η, θ⟩ := q
  have hscale := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m η
  have hF : ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ‖ ≤
      C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * ((2 * π) ^ |m| * (1 + ‖η‖ ^ 2) ^ (m / 2))) := by
    rw [smul_sub, sub_eq_add_neg, ← neg_smul]
    refine (hC θ _).trans ?_
    rw [mul_assoc, mul_comm ((1 + ‖(2 * π) • η‖ ^ 2) ^ (m / 2))]
    gcongr
  simp only [adjointIntegrand, norm_mul, Circle.norm_coe, one_mul]
  calc ‖inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (u y)) (𝓕 v η)‖
      ≤ ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ‖ * ‖u y‖ * ‖𝓕 v η‖ :=
        (norm_inner_le_norm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ ≤ C * ((1 + ‖θ‖) ^ (-((n : ℝ) + 1)) * ((2 * π) ^ |m| * (1 + ‖η‖ ^ 2) ^ (m / 2))) *
          ‖u y‖ * ‖𝓕 v η‖ := by gcongr
    _ = C * (2 * π) ^ |m| * (‖u y‖ * ((1 + ‖η‖ ^ 2) ^ (m / 2) * ‖𝓕 v η‖ *
          (1 + ‖θ‖) ^ (-((n : ℝ) + 1)))) := by ring

/-- Integrating out the position: `∫ exp(2πi ⟪η - θ, y⟫) ⟪B u(y), w⟫ dy = ⟪B û(η - θ), w⟫`. -/
private theorem integral_adjointIntegrand (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (η θ : CoordinateSpace n) :
    ∫ y, adjointIntegrand a u v y η θ =
      inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ (𝓕 u (η - θ))) (𝓕 v η) := by
  set B := 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • (η - θ))) θ
  have hu : Integrable fun y : CoordinateSpace n ↦ (𝐞 (-⟪y, η - θ⟫) : ℂ) • u y :=
    u.integrable.norm.mono' ((Real.continuous_fourierChar.comp (by fun_prop)).subtype_val.smul
      u.continuous).aestronglyMeasurable
      (.of_forall fun y ↦ by rw [norm_smul, Circle.norm_coe, one_mul])
  have hfu : 𝓕 u (η - θ) = ∫ y, (𝐞 (-⟪y, η - θ⟫) : ℂ) • u y := by
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp only [Circle.smul_def]
  rw [hfu, ← ContinuousLinearMap.integral_comp_comm B hu,
    ← integral_inner_left (B.integrable_comp hu)]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [adjointIntegrand]
  rw [map_smul, inner_smul_left, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
    real_inner_comm]

omit [CompleteSpace V] in
/-- The pairing `∫ ⟪Op(a) u, v⟫` on the Fourier side, by Plancherel's theorem and the formula
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) û(ζ) dζ`. -/
private theorem HasCompactSpatialSupport.integral_inner_quantizeSchwartzValue_eq
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
      ∫ η, ∫ ζ, inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ))
        (𝓕 v η) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le 0
  set U : 𝓢(CoordinateSpace n, W) := (ha.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (a.contDiff_quantizeSchwartzValue u)
  have hU : ⇑U = quantizeSchwartzValue a.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [← hU, ← SchwartzMap.integral_inner_fourier_fourier]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  have hint : Integrable fun ζ : CoordinateSpace n ↦
      𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ) := by
    refine (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul
      (C * (2 * π) ^ |m|)).mono' ?_ (.of_forall fun ζ ↦ ?_)
    · exact ((ha.continuous_fourier_slice_comp (by fun_prop) (by fun_prop)).clm_apply
        (𝓕 u).continuous).aestronglyMeasurable
    · have hscale := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m ζ
      have h := hC (η - ζ) ((2 * π) • ζ)
      rw [pow_zero, one_mul] at h
      calc ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)‖
          ≤ ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ)‖ * ‖𝓕 u ζ‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * ‖𝓕 u ζ‖ := by
            gcongr
            exact h.trans (by gcongr)
        _ = C * (2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖) := by ring
  dsimp only
  rw [SchwartzMap.fourier_coe, hU, ha.fourier_quantizeSchwartzValue u η,
    ← integral_inner_left hint]

/-- **The adjoint of a quantization.** For a symbol `a` of order `m` with compact spatial support,
with values in operators between complex Hilbert spaces, the quantization of the adjoint symbol
`a*` is the formal adjoint of the quantization of `a`:
`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a*) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeSchwartzValue_adjoint (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
      ∫ x, inner ℂ (u x) (quantizeSchwartzValue (adjoint a ha).coefficient v x) := by
  have hG := ha.integrable_adjointIntegrand u v
  simp_rw [ha.inner_quantizeSchwartzValue_adjoint u v, ha.integral_inner_quantizeSchwartzValue_eq]
  calc ∫ η, ∫ ζ, inner ℂ (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)) (𝓕 v η)
      = ∫ η, ∫ θ, ∫ y, adjointIntegrand a u v y η θ := by
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp only [integral_adjointIntegrand]
        exact (integral_sub_left_eq_self (fun ζ ↦ inner ℂ
          (𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (η - ζ) (𝓕 u ζ)) (𝓕 v η)) volume η).symm.trans
            (by simp only [sub_sub_cancel])
    _ = ∫ q : CoordinateSpace n × CoordinateSpace n, ∫ y, adjointIntegrand a u v y q.1 q.2 :=
        (integral_prod _ hG.integral_prod_right).symm
    _ = ∫ y, ∫ q : CoordinateSpace n × CoordinateSpace n, adjointIntegrand a u v y q.1 q.2 :=
        (integral_integral_swap (f := fun y (q : CoordinateSpace n × CoordinateSpace n) ↦
          adjointIntegrand a u v y q.1 q.2) hG).symm
    _ = ∫ y, ∫ η, ∫ θ, adjointIntegrand a u v y η θ :=
        integral_congr_ae (hG.prod_right_ae.mono fun y hy ↦ integral_prod _ hy)

end Adjoint

end Symbol

end TauCeti

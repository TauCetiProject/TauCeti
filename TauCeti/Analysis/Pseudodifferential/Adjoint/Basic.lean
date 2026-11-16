/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Pseudodifferential.RightQuantization
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.Fourier.Adjoint
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The adjoint of a quantization

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) whose estimates hold uniformly
in the position (`TauCeti.Symbol.IsUniform`), with values in operators between complex Hilbert
spaces `V` and `W`. Its left quantization
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` (`TauCeti.quantizeSchwartzValue`) has a
formal adjoint on Schwartz space: the right quantization `Op_R(a†)` of the pointwise adjoint
`a(y, ξ)†` (`TauCeti.Symbol.quantizeRightUniformCLM`), with

`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op_R(a†) v⟫`

for all Schwartz functions `u` and `v`. If `a` has moreover compact spatial support, the formal
adjoint is again a left quantization: for the adjoint symbol

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
* `TauCeti.Symbol.integral_inner_quantizeUniformCLM`: for a uniform symbol `a`, `Op_R(a†)` is the
  formal adjoint of `Op(a)`, and dually `TauCeti.Symbol.integral_inner_quantizeRightUniformCLM`:
  `Op(c†)` is the formal adjoint of `Op_R(c)`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_adjoint`: the quantization of `a*` is the
  formal adjoint of the quantization of `a`, and
  `TauCeti.Symbol.coefficient_eq_adjoint_of_forall_integral_inner_eq`: `a*` is the only symbol, of
  any order, with this property.
* `TauCeti.Symbol.quantizeUniformCLM_adjoint`: as an operator on Schwartz space, the quantization
  of `a*` is the right quantization of the pointwise adjoint `a(x, ξ)†`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_sub_smul_le`: the decay of
  `â(θ, ξ - sθ)` in `θ`, uniformly for bounded shifts `s`, with the continuity, integrability and
  growth bound of the integrand `exp(2πi ⟪θ, x⟫) â(θ, ξ - sθ)`
  (`HasCompactSpatialSupport.continuous_fourierChar_smul_fourier_slice_sub_smul`,
  `HasCompactSpatialSupport.integrable_fourierChar_smul_fourier_slice_sub_smul`,
  `HasCompactSpatialSupport.exists_norm_integral_fourierChar_smul_fourier_slice_sub_smul_le`).

The asymptotic expansion `a* ∼ ∑_α (1 / α!) ∂_ξ^α D_x^α a†` of the adjoint symbol is in
`TauCeti.Analysis.Pseudodifferential.Adjoint.Expansion`, and the adjoint of a classical symbol in
`TauCeti.Analysis.Pseudodifferential.Adjoint.Classical`.

## Construction

The adjoint symbol is the left symbol `TauCeti.Symbol.ofRight` of the right quantization of the
pointwise adjoint `a(y, ξ)†`. The Fourier transform of `x ↦ a(x, ξ)†` at `θ` is `â(-θ, ξ)†`, so the
formula for `a*` follows from that of `ofRight` by the substitution `θ ↦ -θ`. The order, the
uniform estimates and the derivative rules are those of `ofRight`.

For a uniform symbol both sides of the adjoint identity equal the absolutely convergent double
integral `∫∫ exp(-2πi ⟪x, ζ⟫) ⟪a(x, 2πζ) û(ζ), v(x)⟫ dζ dx`. For the left side this is the formula
for `Op(a) u (x)`. For the right side, Plancherel's theorem gives
`∫ ⟪u, Op_R(a†) v⟫ = ∫ ⟪û, 𝓕 (Op_R(a†) v)⟫`, and the Fourier transform of `Op_R(a†) v` at `ζ` is
`∫ exp(-2πi ⟪x, ζ⟫) a(x, 2πζ)† v(x) dx` (`TauCeti.Symbol.fourier_quantizeRightUniformCLM`). The
integrand is bounded by `C ‖v(x)‖ ⟨2πζ⟩ ^ m ‖û(ζ)‖`, so Fubini's theorem applies. For a symbol with
compact spatial support, `Op(a*) = Op_R(a†)` on Schwartz space
(`TauCeti.Symbol.quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight`), which gives the adjoint
identity for `a*`.

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

/-! ### The adjoint symbol and the adjoint identity -/

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

/-- As an operator on Schwartz space, the quantization of the adjoint symbol `a*` is the right
quantization `TauCeti.Symbol.quantizeRightUniformCLM` of the pointwise adjoint `a(x, ξ)†`. -/
theorem quantizeUniformCLM_adjoint (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) :
    quantizeUniformCLM (adjoint a ha) (isUniform_adjoint a ha) =
      quantizeRightUniformCLM (a.map adjointRealCLM) (ha.isUniform.map _) :=
  (quantizeRightUniformCLM_eq_quantizeUniformCLM_ofRight (ha.map _)).symm

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

/-- The integrand `exp(-2πi ⟪x, ζ⟫) ⟪a(x, 2πζ) û(ζ), v(x)⟫` of the double integral to which both
sides of the adjoint identity reduce. -/
private def pairingIntegrand (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) (x ζ : CoordinateSpace n) : ℂ :=
  (𝐞 (-⟪x, ζ⟫) : ℂ) * inner ℂ (a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)) (v x)

omit [CompleteSpace V] [CompleteSpace W] in
/-- The double integrand is integrable: it is bounded by `C ‖v(x)‖ ⟨2πζ⟩ ^ m ‖û(ζ)‖`. -/
private lemma integrable_pairingIntegrand {a : Symbol n V W m} (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ pairingIntegrand a u v q.1 q.2)
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := ha.exists_bound_coefficient
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      pairingIntegrand a u v q.1 q.2 := by
    have h₁ : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (𝐞 (-⟪q.1, q.2⟫) : ℂ) :=
      (Real.continuous_fourierChar.comp (by fun_prop)).subtype_val
    have h₂ : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
        a.coefficient (q.1, (2 * π) • q.2) :=
      a.contDiff_coefficient.continuous.comp (by fun_prop)
    exact h₁.mul ((h₂.clm_apply ((𝓕 u).continuous.comp continuous_snd)).inner
      (v.continuous.comp continuous_fst))
  refine ((v.integrable.norm.mul_prod
    ((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m)).const_mul C).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  obtain ⟨x, ζ⟩ := q
  simp only [pairingIntegrand, norm_mul, Circle.norm_coe, one_mul]
  calc ‖inner ℂ (a.coefficient (x, (2 * π) • ζ) (𝓕 u ζ)) (v x)‖
      ≤ ‖a.coefficient (x, (2 * π) • ζ)‖ * ‖𝓕 u ζ‖ * ‖v x‖ :=
        (norm_inner_le_norm _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
    _ ≤ C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ * ‖v x‖ := by gcongr; exact hC _ _
    _ = C * (‖v x‖ * ((1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) := by ring

omit [CompleteSpace V] in
/-- The pairing `⟪Op(a) u (x), v(x)⟫` as an integral over the frequency. -/
private lemma inner_quantizeUniformCLM {a : Symbol n V W m} (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) (x : CoordinateSpace n) :
    inner ℂ (quantizeUniformCLM a ha u x) (v x) = ∫ ζ, pairingIntegrand a u v x ζ := by
  obtain ⟨C, -, hC⟩ := ha.exists_bound_coefficient
  rw [quantizeUniformCLM_apply, quantizeSchwartzValue_def, ← integral_inner_left
    (integrable_quantizeSchwartzValue_integrand
      (a.continuous_coefficient_slice x).aestronglyMeasurable (hC x) (𝓕 u))]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  simp only [pairingIntegrand]
  rw [Circle.smul_def, inner_smul_left, ← Circle.coe_inv_eq_conj,
    ← AddChar.map_neg_eq_inv, real_inner_comm]

/-- The pairing `⟪û(ζ), 𝓕 (Op_R(a†) v) (ζ)⟫` as an integral over the position. -/
private lemma inner_fourier_quantizeRightUniformCLM {a : Symbol n V W m} (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) (ζ : CoordinateSpace n) :
    inner ℂ (𝓕 u ζ) (𝓕 (quantizeRightUniformCLM (a.map adjointRealCLM) (ha.map _) v) ζ) =
      ∫ x, pairingIntegrand a u v x ζ := by
  rw [fourier_quantizeRightUniformCLM, Real.fourier_eq,
    ← integral_inner ((Real.fourierIntegral_convergent_iff ζ).2
      ((ha.map _).integrable_coefficient_apply v _))]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [pairingIntegrand]
  rw [Circle.smul_def, inner_smul_right, coefficient_map, adjointRealCLM_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- **The formal adjoint of a uniform quantization.** For a symbol `a` of order `m` whose estimates
are uniform in the position, with values in operators between complex Hilbert spaces, the right
quantization of the pointwise adjoint `a(y, ξ)†` is the formal adjoint of the quantization of `a`:
`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op_R(a†) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeUniformCLM (a : Symbol n V W m) (ha : a.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeUniformCLM a ha u x) (v x) =
      ∫ x, inner ℂ (u x) (quantizeRightUniformCLM (a.map adjointRealCLM) (ha.map _) v x) := by
  rw [← SchwartzMap.integral_inner_fourier_fourier u]
  simp_rw [inner_quantizeUniformCLM ha u v, inner_fourier_quantizeRightUniformCLM ha u v]
  exact integral_integral_swap (integrable_pairingIntegrand ha u v)

/-- **The formal adjoint of a uniform right quantization.** For a symbol `c` whose estimates are
uniform in the position, with values in operators between complex Hilbert spaces, the
quantization of the pointwise adjoint `c(x, ξ)†` is the formal adjoint of the right quantization
of `c`: `∫ ⟪Op_R(c) u, v⟫ = ∫ ⟪u, Op(c†) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeRightUniformCLM (c : Symbol n V W m) (hc : c.IsUniform)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeRightUniformCLM c hc u x) (v x) =
      ∫ x, inner ℂ (u x) (quantizeUniformCLM (c.map adjointRealCLM) (hc.map _) v x) := by
  have hcc : (c.map adjointRealCLM).map adjointRealCLM = c :=
    Symbol.ext (funext fun p ↦ by simp [adjointRealCLM_apply])
  have key := integral_inner_quantizeUniformCLM (c.map adjointRealCLM) (hc.map _) v u
  simp only [hcc] at key
  calc ∫ x, inner ℂ (quantizeRightUniformCLM c hc u x) (v x)
      = ∫ x, (starRingEnd ℂ) (inner ℂ (v x) (quantizeRightUniformCLM c hc u x)) := by
        simp_rw [inner_conj_symm]
    _ = (starRingEnd ℂ) (∫ x, inner ℂ (quantizeUniformCLM (c.map adjointRealCLM) (hc.map _) v x)
          (u x)) := by
        rw [integral_conj, key]
    _ = _ := by
        rw [← integral_conj]
        simp_rw [inner_conj_symm]

/-- **The adjoint of a quantization.** For a symbol `a` of order `m` with compact spatial support,
with values in operators between complex Hilbert spaces, the quantization of the adjoint symbol
`a*` is the formal adjoint of the quantization of `a`:
`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(a*) v⟫` for all Schwartz functions `u` and `v`. -/
theorem integral_inner_quantizeSchwartzValue_adjoint (a : Symbol n V W m)
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V))
    (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
      ∫ x, inner ℂ (u x) (quantizeSchwartzValue (adjoint a ha).coefficient v x) := by
  have h := integral_inner_quantizeUniformCLM a ha.isUniform u v
  rw [← quantizeUniformCLM_adjoint a ha] at h
  simpa only [quantizeUniformCLM_apply] using h

/-- **Uniqueness of the adjoint symbol.** A symbol `b`, of any order, whose quantization is the
formal adjoint of the quantization of `a` on compactly supported Schwartz functions,
`∫ ⟪Op(a) u, v⟫ = ∫ ⟪u, Op(b) v⟫`, has the coefficient of the adjoint symbol `a*`. -/
theorem coefficient_eq_adjoint_of_forall_integral_inner_eq (ha : a.HasCompactSpatialSupport)
    {m' : ℝ} {b : Symbol n W V m'}
    (h : ∀ (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)), HasCompactSupport u →
      HasCompactSupport v →
        ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (v x) =
          ∫ x, inner ℂ (u x) (quantizeSchwartzValue b.coefficient v x)) :
    b.coefficient = (adjoint a ha).coefficient := by
  refine coefficient_eq_of_forall_quantizeSchwartzValue_eq fun v hv ↦ funext fun x ↦ ?_
  have hf := (b.contDiff_quantizeSchwartzValue v).continuous
  have hf' := ((adjoint a ha).contDiff_quantizeSchwartzValue v).continuous
  -- Both quantizations have the same pairing with every `x ↦ g x • e`, `g` a smooth bump.
  refine ext_inner_left ℂ fun e ↦ ?_
  have hcont (f : CoordinateSpace n → V) (hf : Continuous f) :
      Continuous fun y ↦ inner ℂ e (f y) := continuous_const.inner hf
  refine congrFun (((hcont _ hf).ae_eq_iff_eq volume (hcont _ hf')).1
    (ae_eq_of_integral_contDiff_smul_eq (hcont _ hf).locallyIntegrable
      (hcont _ hf').locallyIntegrable fun g hg hgc ↦ ?_)) x
  have hu : HasCompactSupport fun y ↦ g y • e := hgc.smul_right
  have huc : ContDiff ℝ ∞ fun y ↦ g y • e := hg.smul contDiff_const
  simpa only [HasCompactSupport.toSchwartzMap_toFun, inner_smul_left_eq_smul] using
    (h (hu.toSchwartzMap huc) v hu hv).symm.trans
      (integral_inner_quantizeSchwartzValue_adjoint a ha (hu.toSchwartzMap huc) v)

end Adjoint

end Symbol

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Sobolev
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import TauCeti.Analysis.Pseudodifferential.OutputSupport
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre

/-!
# The composition symbol of two symbols

Let `a` be a symbol of order `m'` with values in `W →L[ℂ] U` and `b` a symbol of order `m` with
values in `V →L[ℂ] W` that vanishes for positions outside a compact set. Their **composition
symbol** is

`(a # b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη`,

where `b̂(η, ξ)` is the Fourier transform (with Mathlib's phase `exp(-2πi ⟪y, η⟫)`) of the
position slice `y ↦ b(y, ξ)`. This file shows that `a # b` is a symbol of order `m' + m`, and that
its quantization `Op(a # b) u` equals the Fourier integral defining `Op(a)`, evaluated on the
function `Op(b) u`. The composition symbol is the starting point of the symbol calculus of
composition: Taylor expanding `a(x, ξ + 2πη)` in `η` gives its asymptotic expansion
`∑_α (1 / α!) ∂_ξ^α a D_x^α b`, whose leading term is the pointwise composition `Symbol.comp`
(`TauCeti.Analysis.Pseudodifferential.Composition.Expansion`).

## Main results

* `TauCeti.Symbol.sharp`: the composition symbol `a # b`, a symbol of order `m' + m`, with its
  defining formula `TauCeti.Symbol.coefficient_sharp`.
* `TauCeti.Symbol.quantizeSchwartzValue_sharp`: **composition of quantizations**. For a Schwartz
  function `u`, `Op(a # b) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 (Op(b) u) ζ) dζ`, the Fourier
  integral defining `Op(a)` applied to the function `Op(b) u`.
* `TauCeti.Symbol.spatialDeriv_sharp`, `TauCeti.Symbol.coefficient_frequencyDeriv_sharp`: the
  Leibniz rules `∂(a # b) = (∂a) # b + a # (∂b)` for position and frequency derivatives.
* `TauCeti.Symbol.sharp_add`, `TauCeti.Symbol.add_sharp`, `TauCeti.Symbol.sharp_smul`,
  `TauCeti.Symbol.smul_sharp` and their companions: `a # b` is bilinear and compatible with the
  inclusions of symbol classes (`TauCeti.Symbol.inclusion_sharp`,
  `TauCeti.Symbol.sharp_inclusion`).
* `TauCeti.Symbol.IsSmoothing.sharp_right`, `TauCeti.Symbol.IsSmoothing.sharp_left`: the
  smoothing symbols form an ideal for `#`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_comp_fourier_slice_le`: the decay
  `‖a(x, ξ + y) ∘ b̂(η, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m) ⟨η⟩ ^ (-r)` of the integrand for frequency shifts
  `‖y‖ ≤ R ‖η‖`.
* `TauCeti.Symbol.sharpIntegrand`: the integrand `exp(2πi ⟪η, x⟫) a(x, ξ + sη) ∘ b̂(η, ξ)` with a
  scaled frequency shift, with its decay, continuity and integrability
  (`TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_sharpIntegrand_le` and its companions).
* `TauCeti.Symbol.exists_norm_mixedDeriv_le_of_leibniz`: the symbol estimates of a family of
  functions of two symbols which satisfies the Leibniz rules follow from its growth bound.
* `TauCeti.Symbol.HasCompactSpatialSupport.sharp`: if `a` also has compact spatial support, then
  so does `a # b`.
* `TauCeti.Symbol.coefficient_const_id_sharp`: the constant symbol `1` is a left identity,
  `1 # b = b`.
* `TauCeti.Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue`: `Op(a # b) u = Op(a) w`
  for the test function `w = Op(b) u`, and
  `TauCeti.Symbol.coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq`: `a # b` is the only
  symbol, of any order, whose quantization is `Op(a) ∘ Op(b)`.
* `TauCeti.Symbol.sharp_assoc`: **associativity**, `(a # b) # c = a # (b # c)` for `b` and `c` with
  compact spatial support, since both are the symbol of `Op(a) ∘ Op(b) ∘ Op(c)`.
* `TauCeti.Symbol.quantizeSobolev_sharp`: if `a` also has compact spatial support, then
  `Op(a # b) = Op(a) ∘ Op(b)` as operators between Bessel-potential spaces.

The facts used about `b̂` (rapid decay, joint continuity, differentiation in `ξ` and the formula
`(∂_{x_j} b)^(η, ξ) = 2πi ηⱼ b̂(η, ξ)`) are in `TauCeti.Analysis.Pseudodifferential.Sobolev`.

## Proof outline

By the rapid decay of `b̂` and Peetre's inequality `⟨ξ + 2πη⟩ ^ m' ≤ C ⟨ξ⟩ ^ m' ⟨η⟩ ^ |m'|`, the
integrand is bounded by `C ⟨ξ⟩ ^ (m' + m) ⟨η⟩ ^ (-(n + 1))`, locally uniformly in the position,
which gives the order-`m' + m` bound on `a # b` itself. A derivative of the integrand in a position
or frequency direction is the sum of the integrands for the pairs `(∂a, b)` and `(a, ∂b)`: in the
position, the derivative of the phase becomes `(∂_x b)^` by the formula above. Differentiating
under the integral sign therefore gives the Leibniz rules, smoothness follows by induction on the
order of differentiability, and the symbol estimates by induction on the number of derivatives,
each frequency derivative lowering the order of one of the two symbols by one. The composition of
quantizations follows from the formula `𝓕 (Op(b) u) ζ' = ∫ b̂(ζ' - ζ, 2πζ) (𝓕 u ζ) dζ`
(`HasCompactSpatialSupport.fourier_quantizeSchwartzValue`), Fubini's theorem for an integrand
dominated by a convolution of integrable functions, and the change of frequency `ζ' = ζ + η`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7).
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform
open scoped ContDiff RealInnerProductSpace SchwartzMap

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### Symbol estimates from the Leibniz rules -/

section Leibniz

/-- **Symbol estimates from the Leibniz rules.** Let `F a b hb` be a family of smooth functions of
the position and the frequency, indexed by a symbol `a` of order `m'` and a symbol `b` of order
`m` with compact spatial support, which satisfies the Leibniz rules
`∂ (F a b) = F (∂a) b + F a (∂b)` for the position and the frequency derivatives. If every member
is bounded by `C ⟨ξ⟩ ^ (m' + m - s)` for positions in a compact set, then so is every mixed
derivative `∂_x^α ∂_ξ^β (F a b)`, with the weight `⟨ξ⟩ ^ (m' + m - s - |β|)`: each frequency
derivative falls on one of the two symbols and lowers its order by one. -/
theorem exists_norm_mixedDeriv_le_of_leibniz (s : ℝ)
    (F : ∀ {m m' : ℝ}, Symbol n W U m' → (b : Symbol n V W m) → b.HasCompactSpatialSupport →
      CoordinateSpace n × CoordinateSpace n → V →L[ℂ] U)
    (hF : ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m}
      (hb : b.HasCompactSpatialSupport), ContDiff ℝ ∞ (F a b hb))
    (hspatial : ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m}
      (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n),
        coordinateDeriv [j] (fun y ↦ F a b hb (y, ξ)) x =
          F (spatialDeriv j a) b hb (x, ξ) + F a (spatialDeriv j b) (hb.spatialDeriv j) (x, ξ))
    (hfrequency : ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m}
      (hb : b.HasCompactSpatialSupport) (j : Fin n) (x ξ : CoordinateSpace n),
        coordinateDeriv [j] (fun η ↦ F a b hb (x, η)) ξ =
          F (frequencyDeriv j a) b hb (x, ξ) +
            F a (frequencyDeriv j b) (hb.frequencyDeriv j) (x, ξ))
    (hbound : ∀ {m m' : ℝ} (a : Symbol n W U m') {b : Symbol n V W m}
      (hb : b.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}, IsCompact K →
        ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖F a b hb (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - s) / 2))
    (a : Symbol n W U m') {b : Symbol n V W m} (hb : b.HasCompactSpatialSupport)
    (α β : List (Fin n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (F a b hb) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - s - β.length) / 2) := by
  obtain ⟨D, hD⟩ : ∃ D, α.length + β.length = D := ⟨_, rfl⟩
  induction D generalizing m m' α β with
  | zero =>
    obtain ⟨rfl, rfl⟩ : α = [] ∧ β = [] := by
      simpa [List.length_eq_zero_iff] using hD
    obtain ⟨C, hC0, hC⟩ := hbound a hb hK
    exact ⟨C, hC0, fun x hx ξ ↦ by simpa using hC x hx ξ⟩
  | succ D ih =>
    rcases List.eq_nil_or_concat' β with rfl | ⟨β', j, rfl⟩
    · rcases List.eq_nil_or_concat' α with rfl | ⟨α', j, rfl⟩
      · simp at hD
      · obtain ⟨C₁, hC₁0, hC₁⟩ := ih (spatialDeriv j a) hb α' [] (by simpa using hD)
        obtain ⟨C₂, hC₂0, hC₂⟩ := ih a (hb.spatialDeriv j) α' [] (by simpa using hD)
        refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
        have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
            coordinateDeriv [j] (fun y ↦ F a b hb (y, q.2)) q.1) =
              F (spatialDeriv j a) b hb + F a (spatialDeriv j b) (hb.spatialDeriv j) :=
          funext fun q ↦ hspatial a hb j q.1 q.2
        rw [← mixedDeriv_coordinateDeriv_fst (hF a hb), hfun]
        exact norm_mixedDeriv_add_le (hF _ hb) (hF a _) (hC₁ x hx ξ) (hC₂ x hx ξ)
    · have hlen : α.length + β'.length = D := by
        simp only [List.length_append, List.length_singleton] at hD
        omega
      obtain ⟨C₁, hC₁0, hC₁⟩ := ih (frequencyDeriv j a) hb α β' hlen
      obtain ⟨C₂, hC₂0, hC₂⟩ := ih a (hb.frequencyDeriv j) α β' hlen
      refine ⟨C₁ + C₂, add_nonneg hC₁0 hC₂0, fun x hx ξ ↦ ?_⟩
      have hfun : (fun q : CoordinateSpace n × CoordinateSpace n ↦
          coordinateDeriv [j] (fun η ↦ F a b hb (q.1, η)) q.2) =
            F (frequencyDeriv j a) b hb + F a (frequencyDeriv j b) (hb.frequencyDeriv j) :=
        funext fun q ↦ hfrequency a hb j q.1 q.2
      have e₁ : (m' - 1 + m - s - β'.length) / 2 = (m' + m - s - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have e₂ : (m' + (m - 1) - s - β'.length) / 2 = (m' + m - s - (β' ++ [j]).length) / 2 := by
        simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
        ring
      have h₁ := hC₁ x hx ξ
      have h₂ := hC₂ x hx ξ
      rw [e₁] at h₁
      rw [e₂] at h₂
      rw [← mixedDeriv_coordinateDeriv_snd, hfun]
      exact norm_mixedDeriv_add_le (hF _ hb) (hF a _) h₁ h₂

end Leibniz

/-! ### The integrand of the composition symbol -/

section Integrand

variable (a : Symbol n W U m') (b : Symbol n V W m)

/-- The integrand `exp(2πi ⟪η, x⟫) a(x, ξ + sη) ∘ b̂(η, ξ)` of the composition symbol with the
frequency shift `2πη` scaled to `sη`, where `b̂(η, ξ)` is the Fourier transform of the position
slice `y ↦ b(y, ξ)`. The integrand of `a # b` is the case `s = 2π`, and the cases `s = 2πt` with
`t ∈ [0, 1]` interpolate between the pointwise composition and `a # b`
(`TauCeti.Analysis.Pseudodifferential.Composition.Expansion`). -/
def sharpIntegrand (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n)
    (η : CoordinateSpace n) : V →L[ℂ] U :=
  (𝐞 ⟪η, p.1⟫ : ℂ) • (a.coefficient (p.1, p.2 + s • η)).comp
    (𝓕 (fun y ↦ b.coefficient (y, p.2)) η)

theorem sharpIntegrand_apply (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n)
    (η : CoordinateSpace n) :
    sharpIntegrand a b s p η = (𝐞 ⟪η, p.1⟫ : ℂ) • (a.coefficient (p.1, p.2 + s • η)).comp
      (𝓕 (fun y ↦ b.coefficient (y, p.2)) η) :=
  (rfl)

/-- The integrand `exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ)` of the composition symbol. -/
private def compIntegrand (p : CoordinateSpace n × CoordinateSpace n) (η : CoordinateSpace n) :
    V →L[ℂ] U :=
  sharpIntegrand a b (2 * π) p η

variable {a b}

/-- The integrand of the composition symbol in terms of the real bilinear map `(A, B) ↦ A ∘ B`. -/
private theorem compIntegrand_eq_bilinear (p : CoordinateSpace n × CoordinateSpace n)
    (η : CoordinateSpace n) :
    compIntegrand a b p η = (𝐞 ⟪η, p.1⟫ : ℂ) •
      (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
        (a.coefficient (p.1, p.2 + (2 * π) • η)) (𝓕 (fun y ↦ b.coefficient (y, p.2)) η) := by
  simp only [compIntegrand, sharpIntegrand_apply,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply, ContinuousLinearMap.compL_apply]

variable (a) in
/-- **Decay of the composition integrand.** For a symbol `b` with compact spatial support and a
frequency shift `y` with `‖y‖ ≤ R ‖η‖`, `R ≥ 1`, the composition `a(x, ξ + y) ∘ b̂(η, ξ)` decays in
`η` faster than every power, with the weight `⟨ξ⟩ ^ (m' + m)` in the frequency, uniformly for
positions in a compact set. -/
theorem HasCompactSpatialSupport.exists_norm_comp_fourier_slice_le
    (hb : b.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ)
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η y : CoordinateSpace n, ‖y‖ ≤ R * ‖η‖ →
      ‖(a.coefficient (x, ξ + y)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨Ca, hCa0, hCa⟩ := a.exists_bound_coefficient K hK
  obtain ⟨Cb, hCb0, hCb⟩ := hb.exists_norm_fourier_slice_le (r + |m'|)
  refine ⟨Ca * 2 ^ (|m'| / 2) * R ^ |m'| * Cb, by positivity, fun x hx ξ η y hy ↦ ?_⟩
  have hshift : (1 + ‖y‖ ^ 2) ^ (|m'| / 2) ≤ R ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2) := by
    have hy' : ‖y‖ ≤ ‖R • η‖ := by rwa [norm_smul, Real.norm_of_nonneg (zero_le_one.trans hR)]
    refine (Real.rpow_le_rpow (by positivity)
      (show 1 + ‖y‖ ^ 2 ≤ 1 + ‖R • η‖ ^ 2 by gcongr) (by positivity)).trans ?_
    simpa only [abs_abs] using one_add_norm_smul_sq_rpow_le hR |m'| η
  have hξ : (1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) =
      (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  have hη : (1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2) =
      (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  calc ‖(a.coefficient (x, ξ + y)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)‖
      ≤ ‖a.coefficient (x, ξ + y)‖ * ‖𝓕 (fun y ↦ b.coefficient (y, ξ)) η‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (Ca * (2 ^ (|m'| / 2) * (1 + ‖ξ‖ ^ 2) ^ (m' / 2) *
          (R ^ |m'| * (1 + ‖η‖ ^ 2) ^ (|m'| / 2)))) *
        (Cb * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2)) := by
        gcongr
        · exact (hCa x hx _).trans
            (by gcongr; exact (one_add_norm_add_sq_rpow_le_mul m' ξ y).trans (by gcongr))
        · exact hCb η ξ
    _ = Ca * 2 ^ (|m'| / 2) * R ^ |m'| * Cb *
          ((1 + ‖ξ‖ ^ 2) ^ (m' / 2) * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) *
          ((1 + ‖η‖ ^ 2) ^ (|m'| / 2) * (1 + ‖η‖ ^ 2) ^ (-(r + |m'|) / 2)) := by ring
    _ = _ := by rw [hξ, hη]

variable (a) in
/-- **Decay of the shifted composition integrand.** For frequency shifts `sη` with `|s| ≤ R`, the
integrand `sharpIntegrand a b s (x, ξ) η` decays in `η` faster than every power, with the weight
`⟨ξ⟩ ^ (m' + m)` in the frequency, uniformly in `s` and for positions in a compact set. -/
theorem HasCompactSpatialSupport.exists_norm_sharpIntegrand_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ∈ K, ∀ ξ η, ‖sharpIntegrand a b s (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_comp_fourier_slice_le a hK r hR
  refine ⟨C, hC0, fun s hs x hx ξ η ↦ ?_⟩
  rw [sharpIntegrand_apply, norm_smul, Circle.norm_coe, one_mul]
  refine hC x hx ξ η _ ?_
  rw [norm_smul, Real.norm_eq_abs]
  gcongr

/-- The shifted composition integrand is jointly continuous in the position, the frequency and the
integration variable. -/
theorem HasCompactSpatialSupport.continuous_sharpIntegrand (hb : b.HasCompactSpatialSupport)
    (s : ℝ) : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      sharpIntegrand a b s q.1 q.2 := by
  have he : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      (𝐞 ⟪q.2, q.1.1⟫ : ℂ) := by
    fun_prop
  have ha : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      a.coefficient (q.1.1, q.1.2 + s • q.2) :=
    a.contDiff_coefficient.continuous.comp (by fun_prop)
  have hB : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      𝓕 (fun y ↦ b.coefficient (y, q.1.2)) q.2 := by
    have h := hb.continuous_fourier_slice.comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst) :
        Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
          (q.2, q.1.2))
    simpa only [Function.comp_def] using h
  exact he.smul (ha.clm_comp hB)

/-- The shifted composition integrand is integrable. -/
theorem HasCompactSpatialSupport.integrable_sharpIntegrand (hb : b.HasCompactSpatialSupport)
    (s : ℝ) (p : CoordinateSpace n × CoordinateSpace n) : Integrable (sharpIntegrand a b s p) := by
  obtain ⟨C, -, hC⟩ := hb.exists_norm_sharpIntegrand_le a (isCompact_singleton (x := p.1))
    ((n : ℝ) + 1) (le_max_left 1 |s|)
  exact (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _).mono'
    ((hb.continuous_sharpIntegrand s).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (.of_forall fun η ↦ hC s (le_max_right 1 |s|) p.1 rfl p.2 η)

variable (a) in
/-- `‖∫ sharpIntegrand a b s (x, ξ) η dη‖ ≤ C ⟨ξ⟩ ^ (m' + m)`, uniformly for `|s| ≤ R` and
positions in a compact set. -/
theorem HasCompactSpatialSupport.exists_norm_integral_sharpIntegrand_le
    (hb : b.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)} (hK : IsCompact K) {R : ℝ}
    (hR : 1 ≤ R) :
    ∃ C, 0 ≤ C ∧ ∀ s : ℝ, |s| ≤ R → ∀ x ∈ K, ∀ ξ,
      ‖∫ η, sharpIntegrand a b s (x, ξ) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ := hb.exists_norm_sharpIntegrand_le a hK ((n : ℝ) + 1) hR
  set I := ∫ η : CoordinateSpace n, (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)
  have hI : 0 ≤ I := integral_nonneg fun η ↦ by positivity
  refine ⟨C * I, mul_nonneg hC0 hI, fun s hs x hx ξ ↦ ?_⟩
  refine (norm_integral_le_of_norm_le (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul
    (C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2))) (.of_forall fun η ↦ hC s hs x hx ξ η)).trans_eq ?_
  rw [integral_const_mul]
  ring

/-- The integrand of the composition symbol decays in `η` faster than every power, with the
weight `⟨ξ⟩ ^ (m' + m)` in the frequency, uniformly for positions in a compact set. -/
private theorem exists_norm_compIntegrand_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ η, ‖compIntegrand a b (x, ξ) η‖ ≤
      C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    hb.exists_norm_sharpIntegrand_le a hK r (R := 2 * π) (by linarith [Real.two_le_pi])
  exact ⟨C, hC0, hC (2 * π) (abs_of_pos Real.two_pi_pos).le⟩

private theorem continuous_compIntegrand (hb : b.HasCompactSpatialSupport) :
    Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      compIntegrand a b q.1 q.2 :=
  hb.continuous_sharpIntegrand (2 * π)

private theorem integrable_compIntegrand (hb : b.HasCompactSpatialSupport)
    (p : CoordinateSpace n × CoordinateSpace n) : Integrable (compIntegrand a b p) :=
  hb.integrable_sharpIntegrand (2 * π) p

/-- The integrand is dominated, for `p` in a neighbourhood of `p₀`, by a multiple of the
integrable weight `⟨η⟩ ^ (-(n + 1))`. -/
private theorem exists_norm_compIntegrand_le_weight (hb : b.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ C, 0 ≤ C ∧ ∀ p : CoordinateSpace n × CoordinateSpace n, p.1 ∈ Metric.closedBall p₀.1 1 →
      p.2 ∈ Metric.closedBall p₀.2 1 → ∀ η,
        ‖compIntegrand a b p η‖ ≤ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_compIntegrand_le (a := a) hb
    (isCompact_closedBall p₀.1 1) ((n : ℝ) + 1)
  have hw : Continuous fun ξ : CoordinateSpace n ↦ (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) :=
    (continuous_const.add (continuous_norm.pow 2)).rpow_const fun ξ ↦
      Or.inl (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 2).ne'
  obtain ⟨M, hM⟩ := (isCompact_closedBall p₀.2 1).exists_bound_of_continuousOn hw.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p₀.2 (Metric.mem_closedBall_self zero_le_one))
  refine ⟨C * M, mul_nonneg hC0 hM0, fun p hp₁ hp₂ η ↦ (hC p.1 hp₁ p.2 η).trans ?_⟩
  have hMp := (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hM p.2 hp₂))
  gcongr

variable (a b) in
/-- The coefficient `∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη` of the composition symbol. -/
private def compCoeff (p : CoordinateSpace n × CoordinateSpace n) : V →L[ℂ] U :=
  ∫ η, compIntegrand a b p η

private theorem continuous_compCoeff (hb : b.HasCompactSpatialSupport) :
    Continuous (compCoeff a b) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  obtain ⟨C, -, hC⟩ := exists_norm_compIntegrand_le_weight (a := a) hb p₀
  refine continuousAt_of_dominated
    (bound := fun η ↦ C * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2))
    (.of_forall fun p ↦ (integrable_compIntegrand hb p).aestronglyMeasurable) ?_
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul _)
    (.of_forall fun η ↦ ((continuous_compIntegrand hb).comp
      (continuous_id.prodMk continuous_const)).continuousAt)
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds
      (Metric.closedBall_mem_nhds p₀.1 one_pos),
    continuous_snd.continuousAt.preimage_mem_nhds (Metric.closedBall_mem_nhds p₀.2 one_pos)]
    with p hp₁ hp₂
  exact .of_forall (hC p hp₁ hp₂)

/-- **Growth of the composition coefficient.** `‖c(x, ξ)‖ ≤ C ⟨ξ⟩ ^ (m' + m)` uniformly for
positions in a compact set. -/
private theorem exists_norm_compCoeff_le (hb : b.HasCompactSpatialSupport)
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ, ‖compCoeff a b (x, ξ)‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m) / 2) := by
  obtain ⟨C, hC0, hC⟩ :=
    hb.exists_norm_integral_sharpIntegrand_le a hK (R := 2 * π) (by linarith [Real.two_le_pi])
  exact ⟨C, hC0, hC (2 * π) (abs_of_pos Real.two_pi_pos).le⟩

/-- The derivative of the integrand in the `j`-th position direction. The derivative of the phase
gives the Fourier transform of `∂_{x_j} b`, by `fourier_spatialDeriv_slice`. -/
private theorem coordinateDeriv_fst_compIntegrand (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ compIntegrand a b (x, ξ) η) x =
      compIntegrand (Symbol.spatialDeriv j a) b (x, ξ) η +
        compIntegrand a (Symbol.spatialDeriv j b) (x, ξ) η := by
  set ζ := ξ + (2 * π) • η
  set B := 𝓕 (fun y ↦ b.coefficient (y, ξ)) η
  set Φ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] U) :=
    (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  set Ψ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] U) := Φ.flip B
  have hA : HasFDerivAt (fun x ↦ a.coefficient (x, ζ))
      (fderiv ℝ (fun x ↦ a.coefficient (x, ζ)) x) x :=
    ((a.contDiff_coefficient_slice ζ).differentiable (by simp) x).hasFDerivAt
  have he := (Real.hasDerivAt_fourierChar ⟪η, x⟫).hasFDerivAt.comp x
    ((innerSL ℝ η).hasFDerivAt (x := x))
  have h : HasFDerivAt (fun x ↦ (𝐞 ⟪η, x⟫ : ℂ) • Ψ (a.coefficient (x, ζ))) _ x :=
    he.smul (Ψ.hasFDerivAt.comp x hA)
  have hf : (fun x ↦ compIntegrand a b (x, ξ) η) =
      fun x ↦ (𝐞 ⟪η, x⟫ : ℂ) • Ψ (a.coefficient (x, ζ)) :=
    funext fun x ↦ by rw [compIntegrand_eq_bilinear, ContinuousLinearMap.flip_apply]
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hf, h.fderiv]
  simp only [compIntegrand, sharpIntegrand_apply, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, Function.comp_apply,
    innerSL_apply_apply, Ψ, Φ, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.compL_apply, fderiv_coefficient_single, hb.fourier_spatialDeriv_slice,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.toSpanSingleton_apply]
  congr 1
  rw [smul_smul, Complex.real_smul]
  congr 1
  ring

/-- The derivative of the integrand in the `j`-th frequency direction. -/
private theorem coordinateDeriv_snd_compIntegrand (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (x ξ η : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ compIntegrand a b (x, ξ) η) ξ =
      compIntegrand (Symbol.frequencyDeriv j a) b (x, ξ) η +
        compIntegrand a (Symbol.frequencyDeriv j b) (x, ξ) η := by
  set c := (2 * π) • η
  set Φ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] U) :=
    (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have hD : HasFDerivAt (fun ζ ↦ a.coefficient (x, ζ))
      (fderiv ℝ (fun ζ ↦ a.coefficient (x, ζ)) (ξ + c)) (ξ + c) :=
    ((a.contDiff_coefficient.comp (contDiff_prodMk_right x)).differentiable (by simp)
      (ξ + c)).hasFDerivAt
  have hA : HasFDerivAt (fun ξ ↦ a.coefficient (x, ξ + c))
      ((fderiv ℝ (fun ζ ↦ a.coefficient (x, ζ)) (ξ + c)).comp (ContinuousLinearMap.id ℝ _)) ξ :=
    HasFDerivAt.comp (g := fun ζ ↦ a.coefficient (x, ζ)) (f := fun ξ ↦ ξ + c) ξ hD
      ((hasFDerivAt_id ξ).add_const c)
  have hB := hb.hasFDerivAt_fourier_slice η ξ
  have h : HasFDerivAt (fun ξ ↦ (𝐞 ⟪η, x⟫ : ℂ) •
      Φ (a.coefficient (x, ξ + c)) (𝓕 (fun y ↦ b.coefficient (y, ξ)) η)) _ ξ :=
    (hasFDerivAt_const (𝐞 ⟪η, x⟫ : ℂ) ξ).smul (Φ.hasFDerivAt_of_bilinear hA hB)
  have hf : (fun ξ ↦ compIntegrand a b (x, ξ) η) = fun ξ ↦ (𝐞 ⟪η, x⟫ : ℂ) •
      Φ (a.coefficient (x, ξ + c)) (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) :=
    funext fun ξ ↦ compIntegrand_eq_bilinear (x, ξ) η
  have hBj : (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ b.coefficient (y, ξ)) ξ)
      (EuclideanSpace.single j 1) =
        𝓕 (fun y ↦ (Symbol.frequencyDeriv j b).coefficient (y, ξ)) η := by
    rw [← hb.coordinateDeriv_fourier_slice, coordinateDeriv_cons, coordinateDeriv_nil, hB.fderiv]
  have hAj : fderiv ℝ (fun ζ ↦ a.coefficient (x, ζ)) (ξ + c) (EuclideanSpace.single j 1) =
      (Symbol.frequencyDeriv j a).coefficient (x, ξ + c) := by
    rw [coefficient_frequencyDeriv, coordinateDeriv_cons, coordinateDeriv_nil]
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hf, h.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.smulRight_apply, zero_apply, zero_smul,
    add_zero, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hAj, hBj, Φ,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply, compIntegrand, sharpIntegrand_apply]
  rw [smul_add, add_comm]

private theorem differentiableAt_compIntegrand (hb : b.HasCompactSpatialSupport)
    (η : CoordinateSpace n) (p : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (fun p ↦ compIntegrand a b p η) p := by
  set Φ : (W →L[ℂ] U) →L[ℝ] (V →L[ℂ] W) →L[ℝ] (V →L[ℂ] U) :=
    (ContinuousLinearMap.compL ℂ V W U).bilinearRestrictScalars ℝ
  have he : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪η, p.1⟫ : ℂ)) p :=
    DifferentiableAt.comp (g := fun t : ℝ ↦ (𝐞 t : ℂ))
      (f := fun p : CoordinateSpace n × CoordinateSpace n ↦ ⟪η, p.1⟫) p
      (Real.differentiable_fourierChar _)
      (((innerSL ℝ η).differentiableAt).comp p differentiableAt_fst)
  have hA : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      a.coefficient (p.1, p.2 + (2 * π) • η)) p :=
    (a.contDiff_coefficient.differentiable (by simp) _).comp p
      (differentiableAt_fst.prodMk (differentiableAt_snd.add_const _))
  have hB : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ b.coefficient (y, p.2)) η) p :=
    (hb.hasFDerivAt_fourier_slice η p.2).differentiableAt.comp p differentiableAt_snd
  have h : DifferentiableAt ℝ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪η, p.1⟫ : ℂ) • Φ (a.coefficient (p.1, p.2 + (2 * π) • η))
        (𝓕 (fun y ↦ b.coefficient (y, p.2)) η)) p :=
    he.smul ((Φ.differentiableAt.comp p hA).clm_apply hB)
  have hf : (fun p ↦ compIntegrand a b p η) = fun p : CoordinateSpace n × CoordinateSpace n ↦
      (𝐞 ⟪η, p.1⟫ : ℂ) • Φ (a.coefficient (p.1, p.2 + (2 * π) • η))
        (𝓕 (fun y ↦ b.coefficient (y, p.2)) η) :=
    funext fun p ↦ compIntegrand_eq_bilinear p η
  rw [hf]
  exact h

private theorem fderiv_compIntegrand_apply (hb : b.HasCompactSpatialSupport)
    (η : CoordinateSpace n) (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun p ↦ compIntegrand a b p η) p v =
      ∑ j, v.1 j • (compIntegrand (Symbol.spatialDeriv j a) b p η +
        compIntegrand a (Symbol.spatialDeriv j b) p η) +
      ∑ j, v.2 j • (compIntegrand (Symbol.frequencyDeriv j a) b p η +
        compIntegrand a (Symbol.frequencyDeriv j b) p η) := by
  rw [fderiv_apply_eq_sum_coordinateDeriv (differentiableAt_compIntegrand hb η p)]
  simp only [coordinateDeriv_fst_compIntegrand hb, coordinateDeriv_snd_compIntegrand hb,
    Prod.mk.eta]

private theorem continuous_fderiv_compIntegrand_apply (hb : b.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    Continuous fun η ↦ fderiv ℝ (fun p ↦ compIntegrand a b p η) p v := by
  have hc {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂}
      (hb' : b'.HasCompactSpatialSupport) : Continuous fun η ↦ compIntegrand a' b' p η :=
    Continuous.comp (g := fun q : (CoordinateSpace n × CoordinateSpace n) × CoordinateSpace n ↦
      compIntegrand a' b' q.1 q.2) (f := fun η ↦ (p, η)) (continuous_compIntegrand hb')
      (continuous_const.prodMk continuous_id)
  simp only [fderiv_compIntegrand_apply hb]
  refine (continuous_finsetSum _ fun j _ ↦ ?_).add (continuous_finsetSum _ fun j _ ↦ ?_)
  · have h₂ := hc a (hb.spatialDeriv j)
    fun_prop
  · have h₂ := hc a (hb.frequencyDeriv j)
    fun_prop


/-- The derivative of the integrand is dominated, for `p` near `p₀`, by a multiple of the
integrable weight `⟨η⟩ ^ (-(n + 1))`. -/
private theorem exists_norm_fderiv_compIntegrand_le (hb : b.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    ∃ D, ∀ p : CoordinateSpace n × CoordinateSpace n, p.1 ∈ Metric.closedBall p₀.1 1 →
      p.2 ∈ Metric.closedBall p₀.2 1 → ∀ η,
        ‖fderiv ℝ (fun p ↦ compIntegrand a b p η) p‖ ≤
          D * (1 + ‖η‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) := by
  choose C₁ _ hC₁ using fun j ↦
    exists_norm_compIntegrand_le_weight (a := Symbol.spatialDeriv j a) hb p₀
  choose C₂ _ hC₂ using fun j ↦
    exists_norm_compIntegrand_le_weight (a := a) (hb.spatialDeriv j) p₀
  choose C₃ _ hC₃ using fun j ↦
    exists_norm_compIntegrand_le_weight (a := Symbol.frequencyDeriv j a) hb p₀
  choose C₄ _ hC₄ using fun j ↦
    exists_norm_compIntegrand_le_weight (a := a) (hb.frequencyDeriv j) p₀
  refine ⟨∑ j, (C₁ j + C₂ j) + ∑ j, (C₃ j + C₄ j), fun p hp₁ hp₂ η ↦ ?_⟩
  refine ((fderiv ℝ (fun p ↦ compIntegrand a b p η) p).opNorm_le_of_apply_eq_sum _ _
    (fderiv_compIntegrand_apply hb η p)).trans ?_
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  gcongr with j
  · exact (norm_add_le _ _).trans
      ((add_le_add (hC₁ j p hp₁ hp₂ η) (hC₂ j p hp₁ hp₂ η)).trans_eq (by ring))
  · exact (norm_add_le _ _).trans
      ((add_le_add (hC₃ j p hp₁ hp₂ η) (hC₄ j p hp₁ hp₂ η)).trans_eq (by ring))

/-- Differentiation under the integral sign: the composition coefficient is differentiable, and
its derivative in a direction `v` is the integral of the derivative of the integrand. -/
private theorem hasFDerivAt_compCoeff (hb : b.HasCompactSpatialSupport)
    (p₀ : CoordinateSpace n × CoordinateSpace n) :
    DifferentiableAt ℝ (compCoeff a b) p₀ ∧ ∀ v, fderiv ℝ (compCoeff a b) p₀ v =
      ∫ η, fderiv ℝ (fun p ↦ compIntegrand a b p η) p₀ v := by
  obtain ⟨D, hD⟩ := exists_norm_fderiv_compIntegrand_le (a := a) hb p₀
  have hmeas : AEStronglyMeasurable (fun η ↦ fderiv ℝ (fun p ↦ compIntegrand a b p η) p₀) :=
    (continuous_clm_apply.2 (continuous_fderiv_compIntegrand_apply hb p₀)).aestronglyMeasurable
  have hball {p : CoordinateSpace n × CoordinateSpace n} (hp : p ∈ Metric.ball p₀ 1) :
      p.1 ∈ Metric.closedBall p₀.1 1 ∧ p.2 ∈ Metric.closedBall p₀.2 1 :=
    ⟨Metric.mem_closedBall.2 (((le_max_left _ _).trans (Prod.dist_eq).ge).trans
      (Metric.mem_ball.1 hp).le),
    Metric.mem_closedBall.2 (((le_max_right _ _).trans (Prod.dist_eq).ge).trans
      (Metric.mem_ball.1 hp).le)⟩
  have h : HasFDerivAt (compCoeff a b) _ p₀ := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun p η ↦ fderiv ℝ (fun p ↦ compIntegrand a b p η) p) (Metric.ball_mem_nhds p₀ one_pos)
    (.of_forall fun p ↦ (integrable_compIntegrand hb p).aestronglyMeasurable)
    (integrable_compIntegrand hb p₀) hmeas
    (.of_forall fun η p hp ↦ hD p (hball hp).1 (hball hp).2 η)
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul D)
    (.of_forall fun η p _ ↦ (differentiableAt_compIntegrand hb η p).hasFDerivAt)
  -- Instance search does not find `ContinuousENorm` on this space of operator-valued continuous
  -- linear maps by itself, so we provide its normed group structure.
  let : NormedAddCommGroup (CoordinateSpace n × CoordinateSpace n →L[ℝ] V →L[ℂ] U) :=
    inferInstance
  have hint : Integrable fun η ↦ fderiv ℝ (fun p ↦ compIntegrand a b p η) p₀ :=
    (integrable_one_add_norm_sq_rpow_neg_succ_div_two.const_mul D).mono' hmeas
      (.of_forall (hD p₀ (Metric.mem_closedBall_self zero_le_one)
        (Metric.mem_closedBall_self zero_le_one)))
  refine ⟨h.differentiableAt, fun v ↦ ?_⟩
  rw [h.fderiv, ContinuousLinearMap.integral_apply hint]

/-- The derivative of the composition coefficient in a direction `v`, in terms of the composition
coefficients of the derivatives of the two symbols. -/
private theorem fderiv_compCoeff_apply (hb : b.HasCompactSpatialSupport)
    (p v : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (compCoeff a b) p v =
      ∑ j, v.1 j • (compCoeff (Symbol.spatialDeriv j a) b p +
        compCoeff a (Symbol.spatialDeriv j b) p) +
      ∑ j, v.2 j • (compCoeff (Symbol.frequencyDeriv j a) b p +
        compCoeff a (Symbol.frequencyDeriv j b) p) := by
  have hi {m₁ m₂ : ℝ} (a' : Symbol n W U m₁) {b' : Symbol n V W m₂}
      (hb' : b'.HasCompactSpatialSupport) : Integrable (compIntegrand a' b' p) :=
    integrable_compIntegrand hb' p
  have hj₁ (j : Fin n) : Integrable fun η ↦ v.1 j • (compIntegrand (Symbol.spatialDeriv j a) b p η +
      compIntegrand a (Symbol.spatialDeriv j b) p η) :=
    ((hi (Symbol.spatialDeriv j a) hb).add (hi a (hb.spatialDeriv j))).smul (v.1 j)
  have hj₂ (j : Fin n) : Integrable fun η ↦
      v.2 j • (compIntegrand (Symbol.frequencyDeriv j a) b p η +
      compIntegrand a (Symbol.frequencyDeriv j b) p η) :=
    ((hi (Symbol.frequencyDeriv j a) hb).add (hi a (hb.frequencyDeriv j))).smul (v.2 j)
  rw [(hasFDerivAt_compCoeff hb p).2 v]
  simp only [fderiv_compIntegrand_apply hb]
  rw [integral_add (integrable_finsetSum _ fun j _ ↦ hj₁ j)
      (integrable_finsetSum _ fun j _ ↦ hj₂ j),
    integral_finsetSum _ fun j _ ↦ hj₁ j, integral_finsetSum _ fun j _ ↦ hj₂ j]
  congr 1
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul, integral_add (hi (Symbol.spatialDeriv j a) hb) (hi a (hb.spatialDeriv j))]
    rfl
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [integral_smul,
      integral_add (hi (Symbol.frequencyDeriv j a) hb) (hi a (hb.frequencyDeriv j))]
    rfl

/-- **Leibniz rule in the position** for the composition coefficient. -/
private theorem coordinateDeriv_fst_compCoeff (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun x ↦ compCoeff a b (x, ξ)) x =
      compCoeff (Symbol.spatialDeriv j a) b (x, ξ) +
        compCoeff a (Symbol.spatialDeriv j b) (x, ξ) := by
  rw [coordinateDeriv_fst_eq_fderiv (p := (x, ξ)) (hasFDerivAt_compCoeff hb (x, ξ)).1,
    fderiv_compCoeff_apply hb]
  simp [Finset.sum_add_distrib]

/-- **Leibniz rule in the frequency** for the composition coefficient. -/
private theorem coordinateDeriv_snd_compCoeff (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ compCoeff a b (x, ξ)) ξ =
      compCoeff (Symbol.frequencyDeriv j a) b (x, ξ) +
        compCoeff a (Symbol.frequencyDeriv j b) (x, ξ) := by
  rw [coordinateDeriv_snd_eq_fderiv (p := (x, ξ)) (hasFDerivAt_compCoeff hb (x, ξ)).1,
    fderiv_compCoeff_apply hb]
  simp [Finset.sum_add_distrib]

/-- The composition coefficient is smooth. -/
private theorem contDiff_compCoeff (hb : b.HasCompactSpatialSupport) :
    ContDiff ℝ ∞ (compCoeff a b) := by
  refine contDiff_infty.2 fun k ↦ ?_
  induction k generalizing m m' with
  | zero => exact contDiff_zero.2 (continuous_compCoeff hb)
  | succ k ih =>
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv_apply.2
      ⟨fun p ↦ (hasFDerivAt_compCoeff hb p).1, by simp, fun v ↦ ?_⟩
    simp only [fderiv_compCoeff_apply hb]
    exact (ContDiff.sum fun j _ ↦ ((ih (a := Symbol.spatialDeriv j a) hb).add
        (ih (a := a) (hb.spatialDeriv j))).const_smul _).add
      (ContDiff.sum fun j _ ↦ ((ih (a := Symbol.frequencyDeriv j a) hb).add
        (ih (a := a) (hb.frequencyDeriv j))).const_smul _)

/-- The symbol estimates of order `m' + m` for the composition coefficient, from its Leibniz
rules. -/
private theorem exists_bound_compCoeff (hb : b.HasCompactSpatialSupport) (α β : List (Fin n))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (compCoeff a b) x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' + m - β.length) / 2) := by
  simpa only [sub_zero] using exists_norm_mixedDeriv_le_of_leibniz 0 (fun a b _ ↦ compCoeff a b)
    (fun _ _ hb ↦ contDiff_compCoeff hb) (fun _ _ hb ↦ coordinateDeriv_fst_compCoeff hb)
    (fun _ _ hb ↦ coordinateDeriv_snd_compCoeff hb)
    (fun a _ hb _ hK ↦ by simpa only [sub_zero] using exists_norm_compCoeff_le (a := a) hb hK)
    a hb α β hK

end Integrand

/-! ### The composition symbol -/

section Sharp

variable {a : Symbol n W U m'} {b : Symbol n V W m}

variable (a b) in
/-- The **composition symbol** `a # b` of a symbol `a` of order `m'` and a symbol `b` of order `m`
with compact spatial support, a symbol of order `m' + m`:

`(a # b)(x, ξ) = ∫ exp(2πi ⟪η, x⟫) a(x, ξ + 2πη) ∘ b̂(η, ξ) dη`,

where `b̂(η, ξ)` is the Fourier transform of the position slice `y ↦ b(y, ξ)`. Its quantization
`Op(a # b) u` is the Fourier integral defining `Op(a)`, evaluated on the function `Op(b) u`
(`quantizeSchwartzValue_sharp`). It differs from the pointwise composition `Symbol.comp`, which
is only its leading term. -/
def sharp (hb : b.HasCompactSpatialSupport) : Symbol n V U (m' + m) where
  coefficient := compCoeff a b
  contDiff_coefficient := contDiff_compCoeff hb
  exists_bound _ hK α β := exists_bound_compCoeff hb α β hK

@[simp]
theorem coefficient_sharp (hb : b.HasCompactSpatialSupport) (x ξ : CoordinateSpace n) :
    (a.sharp b hb).coefficient (x, ξ) = ∫ η, (𝐞 ⟪η, x⟫ : ℂ) •
      (a.coefficient (x, ξ + (2 * π) • η)).comp (𝓕 (fun y ↦ b.coefficient (y, ξ)) η) :=
  (rfl)

/-- **Leibniz rule in the position** for the composition symbol. -/
theorem spatialDeriv_sharp (hb : b.HasCompactSpatialSupport) (j : Fin n) :
    Symbol.spatialDeriv j (a.sharp b hb) =
      (Symbol.spatialDeriv j a).sharp b hb + a.sharp (Symbol.spatialDeriv j b)
        (hb.spatialDeriv j) := by
  ext1
  funext ⟨x, ξ⟩
  rw [coefficient_spatialDeriv, coefficient_add, Pi.add_apply]
  exact coordinateDeriv_fst_compCoeff (a := a) hb j x ξ

/-- **Leibniz rule in the frequency** for the composition symbol. -/
theorem coefficient_frequencyDeriv_sharp (hb : b.HasCompactSpatialSupport) (j : Fin n)
    (x ξ : CoordinateSpace n) :
    (Symbol.frequencyDeriv j (a.sharp b hb)).coefficient (x, ξ) =
      ((Symbol.frequencyDeriv j a).sharp b hb).coefficient (x, ξ) +
        (a.sharp (Symbol.frequencyDeriv j b) (hb.frequencyDeriv j)).coefficient (x, ξ) := by
  rw [coefficient_frequencyDeriv]
  exact coordinateDeriv_snd_compCoeff (a := a) hb j x ξ

/-! ### Bilinearity, inclusions and the smoothing ideal -/

/-- The coefficient of `a # b` is the composition coefficient of `a` and `b`. -/
private theorem coefficient_sharp_eq_compCoeff (hb : b.HasCompactSpatialSupport) :
    (a.sharp b hb).coefficient = compCoeff a b :=
  (rfl)

/-- The composition coefficient depends only on the coefficients of the two symbols. -/
private theorem compCoeff_congr {m₁ m₂ k₁ k₂ : ℝ} {a₁ : Symbol n W U m₁} {a₂ : Symbol n W U m₂}
    {b₁ : Symbol n V W k₁} {b₂ : Symbol n V W k₂} (ha : a₁.coefficient = a₂.coefficient)
    (hb : b₁.coefficient = b₂.coefficient) : compCoeff a₁ b₁ = compCoeff a₂ b₂ := by
  funext p
  simp only [compCoeff, compIntegrand, sharpIntegrand_apply, ha, hb]

theorem add_sharp (a₁ a₂ : Symbol n W U m') (hb : b.HasCompactSpatialSupport) :
    (a₁ + a₂).sharp b hb = a₁.sharp b hb + a₂.sharp b hb := by
  ext1
  funext p
  rw [coefficient_add, Pi.add_apply, coefficient_sharp_eq_compCoeff,
    coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff, compCoeff, compCoeff, compCoeff,
    ← integral_add (integrable_compIntegrand hb p) (integrable_compIntegrand hb p)]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [compIntegrand, sharpIntegrand_apply, coefficient_add, Pi.add_apply,
    ContinuousLinearMap.add_comp, smul_add]

theorem sharp_add (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.HasCompactSpatialSupport) (hb₂ : b₂.HasCompactSpatialSupport) :
    a.sharp (b₁ + b₂) (hb₁.add hb₂) = a.sharp b₁ hb₁ + a.sharp b₂ hb₂ := by
  ext1
  funext p
  rw [coefficient_add, Pi.add_apply, coefficient_sharp_eq_compCoeff,
    coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff, compCoeff, compCoeff, compCoeff,
    ← integral_add (integrable_compIntegrand hb₁ p) (integrable_compIntegrand hb₂ p)]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [compIntegrand, sharpIntegrand_apply, hb₁.fourier_slice_add hb₂,
    ContinuousLinearMap.comp_add, smul_add]

@[simp]
theorem smul_sharp (c : ℂ) (a : Symbol n W U m') (hb : b.HasCompactSpatialSupport) :
    (c • a).sharp b hb = c • a.sharp b hb := by
  ext1
  funext p
  rw [coefficient_smul, Pi.smul_apply, coefficient_sharp_eq_compCoeff,
    coefficient_sharp_eq_compCoeff, compCoeff, compCoeff, ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [compIntegrand, sharpIntegrand_apply, coefficient_smul, Pi.smul_apply,
    ContinuousLinearMap.smul_comp, smul_comm c]

@[simp]
theorem sharp_smul (a : Symbol n W U m') (hb : b.HasCompactSpatialSupport) (c : ℂ) :
    a.sharp (c • b) (hb.smul c) = c • a.sharp b hb := by
  ext1
  funext p
  rw [coefficient_smul, Pi.smul_apply, coefficient_sharp_eq_compCoeff,
    coefficient_sharp_eq_compCoeff, compCoeff, compCoeff, ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [compIntegrand, sharpIntegrand_apply, hb.fourier_slice_smul,
    ContinuousLinearMap.comp_smul, smul_comm c]

@[simp]
theorem zero_sharp (hb : b.HasCompactSpatialSupport) : (0 : Symbol n W U m').sharp b hb = 0 := by
  simpa using smul_sharp (0 : ℂ) (0 : Symbol n W U m') hb

@[simp]
theorem sharp_zero (a : Symbol n W U m') :
    a.sharp (0 : Symbol n V W m) hasCompactSpatialSupport_zero = 0 := by
  simpa using sharp_smul a (hasCompactSpatialSupport_zero (m := m) (V := V)) 0

@[simp]
theorem neg_sharp (a : Symbol n W U m') (hb : b.HasCompactSpatialSupport) :
    (-a).sharp b hb = -a.sharp b hb := by
  simpa using smul_sharp (-1 : ℂ) a hb

@[simp]
theorem sharp_neg (a : Symbol n W U m') (hb : b.HasCompactSpatialSupport) :
    a.sharp (-b) hb.neg = -a.sharp b hb := by
  simpa using sharp_smul a hb (-1)

theorem sub_sharp (a₁ a₂ : Symbol n W U m') (hb : b.HasCompactSpatialSupport) :
    (a₁ - a₂).sharp b hb = a₁.sharp b hb - a₂.sharp b hb := by
  rw [sub_eq_add_neg, add_sharp, neg_sharp, ← sub_eq_add_neg]

theorem sharp_sub (a : Symbol n W U m') {b₁ b₂ : Symbol n V W m}
    (hb₁ : b₁.HasCompactSpatialSupport) (hb₂ : b₂.HasCompactSpatialSupport) :
    a.sharp (b₁ - b₂) (hb₁.sub hb₂) = a.sharp b₁ hb₁ - a.sharp b₂ hb₂ := by
  calc a.sharp (b₁ - b₂) (hb₁.sub hb₂) = a.sharp (b₁ + -b₂) (hb₁.add hb₂.neg) := by
        simp only [sub_eq_add_neg]
    _ = a.sharp b₁ hb₁ - a.sharp b₂ hb₂ := by
        rw [sharp_add a hb₁ hb₂.neg, sharp_neg, ← sub_eq_add_neg]

theorem inclusion_sharp {m'' : ℝ} (h : m' ≤ m'') (a : Symbol n W U m')
    (hb : b.HasCompactSpatialSupport) :
    (inclusion h a).sharp b hb = inclusion (by linarith) (a.sharp b hb) := by
  ext1
  rw [coefficient_inclusion, coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff]
  exact compCoeff_congr (coefficient_inclusion h a) rfl

theorem sharp_inclusion {m'' : ℝ} (h : m ≤ m'') (a : Symbol n W U m')
    (hb : b.HasCompactSpatialSupport) :
    a.sharp (inclusion h b) (hb.inclusion h) = inclusion (by linarith) (a.sharp b hb) := by
  ext1
  rw [coefficient_inclusion, coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff]
  exact compCoeff_congr rfl (coefficient_inclusion h b)

/-- Smoothing symbols form a right ideal for `#`: a smoothing symbol composed on the right with any
symbol with compact spatial support is smoothing. -/
theorem IsSmoothing.sharp_right (ha : a.IsSmoothing) (b : Symbol n V W m)
    (hb : b.HasCompactSpatialSupport) : (a.sharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨a', ha'⟩ := isSmoothing_iff.1 ha (m'' - m)
  refine ⟨Symbol.inclusion (by linarith) (a'.sharp b hb), ?_⟩
  rw [coefficient_inclusion, coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff]
  exact compCoeff_congr ha' rfl

/-- Smoothing symbols form a left ideal for `#`: any symbol composed on the right with a smoothing
symbol with compact spatial support is smoothing. -/
theorem IsSmoothing.sharp_left (hbs : b.IsSmoothing) (a : Symbol n W U m')
    (hb : b.HasCompactSpatialSupport) : (a.sharp b hb).IsSmoothing := isSmoothing_iff.2 fun m'' ↦ by
  obtain ⟨b', hb'⟩ := isSmoothing_iff.1 hbs (m'' - m')
  refine ⟨Symbol.inclusion (by linarith) (a.sharp b' (hb.of_coefficient_eq hb')), ?_⟩
  rw [coefficient_inclusion, coefficient_sharp_eq_compCoeff, coefficient_sharp_eq_compCoeff]
  exact compCoeff_congr rfl hb'

/-- If the left factor also has compact spatial support, then so does `a # b`. -/
theorem HasCompactSpatialSupport.sharp (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) : (a.sharp b hb).HasCompactSpatialSupport := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  exact hasCompactSpatialSupport_iff.2 ⟨K, hK, fun x hx ξ ↦ by simp [hKa x hx]⟩

/-- The constant symbol `1` is a left identity for the composition: `1 # b = b`. On the level of
coefficients this is the Fourier inversion formula `∫ exp(2πi ⟪η, x⟫) b̂(η, ξ) dη = b(x, ξ)`. -/
@[simp]
theorem coefficient_const_id_sharp [CompleteSpace W] (hb : b.HasCompactSpatialSupport) :
    ((const (ContinuousLinearMap.id ℂ W)).sharp b hb).coefficient = b.coefficient := by
  funext ⟨x, ξ⟩
  set f := hb.sliceSchwartz ξ
  have hf : (fun y ↦ b.coefficient (y, ξ)) = ⇑f := (hb.coe_sliceSchwartz ξ).symm
  have hinv : 𝓕⁻ (𝓕 ⇑f) = ⇑f := f.continuous.fourierInv_fourier_eq f.integrable
    (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).integrable)
  calc ((const (ContinuousLinearMap.id ℂ W)).sharp b hb).coefficient (x, ξ) = 𝓕⁻ (𝓕 ⇑f) x := by
        rw [coefficient_sharp, Real.fourierInv_eq, ← hf]
        refine integral_congr_ae (.of_forall fun η ↦ ?_)
        simp [coefficient_const, Circle.smul_def]
    _ = b.coefficient (x, ξ) := by rw [hinv, ← hf]

end Sharp

/-! ### The composition of the quantizations -/

section Operator

variable {a : Symbol n W U m'} {b : Symbol n V W m}

/-- The double integrand of `Op(a) (Op(b) u)`, after inserting the Fourier transform of `Op(b) u`
from `HasCompactSpatialSupport.fourier_quantizeSchwartzValue`, is integrable in both frequencies:
up to a phase it is `compIntegrand a b (x, 2πζ) (ζ' - ζ)` applied to `𝓕 u ζ`, so it is dominated
by a convolution-type product `h(ζ) k(ζ' - ζ)` of integrable functions. -/
private theorem integrable_composeIntegrand (hb : b.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.1, x⟫ •
      a.coefficient (x, (2 * π) • q.1)
        (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2)))
      (volume.prod volume) := by
  obtain ⟨C, -, hC⟩ := exists_norm_compIntegrand_le (a := a) hb (isCompact_singleton (x := x))
    ((n : ℝ) + 1)
  have hh : Integrable fun ζ : CoordinateSpace n ↦
      (1 + ‖(2 * π) • ζ‖ ^ 2) ^ ((m' + m) / 2) * ‖𝓕 u ζ‖ :=
    (𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) (m' + m)
  have hB : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) := by
    have h := hb.continuous_fourier_slice.comp (by fun_prop :
      Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ (q.1 - q.2, (2 * π) • q.2))
    simpa only [Function.comp_def] using h
  have hcont : Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ 𝐞 ⟪q.1, x⟫ •
      a.coefficient (x, (2 * π) • q.1)
        (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2)) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      (((a.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
        (hB.clm_apply ((𝓕 u).continuous.comp continuous_snd))))
  refine ((hh.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    integrable_one_add_norm_sq_rpow_neg_succ_div_two).const_mul C).mono'
    hcont.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  have hξ : (2 * π) • q.2 + (2 * π) • (q.1 - q.2) = (2 * π) • q.1 := by
    rw [← smul_add, add_sub_cancel]
  have h := hC x rfl ((2 * π) • q.2) (q.1 - q.2)
  rw [compIntegrand, sharpIntegrand_apply, norm_smul, Circle.norm_coe, one_mul, hξ] at h
  rw [Circle.norm_smul, ContinuousLinearMap.mul_apply']
  calc ‖a.coefficient (x, (2 * π) • q.1)
        (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2) (𝓕 u q.2))‖
      ≤ ‖(a.coefficient (x, (2 * π) • q.1)).comp
          (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2))‖ * ‖𝓕 u q.2‖ :=
        ((a.coefficient (x, (2 * π) • q.1)).comp
          (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • q.2)) (q.1 - q.2))).le_opNorm (𝓕 u q.2)
    _ ≤ C * (1 + ‖(2 * π) • q.2‖ ^ 2) ^ ((m' + m) / 2) *
          (1 + ‖q.1 - q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) * ‖𝓕 u q.2‖ := by gcongr
    _ = _ := by ring

/-- For fixed `ζ'`, the inner integrand `ζ ↦ b̂(ζ' - ζ, 2πζ) (𝓕 u ζ)` of `𝓕 (Op(b) u) ζ'` is
integrable. -/
private theorem integrable_fourier_slice_apply (hb : b.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (ζ' : CoordinateSpace n) :
    Integrable fun ζ ↦ 𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ) := by
  obtain ⟨Cb, _, hCb⟩ := hb.exists_norm_fourier_slice_le 0
  have hB : Continuous fun ζ : CoordinateSpace n ↦
      𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) (ζ' - ζ) := by
    have h := hb.continuous_fourier_slice.comp (by fun_prop :
      Continuous fun ζ : CoordinateSpace n ↦ (ζ' - ζ, (2 * π) • ζ))
    simpa only [Function.comp_def] using h
  refine (((𝓕 u).integrable_one_add_norm_smul_sq_rpow_mul_norm (2 * π) m).const_mul Cb).mono'
    (hB.clm_apply (𝓕 u).continuous).aestronglyMeasurable (.of_forall fun ζ ↦ ?_)
  refine ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
  have h := hCb (ζ' - ζ) ((2 * π) • ζ)
  simp only [neg_zero, zero_div, Real.rpow_zero, mul_one] at h
  calc _ ≤ Cb * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖ := by gcongr
    _ = _ := by ring

/-- **Composition of quantizations.** For a symbol `b` with compact spatial support, the
quantization of the composition symbol `a # b` is
`Op(a # b) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 (Op(b) u) ζ) dζ`: the defining Fourier
integral of `quantizeSchwartzValue a.coefficient`, evaluated on the function `Op(b) u` in place of
a Schwartz function. -/
theorem quantizeSchwartzValue_sharp [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp b hb).coefficient u x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ •
        a.coefficient (x, (2 * π) • ζ) (𝓕 (quantizeSchwartzValue b.coefficient u) ζ) := by
  set F : CoordinateSpace n → CoordinateSpace n → U := fun ζ' ζ ↦ 𝐞 ⟪ζ', x⟫ •
    a.coefficient (x, (2 * π) • ζ')
      (𝓕 (fun y ↦ b.coefficient (y, (2 * π) • ζ)) (ζ' - ζ) (𝓕 u ζ)) with hFdef
  have hF : Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦ F q.1 q.2)
      (volume.prod volume) := integrable_composeIntegrand hb u x
  have hR : (∫ ζ', 𝐞 ⟪ζ', x⟫ • a.coefficient (x, (2 * π) • ζ')
      (𝓕 (quantizeSchwartzValue b.coefficient u) ζ')) = ∫ ζ', ∫ ζ, F ζ' ζ := by
    refine integral_congr_ae (.of_forall fun ζ' ↦ ?_)
    beta_reduce
    rw [hb.fourier_quantizeSchwartzValue u ζ',
      ← (a.coefficient (x, (2 * π) • ζ')).integral_comp_comm
        (integrable_fourier_slice_apply hb u ζ')]
    simp only [hFdef, Circle.smul_def, integral_smul]
  rw [hR, integral_integral_swap hF, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  beta_reduce
  rw [← integral_add_right_eq_self (fun ζ' ↦ F ζ' ζ) ζ]
  rw [coefficient_sharp_eq_compCoeff, compCoeff,
    ContinuousLinearMap.integral_apply (integrable_compIntegrand hb _), Circle.smul_def,
    ← integral_smul]
  refine integral_congr_ae (.of_forall fun η ↦ ?_)
  simp only [hFdef, compIntegrand, sharpIntegrand_apply, add_sub_cancel_right, smul_add, smul_apply,
    ContinuousLinearMap.comp_apply, Circle.smul_def, smul_smul, inner_add_left,
    AddChar.map_add_eq_mul, Circle.coe_mul]
  rw [add_comm ((2 * π) • η), mul_comm]

/-- **Composition of quantizations**, as operators: for a symbol `b` with compact spatial support,
`Op(b) u` is a test function `w` for every Schwartz function `u`, and `Op(a # b) u = Op(a) w`. -/
theorem quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue [CompleteSpace W] [CompleteSpace U]
    (hb : b.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.sharp b hb).coefficient u x =
      quantizeSchwartzValue a.coefficient
        ((hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (b.contDiff_quantizeSchwartzValue u)) x := by
  have hw : ⇑((hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
      (b.contDiff_quantizeSchwartzValue u)) = quantizeSchwartzValue b.coefficient u :=
    funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  rw [quantizeSchwartzValue_sharp hb, quantizeSchwartzValue_def, SchwartzMap.fourier_coe, hw]

/-- **Uniqueness of the composition symbol.** A symbol `c`, of any order, whose quantization is
`Op(a) ∘ Op(b)` on compactly supported Schwartz functions has the coefficient of `a # b`. -/
theorem coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq [CompleteSpace V] [CompleteSpace W]
    [CompleteSpace U] (hb : b.HasCompactSpatialSupport) {m'' : ℝ} {c : Symbol n V U m''}
    (h : ∀ u : 𝓢(CoordinateSpace n, V), HasCompactSupport u → ∀ x,
      quantizeSchwartzValue c.coefficient u x = quantizeSchwartzValue a.coefficient
        ((hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
          (b.contDiff_quantizeSchwartzValue u)) x) :
    c.coefficient = (a.sharp b hb).coefficient :=
  coefficient_eq_of_forall_quantizeSchwartzValue_eq fun u hu ↦ funext fun x ↦
    (h u hu x).trans (quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb u x).symm

end Operator

/-! ### Associativity -/

section Assoc

variable {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℂ U'] [CompleteSpace V]
  [CompleteSpace W] [CompleteSpace U] [CompleteSpace U'] {m'' : ℝ}

/-- **Associativity of the composition symbol.** For symbols `b` and `c` with compact spatial
support, `(a # b) # c = a # (b # c)`, up to the identification of the orders
`(m'' + m') + m = m'' + (m' + m)`: both are the symbol of `Op(a) ∘ Op(b) ∘ Op(c)`. -/
theorem sharp_assoc (a : Symbol n U U' m'') {b : Symbol n W U m'} {c : Symbol n V W m}
    (hb : b.HasCompactSpatialSupport) (hc : c.HasCompactSpatialSupport) :
    (a.sharp b hb).sharp c hc =
      inclusion (add_assoc m'' m' m).ge (a.sharp (b.sharp c hc) (hb.sharp hc)) := by
  ext1
  rw [coefficient_inclusion]
  refine coefficient_eq_sharp_of_forall_quantizeSchwartzValue_eq (hb.sharp hc) fun u _ x ↦ ?_
  rw [quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hc,
    quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb]
  congr 1
  ext y
  simp only [HasCompactSupport.toSchwartzMap_toFun,
    quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hc]

end Assoc
/-! ### The composition on Bessel-potential spaces -/

section Sobolev

variable {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
  {a : Symbol n W U m'} {b : Symbol n V W m}

/-- **Composition of quantizations on Bessel-potential spaces.** For symbols `a` and `b` with
compact spatial support, the operator `Op(a # b) : H^s → H^{s - (m' + m)}` is the composition of
`Op(b) : H^s → H^{s - m}` and `Op(a) : H^{s - m} → H^{s - m - m'}`. -/
theorem quantizeSobolev_sharp (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (hab : (a.sharp b hb).HasCompactSpatialSupport) (s : ℝ) :
    (a.sharp b hb).quantizeSobolev hab s =
      BesselPotentialSpace.inclusion (by linarith) ∘L
        (a.quantizeSobolev ha (s - m) ∘L b.quantizeSobolev hb s) := by
  refine BesselPotentialSpace.continuousLinearMap_ext (p := 2) ENNReal.ofNat_ne_top fun u ↦
    BesselPotentialSpace.ext ?_
  -- On a Schwartz function `u`, `Op(b) u` is the test function `w`.
  set w := (hb.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (b.contDiff_quantizeSchwartzValue u)
  have hw : b.quantizeSobolev hb s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      SchwartzMap.toBesselPotentialSpaceCLM (s - m) 2 w := by
    refine BesselPotentialSpace.ext ?_
    ext φ
    simp only [toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
      SchwartzMap.toDistr_toBesselPotentialSpaceCLM,
      SchwartzMap.toTemperedDistributionCLM_apply_apply, w, HasCompactSupport.toSchwartzMap_toFun]
  ext φ
  simp only [ContinuousLinearMap.comp_apply, BesselPotentialSpace.toDistr_inclusion, hw,
    toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply,
    quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb, w]

end Sobolev

end Symbol

end TauCeti

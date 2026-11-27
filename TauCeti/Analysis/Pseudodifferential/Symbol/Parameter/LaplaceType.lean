/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Frequency.Cutoff
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Balakrishnan
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.BoundedSupport
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Differential
import TauCeti.Analysis.Complex.Sector.Bounds

/-!
# Seeley's cut-off symbol of a Laplace-type operator minus a spectral parameter

Let `P = ∑ i ∈ s, bᵢ(x) ∂^{vᵢ}` be a differential operator of order `2` on `ℝⁿ` of Laplace type:
its principal symbol is `q(x, ξ) • id` with `q` real and `q(x, ξ) ≥ μ ‖ξ‖²`, `μ > 0`. Seeley's
construction of the complex powers `P ^ (-σ)` integrates a parametrix of the resolvent
`(P - z)⁻¹` along the negative real axis (`TauCeti.ParameterSymbol.balakrishnanIntegral`), so it
needs the leading symbol `q(x, ξ) - z` to be elliptic with parameter
(`TauCeti.ParameterSymbol.IsElliptic`) on a set of spectral parameters containing the closed
negative real axis, including `z = 0`. This
fails at `(ξ, z) = (0, 0)`, where `q(x, ξ) - z` vanishes, and no symbol that is quasi-homogeneous
of degree `2` under `(ξ, z) ↦ (t ξ, t² z)` can avoid it. The remedy is to modify the leading symbol
near the origin, jointly in the frequency and the spectral parameter.

The modification is the *cutoff at the origin* `TauCeti.ParameterSymbol.originCutoff`, the symbol
`ψ(ξ, z) • id` for a smooth `ψ` with values in `[0, 1]`, equal to `1` where `‖ξ‖ ≤ 1` and `‖z‖ ≤ 1`
and to `0` where `‖ξ‖ ≥ 2` or `‖z‖ ≥ 2`. Its support is bounded in `(ξ, z)`, and such symbols are
smoothing (`TauCeti.ParameterSymbol.isSmoothing_ofBoundedSupport`): they have every order, because
the weight `1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` is bounded on their support. The corrected leading symbol

`a₀((x, ξ), z) = q(x, ξ) - z + ψ(ξ, z)`

has the following properties.

* It is elliptic with parameter on every open set of spectral parameters in a half plane
  `Re z ≤ r₀` with `r₀ ≤ min (1 / 8) (μ / 4)`
  (`TauCeti.ParameterSymbol.isElliptic_sub_spectralParameter_add_originCutoff`). For
  `0 < r₀ ≤ min (1 / 8) (μ / 4)` such a half plane contains a neighbourhood of the closed negative
  real axis.
* It is quasi-homogeneous of degree `2` above the radius `2`, since `ψ` vanishes there (the
  theorem `isQuasiHomogeneousAbove_sub_spectralParameter_add_originCutoff` in the namespace
  `TauCeti.ParameterSymbol.IsQuasiHomogeneous`). Along the negative real axis it is
  `q(x, ξ) + t` at such frequencies.
* Hence the Balakrishnan integral of its inverse is the power `q(x, ξ) ^ (-σ)` at frequencies
  `‖ξ‖ ≥ 2`, for `0 < σ < 1` (the theorem
  `coefficient_balakrishnanIntegral_inverse_sub_spectralParameter_add_originCutoff` in the
  namespace `TauCeti.ParameterSymbol`): this is the principal symbol `σ(P) ^ (-σ)` of the negative
  power.

For a differential operator of Laplace type the symbol of `P - z` is then the sum
`a₀ + a₁ + a₂ - ψ` (`TauCeti.ParameterSymbol.ofDifferentialSymbol_sub_spectralParameter_eq`), where
`a₁` and `a₂` are the symbols of the summands of orders `1` and `0`, quasi-homogeneous of degrees
`1` and `0` (`TauCeti.ParameterSymbol.isQuasiHomogeneous_ofDifferentialSymbol`), and the remainder
`ψ` is smoothing. This is the cut-off expansion of `P - z` from which Seeley's resolvent parametrix
is built: its leading term is elliptic with parameter on a neighbourhood of the negative real axis,
and every term is quasi-homogeneous at large frequencies.

## Main declarations

* `TauCeti.ParameterSymbol.originCutoff`: the cutoff `ψ(ξ, z) • id` at the origin.
* `TauCeti.ParameterSymbol.isElliptic_sub_spectralParameter_add_originCutoff`,
  `TauCeti.ParameterSymbol.isElliptic_ofDifferentialSymbol_sub_spectralParameter_add_originCutoff`:
  the corrected leading symbol of an operator of Laplace type is elliptic with parameter on half
  planes `Re z ≤ r₀`.
* `coefficient_balakrishnanIntegral_inverse_sub_spectralParameter_add_originCutoff`: the
  Balakrishnan integral of its inverse is `q(x, ξ) ^ (-σ)` at large frequencies.

## References

* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §§9–11.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-! ### The cutoff at the origin -/

/-- The profile `1 - χ(ξ, z)` of the cutoff at the origin, for the default frequency cutoff `χ` on
`ℝⁿ × ℂ` with its sup norm. -/
private theorem contDiff_originProfile :
    ContDiff ℝ ∞ fun p : (CoordinateSpace n × CoordinateSpace n) × ℂ =>
      1 - (default : FrequencyCutoff (CoordinateSpace n × ℂ)) (p.1.2, p.2) :=
  contDiff_const.sub ((default : FrequencyCutoff (CoordinateSpace n × ℂ)).contDiff.comp
    ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))

variable (V) in
/-- **The cutoff at the origin** `ψ(ξ, z) • id`, a smoothing parameter-dependent symbol. The
scalar `ψ = 1 - χ`, for the default frequency cutoff `χ` on `ℝⁿ × ℂ` with its sup norm, is smooth
with values in `[0, 1]`; it is `1` where `‖ξ‖ ≤ 1` and `‖z‖ ≤ 1`
(`TauCeti.ParameterSymbol.coefficient_originCutoff_of_norm_le_one`) and `0` where `‖ξ‖ ≥ 2` or
`‖z‖ ≥ 2` (`TauCeti.ParameterSymbol.coefficient_originCutoff_of_two_le_norm`). Added to the symbol
`q(x, ξ) - z` of an operator of Laplace type minus a spectral parameter, it makes it elliptic with
parameter near `(ξ, z) = (0, 0)`. -/
def originCutoff : ParameterSymbol n Λ V V m :=
  ofBoundedSupport
    (fun p => (((1 - (default : FrequencyCutoff (CoordinateSpace n × ℂ)) (p.1.2, p.2) : ℝ) :
      ℂ) • ContinuousLinearMap.id ℂ V))
    ((Complex.ofRealCLM.contDiff.comp contDiff_originProfile).smul contDiff_const) 2
    fun p hp => by
      rw [FrequencyCutoff.apply_eq_one_of_two_le_norm _ hp.le, sub_self, Complex.ofReal_zero,
        zero_smul]

@[simp]
theorem coefficient_originCutoff (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    (originCutoff V : ParameterSymbol n Λ V V m).coefficient ((x, ξ), z) =
      (((1 - (default : FrequencyCutoff (CoordinateSpace n × ℂ)) (ξ, z) : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ V) :=
  coefficient_ofBoundedSupport _ _ _ _ x ξ hz

/-- The cutoff at the origin is the identity where `‖ξ‖ ≤ 1` and `‖z‖ ≤ 1`. -/
theorem coefficient_originCutoff_of_norm_le_one (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    {z : ℂ} (hξ : ‖ξ‖ ≤ 1) (hz : ‖z‖ ≤ 1) (hzΛ : z ∈ Λ) :
    (originCutoff V : ParameterSymbol n Λ V V m).coefficient ((x, ξ), z) =
      ContinuousLinearMap.id ℂ V := by
  rw [coefficient_originCutoff x ξ hzΛ, FrequencyCutoff.apply_eq_zero_of_norm_le_one _
    (by rw [Prod.norm_def]; exact max_le hξ hz), sub_zero, Complex.ofReal_one, one_smul]

/-- The cutoff at the origin vanishes where `‖ξ‖ ≥ 2` or `‖z‖ ≥ 2`. -/
theorem coefficient_originCutoff_of_two_le_norm (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    {z : ℂ} (h : 2 ≤ ‖ξ‖ ∨ 2 ≤ ‖z‖) :
    (originCutoff V : ParameterSymbol n Λ V V m).coefficient ((x, ξ), z) = 0 := by
  by_cases hz : z ∈ Λ
  · rw [coefficient_originCutoff x ξ hz, FrequencyCutoff.apply_eq_one_of_two_le_norm _
      (by rw [Prod.norm_def]; exact le_max_iff.2 h), sub_self, Complex.ofReal_zero, zero_smul]
  · exact (originCutoff V).coefficient_of_notMem _ hz

/-- The value of the cutoff at the origin is a multiple `s • id` with `0 ≤ s ≤ 1`, and `s = 1` where
`‖ξ‖ ≤ 1` and `‖z‖ ≤ 1`. -/
theorem exists_coefficient_originCutoff_eq_smul (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ (‖ξ‖ ≤ 1 → ‖z‖ ≤ 1 → s = 1) ∧
      (originCutoff V : ParameterSymbol n Λ V V m).coefficient ((x, ξ), z) =
        (s : ℂ) • ContinuousLinearMap.id ℂ V := by
  set χ := (default : FrequencyCutoff (CoordinateSpace n × ℂ))
  refine ⟨1 - χ (ξ, z), sub_nonneg.2 (χ.le_one _), sub_le_self _ (χ.nonneg _),
    fun hξ hz' => ?_, coefficient_originCutoff x ξ hz⟩
  rw [χ.apply_eq_zero_of_norm_le_one (by rw [Prod.norm_def]; exact max_le hξ hz'), sub_zero]

theorem isSmoothing_originCutoff : (originCutoff V : ParameterSymbol n Λ V V m).IsSmoothing :=
  isSmoothing_ofBoundedSupport _ _ _ _

/-- The cutoff at the origin vanishes at frequencies of norm at least `2`, so it is
quasi-homogeneous of every degree above the radius `2`. -/
theorem isQuasiHomogeneousAbove_originCutoff (μ : ℝ) :
    (originCutoff V : ParameterSymbol n Λ V V m).IsQuasiHomogeneousAbove μ 2 := by
  refine isQuasiHomogeneousAbove_iff.2 fun x ξ hξ z _ t ht _ => ?_
  have htξ : 2 ≤ ‖t • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg ξ]
  rw [coefficient_originCutoff_of_two_le_norm x (.inl htξ),
    coefficient_originCutoff_of_two_le_norm x (.inl hξ), smul_zero]

/-! ### Parameter-ellipticity of the corrected leading symbol -/

/-- The pointwise estimate behind
`TauCeti.ParameterSymbol.isElliptic_sub_spectralParameter_add_originCutoff`: for
`q ≥ μ ‖ξ‖²`, a cutoff value `0 ≤ s` equal to `1` where `‖ξ‖ ≤ 1` and `‖z‖ ≤ 1`, and `z` in the
half plane `Re z ≤ r₀` with `8 r₀ ≤ 1` and `4 r₀ ≤ μ`, the modulus of `q + s - z` is at
least `κ w²` for `w = 1 + ‖ξ‖ + ‖z‖ ^ (1 / 2)` and `κ = (12 (1 + μ⁻¹ + (min 1 μ)⁻¹))⁻¹`. -/
private theorem mul_parameterWeight_sq_le_norm_ofReal_add_sub {q s μ r₀ : ℝ} (hμ : 0 < μ)
    {ξ : CoordinateSpace n} {z : ℂ} (hq : μ * ‖ξ‖ ^ 2 ≤ q) (hs : 0 ≤ s)
    (hs1 : ‖ξ‖ ≤ 1 → ‖z‖ ≤ 1 → s = 1) (h₁ : 8 * r₀ ≤ 1) (h₂ : 4 * r₀ ≤ μ)
    (hz : z.re ≤ r₀) :
    (12 * (1 + μ⁻¹ + (min 1 μ)⁻¹))⁻¹ * parameterWeight ξ z ^ 2 ≤ ‖((q + s : ℝ) : ℂ) - z‖ := by
  set δ := min 1 μ
  have hδ : 0 < δ := lt_min one_pos hμ
  have hq₀ : 0 ≤ q := (mul_nonneg hμ.le (sq_nonneg _)).trans hq
  -- Near the origin the cutoff is `1`; away from it, `q ≥ μ` or `‖z‖ ≥ 1`.
  have hcase : (δ ≤ q + s ∧ 4 * r₀ ≤ q + s) ∨ (1 ≤ ‖z‖) := by
    by_cases hξ : ‖ξ‖ ≤ 1
    · by_cases hz1 : ‖z‖ ≤ 1
      · rw [hs1 hξ hz1]
        exact .inl ⟨by linarith [min_le_left 1 μ], by linarith⟩
      · exact .inr (not_le.1 hz1).le
    · have : μ ≤ q := by
        have h1 : 1 ≤ ‖ξ‖ ^ 2 := one_le_pow₀ (not_le.1 hξ).le
        nlinarith
      exact .inl ⟨by linarith [min_le_right 1 μ], by linarith⟩
  have hδQ : δ ≤ q + s + ‖z‖ := by
    rcases hcase with h | h
    · linarith [norm_nonneg z]
    · linarith [min_le_left 1 μ]
  have hlow := Complex.add_norm_div_four_le_norm_ofReal_sub (Q := q + s) (by linarith) hz
    (hcase.imp (fun h => h.2) fun h => by linarith)
  have hw := parameterWeight_sq_le_mul_add_norm hμ hδ (q := q + s) (by linarith) hδQ
  calc (12 * (1 + μ⁻¹ + δ⁻¹))⁻¹ * parameterWeight ξ z ^ 2
      ≤ (12 * (1 + μ⁻¹ + δ⁻¹))⁻¹ * (3 * (1 + μ⁻¹ + δ⁻¹) * (q + s + ‖z‖)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (q + s + ‖z‖) / 4 := by field_simp; ring
    _ ≤ _ := hlow

/-- **Parameter-ellipticity of the corrected leading symbol.** Let `a` be a symbol of order `2`
whose value is `q(x, ξ) • id` with `q` real and `q(x, ξ) ≥ μ ‖ξ‖²`, `μ > 0`, as the principal
symbol of an operator of Laplace type. Then `a - z + ψ`, corrected by the cutoff at the origin
`ψ` (`TauCeti.ParameterSymbol.originCutoff`), is elliptic with parameter on every open set `Λ` of
spectral parameters in a half plane `Re z ≤ r₀` with `8 r₀ ≤ 1` and `4 r₀ ≤ μ`. For
`r₀ > 0` such a half plane contains a neighbourhood of the closed negative real axis, `0`
included, unlike the sectors of
`TauCeti.ParameterSymbol.exists_isElliptic_ofDifferentialSymbol_sub_spectralParameter`. -/
theorem isElliptic_sub_spectralParameter_add_originCutoff {a : ParameterSymbol n Λ V V 2}
    {q : CoordinateSpace n × CoordinateSpace n → ℝ} {μ r₀ : ℝ} (hμ : 0 < μ)
    (hq : ∀ x ξ, μ * ‖ξ‖ ^ 2 ≤ q (x, ξ))
    (ha : ∀ x ξ, ∀ z ∈ Λ, a.coefficient ((x, ξ), z) =
      (q (x, ξ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (h₁ : 8 * r₀ ≤ 1) (h₂ : 4 * r₀ ≤ μ) (hΛ : ∀ z ∈ Λ, z.re ≤ r₀) :
    (a - spectralParameter V + originCutoff V).IsElliptic := by
  set κ := (12 * (1 + μ⁻¹ + (min 1 μ)⁻¹))⁻¹
  have hκ : 0 < κ := inv_pos.2 (by have := lt_min one_pos hμ; positivity)
  have key (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
      ((a - spectralParameter V + originCutoff V).coefficient ((x, ξ), z)).IsInvertible ∧
        ‖((a - spectralParameter V + originCutoff V).coefficient ((x, ξ), z)).inverse‖ ≤
          κ⁻¹ * parameterWeight ξ z ^ (-2 : ℝ) := by
    obtain ⟨s, hs, -, hs1, hψ⟩ := exists_coefficient_originCutoff_eq_smul (V := V) (m := 2) x ξ hz
    have hval : (a - spectralParameter V + originCutoff V).coefficient ((x, ξ), z) =
        (((q (x, ξ) + s : ℝ) : ℂ) - z) • ContinuousLinearMap.id ℂ V := by
      rw [coefficient_add, coefficient_sub, Pi.add_apply, Pi.sub_apply, ha x ξ z hz,
        coefficient_spectralParameter x ξ hz, hψ, ← sub_smul, ← add_smul]
      push_cast
      ring_nf
    rw [hval]
    exact isInvertible_smul_id_and_norm_inverse_le V hκ
      (mul_parameterWeight_sq_le_norm_ofReal_add_sub hμ (hq x ξ) hs hs1 h₁ h₂ (hΛ z hz))
  exact ⟨fun x ξ z hz => (key x ξ hz).1, fun K _ => ⟨κ⁻¹, fun x _ ξ z hz => (key x ξ hz).2⟩⟩

/-- **Parameter-ellipticity of Seeley's corrected leading symbol of an operator of Laplace
type.** Let `P = ∑ i ∈ s, bᵢ(x) ∂^{vᵢ}` be a differential operator of order `2` with smooth
coefficients whose principal symbol is `q(x, ξ) • id` with `q` real and `q(x, ξ) ≥ μ ‖ξ‖²`,
`μ > 0`. Then the principal symbol minus `z`, corrected by the cutoff at the origin, is elliptic
with parameter on every open set `Λ` of spectral parameters in a half plane `Re z ≤ r₀` with
`8 r₀ ≤ 1` and `4 r₀ ≤ μ`. -/
theorem isElliptic_ofDifferentialSymbol_sub_spectralParameter_add_originCutoff {ι : Type*}
    {k : ι → ℕ} (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    (b : ι → CoordinateSpace n → V →L[ℂ] V) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ 2) {q : CoordinateSpace n × CoordinateSpace n → ℝ} {μ r₀ : ℝ}
    (hμ : 0 < μ) (hq : ∀ x ξ, μ * ‖ξ‖ ^ 2 ≤ q (x, ξ))
    (hprin : ∀ x ξ, differentialSymbol {i ∈ s | k i = 2} v b (x, ξ) =
      (q (x, ξ) : ℂ) • ContinuousLinearMap.id ℂ V)
    (h₁ : 8 * r₀ ≤ 1) (h₂ : 4 * r₀ ≤ μ) (hΛ : ∀ z ∈ Λ, z.re ≤ r₀) :
    (ofDifferentialSymbol 2 {i ∈ s | k i = 2} v b (fun i hi => hb i (Finset.mem_filter.1 hi).1)
        (fun i hi => hk i (Finset.mem_filter.1 hi).1) - spectralParameter V + originCutoff V :
      ParameterSymbol n Λ V V 2).IsElliptic :=
  isElliptic_sub_spectralParameter_add_originCutoff hμ hq
    (fun x ξ z hz => by rw [coefficient_ofDifferentialSymbol _ _ _ _ _ _ x ξ hz, hprin])
    h₁ h₂ hΛ

/-! ### Quasi-homogeneity and the cut-off expansion -/

/-- If `a` is quasi-homogeneous of degree `2`, the corrected leading symbol `a - z + ψ` is
quasi-homogeneous of degree `2` above the radius `2`, where the cutoff `ψ` at the origin
vanishes. -/
theorem IsQuasiHomogeneous.isQuasiHomogeneousAbove_sub_spectralParameter_add_originCutoff
    {a : ParameterSymbol n Λ V V 2} (ha : a.IsQuasiHomogeneous 2) :
    (a - spectralParameter V + originCutoff V).IsQuasiHomogeneousAbove 2 2 :=
  ((ha.sub isQuasiHomogeneous_spectralParameter).isQuasiHomogeneousAbove 2).add
    (isQuasiHomogeneousAbove_originCutoff 2)

/-- At frequencies of norm at least `2` the cutoff at the origin vanishes, so the corrected leading
symbol is `a - z` there. -/
theorem coefficient_sub_spectralParameter_add_originCutoff_of_two_le_norm
    {a : ParameterSymbol n Λ V V 2} (x : CoordinateSpace n) {ξ : CoordinateSpace n}
    (hξ : 2 ≤ ‖ξ‖) {z : ℂ} (hz : z ∈ Λ) :
    (a - spectralParameter V + originCutoff V).coefficient ((x, ξ), z) =
      a.coefficient ((x, ξ), z) - z • ContinuousLinearMap.id ℂ V := by
  rw [coefficient_add, coefficient_sub, Pi.add_apply, Pi.sub_apply,
    coefficient_spectralParameter x ξ hz, coefficient_originCutoff_of_two_le_norm x (.inl hξ),
    add_zero]

/-- **The cut-off expansion of `P - z`.** For a differential operator `P` of order `2` with smooth
coefficients, the symbol of `P - z` is `a₀ + a₁ + a₂ - ψ`, where `a₀` is the principal symbol
minus `z` corrected by the cutoff `ψ` at the origin, and `a₁`, `a₂` are the symbols of the
summands of orders `1` and `0`. The leading term `a₀` is elliptic with parameter near the
negative real axis for an operator of Laplace type
(`TauCeti.ParameterSymbol.isElliptic_ofDifferentialSymbol_sub_spectralParameter_add_originCutoff`)
and quasi-homogeneous of degree `2` above the radius `2`, `a₁` and `a₂` are quasi-homogeneous of
degrees `1` and `0` (`TauCeti.ParameterSymbol.isQuasiHomogeneous_ofDifferentialSymbol`), and `ψ`
is smoothing (`TauCeti.ParameterSymbol.isSmoothing_originCutoff`). -/
theorem ofDifferentialSymbol_sub_spectralParameter_eq {ι : Type*} {k : ι → ℕ} (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] V)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ 2) :
    (ofDifferentialSymbol 2 s v b hb hk - spectralParameter V : ParameterSymbol n Λ V V 2) =
      (ofDifferentialSymbol 2 {i ∈ s | k i = 2} v b
          (fun i hi => hb i (Finset.mem_filter.1 hi).1)
          (fun i hi => hk i (Finset.mem_filter.1 hi).1) - spectralParameter V + originCutoff V) +
        inclusion (by norm_num) (ofDifferentialSymbol 1 {i ∈ s | k i = 1} v b
          (fun i hi => hb i (Finset.mem_filter.1 hi).1)
          (fun i hi => (Finset.mem_filter.1 hi).2.le)) +
        inclusion (by norm_num) (ofDifferentialSymbol 0 {i ∈ s | k i = 0} v b
          (fun i hi => hb i (Finset.mem_filter.1 hi).1)
          (fun i hi => (Finset.mem_filter.1 hi).2.le)) -
        originCutoff V :=
  ext_of_mem fun x ξ z hz => by
    simp only [coefficient_sub, coefficient_add, coefficient_inclusion, Pi.sub_apply,
      Pi.add_apply, coefficient_ofDifferentialSymbol _ _ _ _ _ _ x ξ hz,
      differentialSymbol_eq_sum_range_filter 2 s v b hk (x, ξ), Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    abel

end ParameterSymbol

/-! ### The Balakrishnan integral of the corrected resolvent symbol -/

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V] {σ : ℝ}

/-- **The principal symbol of a negative power of an operator of Laplace type.** Let `a` be a
symbol of order `2` whose corrected leading symbol `a - z + ψ` is elliptic with parameter on a set
`Λ` of spectral parameters containing the closed negative real axis, as
`TauCeti.ParameterSymbol.isElliptic_sub_spectralParameter_add_originCutoff` provides when the
values of `a` are `q(x, ξ) • id` with `q(x, ξ) ≥ μ ‖ξ‖²`. Let `0 < σ < 1` (the hypothesis
`-2 - 2 σ + 2 < 0`). At a frequency `‖ξ‖ ≥ 2` where `a((x, ξ), z) = q • id` with `q > 0`, the
Balakrishnan integral of the inverse of `a - z + ψ` is the power `q ^ (-σ)`. For the principal
symbol of an operator `P` of Laplace type this is the principal symbol `σ(P)(x, ξ) ^ (-σ)` of
`P ^ (-σ)`, homogeneous of degree `-2 σ`. -/
theorem coefficient_balakrishnanIntegral_inverse_sub_spectralParameter_add_originCutoff
    (hΛ : ∀ t : ℝ, t ≤ 0 → (t : ℂ) ∈ Λ) (hσ : σ < 1) (hm : -2 - 2 * σ + 2 < 0)
    {a : ParameterSymbol n Λ V V 2} (h : (a - spectralParameter V + originCutoff V).IsElliptic)
    {x ξ : CoordinateSpace n} (hξ : 2 ≤ ‖ξ‖) {q : ℝ} (hq : 0 < q)
    (ha : ∀ z ∈ Λ, a.coefficient ((x, ξ), z) = (q : ℂ) • ContinuousLinearMap.id ℂ V) :
    (((a - spectralParameter V + originCutoff V).inverse h).balakrishnanIntegral hΛ hσ
      hm).coefficient (x, ξ) = (q ^ (-σ) : ℝ) • ContinuousLinearMap.id ℂ V := by
  rw [← ContinuousLinearMap.one_def]
  refine coefficient_balakrishnanIntegral_inverse_of_smul_one hΛ hσ (by linarith) hm h hq
    fun t ht ↦ ?_
  have hmem : -(t : ℂ) ∈ Λ := by simpa using hΛ (-t) (by linarith)
  rw [coefficient_sub_spectralParameter_add_originCutoff_of_two_le_norm x hξ hmem,
    ha _ hmem, ← ContinuousLinearMap.one_def, ← sub_smul, ← Complex.coe_smul]
  congr 1
  push_cast
  ring

end ParameterSymbol

end TauCeti

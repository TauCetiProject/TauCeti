/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.DifferentialSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Homogeneous

/-!
# Differential operators minus a spectral parameter

Let `P = ∑ i ∈ s, bᵢ(x) ∂^{vᵢ}` be a differential operator on `ℝⁿ` with smooth coefficients. Its
resolvent `(P - z)⁻¹` is approximated by pseudodifferential operators whose symbols are strongly
parameter-dependent (`TauCeti.ParameterSymbol`). This file shows that the symbol `p(x, ξ) - z` of
`P - z` belongs to that class, and that it is elliptic with parameter when `P` has order `2` and
is of Laplace type. Then `TauCeti.ParameterSymbol.inverse` gives a resolvent symbol of order `-2`,
and `TauCeti.ParameterSymbol.leftInverseTerms` and `TauCeti.ParameterSymbol.rightInverseTerms`
give the terms of Seeley's parametrix of `P - z`.

## Main results

* `TauCeti.ParameterSymbol.ofDifferentialSymbol`: the polynomial symbol
  `TauCeti.differentialSymbol s v b` of a differential operator of order at most `m` with smooth
  coefficients is a parameter-dependent symbol of order `m`, independent of `z`. An ordinary
  symbol of order `m` need not be one, since the class asks its frequency derivatives of order
  above `m` to decay in `z` as well; those of a polynomial of degree at most `m` vanish.
* `TauCeti.ParameterSymbol.isQuasiHomogeneous_ofDifferentialSymbol`: the symbol of summands all of
  order `d` is quasi-homogeneous of degree `d`.
* `TauCeti.ParameterSymbol.exists_isElliptic_ofDifferentialSymbol_sub_spectralParameter`:
  **parameter-ellipticity of `P - z`**. If the principal part of `P` has the real scalar symbol
  `q(x, ξ) • id` with `q(x, ξ) ≥ μ ‖ξ‖²`, `μ > 0`, and the coefficients of order at most `1` are
  bounded, then for every `c < 1` there is `R` such that `p(x, ξ) - z` is elliptic with parameter
  on every open set of spectral parameters in the sector `Re z ≤ c ‖z‖` and outside the ball of
  radius `R`. This covers `-∑ g^{jk}(x) ∂ⱼ ∂ₖ + ∑ βʲ(x) ∂ⱼ + γ(x)` with real `g` uniformly
  positive definite and matrix-valued `β`, `γ` bounded.

The bounds are uniform in the position because a symbol elliptic with parameter is invertible at
every position: the terms of order at most `1` are absorbed by the principal part only where they
are bounded independently of the position.

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open scoped ContDiff

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] {ι : Type*} {k : ι → ℕ}

/-- The symbol of the differential operator `u ↦ ∑ i ∈ s, bᵢ(x) (∂^{vᵢ} u)(x)` with smooth
coefficients `bᵢ`, where the summand `i` has order `k i ≤ m`, as a parameter-dependent symbol of
order `m` that does not depend on the spectral parameter. Its coefficient is the polynomial
`TauCeti.differentialSymbol s v b`
(`TauCeti.ParameterSymbol.coefficient_ofDifferentialSymbol`). -/
def ofDifferentialSymbol (m : ℕ) (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    (b : ι → CoordinateSpace n → V →L[ℂ] W) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ m) : ParameterSymbol n Λ V W m :=
  ∑ i ∈ s.attach, inclusion (by exact_mod_cast hk i i.property)
    (ofQuasiHomogeneous (m := k i) (fun p => differentialSymbol {i.val} v b p.1)
      ((contDiff_differentialSymbol _ v fun j hj =>
        Finset.mem_singleton.1 hj ▸ hb i i.property).comp
        contDiff_fst)
      fun t _ p => by
        rw [parameterDilation_apply, Real.rpow_natCast]
        exact differentialSymbol_smul_snd {i.val} v b (d := k i)
          (fun j hj => by rw [Finset.mem_singleton.1 hj]) p.1.1 p.1.2 t)

@[simp]
theorem coefficient_ofDifferentialSymbol (m : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ m) (x ξ : CoordinateSpace n)
    {z : ℂ} (hz : z ∈ Λ) :
    (ofDifferentialSymbol m s v b hb hk : ParameterSymbol n Λ V W m).coefficient ((x, ξ), z) =
      differentialSymbol s v b (x, ξ) := by
  simp only [ofDifferentialSymbol, coefficient_sum, Finset.sum_apply, coefficient_inclusion,
    coefficient_ofQuasiHomogeneous _ _ _ x ξ hz]
  rw [Finset.sum_attach s fun i => differentialSymbol {i} v b (x, ξ), differentialSymbol_def]
  exact Finset.sum_congr rfl fun i _ => differentialSymbol_singleton i v b (x, ξ)

/-- The symbol of a differential operator whose summands all have order `d` is quasi-homogeneous
of degree `d`: it is a homogeneous polynomial of degree `d` in the frequency, independent of the
spectral parameter. -/
theorem isQuasiHomogeneous_ofDifferentialSymbol (m : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ m) {d : ℕ} (hd : ∀ i ∈ s, k i = d) :
    (ofDifferentialSymbol m s v b hb hk : ParameterSymbol n Λ V W m).IsQuasiHomogeneous d :=
  IsQuasiHomogeneous.sum fun i _ => ((isQuasiHomogeneous_ofQuasiHomogeneous _ _ _).inclusion _
    ).congr_degree (by rw [hd i i.property])

/-- Splitting the summands of a differential operator by a predicate splits its symbol. -/
theorem ofDifferentialSymbol_filter_add_ofDifferentialSymbol_filter_not (m : ℕ) (s : Finset ι)
    (v : ∀ i, Fin (k i) → CoordinateSpace n) (b : ι → CoordinateSpace n → V →L[ℂ] W)
    (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i)) (hk : ∀ i ∈ s, k i ≤ m) (p : ι → Prop) [DecidablePred p] :
    (ofDifferentialSymbol m {i ∈ s | p i} v b (fun i hi => hb i (Finset.mem_filter.1 hi).1)
        (fun i hi => hk i (Finset.mem_filter.1 hi).1) : ParameterSymbol n Λ V W m) +
      ofDifferentialSymbol m {i ∈ s | ¬p i} v b (fun i hi => hb i (Finset.mem_filter.1 hi).1)
        (fun i hi => hk i (Finset.mem_filter.1 hi).1) =
      ofDifferentialSymbol m s v b hb hk :=
  ext_of_mem fun x ξ z hz => by
    simp only [coefficient_add, Pi.add_apply, coefficient_ofDifferentialSymbol _ _ _ _ _ _ x ξ hz,
      differentialSymbol_def, Finset.sum_filter_add_sum_filter_not]

/-! ### Operators of Laplace type -/

/-- A symbol `q • id` of order `2` with real `q ≥ μ ‖ξ‖²`, minus `z`, is invertible at spectral
parameters with `Re z ≤ c ‖z‖` and `‖z‖ ≥ 1`, with inverse bounded by `κ⁻¹ w⁻²` for the constant
`κ` of `TauCeti.ParameterSymbol.isInvertible_ofReal_sub_smul_id_and_norm_inverse_le`. -/
private theorem isInvertible_sub_spectralParameter_and_norm_inverse_le
    {a : ParameterSymbol n Λ V V 2} {μ c : ℝ} (hμ : 0 < μ) (hc : c < 1)
    (ha : ∀ x ξ, ∀ z ∈ Λ, ∃ q : ℝ, μ * ‖ξ‖ ^ 2 ≤ q ∧
      a.coefficient ((x, ξ), z) = (q : ℂ) • ContinuousLinearMap.id ℂ V)
    (hΛ : ∀ z ∈ Λ, z.re ≤ c * ‖z‖ ∧ 1 ≤ ‖z‖) (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :
    ((a - spectralParameter V).coefficient ((x, ξ), z)).IsInvertible ∧
      ‖((a - spectralParameter V).coefficient ((x, ξ), z)).inverse‖ ≤
        ((1 - max c (-1)) / 2 / (3 * (1 + μ⁻¹ + 1⁻¹)))⁻¹ * parameterWeight ξ z ^ (-2 : ℝ) := by
  obtain ⟨q, hq, h⟩ := ha x ξ z hz
  have hq₀ : 0 ≤ q := (mul_nonneg hμ.le (sq_nonneg _)).trans hq
  rw [coefficient_sub, Pi.sub_apply, coefficient_spectralParameter x ξ hz, h, ← sub_smul]
  exact isInvertible_ofReal_sub_smul_id_and_norm_inverse_le V hμ hc one_pos hq (hΛ z hz).1
    (by linarith [(hΛ z hz).2])

/-- The symbol of the summands of order at most `1`, with coefficients bounded by `B`, is at most
`D w` for `D = B ∑ᵢ ∏ⱼ ‖vᵢⱼ‖`. -/
private theorem norm_differentialSymbol_le_mul_parameterWeight {s : Finset ι}
    {v : ∀ i, Fin (k i) → CoordinateSpace n} {b : ι → CoordinateSpace n → V →L[ℂ] W} {B : ℝ}
    (hk : ∀ i ∈ s, k i ≤ 1) (hb : ∀ i ∈ s, ∀ x, ‖b i x‖ ≤ B) (x ξ : CoordinateSpace n) (z : ℂ) :
    ‖differentialSymbol s v b (x, ξ)‖ ≤
      (∑ i ∈ s, (∏ j, ‖v i j‖) * B) * parameterWeight ξ z := by
  rw [Finset.sum_mul]
  refine (norm_differentialSymbol_le _ v b x ξ).trans (Finset.sum_le_sum fun i hi => ?_)
  have hξ : ‖ξ‖ ^ k i ≤ parameterWeight ξ z := by
    have hki := hk i hi
    interval_cases k i
    · simpa using one_le_parameterWeight ξ z
    · simpa using norm_le_parameterWeight ξ z
  have hv : 0 ≤ ∏ j, ‖v i j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  calc ‖ξ‖ ^ k i * (∏ j, ‖v i j‖) * ‖b i x‖
      ≤ parameterWeight ξ z * (∏ j, ‖v i j‖) * B :=
        mul_le_mul (mul_le_mul_of_nonneg_right hξ hv) (hb i hi x) (norm_nonneg _)
          (mul_nonneg (parameterWeight_pos ξ z).le hv)
    _ = _ := by ring

/-- **Parameter-ellipticity of operators of Laplace type.** Let
`P = ∑ i ∈ s, bᵢ(x) ∂^{vᵢ}` be a differential operator of order `2` with smooth coefficients whose
principal symbol is real scalar and uniformly positive, `q(x, ξ) • id` with
`q(x, ξ) ≥ μ ‖ξ‖²` and `μ > 0`, and whose coefficients of order at most `1` are bounded by `B`.
Then for every `c < 1` there is `R` such that the symbol `p(x, ξ) - z` of `P - z` is elliptic
with parameter on every open set `Λ` of spectral parameters with `Re z ≤ c ‖z‖` and `R ≤ ‖z‖`. -/
theorem exists_isElliptic_ofDifferentialSymbol_sub_spectralParameter [CompleteSpace V]
    (s : Finset ι) (v : ∀ i, Fin (k i) → CoordinateSpace n)
    (b : ι → CoordinateSpace n → V →L[ℂ] V) (hb : ∀ i ∈ s, ContDiff ℝ ∞ (b i))
    (hk : ∀ i ∈ s, k i ≤ 2) {μ B c : ℝ} (hμ : 0 < μ) (hc : c < 1)
    (hprin : ∀ x ξ, ∃ q : ℝ, μ * ‖ξ‖ ^ 2 ≤ q ∧
      differentialSymbol {i ∈ s | k i = 2} v b (x, ξ) = (q : ℂ) • ContinuousLinearMap.id ℂ V)
    (hlow : ∀ i ∈ s, k i < 2 → ∀ x, ‖b i x‖ ≤ B) :
    ∃ R : ℝ, ∀ Λ : TopologicalSpace.Opens ℂ, (∀ z ∈ Λ, z.re ≤ c * ‖z‖ ∧ R ≤ ‖z‖) →
      (ofDifferentialSymbol 2 s v b hb hk - spectralParameter V :
        ParameterSymbol n Λ V V 2).IsElliptic := by
  set C := ((1 - max c (-1)) / 2 / (3 * (1 + μ⁻¹ + 1⁻¹)))⁻¹
  set D := ∑ i ∈ s with ¬k i = 2, (∏ j, ‖v i j‖) * B
  refine ⟨max 1 ((2 * C * D) ^ 2), fun Λ hΛ => ?_⟩
  have hΛ₁ (z : ℂ) (hz : z ∈ Λ) : z.re ≤ c * ‖z‖ ∧ 1 ≤ ‖z‖ :=
    ⟨(hΛ z hz).1, (le_max_left _ _).trans (hΛ z hz).2⟩
  -- Split `P - z` into its principal part minus `z` and its part of order at most `1`.
  rw [← ofDifferentialSymbol_filter_add_ofDifferentialSymbol_filter_not 2 s v b hb hk
    (fun i => k i = 2), sub_eq_add_neg, add_right_comm, ← sub_eq_add_neg]
  have hinv (x ξ : CoordinateSpace n) {z : ℂ} (hz : z ∈ Λ) :=
    isInvertible_sub_spectralParameter_and_norm_inverse_le (a := ofDifferentialSymbol 2
      {i ∈ s | k i = 2} v b (fun i hi => hb i (Finset.mem_filter.1 hi).1)
      (fun i hi => hk i (Finset.mem_filter.1 hi).1)) hμ hc
      (fun x ξ z hz => by rw [coefficient_ofDifferentialSymbol _ _ _ _ _ _ x ξ hz]; exact hprin x ξ)
      hΛ₁ x ξ hz
  refine isElliptic_add (C := C) (D := D) (fun x ξ _ hz => (hinv x ξ hz).1)
    (fun x ξ _ hz => (hinv x ξ hz).2) (fun x ξ z hz => ?_) fun z hz => ?_
  · rw [coefficient_ofDifferentialSymbol _ _ _ _ _ _ x ξ hz, show (2 : ℝ) - 1 = 1 by norm_num,
      Real.rpow_one]
    exact norm_differentialSymbol_le_mul_parameterWeight
      (fun i hi => by have := hk i (Finset.mem_filter.1 hi).1; grind)
      (fun i hi => hlow i (Finset.mem_filter.1 hi).1
        (by have := hk i (Finset.mem_filter.1 hi).1; grind)) x ξ z
  · -- At `‖z‖ ≥ R`, `2 C D ≤ ‖z‖ ^ (1 / 2)`.
    have h := Real.sqrt_le_sqrt ((le_max_right _ _).trans (hΛ z hz).2)
    rw [Real.sqrt_sq_eq_abs] at h
    linarith [le_abs_self (2 * C * D), Real.sqrt_nonneg ‖z‖]

end ParameterSymbol

end TauCeti

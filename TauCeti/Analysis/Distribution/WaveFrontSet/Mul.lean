/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import Mathlib.Analysis.LocallyConvex.Barrelled
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.Gluing
import TauCeti.Analysis.Distribution.TestFunction.Frechet
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.MeasureTheory.Integral.Asymptotics

/-!
# The product of two distributions

Let `u` and `v` be complex distributions on an open subset `Ω` of a finite-dimensional real inner
product space `E`. Their product `u v` is defined when no covector of the wave front set of `u` is
the negative of a covector of the wave front set of `v` at the same point:

`(x, ξ) ∈ WF(u) → (x, -ξ) ∉ WF(v)`

(Hörmander I, Theorem 8.2.10). Near every point of `Ω` it is given by the Fourier integral

`(u v) θ = ∫ (φ u)^(η) (θ v)^(-η) dη`,

for test functions `θ` and cutoffs `φ` equal to one on the support of `θ`, where
`(φ u)^(η) = u (φ e_η)` is the localized Fourier transform `Distribution.localFourier`. For
functions this is Parseval's formula `∫ φ θ u v = ∫ (φ u)^(η) (θ v)^(-η) dη`. The hypothesis on the
wave front sets is what makes the integral converge: in every direction `η`, either `(φ u)^`
decays rapidly near `η` or `(θ v)^` decays rapidly near `-η`, while both grow at most
polynomially. The point mass `δ₀` on `ℝ` shows that the hypothesis cannot be dropped: its wave
front set over `0` contains both `ξ` and `-ξ`, and `(φ δ₀)^ (θ δ₀)^(-·)` is the constant
`φ 0 θ 0`, which is not integrable.

## Main declarations

* `Distribution.mul u v`: the product of `u` and `v`, defined to be `0` when the wave front sets
  violate the hypothesis (`Distribution.mul_of_not`), as they do for the square of a point mass
  (`Distribution.not_forall_mem_waveFrontSet_delta`).
* `Distribution.exists_mem_nhds_complexPairing_mul_eq_integral`: the Fourier formula for `u v`
  near every point, with the integrability of its integrand.
* `Distribution.eq_mul_of_forall_mem_nhds`: `u v` is the only distribution given near every point
  by the Fourier formula.
* `Distribution.mul_comm`: the product is commutative.
* `Distribution.complexPairing_mul_ofFun`: the product with a function `g` smooth on `Ω` pairs a
  test function `θ` with `u (θ g)`, so it extends the multiplication of distributions by smooth
  functions. The hypothesis on the wave front sets always holds, since `g` has none.
* `Distribution.integral_localFourier_ofFun`: the Fourier integral of `u` and a smooth function
  `g`, computed by Parseval's formula.

## Proof outline

Near a point `x₀`, the hypothesis gives for every direction `ξ` a cone around `ξ` on which the
localized Fourier transforms of `u`, or those of `v` at `-ξ`, decay rapidly for every cutoff
supported near `x₀` (`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone`). Finitely many such
cones cover the nonzero frequencies, so `(φ u)^(ζ) (θ v)^(-η)` decays rapidly in `η`, uniformly for
`ζ` within `c ‖η‖` of `η`. This makes the integral converge, and it shows that a smooth factor `g`
can be moved from one cutoff to the other:

`∫ (φ g u)^(η) (θ v)^(-η) dη = ∫ (φ u)^(η) (θ g v)^(-η) dη`.

Indeed both localized transforms of the smooth multiples are superpositions of translates,
`(φ g u)^(η) = ∑ m, a m (φ u)^(η - m)` and `(θ g v)^(-η) = ∑ m, a m (θ v)^(-η - m)`, with the same
rapidly decreasing Fourier coefficients `a` of `g`
(`Distribution.exists_forall_hasSum_localFourier_of_eq_mul`), and Lebesgue measure is
translation invariant. Taking for `g` a second cutoff shows that the integral does not depend on
the cutoff `φ`. On test functions supported in a fixed compact set, the integral is the pointwise
limit of the integrals over balls, each bounded by a seminorm of `θ`, so it is continuous by the
Banach–Steinhaus theorem. These local distributions agree on overlaps and glue to `u v`
(`Distribution.existsUnique_gluing_of_isScalarTower`). Parseval's formula for the localized Fourier
transform (`Distribution.complexPairing_eq_integral_localFourier_mul_fourier`) identifies the
product with a smooth function.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.10 and its proof.
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction MeasureTheory
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω : Opens E}

/-! ### Rapid decay of a product near the diagonal -/

/-- `F ζ G η` decays rapidly in `η`, uniformly for `ζ` within `c ‖η‖` of `η`. -/
private def ProductDecay (F G : E → ℂ) : Prop :=
  ∃ c > 0, ∀ N : ℕ, ∃ C, ∀ η ζ : E, ‖ζ - η‖ ≤ c * ‖η‖ → (1 + ‖η‖) ^ N * (‖F ζ‖ * ‖G η‖) ≤ C

private theorem ProductDecay.integrable {F G : E → ℂ} (h : ProductDecay F G) (hF : Continuous F)
    (hG : Continuous G) : Integrable fun η ↦ F η * G η := by
  obtain ⟨c, hc, hN⟩ := h
  obtain ⟨C, hC⟩ := hN (Module.finrank ℝ E + 1)
  exact integrable_of_one_add_norm_pow_mul_norm_le (hF.mul hG) (lt_add_one _) fun η ↦ by
    simpa [norm_mul] using hC η η (by simp only [sub_self, norm_zero]; positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Under polynomial bounds on `F` and `G`, the products `F (η - w) G η` decay rapidly in `η`, with
constants growing polynomially in `w`. -/
private theorem ProductDecay.exists_bound {F G : E → ℂ} (h : ProductDecay F G) {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) (hG : ∀ η, ‖G η‖ ≤ C₀ * (1 + ‖η‖) ^ k) (N : ℕ) :
    ∃ D P, ∀ w η : E, (1 + ‖η‖) ^ N * (‖F (η - w)‖ * ‖G η‖) ≤ D * (1 + ‖w‖) ^ P := by
  obtain ⟨c, hc, hN⟩ := h
  obtain ⟨C, hC⟩ := hN N
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans ((hF 0).trans (by simp))
  set A := 1 + c⁻¹ with hAdef
  have hA : 1 ≤ A := le_add_of_nonneg_right (inv_nonneg.2 hc.le)
  clear_value A
  refine ⟨max C 0 + C₀ ^ 2 * 2 ^ k * A ^ (N + 2 * k), N + 2 * k, fun w η ↦ ?_⟩
  have h1w : 1 ≤ (1 + ‖w‖) ^ (N + 2 * k) := one_le_pow₀ (by simp)
  by_cases hw : ‖w‖ ≤ c * ‖η‖
  · -- `η - w` stays near `η`.
    calc (1 + ‖η‖) ^ N * (‖F (η - w)‖ * ‖G η‖) ≤ C := hC η (η - w) (by simpa using hw)
      _ ≤ max C 0 + C₀ ^ 2 * 2 ^ k * A ^ (N + 2 * k) := le_add_of_le_of_nonneg
          (le_max_left _ _) (by positivity)
      _ ≤ (max C 0 + C₀ ^ 2 * 2 ^ k * A ^ (N + 2 * k)) * (1 + ‖w‖) ^ (N + 2 * k) :=
          le_mul_of_one_le_right (by positivity) h1w
  · -- `‖η‖ < ‖w‖ / c`, so all factors are polynomials in `‖w‖`.
    push Not at hw
    have hη : 1 + ‖η‖ ≤ A * (1 + ‖w‖) := by
      have : ‖η‖ ≤ c⁻¹ * ‖w‖ := by
        rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]; exact hw.le
      rw [hAdef]
      nlinarith [norm_nonneg w, norm_nonneg η, inv_pos.2 hc]
    have hηw : 1 + ‖η - w‖ ≤ A * (1 + ‖w‖) + ‖w‖ := by
      have := norm_sub_le η w
      linarith
    have hηw' : 1 + ‖η - w‖ ≤ A * (1 + ‖w‖) * 2 := by nlinarith [norm_nonneg w]
    calc (1 + ‖η‖) ^ N * (‖F (η - w)‖ * ‖G η‖)
        ≤ (A * (1 + ‖w‖)) ^ N * (C₀ * (A * (1 + ‖w‖) * 2) ^ k * (C₀ * (A * (1 + ‖w‖)) ^ k)) := by
          gcongr
          · exact (hF _).trans (by gcongr)
          · exact (hG _).trans (by gcongr)
      _ = C₀ ^ 2 * 2 ^ k * A ^ (N + 2 * k) * (1 + ‖w‖) ^ (N + 2 * k) := by
          simp only [mul_pow]
          ring
      _ ≤ (max C 0 + C₀ ^ 2 * 2 ^ k * A ^ (N + 2 * k)) * (1 + ‖w‖) ^ (N + 2 * k) := by
          gcongr
          exact le_add_of_nonneg_left (le_max_right _ _)

/-- The shifted products `a i F (η - v i) G η` are integrable, and their `L¹` norms are summable in
`i`, when the coefficients `a` decay rapidly in `‖v i‖`. -/
private theorem ProductDecay.summable_integral_norm {F G : E → ℂ} (h : ProductDecay F G)
    (hFc : Continuous F) (hGc : Continuous G) {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) (hG : ∀ η, ‖G η‖ ≤ C₀ * (1 + ‖η‖) ^ k)
    {ι : Type*} {v : ι → E} {a : ι → ℂ}
    (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) :
    (∀ i, Integrable fun η ↦ a i * F (η - v i) * G η) ∧
      Summable fun i ↦ ∫ η, ‖a i * F (η - v i) * G η‖ := by
  set N := Module.finrank ℝ E + 1
  obtain ⟨D, P, hD⟩ := h.exists_bound hF hG N
  have hf (i : ι) (η : E) :
      (1 + ‖η‖) ^ N * ‖a i * F (η - v i) * G η‖ ≤ ‖a i‖ * D * (1 + ‖v i‖) ^ P := by
    calc (1 + ‖η‖) ^ N * ‖a i * F (η - v i) * G η‖
        = ‖a i‖ * ((1 + ‖η‖) ^ N * (‖F (η - v i)‖ * ‖G η‖)) := by
          simp only [norm_mul]; ring
      _ ≤ ‖a i‖ * (D * (1 + ‖v i‖) ^ P) := mul_le_mul_of_nonneg_left (hD _ _) (norm_nonneg _)
      _ = _ := by ring
  have hfi (i : ι) : Integrable fun η ↦ a i * F (η - v i) * G η :=
    integrable_of_one_add_norm_pow_mul_norm_le
      ((continuous_const.mul (hFc.comp (continuous_id.sub continuous_const))).mul hGc)
      (lt_add_one _) (hf i)
  -- Compare with `(1 + ‖η‖) ^ (-N)`, whose integral `I` is finite.
  have hint : Integrable fun η : E ↦ (1 + ‖η‖) ^ (-(N : ℝ)) :=
    integrable_one_add_norm (by simp [N])
  set I := ∫ η : E, (1 + ‖η‖) ^ (-(N : ℝ))
  refine ⟨hfi, ((ha P).mul_left (D * I)).of_nonneg_of_le (fun i ↦ integral_nonneg fun _ ↦
    norm_nonneg _) fun i ↦ ?_⟩
  calc ∫ η, ‖a i * F (η - v i) * G η‖
      ≤ ∫ η, ‖a i‖ * D * (1 + ‖v i‖) ^ P * (1 + ‖η‖) ^ (-(N : ℝ)) := by
        refine integral_mono (hfi i).norm (hint.const_mul _) fun η ↦ ?_
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv,
          le_div_iff₀ (by positivity), mul_comm]
        exact hf i η
    _ = D * I * ((1 + ‖v i‖) ^ P * ‖a i‖) := by
        rw [integral_const_mul]
        ring

/-- **Moving a multiplier between the factors.** Let `F' η = ∑ i, a i F (η - v i)` and
`G' η = ∑ i, a i G (η + v i)` with rapidly decreasing coefficients. If `F` and `G` grow
polynomially and `F ζ G η` decays rapidly near the diagonal, then `∫ F' G = ∫ F G'`. -/
private theorem integral_mul_eq_integral_mul_of_hasSum {ι : Type*} [Countable ι] {v : ι → E}
    {a : ι → ℂ} (ha : ∀ j : ℕ, Summable fun i ↦ (1 + ‖v i‖) ^ j * ‖a i‖) {F G F' G' : E → ℂ}
    (hFc : Continuous F) (hGc : Continuous G) {C₀ : ℝ} {k : ℕ}
    (hF : ∀ ζ, ‖F ζ‖ ≤ C₀ * (1 + ‖ζ‖) ^ k) (hG : ∀ η, ‖G η‖ ≤ C₀ * (1 + ‖η‖) ^ k)
    (h : ProductDecay F G) (hF' : ∀ η, HasSum (fun i ↦ a i * F (η - v i)) (F' η))
    (hG' : ∀ η, HasSum (fun i ↦ a i * G (η + v i)) (G' η)) :
    ∫ η, F' η * G η = ∫ η, F η * G' η := by
  obtain ⟨hfi, hfs⟩ := h.summable_integral_norm hFc hGc hF hG ha
  -- The translates `g i η = f i (η + v i)` of `f i η = a i F (η - v i) G η` give the other side.
  let f : ι → E → ℂ := fun i η ↦ a i * F (η - v i) * G η
  let g : ι → E → ℂ := fun i η ↦ a i * F η * G (η + v i)
  have hfg (i : ι) : g i = fun η ↦ f i (η + v i) := by
    ext η; simp [f, g]
  have hgi (i : ι) : Integrable (g i) := by
    rw [hfg]; exact (hfi i).comp_add_right (v i)
  have hgs : Summable fun i ↦ ∫ η, ‖g i η‖ := by
    refine hfs.congr fun i ↦ ?_
    rw [hfg]; exact (integral_add_right_eq_self (fun η ↦ ‖f i η‖) (v i)).symm
  calc ∫ η, F' η * G η = ∫ η, ∑' i, f i η := by
        congr 1 with η
        exact ((hF' η).mul_right (G η)).tsum_eq.symm
    _ = ∑' i, ∫ η, f i η := (integral_tsum_of_summable_integral_norm hfi hfs).symm
    _ = ∑' i, ∫ η, g i η := by
        congr 1 with i
        rw [hfg]; exact (integral_add_right_eq_self (f i) (v i)).symm
    _ = ∫ η, ∑' i, g i η := integral_tsum_of_summable_integral_norm hgi hgs
    _ = ∫ η, F η * G' η := by
        congr 1 with η
        refine HasSum.tsum_eq ?_
        convert (hG' η).mul_left (F η) using 1
        ext i
        simp only [g]
        ring

/-! ### Charts for the product -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Near a point `x₀` and a direction `ξ₀`, the hypothesis on the wave front sets makes one of the
two localized Fourier transforms decay rapidly in a cone around `ξ₀`, for all cutoffs supported
near `x₀`: that of `u` around `ξ₀`, or that of `v` around `-ξ₀`. -/
private theorem exists_nhds_cone_productDecay {u v : 𝓓'(Ω, ℂ)}
    (huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) {x₀ : E} (hx₀ : x₀ ∈ Ω)
    {ξ₀ : E} (hξ₀ : ξ₀ ≠ 0) :
    ∃ U ∈ 𝓝 x₀, ∃ Γ : Set E, IsOpen Γ ∧ ξ₀ ∈ Γ ∧ (∀ t : ℝ, 0 < t → ∀ η ∈ Γ, t • η ∈ Γ) ∧
      ∃ c > 0, ∀ φ ψ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → tsupport ψ ⊆ U → ∀ N : ℕ, ∃ C, ∀ η ∈ Γ, ∀ ζ,
        ‖ζ - η‖ ≤ c * ‖η‖ →
          (1 + ‖η‖) ^ N * (‖u.localFourier φ ζ‖ * ‖v.localFourier ψ (-η)‖) ≤ C := by
  by_cases hu : u.IsMicrolocallySmoothAt x₀ ξ₀
  · -- `u` decays near the direction `ξ₀`; `ζ` stays in the cone of decay.
    obtain ⟨U, hU, Γ, hΓ, hξ₀Γ, hcone, hdec⟩ := hu.exists_nhds_cone
    obtain ⟨Γ', hΓ'o, hξ₀Γ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ₀Γ
    refine ⟨U, hU, Γ', hΓ'o, hξ₀Γ', hcone', min c (1 / 2), by positivity,
      fun φ ψ hφ _ N ↦ ?_⟩
    obtain ⟨C₀, k, hG⟩ := exists_norm_localFourier_le v ψ
    obtain ⟨C, hC⟩ := hdec φ hφ (N + k)
    have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans ((hG 0).trans (by simp))
    refine ⟨C₀ * 2 ^ (N + k) * C, fun η hη ζ hζ ↦ ?_⟩
    have hζΓ : ζ ∈ Γ := hΓ' η hη (mem_closedBall_iff_norm.2 (hζ.trans
      (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))))
    have hηζ : 1 + ‖η‖ ≤ 2 * (1 + ‖ζ‖) := by
      have h1 : ‖η - ζ‖ ≤ 1 / 2 * ‖η‖ := norm_sub_rev η ζ ▸
        hζ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _))
      have h2 := norm_sub_norm_le η ζ
      linarith
    calc (1 + ‖η‖) ^ N * (‖u.localFourier φ ζ‖ * ‖v.localFourier ψ (-η)‖)
        ≤ (1 + ‖η‖) ^ N * (‖u.localFourier φ ζ‖ * (C₀ * (1 + ‖η‖) ^ k)) := by
          gcongr
          simpa using hG (-η)
      _ = C₀ * ((1 + ‖η‖) ^ (N + k) * ‖u.localFourier φ ζ‖) := by rw [pow_add]; ring
      _ ≤ C₀ * ((2 * (1 + ‖ζ‖)) ^ (N + k) * ‖u.localFourier φ ζ‖) := by gcongr
      _ = C₀ * 2 ^ (N + k) * ((1 + ‖ζ‖) ^ (N + k) * ‖u.localFourier φ ζ‖) := by
          rw [mul_pow]; ring
      _ ≤ C₀ * 2 ^ (N + k) * C := by gcongr; exact hC ζ hζΓ
  · -- Otherwise `(x₀, ξ₀)` lies in the wave front set of `u`, so `v` decays near `-ξ₀`.
    have hv : v.IsMicrolocallySmoothAt x₀ (-ξ₀) := by
      by_contra hv
      exact huv x₀ ξ₀ (mem_waveFrontSet_iff.2 ⟨hx₀, hξ₀, hu⟩)
        (mem_waveFrontSet_iff.2 ⟨hx₀, neg_ne_zero.2 hξ₀, hv⟩)
    obtain ⟨U, hU, Γ, hΓ, hξ₀Γ, hcone, hdec⟩ := hv.exists_nhds_cone
    refine ⟨U, hU, Neg.neg ⁻¹' Γ, hΓ.preimage continuous_neg, by simpa using hξ₀Γ,
      fun t ht η hη ↦ by simpa [smul_neg] using hcone t ht _ hη, 1, one_pos,
      fun φ ψ _ hψ N ↦ ?_⟩
    obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le u φ
    obtain ⟨C, hC⟩ := hdec ψ hψ (N + k)
    have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans ((hF 0).trans (by simp))
    refine ⟨C₀ * 2 ^ k * C, fun η hη ζ hζ ↦ ?_⟩
    have hζη : 1 + ‖ζ‖ ≤ 2 * (1 + ‖η‖) := by
      have := norm_le_insert' ζ η
      linarith [norm_nonneg η]
    calc (1 + ‖η‖) ^ N * (‖u.localFourier φ ζ‖ * ‖v.localFourier ψ (-η)‖)
        ≤ (1 + ‖η‖) ^ N * (C₀ * (2 * (1 + ‖η‖)) ^ k * ‖v.localFourier ψ (-η)‖) := by
          gcongr
          exact (hF ζ).trans (by gcongr)
      _ = C₀ * 2 ^ k * ((1 + ‖-η‖) ^ (N + k) * ‖v.localFourier ψ (-η)‖) := by
          rw [norm_neg, mul_pow, pow_add]; ring
      _ ≤ C₀ * 2 ^ k * C := by gcongr; exact hC _ hη

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Charts for the product.** If no covector of `WF(u)` is the negative of one of `WF(v)` at the
same point, then every point `x₀ ∈ Ω` has a neighbourhood `U` such that for all cutoffs `φ`, `ψ`
supported in `U`, the product `(φ u)^(ζ) (ψ v)^(-η)` decays rapidly near the diagonal. -/
private theorem exists_mem_nhds_productDecay {u v : 𝓓'(Ω, ℂ)}
    (huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ U ∈ 𝓝 x₀, ∀ φ ψ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → tsupport ψ ⊆ U →
      ProductDecay (u.localFourier φ) fun η ↦ v.localFourier ψ (-η) := by
  choose U hU Γ hΓ hξΓ hcone c hc hdec using fun ξ : sphere (0 : E) 1 ↦
    exists_nhds_cone_productDecay huv hx₀ (ne_zero_of_mem_unit_sphere ξ)
  -- Finitely many of the cones cover the nonzero frequencies.
  obtain ⟨t, ht⟩ := TauCeti.exists_finset_compl_singleton_subset_biUnion hΓ hξΓ hcone
  have hne : (insert 1 (t.image c)).Nonempty := Finset.insert_nonempty _ _
  set c₀ := (insert 1 (t.image c)).min' hne
  have hc₀ : 0 < c₀ := by
    have hmem : c₀ ∈ insert 1 (t.image c) := Finset.min'_mem _ hne
    obtain h | h := Finset.mem_insert.1 hmem
    · rw [h]; exact one_pos
    · obtain ⟨ξ, -, hξ⟩ := Finset.mem_image.1 h
      rw [← hξ]; exact hc ξ
  have hc₀c (ξ : sphere (0 : E) 1) (hξ : ξ ∈ t) : c₀ ≤ c ξ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem c hξ))
  refine ⟨⋂ ξ ∈ t, U ξ, (Finset.iInter_mem_sets t).2 fun ξ _ ↦ hU ξ,
    fun φ ψ hφ hψ ↦ ⟨c₀, hc₀, fun N ↦ ?_⟩⟩
  have hUξ (ξ : sphere (0 : E) 1) (hξ : ξ ∈ t) {θ : 𝓓(Ω, ℂ)} (hθ : tsupport θ ⊆ ⋂ ξ ∈ t, U ξ) :
      tsupport θ ⊆ U ξ := hθ.trans (biInter_subset_of_mem hξ)
  choose! C hC using fun ξ (hξ : ξ ∈ t) ↦ hdec ξ φ ψ (hUξ ξ hξ hφ) (hUξ ξ hξ hψ) N
  refine ⟨∑ ξ ∈ t, max (C ξ) 0 + ‖u.localFourier φ 0‖ * ‖v.localFourier ψ (-0)‖,
    fun η ζ hζ ↦ ?_⟩
  by_cases hη : η = 0
  · -- At `η = 0` also `ζ = 0`.
    subst hη
    have hζ0 : ζ = 0 := by simpa [sub_eq_zero] using hζ
    subst hζ0
    simpa using le_add_of_nonneg_left (a := ‖u.localFourier φ 0‖ * ‖v.localFourier ψ 0‖)
      (Finset.sum_nonneg fun ξ _ ↦ le_max_right (C ξ) 0)
  · obtain ⟨ξ, hξt, hηξ⟩ := mem_iUnion₂.1 (ht hη)
    calc (1 + ‖η‖) ^ N * (‖u.localFourier φ ζ‖ * ‖v.localFourier ψ (-η)‖)
        ≤ C ξ := hC ξ hξt η hηξ ζ (hζ.trans (by gcongr; exact hc₀c ξ hξt))
      _ ≤ max (C ξ) 0 := le_max_left _ _
      _ ≤ ∑ ξ ∈ t, max (C ξ) 0 :=
          Finset.single_le_sum (f := fun ξ ↦ max (C ξ) 0) (fun _ _ ↦ le_max_right _ _) hξt
      _ ≤ _ := le_add_of_nonneg_right (by positivity)

/-! ### The local product pairing -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Common polynomial bounds for the localized Fourier transforms of `u` and `v`. -/
private theorem exists_norm_localFourier_le_and_le (u v : 𝓓'(Ω, ℂ)) (φ ψ : 𝓓(Ω, ℂ)) :
    ∃ (C : ℝ) (k : ℕ), (∀ ζ, ‖u.localFourier φ ζ‖ ≤ C * (1 + ‖ζ‖) ^ k) ∧
      ∀ η, ‖v.localFourier ψ (-η)‖ ≤ C * (1 + ‖η‖) ^ k := by
  obtain ⟨C₁, k₁, h₁⟩ := exists_norm_localFourier_le u φ
  obtain ⟨C₂, k₂, h₂⟩ := exists_norm_localFourier_le v ψ
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans ((h₁ 0).trans (by simp))
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans ((h₂ 0).trans (by simp))
  have hmono {C : ℝ} {k : ℕ} (hC : 0 ≤ C) (hCm : C ≤ max C₁ C₂) (hk : k ≤ max k₁ k₂) (a : ℝ)
      (ha : 0 ≤ a) : C * (1 + a) ^ k ≤ max C₁ C₂ * (1 + a) ^ max k₁ k₂ :=
    mul_le_mul hCm (pow_le_pow_right₀ (by linarith) hk) (by positivity) (hC.trans hCm)
  exact ⟨max C₁ C₂, max k₁ k₂,
    fun ζ ↦ (h₁ ζ).trans (hmono hC₁ (le_max_left _ _) (le_max_left _ _) _ (norm_nonneg _)),
    fun η ↦ (h₂ (-η)).trans (by
      rw [norm_neg]; exact hmono hC₂ (le_max_right _ _) (le_max_right _ _) _ (norm_nonneg _))⟩

/-- **Moving a smooth factor from one cutoff to the other.** If `(φ u)^(ζ) (θ v)^(-η)` decays
rapidly near the diagonal and `g` is smooth on `Ω`, then
`∫ (φ g u)^(η) (θ v)^(-η) dη = ∫ (φ u)^(η) (θ g v)^(-η) dη`. -/
private theorem integral_localFourier_mul_eq_of_eq_mul {u v : 𝓓'(Ω, ℂ)} {φ θ φ' θ' : 𝓓(Ω, ℂ)}
    (hdec : ProductDecay (u.localFourier φ) fun η ↦ v.localFourier θ (-η)) {g : E → ℂ}
    (hg : ContDiffOn ℝ ∞ g Ω) (hφ' : ∀ x, φ' x = φ x * g x) (hθ' : ∀ x, θ' x = θ x * g x) :
    ∫ η, u.localFourier φ' η * v.localFourier θ (-η) =
      ∫ η, u.localFourier φ η * v.localFourier θ' (-η) := by
  -- One Fourier series of `g` serves both cutoffs.
  obtain ⟨L, _, a, ha, hsum⟩ := exists_forall_hasSum_localFourier_of_eq_mul
    (φ.hasCompactSupport.union θ.hasCompactSupport)
    (union_subset φ.tsupport_subset θ.tsupport_subset) hg
  obtain ⟨C, k, hF, hG⟩ := exists_norm_localFourier_le_and_le u v φ θ
  refine integral_mul_eq_integral_mul_of_hasSum (v := fun m : L ↦ (m : E)) ha
    (u.continuous_localFourier φ) ((v.continuous_localFourier θ).comp continuous_neg) hF hG hdec
    (fun η ↦ hsum u φ φ' subset_union_left hφ' η) fun η ↦ ?_
  have e (m : L) : -(η + (m : E)) = -η - m := neg_add' _ _
  simp only [e]
  exact hsum v θ θ' subset_union_right hθ' (-η)

/-- **Independence of the cutoff.** Two cutoffs `φ₁`, `φ₂` equal to one on the support of `θ` give
the same local product pairing `∫ (φ u)^(η) (θ v)^(-η) dη`. -/
private theorem integral_localFourier_mul_eq_of_eqOn {u v : 𝓓'(Ω, ℂ)} {φ₁ φ₂ θ : 𝓓(Ω, ℂ)}
    (h₁ : ProductDecay (u.localFourier φ₁) fun η ↦ v.localFourier θ (-η))
    (h₂ : ProductDecay (u.localFourier φ₂) fun η ↦ v.localFourier θ (-η))
    (hφ₁ : EqOn φ₁ 1 (tsupport θ)) (hφ₂ : EqOn φ₂ 1 (tsupport θ)) :
    ∫ η, u.localFourier φ₁ η * v.localFourier θ (-η) =
      ∫ η, u.localFourier φ₂ η * v.localFourier θ (-η) := by
  -- Both are the pairing with the cutoff `φ₁ φ₂`.
  let ψ : 𝓓(Ω, ℂ) := bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) φ₂.contDiff φ₁
  have hψ : ∀ x, ψ x = φ₁ x * φ₂ x := fun x ↦ rfl
  have hθ {φ : 𝓓(Ω, ℂ)} (hφ : EqOn φ 1 (tsupport θ)) (x : E) : θ x = θ x * φ x := by
    by_cases hx : x ∈ tsupport θ
    · simp [hφ hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← integral_localFourier_mul_eq_of_eq_mul h₁ φ₂.contDiff.contDiffOn hψ (hθ hφ₂),
    ← integral_localFourier_mul_eq_of_eq_mul h₂ φ₁.contDiff.contDiffOn
      (fun x ↦ (hψ x).trans (mul_comm _ _)) (hθ hφ₁)]

/-- **Symmetry of the local product pairing.** If `φ = 1` on the support of `θ`, the pairings
`∫ (φ u)^(η) (θ v)^(-η) dη` and `∫ (φ v)^(η) (θ u)^(-η) dη` agree. -/
private theorem integral_localFourier_mul_comm {u v : 𝓓'(Ω, ℂ)} {φ θ : 𝓓(Ω, ℂ)}
    (h : ProductDecay (u.localFourier φ) fun η ↦ v.localFourier φ (-η))
    (hφ : EqOn φ 1 (tsupport θ)) :
    ∫ η, u.localFourier φ η * v.localFourier θ (-η) =
      ∫ η, v.localFourier φ η * u.localFourier θ (-η) := by
  have hθ (x : E) : θ x = φ x * θ x := by
    by_cases hx : x ∈ tsupport θ
    · simp [hφ hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  rw [← integral_localFourier_mul_eq_of_eq_mul h θ.contDiff.contDiffOn hθ hθ,
    ← integral_neg_eq_self]
  simp only [neg_neg, mul_comm]

/-- **The local product pairing with a smooth function.** If `g` is smooth on `Ω` and `φ = 1` on
the support of `θ`, the pairing of `u` with the regular distribution `g` is `u (θ g)`. -/
theorem integral_localFourier_ofFun {u : 𝓓'(Ω, ℂ)} {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    {φ θ ψ : 𝓓(Ω, ℂ)} (hφ : EqOn φ 1 (tsupport θ)) (hψ : ∀ x, ψ x = θ x * g x) :
    ∫ η, u.localFourier φ η * (ofFun Ω g volume ⊤).localFourier θ (-η) = u.complexPairing ψ := by
  have hloc : LocallyIntegrableOn g Ω := hg.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet
  have hF (η : E) : (ofFun Ω g volume ⊤).localFourier θ η = 𝓕 (ψ : E → ℂ) η := by
    rw [localFourier_eq_fourier hloc (fun φ _ ↦ ofFun_apply hloc) θ.tsupport_subset,
      show (ψ : E → ℂ) = fun y ↦ θ y * g y from funext hψ]
  simp_rw [hF]
  refine (complexPairing_eq_integral_localFourier_mul_fourier u φ ψ ψ fun x ↦ ?_).symm
  by_cases hx : x ∈ tsupport θ
  · simp [hφ hx]
  · simp [hψ, image_eq_zero_of_notMem_tsupport hx]

/-! ### Gluing the local pairings -/

/-- The integral of `(φ u)^(η) (f v)^(-η)` over a ball is a continuous linear function of the test
function `f` supported in `K`: it is bounded by the seminorm `sup_{i ≤ k} N_i f`. -/
private theorem exists_continuousLinearMap_eq_setIntegral_localFourier (u v : 𝓓'(Ω, ℂ))
    (φ : 𝓓(Ω, ℂ)) {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω) (n : ℕ) :
    ∃ Λ : 𝓓_{K}(E, ℂ) →L[ℂ] ℂ, ∀ f, Λ f = ∫ η in closedBall (0 : E) n,
      u.localFourier φ η * v.localFourier (ofSupportedIn hKΩ f) (-η) := by
  obtain ⟨k, C, hC⟩ := exists_norm_localFourier_ofSupportedIn_le v hKΩ
  have hcont (f : 𝓓_{K}(E, ℂ)) : Continuous fun η ↦
      u.localFourier φ η * v.localFourier (ofSupportedInCLM ℂ hKΩ f) (-η) :=
    (u.continuous_localFourier φ).mul ((v.continuous_localFourier _).comp continuous_neg)
  let Λ : 𝓓_{K}(E, ℂ) →ₗ[ℂ] ℂ :=
    { toFun f := ∫ η in closedBall 0 n,
        u.localFourier φ η * v.localFourier (ofSupportedInCLM ℂ hKΩ f) (-η)
      map_add' f₁ f₂ := by
        simp only [map_add, localFourier_add_cutoff, mul_add]
        exact integral_add ((hcont f₁).continuousOn.integrableOn_compact (isCompact_closedBall _ _))
          ((hcont f₂).continuousOn.integrableOn_compact (isCompact_closedBall _ _))
      map_smul' c f := by
        simp only [map_smul, localFourier_smul_cutoff, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1 with η
        ring }
  refine ⟨⟨Λ, WithSeminorms.continuous_of_isBounded
    (ContDiffMapSupportedIn.withSeminorms' ℂ E ℂ ⊤ K) (norm_withSeminorms ℂ ℂ) Λ
    (Seminorm.IsBounded.of_real fun _ ↦ ⟨{k},
      C * ∫ η in closedBall (0 : E) n, ‖u.localFourier φ η‖ * (1 + ‖η‖) ^ k, fun f ↦ ?_⟩)⟩,
    fun f ↦ by simp [Λ]⟩
  set S := ContDiffMapSupportedIn.supSeminorm ℂ E ℂ ⊤ K k f
  have hbound : Integrable (fun η ↦ ‖u.localFourier φ η‖ * (1 + ‖η‖) ^ k)
      (volume.restrict (closedBall (0 : E) n)) :=
    ((u.continuous_localFourier φ).norm.mul (by fun_prop)).continuousOn.integrableOn_compact
      (isCompact_closedBall _ _)
  simp only [Finset.sup_singleton, coe_normSeminorm]
  calc ‖Λ f‖ ≤ ∫ η in closedBall (0 : E) n, C * S * (‖u.localFourier φ η‖ * (1 + ‖η‖) ^ k) :=
        norm_integral_le_of_norm_le (hbound.const_mul _) (ae_of_all _ fun η ↦ by
          rw [norm_mul]
          calc ‖u.localFourier φ η‖ * ‖v.localFourier (ofSupportedInCLM ℂ hKΩ f) (-η)‖
              ≤ ‖u.localFourier φ η‖ * (C * S * (1 + ‖-η‖) ^ k) := by
                gcongr
                exact hC f (-η)
            _ = _ := by rw [norm_neg]; ring)
    _ = C * (∫ η in closedBall (0 : E) n, ‖u.localFourier φ η‖ * (1 + ‖η‖) ^ k) * S := by
        rw [integral_const_mul]; ring

/-- On test functions supported in a fixed compact set `K`, the local product pairing
`f ↦ ∫ (φ u)^(η) (f v)^(-η) dη` is continuous. It is the pointwise limit of the integrals over the
balls of radius `n`, which are continuous linear maps, so the Banach–Steinhaus theorem applies on
the Fréchet space `𝓓_{K}`. -/
private theorem continuous_integral_localFourier_ofSupportedIn {u v : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)}
    {K : Compacts E} (hKΩ : (K : Set E) ⊆ Ω)
    (h : ∀ f : 𝓓_{K}(E, ℂ),
      ProductDecay (u.localFourier φ) fun η ↦ v.localFourier (ofSupportedIn hKΩ f) (-η)) :
    Continuous fun f : 𝓓_{K}(E, ℂ) ↦
      ∫ η, u.localFourier φ η * v.localFourier (ofSupportedIn hKΩ f) (-η) := by
  choose Λ hΛ using exists_continuousLinearMap_eq_setIntegral_localFourier u v φ hKΩ
  -- The integrals over balls converge to the pairing, by dominated convergence.
  have htend : Tendsto (fun n f ↦ Λ n f) atTop (𝓝 fun f ↦
      ∫ η, u.localFourier φ η * v.localFourier (ofSupportedIn hKΩ f) (-η)) := by
    refine tendsto_pi_nhds.2 fun f ↦ ?_
    have hi := (h f).integrable (u.continuous_localFourier φ)
      ((v.continuous_localFourier _).comp continuous_neg)
    have := tendsto_setIntegral_of_monotone (μ := volume)
      (s := fun n : ℕ ↦ closedBall (0 : E) n) (fun _ ↦ measurableSet_closedBall)
      (fun m n hmn ↦ closedBall_subset_closedBall (by exact_mod_cast hmn)) hi.integrableOn
    rw [iUnion_closedBall_nat, setIntegral_univ] at this
    simpa [hΛ] using this
  -- A pointwise limit of continuous linear maps on a barrelled space is continuous.
  exact htend.continuous_of_equicontinuous (PolynormableSpace.banach_steinhaus fun f ↦
    ((tendsto_pi_nhds.1 htend) f).isVonNBounded_range ℂ).equicontinuous

/-- The local product pairing `θ ↦ ∫ (φ u)^(η) (θ v)^(-η) dη`, on test functions supported in an
open set `V` on which it converges as in `ProductDecay`, is a continuous linear map. -/
private theorem exists_continuousLinearMap_eq_integral_localFourier {u v : 𝓓'(Ω, ℂ)}
    {φ : 𝓓(Ω, ℂ)} {V : Opens E} (hVΩ : V ≤ Ω)
    (h : ∀ θ : 𝓓(Ω, ℂ), tsupport θ ⊆ V →
      ProductDecay (u.localFourier φ) fun η ↦ v.localFourier θ (-η)) :
    ∃ T : 𝓓(V, ℂ) →L[ℂ] ℂ, ∀ θ : 𝓓(V, ℂ),
      T θ = ∫ η, u.localFourier φ η * v.localFourier (monoCLM ℂ θ) (-η) := by
  have hmono (θ : 𝓓(V, ℂ)) : ((monoCLM ℂ θ : 𝓓(Ω, ℂ)) : E → ℂ) = θ := by
    rw [monoCLM_apply]
    simp [hVΩ]
  have hint (θ : 𝓓(V, ℂ)) :
      Integrable fun η ↦ u.localFourier φ η * v.localFourier (monoCLM ℂ θ) (-η) :=
    (h _ (by rw [hmono]; exact θ.tsupport_subset)).integrable (u.continuous_localFourier φ)
      ((v.continuous_localFourier _).comp continuous_neg)
  let P : 𝓓(V, ℂ) →ₗ[ℂ] ℂ :=
    { toFun θ := ∫ η, u.localFourier φ η * v.localFourier (monoCLM ℂ θ) (-η)
      map_add' θ₁ θ₂ := by
        simp only [map_add, localFourier_add_cutoff, mul_add]
        exact integral_add (hint θ₁) (hint θ₂)
      map_smul' c θ := by
        simp only [map_smul, localFourier_smul_cutoff, RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1 with η
        ring }
  refine ⟨⟨P, (TestFunction.continuous_iff_continuous_comp (𝕜 := ℂ) P).2 fun K hKV ↦ ?_⟩,
    fun θ ↦ rfl⟩
  have hKΩ : (K : Set E) ⊆ Ω := hKV.trans hVΩ
  have hK (f : 𝓓_{K}(E, ℂ)) : (monoCLM ℂ (ofSupportedIn hKV f) : 𝓓(Ω, ℂ)) = ofSupportedIn hKΩ f :=
    TestFunction.ext fun x ↦ by rw [hmono, coe_ofSupportedIn, coe_ofSupportedIn]
  have hcomp : ⇑P ∘ ofSupportedIn hKV = fun f : 𝓓_{K}(E, ℂ) ↦
      ∫ η, u.localFourier φ η * v.localFourier (ofSupportedIn hKΩ f) (-η) := by
    ext f
    simp only [Function.comp_apply, P, LinearMap.coe_mk, AddHom.coe_mk, hK]
  rw [hcomp]
  exact continuous_integral_localFourier_ofSupportedIn hKΩ fun f ↦
    h _ (by rw [coe_ofSupportedIn]; exact f.tsupport_subset.trans hKV)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A complex test function equal to one on an open neighbourhood `V ⊆ U` of `x₀` and supported in
a neighbourhood `U` of `x₀`. -/
private theorem exists_opens_testFunction_eqOn_one {U : Set E} {x₀ : E} (hU : U ∈ 𝓝 x₀)
    (hx₀ : x₀ ∈ Ω) :
    ∃ (V : Opens E) (φ : 𝓓(Ω, ℂ)), x₀ ∈ V ∧ V ≤ Ω ∧ (V : Set E) ⊆ U ∧ tsupport φ ⊆ U ∧
      EqOn φ 1 V := by
  have hW : IsOpen (interior U ∩ Ω) := isOpen_interior.inter Ω.isOpen
  have hxW : x₀ ∈ interior U ∩ Ω := ⟨mem_interior_iff_mem_nhds.2 hU, hx₀⟩
  obtain ⟨χ, -, hχ1, hχW⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤)
    isCompact_singleton hW (singleton_subset_iff.2 hxW) inter_subset_right
  rw [nhdsSet_singleton] at hχ1
  obtain ⟨V, hVχ, hV, hxV⟩ := _root_.eventually_nhds_iff.1 (hχ1.and (hW.mem_nhds hxW))
  refine ⟨⟨V, hV⟩, postcompCLM (𝕜 := ℝ) ofRealCLM χ, hxV, fun x hx ↦ (hVχ x hx).2.2,
    fun x hx ↦ interior_subset (hVχ x hx).2.1, ?_, fun x hx ↦ by simp [(hVχ x hx).1]⟩
  exact (tsupport_comp_subset (map_zero ofRealCLM) _).trans
    (hχW.trans (inter_subset_left.trans interior_subset))

/-! ### The product of two distributions -/

/-- **Existence of the product of distributions** (Hörmander I, Theorem 8.2.10). If no covector of
the wave front set of `u` is the negative of one of `v` at the same point, there is a distribution
`w` given near every point by the Fourier integral `w θ = ∫ (φ u)^(η) (θ v)^(-η) dη`, for every
test function `θ` and every cutoff `φ` equal to one on its support, both supported in a fixed
neighbourhood of the point. -/
private theorem exists_complexPairing_eq_integral_localFourier (u v : 𝓓'(Ω, ℂ))
    (huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) :
    ∃ w : 𝓓'(Ω, ℂ), ∀ x₀ ∈ Ω, ∃ U ∈ 𝓝 x₀, ∀ φ θ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → tsupport θ ⊆ U →
      EqOn φ 1 (tsupport θ) →
        w.complexPairing θ = ∫ η, u.localFourier φ η * v.localFourier θ (-η) := by
  -- Charts `U x`, open sets `V x ∋ x` and cutoffs `φ x` equal to one on `V x`.
  choose U hU hdec using fun x : Ω ↦ exists_mem_nhds_productDecay huv x.2
  choose V φ hxV hVΩ hVU hφU hφV using fun x : Ω ↦ exists_opens_testFunction_eqOn_one (hU x) x.2
  choose T hT using fun x : Ω ↦ exists_continuousLinearMap_eq_integral_localFourier (hVΩ x)
    fun θ hθ ↦ hdec x (φ x) θ (hφU x) (hθ.trans (hVU x))
  have hcover : ⨆ x, V x = Ω := le_antisymm (iSup_le hVΩ) fun y hy ↦
    (Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxV ⟨y, hy⟩⟩ : y ∈ ⨆ x, V x)
  -- On test functions supported in `V x`, `w` is the pairing with the cutoff `φ x`.
  have hmono {W W' : Opens E} (h : W ≤ W') (θ : 𝓓(W, ℂ)) :
      ((monoCLM ℂ θ : 𝓓(W', ℂ)) : E → ℂ) = θ := by
    rw [monoCLM_apply]; simp [h]
  obtain ⟨S, hS, -⟩ := existsUnique_gluing_of_isScalarTower (𝕜 := ℂ) (L := T) hcover
    fun i j θ ↦ by
      have hθ : tsupport (monoCLM ℂ θ : 𝓓(Ω, ℂ)) ⊆ V i ∩ V j := by
        rw [hmono (inf_le_left.trans (hVΩ i))]; exact θ.tsupport_subset
      have hi : monoCLM ℂ (monoCLM ℂ θ : 𝓓(V i, ℂ)) = (monoCLM ℂ θ : 𝓓(Ω, ℂ)) :=
        TestFunction.ext fun x ↦ by
          rw [hmono (hVΩ i), hmono inf_le_left, hmono (inf_le_left.trans (hVΩ i))]
      have hj : monoCLM ℂ (monoCLM ℂ θ : 𝓓(V j, ℂ)) = (monoCLM ℂ θ : 𝓓(Ω, ℂ)) :=
        TestFunction.ext fun x ↦ by
          rw [hmono (hVΩ j), hmono inf_le_right, hmono (inf_le_left.trans (hVΩ i))]
      rw [hT, hT, hi, hj]
      exact integral_localFourier_mul_eq_of_eqOn
        (hdec i _ _ (hφU i) (hθ.trans (inter_subset_left.trans (hVU i))))
        (hdec j _ _ (hφU j) (hθ.trans (inter_subset_right.trans (hVU j))))
        (fun x hx ↦ hφV i (hθ hx).1) fun x hx ↦ hφV j (hθ hx).2
  refine ⟨(S.restrictScalars ℝ).comp (postcompCLM (𝕜 := ℝ) ofRealCLM), fun x₀ hx₀ ↦ ?_⟩
  -- The formula holds near `x₀` for the cutoff `φ x₀`, hence for every cutoff.
  set x : Ω := ⟨x₀, hx₀⟩
  refine ⟨V x, (V x).isOpen.mem_nhds (hxV x), fun ψ θ hψ hθ hψθ ↦ ?_⟩
  rw [complexPairing_restrictScalars_comp_postcompCLM_ofRealCLM]
  let θ' : 𝓓(V x, ℂ) := ⟨θ, θ.contDiff, θ.hasCompactSupport, hθ⟩
  have hθ' : (monoCLM ℂ θ' : 𝓓(Ω, ℂ)) = θ := TestFunction.ext fun y ↦ by
    rw [hmono (hVΩ x)]; rfl
  rw [← hθ', ← ContinuousLinearMap.comp_apply, hS, hT, hθ']
  exact integral_localFourier_mul_eq_of_eqOn (hdec x _ _ (hφU x) (hθ.trans (hVU x)))
    (hdec x _ _ (hψ.trans (hVU x)) (hθ.trans (hVU x))) (fun y hy ↦ hφV x (hθ hy)) hψθ

open scoped Classical in
/-- The **product** `u v` of two complex distributions on `Ω` such that no covector of the wave
front set of `u` is the negative of a covector of the wave front set of `v` at the same point
(Hörmander I, Theorem 8.2.10). Near every point it is given by the Fourier integral
`(u v) θ = ∫ (φ u)^(η) (θ v)^(-η) dη`, for a cutoff `φ` equal to one on the support of `θ`
(`Distribution.exists_mem_nhds_complexPairing_mul_eq_integral`), and it extends the product
with a smooth function (`Distribution.complexPairing_mul_ofFun`). Without the hypothesis on the
wave front sets it is defined to be `0`. -/
def mul (u v : 𝓓'(Ω, ℂ)) : 𝓓'(Ω, ℂ) :=
  if h : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet then
    (exists_complexPairing_eq_integral_localFourier u v h).choose
  else 0

/-- Without the hypothesis on the wave front sets, the product is `0` by convention. -/
theorem mul_of_not {u v : 𝓓'(Ω, ℂ)}
    (huv : ¬ ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) : u.mul v = 0 := by
  rw [mul, dite_eq_right huv]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The hypothesis of the product fails for the square of a point mass in positive dimension: the
wave front set of `δ_{x₀}` contains both `(x₀, ξ)` and `(x₀, -ξ)`. -/
theorem not_forall_mem_waveFrontSet_delta [Nontrivial E] {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ¬ ∀ x ξ, (x, ξ) ∈ (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).waveFrontSet →
      (x, -ξ) ∉ (mapCLM ofRealCLM (delta x₀ : 𝓓'(Ω, ℝ))).waveFrontSet := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : E)
  rw [waveFrontSet_delta hx₀]
  exact fun h ↦ h x₀ ξ ⟨rfl, hξ⟩ ⟨rfl, neg_ne_zero.2 hξ⟩

/-- **The Fourier formula for the product.** Every point `x₀ ∈ Ω` has a neighbourhood `U` such that
for all test functions `θ` and cutoffs `φ` supported in `U` with `φ = 1` on the support of `θ`, the
function `η ↦ (φ u)^(η) (θ v)^(-η)` is integrable and `(u v) θ` is its integral. -/
theorem exists_mem_nhds_complexPairing_mul_eq_integral {u v : 𝓓'(Ω, ℂ)}
    (huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ U ∈ 𝓝 x₀, ∀ φ θ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → tsupport θ ⊆ U → EqOn φ 1 (tsupport θ) →
      Integrable (fun η ↦ u.localFourier φ η * v.localFourier θ (-η)) ∧
        (u.mul v).complexPairing θ = ∫ η, u.localFourier φ η * v.localFourier θ (-η) := by
  obtain ⟨U₁, hU₁, h₁⟩ :=
    (exists_complexPairing_eq_integral_localFourier u v huv).choose_spec x₀ hx₀
  obtain ⟨U₂, hU₂, h₂⟩ := exists_mem_nhds_productDecay huv hx₀
  refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun φ θ hφ hθ hφθ ↦ ⟨?_, ?_⟩⟩
  · exact (h₂ φ θ (hφ.trans inter_subset_right) (hθ.trans inter_subset_right)).integrable
      (u.continuous_localFourier φ) ((v.continuous_localFourier θ).comp continuous_neg)
  · rw [mul, dite_eq_left huv]
    exact h₁ φ θ (hφ.trans inter_subset_left) (hθ.trans inter_subset_left) hφθ

/-- **Uniqueness of the product.** A distribution given near every point by the Fourier formula of
`Distribution.exists_mem_nhds_complexPairing_mul_eq_integral` is the product `u v`. -/
theorem eq_mul_of_forall_mem_nhds {u v w : 𝓓'(Ω, ℂ)}
    (huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet)
    (hw : ∀ x₀ ∈ Ω, ∃ U ∈ 𝓝 x₀, ∀ φ θ : 𝓓(Ω, ℂ), tsupport φ ⊆ U → tsupport θ ⊆ U →
      EqOn φ 1 (tsupport θ) →
        w.complexPairing θ = ∫ η, u.localFourier φ η * v.localFourier θ (-η)) :
    w = u.mul v := by
  refine eq_of_forall_mem_nhds_complexPairing_eq fun x₀ hx₀ ↦ ?_
  obtain ⟨U₁, hU₁, h₁⟩ := hw x₀ hx₀
  obtain ⟨U₂, hU₂, h₂⟩ := exists_mem_nhds_complexPairing_mul_eq_integral huv hx₀
  obtain ⟨V, φ, hxV, -, hVU, hφU, hφV⟩ := exists_opens_testFunction_eqOn_one (inter_mem hU₁ hU₂) hx₀
  refine ⟨V, V.isOpen.mem_nhds hxV, fun θ hθ ↦ ?_⟩
  have hφθ : EqOn φ 1 (tsupport θ) := fun y hy ↦ hφV (hθ hy)
  rw [h₁ φ θ (hφU.trans inter_subset_left) ((hθ.trans hVU).trans inter_subset_left) hφθ,
    (h₂ φ θ (hφU.trans inter_subset_right) ((hθ.trans hVU).trans inter_subset_right) hφθ).2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The hypothesis of the product on the wave front sets is symmetric in the two factors. -/
theorem forall_mem_waveFrontSet_neg_notMem_comm {u v : 𝓓'(Ω, ℂ)} :
    (∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet) ↔
      ∀ x ξ, (x, ξ) ∈ v.waveFrontSet → (x, -ξ) ∉ u.waveFrontSet := by
  constructor <;> exact fun h x ξ hv hu ↦ h x (-ξ) hu (by rwa [neg_neg])

/-- **The product is commutative.** -/
protected theorem mul_comm (u v : 𝓓'(Ω, ℂ)) : u.mul v = v.mul u := by
  by_cases huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ v.waveFrontSet
  · refine eq_mul_of_forall_mem_nhds (forall_mem_waveFrontSet_neg_notMem_comm.1 huv)
      fun x₀ hx₀ ↦ ?_
    obtain ⟨U₁, hU₁, h₁⟩ := exists_mem_nhds_complexPairing_mul_eq_integral huv hx₀
    obtain ⟨U₂, hU₂, h₂⟩ := exists_mem_nhds_productDecay huv hx₀
    refine ⟨U₁ ∩ U₂, inter_mem hU₁ hU₂, fun φ θ hφ hθ hφθ ↦ ?_⟩
    rw [(h₁ φ θ (hφ.trans inter_subset_left) (hθ.trans inter_subset_left) hφθ).2]
    exact integral_localFourier_mul_comm
      (h₂ φ φ (hφ.trans inter_subset_right) (hφ.trans inter_subset_right)) hφθ
  · have hvu := mt forall_mem_waveFrontSet_neg_notMem_comm.2 huv
    rw [mul, mul, dite_eq_right huv, dite_eq_right hvu]

/-- **The product extends multiplication by smooth functions.** If `g` is smooth on `Ω`, the
product of `u` with the regular distribution `g` pairs a test function `θ` with `u (θ g)`. -/
theorem complexPairing_mul_ofFun (u : 𝓓'(Ω, ℂ)) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    {θ ψ : 𝓓(Ω, ℂ)} (hψ : ∀ x, ψ x = θ x * g x) :
    (u.mul (ofFun Ω g volume ⊤)).complexPairing θ = u.complexPairing ψ := by
  have huv : ∀ x ξ, (x, ξ) ∈ u.waveFrontSet → (x, -ξ) ∉ (ofFun Ω g volume ⊤).waveFrontSet :=
    fun x ξ _ ↦ by simp [waveFrontSet_ofFun_eq_empty hg]
  -- Split `θ` into pieces supported in the neighbourhoods of the Fourier formula.
  choose U hU hUf using fun x : Ω ↦ exists_mem_nhds_complexPairing_mul_eq_integral huv x.2
  obtain ⟨s, θs, hθs, hsum, -⟩ := θ.exists_sum_subordinate (fun x ↦ interior (U x))
    (fun _ ↦ isOpen_interior) fun x hx ↦
      mem_iUnion.2 ⟨⟨x, θ.tsupport_subset hx⟩, mem_interior_iff_mem_nhds.2 (hU ⟨x, _⟩)⟩
  have hpiece (i : s) (ψi : 𝓓(Ω, ℂ)) (hψi : ∀ x, ψi x = θs i x * g x) :
      (u.mul (ofFun Ω g volume ⊤)).complexPairing (θs i) = u.complexPairing ψi := by
    have hθU : tsupport (θs i) ⊆ U i := (hθs i).trans interior_subset
    obtain ⟨χ, -, hχ1, hχW⟩ := TestFunction.exists_cutoff_tsupport_subset (Ω := Ω) (n := ⊤)
      (θs i).hasCompactSupport (isOpen_interior.inter Ω.isOpen)
      (subset_inter (hθs i) (θs i).tsupport_subset) inter_subset_right
    let φ : 𝓓(Ω, ℂ) := postcompCLM (𝕜 := ℝ) ofRealCLM χ
    have hφU : tsupport φ ⊆ U i := (tsupport_comp_subset (map_zero ofRealCLM) _).trans
      (hχW.trans (inter_subset_left.trans interior_subset))
    have hφθ : EqOn φ 1 (tsupport (θs i)) := fun y hy ↦ by
      simp [φ, (hχ1.self_of_nhdsSet y hy)]
    rw [(hUf i φ (θs i) hφU hθU hφθ).2]
    exact integral_localFourier_ofFun hg hφθ hψi
  choose ψs hψs using fun i : s ↦ TestFunction.exists_coe_eq_smul_of_contDiffOn hg (θs i)
  have hψsum : ψ = ∑ i, ψs i := TestFunction.ext fun x ↦ by
    rw [hψ, ← hsum]
    simp [hψs, Finset.sum_mul, mul_comm (g x)]
  rw [← hsum, map_sum, hψsum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hpiece i (ψs i) fun x ↦ by
    rw [hψs]; exact mul_comm _ _

end Distribution

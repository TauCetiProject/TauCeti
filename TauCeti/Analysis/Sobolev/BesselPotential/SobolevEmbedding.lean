/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import TauCeti.Analysis.Sobolev.BesselPotential.Kernel
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TemperedDistribution.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.MeasureTheory.Integral.RieszPotential.Basic

/-!
# The Sobolev embedding of Bessel-potential spaces

Let `E` be a real inner product space of finite dimension `n`, `δ > 0` and `1 < p < q < ∞` with
`1 / q = 1 / p - δ / n`. Then

`H^{s + δ, p}(E, F) ⊆ H^{s, q}(E, F)`

continuously, for every real order `s` and every complex Banach space `F`
(`TemperedDistribution.MemSobolev.of_add_of_inv_eq`, `BesselPotentialSpace.sobolevEmbedding`).
Trading `δ` orders of smoothness for integrability, the exponent `q` is the one forced by scaling.

The proof writes the Bessel potential `J^{-δ}` on `Lᵖ` as convolution with the Bessel kernel `G_δ`
(`TemperedDistribution.besselPotential_neg_toTemperedDistribution_apply`): the symbol
`(1 + ‖ξ‖²) ^ (-δ / 2)` is the Fourier transform of the integrable kernel `G_δ`
(`TauCeti.fourier_besselKernel`), so the general convolution theorem for Fourier multipliers
applies. The kernel is dominated by the Riesz kernel `‖x‖ ^ (δ - n)`
(`TauCeti.besselKernel_le_mul_norm_rpow`), so `G_δ ⋆ f` is dominated by the Riesz potential of
`f`, which the Hardy–Littlewood–Sobolev inequality (`TauCeti.exists_eLpNorm_rieszPotential_le`)
bounds in `L^q`. Since `J^s u = J^{-δ} (J^{s + δ} u)`, an element of `H^{s + δ, p}` lies in
`H^{s, q}` (`TemperedDistribution.exists_besselPotential_neg_eq_and_norm_le`).

## Main declarations

* `TemperedDistribution.besselPotential_neg_toTemperedDistribution_apply`: `J^{-δ} f = G_δ ⋆ f`
  for `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`.
* `TemperedDistribution.exists_besselPotential_neg_eq_and_norm_le`: `J^{-δ}` maps `Lᵖ` boundedly
  into `L^q` for `1 < p` and `1 / q = 1 / p - δ / n`.
* `TemperedDistribution.MemSobolev.of_add_of_inv_eq`: the Sobolev embedding for the predicate.
* `BesselPotentialSpace.sobolevEmbedding`: the Sobolev embedding as a continuous linear map.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V,
  §2.2 and §3.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., §1.2 (Theorem 1.2.4 and Corollary 1.2.5).
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TemperedDistribution

omit [CompleteSpace F] in
/-- `J^{-δ}` is the Fourier multiplier with symbol `(1 + ‖ξ‖²) ^ (-δ / 2)`, the Fourier transform
of the Bessel kernel `G_δ` (`TauCeti.fourier_besselKernel`). -/
private theorem besselPotential_neg_eq_fourierMultiplierCLM (δ : ℝ) :
    besselPotential E F (-δ) =
      fourierMultiplierCLM F (fun ξ : E ↦ (((1 + ‖ξ‖ ^ 2) ^ (-δ / 2) : ℝ) : ℂ)) := by
  rw [besselPotential]

/-- **The Bessel potential of negative order is convolution with the Bessel kernel.** For `δ > 0`
and `f ∈ Lᵖ`, `1 ≤ p ≤ ∞`, the tempered distribution `J^{-δ} f` pairs with every test function
`φ` as the convolution `G_δ ⋆ f` does. -/
theorem besselPotential_neg_toTemperedDistribution_apply {δ : ℝ} (hδ : 0 < δ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (f : Lp F p (volume : Measure E)) (φ : 𝓢(E, ℂ)) :
    besselPotential E F (-δ) (f : 𝓢'(E, F)) φ =
      ∫ x, φ x • ((fun y ↦ (besselKernel δ y : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ]
        (f : E → F)) x := by
  rw [besselPotential_neg_eq_fourierMultiplierCLM]
  exact fourierMultiplierCLM_toTemperedDistribution_apply_of_fourier_eq
    (integrable_besselKernel hδ).ofReal (by fun_prop) (funext (fourier_besselKernel hδ)) f φ

omit [CompleteSpace F] in
/-- The convolution `G_δ ⋆ f` is dominated pointwise by a multiple of the Riesz potential of
order `δ` of `f`, for `0 < δ < n`. -/
private theorem exists_eNorm_besselKernel_convolution_le {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ < Module.finrank ℝ E) :
    ∃ c : ℝ, ∀ (f : E → F) (x : E),
      ‖((fun y ↦ (besselKernel δ y : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) x‖ₑ ≤
        rieszPotential volume δ (c • f) x := by
  set c : ℝ := Real.Gamma ((Module.finrank ℝ E - δ) / 2) / Real.Gamma (δ / 2) *
    Real.pi ^ (δ - Module.finrank ℝ E / 2)
  have hc : 0 < c := by
    have := Real.Gamma_pos_of_pos (by linarith : 0 < (Module.finrank ℝ E - δ) / 2)
    have := Real.Gamma_pos_of_pos (half_pos hδ)
    positivity
  -- The kernel bound in `ℝ≥0∞`, where at `z = 0` the Riesz kernel is `∞`.
  have hK : ∀ z : E, ‖(besselKernel δ z : ℂ)‖ₑ ≤ ‖c‖ₑ * ‖z‖ₑ ^ (δ - Module.finrank ℝ E) := by
    intro z
    rcases eq_or_ne z 0 with rfl | hz
    · rw [eNorm_zero, ENNReal.zero_rpow_of_neg (by linarith),
        ENNReal.mul_top (by simpa using hc.ne')]
      exact le_top
    calc ‖(besselKernel δ z : ℂ)‖ₑ = ENNReal.ofReal (besselKernel δ z) := by
          rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (besselKernel_nonneg hδ z)]
      _ ≤ ENNReal.ofReal (c * ‖z‖ ^ (δ - Module.finrank ℝ E)) :=
          ENNReal.ofReal_le_ofReal (besselKernel_le_mul_norm_rpow hδ hδn hz)
      _ = ‖c‖ₑ * ‖z‖ₑ ^ (δ - Module.finrank ℝ E) := by
          rw [ENNReal.ofReal_mul hc.le, Real.eNorm_of_nonneg hc.le, ← ofReal_norm z,
            ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hz)]
  refine ⟨c, fun f x ↦ ?_⟩
  rw [convolution_eq_swap, rieszPotential_def]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (lintegral_mono fun y ↦ ?_)
  rw [ContinuousLinearMap.lsmul_apply, eNorm_smul, Pi.smul_apply, eNorm_smul, mul_left_comm]
  exact (mul_le_mul_left (hK (x - y)) _).trans_eq (mul_assoc _ _ _)

omit [CompleteSpace F] in
/-- **Hardy–Littlewood–Sobolev for the Bessel kernel.** For `0 < δ < n`, `1 < p` and
`1 / q = 1 / p - δ / n`, convolution with `G_δ` is bounded from `Lᵖ` to `L^q`. -/
private theorem exists_eLpNorm_besselKernel_convolution_le {δ : ℝ} (hδ : 0 < δ)
    (hδn : δ < Module.finrank ℝ E) {p q : ℝ≥0} (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) :
    ∃ C : ℝ≥0, ∀ f : E → F, AEStronglyMeasurable f →
      eLpNorm ((fun y ↦ (besselKernel δ y : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) q volume ≤
        C * eLpNorm f p volume := by
  obtain ⟨c, hc⟩ := exists_eNorm_besselKernel_convolution_le (F := F) hδ hδn
  obtain ⟨C, hC⟩ := exists_eLpNorm_rieszPotential_le (F := F) volume hδ hp hpq
  refine ⟨C * ‖c‖₊, fun f hf ↦ ?_⟩
  have hmeas := (integrable_besselKernel (E := E) hδ).ofReal.aestronglyMeasurable.convolution
    (ContinuousLinearMap.lsmul ℂ ℂ) hf
  calc eLpNorm ((fun y ↦ (besselKernel δ y : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ] f) q volume
      ≤ eLpNorm (rieszPotential volume δ (c • f)) q volume :=
        eLpNorm_mono_eNorm hmeas fun x ↦ (hc f x).trans_eq (eNorm_eq_self _).symm
    _ ≤ C * eLpNorm (c • f) p volume := hC _
    _ = (C * ‖c‖₊ : ℝ≥0) * eLpNorm f p volume := by
      rw [eLpNorm_const_smul, ← mul_assoc, ENNReal.coe_mul, eNorm_eq_nnNorm]

/-- **The Bessel potential `J^{-δ}` maps `Lᵖ` to `L^q`.** For `δ > 0`, `1 < p` and
`1 / q = 1 / p - δ / n`, where `n` is the dimension of `E`, there is `C` such that for every
`f ∈ Lᵖ` the tempered distribution `J^{-δ} f` is an `L^q` function `g` with
`‖g‖_q ≤ C ‖f‖_p`. -/
theorem exists_besselPotential_neg_eq_and_norm_le {δ : ℝ} (hδ : 0 < δ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) :
    ∃ C : ℝ, ∀ f : Lp F p (volume : Measure E), ∃ g : Lp F q (volume : Measure E),
      besselPotential E F (-δ) (f : 𝓢'(E, F)) = g ∧ ‖g‖ ≤ C * ‖f‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In dimension zero `q = p` and `J^{-δ}` is the identity.
    obtain rfl : q = p := by
      rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, div_zero, sub_zero] at hpq
      exact_mod_cast inv_injective hpq
    exact ⟨1, fun f ↦ ⟨f, by rw [besselPotential_eq_id_of_subsingleton,
      ContinuousLinearMap.id_apply], (one_mul _).symm.le⟩⟩
  -- Otherwise `δ < n`, since `0 < 1 / q = 1 / p - δ / n < 1 - δ / n`.
  have hδn : δ < Module.finrank ℝ E := by
    have hq : (0 : ℝ) < q := NNReal.coe_pos.2 <| zero_lt_one.trans_le <|
      ENNReal.one_le_coe_iff.1 Fact.out
    have hp' : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp)
    exact (div_lt_one (by exact_mod_cast Module.finrank_pos)).1 (by linarith [inv_pos.2 hq])
  obtain ⟨C, hC⟩ := exists_eLpNorm_besselKernel_convolution_le (F := F) hδ hδn hp hpq
  refine ⟨C, fun f ↦ ?_⟩
  rw [besselPotential_neg_eq_fourierMultiplierCLM]
  obtain ⟨g, hg, -, hgf⟩ := exists_fourierMultiplierCLM_toTemperedDistribution_eq_of_eLpNorm_le
    (integrable_besselKernel hδ).ofReal (by fun_prop) (funext (fourier_besselKernel hδ)) f
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_lt_top f).ne)
    (hC f (Lp.aestronglyMeasurable f))
  refine ⟨g, hg, ?_⟩
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ← Lp.norm_def] at hgf
  exact hgf

/-- **The Sobolev embedding of Bessel-potential spaces.** For `δ > 0`, `1 < p` and
`1 / q = 1 / p - δ / n`, where `n` is the dimension of `E`, every tempered distribution in
`H^{s + δ, p}` lies in `H^{s, q}`. -/
theorem MemSobolev.of_add_of_inv_eq {δ s : ℝ} (hδ : 0 < δ) {p q : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))] (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) {u : 𝓢'(E, F)}
    (hu : u.MemSobolev (s + δ) p) : u.MemSobolev s q := by
  obtain ⟨f, hf⟩ := hu
  obtain ⟨C, hC⟩ := exists_besselPotential_neg_eq_and_norm_le (F := F) hδ hp hpq
  obtain ⟨g, hg, -⟩ := hC f
  refine ⟨g, ?_⟩
  rw [← hg, ← hf, besselPotential_besselPotential_apply, add_neg_cancel_right]

end TemperedDistribution

namespace BesselPotentialSpace

open TemperedDistribution

variable {δ s : ℝ} {p q : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

variable (E F s) in
/-- **The Sobolev embedding** `H^{s + δ, p}(E, F) ⊆ H^{s, q}(E, F)` as a continuous linear map,
for `δ > 0`, `1 < p` and `1 / q = 1 / p - δ / n`, where `n` is the dimension of `E`. It keeps the
underlying tempered distribution (`BesselPotentialSpace.toDistr_sobolevEmbedding`); at the level
of the predicate it is `TemperedDistribution.MemSobolev.of_add_of_inv_eq`. -/
def sobolevEmbedding (hδ : 0 < δ) (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) :
    H^{s + δ, p}(E, F) →L[ℂ] H^{s, q}(E, F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memSobolev_toDistr.of_add_of_inv_eq hδ hp hpq).toBesselPotentialSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) } <| by
    -- The `L^q` function of the image is `J^{-δ}` of the `Lᵖ` function `J^{s + δ} u` of `u`.
    obtain ⟨C, hC⟩ := exists_besselPotential_neg_eq_and_norm_le (F := F) hδ hp hpq
    refine ⟨C, fun u ↦ ?_⟩
    obtain ⟨g, hg, hgu⟩ := hC u.toLp
    set v := (u.memSobolev_toDistr.of_add_of_inv_eq hδ hp hpq).toBesselPotentialSpace
    have hv : v.toLp = g := Lp.toTemperedDistribution_injective <| by
      dsimp only
      rw [← v.bessel_toDistr_eq_toLp, ← hg, ← u.bessel_toDistr_eq_toLp,
        besselPotential_besselPotential_apply, add_neg_cancel_right,
        MemSobolev.toBesselPotentialSpace_toDistr]
    rw [← hv] at hgu
    simpa [← norm_toLp_eq] using hgu

@[simp]
theorem toDistr_sobolevEmbedding (hδ : 0 < δ) (hp : 1 < p)
    (hpq : (q : ℝ)⁻¹ = (p : ℝ)⁻¹ - δ / Module.finrank ℝ E) (u : H^{s + δ, p}(E, F)) :
    (sobolevEmbedding E F s hδ hp hpq u).toDistr = u.toDistr := by
  simp [sobolevEmbedding]

end BesselPotentialSpace

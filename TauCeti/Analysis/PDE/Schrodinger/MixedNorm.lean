/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Duhamel
public import TauCeti.Analysis.PDE.Schrodinger.Strichartz
import TauCeti.Analysis.PDE.Schrodinger.Endpoint
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.MixedNorm.Bounded

/-!
# Strichartz estimates for the Schrödinger equation in mixed norms

On a finite-dimensional real inner product space `E` of dimension `n`, let `S(t) = exp(itΔ)` be
the Schrödinger propagator. A pair `(q, r)` is an admissible pair with a finite time exponent when
`2 ≤ q < ∞` and `2 / q + n / r = n / 2`, with `n ≥ 3` when `q = 2`; then `2 ≤ r ≤ ∞`. For `2 < q`
it is a non-endpoint pair, and `r = ∞` occurs only on the line, at `(4, ∞)`; for `q = 2` it is the
endpoint pair `(2, 2n / (n - 2))` of Keel and Tao. Write `p` for the Hölder conjugate of `q`. The
`TT*` argument of `TauCeti.Analysis.PDE.Schrodinger.Strichartz` and the endpoint argument of
`TauCeti.Analysis.PDE.Schrodinger.Endpoint` bound the pairings of `S(t) f` and of the retarded
Duhamel integral with `L²`-valued test functions. Duality for mixed norms
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`) turns
these weak estimates into bounds in the mixed norm
`‖u‖_{L^q_t L^r_x} = ‖t ↦ ‖u(t)‖_{L^r}‖_{L^q}`, for every `r ≤ ∞`:

* the homogeneous estimate `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂`
  (`TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_le`), with its case
  `‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂` on the line
  (`TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_le_of_finrank_eq_one`);
* the retarded estimate, for two such pairs `(q, r)` and `(q₁, r₁)`,
  `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{p₁}_t L^{r₁'}_x}` for forcing terms
  `F : ℝ → L²(E)` integrable in time, where `p₁` and `r₁'` are the Hölder conjugates of `q₁` and
  `r₁` (`TauCeti.exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le`);
* the Strichartz estimate for the mild solution `u = TauCeti.schrodingerDuhamel f F` of the
  inhomogeneous equation `i ∂ₜu + Δu = F`, `u(0) = f`, on a time interval `[0, T]`, for two such
  pairs: `‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖F‖_{L^{p₁}((0, T]; L^{r₁'})})` with `C` independent
  of `T` (`TauCeti.exists_eLpNorm_eLpNorm_schrodingerDuhamel_le`).

The pairs may coincide, either or both may be the endpoint pair, and on the line either may be
`(4, ∞)`. The forcing term is assumed integrable on `(0, T]` with values in `L²`, so that
Duhamel's formula is a Bochner integral; the energy estimate `TauCeti.norm_schrodingerDuhamel_le`
and `TauCeti.Analysis.PDE.Schrodinger.EnergyPair` give the companion bounds at the energy pair
`(∞, 2)`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980,
  Theorem 1.2 and Corollary 1.3.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q p₁ q₁ : ℝ≥0} {r r₁ r₁' : ℝ≥0∞}
  [r₁'.HolderConjugate r₁]

/-- **The Strichartz estimate for the Schrödinger equation** in every dimension `n`, at an
admissible pair with a finite time exponent: `2 ≤ q < ∞` and `2 / q + n / r = n / 2`, with `n ≥ 3`
when `q = 2`, where `p` is the Hölder conjugate of `q`. There is `C` such that for every
`f ∈ L²(E)`,

`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂`.

For `q = 2` this is the endpoint estimate of Keel and Tao, and on the line it includes the pair
`(4, ∞)`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerPropagator_le (hq : 2 ≤ q)
    (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume ≤ C * ‖f‖ₑ := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun f ↦ by simp [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]⟩
  have hr2 := two_le_of_admissible (zero_lt_two.trans_le hq) hr0 hqr
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  rcases hq.eq_or_lt with rfl | hq
  · obtain ⟨C, hC⟩ := exists_enorm_integral_inner_schrodingerPropagator_le_of_endpoint
      (r' := (1 - r⁻¹)⁻¹) (hn rfl) (by simpa using hqr)
    refine ⟨C, fun f ↦ ?_⟩
    simpa using (continuous_phasePropagator_apply laplacianSymbol f).aestronglyMeasurable
      |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (p' := 2) (q' := (1 - r⁻¹)⁻¹)
        fun G hG _ ↦ hC f G hG
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_inner_schrodingerPropagator_le (r' := (1 - r⁻¹)⁻¹) hq hpq hqr
  have := hpq.symm.coe_ennreal
  exact ⟨C, fun f ↦ (continuous_phasePropagator_apply laplacianSymbol f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (p' := p) (q' := (1 - r⁻¹)⁻¹)
      fun G hG _ ↦
        hC f G hG.aestronglyMeasurable
          (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG)⟩

/-- **The Strichartz estimate for the Schrödinger equation on the line**, at the admissible pair
`(4, ∞)`. There is `C` such that for every `f ∈ L²(E)` on a one-dimensional space `E`,

`‖S(t) f‖_{L⁴_t L^∞_x} ≤ C ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerPropagator_le_of_finrank_eq_one
    (hE : Module.finrank ℝ E = 1) :
    ∃ C : ℝ≥0, ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) ∞ volume) 4 volume ≤ C * ‖f‖ₑ := by
  have hpq : (4 / 3 : ℝ≥0).HolderConjugate 4 := by
    rw [← NNReal.holderConjugate_coe_iff, Real.holderConjugate_iff]
    norm_num
  simpa using exists_eLpNorm_eLpNorm_schrodingerPropagator_le (E := E) (r := ∞)
    (by norm_num : (2 : ℝ≥0) ≤ 4) (by norm_num) hpq (by simp [hE]; norm_num)

/-- **The retarded Strichartz estimate for the Schrödinger equation** in every dimension `n`, for
any two admissible pairs with finite time exponents: `2 ≤ q, q₁ < ∞` with `2 / q + n / r = n / 2`
and `2 / q₁ + n / r₁ = n / 2`, and `n ≥ 3` when `q = 2` or `q₁ = 2`, where `p₁` and `r₁'` are the
Hölder conjugates of `q₁` and `r₁`. There is `C` such that for every forcing term `F : ℝ → L²(E)`
that is integrable in time,

`‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{p₁}_t L^{r₁'}_x}`.

The two pairs may coincide, either or both may be the endpoint pair, and on the line either may
be `(4, ∞)`. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le (hq : 2 ≤ q)
    (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
      eLpNorm (fun t ↦ eLpNorm ((∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ volume := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun F _ ↦ by simp [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]⟩
  have hr2 := two_le_of_admissible (zero_lt_two.trans_le hq) hr0 hqr
  have := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le_of_integrable
      (r' := (1 - r⁻¹)⁻¹) (r₁' := r₁') hq hn hpq hqr hq₁ hn₁ hpq₁ hqr₁
  have := hpq.symm.coe_ennreal
  refine ⟨C, fun F hF ↦ (aestronglyMeasurable_setIntegral_Iio_phasePropagator_sub laplacianSymbol
    hF.aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) (p' := p)
      (q' := (1 - r⁻¹)⁻¹) fun G hG _ ↦ ?_)⟩
  -- Move the pairing with `G t` inside the integral over `s < t`.
  simp_rw [inner_setIntegral_Iio_phasePropagator_sub _ hF]
  exact hC F G hF.aestronglyMeasurable hG.aestronglyMeasurable
    (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hF)
    (integrable_phasePropagator_apply _ continuous_neg.aestronglyMeasurable hG)

/-- **The Strichartz estimate for the inhomogeneous Schrödinger equation** in every dimension `n`,
for any two admissible pairs with finite time exponents: `2 ≤ q, q₁ < ∞` with
`2 / q + n / r = n / 2` and `2 / q₁ + n / r₁ = n / 2`, and `n ≥ 3` when `q = 2` or `q₁ = 2`, where
`p₁` and `r₁'` are the Hölder conjugates of `q₁` and `r₁`. There is `C` such that for every `T`,
every initial value `f ∈ L²(E)` and every forcing term `F : ℝ → L²(E)` integrable on `(0, T]`, the
mild solution `u = TauCeti.schrodingerDuhamel f F` of `i ∂ₜu + Δu = F`, `u(0) = f`, satisfies

`‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖F‖_{L^{p₁}((0, T]; L^{r₁'})})`.

The constant does not depend on `T`. The two pairs may coincide, either or both may be the
endpoint pair, and on the line either may be `(4, ∞)`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerDuhamel_le (hq : 2 ≤ q)
    (hn : q = 2 → 2 < Module.finrank ℝ E) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hq₁ : 2 ≤ q₁) (hn₁ : q₁ = 2 → 2 < Module.finrank ℝ E) (hpq₁ : p₁.HolderConjugate q₁)
    (hqr₁ : 2 / (q₁ : ℝ) + Module.finrank ℝ E * (r₁⁻¹).toReal = Module.finrank ℝ E / 2) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (F : ℝ → Lp ℂ 2 (volume : Measure E))
      (T : ℝ), IntegrableOn F (Ioc 0 T) →
      eLpNorm (fun t ↦ eLpNorm (schrodingerDuhamel f F t) r volume) q
          (volume.restrict (Icc 0 T)) ≤
        C * (‖f‖ₑ + eLpNorm (fun s ↦ eLpNorm (F s) r₁' volume) p₁ (volume.restrict (Ioc 0 T))) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨0, fun f F T _ ↦ by simp [eLpNorm_exponent_zero (Lp.aestronglyMeasurable _)]⟩
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_eLpNorm_schrodingerPropagator_le hq hn hpq hqr
  obtain ⟨C₂, hC₂⟩ := exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le
    (r₁' := r₁') hq hn hpq hqr hq₁ hn₁ hpq₁ hqr₁
  refine ⟨C₁ + C₂, fun f F T hF ↦ ?_⟩
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast one_le_two.trans hq
  have hr2 := two_le_of_admissible (zero_lt_two.trans_le hq) hr0 hqr
  set FT := (Ioc 0 T).indicator F
  have hFT : Integrable FT := (integrable_indicator_iff measurableSet_Ioc).2 hF
  set Φ := fun t ↦ ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (FT s)
  -- On `[0, T]` the `Lʳ` norm of `u(t)` is at most that of `S(t) f` plus that of `Φ(t)`.
  have hle : ∀ᵐ t ∂volume.restrict (Icc 0 T), ‖eLpNorm (schrodingerDuhamel f F t) r volume‖ₑ ≤
      ‖eLpNorm (schrodingerPropagator ℂ t f) r volume + eLpNorm (Φ t) r volume‖ₑ := by
    refine ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ ?_
    simp only [eNorm_eq_self]
    rw [schrodingerDuhamel_eq_sub_setIntegral_Iio f F ht,
      eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
    refine (eLpNorm_sub_le (one_le_two.trans hr2)).trans_eq ?_
    rw [eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I,
      ENNReal.ofReal_one, one_mul]
  have hmeas : AEStronglyMeasurable (fun t ↦ eLpNorm (schrodingerDuhamel f F t) r volume)
      (volume.restrict (Icc 0 T)) :=
    (AEStronglyMeasurable.aemeasurable_eLpNorm_Lp
      ((continuousOn_schrodingerDuhamel_Icc f hF).aestronglyMeasurable measurableSet_Icc)
      .rfl r).aestronglyMeasurable
  -- The forcing norms of `F` on `(0, T]` are those of the cut-off forcing term on the line.
  have hFTnorm : (fun s ↦ eLpNorm (FT s) r₁' volume) =
      (Ioc 0 T).indicator fun s ↦ eLpNorm (F s) r₁' volume := by
    ext s
    by_cases hs : s ∈ Ioc 0 T
    · simp [FT, hs]
    · simp only [FT, Set.indicator_of_notMem hs]
      exact (eLpNorm_congr_ae (Lp.coeFn_zero _ _ _)).trans eLpNorm_zero
  calc _ ≤ eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume +
          eLpNorm (Φ t) r volume) q (volume.restrict (Icc 0 T)) := eLpNorm_mono_eNorm_ae hmeas hle
    _ ≤ eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume +
          eLpNorm (fun t ↦ eLpNorm (Φ t) r volume) q volume :=
        (eLpNorm_add_le hq1).trans (add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self)
          (eLpNorm_mono_measure _ Measure.restrict_le_self))
    _ ≤ C₁ * ‖f‖ₑ + C₂ * eLpNorm (fun s ↦ eLpNorm (FT s) r₁' volume) p₁ volume :=
        add_le_add (hC₁ f) (hC₂ FT hFT)
    _ ≤ _ := by
        rw [hFTnorm, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet,
          ENNReal.coe_add, add_mul, mul_add, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

end TauCeti

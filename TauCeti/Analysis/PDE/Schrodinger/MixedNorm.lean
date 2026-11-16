/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Duhamel
public import TauCeti.Analysis.PDE.Schrodinger.Strichartz
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.MixedNorm

/-!
# Strichartz estimates for the Schrödinger equation in mixed norms

On a finite-dimensional real inner product space `E` of dimension `n`, let `S(t) = exp(itΔ)` be
the Schrödinger propagator and let `(q, r)` be a non-endpoint admissible pair with finite `r`:
`2 < q < ∞`, `2 / q + n / r = n / 2` and `r < ∞`, with Hölder conjugates `q'` and `r'`. The `TT*`
argument of `TauCeti.Analysis.PDE.Schrodinger.Strichartz` bounds the pairings of `S(t) f` and of
the retarded Duhamel integral with `L²`-valued test functions. Testing against truncated extremal
functions
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le`) turns
these weak estimates into bounds in the mixed norm
`‖u‖_{L^q_t L^r_x} = ‖t ↦ ‖u(t)‖_{L^r}‖_{L^q}`:

* the homogeneous estimate `‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂`
  (`TauCeti.exists_eLpNorm_eLpNorm_schrodingerPropagator_le`);
* the retarded estimate `‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^{q'}_t L^{r'}_x}`
  for forcing terms `F : ℝ → L²(E)` integrable in time
  (`TauCeti.exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le`);
* the Strichartz estimate for the mild solution `u = TauCeti.schrodingerDuhamel f F` of the
  inhomogeneous equation `i ∂ₜu + Δu = F`, `u(0) = f`, on a time interval `[0, T]`:
  `‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖F‖_{L^{q'}((0, T]; L^{r'})})` with `C` independent of `T`
  (`TauCeti.exists_eLpNorm_eLpNorm_schrodingerDuhamel_le`).

The forcing term is assumed integrable on `(0, T]` with values in `L²`, so that Duhamel's formula is
a Bochner integral; the energy estimate `TauCeti.norm_schrodingerDuhamel_le` is the companion bound
at the energy pair `(∞, 2)`. The endpoint `q = 2` and the pair `(4, ∞)` on the line are not covered
here.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Theorem 2.3.
* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {p q : ℝ≥0} {r r' : ℝ≥0∞} [r'.HolderConjugate r]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Admissibility `2 / q + n / r = n / 2` with `2 < q` forces `2 ≤ r`. -/
private theorem two_le_of_admissible (hq : 2 < q) (hr0 : r ≠ 0)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2) :
    2 ≤ r := by
  have hq0 : (0 : ℝ) < 2 / q := div_pos two_pos (by exact_mod_cast zero_lt_two.trans hq)
  have hlt : (r⁻¹).toReal < 2⁻¹ := by nlinarith
  rw [← ENNReal.inv_le_inv, ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hr0),
    ← ENNReal.ofReal_toReal (a := 2⁻¹) (by simp)]
  exact ENNReal.ofReal_le_ofReal (hlt.le.trans_eq (by simp))

/-- For `G` integrable in time with values in `L²`, so is `t ↦ S(-t) G(t)`. -/
private theorem integrable_schrodingerPropagator_neg_apply {G : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hG : Integrable G) : Integrable fun t ↦ schrodingerPropagator ℂ (-t) (G t) :=
  hG.norm.mono' ((continuous_phasePropagator_uncurry laplacianSymbol).comp_aestronglyMeasurable
    (continuous_neg.aestronglyMeasurable.prodMk hG.aestronglyMeasurable))
    (ae_of_all _ fun _ ↦ (norm_phasePropagator_apply _ _ _).le)

/-- For `F` integrable in time with values in `L²`, so is `s ↦ S(t - s) F(s)`, for every `t`. -/
private theorem integrable_schrodingerPropagator_sub_apply {F : ℝ → Lp ℂ 2 (volume : Measure E)}
    (hF : Integrable F) (t : ℝ) : Integrable fun s ↦ schrodingerPropagator ℂ (t - s) (F s) :=
  hF.norm.mono' ((continuous_phasePropagator_uncurry laplacianSymbol).comp_aestronglyMeasurable
    ((continuous_const.sub continuous_id).aestronglyMeasurable.prodMk hF.aestronglyMeasurable))
    (ae_of_all _ fun _ ↦ (norm_phasePropagator_apply _ _ _).le)

/-- The retarded Duhamel integral `t ↦ ∫_{s < t} S(t - s) F(s) ds` of a forcing term `F` integrable
in time is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_setIntegral_Iio_schrodingerPropagator_sub
    {F : ℝ → Lp ℂ 2 (volume : Measure E)} (hF : Integrable F) :
    AEStronglyMeasurable fun t ↦ ∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) := by
  -- The integrand on the half-plane `s < t`, as a function of `(t, s)`.
  set K : ℝ × ℝ → Lp ℂ 2 (volume : Measure E) := {q : ℝ × ℝ | q.2 < q.1}.indicator
    fun q ↦ schrodingerPropagator ℂ (q.1 - q.2) (F q.2)
  have hK : AEStronglyMeasurable K (volume.prod volume) :=
    ((continuous_phasePropagator_uncurry laplacianSymbol).comp_aestronglyMeasurable
      ((continuous_fst.sub continuous_snd).aestronglyMeasurable.prodMk
        hF.aestronglyMeasurable.comp_snd)).indicator
      (measurableSet_lt measurable_snd measurable_fst)
  refine hK.integral_prod_right'.congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  -- `(t, s)` lies in the half-plane `s < t` exactly when `s ∈ Iio t`.
  rw [← integral_indicator measurableSet_Iio]
  rfl

/-- **The Strichartz estimate for the Schrödinger equation** in every dimension `n`, at a
non-endpoint admissible pair with finite `r`: `2 < q < ∞`, `2 / q + n / r = n / 2` and
`0 < r < ∞`, with `p` the Hölder conjugate of `q`. There is `C` such that for every `f ∈ L²(E)`,

`‖S(t) f‖_{L^q_t L^r_x} ≤ C ‖f‖₂`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerPropagator_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hr0 : r ≠ 0) (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp ℂ 2 (volume : Measure E),
      eLpNorm (fun t ↦ eLpNorm (schrodingerPropagator ℂ t f) r volume) q volume ≤ C * ‖f‖ₑ := by
  have hr2 := two_le_of_admissible hq hr0 hqr
  -- Test against `L^{r'}` with `r'` the Hölder conjugate of `r`.
  have hrr := ENNReal.HolderConjugate.inv_one_sub_inv' (one_le_two.trans hr2)
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_inner_schrodingerPropagator_le (r' := (1 - r⁻¹)⁻¹) hq hpq hqr
  have := hpq.symm.coe_ennreal
  exact ⟨C, fun f ↦ (continuous_phasePropagator_apply laplacianSymbol f).aestronglyMeasurable
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (q' := p) (r' := (1 - r⁻¹)⁻¹)
      ENNReal.coe_ne_top hr hr2 fun G hG _ ↦
        hC f G hG.aestronglyMeasurable (integrable_schrodingerPropagator_neg_apply hG)⟩

/-- **The retarded Strichartz estimate for the Schrödinger equation** in every dimension `n`, at a
non-endpoint admissible pair with finite `r`: `2 < q < ∞`, `2 / q + n / r = n / 2` and `r < ∞`,
with `p` and `r'` the Hölder conjugates of `q` and `r`. There is `C` such that for every forcing
term `F : ℝ → L²(E)` that is integrable in time,

`‖∫_{s < t} S(t - s) F(s) ds‖_{L^q_t L^r_x} ≤ C ‖F‖_{L^p_t L^{r'}_x}`. -/
theorem exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le (hq : 2 < q)
    (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ F : ℝ → Lp ℂ 2 (volume : Measure E), Integrable F →
      eLpNorm (fun t ↦ eLpNorm ((∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) :
          Lp ℂ 2 (volume : Measure E))) r volume) q volume ≤
        C * eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p volume := by
  obtain ⟨C, hC⟩ :=
    exists_enorm_integral_setIntegral_Iio_inner_schrodingerPropagator_sub_le (r' := r') hq hpq hqr
  have := hpq.symm.coe_ennreal
  refine ⟨C, fun F hF ↦ (aestronglyMeasurable_setIntegral_Iio_schrodingerPropagator_sub hF
    |>.eLpNorm_eLpNorm_le_of_forall_enorm_integral_inner_le (𝕜 := ℂ) (q' := p) (r' := r')
      ENNReal.coe_ne_top hr (two_le_of_admissible hq (ENNReal.HolderConjugate.ne_zero r r') hqr)
      fun G hG _ ↦ ?_)⟩
  -- Move the pairing with `G t` inside the integral over `s < t`.
  have hpair (t : ℝ) : ⟪(∫ s in Iio t, schrodingerPropagator ℂ (t - s) (F s) :
      Lp ℂ 2 (volume : Measure E)), G t⟫_ℂ =
      ∫ s in Iio t, ⟪schrodingerPropagator ℂ (t - s) (F s), G t⟫_ℂ := by
    rw [← inner_conj_symm, ← integral_inner
      (integrable_schrodingerPropagator_sub_apply hF t).integrableOn, ← integral_conj]
    simp_rw [inner_conj_symm]
  simp_rw [hpair]
  exact hC F G hF.aestronglyMeasurable hG.aestronglyMeasurable

/-- On `[0, T]`, Duhamel's formula is the free evolution minus `i` times the retarded integral of
the forcing term cut off to `(0, T]`. -/
private theorem schrodingerDuhamel_eq_sub_setIntegral_Iio (f : Lp ℂ 2 (volume : Measure E))
    (F : ℝ → Lp ℂ 2 (volume : Measure E)) {T t : ℝ} (ht : t ∈ Icc 0 T) :
    schrodingerDuhamel f F t = schrodingerPropagator ℂ t f - Complex.I •
      ∫ s in Iio t, schrodingerPropagator ℂ (t - s) ((Ioc 0 T).indicator F s) := by
  have hset : Iio t ∩ Ioc 0 T = Ioo 0 t := by
    ext s
    simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, h2.le.trans ht.2⟩
  have hind (s : ℝ) : schrodingerPropagator ℂ (t - s) ((Ioc 0 T).indicator F s) =
      (Ioc 0 T).indicator (fun s ↦ schrodingerPropagator ℂ (t - s) (F s)) s := by
    by_cases hs : s ∈ Ioc 0 T <;> simp [hs]
  simp_rw [schrodingerDuhamel_def, hind, setIntegral_indicator measurableSet_Ioc, hset,
    intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]

/-- **The Strichartz estimate for the inhomogeneous Schrödinger equation** in every dimension `n`,
at a non-endpoint admissible pair with finite `r`: `2 < q < ∞`, `2 / q + n / r = n / 2` and
`r < ∞`, with `p` and `r'` the Hölder conjugates of `q` and `r`. There is `C` such that for every
`T`, every initial value `f ∈ L²(E)` and every forcing term `F : ℝ → L²(E)` integrable on `(0, T]`,
the mild solution `u = TauCeti.schrodingerDuhamel f F` of `i ∂ₜu + Δu = F`, `u(0) = f`, satisfies

`‖u‖_{L^q([0, T]; L^r)} ≤ C (‖f‖₂ + ‖F‖_{L^p((0, T]; L^{r'})})`.

The constant does not depend on `T`. -/
theorem exists_eLpNorm_eLpNorm_schrodingerDuhamel_le (hq : 2 < q) (hpq : p.HolderConjugate q)
    (hqr : 2 / (q : ℝ) + Module.finrank ℝ E * (r⁻¹).toReal = Module.finrank ℝ E / 2)
    (hr : r ≠ ∞) :
    ∃ C : ℝ≥0, ∀ (f : Lp ℂ 2 (volume : Measure E)) (F : ℝ → Lp ℂ 2 (volume : Measure E))
      (T : ℝ), IntegrableOn F (Ioc 0 T) →
      eLpNorm (fun t ↦ eLpNorm (schrodingerDuhamel f F t) r volume) q
          (volume.restrict (Icc 0 T)) ≤
        C * (‖f‖ₑ + eLpNorm (fun s ↦ eLpNorm (F s) r' volume) p (volume.restrict (Ioc 0 T))) := by
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_eLpNorm_schrodingerPropagator_le hq hpq hqr
    (ENNReal.HolderConjugate.ne_zero r r') hr
  obtain ⟨C₂, hC₂⟩ :=
    exists_eLpNorm_eLpNorm_setIntegral_Iio_schrodingerPropagator_sub_le (r' := r') hq hpq hqr hr
  refine ⟨C₁ + C₂, fun f F T hF ↦ ?_⟩
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast one_le_two.trans hq.le
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
    refine (eLpNorm_sub_le (one_le_two.trans (two_le_of_admissible hq
      (ENNReal.HolderConjugate.ne_zero r r') hqr))).trans_eq ?_
    rw [eLpNorm_congr_ae (Lp.coeFn_smul _ _), eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I,
      ENNReal.ofReal_one, one_mul]
  have hmeas : AEStronglyMeasurable (fun t ↦ eLpNorm (schrodingerDuhamel f F t) r volume)
      (volume.restrict (Icc 0 T)) :=
    (AEStronglyMeasurable.aemeasurable_eLpNorm_Lp
      ((continuousOn_schrodingerDuhamel_Icc f hF).aestronglyMeasurable measurableSet_Icc)
      .rfl r).aestronglyMeasurable
  -- The forcing norms of `F` on `(0, T]` are those of the cut-off forcing term on the line.
  have hFTnorm : (fun s ↦ eLpNorm (FT s) r' volume) =
      (Ioc 0 T).indicator fun s ↦ eLpNorm (F s) r' volume := by
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
    _ ≤ C₁ * ‖f‖ₑ + C₂ * eLpNorm (fun s ↦ eLpNorm (FT s) r' volume) p volume :=
        add_le_add (hC₁ f) (hC₂ FT hFT)
    _ ≤ _ := by
        rw [hFTnorm, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioc.nullMeasurableSet,
          ENNReal.coe_add, add_mul, mul_add, mul_add]
        gcongr
        · exact le_self_add
        · exact le_add_self

end TauCeti

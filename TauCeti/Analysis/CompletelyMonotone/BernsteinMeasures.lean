/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import TauCeti.Analysis.CompletelyMonotone.BernsteinAux

/-!
# Approximating measures for Bernstein's theorem

The Chafaï-style construction of the representing measure in Bernstein's theorem. For a
completely monotone `f` the densities `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` are nonnegative,
define finite measures `cm_measure f n` whose total mass is bounded by `f(0) - f(∞)`, and after
the rescaling `t ↦ (n-1)/t` give measures `cm_rescaled f n` supported on `[0, ∞)` whose Laplace
kernels `(1 - xp/(n-1))₊ⁿ⁻¹` converge to `e^{-xp}`. These feed the Prokhorov tightness argument.

Ported from the sorry-free `mrdouglasny/hille-yosida` (`HilleYosida.BernsteinMeasures`); the
`IsCompletelyMonotone` predicate and the analytic lemmas it relies on match TauCeti's
`CompletelyMonotone/Basic.lean` and `CompletelyMonotone/BernsteinAux.lean`.

## Main declarations

* `TauCeti.cm_density`, `TauCeti.cm_measure`: the approximating densities and measures.
* `TauCeti.IsCompletelyMonotone.neg_deriv_integrableOn`,
  `TauCeti.IsCompletelyMonotone.integral_Ioi_neg_deriv`: `-f'` is integrable on `(0, ∞)` with
  improper integral `f(0) - L`.
* `TauCeti.bernstein_packaging`: absorb the mass at infinity into a Dirac at `0`.
* `TauCeti.bernstein_kernel`, `TauCeti.bernstein_kernel_tendsto`: the rescaled Laplace kernel and
  its pointwise limit `e^{-xp}`.
* `TauCeti.cm_rescaled`, `TauCeti.cm_rescaled_Iio_zero`, `TauCeti.cm_rescaled_mass_eq`: the
  pushed-forward measures, their support, and mass preservation.
* `TauCeti.cm_measure_finite_mass`: finiteness and the total-mass bound `≤ f(0) - L`.

## References

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
private lemma nat_lt_top (n : ℕ) : (n : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)

/-- The first iterated derivative within `[0, ∞)` of a completely monotone function is
nonpositive (the `derivWithin` sign condition restated for `iteratedDerivWithin 1`). -/
private lemma IsCompletelyMonotone.iteratedDerivWithin_one_nonpos
    (hf : IsCompletelyMonotone f) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin 1 f (Ici 0) t ≤ 0 := by
  rw [iteratedDerivWithin_one]; exact hf.derivWithin_nonpos ht

/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for the `n`-th approximating measure in
the Bernstein proof (Chafaï 2013). -/
@[expose] noncomputable def cm_density (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t

/-- The `n`-th approximating measure `σ_n` for the Bernstein proof, with density `ρ_n` on
`(0, ∞)`. -/
@[expose] noncomputable def cm_measure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (cm_density f n t))

/-- The density `ρ_n` is nonnegative for completely monotone functions. -/
lemma cm_density_nonneg (hcm : IsCompletelyMonotone f) (n : ℕ)
    (t : ℝ) (ht : 0 < t) : 0 ≤ cm_density f n t := by
  simp only [cm_density]
  split_ifs with hn
  · exact le_refl 0
  · have hcm_sign := hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le
    have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht.le _) hfact_pos.le) hcm_sign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
lemma cm_density_one (t : ℝ) :
    cm_density f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [cm_density]

/-- The interval integral of `-f'` with the `T`-dependent set `Icc 0 T` equals the integral with
the fixed set `Ici 0` (both agree a.e. by set transfer at interior points). -/
lemma IsCompletelyMonotone.integral_neg_deriv_Ici
    (hcm : IsCompletelyMonotone f) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t =
    ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t := by
  apply intervalIntegral.integral_congr_ae
  apply ae_of_all volume
  intro t ht
  rw [uIoc_of_le hT.le] at ht
  have ht_pos : 0 < t := ht.1
  have hcda : ContDiffAt ℝ (↑1 : WithTop ℕ∞) f t :=
    (hcm.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
  simp only [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hT) hcda
      (Ioc_subset_Icc_self ht),
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
      (mem_Ici.mpr ht_pos.le)]

/-- The total mass `∫₀ᵀ (-f') dt → f(0) - L` as `T → ∞`, where `L = lim f(t)`. This is the key
uniform bound for the tightness argument in Bernstein's theorem. -/
lemma IsCompletelyMonotone.tendsto_total_mass
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Icc 0 T) t) atTop
        (nhds (f 0 - L)) :=
  Tendsto.congr' (EventuallyEq.symm
    ((eventually_gt_atTop 0).mono fun T hT => hcm.integral_mass T hT))
    (Tendsto.sub tendsto_const_nhds hL)

/-- `-f'` is integrable on `(0, ∞)` for completely monotone functions (total mass `f(0) - L`). -/
lemma IsCompletelyMonotone.neg_deriv_integrableOn
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto (f 0 - L) 0
      (l := atTop) (b := id)
  · intro T
    exact ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
      (uniqueDiffOn_Ici 0)).neg.mono Icc_subset_Ici_self).integrableOn_compact
        isCompact_Icc |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  · have hnorm : ∀ᶠ T in atTop, (∫ t in (0 : ℝ)..id T,
        ‖(fun t => -iteratedDerivWithin 1 f (Ici 0) t) t‖) = f 0 - f T := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      simp only [id]
      have : (∫ t in (0 : ℝ)..T, ‖(fun t => -iteratedDerivWithin 1 f (Ici 0) t) t‖) =
          ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
        intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
          rw [uIoc_of_le hT.le] at ht
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonneg (by linarith [hcm.iteratedDerivWithin_one_nonpos ht.1.le])])
      rw [this, ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
    exact Tendsto.congr' (EventuallyEq.symm hnorm) (Tendsto.sub tendsto_const_nhds hL)

/-- The improper integral `∫₀^∞ (-f') dt = f(0) - L` for completely monotone functions. -/
lemma IsCompletelyMonotone.integral_Ioi_neg_deriv
    (hcm : IsCompletelyMonotone f) {L : ℝ} (hL : Tendsto f atTop (nhds L))
    (hint : IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi 0)) :
    ∫ t in Ioi 0, -iteratedDerivWithin 1 f (Ici 0) t = f 0 - L := by
  have htend := intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id
  have htend2 : Tendsto (fun T => ∫ t in (0 : ℝ)..T,
      -iteratedDerivWithin 1 f (Ici 0) t) atTop (nhds (f 0 - L)) :=
    Tendsto.congr'
      ((eventually_gt_atTop 0).mono fun T hT =>
        ((hcm.integral_neg_deriv_Ici T hT).symm.trans (hcm.integral_mass T hT)).symm)
      (Tendsto.sub tendsto_const_nhds hL)
  exact tendsto_nhds_unique htend htend2

/-- **Packaging step**: if `f(x) = L + ∫ e^{-xp} dμ₀` with `μ₀` supported on `[0,∞)`, then
`μ = μ₀ + L·δ₀` gives `f(x) = ∫ e^{-xp} dμ` with `μ` finite and supported on `[0,∞)`. -/
lemma bernstein_packaging {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    {μ₀ : Measure ℝ} [IsFiniteMeasure μ₀] (hsupp₀ : μ₀ (Iio 0) = 0)
    (hrep : ∀ t, 0 ≤ t → f t = L + ∫ p, Real.exp (-(t * p)) ∂μ₀) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ (Iio 0) = 0 ∧
      ∀ t, 0 ≤ t → f t = ∫ p, Real.exp (-(t * p)) ∂μ := by
  set μ := μ₀ + (ENNReal.ofReal L) • Measure.dirac (0 : ℝ)
  haveI : IsFiniteMeasure μ := by
    constructor
    simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
    exact ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.ofReal_lt_top⟩
  refine ⟨μ, inferInstance, ?_, ?_⟩
  · simp only [μ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply, Set.indicator, Set.mem_Iio, lt_irrefl,
      ↓reduceIte, mul_zero, hsupp₀, add_zero]
  · intro t ht
    rw [hrep t ht]
    set ν := (ENNReal.ofReal L) • Measure.dirac (0 : ℝ)
    have exp_int : ∀ (μ' : Measure ℝ) [IsFiniteMeasure μ'],
        μ' (Iio 0) = 0 → Integrable (fun p => Real.exp (-(t * p))) μ' := by
      intro μ' _ hsupp'
      apply Integrable.mono' (integrable_const (1 : ℝ))
      · fun_prop
      · rw [ae_iff]; refine measure_mono_null (fun p hp => ?_) hsupp'
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at hp
        rw [Set.mem_Iio]; by_contra hge; rw [not_lt] at hge
        linarith [abs_of_nonneg (Real.exp_pos (-(t * p))).le,
          Real.exp_le_exp_of_le (neg_nonpos.mpr (mul_nonneg ht hge)), Real.exp_zero]
    have h1 : Integrable (fun p => Real.exp (-(t * p))) μ₀ := exp_int μ₀ hsupp₀
    have h2 : Integrable (fun p => Real.exp (-(t * p))) ν := by
      haveI : IsFiniteMeasure ν := by
        constructor; simp only [ν, Measure.smul_apply, smul_eq_mul,
          Measure.dirac_apply, Set.indicator_univ, Pi.one_apply, mul_one]
        exact ENNReal.ofReal_lt_top
      apply exp_int; simp [ν, Measure.smul_apply, Set.indicator, Set.mem_Iio]
    change L + ∫ p, Real.exp (-(t * p)) ∂μ₀ = ∫ p, Real.exp (-(t * p)) ∂(μ₀ + ν)
    rw [integral_add_measure h1 h2]
    suffices h : ∫ p, Real.exp (-(t * p)) ∂ν = L by linarith
    rw [@integral_smul_measure ℝ ℝ _ _ _ (Measure.dirac 0)
      (fun p => Real.exp (-(t * p))) (ENNReal.ofReal L),
      integral_dirac, ENNReal.toReal_ofReal hL,
      mul_zero, neg_zero, Real.exp_zero, smul_eq_mul, mul_one]

/-! ## Rescaled measures and Prokhorov extraction -/

/-- The Bernstein kernel `φ_n(x,p) = max(1 - xp/(n-1), 0)ⁿ⁻¹` for `n ≥ 2`. After the change of
variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]` becomes `φ_n(x, p)`, which
converges pointwise to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)ⁿ → e^{-x}` limit). -/
@[expose] noncomputable def bernstein_kernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0 else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- **Pointwise convergence of the Bernstein kernel** to the Laplace kernel:
`φ_n(x,p) → e^{-xp}` as `n → ∞`, for `x, p ≥ 0`. -/
lemma bernstein_kernel_tendsto (x p : ℝ) (_hx : 0 ≤ x) (_hp : 0 ≤ p) :
    Tendsto (fun n : ℕ => bernstein_kernel n x p) atTop (nhds (Real.exp (-(x * p)))) := by
  set g := fun n : ℕ => (1 + (-(x * p)) / (↑n : ℝ)) ^ n with hg_def
  have hg_tendsto : Tendsto g atTop (nhds (Real.exp (-(x * p)))) :=
    Real.tendsto_one_add_div_pow_exp (-(x * p))
  have hshift : Tendsto (fun n : ℕ => g (n - 1)) atTop (nhds (Real.exp (-(x * p)))) :=
    hg_tendsto.comp (tendsto_atTop_atTop.mpr (fun b => ⟨b + 1, fun n hn => by omega⟩))
  apply Tendsto.congr' _ hshift
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{n : ℕ | n ≥ Nat.ceil (x * p) + 2}, mem_atTop _, ?_⟩
  intro n hn
  simp only [Set.mem_setOf_eq] at hn
  simp only [bernstein_kernel, hg_def]
  have hn1 : ¬(n ≤ 1) := by omega
  simp only [hn1, ite_false]
  have hn1_pos : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr (by omega)
  have hn1_ge : x * p ≤ ↑(n - 1) := by
    calc x * p ≤ ↑(Nat.ceil (x * p)) := Nat.le_ceil _
    _ ≤ ↑(n - 1) := by exact_mod_cast (by omega : Nat.ceil (x * p) ≤ n - 1)
  congr 1
  rw [max_eq_left]
  · ring
  · rw [sub_nonneg]; exact div_le_one_of_le₀ hn1_ge hn1_pos.le

/-- The rescaled measure `σ̃_n`: pushforward of `cm_measure f n` under `t ↦ (n-1)/t`. -/
@[expose] noncomputable def cm_rescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  Measure.map (fun t => ((n : ℝ) - 1) / t) (cm_measure f n)

/-- The rescaling map `t ↦ (n-1)/t` is measurable. -/
lemma cm_rescaling_measurable (n : ℕ) :
    Measurable (fun t : ℝ => ((n : ℝ) - 1) / t) :=
  measurable_const.div measurable_id

/-- `cm_measure f n` lives on `(0, ∞)`: its complement has zero mass. -/
lemma cm_measure_compl_Ioi (f : ℝ → ℝ) (n : ℕ) :
    (cm_measure f n) (Ioi 0)ᶜ = 0 := by
  unfold cm_measure
  rw [withDensity_apply _ (measurableSet_Ioi.compl)]
  apply setLIntegral_measure_zero
  rw [Measure.restrict_apply (measurableSet_Ioi.compl)]
  have : (Ioi (0 : ℝ))ᶜ ∩ Ioi 0 = ∅ := by ext x; simp [Set.mem_Ioi]
  rw [this, measure_empty]

/-- The rescaled measure `σ̃_n` is supported on `[0, ∞)` for `n ≥ 2`. -/
lemma cm_rescaled_Iio_zero (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (cm_rescaled f n) (Iio 0) = 0 := by
  unfold cm_rescaled
  rw [Measure.map_apply (cm_rescaling_measurable n) measurableSet_Iio]
  have h_sub : (fun t : ℝ => ((n : ℝ) - 1) / t) ⁻¹' Iio 0 ⊆ (Ioi 0)ᶜ := by
    intro t ht
    simp only [Set.mem_preimage, Set.mem_Iio] at ht
    simp only [Set.mem_compl_iff, Set.mem_Ioi, not_lt]
    by_contra h; rw [not_le] at h
    have : (0 : ℝ) < (↑n : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
      linarith
    linarith [div_pos this h]
  exact nonpos_iff_eq_zero.mp
    (le_trans (measure_mono h_sub) (le_of_eq (cm_measure_compl_Ioi f n)))

/-- Pushforward preserves total mass. -/
lemma cm_rescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (cm_rescaled f n) univ = (cm_measure f n) univ := by
  unfold cm_rescaled
  rw [Measure.map_apply (cm_rescaling_measurable n) MeasurableSet.univ, Set.preimage_univ]

/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`. -/
private lemma cm_density_ibp_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, cm_density f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, cm_density f (m + 1) t := by
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set g' := iteratedDerivWithin (m + 2) f (Ici 0)
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hg_cont : ContinuousOn g (Ici 0) :=
    hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0)
  have hg_deriv : ∀ t, 0 < t → HasDerivAt g (g' t) t := by
    intro t ht
    have hmem : Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds ht
    have hda := (hcm.contDiffOn.differentiableOn_iteratedDerivWithin
      (nat_lt_top (m + 1)) (uniqueDiffOn_Ici 0)).hasDerivAt hmem
    have hval : g' t = deriv g t := by
      simp only [g, g']
      rw [show m + 2 = (m + 1) + 1 from rfl, iteratedDerivWithin_succ,
        derivWithin_of_mem_nhds hmem]
    rw [hval]; exact hda
  have huIcc : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul
      (continuousOn_const.mul (hg_cont.mono Icc_subset_Ici_self))
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) t :=
    fun t ht => (hasDerivAt_pow (m + 1) t).mul ((hg_deriv t ht.1).const_mul c)
  have hcm_int : ∀ k, k ≠ 0 → IntervalIntegrable (fun t => cm_density f k t) volume 0 T := by
    intro k hk; apply ContinuousOn.intervalIntegrable; rw [huIcc]
    apply ContinuousOn.mono _ Icc_subset_Ici_self
    change ContinuousOn (fun t => cm_density f k t) (Ici 0)
    have : (fun t => cm_density f k t) = fun t =>
        (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t := funext fun t => by simp [cm_density, hk]
    rw [this]
    exact (continuousOn_const.mul (continuous_pow _).continuousOn).mul
      (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0))
  have hF'_eq : ∀ t, ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t) =
      cm_density f (m + 2) t - cm_density f (m + 1) t := by
    intro t
    simp only [cm_density, show m + 2 ≠ 0 from by omega, show m + 1 ≠ 0 from by omega,
      ite_false, show m + 2 - 1 = m + 1 from by omega,
      show m + 1 - 1 = m from by omega, g, g', c]
    have : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [this]
    have : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have : ((m : ℝ) + 1) ≠ 0 := by positivity
    have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
    rw [this]; field_simp; ring
  have hF'_int : IntervalIntegrable
      (fun t => ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) volume 0 T :=
    ((hcm_int _ (by omega)).sub (hcm_int _ (by omega))).congr fun t _ => (hF'_eq t).symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv hF'_int
  have hstep1 : ∫ t in (0 : ℝ)..T,
      (cm_density f (m + 2) t - cm_density f (m + 1) t) = F T - F 0 := by
    rw [← hftc]
    exact intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t _ => (hF'_eq t).symm)
  have hF0 : F 0 = 0 := by simp [F, zero_pow (show m + 1 ≠ 0 from by omega)]
  rw [hF0, sub_zero] at hstep1
  rw [intervalIntegral.integral_sub (hcm_int _ (by omega)) (hcm_int _ (by omega))] at hstep1
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- **IBP step**: integrating from density `k` to density `k-1`. -/
lemma cm_density_ibp_step (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 2 ≤ k) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, cm_density f k t ≤ ∫ t in (0 : ℝ)..T, cm_density f (k - 1) t := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 from by omega]
  have hibp := cm_density_ibp_identity f hcm m T hT
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Ici 0) T
  have hB : B ≤ 0 := by
    have h_neg : (-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg (m + 1) hT.le]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg hT.le _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- **Total mass bound**: `cm_measure f n` is finite with total mass `≤ f(0) - L`. -/
lemma cm_measure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (cm_measure f n) ∧
    (cm_measure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  have hn0 : n ≠ 0 := by omega
  have hcont : ContinuousOn (cm_density f n) (Ici 0) := by
    unfold cm_density; simp only [hn0, ↓reduceIte]
    exact ((continuousOn_const.mul
      ((continuousOn_pow _).mono fun _ _ => trivial)).mul
      (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0)))
  have hbound : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, cm_density f n t ≤ f 0 - L := by
    have base : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, cm_density f 1 t = f 0 - f T := by
      intro T hT
      have h1 : ∫ t in (0 : ℝ)..T, cm_density f 1 t =
          ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
        intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall fun t _ => cm_density_one t)
      rw [h1, ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
    have density_le : ∀ j, 1 ≤ j → ∀ T, 0 < T →
        ∫ t in (0 : ℝ)..T, cm_density f j t ≤ f 0 - f T := by
      intro j hj
      induction j with
      | zero => omega
      | succ p ih =>
        intro T hT
        by_cases hp : p = 0
        · subst hp; exact le_of_eq (base T hT)
        · calc ∫ t in (0 : ℝ)..T, cm_density f (p + 1) t
              ≤ ∫ t in (0 : ℝ)..T, cm_density f p t := by
                simpa using cm_density_ibp_step f hcm (p + 1) (by omega) T hT
            _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp) T hT
    intro T hT
    have hfT : L ≤ f T := by
      set g₀ := fun t : ℝ => f (max t 0) with hg₀
      have hg_anti : Antitone g₀ := fun a b hab =>
        hcm.antitoneOn (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
          (max_le_max_right 0 hab)
      have := hg_anti.le_of_tendsto
        (hL.congr' (eventually_atTop.mpr ⟨0, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
      simpa [hg₀, max_eq_left hT.le] using this
    linarith [density_le n (by omega : 1 ≤ n) T hT]
  have hint : IntegrableOn (cm_density f n) (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
      (l := atTop) (b := id)
    · intro T
      exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
        |>.mono_set Ioc_subset_Icc_self
    · exact tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with T hT; simp only [id]
      calc ∫ t in (0 : ℝ)..T, ‖cm_density f n t‖
          = ∫ t in (0 : ℝ)..T, cm_density f n t := by
            apply intervalIntegral.integral_congr_ae; apply ae_of_all
            intro t ht; rw [uIoc_of_le hT.le] at ht
            rw [Real.norm_eq_abs, abs_of_nonneg (cm_density_nonneg hcm n t ht.1)]
        _ ≤ f 0 - L := hbound T hT
  have hfin : IsFiniteMeasure (cm_measure f n) := by
    unfold cm_measure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (cm_measure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
    change (volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal (cm_density f n t)) univ ≤ _
    rw [withDensity_apply _ MeasurableSet.univ]; simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
        cm_density_nonneg hcm n t ht)]
    exact ENNReal.ofReal_le_ofReal
      (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
        (eventually_atTop.mpr ⟨1, fun T hT => hbound T (by linarith)⟩))
  exact ⟨hfin, hmass⟩

end TauCeti

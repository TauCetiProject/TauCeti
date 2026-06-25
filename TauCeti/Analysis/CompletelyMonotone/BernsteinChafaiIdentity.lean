/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Analysis.CompletelyMonotone.BernsteinMeasures

/-!
# The Chafaï identity for Bernstein's theorem

For a completely monotone `f` with `f(t) → L`, the Chafaï identity expresses the finite-`n`
approximation exactly:
`f(x) - L = ∫ φ_n(x, p) d(chafaiRescaled f n)(p)`,
where `φ_n` is `bernstein_kernel`. It comes from the repeated integration by parts of the Taylor
kernel (`chafai_repeated_ibp`), whose boundary terms `Tᵏ f⁽ᵏ⁾(T)` decay to `0`
(`boundary_term_decay`), combined with the change of variables `p = (n-1)/t`
(`chafai_kernel_density_eq`).

## Main declarations

* `TauCeti.chafai_identity`: `f(x) - L = ∫ φ_n(x, ·) d(chafaiRescaled f n)`.
* `TauCeti.chafai_repeated_ibp`: `∫_{(x,∞)} (Taylor kernel) = f(x) - L`.
* `TauCeti.boundary_term_decay`, `TauCeti.ibp_kernel_integrableOn`, supporting analytic facts.

## References

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
private lemma nat_lt_top (n : ℕ) : (n : WithTop ℕ∞) < ∞ :=
  WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top n)

/-- `f(T) ≥ L` for `T > 0`: a completely monotone function is antitone and tends to `L`. -/
private lemma IsCompletelyMonotone.le_of_tendsto_atTop (hcm : IsCompletelyMonotone f) {L : ℝ}
    (hL : Tendsto f atTop (nhds L)) {T : ℝ} (hT : 0 < T) : L ≤ f T := by
  set g₀ := fun t : ℝ => f (max t 0) with hg₀
  have hg_anti : Antitone g₀ := fun a b hab =>
    hcm.antitoneOn (mem_Ici.mpr (le_max_right _ _)) (mem_Ici.mpr (le_max_right _ _))
      (max_le_max_right 0 hab)
  have := hg_anti.le_of_tendsto
    (hL.congr' (eventually_atTop.mpr ⟨0, fun t ht => by simp [hg₀, max_eq_left ht]⟩)) T
  simpa [hg₀, max_eq_left hT.le] using this

/-! ### Chafaï identity -/

/-- The rescaled measure `chafaiRescaled f n` is finite when `chafaiMeasure f n` is. -/
lemma chafaiRescaled_isFiniteMeasure (f : ℝ → ℝ) (n : ℕ)
    [IsFiniteMeasure (chafaiMeasure f n)] : IsFiniteMeasure (chafaiRescaled f n) where
  measure_univ_lt_top := by
    rw [chafaiRescaled_eq_map]
    rw [Measure.map_apply (chafaiRescaling_measurable n) MeasurableSet.univ, Set.preimage_univ]
    exact IsFiniteMeasure.measure_univ_lt_top

/-- The change of variables `p = (n-1)/t` turning the rescaled Bernstein kernel against the
density into the shifted Taylor kernel on `(x, ∞)`. -/
private lemma chafai_kernel_density_eq (f : ℝ → ℝ) (_hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x) :
    ∫ t in Ioi 0, bernstein_kernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t =
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial *
      (t - x) ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : ¬(n ≤ 1) := by omega
  have hne : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsubset : Ioi x ⊆ Ioi 0 := Ioi_subset_Ioi hx
  have hvanish : ∀ t ∈ Ioi 0 \ Ioi x,
      bernstein_kernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t = 0 := by
    intro t ht
    simp only [Set.mem_sdiff, Set.mem_Ioi, not_lt] at ht
    rw [bernstein_kernel_of_two_le hn]
    have hcast : (↑(n - 1) : ℝ) = ↑n - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
    have : x * (((n : ℝ) - 1) / t) / ↑(n - 1) = x / t := by
      rw [hcast]; field_simp [hne, ne_of_gt ht.1]
    rw [this, max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht.1]; linarith)]
    rw [zero_pow (by omega : n - 1 ≠ 0), zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset hvanish]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht; simp only [Set.mem_Ioi] at ht
  have ht_pos : 0 < t := lt_of_le_of_lt hx ht
  have hcast : (↑(n - 1) : ℝ) = ↑n - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  change bernstein_kernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t =
    (-1 : ℝ) ^ n / ↑(n - 1).factorial * (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Ici 0) t
  rw [bernstein_kernel_of_two_le hn]
  have hrw : x * (((n : ℝ) - 1) / t) / ↑(n - 1) = x / t := by
    rw [hcast]; field_simp [hne, ne_of_gt ht_pos]
  rw [hrw, max_eq_left (by rw [sub_nonneg, div_le_one₀ ht_pos]; linarith)]
  rw [chafaiDensity_of_ne_zero hn0]
  have key : (1 - x / t) ^ (n - 1) * t ^ (n - 1) = (t - x) ^ (n - 1) := by
    rw [← mul_pow]; congr 1; field_simp [ne_of_gt ht_pos]
  calc (1 - x / t) ^ (n - 1) * ((-1 : ℝ) ^ n / ↑(n - 1).factorial *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t)
      = (-1 : ℝ) ^ n / ↑(n - 1).factorial *
        ((1 - x / t) ^ (n - 1) * t ^ (n - 1)) * iteratedDerivWithin n f (Ici 0) t := by ring
    _ = _ := by rw [key]

/-- IBP on `[x, T]`: integrating the `(k+1)`-th order Taylor kernel by parts gives a boundary
term plus the `k`-th order kernel (with a sign flip). -/
private lemma ibp_finite_interval (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x T : ℝ) (hx : 0 ≤ x) (hxT : x < T) :
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
      iteratedDerivWithin (k + 1) f (Ici 0) t =
    (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k * iteratedDerivWithin k f (Ici 0) T -
    ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t := by
  set c := (-1 : ℝ) ^ (k + 1) / ↑k.factorial
  set g := iteratedDerivWithin k f (Ici 0)
  set g' := iteratedDerivWithin (k + 1) f (Ici 0)
  set u := fun t : ℝ => c * (t - x) ^ k
  set u' := fun t : ℝ => c * (↑k * (t - x) ^ (k - 1))
  have hu'_eq : ∀ t, u' t = (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) := by
    intro t; simp only [u', c]
    have : k.factorial = k * (k - 1).factorial := by
      cases k with | zero => contradiction | succ n => simp [Nat.factorial_succ]
    rw [this]; push_cast; field_simp
  have hu_cont : ContinuousOn u (uIcc x T) :=
    continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)
  have hg_cont : ContinuousOn g (uIcc x T) := by
    rw [uIcc_of_le hxT.le]
    exact (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
      (uniqueDiffOn_Ici 0)).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))
  have hu_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt u (u' t) (Ioi t) t := by
    intro t _; apply HasDerivAt.hasDerivWithinAt
    change HasDerivAt (fun t => c * (t - x) ^ k) (c * (↑k * (t - x) ^ (k - 1))) t
    simpa using ((hasDerivAt_pow k (t - x)).comp t
      ((hasDerivAt_id t).sub_const x)).const_mul c
  have hg_deriv : ∀ t ∈ Ioo (min x T) (max x T),
      HasDerivWithinAt g (g' t) (Ioi t) t := by
    intro t ht
    rw [min_eq_left hxT.le, max_eq_right hxT.le] at ht
    have hmem : Ici (0 : ℝ) ∈ nhds t := Ici_mem_nhds (by linarith [ht.1])
    apply HasDerivAt.hasDerivWithinAt
    have hval : g' t = deriv g t := by
      simp only [g', g, iteratedDerivWithin_succ, derivWithin_of_mem_nhds hmem]
    rw [hval]
    exact (hcm.contDiffOn.differentiableOn_iteratedDerivWithin (nat_lt_top _)
      (uniqueDiffOn_Ici 0)).hasDerivAt hmem
  have hu'_int : IntervalIntegrable u' volume x T :=
    (continuousOn_const.mul (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).pow _))).intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume x T := by
    apply ContinuousOn.intervalIntegrable; rw [uIcc_of_le hxT.le]
    exact (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
      (uniqueDiffOn_Ici 0)).mono (Icc_subset_Ici_self.trans (Ici_subset_Ici.mpr hx))
  have hibp := integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hu_cont hg_cont hu_deriv hg_deriv hu'_int hg'_int
  have hu0 : u x = 0 := by simp [u, sub_self, zero_pow hk]
  rw [hu0, zero_mul, sub_zero] at hibp
  have h1 : ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
        iteratedDerivWithin (k + 1) f (Ici 0) t = ∫ t in x..T, u t * g' t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by ring)
  have h2 : ∫ t in x..T, u' t * g t =
      ∫ t in x..T, (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t :=
    intervalIntegral.integral_congr_ae (ae_of_all _ fun t _ => by rw [hu'_eq])
  linarith

/-- Tail set integral of an integrable function on `(a, ∞)` tends to 0. -/
private lemma tail_setIntegral_tendsto_zero {g : ℝ → ℝ} {a : ℝ}
    (hg : IntegrableOn g (Ioi a)) :
    Tendsto (fun T => ∫ t in Ioi T, g t) atTop (nhds 0) := by
  set I := ∫ t in Ioi a, g t
  have h_total : Tendsto (fun T => ∫ t in a..T, g t) atTop (nhds I) :=
    (intervalIntegral_tendsto_integral_Ioi a hg tendsto_id).congr fun _ => by simp [id]
  have hsub : Tendsto (fun T => I - ∫ t in a..T, g t) atTop (nhds 0) := by
    convert tendsto_const_nhds.sub h_total using 1; simp
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop a] with T hT
  symm
  have hdisj : Disjoint (Ioc a T) (Ioi T) := by
    rw [disjoint_left]; intro y hy1 hy2; simp at hy1 hy2; linarith
  have hunion : Ioc a T ∪ Ioi T = Ioi a := by
    ext y; simp only [mem_union, mem_Ioc, mem_Ioi]; constructor
    · rintro (⟨hy, _⟩ | hy) <;> linarith
    · intro hy; by_cases hyT : y ≤ T
      · left; exact ⟨hy, hyT⟩
      · right; linarith
  have hd := setIntegral_union hdisj measurableSet_Ioi
    (hg.mono_set Ioc_subset_Ioi_self) (hg.mono_set (Ioi_subset_Ioi hT.le))
  rw [hunion] at hd; rw [intervalIntegral.integral_of_le hT.le]; linarith

/-- Boundary decay: `(-1)^{k+1}/k! (T-x)ᵏ Dᵏf(T) → 0` as `T → ∞` for completely monotone `f`. -/
private lemma boundary_term_decay (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : k ≠ 0) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    Tendsto (fun T => (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T) atTop (nhds 0) := by
  set h := fun T => (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) T
  have hkey : Tendsto (fun T => (T - x) ^ k * h T) atTop (nhds 0) := by
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    have h_nonneg : ∀ T, 0 ≤ T → 0 ≤ h T := fun T hT => by
      simpa [h] using hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k hT
    have h_antitone : AntitoneOn h (Ici 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      · simpa [h] using
          (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _)
            (uniqueDiffOn_Ici 0)).const_mul ((-1 : ℝ) ^ k)
      · rw [interior_Ici]
        intro T hT
        have hdiff : DifferentiableAt ℝ (iteratedDerivWithin k f (Ici 0)) T :=
          (hcm.contDiffOn.differentiableOn_iteratedDerivWithin (nat_lt_top _)
            (uniqueDiffOn_Ici 0)) T (mem_Ici.mpr hT.le) |>.differentiableAt (Ici_mem_nhds hT)
        exact (hdiff.const_mul ((-1 : ℝ) ^ k)).differentiableWithinAt
      · rw [interior_Ici]
        intro T hT
        have hderiv : deriv h T = (-1 : ℝ) ^ k * iteratedDerivWithin (k + 1) f (Ici 0) T := by
          simp only [h]
          rw [deriv_const_mul_field, ← derivWithin_of_mem_nhds (Ici_mem_nhds hT),
            ← iteratedDerivWithin_succ]
        rw [hderiv]
        have hsign : 0 ≤ (-1 : ℝ) ^ (k + 1) * iteratedDerivWithin (k + 1) f (Ici 0) T :=
          hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg (k + 1) hT.le
        have : 0 ≤ -(((-1 : ℝ) ^ k) * iteratedDerivWithin (k + 1) f (Ici 0) T) := by
          simpa [pow_succ, mul_assoc] using hsign
        linarith
    have hcont_density : ContinuousOn (chafaiDensity f k) (Ici 0) :=
      continuousOn_chafaiDensity hcm k
    have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) := by
      by_cases hk_eq : k = 1
      · subst hk_eq
        convert hcm.neg_deriv_integrableOn using 1
        ext t; rw [chafaiDensity_one]
      · have hk2 : 2 ≤ k := by omega
        have hmeas_density : AEStronglyMeasurable (chafaiDensity f k)
            (volume.restrict (Ioi 0)) :=
          (hcont_density.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
        have hnonneg_density : 0 ≤ᵐ[volume.restrict (Ioi 0)] chafaiDensity f k :=
          (ae_restrict_mem measurableSet_Ioi).mono fun t ht => chafaiDensity_nonneg hcm k t ht.le
        refine ⟨hmeas_density, ?_⟩
        rw [hasFiniteIntegral_iff_ofReal hnonneg_density]
        obtain ⟨_, hmass⟩ := chafaiMeasure_finite_mass_of_tendsto f hcm k (by omega) L hL
        have hmass' := hmass
        rw [chafaiMeasure_eq_withDensity] at hmass'
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass'
        exact lt_of_le_of_lt hmass' ENNReal.ofReal_lt_top
    have htail : Tendsto (fun S : ℝ => ∫ t in Ioi S, chafaiDensity f k t) atTop (nhds 0) :=
      tail_setIntegral_tendsto_zero hint_density
    have htail_half :
        Tendsto (fun T : ℝ => ∫ t in Ioi (T / 2), chafaiDensity f k t) atTop (nhds 0) := by
      have hhalf_map : Tendsto (fun T : ℝ => (1 / 2 : ℝ) * T) atTop atTop :=
        (Filter.tendsto_const_mul_atTop_of_pos (show (0 : ℝ) < 1 / 2 by positivity)).2 tendsto_id
      simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using htail.comp hhalf_map
    have hupper : ∀ᶠ T in atTop, (T - x) ^ k * h T ≤
        ((2 : ℝ) ^ k * ↑((k - 1).factorial)) * ∫ t in Ioi (T / 2), chafaiDensity f k t := by
      filter_upwards [eventually_gt_atTop (max (2 * x) 2)] with T hT
      have hT2 : (2 : ℝ) < T := lt_of_le_of_lt (le_max_right (2 * x) 2) hT
      have hTpos : 0 < T := by linarith
      have hxT : x < T := by
        have h2xT : 2 * x < T := lt_of_le_of_lt (le_max_left (2 * x) 2) hT
        linarith
      have hTx_nonneg : 0 ≤ T - x := sub_nonneg.mpr hxT.le
      have hT_nonneg : 0 ≤ T := hTpos.le
      have hhalf_nonneg : 0 ≤ T / 2 := by positivity
      have hhT_nonneg : 0 ≤ h T := h_nonneg T hT_nonneg
      have h_interval_le :
          ∫ t in T / 2..T, chafaiDensity f k t ≤ ∫ t in Ioi (T / 2), chafaiDensity f k t := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        apply setIntegral_mono_set (hint_density.mono_set (Ioi_subset_Ioi hhalf_nonneg))
        · exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
            chafaiDensity_nonneg hcm k t (lt_of_le_of_lt hhalf_nonneg ht).le
        · exact ae_of_all _ fun t ht => Ioc_subset_Ioi_self ht
      have h_density_eq : ∀ t, chafaiDensity f k t =
          (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t := by
        intro t; rw [chafaiDensity_of_ne_zero hk]; simp only [h]; field_simp
      have h_const_le : (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T ≤
          ∫ t in T / 2..T, chafaiDensity f k t := by
        have hmono : ∀ᵐ t ∂(volume.restrict (Icc (T / 2) T)),
            (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤ chafaiDensity f k t := by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          have ht_nonneg : 0 ≤ t := le_trans hhalf_nonneg ht.1
          have hpow : (T / 2) ^ (k - 1) ≤ t ^ (k - 1) := pow_le_pow_left₀ hhalf_nonneg ht.1 _
          have hh_le : h T ≤ h t := h_antitone ht_nonneg hT_nonneg ht.2
          have hmul : (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T ≤
              (1 / ↑((k - 1).factorial)) * t ^ (k - 1) * h t := by
            have hcoeff_nonneg : 0 ≤ (1 / ↑((k - 1).factorial) : ℝ) := by positivity
            have hright_nonneg : 0 ≤ (1 / ↑((k - 1).factorial)) * t ^ (k - 1) :=
              mul_nonneg hcoeff_nonneg (pow_nonneg ht_nonneg _)
            calc (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T
                  ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h T := by
                    simpa [mul_assoc] using mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hpow hcoeff_nonneg) hhT_nonneg
              _ ≤ ((1 / ↑((k - 1).factorial)) * t ^ (k - 1)) * h t :=
                    mul_le_mul_of_nonneg_left hh_le hright_nonneg
          simpa [h_density_eq t] using hmul
        have hconst_int : IntervalIntegrable (fun _ : ℝ =>
            (1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) volume (T / 2) T :=
          intervalIntegrable_const
        have hIcc_subset : Icc (T / 2) T ⊆ Ici 0 := fun t ht => le_trans hhalf_nonneg ht.1
        have hdens_int : IntervalIntegrable (chafaiDensity f k) volume (T / 2) T :=
          (hcont_density.mono hIcc_subset).intervalIntegrable_of_Icc (by linarith)
        have hmono_int := intervalIntegral.integral_mono_ae_restrict (μ := volume)
          (a := T / 2) (b := T) (hab := by linarith) hconst_int hdens_int hmono
        rw [intervalIntegral.integral_const] at hmono_int
        have hhalf_eq : (T - T / 2) = T / 2 := by ring
        rw [hhalf_eq, smul_eq_mul] at hmono_int
        have hconst_eq : T / 2 * ((1 / ↑((k - 1).factorial)) * (T / 2) ^ (k - 1) * h T) =
            (1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T := by
          have hk_succ : k = (k - 1) + 1 := by omega
          rw [hk_succ]; ring_nf
          have hnat : 1 + (k - 1) - 1 = k - 1 := by omega
          simp [hnat]
        rw [hconst_eq] at hmono_int
        exact hmono_int
      have hhalf_le : (T / 2) ^ k * h T ≤
          ↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t := by
        have hfact_pos : (0 : ℝ) < ↑((k - 1).factorial) := Nat.cast_pos.mpr (Nat.factorial_pos _)
        have haux := le_trans h_const_le h_interval_le
        have hmul := mul_le_mul_of_nonneg_left haux hfact_pos.le
        have hleft_eq : ↑((k - 1).factorial) *
            ((1 / ↑((k - 1).factorial)) * (T / 2) ^ k * h T) = (T / 2) ^ k * h T := by
          field_simp [hfact_pos.ne']
        rw [hleft_eq] at hmul; exact hmul
      have hTk_eq : T ^ k * h T = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := by
        calc T ^ k * h T = ((2 : ℝ) * (T / 2)) ^ k * h T := by congr 1; field_simp
          _ = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := by rw [mul_pow]; ring
      calc (T - x) ^ k * h T ≤ T ^ k * h T := by gcongr; linarith
        _ = (2 : ℝ) ^ k * ((T / 2) ^ k * h T) := hTk_eq
        _ ≤ (2 : ℝ) ^ k * (↑((k - 1).factorial) * ∫ t in Ioi (T / 2), chafaiDensity f k t) := by
            gcongr
        _ = ((2 : ℝ) ^ k * ↑((k - 1).factorial)) *
              ∫ t in Ioi (T / 2), chafaiDensity f k t := by ring
    have hnonneg_event : ∀ᶠ T in atTop, 0 ≤ (T - x) ^ k * h T := by
      filter_upwards [eventually_gt_atTop (max x 0)] with T hT
      have hT0 : 0 < T := lt_of_le_of_lt (le_max_right x 0) hT
      have hxT : x < T := lt_of_le_of_lt (le_max_left x 0) hT
      exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hxT.le) _) (h_nonneg T hT0.le)
    have hupper_tendsto : Tendsto (fun T : ℝ =>
        ((2 : ℝ) ^ k * ↑((k - 1).factorial)) *
          ∫ t in Ioi (T / 2), chafaiDensity f k t) atTop (nhds 0) := by
      simpa [mul_zero] using htail_half.const_mul (((2 : ℝ) ^ k) * ↑((k - 1).factorial))
    exact squeeze_zero' hnonneg_event hupper hupper_tendsto
  have heq : ∀ T, (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
      iteratedDerivWithin k f (Ici 0) T = -(1 / ↑k.factorial) * ((T - x) ^ k * h T) := by
    intro T; simp only [h, pow_succ]; ring
  simp_rw [heq]
  rw [show (0 : ℝ) = -(1 / ↑k.factorial) * 0 from by ring]
  exact hkey.const_mul _

/-- Integrability of the `k`-th Taylor kernel on `(x, ∞)`, by domination by `chafaiDensity f k`. -/
private lemma ibp_kernel_integrableOn (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (fun t => (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
      iteratedDerivWithin k f (Ici 0) t) (Ioi x) := by
  have hk0 : k ≠ 0 := by omega
  have hcont_density : ContinuousOn (chafaiDensity f k) (Ici 0) :=
    continuousOn_chafaiDensity hcm k
  have density_le : ∀ j, 1 ≤ j → ∀ T, 0 < T →
      ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
    intro j hj; induction j with
    | zero => omega
    | succ p ih =>
      intro T hT; by_cases hp : p = 0
      · subst hp
        rw [intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t),
          ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
      · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
            ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
              simpa using integral_chafaiDensity_le_pred f hcm (p + 1) (by omega) T hT
          _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp) T hT
  have hint_density : IntegrableOn (chafaiDensity f k) (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0 (l := atTop) (b := id)
    · intro T
      exact (hcont_density.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
        |>.mono_set Ioc_subset_Icc_self
    · exact tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with T hT; simp only [id]
      calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f k t‖
          = ∫ t in (0 : ℝ)..T, chafaiDensity f k t := by
            apply intervalIntegral.integral_congr_ae; apply ae_of_all
            intro t ht; rw [uIoc_of_le hT.le] at ht
            rw [Real.norm_eq_abs, abs_of_nonneg (chafaiDensity_nonneg hcm k t ht.1.le)]
        _ ≤ f 0 - L := by linarith [density_le k hk T hT, hcm.le_of_tendsto_atTop hL hT]
  apply Integrable.mono' (hint_density.mono_set (Ioi_subset_Ioi hx))
  · apply (ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi)
    exact ((continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).pow _)).mul
      ((hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0)).mono
        (fun t ht => mem_Ici.mpr (lt_of_le_of_lt hx ht).le)))
  · rw [ae_restrict_iff' measurableSet_Ioi]; apply ae_of_all; intro t ht
    simp only [Ioi, mem_setOf_eq] at ht
    have ht0 : 0 < t := lt_of_le_of_lt hx ht
    have htx : 0 ≤ t - x := by linarith
    have htx_le : t - x ≤ t := by linarith
    rw [chafaiDensity_of_ne_zero hk0]
    have hcm_sign : 0 ≤ (-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t :=
      hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg k ht0.le
    have hfact : (0 : ℝ) < ↑(k - 1).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hval_nn : 0 ≤ (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
        iteratedDerivWithin k f (Ici 0) t := by
      calc (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
            iteratedDerivWithin k f (Ici 0) t
          = (t - x) ^ (k - 1) / ↑(k - 1).factorial *
            ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
        _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg htx _) hfact.le) hcm_sign
    rw [Real.norm_eq_abs, abs_of_nonneg hval_nn]
    calc (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t
        = (1 / ↑(k - 1).factorial) * (t - x) ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) := by field_simp
      _ ≤ (1 / ↑(k - 1).factorial) * t ^ (k - 1) *
          ((-1 : ℝ) ^ k * iteratedDerivWithin k f (Ici 0) t) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htx htx_le _) (by positivity)) hcm_sign
      _ = (-1 : ℝ) ^ k / ↑(k - 1).factorial * t ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t := by field_simp

/-- Repeated integration by parts of the Taylor kernel down to order 1, giving `f(x) - L`. -/
private lemma chafai_repeated_ibp (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    ∫ t in Ioi x, (-1 : ℝ) ^ n / ↑(n - 1).factorial * (t - x) ^ (n - 1) *
      iteratedDerivWithin n f (Ici 0) t = f x - L := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      have hsimpl : (fun t => (-1 : ℝ) ^ (0 + 1) / ↑(0 + 1 - 1).factorial *
            (t - x) ^ (0 + 1 - 1) * iteratedDerivWithin (0 + 1) f (Ici 0) t) =
          (fun t => -iteratedDerivWithin 1 f (Ici 0) t) := by ext t; simp
      rw [hsimpl]
      have hintx : IntegrableOn (fun t => -iteratedDerivWithin 1 f (Ici 0) t) (Ioi x) :=
        (hcm.neg_deriv_integrableOn).mono_set (Ioi_subset_Ioi hx)
      refine tendsto_nhds_unique
        (intervalIntegral_tendsto_integral_Ioi x hintx tendsto_id) ?_
      simp only [id]
      refine Tendsto.congr' ?_ (Tendsto.sub tendsto_const_nhds hL)
      filter_upwards [eventually_gt_atTop (max x 1)] with T hT
      have hxT : x < T := lt_of_le_of_lt (le_max_left x 1) hT
      rw [show (∫ t in x..T, -iteratedDerivWithin 1 f (Ici 0) t) =
          ∫ t in x..T, -iteratedDerivWithin 1 f (Icc x T) t from by
        apply intervalIntegral.integral_congr_ae
        apply ae_of_all volume; intro t ht
        rw [uIoc_of_le hxT.le] at ht
        have ht_pos : 0 < t := lt_of_le_of_lt hx ht.1
        have hcda : ContDiffAt ℝ (↑1 : WithTop ℕ∞) f t :=
          (hcm.contDiffOn.contDiffAt (Ici_mem_nhds ht_pos)).of_le (nat_le_top _)
        congr 1
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hxT) hcda
            (Ioc_subset_Icc_self ht),
          iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcda
            (mem_Ici.mpr ht_pos.le)]]
      exact hcm.integral_neg_deriv x T hx hxT
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      have ih_applied := ih hk1
      simp only [show k + 1 - 1 = k from by omega]
      have hintk := ibp_kernel_integrableOn f hcm k hk1 x hx L hL
      have hintkp1 := ibp_kernel_integrableOn f hcm (k + 1) (by omega) x hx L hL
      simp only [show k + 1 - 1 = k from by omega] at hintkp1
      have hibp := fun T (hT : x < T) => ibp_finite_interval f hcm k hk x T hx hT
      have hbdry := boundary_term_decay f hcm k hk x hx L hL
      have htend_k : Tendsto (fun T => ∫ t in x..T,
          (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
        rw [← ih_applied]; exact intervalIntegral_tendsto_integral_Ioi x hintk tendsto_id
      have hsign : ∀ T, ∫ t in x..T,
          (-1 : ℝ) ^ (k + 1) / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t =
          -(∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
          iteratedDerivWithin k f (Ici 0) t) := by
        intro T; rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr_ae; apply ae_of_all; intro t _
        have : (-1 : ℝ) ^ (k + 1) = (-1) ^ k * (-1) := pow_succ (-1) k
        rw [this]; ring
      have htend_sum : Tendsto (fun T =>
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (T - x) ^ k *
            iteratedDerivWithin k f (Ici 0) T +
          ∫ t in x..T, (-1 : ℝ) ^ k / ↑(k - 1).factorial * (t - x) ^ (k - 1) *
            iteratedDerivWithin k f (Ici 0) t) atTop (nhds (f x - L)) := by
        simpa [zero_add] using hbdry.add htend_k
      have htend_via_ibp : Tendsto (fun T => ∫ t in x..T,
          (-1 : ℝ) ^ (k + 1) / ↑k.factorial * (t - x) ^ k *
          iteratedDerivWithin (k + 1) f (Ici 0) t) atTop (nhds (f x - L)) :=
        Tendsto.congr' (Filter.Eventually.mono (eventually_gt_atTop x) fun T hxT => by
          have := hibp T hxT; linarith [hsign T]) htend_sum
      exact tendsto_nhds_unique
        ((intervalIntegral_tendsto_integral_Ioi x hintkp1 tendsto_id).congr
          (fun T => by simp [id])) htend_via_ibp

/-- **Chafaï identity**: `f(x) - L = ∫ φ_n(x, ·) d(chafaiRescaled f n)` for `n ≥ 2`, `x ≥ 0`. -/
lemma chafai_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (hx : 0 ≤ x)
    (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    f x - L = ∫ p : ℝ≥0, bernstein_kernel n x (p : ℝ) ∂(chafaiRescaled f n) := by
  have hn0 : n ≠ 0 := by omega
  have step1 : ∫ p : ℝ≥0, bernstein_kernel n x (p : ℝ) ∂(chafaiRescaled f n) =
      ∫ t, bernstein_kernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) := by
    rw [chafaiRescaled_eq_map]
    exact integral_map_of_stronglyMeasurable (chafaiRescaling_measurable n)
      ((measurable_bernstein_kernel n x).comp measurable_subtype_coe).stronglyMeasurable
  have step2 : ∫ t, bernstein_kernel n x (chafaiRescaling n t : ℝ) ∂(chafaiMeasure f n) =
      ∫ t in Ioi 0, bernstein_kernel n x (((n : ℝ) - 1) / t) * chafaiDensity f n t := by
    rw [chafaiMeasure_eq_withDensity]
    have hcont_density : ContinuousOn (chafaiDensity f n) (Ici 0) :=
      continuousOn_chafaiDensity hcm n
    rw [integral_withDensity_eq_integral_toReal_smul₀
      (AEMeasurable.ennreal_ofReal
        ((hcont_density.mono Ioi_subset_Ici_self).aestronglyMeasurable
          measurableSet_Ioi |>.aemeasurable))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_ae measurableSet_Ioi
      (ae_of_all _ fun t ht => by
        simp only [smul_eq_mul, Set.mem_Ioi] at ht ⊢
        rw [chafaiRescaling_coe_of_pos (by omega : 1 ≤ n) ht]
        rw [ENNReal.toReal_ofReal (chafaiDensity_nonneg hcm n t ht.le)]; ring)
  have step3 := chafai_kernel_density_eq f hcm n hn x hx
  have step4 := chafai_repeated_ibp f hcm n (by omega) x hx L hL
  linarith

end TauCeti

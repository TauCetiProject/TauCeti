/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import TauCeti.Analysis.CompletelyMonotone.BernsteinIntegral

/-!
# Approximating measures for Bernstein's theorem

The Chafaï-style construction of the representing measure in Bernstein's theorem. For a
completely monotone `f` the densities `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` are nonnegative,
define finite measures `chafaiMeasure f n` whose total mass is bounded by `f(0) - f(∞)`, and after
the rescaling `t ↦ (n-1)/t` give measures `chafaiRescaled f n` on `ℝ≥0` whose Laplace kernels
`(1 - xp/(n-1))₊ⁿ⁻¹` converge to `e^{-xp}`. These feed the Prokhorov tightness argument.

These build on the `IsCompletelyMonotone` API in `CompletelyMonotone/Basic.lean` and
`CompletelyMonotone/BernsteinAux.lean`.

## Main declarations

* `TauCeti.chafaiDensity`, `TauCeti.chafaiMeasure`: the approximating densities and measures.
* `TauCeti.bernstein_kernel`, `TauCeti.bernstein_kernel_tendsto`: the rescaled Laplace kernel and
  its pointwise limit `e^{-xp}`.
* `TauCeti.chafaiRescaled`, `TauCeti.chafaiRescaled_mass_eq`: the `ℝ≥0`-valued pushed-forward
  measures and mass preservation.
* `TauCeti.chafaiMeasure_finite_mass`: finiteness and the total-mass bound `≤ f(0) - L`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped ContDiff NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for the `n`-th approximating measure in
the Bernstein proof (Chafaï 2013). -/
noncomputable def chafaiDensity (f : ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  if n = 0 then 0
  else (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
    t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t

/-- `chafaiDensity f 0 = 0`. -/
@[simp] lemma chafaiDensity_zero (f : ℝ → ℝ) (t : ℝ) : chafaiDensity f 0 t = 0 := by
  rw [chafaiDensity, if_pos rfl]

/-- The defining formula for `chafaiDensity` at a nonzero order. -/
lemma chafaiDensity_of_ne_zero {n : ℕ} (hn : n ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    chafaiDensity f n t = (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t := by
  rw [chafaiDensity, if_neg hn]

/-- `chafaiDensity f n` is continuous on `[0, ∞)` for a completely monotone `f`. -/
lemma continuousOn_chafaiDensity (hcm : IsCompletelyMonotone f) (n : ℕ) :
    ContinuousOn (chafaiDensity f n) (Ici 0) := by
  by_cases hn : n = 0
  · subst n
    have hzero : chafaiDensity f 0 = fun _ : ℝ => 0 := funext (chafaiDensity_zero f)
    rw [hzero]
    exact continuousOn_const
  have heq : chafaiDensity f n = fun t => (-1 : ℝ) ^ n / (Nat.factorial (n - 1) : ℝ) *
      t ^ (n - 1) * iteratedDerivWithin n f (Ici 0) t :=
    funext (chafaiDensity_of_ne_zero hn f)
  rw [heq]
  exact (continuousOn_const.mul ((continuousOn_pow _).mono fun _ _ => trivial)).mul
    (hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0))

/-- The `n`-th approximating measure `σ_n` for the Bernstein proof, with density `ρ_n` on
`(0, ∞)`. -/
noncomputable def chafaiMeasure (f : ℝ → ℝ) (n : ℕ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t))

/-- `chafaiMeasure` as a `withDensity`, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiMeasure_eq_withDensity (f : ℝ → ℝ) (n : ℕ) :
    chafaiMeasure f n =
      (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (chafaiDensity f n t)) := by
  rw [chafaiMeasure]

/-- The mass `chafaiMeasure f n` assigns to a measurable set, as a set lintegral of the density. -/
lemma chafaiMeasure_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    chafaiMeasure f n s =
      ∫⁻ t in s, ENNReal.ofReal (chafaiDensity f n t) ∂(volume.restrict (Ioi 0)) := by
  rw [chafaiMeasure, withDensity_apply _ hs]

/-- The density `ρ_n` is nonnegative for completely monotone functions. -/
lemma chafaiDensity_nonneg (hcm : IsCompletelyMonotone f) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ chafaiDensity f n t := by
  simp only [chafaiDensity]
  split_ifs with hn
  · exact le_refl 0
  · have hcm_sign := hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht
    have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht _) hfact_pos.le) hcm_sign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
@[simp] lemma chafaiDensity_one (t : ℝ) :
    chafaiDensity f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [chafaiDensity]

/-- Difference of two successive Chafaï densities, in the algebraic form used by integration by
parts. -/
lemma chafaiDensity_succ_succ_sub_succ (f : ℝ → ℝ) (m : ℕ) (t : ℝ) :
    chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t =
      ↑(m + 1) * t ^ m *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 1) f (Ici 0) t) +
        t ^ (m + 1) *
          (((-1 : ℝ) ^ (m + 2) / ↑(m + 1).factorial) *
            iteratedDerivWithin (m + 2) f (Ici 0) t) := by
  have hm2 : m + 2 ≠ 0 := by omega
  have hm1 : m + 1 ≠ 0 := by omega
  have hdens_m2 :
      chafaiDensity f (m + 2) t =
        (-1 : ℝ) ^ (m + 2) / ((m + 1).factorial : ℝ) *
          t ^ (m + 1) * iteratedDerivWithin (m + 2) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm2]
    norm_num
  have hdens_m1 :
      chafaiDensity f (m + 1) t =
        (-1 : ℝ) ^ (m + 1) / (m.factorial : ℝ) *
          t ^ m * iteratedDerivWithin (m + 1) f (Ici 0) t := by
    rw [chafaiDensity_of_ne_zero hm1]
    norm_num
  rw [hdens_m2, hdens_m1]
  have hfact : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * ↑m.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  have hfact_ne : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hsucc_ne : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hneg : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
  rw [hneg]
  field_simp
  ring

/-! ## Rescaled measures and Prokhorov extraction -/

/-- The Bernstein kernel `φ_n(x,p) = max(1 - xp/(n-1), 0)ⁿ⁻¹` for `n ≥ 2`. After the change of
variable `p = (n-1)/t`, the Taylor integral kernel on `[0, T]` becomes `φ_n(x, p)`, which
converges pointwise to `e^{-xp}` as `n → ∞` (the classical `(1-x/n)ⁿ → e^{-x}` limit). -/
noncomputable def bernstein_kernel (n : ℕ) (x p : ℝ) : ℝ :=
  if n ≤ 1 then 0 else (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1)

/-- The Bernstein kernel vanishes for `n ≤ 1`. -/
@[simp] lemma bernstein_kernel_of_le_one {n : ℕ} (hn : n ≤ 1) (x p : ℝ) :
    bernstein_kernel n x p = 0 := by
  rw [bernstein_kernel, if_pos hn]

/-- The defining formula for the Bernstein kernel at `2 ≤ n`. -/
lemma bernstein_kernel_of_two_le {n : ℕ} (hn : 2 ≤ n) (x p : ℝ) :
    bernstein_kernel n x p = (max (1 - x * p / (↑(n - 1) : ℝ)) 0) ^ (n - 1) := by
  have hnle : ¬ n ≤ 1 := by omega
  rw [bernstein_kernel, if_neg hnle]

/-- The Bernstein kernel is nonnegative. -/
@[simp] lemma bernstein_kernel_nonneg (n : ℕ) (x p : ℝ) : 0 ≤ bernstein_kernel n x p := by
  rw [bernstein_kernel]; split_ifs <;> positivity

/-- The Bernstein kernel is measurable in `p` for fixed `n` and `x`. -/
lemma measurable_bernstein_kernel (n : ℕ) (x : ℝ) : Measurable (bernstein_kernel n x) := by
  unfold bernstein_kernel; split_ifs
  · exact measurable_const
  · fun_prop

/-- **Pointwise convergence of the Bernstein kernel** to the Laplace kernel:
`φ_n(x,p) → e^{-xp}` as `n → ∞`, for `x, p ≥ 0`. -/
lemma bernstein_kernel_tendsto (x p : ℝ) :
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

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`. -/
noncomputable def chafaiRescaling (n : ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (((n : ℝ) - 1) / t)

/-- The rescaling map `t ↦ max ((n-1)/t) 0`, valued in `ℝ≥0`, is measurable. -/
lemma chafaiRescaling_measurable (n : ℕ) :
    Measurable (chafaiRescaling n) :=
  continuous_real_toNNReal.measurable.comp (measurable_const.div measurable_id)

/-- On the positive part of the source, the `ℝ≥0` rescaling coerces back to `(n-1)/t`. -/
lemma chafaiRescaling_coe_of_pos {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    (chafaiRescaling n t : ℝ) = ((n : ℝ) - 1) / t := by
  have hnum : 0 ≤ (n : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast hn)
  have hnonneg : 0 ≤ ((n : ℝ) - 1) / t := div_nonneg hnum ht.le
  simp [chafaiRescaling, Real.coe_toNNReal', max_eq_left hnonneg]

/-- The rescaled measure `σ̃_n`: pushforward of `chafaiMeasure f n` under the `ℝ≥0` rescaling. -/
noncomputable def chafaiRescaled (f : ℝ → ℝ) (n : ℕ) : Measure ℝ≥0 :=
  Measure.map (chafaiRescaling n) (chafaiMeasure f n)

/-- `chafaiRescaled` as a pushforward, exposed as a lemma rather than an unfoldable body. -/
lemma chafaiRescaled_eq_map (f : ℝ → ℝ) (n : ℕ) :
    chafaiRescaled f n = Measure.map (chafaiRescaling n) (chafaiMeasure f n) := by
  rw [chafaiRescaled]

/-- The mass `chafaiRescaled f n` assigns to a measurable set, as the pushforward formula. -/
lemma chafaiRescaled_apply (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    chafaiRescaled f n s = chafaiMeasure f n ((chafaiRescaling n) ⁻¹' s) := by
  rw [chafaiRescaled, Measure.map_apply (chafaiRescaling_measurable n) hs]

/-- `chafaiMeasure f n` lives on `(0, ∞)`: its complement has zero mass. -/
lemma chafaiMeasure_compl_Ioi (f : ℝ → ℝ) (n : ℕ) :
    (chafaiMeasure f n) (Ioi 0)ᶜ = 0 := by
  unfold chafaiMeasure
  rw [withDensity_apply _ (measurableSet_Ioi.compl)]
  apply setLIntegral_measure_zero
  rw [Measure.restrict_apply (measurableSet_Ioi.compl)]
  have : (Ioi (0 : ℝ))ᶜ ∩ Ioi 0 = ∅ := by ext x; simp [Set.mem_Ioi]
  rw [this, measure_empty]

/-- Pushforward preserves total mass. -/
lemma chafaiRescaled_mass_eq (f : ℝ → ℝ) (n : ℕ) :
    (chafaiRescaled f n) univ = (chafaiMeasure f n) univ := by
  unfold chafaiRescaled
  rw [Measure.map_apply (chafaiRescaling_measurable n) MeasurableSet.univ, Set.preimage_univ]

/-- **IBP identity** for the CM density:
`∫₀ᵀ ρ_{m+2}(t) dt = B_{m+2}(T) + ∫₀ᵀ ρ_{m+1}(t) dt`. -/
private lemma chafaiDensity_ibp_identity (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (m : ℕ) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 1) t := by
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set g' := iteratedDerivWithin (m + 2) f (Ici 0)
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hg_cont : ContinuousOn g (Ici 0) :=
    hcm.contDiffOn.continuousOn_iteratedDerivWithin (nat_le_top _) (uniqueDiffOn_Ici 0)
  have hg_deriv : ∀ t, 0 < t → HasDerivAt g (g' t) t :=
    fun t ht => hcm.hasDerivAt_iteratedDerivWithin_succ (m + 1) ht
  have huIcc : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul
      (continuousOn_const.mul (hg_cont.mono Icc_subset_Ici_self))
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) t :=
    fun t ht => (hasDerivAt_pow (m + 1) t).mul ((hg_deriv t ht.1).const_mul c)
  have hcm_int : ∀ k, k ≠ 0 → IntervalIntegrable (fun t => chafaiDensity f k t) volume 0 T := by
    intro k hk; apply ContinuousOn.intervalIntegrable; rw [huIcc]
    exact (continuousOn_chafaiDensity hcm k).mono Icc_subset_Ici_self
  have hF'_eq : ∀ t, ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t) =
      chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t := by
    intro t
    simp only [g, g', c]
    exact (chafaiDensity_succ_succ_sub_succ f m t).symm
  have hF'_int : IntervalIntegrable
      (fun t => ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) volume 0 T :=
    ((hcm_int _ (by omega)).sub (hcm_int _ (by omega))).congr fun t _ => (hF'_eq t).symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv hF'_int
  have hstep1 : ∫ t in (0 : ℝ)..T,
      (chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t) = F T - F 0 := by
    rw [← hftc]
    exact intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t _ => (hF'_eq t).symm)
  have hm1 : m + 1 ≠ 0 := by omega
  have hF0 : F 0 = 0 := by simp [F, zero_pow hm1]
  rw [hF0, sub_zero] at hstep1
  rw [intervalIntegral.integral_sub (hcm_int _ (by omega)) (hcm_int _ (by omega))] at hstep1
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- **IBP step**: integrating from density `k` to density `k-1`. -/
lemma integral_chafaiDensity_le_pred (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (k : ℕ) (hk : 2 ≤ k) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f k t ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f (k - 1) t := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  have hibp := chafaiDensity_ibp_identity f hcm m T hT
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

/-- **Total mass bound with a chosen limit**: `chafaiMeasure f n` is finite with total mass
`≤ f(0) - L` whenever `f(t) → L` at infinity. -/
lemma chafaiMeasure_finite_mass_of_tendsto (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (chafaiMeasure f n) ∧
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  by_cases hn0 : n = 0
  · subst n
    have hzero : chafaiMeasure f 0 = 0 := by
      rw [chafaiMeasure_eq_withDensity]
      ext s hs
      rw [withDensity_apply _ hs]
      simp
    rw [hzero]
    exact ⟨inferInstance, by simp⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) := continuousOn_chafaiDensity hcm n
  have hbound : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, chafaiDensity f n t ≤ f 0 - L := by
    have base : ∀ T, 0 < T → ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t = f 0 - f T := by
      intro T hT
      have h1 : ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t =
          ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
        intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t)
      rw [h1, ← hcm.integral_neg_deriv_Ici T hT, hcm.integral_mass T hT]
    have density_le : ∀ j, 1 ≤ j → ∀ T, 0 < T →
        ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
      intro j hj
      induction j with
      | zero => omega
      | succ p ih =>
        intro T hT
        by_cases hp : p = 0
        · subst hp; exact le_of_eq (base T hT)
        · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
              ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
                simpa using integral_chafaiDensity_le_pred f hcm (p + 1) (by omega) T hT
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
    linarith [density_le n hn T hT]
  have hint : IntegrableOn (chafaiDensity f n) (Ioi 0) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
      (l := atTop) (b := id)
    · intro T
      exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
        |>.mono_set Ioc_subset_Icc_self
    · exact tendsto_id
    · filter_upwards [eventually_gt_atTop 0] with T hT; simp only [id]
      calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f n t‖
          = ∫ t in (0 : ℝ)..T, chafaiDensity f n t := by
            apply intervalIntegral.integral_congr_ae; apply ae_of_all
            intro t ht; rw [uIoc_of_le hT.le] at ht
            rw [Real.norm_eq_abs, abs_of_nonneg (chafaiDensity_nonneg hcm n t ht.1.le)]
        _ ≤ f 0 - L := hbound T hT
  have hfin : IsFiniteMeasure (chafaiMeasure f n) := by
    unfold chafaiMeasure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
    rw [chafaiMeasure_eq_withDensity]
    rw [withDensity_apply _ MeasurableSet.univ]; simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
        chafaiDensity_nonneg hcm n t ht.le)]
    exact ENNReal.ofReal_le_ofReal
      (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
        (eventually_atTop.mpr ⟨1, fun T hT => hbound T (by linarith)⟩))
  exact ⟨hfin, hmass⟩

/-- **Natural total mass bound**: for a completely monotone `f`, the Chafaï measures are finite
and uniformly bounded by `f(0) - L`, where `L` is the automatically obtained limit of `f` at
infinity. -/
lemma chafaiMeasure_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiMeasure f n) ∧
        (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn⟩ := hcm.tendsto_atTop
  exact ⟨L, hL, hL_nn, fun n => chafaiMeasure_finite_mass_of_tendsto f hcm n L hL⟩

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import TauCeti.Analysis.CompletelyMonotone.Integral

/-!
# Approximating measures for Bernstein's theorem

The Chafaï-style construction of the representing measure in Bernstein's theorem. For a
completely monotone `f` the densities `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` are nonnegative on
`[0, ∞)`, the positive support used by `chafaiMeasure`; they define finite measures whose total
mass is bounded by `f(0) - f(∞)`, and after the rescaling `t ↦ (n-1)/t` give measures
`chafaiRescaled f n` on `ℝ≥0` whose Laplace kernels `(1 - xp/(n-1))₊ⁿ⁻¹` converge to `e^{-xp}`.
These feed the Prokhorov tightness argument.

These build on the `IsCompletelyMonotone` API in `CompletelyMonotone/Basic.lean` and
`CompletelyMonotone/Integral.lean`.

## Main declarations

* `TauCeti.chafaiDensity`, `TauCeti.chafaiMeasure`: the approximating densities and measures.
* `TauCeti.bernstein_kernel`, `TauCeti.continuous_bernstein_kernel`,
  `TauCeti.bernstein_kernel_nonneg`, `TauCeti.bernstein_kernel_le_one`,
  `TauCeti.bernsteinKernelBCF`, `TauCeti.bernsteinKernelBCF_apply`,
  `TauCeti.bernstein_kernel_tendsto`: the rescaled Laplace kernel, its bundled
  bounded-continuous `p`-dependence on the nonnegative half-line, and its pointwise limit
  `e^{-xp}`.
* `TauCeti.chafaiRescaled`, `TauCeti.chafaiRescaled_mass_eq`: the `ℝ≥0`-valued pushed-forward
  measures and mass preservation.
* `TauCeti.chafaiMeasure_finite_mass`, `TauCeti.chafaiRescaled_finite_mass`: finiteness and the
  total-mass bound `≤ f(0) - L`.

## References

* Roadmap: `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part B (Bernstein theorem milestone).

* D. Chafaï, *Aspects of the Bernstein theorem* (2013).
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions* (de Gruyter, 2nd ed. 2012), Ch. 1.
-/

public section

open MeasureTheory Set intervalIntegral Filter
open scoped BoundedContinuousFunction ContDiff NNReal Topology

namespace TauCeti

variable {f : ℝ → ℝ}

/-! ## Smoothness-index helpers -/

private lemma nat_le_top (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-! ## Measure construction for Bernstein -/

/-- The density `ρ_n(t) = (-1)ⁿ/(n-1)! · tⁿ⁻¹ · f⁽ⁿ⁾(t)` for nonzero `n`, used for the `n`-th
approximating measure in the Bernstein proof (Chafaï 2013). By convention the `n = 0` branch
returns `0`. -/
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

/-- `chafaiDensity f n` is continuous on `[0, ∞)` when `f` has `n` continuous derivatives
there. -/
lemma continuousOn_chafaiDensity {n : ℕ}
    (hf : ContDiffOn ℝ (n : WithTop ℕ∞) f (Ici 0)) :
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
    (hf.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ici 0))

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

/-- The density `ρ_n(t)` is nonnegative when `t ≥ 0` and the `n`-th derivative has the
alternating sign at `t`. -/
lemma chafaiDensity_nonneg {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hsign : 0 ≤ (-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) :
    0 ≤ chafaiDensity f n t := by
  simp only [chafaiDensity]
  split_ifs with hn
  · exact le_refl 0
  · have hfact_pos : (0 : ℝ) < ↑(Nat.factorial (n - 1)) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    calc (-1 : ℝ) ^ n / ↑(Nat.factorial (n - 1)) * t ^ (n - 1) *
          iteratedDerivWithin n f (Ici 0) t
        = t ^ (n - 1) / ↑(Nat.factorial (n - 1)) *
          ((-1 : ℝ) ^ n * iteratedDerivWithin n f (Ici 0) t) := by field_simp
      _ ≥ 0 := mul_nonneg (div_nonneg (pow_nonneg ht _) hfact_pos.le) hsign

/-- For `n = 1`, the density simplifies to `-f'(t)`. -/
@[simp] lemma chafaiDensity_one (t : ℝ) :
    chafaiDensity f 1 t = -iteratedDerivWithin 1 f (Ici 0) t := by
  simp [chafaiDensity]

/-- Difference of two successive Chafaï densities, in the algebraic form used by integration by
parts. -/
private lemma chafaiDensity_succ_succ_sub_succ (f : ℝ → ℝ) (m : ℕ) (t : ℝ) :
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

/-- The Bernstein kernel is continuous in `p` for fixed `n` and `x`. -/
lemma continuous_bernstein_kernel (n : ℕ) (x : ℝ) : Continuous (bernstein_kernel n x) := by
  unfold bernstein_kernel
  split_ifs <;> fun_prop

/-- The Bernstein kernel is nonnegative. -/
@[simp] lemma bernstein_kernel_nonneg (n : ℕ) (x p : ℝ) : 0 ≤ bernstein_kernel n x p := by
  rw [bernstein_kernel]; split_ifs <;> positivity

/-- On the nonnegative half-plane, the Bernstein kernel is bounded above by `1`. -/
lemma bernstein_kernel_le_one {n : ℕ} {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) :
    bernstein_kernel n x p ≤ 1 := by
  rw [bernstein_kernel]
  split_ifs with hn
  · norm_num
  · have hn_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hratio_nonneg : 0 ≤ x * p / (↑(n - 1) : ℝ) :=
      div_nonneg (mul_nonneg hx hp) hn_pos.le
    have hbase_nonneg : 0 ≤ max (1 - x * p / (↑(n - 1) : ℝ)) 0 := le_max_right _ _
    have hbase_le_one : max (1 - x * p / (↑(n - 1) : ℝ)) 0 ≤ 1 := by
      exact max_le (by linarith) zero_le_one
    exact pow_le_one₀ hbase_nonneg hbase_le_one

/-- The Bernstein kernel as a bundled bounded continuous test function of the nonnegative
variable `p`, for fixed `n` and nonnegative `x`. -/
@[expose]
noncomputable def bernsteinKernelBCF (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : ℝ≥0 →ᵇ ℝ where
  toFun := fun p => bernstein_kernel n x (p : ℝ)
  continuous_toFun := (continuous_bernstein_kernel n x).comp continuous_subtype_val
  map_bounded' :=
    ⟨1, fun p q => by
      rw [Real.dist_eq]
      have hp0 : 0 ≤ bernstein_kernel n x (p : ℝ) := bernstein_kernel_nonneg n x (p : ℝ)
      have hp1 : bernstein_kernel n x (p : ℝ) ≤ 1 := bernstein_kernel_le_one hx p.2
      have hq0 : 0 ≤ bernstein_kernel n x (q : ℝ) := bernstein_kernel_nonneg n x (q : ℝ)
      have hq1 : bernstein_kernel n x (q : ℝ) ≤ 1 := bernstein_kernel_le_one hx q.2
      exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩⟩

/-- The bundled Bernstein kernel evaluates to the unbundled kernel on `ℝ≥0`. -/
@[simp]
lemma bernsteinKernelBCF_apply (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (p : ℝ≥0) :
    bernsteinKernelBCF n hx p = bernstein_kernel n x (p : ℝ) := rfl

/-- The Bernstein kernel is measurable in `p` for fixed `n` and `x`. -/
lemma measurable_bernstein_kernel (n : ℕ) (x : ℝ) : Measurable (bernstein_kernel n x) := by
  unfold bernstein_kernel; split_ifs
  · exact measurable_const
  · fun_prop

/-- **Pointwise convergence of the Bernstein kernel** to the Laplace kernel:
`φ_n(x,p) → e^{-xp}` as `n → ∞`. -/
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

/-- Integrating against `chafaiRescaled f n` is integrating the pullback along the Chafaï
rescaling against `chafaiMeasure f n`. -/
lemma chafaiRescaled_integral (f : ℝ → ℝ) (n : ℕ) {g : ℝ≥0 → ℝ}
    (hg : AEStronglyMeasurable g (chafaiRescaled f n)) :
    ∫ x, g x ∂(chafaiRescaled f n) =
      ∫ t, g (chafaiRescaling n t) ∂(chafaiMeasure f n) := by
  rw [chafaiRescaled_eq_map] at hg ⊢
  exact MeasureTheory.integral_map (chafaiRescaling_measurable n).aemeasurable hg

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
private lemma chafaiDensity_ibp_identity (f : ℝ → ℝ) {m : ℕ}
    (hf : ContDiffOn ℝ ((m + 2 : ℕ) : WithTop ℕ∞) f (Ici 0)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 2) t =
    (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
      iteratedDerivWithin (m + 1) f (Ici 0) T +
    ∫ t in (0 : ℝ)..T, chafaiDensity f (m + 1) t := by
  set g := iteratedDerivWithin (m + 1) f (Ici 0)
  set g' := iteratedDerivWithin (m + 2) f (Ici 0)
  set c : ℝ := (-1) ^ (m + 2) / ↑(m + 1).factorial
  set F := fun t : ℝ => t ^ (m + 1) * (c * g t)
  have hg_cont : ContinuousOn g (Ici 0) :=
    (hf.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))).continuousOn_iteratedDerivWithin
      le_rfl (uniqueDiffOn_Ici 0)
  have hg_deriv : ∀ t, 0 < t → HasDerivAt g (g' t) t :=
    fun t ht =>
      ContDiffOn.hasDerivAt_iteratedDerivWithin hf (uniqueDiffOn_Ici 0) (Ici_mem_nhds ht)
  have huIcc : uIcc (0 : ℝ) T = Icc 0 T := uIcc_of_le hT.le
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((continuous_pow _).continuousOn).mul
      (continuousOn_const.mul (hg_cont.mono Icc_subset_Ici_self))
  have hF_deriv : ∀ t ∈ Ioo 0 T, HasDerivAt F
      (↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) t :=
    fun t ht => (hasDerivAt_pow (m + 1) t).mul ((hg_deriv t ht.1).const_mul c)
  have h_int_m2 : IntervalIntegrable (fun t => chafaiDensity f (m + 2) t) volume 0 T := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]
    exact (continuousOn_chafaiDensity (n := m + 2) hf).mono Icc_subset_Ici_self
  have h_int_m1 : IntervalIntegrable (fun t => chafaiDensity f (m + 1) t) volume 0 T := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]
    exact (continuousOn_chafaiDensity (n := m + 1)
      (hf.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2)))).mono Icc_subset_Ici_self
  have hF'_eq : ∀ t, ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t) =
      chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t := by
    intro t
    simp only [g, g', c]
    exact (chafaiDensity_succ_succ_sub_succ f m t).symm
  have hF'_int : IntervalIntegrable
      (fun t => ↑(m + 1) * t ^ m * (c * g t) + t ^ (m + 1) * (c * g' t)) volume 0 T :=
    (h_int_m2.sub h_int_m1).congr fun t _ => (hF'_eq t).symm
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hF_cont hF_deriv hF'_int
  have hstep1 : ∫ t in (0 : ℝ)..T,
      (chafaiDensity f (m + 2) t - chafaiDensity f (m + 1) t) = F T - F 0 := by
    rw [← hftc]
    exact intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t _ => (hF'_eq t).symm)
  have hm1 : m + 1 ≠ 0 := by omega
  have hF0 : F 0 = 0 := by simp [F, zero_pow hm1]
  rw [hF0, sub_zero] at hstep1
  rw [intervalIntegral.integral_sub h_int_m2 h_int_m1] at hstep1
  suffices hgoal : (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial * g T = F T by linarith
  simp only [F, c]; ring

/-- Monotonicity of the finite-interval Chafaï-density masses in the order:
`∫₀ᵀ dₖ ≤ ∫₀ᵀ dₖ₋₁` for `2 ≤ k` and `0 ≤ T`. This is the exported
integration-by-parts consequence
(the raw IBP identity `chafaiDensity_ibp_identity` is private); it is the per-step density
mass-monotonicity bound consumed by the Bernstein-identity assembly. -/
lemma integral_chafaiDensity_le_pred (f : ℝ → ℝ) {k : ℕ} (hk : 2 ≤ k)
    (hf : ContDiffOn ℝ (k : WithTop ℕ∞) f (Ici 0))
    (T : ℝ) (hT : 0 ≤ T)
    (hsign : 0 ≤ (-1 : ℝ) ^ (k - 1) * iteratedDerivWithin (k - 1) f (Ici 0) T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f k t ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f (k - 1) t := by
  rcases hT.eq_or_lt with rfl | hT_pos
  · simp
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  simp only [hsub]
  have hibp := chafaiDensity_ibp_identity (m := m) f hf T hT_pos
  set B := (-1 : ℝ) ^ (m + 2) * T ^ (m + 1) / ↑(m + 1).factorial *
    iteratedDerivWithin (m + 1) f (Ici 0) T
  have hB : B ≤ 0 := by
    have hsign_m : 0 ≤ (-1 : ℝ) ^ (m + 1) * iteratedDerivWithin (m + 1) f (Ici 0) T := by
      simpa [hsub] using hsign
    have h_neg : (-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T ≤ 0 := by
      have : (-1 : ℝ) ^ (m + 2) = (-1) ^ (m + 1) * (-1) := pow_succ (-1) (m + 1)
      rw [this]; nlinarith [hsign_m]
    suffices B = T ^ (m + 1) / ↑(m + 1).factorial *
        ((-1 : ℝ) ^ (m + 2) * iteratedDerivWithin (m + 1) f (Ici 0) T) by
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos
        (div_nonneg (pow_nonneg hT_pos.le _) (Nat.cast_nonneg _)) h_neg
    simp only [B]; ring
  linarith

/-- The public `n = 0` convention for Chafaï measures: the zeroth approximating measure is
zero. -/
@[simp]
lemma chafaiMeasure_zero (f : ℝ → ℝ) : chafaiMeasure f 0 = 0 := by
  rw [chafaiMeasure_eq_withDensity]
  ext s hs
  rw [withDensity_apply _ hs]
  simp

/-- The rescaled Chafaï measure on the target type `ℝ≥0` shares the `n = 0` zero convention:
`chafaiRescaled f 0 = 0`, as the pushforward of the zero measure. -/
@[simp]
lemma chafaiRescaled_zero (f : ℝ → ℝ) : chafaiRescaled f 0 = 0 := by
  rw [chafaiRescaled_eq_map, chafaiMeasure_zero, Measure.map_zero]

private lemma integral_chafaiDensity_one_eq (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t = f 0 - f T := by
  have h1 : ∫ t in (0 : ℝ)..T, chafaiDensity f 1 t =
      ∫ t in (0 : ℝ)..T, -iteratedDerivWithin 1 f (Ici 0) t :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun t _ => chafaiDensity_one t)
  rw [h1, ← hcm.integral_neg_deriv_Ici T hT.le, hcm.integral_mass T hT.le]

private lemma integral_chafaiDensity_le_sub (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (j : ℕ) (hj : 1 ≤ j) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f j t ≤ f 0 - f T := by
  induction j with
  | zero => omega
  | succ p ih =>
    by_cases hp : p = 0
    · subst hp
      exact le_of_eq (integral_chafaiDensity_one_eq f hcm T hT)
    · calc ∫ t in (0 : ℝ)..T, chafaiDensity f (p + 1) t
          ≤ ∫ t in (0 : ℝ)..T, chafaiDensity f p t := by
            exact integral_chafaiDensity_le_pred f (k := p + 1) (by omega)
              (hcm.contDiffOn.of_le (nat_le_top (p + 1)))
              T hT.le (by
                simpa using hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg p hT.le)
        _ ≤ f 0 - f T := ih (Nat.one_le_iff_ne_zero.mpr hp)

private lemma integral_chafaiDensity_le_tendsto_sub (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L)) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0 : ℝ)..T, chafaiDensity f n t ≤ f 0 - L := by
  linarith [integral_chafaiDensity_le_sub f hcm n hn T hT,
    hcm.le_of_tendsto_atTop hL hT.le]

private lemma chafaiDensity_integrableOn_Ioi_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L)) :
    IntegrableOn (chafaiDensity f n) (Ioi 0) := by
  have hcont : ContinuousOn (chafaiDensity f n) (Ici 0) :=
    continuousOn_chafaiDensity (n := n) ((hcm.contDiffOn).of_le (nat_le_top n))
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (f 0 - L) 0
    (l := atTop) (b := id)
  · intro T
    exact (hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
      |>.mono_set Ioc_subset_Icc_self
  · exact tendsto_id
  · filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [id]
    calc ∫ t in (0 : ℝ)..T, ‖chafaiDensity f n t‖
        = ∫ t in (0 : ℝ)..T, chafaiDensity f n t := by
          apply intervalIntegral.integral_congr_ae
          apply ae_of_all
          intro t ht
          rw [uIoc_of_le hT.le] at ht
          rw [Real.norm_eq_abs,
            abs_of_nonneg (chafaiDensity_nonneg ht.1.le
              (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.1.le))]
      _ ≤ f 0 - L := integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T hT

private lemma chafaiMeasure_mass_le_of_tendsto (f : ℝ → ℝ)
    (hcm : IsCompletelyMonotone f) (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    (hL : Tendsto f atTop (nhds L))
    (hint : IntegrableOn (chafaiDensity f n) (Ioi 0)) :
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  rw [chafaiMeasure_eq_withDensity]
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) =>
      chafaiDensity_nonneg ht.le (hcm.neg_one_pow_mul_iteratedDerivWithin_nonneg n ht.le))]
  exact ENNReal.ofReal_le_ofReal
    (le_of_tendsto (intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_id)
      (eventually_atTop.mpr ⟨1, fun T hT =>
        integral_chafaiDensity_le_tendsto_sub f hcm n hn L hL T (by linarith)⟩))

/-- **Total mass bound with a chosen limit**: `chafaiMeasure f n` is finite with total mass
`≤ f(0) - L` whenever `f(t) → L` at infinity. -/
lemma chafaiMeasure_finite_mass_of_tendsto (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f)
    (n : ℕ) (L : ℝ) (hL : Tendsto f atTop (nhds L)) :
    IsFiniteMeasure (chafaiMeasure f n) ∧
    (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  by_cases hn0 : n = 0
  · subst n
    rw [chafaiMeasure_zero]
    exact ⟨inferInstance, by simp⟩
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hint : IntegrableOn (chafaiDensity f n) (Ioi 0) :=
    chafaiDensity_integrableOn_Ioi_of_tendsto f hcm n hn L hL
  have hfin : IsFiniteMeasure (chafaiMeasure f n) := by
    unfold chafaiMeasure
    exact isFiniteMeasure_withDensity_ofReal hint.hasFiniteIntegral
  have hmass : (chafaiMeasure f n) univ ≤ ENNReal.ofReal (f 0 - L) :=
    chafaiMeasure_mass_le_of_tendsto f hcm n hn L hL hint
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

/-- **Natural rescaled total mass bound**: for a completely monotone `f`, the rescaled
Chafaï measures on `ℝ≥0` are finite and uniformly bounded by `f(0) - L`, where `L` is the
automatically obtained limit of `f` at infinity. -/
lemma chafaiRescaled_finite_mass (f : ℝ → ℝ) (hcm : IsCompletelyMonotone f) :
    ∃ L : ℝ, Tendsto f atTop (nhds L) ∧ 0 ≤ L ∧
      ∀ n,
        IsFiniteMeasure (chafaiRescaled f n) ∧
        (chafaiRescaled f n) univ ≤ ENNReal.ofReal (f 0 - L) := by
  obtain ⟨L, hL, hL_nn, hfinite⟩ := chafaiMeasure_finite_mass f hcm
  refine ⟨L, hL, hL_nn, fun n => ?_⟩
  have hmass := chafaiRescaled_mass_eq f n
  refine ⟨?_, ?_⟩
  · exact ⟨by rw [hmass]; exact (hfinite n).1.measure_univ_lt_top⟩
  · rw [hmass]
    exact (hfinite n).2

end TauCeti

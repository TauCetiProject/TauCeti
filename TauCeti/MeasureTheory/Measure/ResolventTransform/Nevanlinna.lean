/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import TauCeti.MeasureTheory.Measure.ResolventTransform.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.ResolventTransform.Expansion
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Analytic characterization of resolvent transforms on the real line

A holomorphic function `F` on the upper half-plane `{z : ℂ | 0 < z.im}` is the resolvent transform
`m_μ(z) = ∫ (x - z)⁻¹ dμ(x)` of a finite Borel measure `μ` on `ℝ` if and only if `0 ≤ Im F(z)` on
the upper half-plane and `y ‖F(iy)‖` is bounded at infinity along the imaginary axis. It is the
resolvent transform of a probability measure if and only if `iy F(iy) → -1` as `y → ∞`.

The proof passes through the Nevanlinna representation
`F(z) = b z + ∫ (1 + x z) / (x - z) dρ(x) + Re F(i)`
(`TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add`).
Along the imaginary axis, `y Im F(iy) = b y² + ∫ y² (1 + x²) / (x² + y²) dρ(x)`. Boundedness of
`y ‖F(iy)‖` forces the linear coefficient `b` to vanish and, by monotone convergence, makes
`1 + x²` integrable against `ρ`. Weighting `ρ` by `1 + x²` produces a finite measure `μ` whose
resolvent transform differs from `F` by a constant; sending `y → ∞` kills that constant because
both `F(iy)` and `m_μ(iy)` decay to zero.

We use Mathlib's `MeasureTheory.resolventTransform`, with sign `(x - z)⁻¹`, not `(z - x)⁻¹`.

## Main results

* `TauCeti.nevanlinnaKernel_eq_one_add_sq_mul_resolvent_sub`: away from its pole, the Nevanlinna
  kernel `(1 + x z) / (x - z)` equals `(1 + x²) (x - z)⁻¹ - x`.
* `MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq`: existence of a representing finite
  measure from `0 ≤ Im F` and an eventual bound on `y ‖F(iy)‖`.
* `MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq_iff`: analytic characterization of
  resolvent transforms of finite measures on `ℝ`.
* `MeasureTheory.exists_isFiniteMeasure_resolventTransform_eq_of_tendsto`: existence with
  prescribed total mass `c` when `iy F(iy) → -c`.
* `MeasureTheory.exists_isProbabilityMeasure_resolventTransform_eq_iff`: analytic characterization
  of resolvent transforms of probability measures on `ℝ`.

## References

* N. I. Akhiezer, *The Classical Moment Problem*, Oliver & Boyd (1965), Theorem 3.1.1.
* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.4.1.
* R. Schilling, R. Song, Z. Vondraček, *Bernstein Functions: Theory and Applications*, 2nd ed.,
  de Gruyter (2012), Chapter 6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology ENNReal

namespace TauCeti

/-- Away from its pole, the Nevanlinna kernel `(1 + x z) / (x - z)` decomposes into the weighted
resolvent `(1 + x²) (x - z)⁻¹` minus `x`. -/
theorem nevanlinnaKernel_eq_one_add_sq_mul_resolvent_sub {z : ℂ} {x : ℝ}
    (h : (x : ℂ) - z ≠ 0) :
    nevanlinnaKernel z x = ((1 + x ^ 2 : ℝ) : ℂ) * resolvent z x - x := by
  rw [nevanlinnaKernel_def, resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
  push_cast
  field_simp [h]
  ring

end TauCeti

namespace MeasureTheory

/-- Along the positive imaginary axis, the imaginary part of a Nevanlinna representation splits
into `b y` and a positive rational integral. -/
private lemma mul_im_nevanlinna_rep {ρ : Measure ℝ} [IsFiniteMeasure ρ] {F : ℂ → ℂ} {b c y : ℝ}
    (hy : 0 < y)
    (hrep : F (y * I) = (b : ℂ) * (y * I) + ∫ x, TauCeti.nevanlinnaKernel (y * I) x ∂ρ + c) :
    y * (F (y * I)).im =
      b * y ^ 2 + ∫ x, y ^ 2 * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ := by
  have hz : (y * I : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by simpa using hy
  have hi := TauCeti.integrable_nevanlinnaKernel hz ρ
  have him_int : (∫ x, TauCeti.nevanlinnaKernel (y * I) x ∂ρ).im =
      ∫ x, y * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ := by
    rw [← RCLike.im_eq_complex_im, ← integral_im (𝕜 := ℂ) hi]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [TauCeti.nevanlinnaKernel_im, normSq_apply, sq]
  have him : (F (y * I)).im =
      b * y + ∫ x, y * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ := by
    rw [hrep]
    simp [him_int]
  rw [him, mul_add, ← integral_const_mul]
  congr 1
  · ring
  · refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    ring

/-- Pointwise limit of the Nevanlinna imaginary-part kernel `y_n² (1 + x²) / (x² + y_n²)` as
`y_n = y₀ + n + 1 → ∞`. -/
private lemma tendsto_mul_one_add_sq_div_sq_add (y₀ x : ℝ) (hy₀ : 1 ≤ y₀) :
    Tendsto (fun n : ℕ ↦
        (y₀ + (n + 1 : ℝ)) ^ 2 * (1 + x ^ 2) / (x ^ 2 + (y₀ + (n + 1 : ℝ)) ^ 2))
      atTop (𝓝 (1 + x ^ 2)) := by
  let y : ℕ → ℝ := fun n ↦ y₀ + (n + 1 : ℝ)
  have hy_top : Tendsto y atTop atTop :=
    tendsto_atTop_add_const_left _ y₀
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n ↦ x ^ 2 * (y n ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := x ^ 2)).mul
      (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp hy_top))
  have hlim : Tendsto (fun n ↦ (1 + x ^ 2) / (x ^ 2 * (y n ^ 2)⁻¹ + 1)) atTop
      (𝓝 (1 + x ^ 2)) := by
    simpa [Pi.div_def] using (tendsto_const_nhds (x := 1 + x ^ 2)).div
      (hinv.add (tendsto_const_nhds (x := (1 : ℝ)))) (by norm_num)
  refine hlim.congr' (Eventually.of_forall fun n ↦ ?_)
  have hyn : y n ≠ 0 := by
    dsimp only [y]
    linarith [hy₀, Nat.cast_nonneg (α := ℝ) n]
  dsimp only [y]
  field_simp [hyn]

/-- The kernel `y² (1 + x²) / (x² + y²)` increases with `y > 0` and converges to `1 + x²`, so a
uniform bound on its integrals makes `1 + x²` integrable. -/
private lemma integrable_one_add_sq_of_integral_bound {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {y₀ C : ℝ} (hy₀ : 1 ≤ y₀)
    (hbdd : ∀ y : ℝ, y₀ ≤ y → ∫ x, y ^ 2 * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ ≤ C) :
    Integrable (fun x : ℝ ↦ 1 + x ^ 2) ρ := by
  let y : ℕ → ℝ := fun n ↦ y₀ + (n + 1 : ℝ)
  have hy1 (n : ℕ) : 1 ≤ y n := by linarith [hy₀, Nat.cast_nonneg (α := ℝ) n]
  let g : ℕ → ℝ → ℝ := fun n x ↦ y n ^ 2 * (1 + x ^ 2) / (x ^ 2 + y n ^ 2)
  have hg_nonneg (n : ℕ) (x : ℝ) : 0 ≤ g n x := by
    have : 0 < y n := by linarith [hy1 n]
    exact div_nonneg (by positivity) (by positivity)
  have hg_int (n : ℕ) : Integrable (g n) ρ := by
    have _ : 0 < y n := by linarith [hy1 n]
    refine Integrable.of_bound (by fun_prop : Measurable (g n)).aestronglyMeasurable (y n ^ 2)
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nonneg n x),
      div_le_iff₀ (by positivity : 0 < x ^ 2 + y n ^ 2)]
    have hy1sq : 1 ≤ y n ^ 2 := by nlinarith [hy1 n]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hg_mono : Monotone fun n x ↦ ENNReal.ofReal (g n x) := by
    intro m n hmn x
    apply ENNReal.ofReal_le_ofReal
    have hym : 0 < y m := by linarith [hy1 m]
    have _ : 0 < y n := by linarith [hy1 n]
    have hmn' : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    have hle : y m ≤ y n := by dsimp only [y]; linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hsq : 0 ≤ y n ^ 2 - y m ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ hym.le hle 2)
    have hdiff : y n ^ 2 * (1 + x ^ 2) * (x ^ 2 + y m ^ 2) -
        y m ^ 2 * (1 + x ^ 2) * (x ^ 2 + y n ^ 2) =
        (y n ^ 2 - y m ^ 2) * (1 + x ^ 2) * x ^ 2 := by ring
    linarith [hdiff, mul_nonneg (mul_nonneg hsq (by positivity : 0 ≤ 1 + x ^ 2)) (sq_nonneg x)]
  have hsup (x : ℝ) : (⨆ n, ENNReal.ofReal (g n x)) = ENNReal.ofReal (1 + x ^ 2) :=
    tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn ↦ hg_mono hmn x)
      (ENNReal.tendsto_ofReal (tendsto_mul_one_add_sq_div_sq_add y₀ x hy₀))
  have hlint : ∫⁻ x, ENNReal.ofReal (1 + x ^ 2) ∂ρ ≤ ENNReal.ofReal C := by
    simp_rw [← hsup]
    rw [lintegral_iSup (fun n ↦ (by fun_prop : Measurable (g n)).ennreal_ofReal) hg_mono]
    refine iSup_le fun n ↦ ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hg_int n) (ae_of_all _ (hg_nonneg n))]
    exact ENNReal.ofReal_le_ofReal
      (hbdd (y n) (by dsimp only [y]; linarith [Nat.cast_nonneg (α := ℝ) n]))
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ by positivity)]
  exact hlint.trans_lt ENNReal.ofReal_lt_top

/-- Weighting `ρ` by `1 + x²` converts the Nevanlinna integral into a resolvent transform minus
the first moment of `ρ`. -/
private lemma integral_nevanlinnaKernel_eq_resolventTransform_withDensity_sub {ρ : Measure ℝ}
    (hint1 : Integrable (fun x : ℝ ↦ 1 + x ^ 2) ρ) {z : ℂ} (hz : 0 < z.im) :
    ∫ x, TauCeti.nevanlinnaKernel z x ∂ρ =
      resolventTransform (ρ.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)) z -
        ∫ x, (x : ℂ) ∂ρ := by
  have hintx : Integrable (fun x : ℝ ↦ (x : ℂ)) ρ := by
    refine hint1.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [norm_real, Real.norm_eq_abs]
    nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
  have hxz (x : ℝ) : (x : ℂ) - z ≠ 0 := fun h ↦ hz.ne' (by simpa using (congrArg im h).symm)
  have hres_int : Integrable (fun x : ℝ ↦ ((1 + x ^ 2 : ℝ) : ℂ) * resolvent z x) ρ := by
    refine (hint1.mul_const |z.im|⁻¹).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Complex.norm_resolvent_real_le z x hz.ne') (by positivity)
  have hw_meas : Measurable fun x : ℝ ↦ ENNReal.ofReal (1 + x ^ 2) :=
    (by fun_prop : Measurable fun x : ℝ ↦ 1 + x ^ 2).ennreal_ofReal
  have hμz : resolventTransform (ρ.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)) z =
      ∫ x, ((1 + x ^ 2 : ℝ) : ℂ) * resolvent z x ∂ρ := by
    rw [resolventTransform_apply, integral_withDensity_eq_integral_toReal_smul hw_meas
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 + x ^ 2), real_smul]
  rw [hμz, ← integral_sub hres_int hintx]
  exact integral_congr_ae (ae_of_all _ fun x ↦
    TauCeti.nevanlinnaKernel_eq_one_add_sq_mul_resolvent_sub (hxz x))

/-- A nonnegative real `b` satisfying `b y² ≤ C` for all sufficiently large `y ≥ 1` vanishes. -/
private lemma eq_zero_of_mul_sq_le {b y₀ C : ℝ} (hb0 : 0 ≤ b) (hy₀1 : 1 ≤ y₀)
    (hle : ∀ y : ℝ, y₀ ≤ y → b * y ^ 2 ≤ C) : b = 0 := by
  by_contra hbne
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hbne)
  set y := max y₀ (C / b + 1)
  have hyy₀ : y₀ ≤ y := le_max_left _ _
  have hby : C < b * y := by
    rw [mul_comm, ← div_lt_iff₀ hbpos]
    linarith [le_max_right y₀ (C / b + 1)]
  have hby2 : b * y ≤ b * y ^ 2 := by
    rw [sq, ← mul_assoc]
    exact le_mul_of_one_le_right (by positivity) (hy₀1.trans hyy₀)
  linarith [hle y hyy₀]

/-- **Existence of a representing measure from the Pick–Nevanlinna conditions.** If `F` is
holomorphic on the upper half-plane with nonnegative imaginary part and `y ‖F(iy)‖` is eventually
bounded as `y → ∞`, then `F` agrees on the upper half-plane with the resolvent transform of a
finite measure on `ℝ`. -/
theorem exists_isFiniteMeasure_resolventTransform_eq {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im)
    (hbdd : ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z := by
  obtain ⟨ρ, b, hρ, hb0, hrep⟩ := TauCeti.exists_isFiniteMeasure_eq_nevanlinnaKernel_add hF him
  let _ := hρ
  obtain ⟨C, hCev⟩ := hbdd
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 (hCev.and (eventually_ge_atTop 1))
  have hy₀1 : 1 ≤ y₀ := (hy₀ y₀ le_rfl).2
  have him_le (y : ℝ) (hy : y₀ ≤ y) :
      b * y ^ 2 + ∫ x, y ^ 2 * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ ≤ C := by
    have hypos : 0 < y := by linarith
    rw [← mul_im_nevanlinna_rep hypos (hrep (y * I) (by simpa using hypos))]
    exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_im_le_norm _)) hypos.le).trans
      (hy₀ y hy).1
  have hb : b = 0 := eq_zero_of_mul_sq_le (C := C) hb0 hy₀1 fun y hy ↦ by
    have hpos : 0 < y := by linarith
    have hnn : 0 ≤ ∫ x, y ^ 2 * (1 + x ^ 2) / (x ^ 2 + y ^ 2) ∂ρ :=
      integral_nonneg fun x ↦ div_nonneg (by positivity) (by positivity)
    linarith [him_le y hy]
  have hint1 : Integrable (fun x : ℝ ↦ 1 + x ^ 2) ρ :=
    integrable_one_add_sq_of_integral_bound hy₀1 fun y hy ↦ by simpa [hb] using him_le y hy
  let μ : Measure ℝ := ρ.withDensity fun x ↦ ENNReal.ofReal (1 + x ^ 2)
  have hw_lt : ∫⁻ x, ENNReal.ofReal (1 + x ^ 2) ∂ρ < ⊤ := by
    have h := hint1.hasFiniteIntegral
    rwa [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ by positivity)] at h
  have hμfin : IsFiniteMeasure μ := isFiniteMeasure_withDensity hw_lt.ne
  let k : ℂ := ((F I).re : ℂ) - ∫ x, (x : ℂ) ∂ρ
  have hF_eq (z : ℂ) (hz : 0 < z.im) : F z = resolventTransform μ z + k := by
    rw [hrep z hz, hb, ofReal_zero, zero_mul, zero_add,
      integral_nevanlinnaKernel_eq_resolventTransform_withDensity_sub hint1 hz]
    dsimp only [μ, k]; ring
  have hF0 : Tendsto (fun y : ℝ ↦ F (y * I)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 <|
      squeeze_zero' (g := fun y : ℝ ↦ C * y⁻¹) (Eventually.of_forall fun _ ↦ norm_nonneg _)
        ((eventually_ge_atTop y₀).mono fun y hy ↦ by
          rw [← div_eq_mul_inv, le_div_iff₀' (by linarith : 0 < y)]; exact (hy₀ y hy).1)
        (by simpa using (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_zero)
  have hμ0 : Tendsto (fun y : ℝ ↦ resolventTransform μ (y * I)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 <|
      squeeze_zero' (g := fun y : ℝ ↦ y⁻¹ * μ.real univ)
        (Eventually.of_forall fun _ ↦ norm_nonneg _)
        ((eventually_gt_atTop 0).mono fun y hy ↦ by
          simpa [abs_of_pos hy] using
            norm_resolventTransform_le (μ := μ) (by simpa using hy.ne' : (y * I : ℂ).im ≠ 0))
        (by simpa using tendsto_inv_atTop_zero.mul (tendsto_const_nhds (x := μ.real univ)))
  have hk0 : k = 0 := by
    have hlim : Tendsto (fun y : ℝ ↦ F (y * I) - resolventTransform μ (y * I)) atTop (𝓝 k) :=
      tendsto_const_nhds.congr' <| (eventually_gt_atTop 0).mono fun y hy ↦ by
        dsimp only; rw [hF_eq (y * I) (by simpa using hy)]; ring
    simpa using tendsto_nhds_unique hlim (hF0.sub hμ0)
  exact ⟨μ, hμfin, fun z hz ↦ by simpa [hk0] using hF_eq z hz⟩

/-- **Analytic characterization of resolvent transforms of finite measures.** A function on `ℂ`
agrees on the upper half-plane with the resolvent transform of a finite Borel measure on `ℝ` if and
only if it is holomorphic there, has nonnegative imaginary part there, and satisfies an eventual
`O(y⁻¹)` bound along the positive imaginary axis. -/
theorem exists_isFiniteMeasure_resolventTransform_eq_iff {F : ℂ → ℂ} :
    (∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z) ↔
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
        (∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im) ∧
        ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C := by
  refine ⟨?_, fun ⟨hF, him, hbdd⟩ ↦ exists_isFiniteMeasure_resolventTransform_eq hF him hbdd⟩
  rintro ⟨μ, hμ, hF⟩
  let _ := hμ
  have hU : {z : ℂ | 0 < z.im} ⊆ (algebraMap ℝ ℂ '' μ.support)ᶜ := by
    rintro z (hz : 0 < z.im) ⟨x, -, rfl⟩
    simp at hz
  refine ⟨((analyticOn_resolventTransform.mono hU).differentiableOn).congr fun z hz ↦ hF z hz,
    fun z hz ↦ ?_, μ.real univ, ?_⟩
  · rw [hF z hz, im_resolventTransform]
    exact integral_nonneg fun x ↦ div_nonneg hz.le (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with y hy
    have hz : 0 < (y * I : ℂ).im := by simpa using hy
    rw [hF (y * I) hz]
    calc y * ‖resolventTransform μ (y * I)‖
        ≤ y * (|(y * I : ℂ).im|⁻¹ * μ.real univ) :=
          mul_le_mul_of_nonneg_left (norm_resolventTransform_le hz.ne') hy.le
      _ = μ.real univ := by simp [abs_of_pos hy, hy.ne']

/-- **Existence of a representing finite measure with prescribed total mass.** If `F` is
holomorphic on the upper half-plane with nonnegative imaginary part and `iy F(iy) → -c` as
`y → ∞`, then `F` is the resolvent transform of a finite measure on `ℝ` of total mass `c`. -/
theorem exists_isFiniteMeasure_resolventTransform_eq_of_tendsto {F : ℂ → ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (him : ∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im)
    (hlim : Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-(c : ℂ)))) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧ μ.real univ = c ∧
      ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z := by
  have hbdd : ∃ C : ℝ, ∀ᶠ y : ℝ in atTop, y * ‖F (y * I)‖ ≤ C := by
    refine ⟨|c| + 1, ?_⟩
    have hnorm : Tendsto (fun y : ℝ ↦ ‖(y : ℂ) * I * F (y * I)‖) atTop (𝓝 |c|) := by
      simpa using hlim.norm
    filter_upwards [hnorm.eventually (gt_mem_nhds (by linarith : |c| < |c| + 1)),
      eventually_gt_atTop 0] with y hy hypos
    simpa [abs_of_pos hypos] using hy.le
  obtain ⟨μ, hμ, hFμ⟩ := exists_isFiniteMeasure_resolventTransform_eq hF him hbdd
  let _ := hμ
  have hμlim : Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-(μ.real univ : ℂ))) :=
    (tendsto_mul_I_mul_resolventTransform (μ := μ)).congr' <|
      (eventually_gt_atTop 0).mono fun y hy ↦ by
        dsimp only
        rw [hFμ (y * I) (by simpa using hy)]
  have hmass : μ.real univ = c := by
    have := neg_inj.1 (tendsto_nhds_unique hμlim hlim)
    exact_mod_cast this
  exact ⟨μ, hμ, hmass, hFμ⟩

/-- **Analytic characterization of resolvent transforms of probability measures.** A function on
`ℂ` agrees on the upper half-plane with the resolvent transform of a probability measure on `ℝ` if
and only if it is holomorphic there, has nonnegative imaginary part there, and satisfies
`iy F(iy) → -1` as `y → ∞`. -/
theorem exists_isProbabilityMeasure_resolventTransform_eq_iff {F : ℂ → ℂ} :
    (∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ z : ℂ, 0 < z.im → F z = resolventTransform μ z) ↔
      DifferentiableOn ℂ F {z : ℂ | 0 < z.im} ∧
        (∀ z : ℂ, 0 < z.im → 0 ≤ (F z).im) ∧
        Tendsto (fun y : ℝ ↦ (y : ℂ) * I * F (y * I)) atTop (𝓝 (-1)) := by
  refine ⟨?_, fun ⟨hF, him, hlim⟩ ↦ ?_⟩
  · rintro ⟨μ, hμ, hF⟩
    let _ := hμ
    obtain ⟨hdiff, him, -⟩ :=
      exists_isFiniteMeasure_resolventTransform_eq_iff.1 ⟨μ, inferInstance, hF⟩
    have hlim1 : Tendsto (fun y : ℝ ↦ (y : ℂ) * I * resolventTransform μ (y * I))
        atTop (𝓝 (-1)) := by
      simpa using tendsto_mul_I_mul_resolventTransform (μ := μ)
    refine ⟨hdiff, him, hlim1.congr' ?_⟩
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact congrArg ((y : ℂ) * I * ·) (hF (y * I) (by simpa using hy)).symm
  · obtain ⟨μ, hμ, hmass, hFμ⟩ :=
      exists_isFiniteMeasure_resolventTransform_eq_of_tendsto (c := 1) hF him (by simpa using hlim)
    let _ := hμ
    have hprob : IsProbabilityMeasure μ :=
      ⟨by rw [← ENNReal.ofReal_one, ← hmass, ofReal_measureReal]⟩
    exact ⟨μ, hprob, hFμ⟩

end MeasureTheory

end

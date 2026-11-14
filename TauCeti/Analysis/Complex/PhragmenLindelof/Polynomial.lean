/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PhragmenLindelof.VerticalStrip
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Polynomial edge bounds in the Phragmén–Lindelöf strip principle

Let `f : ℂ → E` be holomorphic on an open vertical strip `a < Re z < b`, continuous on its closure,
and of admissible sub-double-exponential (in particular, finite-order) growth along the strip. If
`f` satisfies polynomial height bounds `‖f w‖ ≤ C₁ * (d + |Im w|) ^ p` on `Re w = a` and
`‖f w‖ ≤ C₂ * (d + |Im w|) ^ q` on `Re w = b` for some `d > 0`, then on the closed strip
`a ≤ Re z ≤ b` both the edge constants and the height exponents interpolate:
`‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) * C₁ ^ (1 - θ) * C₂ ^ θ *`
`(d + |Im z|) ^ ((1 - θ) p + θ q)`, where `θ = (Re z - a) / (b - a)`.

When `p = q = 0` the prefactor `((b - a) / d + 2) ^ 0` equals `1`, recovering the constant-edge
three-lines bound without loss. When `max |p| |q| > 0`, polynomial growth of the prefactor in the
normalized strip width `(b - a) / d` is genuine: on `[-R, R]` (`R ≥ 1`), the polynomial
`g(z) = (R ^ 2 - z ^ 2) / R` satisfies `‖g(±R + i t)‖ ≤ (1 + |t|) ^ 2` for all `t : ℝ`, while
`‖g(0)‖ = R`. Keeping `C₁ ^ (1 - θ) * C₂ ^ θ` factored out of a prefactor depending only on
`(b - a) / d`, `p`, and `q` allows parameters carried by `C₁` and `C₂` (such as an arithmetic
conductor in convexity bounds for L-functions) to interpolate uniformly across families. As in the
constant-edge Phragmén–Lindelöf theorem, the interior growth hypothesis cannot be omitted: on
`[0, 1]`, `z ↦ exp (sin (π z))` has norm `1` on both boundary lines and growth rate `c = π`, yet is
unbounded on `Re z = 1 / 2`.

The analytic inputs are Mathlib's `_root_.PhragmenLindelof.vertical_strip` and
`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`, combined with
`TauCeti.PhragmenLindelof.isBigO_exp_rpow_exp_exp_vertical_strip` after normalizing the polynomial
edge bounds by a holomorphic logarithmic weight symmetric across the strip.

## Main results

* `TauCeti.PhragmenLindelof.norm_le_mul_rpow_interp_of_isBigO_exp_exp`: polynomial-edge
  interpolation under Mathlib's sharp sub-double-exponential strip growth `c < π / (b - a)`.
* `TauCeti.PhragmenLindelof.norm_le_mul_rpow_interp_of_isBigO_exp_rpow`: polynomial-edge
  interpolation under finite-order growth on the open strip.
* `TauCeti.PhragmenLindelof.norm_le_mul_rpow_interp_of_isFiniteOrder`: polynomial-edge
  interpolation for complex functions of global finite order (`TauCeti.IsFiniteOrder`).
* `TauCeti.PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_isBigO_exp_exp`,
  `TauCeti.PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_isBigO_exp_rpow`,
  `TauCeti.PhragmenLindelof.exists_norm_le_mul_rpow_interp_of_isFiniteOrder`: conversion of
  asymptotic `O(|t| ^ p)` and `O(|t| ^ q)` vertical-line bounds along `cocompact ℝ` into uniform
  closed-strip bounds on `a < b`.

## References

* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., Oxford University Press, 1939, §5.65.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., Oxford University Press,
  1986, §§5.1, 9.41.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications **53**, 2004,
  §5.1.
-/

public section

open Complex Set Filter Asymptotics Bornology
open scoped Topology

namespace TauCeti.PhragmenLindelof

/-! ### Holomorphic strip normalizer -/

/-- Holomorphic primitive `z * log z - z` of `Complex.log` on `Complex.slitPlane`. -/
private noncomputable def logPrim (z : ℂ) : ℂ :=
  z * Complex.log z - z

/-- Holomorphic logarithmic weight on `[a, b]` whose real part tracks
`((1 - θ) * p + θ * q) * log (1 + |Im s|)` up to `max |p| |q| * log (b - a + 2)`, where
`θ = (Re s - a) / (b - a)`. -/
private noncomputable def stripLogWeight (a b p q : ℝ) (s : ℂ) : ℂ :=
  let w₀ : ℂ := ((a - 2 : ℝ) : ℂ)
  let w₁ : ℂ := ((b + 2 : ℝ) : ℂ)
  ((q - p) / (2 * (b - a)) : ℝ) * (logPrim (s - w₀) - logPrim (w₁ - s)) +
    ((p + q) / 4 : ℝ) * (Complex.log (s - w₀) + Complex.log (w₁ - s))

/-- `cexp (- stripLogWeight a b p q ·)` is holomorphic on the open strip and continuous on its
closure, since its branch cuts lie outside `Re s ∈ (a - 2, b + 2)`. -/
private theorem diffContOnCl_cexp_neg_stripLogWeight (a b p q : ℝ) :
    DiffContOnCl ℂ (fun s ↦ cexp (-stripLogWeight a b p q s)) (re ⁻¹' Ioo a b) := by
  let U : Set ℂ := re ⁻¹' Ioo (a - 2) (b + 2)
  have hdiff : DifferentiableOn ℂ (fun s ↦ cexp (-stripLogWeight a b p q s)) U := by
    intro s hs
    have hw₀ : s - ((a - 2 : ℝ) : ℂ) ∈ slitPlane := Or.inl (by simp [hs.1])
    have hw₁ : ((b + 2 : ℝ) : ℂ) - s ∈ slitPlane := Or.inl (by simp [hs.2])
    have hd₀ : DifferentiableAt ℂ (fun z : ℂ ↦ z - ((a - 2 : ℝ) : ℂ)) s :=
      differentiableAt_id.sub_const _
    have hd₁ : DifferentiableAt ℂ (fun z : ℂ ↦ ((b + 2 : ℝ) : ℂ) - z) s :=
      (differentiableAt_const _).sub differentiableAt_id
    have hp₀ : DifferentiableAt ℂ (fun z ↦ logPrim (z - ((a - 2 : ℝ) : ℂ))) s :=
      (hd₀.mul (hd₀.clog hw₀)).sub hd₀
    have hp₁ : DifferentiableAt ℂ (fun z ↦ logPrim (((b + 2 : ℝ) : ℂ) - z)) s :=
      (hd₁.mul (hd₁.clog hw₁)).sub hd₁
    have hL : DifferentiableAt ℂ (stripLogWeight a b p q) s :=
      ((hp₀.sub hp₁).const_mul _).add (((hd₀.clog hw₀).add (hd₁.clog hw₁)).const_mul _)
    exact hL.neg.cexp.differentiableWithinAt
  have hcl : closure (re ⁻¹' Ioo a b) ⊆ U := by
    refine (closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage continuous_re)).trans fun s hs ↦ ?_
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact ⟨hdiff.mono (subset_closure.trans hcl), hdiff.continuousOn.mono hcl⟩

/-- Uniform comparison between `log ‖x + i t‖` and `log (1 + |t|)` for `x ∈ [2, M]`. -/
private theorem abs_log_norm_ofReal_add_mul_I_sub_le {x M : ℝ} (hx2 : 2 ≤ x) (hxM : x ≤ M)
    (t : ℝ) :
    |Real.log ‖(x : ℂ) + t * I‖ - Real.log (1 + |t|)| ≤ Real.log M := by
  set z : ℂ := (x : ℂ) + t * I
  have hM2 : 2 ≤ M := hx2.trans hxM
  have hM0 : 0 < M := by positivity
  have ht1 : 0 < 1 + |t| := by positivity
  have hx_le : x ≤ ‖z‖ := by
    simpa [z, abs_of_pos (by positivity : 0 < x)] using abs_re_le_norm z
  have ht_le : |t| ≤ ‖z‖ := by simpa [z] using abs_im_le_norm z
  have hhalf : (1 + |t|) / 2 ≤ ‖z‖ := by
    rcases le_total |t| 2 with _ | _ <;> linarith
  have hlo : (1 + |t|) / M ≤ ‖z‖ :=
    (div_le_div_of_nonneg_left ht1.le two_pos hM2).trans hhalf
  have hhi : ‖z‖ ≤ M * (1 + |t|) := by
    have hsum : ‖z‖ ≤ x + |t| := by
      simpa [z, abs_of_pos (by positivity : 0 < x)] using norm_le_abs_re_add_abs_im z
    nlinarith [abs_nonneg t]
  have hz0 : 0 < ‖z‖ := (div_pos ht1 hM0).trans_le hlo
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h := Real.log_le_log (div_pos ht1 hM0) hlo
    rw [Real.log_div ht1.ne' hM0.ne'] at h
    linarith
  · have h := Real.log_le_log hz0 hhi
    rw [Real.log_mul hM0.ne' ht1.ne'] at h
    linarith

/-- Real derivative of `x ↦ Re (logPrim (x + i t)) - x * log (1 + |t|)` for `0 < x`. -/
private theorem hasDerivAt_re_logPrim_sub {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (logPrim ((y : ℂ) + t * I)).re - y * Real.log (1 + |t|))
      (Real.log ‖(x : ℂ) + t * I‖ - Real.log (1 + |t|)) x := by
  let γ : ℝ → ℂ := fun y ↦ (y : ℂ) + t * I
  have hγ : HasDerivAt γ 1 x := by
    simpa [γ] using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((t : ℂ) * I)
  have hslit : γ x ∈ slitPlane := Or.inl (by simpa [γ] using hx)
  have hne : γ x ≠ 0 := slitPlane_ne_zero hslit
  have hprim : HasDerivAt (fun y ↦ logPrim (γ y)) (Complex.log (γ x)) x := by
    have hmul : HasDerivAt (fun y ↦ γ y * Complex.log (γ y))
        (1 * Complex.log (γ x) + γ x * (1 / γ x)) x := hγ.mul (hγ.clog_real hslit)
    convert hmul.sub hγ using 1
    · rfl
    · rw [one_mul, mul_one_div_cancel hne, add_sub_cancel_right]
  have hre : HasDerivAt (fun y ↦ (logPrim (γ y)).re) (Real.log ‖γ x‖) x := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hprim
  have hlin : HasDerivAt (fun y : ℝ ↦ y * Real.log (1 + |t|)) (Real.log (1 + |t|)) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.log (1 + |t|))
  exact hre.sub hlin

/-- Mean-value estimate for `Re (logPrim (x₁ + i t)) - Re (logPrim (x₂ + i t))` on `[2, M]`. -/
private theorem abs_re_logPrim_sub_le {M x₁ x₂ : ℝ} (hx₁ : x₁ ∈ Icc 2 M) (hx₂ : x₂ ∈ Icc 2 M)
    (t : ℝ) :
    |(logPrim ((x₁ : ℂ) + t * I)).re - (logPrim ((x₂ : ℂ) + t * I)).re -
        (x₁ - x₂) * Real.log (1 + |t|)| ≤ Real.log M * |x₁ - x₂| := by
  let g : ℝ → ℝ := fun y ↦ (logPrim ((y : ℂ) + t * I)).re - y * Real.log (1 + |t|)
  have hbound := (convex_Icc 2 M).norm_image_sub_le_of_norm_hasDerivWithin_le (f := g)
    (C := Real.log M)
    (fun y hy ↦ (hasDerivAt_re_logPrim_sub (by linarith [hy.1])).hasDerivWithinAt)
    (fun y hy ↦ by
      simpa only [Real.norm_eq_abs] using abs_log_norm_ofReal_add_mul_I_sub_le hy.1 hy.2 t)
    hx₂ hx₁
  have hsub : g x₁ - g x₂ =
      (logPrim ((x₁ : ℂ) + t * I)).re - (logPrim ((x₂ : ℂ) + t * I)).re -
        (x₁ - x₂) * Real.log (1 + |t|) := by dsimp [g]; ring
  simpa only [Real.norm_eq_abs, hsub] using hbound

/-- Conjugation symmetry of `Complex.log` and `logPrim` at `(c : ℂ) - s` when `Re s < c`. -/
private theorem re_log_and_logPrim_ofReal_sub {c : ℝ} {s : ℂ} (hs : s.re < c) :
    (Complex.log ((c : ℂ) - s)).re = Real.log ‖((c - s.re : ℝ) : ℂ) + s.im * I‖ ∧
      (logPrim ((c : ℂ) - s)).re = (logPrim (((c - s.re : ℝ) : ℂ) + s.im * I)).re := by
  set z : ℂ := ((c - s.re : ℝ) : ℂ) + s.im * I
  have hz : z ∈ slitPlane := Or.inl (by simp [z, sub_pos.mpr hs])
  have hconj : (c : ℂ) - s = starRingEnd ℂ z := by
    apply Complex.ext <;> simp [z]
  have hlog : Complex.log ((c : ℂ) - s) = starRingEnd ℂ (Complex.log z) := by
    rw [hconj, Complex.log_conj z (slitPlane_arg_ne_pi hz)]
  have hprim : logPrim ((c : ℂ) - s) = starRingEnd ℂ (logPrim z) := by
    rw [logPrim, hlog, hconj, logPrim, map_sub, map_mul]
  exact ⟨by simp [hlog, Complex.log_re], by simp [hprim]⟩

/-- Algebraic decomposition of `Re (stripLogWeight a b p q s)` minus its linear height model. -/
private theorem re_stripLogWeight_sub_eq {a b : ℝ} (hab : a < b) (p q : ℝ) {s : ℂ}
    (hs : s.re ≤ b) :
    (stripLogWeight a b p q s).re -
        ((1 - (s.re - a) / (b - a)) * p + (s.re - a) / (b - a) * q) * Real.log (1 + |s.im|) =
      ((q - p) / (2 * (b - a))) *
          ((logPrim (((s.re - (a - 2) : ℝ) : ℂ) + s.im * I)).re -
            (logPrim (((b + 2 - s.re : ℝ) : ℂ) + s.im * I)).re -
            (s.re - (a - 2) - (b + 2 - s.re)) * Real.log (1 + |s.im|)) +
        ((p + q) / 4) *
          ((Real.log ‖((s.re - (a - 2) : ℝ) : ℂ) + s.im * I‖ - Real.log (1 + |s.im|)) +
            (Real.log ‖((b + 2 - s.re : ℝ) : ℂ) + s.im * I‖ - Real.log (1 + |s.im|))) := by
  set x₁ : ℝ := s.re - (a - 2)
  set x₂ : ℝ := b + 2 - s.re
  have hs₀ : s - ((a - 2 : ℝ) : ℂ) = (x₁ : ℂ) + s.im * I := by
    apply Complex.ext <;> simp [x₁]
  obtain ⟨hlog₂, hprim₂⟩ :=
    re_log_and_logPrim_ofReal_sub (c := b + 2) (s := s) (by linarith)
  set p₁ : ℝ := (logPrim ((x₁ : ℂ) + s.im * I)).re
  set p₂ : ℝ := (logPrim ((x₂ : ℂ) + s.im * I)).re
  set l₁ : ℝ := Real.log ‖(x₁ : ℂ) + s.im * I‖
  set l₂ : ℝ := Real.log ‖(x₂ : ℂ) + s.im * I‖
  set L : ℝ := Real.log (1 + |s.im|)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hw_re : (stripLogWeight a b p q s).re =
      ((q - p) / (2 * (b - a))) * (p₁ - p₂) + ((p + q) / 4) * (l₁ + l₂) := by
    rw [stripLogWeight]
    simp only [add_re, mul_re, ofReal_re, ofReal_im, sub_re, zero_mul, sub_zero]
    rw [hs₀, hlog₂, hprim₂, Complex.log_re]
  rw [hw_re]
  dsimp only [x₁, x₂]
  field_simp
  ring

/-- Uniform closed-strip comparison between `Re (stripLogWeight a b p q s)` and
`((1 - θ) * p + θ * q) * log (1 + |Im s|)`. -/
private theorem abs_re_stripLogWeight_sub_le {a b : ℝ} (hab : a < b) (p q : ℝ) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    |(stripLogWeight a b p q s).re -
        ((1 - (s.re - a) / (b - a)) * p + (s.re - a) / (b - a) * q) * Real.log (1 + |s.im|)| ≤
      max |p| |q| * Real.log (b - a + 2) := by
  set M : ℝ := b - a + 2
  set x₁ : ℝ := s.re - (a - 2)
  set x₂ : ℝ := b + 2 - s.re
  have hx₁ : x₁ ∈ Icc 2 M := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hx₂ : x₂ ∈ Icc 2 M := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  set E₁ : ℝ := (logPrim ((x₁ : ℂ) + s.im * I)).re - (logPrim ((x₂ : ℂ) + s.im * I)).re -
    (x₁ - x₂) * Real.log (1 + |s.im|)
  set E₂ : ℝ := Real.log ‖(x₁ : ℂ) + s.im * I‖ - Real.log (1 + |s.im|)
  set E₃ : ℝ := Real.log ‖(x₂ : ℂ) + s.im * I‖ - Real.log (1 + |s.im|)
  have hE₁ : |E₁| ≤ Real.log M * (b - a) := by
    have hdiff : |x₁ - x₂| ≤ b - a := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by linarith [hab])
    exact (abs_re_logPrim_sub_le hx₁ hx₂ s.im).trans (by gcongr)
  have hE₂₃ : |E₂ + E₃| ≤ 2 * Real.log M := by
    have h₂ := abs_log_norm_ofReal_add_mul_I_sub_le hx₁.1 hx₁.2 s.im
    have h₃ := abs_log_norm_ofReal_add_mul_I_sub_le hx₂.1 hx₂.2 s.im
    linarith [abs_add_le E₂ E₃]
  have hpq : |q - p| / 2 + |p + q| / 2 ≤ max |p| |q| := by
    rcases abs_cases (q - p) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      rcases abs_cases (p + q) with ⟨_, _⟩ | ⟨_, _⟩ <;>
      linarith [le_abs_self p, neg_abs_le p, le_abs_self q, neg_abs_le q,
        le_max_left |p| |q|, le_max_right |p| |q|]
  have hba_pos : 0 < b - a := sub_pos.mpr hab
  have hba : b - a ≠ 0 := hba_pos.ne'
  rw [re_stripLogWeight_sub_eq hab p q hs.2]
  calc
    |((q - p) / (2 * (b - a))) * E₁ + ((p + q) / 4) * (E₂ + E₃)|
      ≤ |((q - p) / (2 * (b - a))) * E₁| + |((p + q) / 4) * (E₂ + E₃)| := abs_add_le _ _
    _ = (|q - p| / (2 * (b - a))) * |E₁| + (|p + q| / 4) * |E₂ + E₃| := by
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos (mul_pos two_pos hba_pos),
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ (|q - p| / (2 * (b - a))) * (Real.log M * (b - a)) +
        (|p + q| / 4) * (2 * Real.log M) := by gcongr
    _ = (|q - p| / 2 + |p + q| / 2) * Real.log M := by field_simp; ring
    _ ≤ max |p| |q| * Real.log M := by
      gcongr
      exact Real.log_nonneg (by linarith [hab])

/-- Upper bound on `‖cexp (stripLogWeight a b p q s)‖` across the closed strip. -/
private theorem norm_cexp_stripLogWeight_le {a b : ℝ} (hab : a < b) (p q : ℝ) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    ‖cexp (stripLogWeight a b p q s)‖ ≤ (b - a + 2) ^ max |p| |q| *
      (1 + |s.im|) ^ ((1 - (s.re - a) / (b - a)) * p + (s.re - a) / (b - a) * q) := by
  have hre := (abs_le.mp (abs_re_stripLogWeight_sub_le hab p q hs)).2
  have hM : 0 < b - a + 2 := by linarith
  have ht : 0 < 1 + |s.im| := by positivity
  rw [Complex.norm_exp, Real.rpow_def_of_pos hM, Real.rpow_def_of_pos ht, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Upper bound on `‖cexp (-stripLogWeight a b p q s)‖` across the closed strip. -/
private theorem norm_cexp_neg_stripLogWeight_le {a b : ℝ} (hab : a < b) (p q : ℝ) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    ‖cexp (-stripLogWeight a b p q s)‖ ≤ (b - a + 2) ^ max |p| |q| *
      (1 + |s.im|) ^ (-((1 - (s.re - a) / (b - a)) * p + (s.re - a) / (b - a) * q)) := by
  have hre := (abs_le.mp (abs_re_stripLogWeight_sub_le hab p q hs)).1
  have hM : 0 < b - a + 2 := by linarith
  have ht : 0 < 1 + |s.im| := by positivity
  rw [Complex.norm_exp, neg_re, Real.rpow_def_of_pos hM, Real.rpow_def_of_pos ht, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-! ### Growth preservation and `d = 1` core interpolation -/

/-- Coarse exponential bound on `cexp (-stripLogWeight a b p q ·)` along the open strip. -/
private theorem isBigO_cexp_neg_stripLogWeight_exp {a b : ℝ} (hab : a < b) (p q : ℝ) :
    (fun w : ℂ ↦ cexp (-stripLogWeight a b p q w))
      =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun w : ℂ ↦ Real.exp (max |p| |q| * |w.im|) := by
  let M := max |p| |q|
  refine IsBigO.of_bound ((b - a + 2) ^ M) ?_
  filter_upwards [(eventually_mem_principal (re ⁻¹' Ioo a b)).filter_mono inf_le_right] with w hw
  have hw_cc : w.re ∈ Icc a b := ⟨hw.1.le, hw.2.le⟩
  have hθ0 : 0 ≤ (w.re - a) / (b - a) :=
    div_nonneg (sub_nonneg.mpr hw_cc.1) (sub_pos.mpr hab).le
  have hθ1 : (w.re - a) / (b - a) ≤ 1 :=
    (div_le_one (sub_pos.mpr hab)).mpr (sub_le_sub_right hw_cc.2 a)
  have hexp_le : -((1 - (w.re - a) / (b - a)) * p + (w.re - a) / (b - a) * q) ≤ M := by
    have hp : -p ≤ M := (neg_le_abs p).trans (le_max_left _ _)
    have hq : -q ≤ M := (neg_le_abs q).trans (le_max_right _ _)
    nlinarith
  have hlog_le : Real.log (1 + |w.im|) ≤ |w.im| := by
    linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |w.im|)]
  have hlog_nn : 0 ≤ Real.log (1 + |w.im|) :=
    Real.log_nonneg (by linarith [abs_nonneg w.im])
  have hM0 : 0 ≤ M := (abs_nonneg p).trans (le_max_left _ _)
  have hrpow : (1 + |w.im|) ^
      (-((1 - (w.re - a) / (b - a)) * p + (w.re - a) / (b - a) * q)) ≤
      Real.exp (M * |w.im|) := by
    rw [Real.rpow_def_of_pos (by positivity)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  simpa only [Real.norm_eq_abs, Real.abs_exp] using
    (norm_cexp_neg_stripLogWeight_le hab p q hw_cc).trans (by gcongr)

/-- Multiplying by `cexp (-stripLogWeight a b p q ·)` preserves Mathlib's sharp Phragmén–Lindelöf
growth condition on `re ⁻¹' Ioo a b` after slightly increasing the inner exponential rate. -/
private theorem exists_isBigO_cexp_neg_stripLogWeight_smul_exp_exp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b : ℝ}
    (hab : a < b) (p q : ℝ)
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|))) :
    ∃ c' < Real.pi / (b - a), ∃ B',
      (fun w ↦ cexp (-stripLogWeight a b p q w) • f w)
        =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B' * Real.exp (c' * |w.im|)) := by
  obtain ⟨c, hc, B, hO⟩ := hg
  let l := comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)
  let M := max |p| |q|
  let c₀ := max c 0
  have hπ : 0 < Real.pi / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hc₀ : c₀ < Real.pi / (b - a) := max_lt hc hπ
  let c' := (c₀ + Real.pi / (b - a)) / 2
  have hc'_lt : c' < Real.pi / (b - a) := add_div_two_lt_right.mpr hc₀
  have hc₀_lt : c₀ < c' := left_lt_add_div_two.mpr hc₀
  have hc'_pos : 0 < c' := (le_max_right c 0).trans_lt hc₀_lt
  have hcc' : c < c' := (le_max_left c 0).trans_lt hc₀_lt
  have hprod : (fun w ↦ cexp (-stripLogWeight a b p q w) • f w) =O[l]
      fun w ↦ Real.exp (M * |w.im| + B * Real.exp (c * |w.im|)) := by
    simpa only [smul_eq_mul, Real.exp_add] using
      (isBigO_cexp_neg_stripLogWeight_exp hab p q).smul hO
  have htail := (((isLittleO_rpow_exp_pos_mul_atTop 1 hc'_pos).const_mul_left M).add
    ((isLittleO_exp_mul_rpow_of_lt 0 hcc').const_mul_left |B|)).eventuallyLE
  have ht : Tendsto (fun w : ℂ ↦ |w.im|) l atTop := tendsto_comap.mono_left inf_le_left
  refine ⟨c', hc'_lt, 1, hprod.trans (IsBigO.of_norm_eventuallyLE ?_)⟩
  filter_upwards [ht.eventually htail] with w hw_tail
  have hw' : |M * |w.im| + |B| * Real.exp (c * |w.im|)| ≤ Real.exp (c' * |w.im|) := by
    simpa only [Real.rpow_one, Real.rpow_zero, mul_one, Real.norm_eq_abs, Real.abs_exp] using
      hw_tail
  have hle : M * |w.im| + B * Real.exp (c * |w.im|) ≤ 1 * Real.exp (c' * |w.im|) := by
    have hB : B * Real.exp (c * |w.im|) ≤ |B| * Real.exp (c * |w.im|) :=
      mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
    linarith [le_abs_self (M * |w.im| + |B| * Real.exp (c * |w.im|))]
  simpa only [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp] using hle

/-- Cancellation of `(1 + |Im w|) ^ r` against `cexp (-stripLogWeight a b p q w)` when `r` matches
the interpolated exponent at `w`. -/
private theorem norm_cexp_neg_stripLogWeight_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b p q C : ℝ} {w : ℂ} {v : E}
    (hab : a < b) (hw : w.re ∈ Icc a b)
    (hv : ‖v‖ ≤ C * (1 + |w.im|) ^ ((1 - (w.re - a) / (b - a)) * p + (w.re - a) / (b - a) * q)) :
    ‖cexp (-stripLogWeight a b p q w) • v‖ ≤ (b - a + 2) ^ max |p| |q| * C := by
  set r : ℝ := (1 - (w.re - a) / (b - a)) * p + (w.re - a) / (b - a) * q
  let K₀ : ℝ := (b - a + 2) ^ max |p| |q|
  calc
    ‖cexp (-stripLogWeight a b p q w) • v‖
      = ‖cexp (-stripLogWeight a b p q w)‖ * ‖v‖ := norm_smul _ _
    _ ≤ (K₀ * (1 + |w.im|) ^ (-r)) * (C * (1 + |w.im|) ^ r) :=
      mul_le_mul (norm_cexp_neg_stripLogWeight_le hab p q hw) hv (norm_nonneg _) (by positivity)
    _ = K₀ * C * ((1 + |w.im|) ^ (-r) * (1 + |w.im|) ^ r) := by ring
    _ = K₀ * C := by
      rw [← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero, mul_one]

/-- Core `d = 1` polynomial-edge interpolation on a nondegenerate strip `a < b`. -/
private theorem norm_le_one_add_interp_of_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b C₁ C₂ p q : ℝ}
    {z : ℂ} (hab : a < b)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (1 + |w.im|) ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (1 + |w.im|) ^ q)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ (b - a + 2) ^ (2 * max |p| |q|) *
      C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
      (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  have hC₁ : 0 ≤ C₁ := by simpa using (norm_nonneg _).trans (ha a (ofReal_re a))
  have hC₂ : 0 ≤ C₂ := by simpa using (norm_nonneg _).trans (hb b (ofReal_re b))
  let K₀ : ℝ := (b - a + 2) ^ max |p| |q|
  have hK₀_pos : 0 < K₀ := Real.rpow_pos_of_pos (by linarith) _
  let g : ℂ → E := fun w ↦ cexp (-stripLogWeight a b p q w) • f w
  have hdg : DiffContOnCl ℂ g (re ⁻¹' Ioo a b) :=
    (diffContOnCl_cexp_neg_stripLogWeight a b p q).smul hd
  have ha' : ∀ w : ℂ, w.re = a → ‖g w‖ ≤ K₀ * C₁ := fun w hw ↦
    norm_cexp_neg_stripLogWeight_smul_le hab ⟨hw.ge, hw.trans_le hab.le⟩
      (by simpa [hw] using ha w hw)
  have hb' : ∀ w : ℂ, w.re = b → ‖g w‖ ≤ K₀ * C₂ := fun w hw ↦
    norm_cexp_neg_stripLogWeight_smul_le hab ⟨hab.le.trans hw.symm.le, hw.le⟩
      (by simpa [hw, div_self (sub_ne_zero.mpr hab.ne')] using hb w hw)
  obtain ⟨c', hc', B', hg'⟩ := exists_isBigO_cexp_neg_stripLogWeight_smul_exp_exp hab p q hg
  have hstrip : ∀ w : ℂ, w.re ∈ Icc a b → ‖g w‖ ≤ max (K₀ * C₁) (K₀ * C₂) := fun w hw ↦
    _root_.PhragmenLindelof.vertical_strip hdg
      ⟨c', hc', B', by simpa only [Function.comp_def] using hg'⟩
      (fun v hv ↦ (ha' v hv).trans (le_max_left _ _))
      (fun v hv ↦ (hb' v hv).trans (le_max_right _ _)) hw.1 hw.2
  set θ : ℝ := (z.re - a) / (b - a)
  have hinterp : ‖g z‖ ≤ (K₀ * C₁) ^ (1 - θ) * (K₀ * C₂) ^ θ :=
    Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip' hab hz hdg
      ⟨max (K₀ * C₁) (K₀ * C₂), by rintro _ ⟨w, hw, rfl⟩; exact hstrip w hw⟩ ha' hb'
  have hgz : ‖g z‖ ≤ K₀ * C₁ ^ (1 - θ) * C₂ ^ θ := by
    refine hinterp.trans_eq ?_
    rw [Real.mul_rpow hK₀_pos.le hC₁, Real.mul_rpow hK₀_pos.le hC₂]
    calc
      K₀ ^ (1 - θ) * C₁ ^ (1 - θ) * (K₀ ^ θ * C₂ ^ θ)
        = (K₀ ^ (1 - θ) * K₀ ^ θ) * C₁ ^ (1 - θ) * C₂ ^ θ := by ring
      _ = K₀ * C₁ ^ (1 - θ) * C₂ ^ θ := by
        rw [← Real.rpow_add hK₀_pos, sub_add_cancel, Real.rpow_one]
  have hfz : f z = cexp (stripLogWeight a b p q z) • g z := by
    simp only [g, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
  calc
    ‖f z‖ = ‖cexp (stripLogWeight a b p q z)‖ * ‖g z‖ := by rw [hfz, norm_smul]
    _ ≤ (K₀ * (1 + |z.im|) ^ ((1 - θ) * p + θ * q)) * (K₀ * C₁ ^ (1 - θ) * C₂ ^ θ) :=
      mul_le_mul (norm_cexp_stripLogWeight_le hab p q hz) hgz (norm_nonneg _) (by positivity)
    _ = (K₀ * K₀) * C₁ ^ (1 - θ) * C₂ ^ θ *
        (1 + |z.im|) ^ ((1 - θ) * p + θ * q) := by ring
    _ = (b - a + 2) ^ (2 * max |p| |q|) * C₁ ^ (1 - θ) * C₂ ^ θ *
        (1 + |z.im|) ^ ((1 - θ) * p + θ * q) := by
      dsimp [K₀]
      rw [← Real.rpow_add (by linarith : 0 < b - a + 2), two_mul]

/-- Dilation `u ↦ d * u` (`d > 0`) transfers Mathlib's sharp Phragmén–Lindelöf strip growth from
`(a, b)` to `(a / d, b / d)`. -/
private theorem exists_isBigO_comp_ofReal_mul_exp_exp
    {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} {a b d : ℝ} (hab : a < b) (hd_pos : 0 < d)
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|))) :
    ∃ c' < Real.pi / (b / d - a / d), ∃ B',
      (fun u ↦ f ((d : ℂ) * u))
        =O[comap (fun u : ℂ ↦ |u.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (a / d) (b / d))]
        fun u ↦ Real.exp (B' * Real.exp (c' * |u.im|)) := by
  obtain ⟨c, hc, B, hO⟩ := hg
  have hmaps : MapsTo (fun u : ℂ ↦ (d : ℂ) * u)
      (re ⁻¹' Ioo (a / d) (b / d)) (re ⁻¹' Ioo a b) := fun u hu ↦ by
    simpa only [mem_preimage, mem_Ioo, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      lt_div_iff₀' hd_pos, div_lt_iff₀' hd_pos] using hu
  have htend : Tendsto (fun u : ℂ ↦ (d : ℂ) * u)
      (comap (fun u : ℂ ↦ |u.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (a / d) (b / d)))
      (comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)) := by
    refine (tendsto_comap_iff.mpr ?_).inf hmaps.tendsto
    have him : (fun w : ℂ ↦ |w.im|) ∘ (fun u : ℂ ↦ (d : ℂ) * u) = fun u : ℂ ↦ d * |u.im| := by
      ext u; simp [abs_of_pos hd_pos]
    rw [him]
    exact tendsto_comap.const_mul_atTop' hd_pos
  have hc_d : c * d < Real.pi / (b / d - a / d) := by
    calc
      c * d < (Real.pi / (b - a)) * d := mul_lt_mul_of_pos_right hc hd_pos
      _ = Real.pi / (b / d - a / d) := by
        have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
        have hd_ne : d ≠ 0 := hd_pos.ne'
        rw [← sub_div]
        field_simp
  refine ⟨c * d, hc_d, B, (hO.comp_tendsto htend).congr' EventuallyEq.rfl ?_⟩
  exact Eventually.of_forall fun u ↦ by simp [abs_of_pos hd_pos, mul_assoc]

/-! ### Pointwise polynomial-edge interpolation -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Rescaled `0 < d` polynomial-edge interpolation on a nondegenerate strip `a < b`. -/
private theorem norm_le_mul_rpow_interp_of_lt {f : ℂ → E} {a b C₁ C₂ d p q : ℝ} {z : ℂ}
    (hab : a < b) (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (d + |w.im|) ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (d + |w.im|) ^ q)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) *
      C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
      (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  have hC {σ C r : ℝ} (h : ∀ w : ℂ, w.re = σ → ‖f w‖ ≤ C * (d + |w.im|) ^ r) : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hd_pos r)).mp <|
      (norm_nonneg _).trans (by simpa using h σ (ofReal_re σ))
  have hmaps : MapsTo (fun u : ℂ ↦ (d : ℂ) * u)
      (re ⁻¹' Ioo (a / d) (b / d)) (re ⁻¹' Ioo a b) := fun u hu ↦ by
    simpa only [mem_preimage, mem_Ioo, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
      lt_div_iff₀' hd_pos, div_lt_iff₀' hd_pos] using hu
  have hedge {σ C r : ℝ} (h : ∀ w : ℂ, w.re = σ → ‖f w‖ ≤ C * (d + |w.im|) ^ r) :
      ∀ u : ℂ, u.re = σ / d → ‖f ((d : ℂ) * u)‖ ≤ (C * d ^ r) * (1 + |u.im|) ^ r := by
    intro u hu
    have hre : ((d : ℂ) * u).re = σ := by simp [hu, mul_div_cancel₀ _ hd_pos.ne']
    have him : d + |((d : ℂ) * u).im| = d * (1 + |u.im|) := by simp [abs_of_pos hd_pos, mul_add]
    exact (h _ hre).trans_eq (by rw [him, Real.mul_rpow hd_pos.le (by positivity), mul_assoc])
  let u : ℂ := z / (d : ℂ)
  have hu_re : u.re = z.re / d := by simp [u, div_ofReal_re]
  have hu_im : |u.im| = |z.im| / d := by simp [u, div_ofReal_im, abs_div, abs_of_pos hd_pos]
  have hu_cc : u.re ∈ Icc (a / d) (b / d) := by
    rw [hu_re]
    exact ⟨div_le_div_of_nonneg_right hz.1 hd_pos.le, div_le_div_of_nonneg_right hz.2 hd_pos.le⟩
  have hmain := norm_le_one_add_interp_of_lt (div_lt_div_of_pos_right hab hd_pos)
    (hd.comp ((differentiable_id.const_mul (d : ℂ)).diffContOnCl) hmaps)
    (exists_isBigO_comp_ofReal_mul_exp_exp hab hd_pos hg) (hedge ha) (hedge hb) hu_cc
  dsimp only [Function.comp_def] at hmain
  have hdu : (d : ℂ) * u = z := mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr hd_pos.ne')
  have hθ : (u.re - a / d) / (b / d - a / d) = (z.re - a) / (b - a) := by
    rw [hu_re, ← sub_div, ← sub_div, div_div_div_cancel_right₀ hd_pos.ne']
  rw [hdu, hθ, ← sub_div b a d] at hmain
  refine hmain.trans_eq ?_
  set θ : ℝ := (z.re - a) / (b - a)
  rw [Real.mul_rpow (hC ha) (Real.rpow_nonneg hd_pos.le p),
    Real.mul_rpow (hC hb) (Real.rpow_nonneg hd_pos.le q),
    ← Real.rpow_mul hd_pos.le, ← Real.rpow_mul hd_pos.le]
  have hd_comb : d ^ (p * (1 - θ)) * d ^ (q * θ) * (1 + |u.im|) ^ ((1 - θ) * p + θ * q) =
      (d + |z.im|) ^ ((1 - θ) * p + θ * q) := by
    have hexp : p * (1 - θ) + q * θ = (1 - θ) * p + θ * q := by ring
    rw [← Real.rpow_add hd_pos, hexp, ← Real.mul_rpow hd_pos.le (by positivity), hu_im]
    congr 1
    field_simp
  calc
    ((b - a) / d + 2) ^ (2 * max |p| |q|) * (C₁ ^ (1 - θ) * d ^ (p * (1 - θ))) *
        (C₂ ^ θ * d ^ (q * θ)) * (1 + |u.im|) ^ ((1 - θ) * p + θ * q)
      = ((b - a) / d + 2) ^ (2 * max |p| |q|) * C₁ ^ (1 - θ) * C₂ ^ θ *
          (d ^ (p * (1 - θ)) * d ^ (q * θ) * (1 + |u.im|) ^ ((1 - θ) * p + θ * q)) := by ring
    _ = ((b - a) / d + 2) ^ (2 * max |p| |q|) * C₁ ^ (1 - θ) * C₂ ^ θ *
          (d + |z.im|) ^ ((1 - θ) * p + θ * q) := by rw [hd_comb]

/-- **Polynomial-edge Phragmén–Lindelöf interpolation** under Mathlib's sharp sub-double-exponential
strip growth `c < π / (b - a)`. Both the edge constants `C₁, C₂` and the height exponents `p, q`
interpolate across `a ≤ Re z ≤ b`, with a prefactor depending only on `(b - a) / d`, `p`, and
`q`. -/
theorem norm_le_mul_rpow_interp_of_isBigO_exp_exp {f : ℂ → E} {a b C₁ C₂ d p q : ℝ} {z : ℂ}
    (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (d + |w.im|) ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (d + |w.im|) ^ q)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) *
      C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
      (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  rcases lt_or_ge a b with hab | hba
  · exact norm_le_mul_rpow_interp_of_lt hab hd_pos hd hg ha hb hz
  · have hab_eq : a = b := le_antisymm (hz.1.trans hz.2) hba
    have hz_eq : z.re = a := le_antisymm (hz.2.trans_eq hab_eq.symm) hz.1
    have hfz := ha z hz_eq
    have hrhs_nonneg : 0 ≤ C₁ * (d + |z.im|) ^ p := (norm_nonneg _).trans hfz
    have hpref : 1 ≤ (2 : ℝ) ^ (2 * max |p| |q|) :=
      Real.one_le_rpow one_le_two (by positivity)
    subst hab_eq
    simp only [hz_eq, sub_self, zero_div, sub_zero, zero_add, Real.rpow_one, Real.rpow_zero,
      mul_one, one_mul, zero_mul, add_zero]
    rw [mul_assoc]
    exact hfz.trans (le_mul_of_one_le_left hrhs_nonneg hpref)

/-- **Polynomial-edge Phragmén–Lindelöf interpolation** under finite-order growth on the open
vertical strip. -/
theorem norm_le_mul_rpow_interp_of_isBigO_exp_rpow {f : ℂ → E} {a b C₁ C₂ d p q : ℝ} {z : ℂ}
    (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ A B : ℝ,
      f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)] (fun w ↦ Real.exp (B * ‖w‖ ^ A)))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (d + |w.im|) ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (d + |w.im|) ^ q)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) *
      C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
      (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  refine norm_le_mul_rpow_interp_of_isBigO_exp_exp hd_pos hd ?_ ha hb hz
  rcases lt_or_ge a b with hab | hba
  · obtain ⟨A, B, hg⟩ := hg
    have hl : comap (fun w : ℂ ↦ |w.im|) atTop ≤ cobounded ℂ :=
      tendsto_id'.mp (tendsto_norm_atTop_iff_cobounded.mp
        (tendsto_atTop_mono abs_im_le_norm tendsto_comap))
    have hπ : 0 < Real.pi / (b - a) := div_pos Real.pi_pos (sub_pos.mpr hab)
    refine ⟨Real.pi / (b - a) / 2, half_lt_self hπ, 1, ?_⟩
    simpa only [one_mul] using (hg.mono (inf_le_inf_right _ hl)).trans
      (isBigO_exp_rpow_exp_exp_vertical_strip a b A B (half_pos hπ))
  · have hab_eq : a = b := le_antisymm (hz.1.trans hz.2) hba
    exact ⟨-1, by simp [hab_eq], 0, IsBigO.of_bound 0 (by simp [hab_eq])⟩

/-! ### Asymptotic vertical-line bounds along `cocompact ℝ` -/

/-- On a closed boundary or interior vertical line `Re w = σ` of a nondegenerate strip `a < b`, an
asymptotic `O(|t| ^ p)` bound along `cocompact ℝ` combines with continuity from `DiffContOnCl` to
give a global bound in `(d + |Im w|) ^ p`. -/
private theorem exists_vertical_line_bound_of_isBigO_cocompact {f : ℂ → E} {a b σ d p : ℝ}
    (hab : a < b) (hd_pos : 0 < d) (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hσ : σ ∈ Icc a b)
    (hO : (fun t : ℝ ↦ f (σ + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p) :
    ∃ C : ℝ, ∀ w : ℂ, w.re = σ → ‖f w‖ ≤ C * (d + |w.im|) ^ p := by
  have hcont_line : Continuous fun t : ℝ ↦ f (σ + t * I) := by
    have hcl : re ⁻¹' Icc a b ⊆ closure (re ⁻¹' Ioo a b) := by
      rw [closure_preimage_re, closure_Ioo hab.ne]
    exact (hd.continuousOn.mono hcl).comp_continuous (by fun_prop) fun t ↦ by simpa using hσ
  let q : ℝ → ℝ := fun t ↦ ‖f (σ + t * I)‖ / (d + |t|) ^ p
  have hcont_q : Continuous q := by
    refine hcont_line.norm.div ?_ fun t ↦
      (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg hd_pos (abs_nonneg t)) p).ne'
    exact (continuous_const.add continuous_abs).rpow_const fun t ↦
      Or.inl (add_pos_of_pos_of_nonneg hd_pos (abs_nonneg t)).ne'
  have hdom : (fun t : ℝ ↦ |t| ^ p) =O[cocompact ℝ] fun t : ℝ ↦ (d + |t|) ^ p := by
    refine IsBigO.of_bound (max 1 ((2 : ℝ) ^ (-p))) ?_
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop d] with t ht
    rw [Real.norm_eq_abs] at ht
    have ht_pos : 0 < |t| := hd_pos.trans_le ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht_pos p),
      abs_of_pos (Real.rpow_pos_of_pos (by positivity) p)]
    rcases le_total 0 p with hp | hp
    · calc
        |t| ^ p ≤ 1 * (d + |t|) ^ p := by
          rw [one_mul]
          exact Real.rpow_le_rpow ht_pos.le (by linarith) hp
        _ ≤ max 1 ((2 : ℝ) ^ (-p)) * (d + |t|) ^ p := by gcongr; exact le_max_left _ _
    · have h2 : (2 * |t|) ^ p ≤ (d + |t|) ^ p :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hp
      rw [Real.mul_rpow two_pos.le ht_pos.le] at h2
      have hmul : |t| ^ p ≤ (2 : ℝ) ^ (-p) * (d + |t|) ^ p := by
        calc
          |t| ^ p = (2 : ℝ) ^ (-p) * ((2 : ℝ) ^ p * |t| ^ p) := by
            rw [← mul_assoc, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, one_mul]
          _ ≤ (2 : ℝ) ^ (-p) * (d + |t|) ^ p := by gcongr
      exact hmul.trans (by gcongr; exact le_max_right _ _)
  have hqO : q =O[cocompact ℝ] (1 : ℝ → ℝ) :=
    (div_isBoundedUnder_of_isBigO (hO.norm_left.trans hdom)).isBigO_const one_ne_zero
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp (hcont_q.isBounded_range_iff_isBigO.mpr hqO)
  refine ⟨C, fun w hw ↦ ?_⟩
  have hw_eq : (σ : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [hw]
  have hle : q w.im ≤ C :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC _ (mem_range_self w.im))
  simpa only [q, hw_eq] using (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) p)).mp hle

/-- Shared upgrade from `cocompact ℝ` boundary-line bounds to an existential closed-strip bound
given any pointwise polynomial-edge interpolation scheme for `f`. -/
private theorem exists_norm_le_of_cocompact_of_interp {f : ℂ → E} {a b d p q : ℝ}
    (hab : a < b) (hd_pos : 0 < d) (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (ha : (fun t : ℝ ↦ f (a + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p)
    (hb : (fun t : ℝ ↦ f (b + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ q)
    (hinterp : ∀ {C₁ C₂ : ℝ} {z : ℂ},
      (∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (d + |w.im|) ^ p) →
      (∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (d + |w.im|) ^ q) →
      z.re ∈ Icc a b →
      ‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) *
        C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
        (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C *
        (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  obtain ⟨C₁, hC₁⟩ := exists_vertical_line_bound_of_isBigO_cocompact hab hd_pos hd
    (left_mem_Icc.mpr hab.le) ha
  obtain ⟨C₂, hC₂⟩ := exists_vertical_line_bound_of_isBigO_cocompact hab hd_pos hd
    (right_mem_Icc.mpr hab.le) hb
  let M : ℝ := max (max C₁ C₂) 1
  have hM0 : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have ha' : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ M * (d + |w.im|) ^ p := fun w hw ↦
    (hC₁ w hw).trans (by gcongr; exact (le_max_left C₁ C₂).trans (le_max_left _ _))
  have hb' : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ M * (d + |w.im|) ^ q := fun w hw ↦
    (hC₂ w hw).trans (by gcongr; exact (le_max_right C₁ C₂).trans (le_max_left _ _))
  let K : ℝ := ((b - a) / d + 2) ^ (2 * max |p| |q|) * M
  refine ⟨K, mul_pos (Real.rpow_pos_of_pos (by positivity) _) hM0, fun z hz ↦ ?_⟩
  refine (hinterp ha' hb' hz).trans_eq ?_
  set θ : ℝ := (z.re - a) / (b - a)
  have hM_comb : M ^ (1 - θ) * M ^ θ = M := by
    rw [← Real.rpow_add hM0, sub_add_cancel, Real.rpow_one]
  calc
    ((b - a) / d + 2) ^ (2 * max |p| |q|) * M ^ (1 - θ) * M ^ θ *
        (d + |z.im|) ^ ((1 - θ) * p + θ * q)
      = ((b - a) / d + 2) ^ (2 * max |p| |q|) * (M ^ (1 - θ) * M ^ θ) *
          (d + |z.im|) ^ ((1 - θ) * p + θ * q) := by ring
    _ = K * (d + |z.im|) ^ ((1 - θ) * p + θ * q) := by rw [hM_comb]

/-- Asymptotic `O(|t| ^ p)` and `O(|t| ^ q)` bounds along `cocompact ℝ` on the boundary lines of a
strip `a < b` upgrade, under sub-double-exponential growth `c < π / (b - a)`, to a uniform
interpolated bound across the closed strip. -/
theorem exists_norm_le_mul_rpow_interp_of_isBigO_exp_exp {f : ℂ → E} {a b d p q : ℝ}
    (hab : a < b) (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[comap (fun w : ℂ ↦ |w.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        fun w ↦ Real.exp (B * Real.exp (c * |w.im|)))
    (ha : (fun t : ℝ ↦ f (a + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p)
    (hb : (fun t : ℝ ↦ f (b + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C *
        (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) :=
  exists_norm_le_of_cocompact_of_interp hab hd_pos hd ha hb
    (norm_le_mul_rpow_interp_of_isBigO_exp_exp hd_pos hd hg)

/-- Asymptotic `O(|t| ^ p)` and `O(|t| ^ q)` bounds along `cocompact ℝ` on the boundary lines of a
strip `a < b` upgrade, under finite-order growth on the open strip, to a uniform interpolated bound
across the closed strip. -/
theorem exists_norm_le_mul_rpow_interp_of_isBigO_exp_rpow {f : ℂ → E} {a b d p q : ℝ}
    (hab : a < b) (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : ∃ A B : ℝ,
      f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)] (fun w ↦ Real.exp (B * ‖w‖ ^ A)))
    (ha : (fun t : ℝ ↦ f (a + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p)
    (hb : (fun t : ℝ ↦ f (b + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C *
        (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) :=
  exists_norm_le_of_cocompact_of_interp hab hd_pos hd ha hb
    (norm_le_mul_rpow_interp_of_isBigO_exp_rpow hd_pos hd hg)

end NormedSpace

/-! ### Global finite-order specializations -/

/-- **Polynomial-edge Phragmén–Lindelöf interpolation** for complex functions of global finite
order (`TauCeti.IsFiniteOrder`). -/
theorem norm_le_mul_rpow_interp_of_isFiniteOrder {f : ℂ → ℂ} {a b C₁ C₂ d p q : ℝ} {z : ℂ}
    (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : IsFiniteOrder f)
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (d + |w.im|) ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (d + |w.im|) ^ q)
    (hz : z.re ∈ Icc a b) :
    ‖f z‖ ≤ ((b - a) / d + 2) ^ (2 * max |p| |q|) *
      C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
      (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  obtain ⟨A, hA⟩ := isFiniteOrder_def.mp hg
  refine norm_le_mul_rpow_interp_of_isBigO_exp_rpow hd_pos hd ⟨A + 1, 1, ?_⟩ ha hb hz
  simpa only [one_mul] using (hA.isBigO (by linarith : A < A + 1)).mono inf_le_left

/-- Asymptotic `O(|t| ^ p)` and `O(|t| ^ q)` vertical-line bounds along `cocompact ℝ` upgrade, for
a complex function of global finite order, to a uniform interpolated bound on `a ≤ Re z ≤ b`. -/
theorem exists_norm_le_mul_rpow_interp_of_isFiniteOrder {f : ℂ → ℂ} {a b d p q : ℝ}
    (hab : a < b) (hd_pos : 0 < d)
    (hd : DiffContOnCl ℂ f (re ⁻¹' Ioo a b))
    (hg : IsFiniteOrder f)
    (ha : (fun t : ℝ ↦ f (a + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ p)
    (hb : (fun t : ℝ ↦ f (b + t * I)) =O[cocompact ℝ] fun t : ℝ ↦ |t| ^ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ C *
        (d + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) :=
  exists_norm_le_of_cocompact_of_interp hab hd_pos hd ha hb
    (norm_le_mul_rpow_interp_of_isFiniteOrder hd_pos hd hg)

end TauCeti.PhragmenLindelof

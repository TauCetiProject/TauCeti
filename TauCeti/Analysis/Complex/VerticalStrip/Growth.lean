/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.Defs
public import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Polynomial growth on vertical strips

`TauCeti.HasVerticalStripGrowth f` says that on each bounded interval of real parts,
`f` is bounded by a power of `1 + |Im s|` at sufficiently large absolute height.
The height threshold depends on the strip: in particular, poles at nonzero heights
need not obstruct this property. No regularity of `f` is required.

The property is stable under addition, finite sums, multiplication and affine pullbacks
`s ↦ a * s + b` with a real dilation `a : ℝ` (whereas a non-real dilation rotates vertical strips
into horizontal ones, so `exp (-I * s)` fails to have vertical-strip growth). Every function
bounded on each closed vertical strip has it, as does the identity function. Bounds extend to
degenerate strips, and real exponential functions provide nonconstant examples. Any function with
vertical-strip growth decays faster than `exp (r * |Im s|)` for every `r > 0` uniformly on closed
strips (`TauCeti.HasVerticalStripGrowth.tendsto_mul_exp_neg_mul_abs_im`), and this uniform
exponential decay is preserved by Schwarz conjugation
(`TauCeti.tendsto_conj_comp_conj_mul_exp_neg_mul_abs_im`). These facts allow
growth estimates for completed and pole-cleared L-functions to be assembled from their factors.
-/

public section

namespace TauCeti

/-- Polynomial growth at large absolute height on every closed vertical strip.
The positive constant, nonnegative exponent, and nonnegative height threshold may all
depend on the strip. -/
def HasVerticalStripGrowth (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
    ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
      ‖f s‖ ≤ C * (1 + |s.im|) ^ A

/-- Unfolds `HasVerticalStripGrowth` into its quantifier form. -/
theorem hasVerticalStripGrowth_iff {f : ℂ → ℂ} :
    HasVerticalStripGrowth f ↔
      ∀ a b : ℝ, a < b → ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
        ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
          ‖f s‖ ≤ C * (1 + |s.im|) ^ A := Iff.rfl

namespace HasVerticalStripGrowth

variable {f g : ℂ → ℂ}

/-- Growth bounds hold on every closed strip `a ≤ re s ≤ b` with `a ≤ b`,
including a single vertical line. -/
theorem exists_bound (hf : HasVerticalStripGrowth f) {a b : ℝ} (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ T₀ : ℝ, 0 ≤ T₀ ∧
      ∀ s : ℂ, s.re ∈ Set.Icc a b → T₀ ≤ |s.im| →
        ‖f s‖ ≤ C * (1 + |s.im|) ^ A := by
  obtain ⟨C, hC, A, hA, T₀, hT₀, hbound⟩ := hf (a - 1) (b + 1) (by linarith)
  exact ⟨C, hC, A, hA, T₀, hT₀, fun s hs ht ↦
    hbound s ⟨by linarith [hs.1], by linarith [hs.2]⟩ ht⟩

/-- Pointwise domination of norms transfers vertical-strip growth. -/
theorem mono (hg : HasVerticalStripGrowth g) (hfg : ∀ s, ‖f s‖ ≤ ‖g s‖) :
    HasVerticalStripGrowth f := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T₀, hT₀, hbound⟩ := hg a b hab
  exact ⟨C, hC, A, hA, T₀, hT₀, fun s hs ht ↦ (hfg s).trans (hbound s hs ht)⟩

/-- Vertical-strip growth is stable under addition. -/
theorem add (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s + g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hfbound⟩ := hf a b hab
  obtain ⟨D, hD, B, _, U, _, hgbound⟩ := hg a b hab
  refine ⟨C + D, add_pos hC hD, max A B, le_max_of_le_left hA,
    max T U, le_max_of_le_left hT, fun s hs ht ↦ ?_⟩
  have hbase : 1 ≤ 1 + |s.im| := le_add_of_nonneg_right (abs_nonneg _)
  calc
    ‖f s + g s‖ ≤ ‖f s‖ + ‖g s‖ := norm_add_le _ _
    _ ≤ C * (1 + |s.im|) ^ A + D * (1 + |s.im|) ^ B :=
      by
        gcongr
        · exact hfbound s hs ((le_max_left _ _).trans ht)
        · exact hgbound s hs ((le_max_right _ _).trans ht)
    _ ≤ C * (1 + |s.im|) ^ max A B + D * (1 + |s.im|) ^ max A B :=
      by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = (C + D) * (1 + |s.im|) ^ max A B := (add_mul _ _ _).symm

/-- Vertical-strip growth is stable under multiplication. -/
theorem mul (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s * g s) := by
  intro a b hab
  obtain ⟨C, hC, A, hA, T, hT, hfbound⟩ := hf a b hab
  obtain ⟨D, hD, B, hB, U, _, hgbound⟩ := hg a b hab
  refine ⟨C * D, mul_pos hC hD, A + B, add_nonneg hA hB,
    max T U, le_max_of_le_left hT, fun s hs ht ↦ ?_⟩
  calc
    ‖f s * g s‖ = ‖f s‖ * ‖g s‖ := norm_mul _ _
    _ ≤ (C * (1 + |s.im|) ^ A) * (D * (1 + |s.im|) ^ B) :=
      by
        gcongr
        · exact hfbound s hs ((le_max_left _ _).trans ht)
        · exact hgbound s hs ((le_max_right _ _).trans ht)
    _ = (C * D) * (1 + |s.im|) ^ (A + B) := by
      rw [Real.rpow_add (by positivity)]
      ring

/-- Vertical-strip growth is stable under negation. -/
theorem neg (hf : HasVerticalStripGrowth f) :
    HasVerticalStripGrowth (fun s ↦ -f s) :=
  hf.mono fun s ↦ (norm_neg (f s)).le

/-- Vertical-strip growth is stable under subtraction. -/
theorem sub (hf : HasVerticalStripGrowth f) (hg : HasVerticalStripGrowth g) :
    HasVerticalStripGrowth (fun s ↦ f s - g s) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end HasVerticalStripGrowth

/-- Constant functions have vertical-strip growth. -/
@[simp]
theorem hasVerticalStripGrowth_const {c : ℂ} : HasVerticalStripGrowth (fun _ ↦ c) := by
  intro a b _
  exact ⟨‖c‖ + 1, by positivity, 0, le_rfl, 0, le_rfl, fun s _ _ ↦ by simp⟩

namespace HasVerticalStripGrowth

variable {f : ℂ → ℂ}

/-- Multiplication by a constant preserves vertical-strip growth. -/
theorem const_mul (hf : HasVerticalStripGrowth f) (c : ℂ) :
    HasVerticalStripGrowth (fun s ↦ c * f s) :=
  hasVerticalStripGrowth_const.mul hf

/-- Natural powers preserve vertical-strip growth. -/
theorem pow (hf : HasVerticalStripGrowth f) (n : ℕ) :
    HasVerticalStripGrowth (fun s ↦ f s ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (hasVerticalStripGrowth_const (c := 1))
  | succ n ih => simpa only [pow_succ] using ih.mul hf

/-- Finite sums preserve vertical-strip growth. -/
theorem sum {ι : Type*} {t : Finset ι} {F : ι → ℂ → ℂ}
    (h : ∀ i ∈ t, HasVerticalStripGrowth (F i)) :
    HasVerticalStripGrowth (fun s ↦ ∑ i ∈ t, F i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (hasVerticalStripGrowth_const (c := 0))
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

end HasVerticalStripGrowth

/-- A function bounded on every closed vertical strip has vertical-strip growth. -/
theorem hasVerticalStripGrowth_of_forall_bound {f : ℂ → ℂ}
    (h : ∀ a b : ℝ, ∃ M, ∀ s : ℂ, s.re ∈ Set.Icc a b → ‖f s‖ ≤ M) :
    HasVerticalStripGrowth f := by
  intro a b _
  obtain ⟨M, hM⟩ := h a b
  exact ⟨max M 1, lt_max_of_lt_right one_pos, 0, le_rfl, 0, le_rfl, fun s hs _ ↦ by
    simpa only [Real.rpow_zero, mul_one] using (hM s hs).trans (le_max_left _ _)⟩

/-- Pointwise equal functions have the same vertical-strip growth property. -/
theorem hasVerticalStripGrowth_congr {f g : ℂ → ℂ} (h : ∀ s, f s = g s) :
    HasVerticalStripGrowth f ↔ HasVerticalStripGrowth g := by
  rw [funext h]

/-- Real exponentials `exp (r * s)` have vertical-strip growth. -/
theorem hasVerticalStripGrowth_cexp_ofReal_mul {r : ℝ} :
    HasVerticalStripGrowth (fun s : ℂ ↦ Complex.exp (r * s)) := by
  intro a b _
  refine ⟨Real.exp (|r| * max |a| |b|), Real.exp_pos _, 0, le_rfl,
    0, le_rfl, fun s hs _ ↦ ?_⟩
  have hre : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hs.1 hs.2
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Real.rpow_zero, mul_one]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans (by rw [abs_mul]; gcongr)

/-- For a positive integer `n` and real `c`, the powers `n ^ (c s)` have vertical-strip
growth. -/
theorem hasVerticalStripGrowth_natCast_cpow_ofReal_mul {n : ℕ} (hn : n ≠ 0) (c : ℝ) :
    HasVerticalStripGrowth fun s : ℂ ↦ (n : ℂ) ^ ((c : ℂ) * s) :=
  (hasVerticalStripGrowth_congr fun s ↦ (natCast_cpow_ofReal_mul hn c s).symm).mp
    hasVerticalStripGrowth_cexp_ofReal_mul

/-- The identity function has vertical-strip growth. -/
@[to_fun (attr := simp) hasVerticalStripGrowth_fun_id]
theorem hasVerticalStripGrowth_id : HasVerticalStripGrowth id := by
  intro a b _
  refine ⟨max |a| |b| + 1, by positivity, 1, zero_le_one, 0, le_rfl, fun s hs _ ↦ ?_⟩
  have hre : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hs.1 hs.2
  have hnorm : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  dsimp only [id_eq]
  rw [Real.rpow_one]
  nlinarith [abs_nonneg s.im, (abs_nonneg s.re).trans hre]

/-- Pulling back along `s ↦ a * s + b` with a real dilation `a : ℝ` and complex shift `b : ℂ`
preserves vertical-strip growth, including when `a = 0`. -/
theorem HasVerticalStripGrowth.comp_ofReal_mul_add {f : ℂ → ℂ} (hf : HasVerticalStripGrowth f)
    (a : ℝ) (b : ℂ) : HasVerticalStripGrowth (fun s ↦ f ((a : ℂ) * s + b)) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  intro x y _
  let u := min (a * x) (a * y) + b.re
  let v := max (a * x) (a * y) + b.re
  obtain ⟨C, hC, A, hA, T₀, hT₀, hbound⟩ :=
    hf.exists_bound (a := u) (b := v) (add_le_add_left min_le_max _)
  let K := 1 + |a| + |b.im|
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C * K ^ A, by positivity, A, hA, (T₀ + |b.im|) / |a|, by positivity, fun s hs ht ↦ ?_⟩
  have hre : ((a : ℂ) * s + b).re ∈ Set.Icc u v := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Set.mem_Icc, u, v]
    rcases le_total 0 a with ha0 | ha0
    · exact ⟨add_le_add_left ((min_le_left _ _).trans (mul_le_mul_of_nonneg_left hs.1 ha0)) _,
        add_le_add_left ((mul_le_mul_of_nonneg_left hs.2 ha0).trans (le_max_right _ _)) _⟩
    · exact ⟨add_le_add_left ((min_le_right _ _).trans (mul_le_mul_of_nonpos_left hs.2 ha0)) _,
        add_le_add_left ((mul_le_mul_of_nonpos_left hs.1 ha0).trans (le_max_left _ _)) _⟩
  have him_eq : ((a : ℂ) * s + b).im = a * s.im + b.im := by simp
  have him_low : T₀ ≤ |((a : ℂ) * s + b).im| := by
    have hmul : T₀ + |b.im| ≤ |s.im| * |a| := (div_le_iff₀ (abs_pos.mpr ha)).mp ht
    have htri : |a * s.im| ≤ |a * s.im + b.im| + |-b.im| := by
      simpa [sub_eq_add_neg] using abs_add_le (a * s.im + b.im) (-b.im)
    rw [abs_mul, abs_neg] at htri
    rw [him_eq]
    nlinarith [abs_nonneg a, abs_nonneg s.im]
  have him_up : 1 + |((a : ℂ) * s + b).im| ≤ K * (1 + |s.im|) := by
    have htri : |a * s.im + b.im| ≤ |a| * |s.im| + |b.im| :=
      (abs_add_le _ _).trans (by rw [abs_mul])
    rw [him_eq]
    dsimp [K]
    nlinarith [abs_nonneg a, abs_nonneg s.im, abs_nonneg b.im]
  calc ‖f ((a : ℂ) * s + b)‖
      ≤ C * (1 + |((a : ℂ) * s + b).im|) ^ A := hbound _ hre him_low
    _ ≤ C * (K * (1 + |s.im|)) ^ A := by gcongr
    _ = C * K ^ A * (1 + |s.im|) ^ A := by
        rw [Real.mul_rpow hK.le (by positivity), mul_assoc]

/-- A nonzero real dilation with complex shift preserves vertical-strip growth in both
directions. -/
@[simp]
theorem hasVerticalStripGrowth_comp_ofReal_mul_add_iff {f : ℂ → ℂ} {a : ℝ} (ha : a ≠ 0) (b : ℂ) :
    HasVerticalStripGrowth (fun s ↦ f ((a : ℂ) * s + b)) ↔ HasVerticalStripGrowth f := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_ofReal_mul_add a b⟩
  have hi := h.comp_ofReal_mul_add a⁻¹ (-(a⁻¹ : ℂ) * b)
  refine (hasVerticalStripGrowth_congr fun s ↦ ?_).mp hi
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  congr 1
  push_cast
  field_simp
  ring

/-- Non-real dilations need not preserve vertical-strip growth: `exp (-I * s)` grows as `exp t`
along the imaginary axis `s = I * t`. -/
theorem not_hasVerticalStripGrowth_cexp_neg_I_mul :
    ¬ HasVerticalStripGrowth (fun s : ℂ ↦ Complex.exp (-Complex.I * s)) := by
  intro h
  obtain ⟨C, hC, A, _, T₀, _, hbound⟩ := h 0 1 zero_lt_one
  have ho := (((isLittleO_rpow_exp_atTop A).comp_tendsto
    (Filter.tendsto_atTop_add_const_left Filter.atTop 1 Filter.tendsto_id)).const_mul_left
    (2 * Real.exp 1 * C)).eventuallyLE
  obtain ⟨t, ht0, htT, ht⟩ :=
    ((Filter.eventually_gt_atTop (0 : ℝ)).and
      ((Filter.eventually_ge_atTop T₀).and ho)).exists
  have h1t : 0 < 1 + t := by linarith
  have hpos : 0 < C * (1 + t) ^ A := mul_pos hC (Real.rpow_pos_of_pos h1t A)
  simp only [Function.comp_apply, id_eq] at ht
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.exp_add] at ht
  have hlt : C * (1 + t) ^ A < Real.exp t := by
    have he := Real.exp_pos 1
    nlinarith
  have hs := hbound (Complex.I * t) (by simp) (by simpa [abs_of_pos ht0] using htT)
  have hval : ‖Complex.exp (-Complex.I * (Complex.I * (t : ℂ)))‖ = Real.exp t := by
    have hmul : -Complex.I * (Complex.I * (t : ℂ)) = (t : ℂ) := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    rw [hmul, Complex.norm_exp, Complex.ofReal_re]
  rw [hval] at hs
  simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
    Complex.ofReal_re, one_mul, zero_add, abs_of_pos ht0] at hs
  linarith

open Filter in
open scoped Topology in
/-- Any function bounded eventually for large `|Im z|` on `verticalClosedStrip a b` by
`C * (1 + |z.im|) ^ p * exp (c * |z.im|)` with `c < r` satisfies
`f z * exp (-(r * |z.im|)) → 0` as `|z.im| → ∞` uniformly in the strip. -/
theorem tendsto_mul_exp_neg_mul_abs_im_of_norm_le {f : ℂ → ℂ} {a b C p c r : ℝ}
    (hc : c < r)
    (hbound : ∀ᶠ z in comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b),
      ‖f z‖ ≤ C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) :
    Tendsto (fun z => f z * Real.exp (-(r * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) (𝓝 0) := by
  have hd : 0 < r - c := sub_pos.mpr hc
  have hdec : Tendsto (fun t : ℝ => |C| * (t ^ p * Real.exp (-(r - c) * t))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (r - c) hd).const_mul |C|
  have hmaj : Tendsto (fun z : ℂ =>
      |C| * ((1 + |z.im|) ^ p * Real.exp (-(r - c) * (1 + |z.im|))) * Real.exp (r - c))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) (𝓝 0) := by
    simpa [Function.comp_def] using
      (((hdec.comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)).mul_const
        (Real.exp (r - c))).comp (tendsto_comap.mono_left inf_le_left))
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj)
  filter_upwards [hbound] with z hz
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (c * |z.im|) * Real.exp (-(r * |z.im|)) =
      Real.exp (-(r - c) * (1 + |z.im|)) * Real.exp (r - c) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    ‖f z‖ * Real.exp (-(r * |z.im|))
      ≤ (C * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(r * |z.im|)) := by
        gcongr
    _ ≤ (|C| * (1 + |z.im|) ^ p * Real.exp (c * |z.im|)) * Real.exp (-(r * |z.im|)) := by
        gcongr; exact le_abs_self C
    _ = |C| * ((1 + |z.im|) ^ p * Real.exp (-(r - c) * (1 + |z.im|))) *
          Real.exp (r - c) := by
        linear_combination |C| * (1 + |z.im|) ^ p * hexp

open Filter in
open scoped Topology in
/-- Any function with `HasVerticalStripGrowth` decays faster than `exp (r * |Im z|)` for any
positive rate `r > 0`, uniformly on every closed vertical strip `verticalClosedStrip a b`. -/
theorem HasVerticalStripGrowth.tendsto_mul_exp_neg_mul_abs_im {f : ℂ → ℂ}
    (hf : HasVerticalStripGrowth f) {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    Tendsto (fun z : ℂ => f z * Real.exp (-(r * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) (𝓝 0) := by
  rcases le_or_gt a b with hab | hab
  · obtain ⟨C, _, p, _, T₀, _, hbound⟩ := hf.exists_bound hab
    refine tendsto_mul_exp_neg_mul_abs_im_of_norm_le (C := C) (p := p) hr ?_
    rw [eventually_inf_principal, eventually_comap, eventually_atTop]
    refine ⟨T₀, fun t ht z hzt hz => ?_⟩
    simpa only [zero_mul, Real.exp_zero, mul_one] using hbound z hz (hzt ▸ ht)
  · have hemp : Complex.HadamardThreeLines.verticalClosedStrip a b = ∅ := by
      ext z
      simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc,
        Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro h; linarith
    simp [hemp]

open Filter in
open scoped ComplexConjugate Topology in
/-- Conjugating input and output preserves uniform exponential decay along closed vertical strips:
if `f z * exp (-(r * |z.im|)) → 0` as `|z.im| → ∞` uniformly on `verticalClosedStrip a b`, then
the same holds for `fun z => conj (f (conj z))`. -/
theorem tendsto_conj_comp_conj_mul_exp_neg_mul_abs_im {f : ℂ → ℂ} {a b r : ℝ}
    (hgrowth : Tendsto (fun z : ℂ => f z * Real.exp (-(r * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) (𝓝 0)) :
    Tendsto (fun z : ℂ => conj (f (conj z)) * Real.exp (-(r * |z.im|)))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) (𝓝 0) := by
  have hmap : Tendsto (starRingEnd ℂ)
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b))
      (comap (fun z : ℂ => |z.im|) atTop ⊓
        𝓟 (Complex.HadamardThreeLines.verticalClosedStrip a b)) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · rw [tendsto_comap_iff]
      have heq : ((fun z : ℂ => |z.im|) ∘ starRingEnd ℂ) = fun z : ℂ => |z.im| := by
        ext z; simp
      rw [heq]
      exact tendsto_comap.mono_left inf_le_left
    · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
      simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  have h1 := (Complex.continuous_conj.tendsto 0).comp (hgrowth.comp hmap)
  simp only [map_zero] at h1
  refine h1.congr fun z => ?_
  simp only [Function.comp_apply, map_mul, Complex.conj_ofReal, Complex.conj_im, abs_neg]

end TauCeti

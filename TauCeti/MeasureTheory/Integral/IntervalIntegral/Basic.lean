/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.MetricSpace.Equicontinuity
import TauCeti.Analysis.Convex.Segment

/-!
# Additional lemmas for interval integrals

This file records general-purpose lemmas about interval integrals `∫ x in a..b, f x ∂μ` that do
not belong to any particular application.

## Main results

* `TauCeti.intervalIntegral.monotoneOn_primitive_of_nonneg`: the primitive `t ↦ ∫ x in a..t, f x`
  of a function that is nonnegative and interval integrable on `[a, b]` is nondecreasing on
  `[a, b]`.
* `TauCeti.intervalIntegral.eq_of_integral_eq_sub`: if the increments of `F` are the interval
  integrals of a function vanishing outside `[-r, r]` with total integral zero, then `F` is
  constant outside `[-r, r]`.
* `TauCeti.intervalIntegral.integral_re_mul_im_sub_im_mul_re_eq`: a polarization identity
  expressing `∫ (x v - y u)` for `f = x + i y` and `g = u + i v` through the integrals of
  `‖g‖²`, `‖f‖²` and `‖g - i k f‖²`.
* `TauCeti.intervalIntegral.norm_sub_sub_integral_le`: the defect `a₂ - a₁ - ∫ g` from an integral
  equation changes by at most the changes of the endpoint values plus `δ |t₂ - t₁|` when the
  integrand changes by at most `δ`.
* `TauCeti.intervalIntegral.norm_sub_smul_sub_integral_le`: bounding
  `‖(v - u) • c - ∫ t in u..v, g t‖` by `C * |v - u|` when `‖c - g t‖ ≤ C` on `uIoc u v`.
* `TauCeti.intervalIntegral.sum_integral_lineMap_div`: splitting an interval integral over `a..b`
  as the sum of integrals over the `N + 1` uniform affine subintervals.
* `TauCeti.intervalIntegral.norm_riemannSum_sub_integral_le`: quantitative error bound for
  uniform `(N + 1)`-subinterval left-endpoint Riemann sums in terms of subinterval oscillation.
* `TauCeti.intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le`: if `‖F i x‖ ≤ B i` almost
  everywhere on `Ι a b` eventually along `l` and `B i → 0`, then `∫ x in a..b, F i x ∂μ → 0`.
* `TauCeti.intervalIntegral.eq_zero_of_tendsto_average_const`: a constant whose time averages
  `T⁻¹ ∫₀ᵀ c dt` tend to `0` vanishes.
* `TauCeti.intervalIntegral.integral_eq_zero_of_forall_lt`: for `b ≤ a` and a measure vanishing
  on singletons, the integral over `a..b` of a function vanishing on `(-∞, a)` is zero.
* `TauCeti.intervalIntegral_sub_intervalAverage`: subtracting its average over `a..b` from a
  function leaves a function of integral zero over `a..b`.
* `TauCeti.tendsto_intervalIntegral_atTop_atBot`: the accumulated integral of a locally
  integrable function bounded below almost everywhere by a positive constant tends to `+∞` at
  `+∞` and to `-∞` at `-∞`.
* `TauCeti.intervalIntegral.integral_mul_comp_mul_neg`: for an even `f : ℂ → ℂ`, the integral
  `∫ t in a..b, z f(tz)` is odd in `z`; `TauCeti.intervalIntegral.integral_mul_comp_mul_conj`:
  for `f` commuting with conjugation, it commutes with conjugation in `z`.
* `MeasureTheory.IntegrableOn.intervalIntegrable_of_mem_Icc`: a function integrable on `(a, b)`
  for a measure without mass at points is interval integrable between any two points of `[a, b]`.
* `MeasureTheory.IntegrableOn.intervalIntegrable_clm_comp`: for an operator field `P` integrable
  on `[a, b]` and an operator field `N` continuous on `[a, b]`, the composition `u ↦ P u ∘L N u`
  is interval integrable between any two points of `[a, b]`.
* `TauCeti.intervalIntegral.norm_integral_le_setIntegral_norm` and
  `TauCeti.intervalIntegral.norm_integral_le_abs_of_ae_norm_le`: for such a function
  and measure, the integral between two points of `[a, b]` is bounded by the `L¹(a, b)` norm, and
  by the integral of a function dominating `‖f‖` almost everywhere on `(a, b)`.
* `TauCeti.intervalIntegral.abs_integral_norm_le`: for `M` integrable on `[a, b]`, the integral
  of `‖M‖` between two points of `[a, b]` is at most its integral over `[a, b]`.
* `TauCeti.intervalIntegral.abs_integral_norm_le_abs_integral_of_norm_le`: if `‖M‖ ≤ m` almost
  everywhere between `c` and `d`, then `|∫ r in c..d, ‖M r‖| ≤ |∫ r in c..d, m r|`.
* `MeasureTheory.IntegrableOn.setIntegral_Ioo_eq_sub`: for `f` integrable on `(a, b)`, the
  integral over a subinterval `(s, t)` is a difference of primitives based at any `c ∈ [a, b]`.
* `MeasureTheory.Integrable.norm_intervalIntegral_le_integral_norm`: an interval integral of an
  integrable function is bounded in norm by the integral of its norm over the whole space.
* `MeasureTheory.setIntegral_Ioc_comp_add_left`: translating a set integral over `(a, b]` to one
  over `(d + a, d + b]`.
* `MeasureTheory.IntegrableOn.comp_add_right_Icc`: a function integrable on `[a, b]` has its
  translate `u ↦ f (u + c)` integrable on `[a - c, b - c]`.
* `intervalIntegral.integral_of_not_completeSpace`: in an incomplete codomain every interval
  integral is `0`.
* `ContinuousLinearEquiv.intervalIntegral_comp_comm`: a continuous linear equivalence commutes
  with interval integrals, with no integrability assumption.
* `PiLp.ofLp_intervalIntegral`: `WithLp.ofLp` commutes with interval integrals of `PiLp`-valued
  functions, with no integrability assumption.
* `MeasureTheory.LocallyIntegrableOn.intervalIntegrable_comp_max`: if `f` is locally integrable
  on `[c, ∞)`, then its constant extension `x ↦ f (max x c)` is interval integrable on every
  interval.
* `TauCeti.intervalIntegral.tendstoUniformlyOn_riemannSum` and
  `TauCeti.intervalIntegral.tendsto_riemannSum`: for a Banach-space-valued function jointly
  continuous on `uIcc a b ×ˢ K` (with `K` compact), or continuous on `uIcc a b`, uniform
  left-endpoint Riemann sums converge uniformly on `K`, respectively pointwise, to
  `∫ t in a..b, f t`.
-/

public section

open MeasureTheory Set

namespace TauCeti

namespace intervalIntegral

/-- Interval integrals add over a `Fin`-indexed partition, which need not be increasing. -/
theorem sum_integral_adjacent_intervals_fin {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} {f : ℝ → E} {n : ℕ} (τ : Fin (n + 1) → ℝ)
    (hint : ∀ i : Fin n, IntervalIntegrable f μ (τ i.castSucc) (τ i.succ)) :
    ∑ i : Fin n, ∫ t in τ i.castSucc..τ i.succ, f t ∂μ =
      ∫ t in τ 0..τ (Fin.last n), f t ∂μ := by
  let a (k : ℕ) := τ (Fin.ofNat (n + 1) k)
  have ha (i : Fin (n + 1)) : a i = τ i := by
    simp [a, Fin.ofNat_eq_cast]
  have hint' (k : ℕ) (hk : k < n) : IntervalIntegrable f μ (a k) (a (k + 1)) := by
    simpa only [← ha (⟨k, hk⟩ : Fin n).castSucc, ← ha (⟨k, hk⟩ : Fin n).succ,
      Fin.val_castSucc, Fin.val_succ, Fin.val_mk] using hint ⟨k, hk⟩
  have h0 : a 0 = τ 0 := by simpa only [Fin.val_zero] using ha 0
  have hn : a n = τ (Fin.last n) := by simpa only [Fin.val_last] using ha (Fin.last n)
  have hsum := _root_.intervalIntegral.sum_integral_adjacent_intervals hint'
  rw [← Fin.sum_univ_eq_sum_range, h0, hn] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← ha i.castSucc, ← ha i.succ, Fin.val_castSucc, Fin.val_succ]

/-- The primitive `t ↦ ∫ x in a..t, f x ∂μ` of a function that is almost everywhere nonnegative and
interval integrable on `[a, b]` is nondecreasing on `[a, b]`. -/
theorem monotoneOn_primitive_of_nonneg {f : ℝ → ℝ} {μ : Measure ℝ} {a b : ℝ}
    (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f) (hfi : IntervalIntegrable f μ a b) :
    MonotoneOn (fun t ↦ ∫ x in a..t, f x ∂μ) (Icc a b) := fun _ hs _ ht hst ↦
  _root_.intervalIntegral.integral_mono_interval le_rfl hs.1 hst
    (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl) hf)
    (hfi.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le ht.1 ht.2)))

/-- If the increments of `F` are the interval integrals of a function `f` that vanishes outside
`[-r, r]` and has total integral zero, then `F` is constant outside `[-r, r]`. -/
theorem eq_of_integral_eq_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f F : ℝ → E} {r : ℝ} (hF : ∀ a b, ∫ t in a..b, f t = F b - F a)
    (hf : ∀ t, r < |t| → f t = 0) (h : ∫ t, f t = 0) {x y : ℝ} (hx : r < |x|) (hy : r < |y|) :
    F x = F y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  have hxy' := hF x y
  rw [_root_.intervalIntegral.integral_of_le hxy] at hxy'
  refine (sub_eq_zero.mp (hxy'.symm.trans ?_)).symm
  rcases lt_abs.mp hx with hx | hx <;> rcases lt_abs.mp hy with hy | hy
  · -- Both points lie to the right of `[-r, r]`, so `f` vanishes between them.
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ hf t (lt_abs.mpr (.inl ?_))
    linarith [ht.1]
  · -- `r < x ≤ y < -r` forces `r < 0`, so `f` vanishes everywhere.
    exact setIntegral_eq_zero_of_forall_eq_zero fun t _ ↦ hf t (by linarith [abs_nonneg t])
  · -- The interval `(x, y]` contains `[-r, r]`, so the integral over it is the total integral.
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ hf t ?_, h]
    rw [mem_Ioc, not_and_or, not_lt, not_le] at ht
    exact lt_abs.mpr (ht.elim (fun ht ↦ .inr (by linarith)) fun ht ↦ .inl (by linarith))
  · -- Both points lie to the left of `[-r, r]`, so `f` vanishes between them.
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ hf t (lt_abs.mpr (.inr ?_))
    linarith [ht.2]

/-- A polarization identity for complex functions `f = x + i y` and `g = u + i v`, square
integrable on `uIoc a b`: for real `k ≠ 0`,
`∫ₐᵇ (x v - y u) = (∫ₐᵇ ‖g‖² + k² ∫ₐᵇ ‖f‖² - ∫ₐᵇ ‖g - i k f‖²) / (2k)`.
For a curve `f` with velocity `g`, the left side is twice the signed area of `f`. -/
theorem integral_re_mul_im_sub_im_mul_re_eq {a b : ℝ} {k : ℝ} (hk : k ≠ 0)
    {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (uIoc a b)))
    (hg : MemLp g 2 (volume.restrict (uIoc a b))) :
    (∫ t in a..b, ((f t).re * (g t).im - (f t).im * (g t).re)) =
      ((∫ t in a..b, ‖g t‖ ^ 2) + k ^ 2 * (∫ t in a..b, ‖f t‖ ^ 2) -
        ∫ t in a..b, ‖g t - (k * Complex.I) * f t‖ ^ 2) / (2 * k) := by
  have hint {h : ℝ → ℂ} (hh : MemLp h 2 (volume.restrict (uIoc a b))) :
      IntervalIntegrable (fun t ↦ ‖h t‖ ^ 2) volume a b :=
    intervalIntegrable_iff.2 (hh.integrable_norm_pow two_ne_zero)
  have hG := hint hg
  have hF := hint hf
  have hH := hint (h := fun t ↦ g t - (k * Complex.I) * f t) (hg.sub (hf.const_mul _))
  -- Pointwise, `‖g - i k f‖² = ‖g‖² + k² ‖f‖² - 2 k (x v - y u)`.
  have hpt (t : ℝ) : (f t).re * (g t).im - (f t).im * (g t).re =
      (‖g t‖ ^ 2 + k ^ 2 * ‖f t‖ ^ 2 - ‖g t - (k * Complex.I) * f t‖ ^ 2) / (2 * k) := by
    field_simp
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  simp_rw [hpt]
  rw [_root_.intervalIntegral.integral_div,
    _root_.intervalIntegral.integral_sub (hG.add (hF.const_mul _)) hH,
    _root_.intervalIntegral.integral_add hG (hF.const_mul _),
    _root_.intervalIntegral.integral_const_mul]

/-- The defect `a₂ - a₁ - ∫ g` from an integral equation over `[t₁, t₂]` differs from the defect
`b₂ - b₁ - ∫ g'` by at most `‖a₁ - b₁‖ + ‖a₂ - b₂‖ + δ |t₂ - t₁|` when `‖g - g'‖ ≤ δ` on the
interval. -/
theorem norm_sub_sub_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a₁ a₂ b₁ b₂ : E} {g g' : ℝ → E} {t₁ t₂ δ : ℝ} (hg : IntervalIntegrable g volume t₁ t₂)
    (hg' : IntervalIntegrable g' volume t₁ t₂) (hgg : ∀ t ∈ uIoc t₁ t₂, ‖g t - g' t‖ ≤ δ) :
    ‖a₂ - a₁ - ∫ t in t₁..t₂, g t‖ ≤
      ‖b₂ - b₁ - ∫ t in t₁..t₂, g' t‖ + ‖a₁ - b₁‖ + ‖a₂ - b₂‖ + δ * |t₂ - t₁| := by
  have hI : ‖∫ t in t₁..t₂, (g t - g' t)‖ ≤ δ * |t₂ - t₁| :=
    _root_.intervalIntegral.norm_integral_le_of_norm_le_const hgg
  have hsplit : a₂ - a₁ - ∫ t in t₁..t₂, g t = (b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂) -
      (a₁ - b₁) - ∫ t in t₁..t₂, (g t - g' t) := by
    rw [_root_.intervalIntegral.integral_sub hg hg']
    abel
  rw [hsplit]
  linarith [norm_sub_le ((b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂) - (a₁ - b₁))
      (∫ t in t₁..t₂, (g t - g' t)),
    norm_sub_le ((b₂ - b₁ - ∫ t in t₁..t₂, g' t) + (a₂ - b₂)) (a₁ - b₁),
    norm_add_le (b₂ - b₁ - ∫ t in t₁..t₂, g' t) (a₂ - b₂)]

/-- For an even function `f : ℂ → ℂ`, the integral `∫ t in a..b, z f(tz)` is odd in `z`:
`∫ t in a..b, (−z) f(t(−z)) = −∫ t in a..b, z f(tz)`. -/
theorem integral_mul_comp_mul_neg {f : ℂ → ℂ} (hf : ∀ u, f (-u) = f u) (a b : ℝ) (z : ℂ) :
    ∫ t : ℝ in a..b, -z * f (t * -z) = -∫ t : ℝ in a..b, z * f (t * z) := by
  simp only [mul_neg, hf, neg_mul, _root_.intervalIntegral.integral_neg]

open scoped ComplexConjugate in
/-- For a function `f : ℂ → ℂ` commuting with conjugation, the integral `∫ t in a..b, z f(tz)`
commutes with conjugation in `z`:
`∫ t in a..b, conj z f(t conj z) = conj (∫ t in a..b, z f(tz))`. -/
theorem integral_mul_comp_mul_conj {f : ℂ → ℂ} (hf : ∀ u, f (conj u) = conj (f u)) (a b : ℝ)
    (z : ℂ) :
    ∫ t : ℝ in a..b, conj z * f (t * conj z) =
      conj (∫ t : ℝ in a..b, z * f (t * z)) := by
  rw [← _root_.intervalIntegral.intervalIntegral_conj]
  congr 1
  funext t
  rw [map_mul, ← hf, map_mul, Complex.conj_ofReal]

/-- Approximating an interval integral by a constant value `c` incurs error at most `C * |v - u|`
whenever `‖c - g t‖ ≤ C` on `uIoc u v`. -/
theorem norm_sub_smul_sub_integral_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : ℝ → E} {c : E} {u v C : ℝ}
    (hg : IntervalIntegrable g volume u v) (hC : ∀ t ∈ uIoc u v, ‖c - g t‖ ≤ C) :
    ‖(v - u) • c - ∫ t in u..v, g t‖ ≤ C * |v - u| := by
  rw [← _root_.intervalIntegral.integral_const,
    ← _root_.intervalIntegral.integral_sub intervalIntegrable_const hg]
  exact _root_.intervalIntegral.norm_integral_le_of_norm_le_const hC

/-- An interval integral over `a..b` splits as the sum of the integrals over the `N + 1` uniform
subintervals determined by `AffineMap.lineMap a b (k / (N + 1))`. -/
theorem sum_integral_lineMap_div {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {g : ℝ → E} {a b : ℝ} (hg : IntervalIntegrable g μ a b) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
      ∫ t in AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))..
        AffineMap.lineMap a b (((k + 1 : ℕ) : ℝ) / (N + 1 : ℝ)), g t ∂μ =
      ∫ t in a..b, g t ∂μ := by
  have hint : ∀ k < N + 1, IntervalIntegrable g μ
      (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)))
      (AffineMap.lineMap a b (((k + 1 : ℕ) : ℝ) / (N + 1 : ℝ))) := fun k hk ↦
    hg.mono_set (uIcc_subset_uIcc
      (TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg k) (by exact_mod_cast hk.le))
      (TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg _) (by exact_mod_cast hk)))
  have htop : AffineMap.lineMap a b (((N + 1 : ℕ) : ℝ) / (N + 1 : ℝ)) = b := by
    simp [div_self (Nat.cast_add_one_pos (α := ℝ) N).ne']
  simpa only [Nat.cast_zero, zero_div, AffineMap.lineMap_apply_zero, htop] using
    _root_.intervalIntegral.sum_integral_adjacent_intervals hint

/-- **Quantitative error bound for uniform left-endpoint Riemann sums.** If an interval-integrable
function `g : ℝ → E` into a Banach space varies by at most `M` from its left endpoint on each of
the `N + 1` uniform subintervals of `a..b`, then the uniform left-endpoint Riemann sum approximates
`∫ t in a..b, g t` within `M * |b - a|`. -/
theorem norm_riemannSum_sub_integral_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {g : ℝ → E} {a b M : ℝ} (hg : IntervalIntegrable g volume a b) (N : ℕ)
    (hM : ∀ k < N + 1, ∀ t ∈ uIoc (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)))
      (AffineMap.lineMap a b (((k + 1 : ℕ) : ℝ) / (N + 1 : ℝ))),
      ‖g (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))) - g t‖ ≤ M) :
    ‖((b - a) / (N + 1 : ℝ)) •
      ∑ k ∈ Finset.range (N + 1), g (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))) -
      ∫ t in a..b, g t‖ ≤ M * |b - a| := by
  let τ : ℕ → ℝ := fun k ↦ AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))
  have hN1 : (0 : ℝ) < N + 1 := Nat.cast_add_one_pos N
  have hτ_diff (k : ℕ) : τ (k + 1) - τ k = (b - a) / (N + 1 : ℝ) := by
    simp only [τ, AffineMap.lineMap_apply_module, Nat.cast_add, Nat.cast_one, smul_eq_mul]; ring
  rw [← sum_integral_lineMap_div hg N, Finset.smul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      ‖((b - a) / (N + 1 : ℝ)) • g (τ k) - ∫ t in τ k..τ (k + 1), g t‖ ≤
        M * (|b - a| / (N + 1 : ℝ)) := fun k hk ↦ by
    have hk' : k < N + 1 := Finset.mem_range.mp hk
    have hsub : uIcc (τ k) (τ (k + 1)) ⊆ uIcc a b := uIcc_subset_uIcc
      (TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg k) (by exact_mod_cast hk'.le))
      (TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg _) (by exact_mod_cast hk'))
    rw [← hτ_diff k]
    exact (norm_sub_smul_sub_integral_le (hg.mono_set hsub) (hM k hk')).trans_eq
      (by rw [hτ_diff, abs_div, abs_of_pos hN1])
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add_one]
  field_simp [hN1.ne']

/-- **Parametric uniform convergence of uniform left-endpoint Riemann sums.** If `f : ℝ → α → E`
is jointly continuous on `uIcc a b ×ˢ K` with `K` compact in `α` and `E` a Banach space, then the
uniform `(N + 1)`-subinterval left-endpoint Riemann sums converge to `x ↦ ∫ t in a..b, f t x`
uniformly on `K` as `N → ∞`, with no order assumption on `a` and `b`. -/
theorem tendstoUniformlyOn_riemannSum {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → α → E} {a b : ℝ} {K : Set α} (hK : IsCompact K)
    (hf : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ K)) :
    TendstoUniformlyOn
      (fun (N : ℕ) (x : α) ↦ ((b - a) / (N + 1 : ℝ)) •
        ∑ k ∈ Finset.range (N + 1), f (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))) x)
      (fun x : α ↦ ∫ t in a..b, f t x) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases eq_or_ne a b with rfl | hab
  · exact Filter.Eventually.of_forall fun _ _ _ ↦ by simp [hε]
  have hba : 0 < |b - a| := abs_pos.mpr (sub_ne_zero.mpr hab.symm)
  -- Compactness of `K` gives equicontinuity of `t ↦ f t x` on `uIcc a b`, hence uniform
  -- equicontinuity by compactness of `uIcc a b`.
  have : CompactSpace (uIcc a b) := isCompact_iff_compactSpace.mp isCompact_uIcc
  have hEq : Equicontinuous fun (x : K) (t : uIcc a b) ↦ f t x := fun t ↦
    Metric.equicontinuousAt_iff_right.mpr fun η hη ↦ by
      obtain ⟨v, hv, hvf⟩ := hK.mem_uniformity_of_prod hf t.property (Metric.dist_mem_uniformity hη)
      filter_upwards [nhdsWithin_eq_map_subtypeVal t.property ▸ hv] with s hs x
      exact dist_comm (f s x) (f t x) ▸ hvf s hs x x.property
  obtain ⟨δ, hδ, hδF⟩ := Metric.uniformEquicontinuous_iff.mp
    (CompactSpace.uniformEquicontinuous_of_equicontinuous hEq) (ε / (2 * |b - a|)) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (|b - a| / δ)
  refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN x hx ↦ ?_⟩
  have hN1 : (0 : ℝ) < N + 1 := Nat.cast_add_one_pos N
  have hstep_lt : |b - a| / (N + 1 : ℝ) < δ := (div_lt_iff₀ hN1).mpr <| by
    have hlt : (N₀ : ℝ) < N + 1 := by exact_mod_cast Nat.lt_succ_of_le hN
    nlinarith [(div_lt_iff₀ hδ).mp hN₀, hlt]
  have hfx : ContinuousOn (fun t ↦ f t x) (uIcc a b) :=
    hf.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht ↦ ⟨ht, hx⟩
  rw [dist_comm, dist_eq_norm]
  refine (norm_riemannSum_sub_integral_le (M := ε / (2 * |b - a|)) hfx.intervalIntegrable N
    fun k hk t ht ↦ ?_).trans_lt ?_
  · have hk_mem : AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)) ∈ uIcc a b :=
      TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg k) (by exact_mod_cast hk.le)
    have hsub : uIcc (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)))
        (AffineMap.lineMap a b (((k + 1 : ℕ) : ℝ) / (N + 1 : ℝ))) ⊆ uIcc a b :=
      uIcc_subset_uIcc hk_mem
        (TauCeti.lineMap_div_mem_uIcc (Nat.cast_nonneg _) (by exact_mod_cast hk))
    have hdiff : AffineMap.lineMap a b (((k + 1 : ℕ) : ℝ) / (N + 1 : ℝ)) -
        AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)) = (b - a) / (N + 1 : ℝ) := by
      simp only [AffineMap.lineMap_apply_module, Nat.cast_add, Nat.cast_one, smul_eq_mul]; ring
    have htdist : dist (⟨AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ)), hk_mem⟩ : uIcc a b)
        ⟨t, hsub (uIoc_subset_uIcc ht)⟩ < δ := by
      refine ((Real.dist_le_of_mem_uIcc left_mem_uIcc (uIoc_subset_uIcc ht)).trans_eq ?_).trans_lt
        hstep_lt
      rw [Real.dist_eq, abs_sub_comm, hdiff, abs_div, abs_of_pos hN1]
    rw [← dist_eq_norm]
    exact (hδF _ _ htdist ⟨x, hx⟩).le
  · have hhalf : ε / (2 * |b - a|) * |b - a| = ε / 2 := by field_simp [hba.ne']
    linarith

/-- For `f : ℝ → α → E` jointly continuous on `[0, 1] ×ˢ K` with `K` compact and `E` a Banach
space, parametric uniform left-endpoint Riemann sums on `[0, 1]` converge uniformly on `K`. -/
theorem tendstoUniformlyOn_riemannSum_zero_one {α E : Type*} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → α → E} {K : Set α}
    (hK : IsCompact K) (hf : ContinuousOn (Function.uncurry f) (Icc 0 1 ×ˢ K)) :
    TendstoUniformlyOn
      (fun (N : ℕ) (x : α) ↦ (N + 1 : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (N + 1), f ((k : ℝ) / (N + 1 : ℝ)) x)
      (fun x : α ↦ ∫ t in (0 : ℝ)..1, f t x) Filter.atTop K := by
  have h := tendstoUniformlyOn_riemannSum (a := 0) (b := 1) hK (by rwa [uIcc_of_le zero_le_one])
  simpa [one_div, AffineMap.lineMap_apply_module] using h

/-- **Convergence of uniform left-endpoint Riemann sums.** For a Banach-space-valued function `f`
continuous on `uIcc a b`, the uniform `(N + 1)`-subinterval left-endpoint Riemann sums converge to
`∫ t in a..b, f t` as `N → ∞`, with no order assumption on `a` and `b`. -/
theorem tendsto_riemannSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} {a b : ℝ} (hf : ContinuousOn f (uIcc a b)) :
    Filter.Tendsto
      (fun N : ℕ ↦ ((b - a) / (N + 1 : ℝ)) •
        ∑ k ∈ Finset.range (N + 1), f (AffineMap.lineMap a b ((k : ℝ) / (N + 1 : ℝ))))
      Filter.atTop (nhds (∫ t in a..b, f t)) :=
  (tendstoUniformlyOn_riemannSum (α := PUnit.{1}) (f := fun t _ ↦ f t) isCompact_univ
    (hf.comp continuous_fst.continuousOn fun _ hp ↦ hp.1)).tendsto_at (mem_univ PUnit.unit)

/-- For a Banach-space-valued function `f` continuous on `[0, 1]`, uniform left-endpoint Riemann
sums on `[0, 1]` converge to `∫ t in 0..1, f t`. -/
theorem tendsto_riemannSum_zero_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : ContinuousOn f (Icc 0 1)) :
    Filter.Tendsto
      (fun N : ℕ ↦ (N + 1 : ℝ)⁻¹ • ∑ k ∈ Finset.range (N + 1), f ((k : ℝ) / (N + 1 : ℝ)))
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, f t)) := by
  have h := tendsto_riemannSum (a := 0) (b := 1) (by rwa [uIcc_of_le zero_le_one])
  simpa [one_div, AffineMap.lineMap_apply_module] using h

open Filter Topology Interval in
/-- If `‖F i x‖ ≤ B i` almost everywhere on `Ι a b` eventually along `l` and `B i → 0`, then for
any locally finite measure `μ` the interval integrals `∫ x in a..b, F i x ∂μ` tend to `0` along
`l`. -/
theorem tendsto_integral_nhds_zero_of_ae_norm_le {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {l : Filter ι} {F : ι → ℝ → E}
    {B : ι → ℝ} {a b : ℝ} (hB : Tendsto B l (𝓝 0))
    (hF : ∀ᶠ i in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ‖F i x‖ ≤ B i) :
    Tendsto (fun i ↦ ∫ x in a..b, F i x ∂μ) l (𝓝 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hF.mono fun i hi ↦ ?_) (by simpa using hB.mul_const (μ.real (Ι a b))))
  rw [_root_.intervalIntegral.norm_integral_eq_norm_integral_uIoc]
  exact norm_setIntegral_le_of_norm_le_const_ae' measure_Ioc_lt_top hi

open Filter Topology in
/-- If the time averages `T⁻¹ ∫₀ᵀ c dt` of a constant `c` tend to `0` as `T → ∞`, then `c = 0`:
the averages are eventually equal to `c`. -/
theorem eq_zero_of_tendsto_average_const {c : ℝ}
    (h : Tendsto (fun T : ℝ ↦ T⁻¹ * ∫ _ in (0 : ℝ)..T, c) atTop (𝓝 0)) : c = 0 := by
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [_root_.intervalIntegral.integral_const, sub_zero, smul_eq_mul, inv_mul_cancel_left₀ hT.ne']

/-- For `b ≤ a` and a measure vanishing on singletons, the integral over `a..b` of a function
vanishing on `(-∞, a)` is zero. -/
theorem integral_eq_zero_of_forall_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} [NullSingletonClass μ] {F : ℝ → E} {a b : ℝ} (hF : ∀ t < a, F t = 0)
    (hb : b ≤ a) :
    ∫ t in a..b, F t ∂μ = 0 := by
  refine _root_.intervalIntegral.integral_zero_ae ?_
  filter_upwards [Measure.ae_ne μ a] with t hta ht
  rw [uIoc_of_ge hb] at ht
  exact hF t (lt_of_le_of_ne ht.2 hta)

end intervalIntegral

/-- A function vanishing on `(-∞, a]` and on a ball around `a` has zero integral on `a..t` for
every `t < a + ε`, where `ε` is the radius of that ball. -/
lemma integral_eq_zero_of_lt_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure ℝ} {a ε t : ℝ} {φ : ℝ → E} (hφ0 : ∀ x, x ≤ a → φ x = 0)
    (hφa : ∀ ⦃y⦄, dist y a < ε → φ y = 0) (ht : t < a + ε) : ∫ s in a..t, φ s ∂μ = 0 := by
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : E)) fun s hs ↦ ?_).trans
    intervalIntegral.integral_zero
  rcases le_or_gt s a with hsa | hsa
  · exact hφ0 s hsa
  · refine hφa ?_
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsa)]
    linarith [(le_max_iff.1 hs.2).resolve_left hsa.not_ge]

/-- The primitive of a step velocity corrected by its average defect reaches the prescribed
endpoint. -/
theorem add_integral_add_inv_smul_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {a b : ℝ} (hab : a ≠ b) {s : ℝ → E} (hsi : IntervalIntegrable s volume a b)
    (x y : E) :
    x + ∫ t in a..b, (s t + (b - a)⁻¹ • (y - x - ∫ t in a..b, s t)) = y := by
  rw [_root_.intervalIntegral.integral_add hsi (intervalIntegrable_const),
    _root_.intervalIntegral.integral_const, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm),
    one_smul]
  abel

/-- The `L¹` norm over `(a, b]` of the constant `(b - a)⁻¹ • D` is `‖D‖`. -/
theorem setIntegral_norm_inv_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b) (D : E) :
    (∫ _ in Ioc a b, ‖(b - a)⁻¹ • D‖) = ‖D‖ := by
  rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (sub_pos.mpr hab), smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_mul]

/-- Subtracting its average over `a..b` from a function leaves a function of integral zero over
`a..b`. -/
theorem intervalIntegral_sub_intervalAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (a b : ℝ) :
    ∫ t in a..b, (f t - ⨍ t in a..b, f t) = 0 := by
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  rw [_root_.intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_sub_average, smul_zero]

open Filter in
/-- The accumulated integral `t ↦ ∫ r in a..t, w r` of a locally integrable function bounded below
almost everywhere by a positive constant tends to `+∞` at `+∞` and to `-∞` at `-∞`. -/
theorem tendsto_intervalIntegral_atTop_atBot {w : ℝ → ℝ}
    {a : ℝ} (hw : ∀ t, IntervalIntegrable w volume a t) {m : ℝ} (hm : 0 < m)
    (hwm : ∀ᵐ t ∂volume, m ≤ w t) :
    Tendsto (fun t ↦ ∫ r in a..t, w r) atTop atTop ∧
      Tendsto (fun t ↦ ∫ r in a..t, w r) atBot atBot := by
  -- Compare with the integral `(t - a) * m` of the constant lower bound.
  refine ⟨tendsto_atTop_mono' _ ?_
      ((tendsto_atTop_add_const_right _ (-a) tendsto_id).atTop_mul_const hm),
    tendsto_atBot_mono' _ ?_
      ((tendsto_atBot_add_const_right _ (-a) tendsto_id).atBot_mul_const hm)⟩
  · filter_upwards [eventually_ge_atTop a] with t ht
    simpa [sub_eq_add_neg] using
      intervalIntegral.integral_mono_ae ht intervalIntegrable_const (hw t) hwm
  · filter_upwards [eventually_le_atBot a] with t ht
    rw [intervalIntegral.integral_symm t, neg_le]
    simpa [sub_eq_add_neg, add_comm, ← neg_mul] using
      intervalIntegral.integral_mono_ae ht intervalIntegrable_const (hw t).symm hwm

end TauCeti

/-- A function integrable on `(a, b)` for a measure without mass at points is interval integrable
between any two points `s, t ∈ [a, b]`. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_of_mem_Icc {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {μ : Measure ℝ} [NullSingletonClass μ] {a b s t : ℝ}
    (hf : IntegrableOn f (Ioo a b) μ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    IntervalIntegrable f μ s t :=
  ((integrableOn_Icc_iff_integrableOn_Ioo (f := f)).2 hf |>.mono_set
    (uIcc_subset_Icc hs ht)).intervalIntegrable

/-- For `P` integrable on `[a, b]` and `N` continuous on `[a, b]`, the integrand
`u ↦ P u ∘L N u` is interval integrable between any two points of `[a, b]`. -/
theorem MeasureTheory.IntegrableOn.intervalIntegrable_clm_comp {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {P : ℝ → F →L[𝕜] G} {N : ℝ → E →L[𝕜] F} {a b c d : ℝ} (hP : IntegrableOn P (Icc a b))
    (hN : ContinuousOn N (Icc a b)) (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    IntervalIntegrable (fun u ↦ P u ∘L N u) volume c d := by
  have hsub := uIcc_subset_Icc hc hd
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn (hN.mono hsub)
  exact IntegrableOn.intervalIntegrable <|
    (ContinuousLinearMap.compL 𝕜 E F G).integrable_of_bilin_of_bdd_right C (hP.mono_set hsub)
      ((hN.mono hsub).aestronglyMeasurable measurableSet_uIcc)
      (ae_restrict_of_forall_mem measurableSet_uIcc hC)

/-- For `f` integrable on `(a, b)`, `c ∈ [a, b]` and `a ≤ s ≤ t ≤ b`, the integral of `f` over
`(s, t)` is the difference of the primitives `∫ x in c..t, f x` and `∫ x in c..s, f x` based at
`c`. -/
theorem MeasureTheory.IntegrableOn.setIntegral_Ioo_eq_sub {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {μ : Measure ℝ} [NullSingletonClass μ] {a b c s t : ℝ}
    (hf : IntegrableOn f (Ioo a b) μ) (hc : c ∈ Icc a b) (has : a ≤ s) (hst : s ≤ t)
    (htb : t ≤ b) :
    ∫ x in Ioo s t, f x ∂μ = (∫ x in c..t, f x ∂μ) - ∫ x in c..s, f x ∂μ := by
  rw [intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable_of_mem_Icc hc ⟨has.trans hst, htb⟩)
      (hf.intervalIntegrable_of_mem_Icc hc ⟨has, hst.trans htb⟩),
    intervalIntegral.integral_of_le hst, integral_Ioc_eq_integral_Ioo]

/-- The norm of an interval integral of an integrable function is at most the integral of its
norm over the whole space. -/
theorem MeasureTheory.Integrable.norm_intervalIntegral_le_integral_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {μ : Measure ℝ} (hf : Integrable f μ)
    (a b : ℝ) : ‖∫ x in a..b, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
  intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (setIntegral_le_integral hf.norm (.of_forall fun _ ↦ norm_nonneg _))

/-- Translating a set integral over `(a, b]` to one over `(d + a, d + b]`; the set-integral form
of `intervalIntegral.integral_comp_add_left`, with no order assumption on `a` and `b`. -/
theorem MeasureTheory.setIntegral_Ioc_comp_add_left {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (d a b : ℝ) :
    ∫ x in Ioc a b, f (d + x) = ∫ x in Ioc (d + a) (d + b), f x := by
  rcases le_total a b with hab | hab
  · rw [← intervalIntegral.integral_of_le hab,
      ← intervalIntegral.integral_of_le (add_le_add_right hab d),
      intervalIntegral.integral_comp_add_left]
  · rw [Ioc_eq_empty_of_le hab, Ioc_eq_empty_of_le (add_le_add_right hab d), setIntegral_empty,
      setIntegral_empty]

/-- A function integrable on `[a, b]` has its translate by `c` integrable on `[a - c, b - c]`. -/
theorem MeasureTheory.IntegrableOn.comp_add_right_Icc {F : Type*} [NormedAddCommGroup F]
    {f : ℝ → F} {a b : ℝ} (hf : IntegrableOn f (Icc a b)) (c : ℝ) :
    IntegrableOn (fun u ↦ f (u + c)) (Icc (a - c) (b - c)) := by
  have h := (measurePreserving_add_right volume c).integrableOn_comp_preimage
    (measurableEmbedding_addRight c) (f := f) (s := Icc a b)
  rw [preimage_add_const_Icc] at h
  exact h.2 hf

/-- In an incomplete codomain every interval integral is `0`, as for the Bochner integral
(`MeasureTheory.integral_of_not_completeSpace`). -/
theorem intervalIntegral.integral_of_not_completeSpace {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : ¬CompleteSpace E) (f : ℝ → E) (a b : ℝ) (μ : Measure ℝ) :
    ∫ x in a..b, f x ∂μ = 0 := by
  rw [intervalIntegral, MeasureTheory.integral_of_not_completeSpace hE,
    MeasureTheory.integral_of_not_completeSpace hE, sub_zero]

namespace TauCeti.intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {μ : Measure ℝ}
  [NullSingletonClass μ] {a b s t : ℝ}

/-- For a measure without mass at points, the integral of `f` between two points of `[a, b]` is
bounded by the `L¹(a, b)` norm of `f`. -/
theorem norm_integral_le_setIntegral_norm (hf : IntegrableOn f (Ioo a b) μ)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖∫ x in s..t, f x ∂μ‖ ≤ ∫ x in Ioo a b, ‖f x‖ ∂μ := by
  have hf' : IntegrableOn f (Icc a b) μ := (integrableOn_Icc_iff_integrableOn_Ioo (f := f)).2 hf
  calc ‖∫ x in s..t, f x ∂μ‖ ≤ ∫ x in Ι s t, ‖f x‖ ∂μ :=
        _root_.intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ x in Icc a b, ‖f x‖ ∂μ :=
        setIntegral_mono_set hf'.norm (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)).eventuallySubset
    _ = ∫ x in Ioo a b, ‖f x‖ ∂μ := integral_Icc_eq_integral_Ioo

/-- For a measure without mass at points, if `‖f‖ ≤ g` almost everywhere on `(a, b)`, with `g`
integrable there, then the integral of `f` between two points of `[a, b]` is bounded by the
integral of `g` between them. -/
theorem norm_integral_le_abs_of_ae_norm_le {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) μ) (hfg : ∀ᵐ x ∂μ.restrict (Ioo a b), ‖f x‖ ≤ g x)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖∫ x in s..t, f x ∂μ‖ ≤ |∫ x in s..t, g x ∂μ| := by
  rw [restrict_Ioo_eq_restrict_Icc] at hfg
  exact _root_.intervalIntegral.norm_integral_le_abs_of_norm_le
    (ae_restrict_of_ae_restrict_of_subset (uIoc_subset_uIcc.trans (uIcc_subset_Icc hs ht)) hfg)
    (hg.intervalIntegrable_of_mem_Icc hs ht)

/-- For a function `M` into a normed group, integrable on `[a, b]`, the integral of `‖M‖` between
two points of `[a, b]` is at most its integral over `[a, b]`. -/
theorem abs_integral_norm_le {G : Type*} [NormedAddCommGroup G] {M : ℝ → G}
    (hM : IntegrableOn M (Icc a b)) {c d : ℝ} (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) :
    |∫ s in c..d, ‖M s‖| ≤ ∫ s in a..b, ‖M s‖ := by
  rw [_root_.intervalIntegral.abs_integral_eq_abs_integral_uIoc,
    abs_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun _ _ ↦ norm_nonneg _),
    _root_.intervalIntegral.integral_of_le (hc.1.trans hc.2)]
  have hsub : Ι c d ⊆ Ioc a b := fun x hx ↦
    ⟨(le_min hc.1 hd.1).trans_lt hx.1, hx.2.trans (max_le hc.2 hd.2)⟩
  exact setIntegral_mono_set (IntegrableOn.mono_set hM.norm Ioc_subset_Icc_self)
    (ae_of_all _ fun _ ↦ norm_nonneg _) hsub.eventuallySubset

/-- For a function `M` into a normed group and `m` integrable between `c` and `d` with
`‖M r‖ ≤ m r` for almost every `r` between them, `|∫ r in c..d, ‖M r‖| ≤ |∫ r in c..d, m r|`. -/
theorem abs_integral_norm_le_abs_integral_of_norm_le {G : Type*} [NormedAddCommGroup G]
    {M : ℝ → G} {m : ℝ → ℝ} {c d : ℝ} (hm : IntervalIntegrable m volume c d)
    (hMm : ∀ᵐ r, r ∈ Ι c d → ‖M r‖ ≤ m r) :
    |∫ r in c..d, ‖M r‖| ≤ |∫ r in c..d, m r| := by
  simpa only [Real.norm_eq_abs] using
    _root_.intervalIntegral.norm_integral_le_abs_of_norm_le (f := fun r ↦ ‖M r‖)
      ((ae_restrict_iff' measurableSet_uIoc).2 (by simpa only [norm_norm] using hMm)) hm

end TauCeti.intervalIntegral

/-- A continuous linear equivalence commutes with interval integrals of arbitrary functions;
compare `ContinuousLinearMap.intervalIntegral_comp_comm`, which needs integrability. -/
theorem ContinuousLinearEquiv.intervalIntegral_comp_comm {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] {μ : Measure ℝ} {a b : ℝ}
    (L : E ≃L[𝕜] F) (f : ℝ → E) :
    ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) := by
  simp_rw [intervalIntegral, L.integral_comp_comm, map_sub]

/-- `WithLp.ofLp` commutes with interval integrals of arbitrary `PiLp`-valued functions. -/
@[simp]
theorem PiLp.ofLp_intervalIntegral {p : ENNReal} [Fact (1 ≤ p)] {ι : Type*} [Fintype ι]
    {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℝ (β i)]
    {μ : Measure ℝ} {a b : ℝ} (f : ℝ → PiLp p β) :
    WithLp.ofLp (∫ x in a..b, f x ∂μ) = ∫ x in a..b, WithLp.ofLp (f x) ∂μ :=
  ((PiLp.continuousLinearEquiv p ℝ β).intervalIntegral_comp_comm f).symm

/-- If `f` is locally integrable on `[c, ∞)` for a locally finite measure, then its constant
extension `x ↦ f (max x c)` to all of `ℝ` is interval integrable between any two points. -/
theorem MeasureTheory.LocallyIntegrableOn.intervalIntegrable_comp_max {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {c : ℝ}
    (hf : LocallyIntegrableOn f (Ici c) μ) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ f (max x c)) μ a b := by
  suffices h : ∀ x, IntervalIntegrable (fun x ↦ f (max x c)) μ c x from (h a).symm.trans (h b)
  intro x
  rcases le_total c x with hx | hx
  · refine IntegrableOn.intervalIntegrable ?_
    rw [uIcc_of_le hx]
    exact (hf.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc).congr_fun
      (fun y hy ↦ by rw [max_eq_left hy.1]) measurableSet_Icc
  · refine (intervalIntegrable_const (c := f c)).congr fun y hy ↦ ?_
    rw [uIoc_of_ge hx] at hy
    simp only [max_eq_right hy.2]

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.GrowthOrder.Zero.Summability

/-!
# Real-part partial fractions and reflection cancellation at order one

For an entire function `f` of order less than two, the Hadamard partial-fraction series pairs each
zero `ρ` with `1 / ρ` so that `1 / (z - ρ) + 1 / ρ = z / (ρ (z - ρ))` is inverse-square summable.
The unpaired series `∑ m_ρ / ρ` need not converge at order one, since `∑ 1 / ‖ρ‖` can diverge.
When the zeros of `f` have bounded real part, however, taking real parts restores inverse-square
decay: `|(1 / ρ).re| = |ρ.re| ‖ρ⁻¹‖²`, so both `∑ m_ρ Re (1 / ρ)` and `∑ m_ρ Re (1 / (z - ρ))`
converge absolutely on their own.

At order at most one with `f 0 ≠ 0`, the real part of `logDeriv f z` therefore splits off its
zeros into `(logDeriv f 0).re + ∑ m_ρ Re (1 / (z - ρ)) + ∑ m_ρ Re (1 / ρ)`. If the divisor of `f`
is invariant under `ρ ↦ c - conj ρ` for some real point `c` with `f c ≠ 0` and
`(logDeriv f c).re = -(logDeriv f 0).re`, evaluating the split expansion at `z = c` identifies
`(logDeriv f 0).re = -∑ m_ρ Re (1 / ρ)` and cancels the constant term altogether:
`(logDeriv f z).re = ∑ m_ρ Re (1 / (z - ρ))`. In the half-plane `B ≤ z.re` to the right of all
zeros, every summand is nonnegative, so `0 ≤ (logDeriv f z).re` and any finite partial sum over
`ℂ` bounds `(logDeriv f z).re` from below.

## Main results

* `TauCeti.abs_re_one_div_eq`, `TauCeti.abs_re_one_div_le_mul_norm_inv_sq` and
  `TauCeti.abs_re_one_div_sub_le_mul_norm_inv_sq`: exact identity and inverse-square bounds for
  `|(1 / w).re|` and `|(1 / (z - w)).re|` on vertical strips.
* `TauCeti.OrderLE.summable_abs_divisor_mul_re_one_div`,
  `TauCeti.OrderLE.summable_divisor_mul_re_one_div`,
  `TauCeti.OrderLE.summable_abs_divisor_mul_re_one_div_sub` and
  `TauCeti.OrderLE.summable_divisor_mul_re_one_div_sub`: unconditional real-part summability for
  entire functions of order below two whose zeros have bounded real part.
* `TauCeti.OrderLE.re_logDeriv_eq_add_tsum_add_tsum`: split real-part partial-fraction expansion
  at order at most one.
* `TauCeti.OrderLE.re_logDeriv_zero_eq_neg_tsum` and `TauCeti.OrderLE.re_logDeriv_eq_tsum`:
  cancellation `(logDeriv f 0).re = -∑ m_ρ Re (1 / ρ)` and
  `(logDeriv f z).re = ∑ m_ρ Re (1 / (z - ρ))` under reflection `ρ ↦ c - conj ρ`.
* `TauCeti.OrderLE.sum_divisor_mul_re_one_div_sub_le_re_logDeriv` and
  `TauCeti.OrderLE.re_logDeriv_nonneg`: finite-subset lower bound and nonnegativity on the
  zero-free right half-plane `B ≤ z.re`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 11 and 12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), Theorem 10.16 and
  Corollary 10.18.
-/

public section

open Complex ComplexConjugate Filter Topology
open scoped BigOperators

namespace TauCeti

variable {f : ℂ → ℂ}

/-! ### Pointwise inverse-square bounds for real parts -/

/-- For every complex number `w`, including `w = 0` under totalized division,
`|(1 / w).re| = |w.re| ‖w⁻¹‖²`. -/
theorem abs_re_one_div_eq (w : ℂ) : |(1 / w).re| = |w.re| * ‖w⁻¹‖ ^ 2 := by
  rw [one_div, inv_re, abs_div, abs_of_nonneg (normSq_nonneg w), norm_inv, inv_pow,
    normSq_eq_norm_sq, div_eq_mul_inv]

/-- When `|w.re| ≤ B`, the real part of `1 / w` is bounded in absolute value by `B ‖w⁻¹‖²`. -/
theorem abs_re_one_div_le_mul_norm_inv_sq {w : ℂ} {B : ℝ} (hw : |w.re| ≤ B) :
    |(1 / w).re| ≤ B * ‖w⁻¹‖ ^ 2 := by
  rw [abs_re_one_div_eq]
  gcongr

/-- Far from `z`, a point `w` with `|w.re| ≤ B` and `2 ‖z‖ ≤ ‖w‖` satisfies
`|(1 / (z - w)).re| ≤ 4 (|z.re| + B) ‖w⁻¹‖²`. -/
theorem abs_re_one_div_sub_le_mul_norm_inv_sq {z w : ℂ} {B : ℝ} (hw : |w.re| ≤ B)
    (hzw : 2 * ‖z‖ ≤ ‖w‖) :
    |(1 / (z - w)).re| ≤ 4 * (|z.re| + B) * ‖w⁻¹‖ ^ 2 := by
  have hB0 : 0 ≤ B := (abs_nonneg w.re).trans hw
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [norm_zero] at hzw
    have hz0 : z = 0 := norm_le_zero_iff.mp (by linarith)
    simp [hz0]
  have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hsub : ‖w‖ ≤ 2 * ‖z - w‖ := by
    have htri := norm_sub_norm_le w z
    rw [norm_sub_rev] at htri
    linarith
  have hinv : ‖(z - w)⁻¹‖ ≤ 2 * ‖w⁻¹‖ := by
    rw [norm_inv, norm_inv, inv_le_iff_one_le_mul₀ (by linarith)]
    calc 1 = ‖w‖⁻¹ * ‖w‖ := (inv_mul_cancel₀ hw_pos.ne').symm
      _ ≤ ‖w‖⁻¹ * (2 * ‖z - w‖) := by gcongr
      _ = 2 * ‖w‖⁻¹ * ‖z - w‖ := by ring
  have hre : |(z - w).re| ≤ |z.re| + B := by
    rw [sub_re]
    linarith [abs_sub z.re w.re]
  calc |(1 / (z - w)).re| = |(z - w).re| * ‖(z - w)⁻¹‖ ^ 2 := abs_re_one_div_eq (z - w)
    _ ≤ (|z.re| + B) * (2 * ‖w⁻¹‖) ^ 2 := by gcongr
    _ = 4 * (|z.re| + B) * ‖w⁻¹‖ ^ 2 := by ring

/-! ### Unpaired real-part summability -/

private theorem summable_of_subtype_support {α : Type*} {s : Set α} {g : α → ℝ}
    (hsupp : ∀ x, x ∉ s → g x = 0) (hs : Summable (fun x : s ↦ g x)) : Summable g := by
  refine summable_subtype_and_compl.mp ⟨hs, ?_⟩
  convert summable_zero using 1
  ext x
  exact hsupp x.1 x.2

/-- If an entire function `f` has order less than two and its zeros have bounded real part, then
`∑ m_ρ |Re (1 / ρ)|` converges over `ℂ`. -/
theorem OrderLE.summable_abs_divisor_mul_re_one_div {A B : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ B) :
    Summable (fun ρ : ℂ ↦ |((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ρ).re|) := by
  set d := MeromorphicOn.divisor f Set.univ
  have hsq := (h.summable_divisor_toNat_mul_norm_inv_sq hf hA).mul_left (max B 0)
  refine summable_of_subtype_support (s := d.support) (fun ρ hρ ↦ ?_) ?_
  · rw [Function.notMem_support.mp hρ]
    simp
  · refine Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) (fun ρ ↦ ?_) hsq
    rw [abs_mul, Nat.abs_cast]
    calc ((d ρ).toNat : ℝ) * |(1 / (ρ : ℂ)).re|
        ≤ ((d ρ).toNat : ℝ) * (max B 0 * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
          gcongr
          exact abs_re_one_div_le_mul_norm_inv_sq ((hre ρ ρ.property).trans (le_max_left B 0))
      _ = max B 0 * (((d ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by ring

/-- If an entire function `f` has order less than two and its zeros have bounded real part, then
`∑ m_ρ Re (1 / ρ)` converges over `ℂ`. -/
theorem OrderLE.summable_divisor_mul_re_one_div {A B : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ B) :
    Summable (fun ρ : ℂ ↦ ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ρ).re) :=
  (h.summable_abs_divisor_mul_re_one_div hf hA hre).of_abs

/-- If an entire function `f` has order less than two and its zeros have bounded real part, then
`∑ m_ρ |Re (1 / (z - ρ))|` converges over `ℂ` at every point `z : ℂ` (including zeros, where the
`ρ = z` term vanishes under totalized division). -/
theorem OrderLE.summable_abs_divisor_mul_re_one_div_sub {A B : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ B) (z : ℂ) :
    Summable
      (fun ρ : ℂ ↦ |((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (z - ρ)).re|) := by
  set d := MeromorphicOn.divisor f Set.univ
  set C := 4 * (|z.re| + max B 0)
  have : 0 ≤ C := by positivity
  let u : d.support → ℝ := fun ρ ↦ |((d ρ).toNat : ℝ) * (1 / (z - ρ)).re|
  let g : d.support → ℝ := fun ρ ↦ C * (((d ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2)
  have hg : Summable g := (h.summable_divisor_toNat_mul_norm_inv_sq hf hA).mul_left C
  have hmin : Summable (fun ρ : d.support ↦ min (u ρ) (g ρ)) :=
    Summable.of_nonneg_of_le (fun ρ ↦ le_min (abs_nonneg _) (by positivity))
      (fun _ ↦ min_le_right _ _) hg
  refine summable_of_subtype_support (s := d.support) (fun ρ hρ ↦ ?_) ?_
  · rw [Function.notMem_support.mp hρ]
    simp
  · refine hmin.congr_cofinite ?_
    filter_upwards [(MeromorphicOn.divisor_norm_sublevel_finite f
      (2 * ‖z‖)).eventually_cofinite_notMem] with ρ hρ
    have hzw : 2 * ‖z‖ ≤ ‖(ρ : ℂ)‖ := le_of_not_ge hρ
    refine min_eq_left ?_
    dsimp only [u, g]
    rw [abs_mul, Nat.abs_cast]
    calc ((d ρ).toNat : ℝ) * |(1 / (z - ρ)).re|
        ≤ ((d ρ).toNat : ℝ) * (C * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by
          gcongr
          exact abs_re_one_div_sub_le_mul_norm_inv_sq
            ((hre ρ ρ.property).trans (le_max_left B 0)) hzw
      _ = C * (((d ρ).toNat : ℝ) * ‖(ρ : ℂ)⁻¹‖ ^ 2) := by ring

/-- If an entire function `f` has order less than two and its zeros have bounded real part, then
`∑ m_ρ Re (1 / (z - ρ))` converges over `ℂ` at every point `z : ℂ`. -/
theorem OrderLE.summable_divisor_mul_re_one_div_sub {A B : ℝ} (h : OrderLE f A)
    (hf : Differentiable ℂ f) (hA : A < 2)
    (hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ B) (z : ℂ) :
    Summable (fun ρ : ℂ ↦ ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (z - ρ)).re) :=
  (h.summable_abs_divisor_mul_re_one_div_sub hf hA hre z).of_abs

/-! ### Split partial fractions and reflection cancellation -/

/-- **Split real-part partial fractions.** For an entire function `f` of order at most one with
`f 0 ≠ 0` whose zeros have bounded real part, off the zeros of `f` the real part of `logDeriv f z`
splits into `(logDeriv f 0).re`, `∑ m_ρ Re (1 / (z - ρ))`, and `∑ m_ρ Re (1 / ρ)`. -/
theorem OrderLE.re_logDeriv_eq_add_tsum_add_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {B : ℝ}
    (hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ B) {z : ℂ}
    (hz : f z ≠ 0) :
    (logDeriv f z).re = (logDeriv f 0).re +
      (∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (z - ρ)).re) +
      ∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ρ).re := by
  set d := MeromorphicOn.divisor f Set.univ with hd_def
  have hpair :=
    (h.summable_norm_divisor_mul_one_div_sub_add_one_div hf hf0 (by norm_num) hz).of_norm
  have hsub := h.summable_divisor_mul_re_one_div_sub hf (by norm_num) hre z
  have h0 := h.summable_divisor_mul_re_one_div hf (by norm_num) hre
  have hsupp : (Function.support fun ρ : ℂ ↦
      ((d ρ).toNat : ℝ) * (1 / (z - ρ)).re + ((d ρ).toNat : ℝ) * (1 / ρ).re) ⊆ d.support := by
    intro ρ hρ
    by_contra hnd
    rw [Function.notMem_support] at hnd
    exact hρ (by simp [hnd])
  have hterm (ρ : d.support) :
      (((d ρ).toNat : ℂ) * (1 / (z - ρ) + 1 / (ρ : ℂ))).re =
        ((d ρ).toNat : ℝ) * (1 / (z - ρ)).re + ((d ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
    rw [← ofReal_natCast, mul_add, add_re, re_ofReal_mul, re_ofReal_mul]
  rw [h.logDeriv_eq_add_tsum hf hf0 hz, add_re, Complex.re_tsum hpair]
  simp_rw [← hd_def]
  rw [tsum_congr hterm, tsum_subtype_eq_of_support_subset hsupp]
  rw [← hd_def] at hsub h0
  rw [hsub.tsum_add h0, add_assoc]

/-- If the whole-plane divisor of `f` is invariant under `ρ ↦ c - conj ρ` for real `c`, then
reindexing by that involution equates `∑ m_ρ Re (1 / (c - ρ))` with `∑ m_ρ Re (1 / ρ)`. -/
theorem tsum_divisor_mul_re_one_div_ofReal_sub {c : ℝ}
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ) :
    (∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ((c : ℂ) - ρ)).re) =
      ∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ρ).re := by
  let e : ℂ ≃ ℂ :=
    { toFun := fun ρ ↦ (c : ℂ) - conj ρ
      invFun := fun ρ ↦ (c : ℂ) - conj ρ
      left_inv := fun ρ ↦ by simp
      right_inv := fun ρ ↦ by simp }
  rw [← e.tsum_eq]
  refine tsum_congr fun ρ ↦ ?_
  have hsub : (c : ℂ) - e ρ = conj ρ := by simp [e]
  have hre : (1 / conj ρ).re = (1 / ρ).re := by
    rw [one_div, ← map_inv₀, conj_re, ← one_div]
  rw [show MeromorphicOn.divisor f Set.univ (e ρ) = MeromorphicOn.divisor f Set.univ ρ from hsym ρ,
    hsub, hre]

/-- Under `ρ ↦ c - conj ρ` symmetry of the divisor, an upper bound `ρ.re ≤ B` on the divisor
support implies a two-sided bound `|ρ.re| ≤ max |c - B| |B|`. -/
private theorem abs_re_le_of_re_le_of_symm {c B : ℝ}
    (hupper : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, ρ.re ≤ B)
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ)
    {ρ : ℂ} (hρ : ρ ∈ (MeromorphicOn.divisor f Set.univ).support) :
    |ρ.re| ≤ max |c - B| |B| := by
  have hρ' : (c : ℂ) - conj ρ ∈ (MeromorphicOn.divisor f Set.univ).support := by
    rw [Function.mem_support, hsym ρ]
    exact hρ
  have hhi : ρ.re ≤ B := hupper ρ hρ
  have hlo : c - B ≤ ρ.re := by
    have := hupper ((c : ℂ) - conj ρ) hρ'
    simp only [sub_re, ofReal_re, conj_re] at this
    linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [neg_abs_le (c - B), le_max_left |c - B| |B|]
  · linarith [le_abs_self B, le_max_right |c - B| |B|]

/-- **Cancellation of the Hadamard constant's real part.** If `f` is entire of order at most one
with `f 0 ≠ 0` and `f c ≠ 0` for real `c`, its zeros have real part bounded above by `B`, its
divisor is invariant under `ρ ↦ c - conj ρ`, and `(logDeriv f c).re = -(logDeriv f 0).re`, then
`(logDeriv f 0).re = -∑ m_ρ Re (1 / ρ)`. -/
theorem OrderLE.re_logDeriv_zero_eq_neg_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {c B : ℝ} (hfc : f c ≠ 0)
    (hupper : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, ρ.re ≤ B)
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ)
    (hlog : (logDeriv f c).re = -(logDeriv f 0).re) :
    (logDeriv f 0).re =
      -∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / ρ).re := by
  have hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ max |c - B| |B| :=
    fun _ hρ ↦ abs_re_le_of_re_le_of_symm hupper hsym hρ
  have hsplit := h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hre hfc
  rw [tsum_divisor_mul_re_one_div_ofReal_sub hsym, hlog] at hsplit
  linarith

/-- **Unpaired real-part partial fractions.** Under the reflection hypotheses of
`OrderLE.re_logDeriv_zero_eq_neg_tsum`, at every `z : ℂ` with `f z ≠ 0` the constant terms cancel:
`(logDeriv f z).re = ∑ m_ρ Re (1 / (z - ρ))`. -/
theorem OrderLE.re_logDeriv_eq_tsum (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {c B : ℝ} (hfc : f c ≠ 0)
    (hupper : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, ρ.re ≤ B)
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ)
    (hlog : (logDeriv f c).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0) :
    (logDeriv f z).re =
      ∑' ρ : ℂ, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (z - ρ)).re := by
  have hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ max |c - B| |B| :=
    fun _ hρ ↦ abs_re_le_of_re_le_of_symm hupper hsym hρ
  have hsplit := h.re_logDeriv_eq_add_tsum_add_tsum hf hf0 hre hz
  have h0 := h.re_logDeriv_zero_eq_neg_tsum hf hf0 hfc hupper hsym hlog
  linarith

/-! ### Nonnegativity and finite-subset bounds on zero-free half-planes -/

/-- Under the reflection hypotheses of `OrderLE.re_logDeriv_eq_tsum`, at any point `z` with
`B ≤ z.re` and `f z ≠ 0`, every finite partial sum of `m_ρ Re (1 / (z - ρ))` is bounded above by
`(logDeriv f z).re`. -/
theorem OrderLE.sum_divisor_mul_re_one_div_sub_le_re_logDeriv (h : OrderLE f 1)
    (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0) {c B : ℝ} (hfc : f c ≠ 0)
    (hupper : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, ρ.re ≤ B)
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ)
    (hlog : (logDeriv f c).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0) (hzre : B ≤ z.re)
    (S : Finset ℂ) :
    (∑ ρ ∈ S, ((MeromorphicOn.divisor f Set.univ ρ).toNat : ℝ) * (1 / (z - ρ)).re) ≤
      (logDeriv f z).re := by
  have hre : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, |ρ.re| ≤ max |c - B| |B| :=
    fun _ hρ ↦ abs_re_le_of_re_le_of_symm hupper hsym hρ
  rw [h.re_logDeriv_eq_tsum hf hf0 hfc hupper hsym hlog hz]
  refine (h.summable_divisor_mul_re_one_div_sub hf (by norm_num) hre z).sum_le_tsum S fun ρ _ ↦ ?_
  by_cases hρ : ρ ∈ (MeromorphicOn.divisor f Set.univ).support
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [one_div, inv_re]
    exact div_nonneg (by rw [sub_re]; linarith [hupper ρ hρ]) (normSq_nonneg _)
  · rw [Function.notMem_support.mp hρ]
    simp

/-- Under the reflection hypotheses of `OrderLE.re_logDeriv_eq_tsum`, `(logDeriv f z).re` is
nonnegative whenever `B ≤ z.re` and `f z ≠ 0`. -/
theorem OrderLE.re_logDeriv_nonneg (h : OrderLE f 1) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) {c B : ℝ} (hfc : f c ≠ 0)
    (hupper : ∀ ρ ∈ (MeromorphicOn.divisor f Set.univ).support, ρ.re ≤ B)
    (hsym : ∀ ρ : ℂ,
      MeromorphicOn.divisor f Set.univ ((c : ℂ) - conj ρ) = MeromorphicOn.divisor f Set.univ ρ)
    (hlog : (logDeriv f c).re = -(logDeriv f 0).re) {z : ℂ} (hz : f z ≠ 0) (hzre : B ≤ z.re) :
    0 ≤ (logDeriv f z).re := by
  simpa using h.sum_divisor_mul_re_one_div_sub_le_re_logDeriv hf hf0 hfc hupper hsym hlog hz hzre ∅

/-! ### Example -/

/-- `Complex.exp` has order at most one, no zeros, and trivial divisor symmetry, yet
`(logDeriv exp 0).re = 1 ≠ 0`: the reflection hypothesis `(logDeriv f c).re = -(logDeriv f 0).re`
in `OrderLE.re_logDeriv_zero_eq_neg_tsum` cannot be omitted. -/
example :
    (logDeriv exp 0).re = 1 ∧
      -∑' ρ : ℂ, ((MeromorphicOn.divisor exp Set.univ ρ).toNat : ℝ) * (1 / ρ).re = 0 := by
  refine ⟨?_, ?_⟩
  · rw [logDeriv_apply, Complex.deriv_exp, exp_zero, div_self one_ne_zero, one_re]
  · have hzero (ρ : ℂ) : MeromorphicOn.divisor exp Set.univ ρ = 0 :=
      (differentiable_exp.analyticAt ρ).divisor_apply_eq_zero (exp_ne_zero ρ)
    simp [hzero]

end TauCeti

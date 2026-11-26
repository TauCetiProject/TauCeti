/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import TauCeti.Analysis.Complex.ClosedHalfPlane

/-!
# Boundary continuation with a pole of integer order

A Tauberian theorem for a pole of order `k + 1` (Delange's theorem for integer exponents) needs
to know how a function `F`, holomorphic on the half-plane `Re s > a`, behaves on its boundary
line `Re s = a`: near `a` it is a holomorphic numerator over `(s - a) ^ (k + 1)`, and at every
other point `a + y i` of the line it continues holomorphically. This file packages these
hypotheses as the predicate `TauCeti.HigherPoleTauberian.PoleBoundary F a k A`, where `A` is the
value of the numerator at `a`.

Every agreement in `PoleBoundary` is required only on the open half-plane `Re s > a`, so the
values of `F` on the line are never consulted. In particular the predicate applies to a totalised
function such as an `LSeries`, whose values off its half-plane of convergence carry no meaning.

## Main definitions

* `TauCeti.HigherPoleTauberian.PoleBoundary F a k A`: `F` is analytic on `Re s > a`, equals
  `g s / (s - a) ^ (k + 1)` near `a` with `g` holomorphic and `g a = A`, and continues
  holomorphically across every other point of the line `Re s = a`.

## Main results

* `PoleBoundary.tendsto_sub_pow_mul`: `(s - a) ^ (k + 1) F s → A` as `s → a` within `Re s > a`.
* `PoleBoundary.unique`, `PoleBoundary.of_lt`, `PoleBoundary.order_le_of_ne_zero` and
  `PoleBoundary.order_unique`: the leading coefficient is determined by `F`, a pole of order at
  most `k + 1` also has order at most `l + 1` with leading coefficient `0` for `k < l`, and the
  order is determined when the coefficient is nonzero.
* `poleBoundary_congr`, `PoleBoundary.update_of_re_le` and `poleBoundary_update_iff_of_re_le`: only
  the values on the open half-plane matter.
* `PoleBoundary.mul_analyticOnNhd`, `PoleBoundary.analyticOnNhd_mul`, `PoleBoundary.const_mul`,
  `PoleBoundary.neg`, `PoleBoundary.add`, `PoleBoundary.sub`, `PoleBoundary.div_id`,
  `PoleBoundary.comp_const_mul`, `PoleBoundary.comp_add_right`, `PoleBoundary.mul` and
  `PoleBoundary.pow`: multiplication by a function holomorphic on the closed half-plane, linear
  combinations at fixed `(a, k)`, division by the argument, rescaling and horizontal translation of
  the variable, and products, under which the pole orders add.
* `poleBoundary_const_div_pow`, `poleBoundary_const_div_pow_iff`,
  `poleBoundary_of_analyticOnNhd`, `poleBoundary_riemannZeta`, `poleBoundary_riemannZeta_pow` and
  `not_poleBoundary_inv_one_sub_cexp_log_two`: the model pole `A / (s - a) ^ (k + 1)`, functions
  holomorphic on the closed half-plane, the Riemann zeta function and its powers at `1`, and the
  dyadic negative control `(1 - exp ((1 - s) log 2))⁻¹` showing that holomorphic continuation off
  the real axis cannot be omitted.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242, §5.2.1, pp. 235–238 (Théorème III) and §5.3, p. 242.
-/

public section

open Complex Filter Metric Set
open scoped Topology

namespace TauCeti.HigherPoleTauberian

/-- `PoleBoundary F a k A`: the function `F` is holomorphic on the half-plane `Re s > a`; near `a`
it equals `g s / (s - a) ^ (k + 1)` with `g` holomorphic on a disc about `a` and `g a = A`; and at
every other point `a + y i` of the line `Re s = a` it continues holomorphically. All agreements are
required on the open half-plane only. With `A ≠ 0` the pole has order exactly `k + 1`; `A = 0`
allows order at most `k`.

This is the hypothesis of Delange's Theorem III (Delange 1954, §5.2.1) for the integer exponent
`k + 1`: there the transform is `g s / (s - a) ^ (k + 1) + h s` near `a`, and the holomorphic
`h` is absorbed into the numerator. -/
structure PoleBoundary (F : ℂ → ℂ) (a : ℝ) (k : ℕ) (A : ℝ) : Prop where
  /-- `F` is holomorphic on the open half-plane `Re s > a`. -/
  interior : AnalyticOnNhd ℂ F {s : ℂ | a < s.re}
  /-- Near `a`, `F` is a holomorphic numerator with value `A` over `(s - a) ^ (k + 1)`. -/
  pole : ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (a : ℂ) r) ∧
    g a = A ∧ ∀ s ∈ ball (a : ℂ) r, a < s.re → F s = g s / (s - a) ^ (k + 1)
  /-- `F` continues holomorphically across every point `a + y i` with `y ≠ 0`. -/
  away : ∀ y : ℝ, y ≠ 0 → ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g (ball ((a : ℂ) + y * I) r) ∧
      ∀ s ∈ ball ((a : ℂ) + y * I) r, a < s.re → F s = g s

variable {F G H : ℂ → ℂ} {a A B : ℝ} {k l : ℕ}

/-- Membership in a ball after multiplying by a positive real. -/
private lemma ofReal_mul_mem_ball {c r : ℝ} (hc : 0 < c) {s z : ℂ} (hs : s ∈ ball z (r / c)) :
    (c : ℂ) * s ∈ ball ((c : ℂ) * z) r := by
  rw [mem_ball, dist_eq, ← mul_sub, norm_mul, norm_real, Real.norm_of_nonneg hc.le]
  rw [mem_ball, dist_eq, lt_div_iff₀ hc] at hs
  linarith

/-- Multiplying by a positive real `c` maps the half-plane `Re s > a / c` into `Re s > a`. -/
private lemma lt_re_ofReal_mul {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : a / c < s.re) :
    a < ((c : ℂ) * s).re := by
  rw [re_ofReal_mul]
  exact (div_lt_iff₀' hc).1 hs

/-- Multiplying by `c ≠ 0` sends a point `a / c + w` to `a + c w`. -/
private lemma ofReal_mul_ofReal_div_add {c : ℝ} (hc : c ≠ 0) (w : ℂ) :
    (c : ℂ) * (((a / c : ℝ) : ℂ) + w) = a + c * w := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
  push_cast
  field_simp

/-- Two germs holomorphic on balls about `z` restrict to a common ball about `z` contained in
both. -/
private lemma exists_ball_analyticOnNhd_pair {z : ℂ} {r ρ : ℝ} {g h : ℂ → ℂ} (hr : 0 < r)
    (hρ : 0 < ρ) (hg : AnalyticOnNhd ℂ g (ball z r)) (hh : AnalyticOnNhd ℂ h (ball z ρ)) :
    ∃ δ : ℝ, 0 < δ ∧ AnalyticOnNhd ℂ g (ball z δ) ∧ AnalyticOnNhd ℂ h (ball z δ) ∧
      ∀ s ∈ ball z δ, s ∈ ball z r ∧ s ∈ ball z ρ :=
  ⟨min r ρ, lt_min hr hρ, hg.mono (ball_subset_ball (min_le_left _ _)),
    hh.mono (ball_subset_ball (min_le_right _ _)),
    fun _ hs ↦ ⟨ball_subset_ball (min_le_left _ _) hs, ball_subset_ball (min_le_right _ _) hs⟩⟩

/-- If `F` is holomorphic at every point of the closed half-plane `Re s ≥ a` other than `a`, then
`PoleBoundary F a k A` follows from its `pole` field alone: the germs away from `a` are `F`
itself. -/
theorem PoleBoundary.of_analyticAt (hF : ∀ s : ℂ, a ≤ s.re → s ≠ a → AnalyticAt ℂ F s)
    (hpole : ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (a : ℂ) r) ∧
      g a = A ∧ ∀ s ∈ ball (a : ℂ) r, a < s.re → F s = g s / (s - a) ^ (k + 1)) :
    PoleBoundary F a k A where
  interior s hs := hF s (le_of_lt hs) fun h ↦ by simp [h] at hs
  pole := hpole
  away y hy := by
    obtain ⟨r, hr, hFr⟩ := (hF ((a : ℂ) + y * I) (by simp) fun h ↦ hy <| by
      simpa using congrArg Complex.im h).exists_ball_analyticOnNhd
    exact ⟨r, hr, F, hFr, fun _ _ _ ↦ rfl⟩

/-- Only the values of `F` on the open half-plane `Re s > a` enter `PoleBoundary F a k A`. -/
theorem PoleBoundary.congr (hF : PoleBoundary F a k A) (hFG : ∀ s : ℂ, a < s.re → F s = G s) :
    PoleBoundary G a k A where
  interior s hs := (hF.interior s hs).congr <|
    eventually_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds hs) fun t ht ↦ hFG t ht
  pole := by
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    exact ⟨r, hr, g, hg, hga, fun s hs hre ↦ (hFG s hre).symm.trans (hFg s hs hre)⟩
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    exact ⟨r, hr, g, hg, fun s hs hre ↦ (hFG s hre).symm.trans (hFg s hs hre)⟩

/-- Two functions that agree on the open half-plane `Re s > a` satisfy the same `PoleBoundary`
predicates; their values on the line `Re s = a` are irrelevant. -/
theorem poleBoundary_congr (hFG : ∀ s : ℂ, a < s.re → F s = G s) :
    PoleBoundary F a k A ↔ PoleBoundary G a k A :=
  ⟨fun h ↦ h.congr hFG, fun h ↦ h.congr fun s hs ↦ (hFG s hs).symm⟩

/-- Updating a function at any point `z` with `Re z ≤ a` leaves `PoleBoundary` unchanged. -/
@[simp]
theorem poleBoundary_update_iff_of_re_le {z : ℂ} (hz : z.re ≤ a) (w : ℂ) :
    PoleBoundary (Function.update F z w) a k A ↔ PoleBoundary F a k A :=
  poleBoundary_congr fun _ hs ↦
    Function.update_of_ne (by rintro rfl; exact lt_irrefl _ (hs.trans_le hz)) _ _

/-- Modifying `F` at a point `z` with `Re z ≤ a` preserves `PoleBoundary`. -/
theorem PoleBoundary.update_of_re_le (hF : PoleBoundary F a k A) {z : ℂ} (hz : z.re ≤ a) (w : ℂ) :
    PoleBoundary (Function.update F z w) a k A :=
  (poleBoundary_update_iff_of_re_le hz w).2 hF

/-- The leading coefficient as a limit: `(s - a) ^ (k + 1) F s → A` as `s → a` within the open
half-plane `Re s > a`. -/
theorem PoleBoundary.tendsto_sub_pow_mul (hF : PoleBoundary F a k A) :
    Tendsto (fun s ↦ (s - a) ^ (k + 1) * F s) (𝓝[{s : ℂ | a < s.re}] (a : ℂ)) (𝓝 (A : ℂ)) := by
  obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
  rw [← hga]
  refine ((hg a (mem_ball_self hr)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds _ hr), self_mem_nhdsWithin] with s hs hre
  have hsa : (s - a) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.2 fun h ↦ by simp [h] at hre)
  rw [hFg s hs hre, mul_div_cancel₀ _ hsa]

/-- **Uniqueness of the leading coefficient**: the value `A` in `PoleBoundary F a k A` is
determined by `F`, `a` and `k`. -/
theorem PoleBoundary.unique (hA : PoleBoundary F a k A) (hB : PoleBoundary F a k B) : A = B := by
  have := nhdsWithin_setOfPred_lt_re_neBot (s := (a : ℂ)) (ofReal_re a).ge
  exact_mod_cast tendsto_nhds_unique hA.tendsto_sub_pow_mul hB.tendsto_sub_pow_mul

/-- A pole of order at most `k + 1` is also a pole of order at most `l + 1` with leading
coefficient `0` whenever `k < l`. -/
theorem PoleBoundary.of_lt (hF : PoleBoundary F a k A) (hkl : k < l) : PoleBoundary F a l 0 where
  interior := hF.interior
  pole := by
    obtain ⟨r, hr, g, hg, -, hFg⟩ := hF.pole
    refine ⟨r, hr, fun s ↦ g s * (s - a) ^ (l - k),
      hg.mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _), ?_, fun s hs hre ↦ ?_⟩
    · simp [Nat.sub_ne_zero_of_lt hkl]
    · have hsa : s - (a : ℂ) ≠ 0 := sub_ne_zero.2 fun hs' ↦ by simp [hs'] at hre
      have hexp : l + 1 = (k + 1) + (l - k) := by omega
      dsimp only
      rw [hFg s hs hre, hexp, pow_add _ (k + 1) (l - k),
        mul_div_mul_right _ _ (pow_ne_zero _ hsa)]
  away := hF.away

/-- If `F` has a pole of order at most `k + 1` at `a`, then it has no pole of higher order `l + 1`
with a nonzero leading coefficient there. -/
theorem PoleBoundary.order_le_of_ne_zero (hA : PoleBoundary F a k A)
    (hB : PoleBoundary F a l B) (hB0 : B ≠ 0) : l ≤ k := by
  by_contra! hkl
  exact hB0 (hB.unique (hA.of_lt hkl))

/-- **Uniqueness of the pole order**: if `F` has a pole of order `k + 1` with leading coefficient
`A ≠ 0` and of order `l + 1` with leading coefficient `B ≠ 0`, then `k = l`. -/
theorem PoleBoundary.order_unique (hA : PoleBoundary F a k A) (hB : PoleBoundary F a l B)
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) : k = l :=
  le_antisymm (hB.order_le_of_ne_zero hA hA0) (hA.order_le_of_ne_zero hB hB0)

/-- **Multiplication by a regular function**: if `H` is holomorphic at every point of the closed
half-plane `Re s ≥ a` and real at `a`, then `F H` satisfies `PoleBoundary` with the same `k` and
leading coefficient `A H(a)`. In particular the pole order is unchanged when `H a ≠ 0`. -/
theorem PoleBoundary.mul_analyticOnNhd {C : ℝ} (hF : PoleBoundary F a k A)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | a ≤ s.re}) (hHa : H a = C) :
    PoleBoundary (fun s ↦ F s * H s) a k (A * C) where
  interior s hs := (hF.interior s hs).mul (hH s (mem_ofPred.1 hs).le)
  pole := by
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    obtain ⟨ρ, hρ, hHρ⟩ := (hH a (by simp)).exists_ball_analyticOnNhd
    obtain ⟨δ, hδ, hg', hH', hball⟩ := exists_ball_analyticOnNhd_pair hr hρ hg hHρ
    refine ⟨δ, hδ, _, hg'.mul hH', by simp [hga, hHa], fun s hs hre ↦ ?_⟩
    rw [hFg s (hball s hs).1 hre, div_mul_eq_mul_div]
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    obtain ⟨ρ, hρ, hHρ⟩ := (hH ((a : ℂ) + y * I) (by simp)).exists_ball_analyticOnNhd
    obtain ⟨δ, hδ, hg', hH', hball⟩ := exists_ball_analyticOnNhd_pair hr hρ hg hHρ
    exact ⟨δ, hδ, _, hg'.mul hH', fun s hs hre ↦ by rw [hFg s (hball s hs).1 hre]⟩

/-- Multiplying `F` on the left by a function `H` holomorphic at every point of `Re s ≥ a` with
real value `H a = C` multiplies the leading coefficient by `C`. -/
theorem PoleBoundary.analyticOnNhd_mul {C : ℝ} (hF : PoleBoundary F a k A)
    (hH : AnalyticOnNhd ℂ H {s : ℂ | a ≤ s.re}) (hHa : H a = C) :
    PoleBoundary (fun s ↦ H s * F s) a k (C * A) := by
  rw [mul_comm C A]
  exact (hF.mul_analyticOnNhd hH hHa).congr fun s _ ↦ mul_comm (F s) (H s)

/-- Multiplying `F` by a real constant `c` scales the leading coefficient by `c`. -/
theorem PoleBoundary.const_mul (hF : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ (c : ℂ) * F s) a k (c * A) :=
  hF.analyticOnNhd_mul analyticOnNhd_const rfl

/-- Negating `F` negates the leading coefficient. -/
theorem PoleBoundary.neg (hF : PoleBoundary F a k A) : PoleBoundary (fun s ↦ -F s) a k (-A) := by
  simpa using hF.const_mul (-1)

/-- Adding two functions satisfying `PoleBoundary` at the same `(a, k)` adds their leading
coefficients. -/
theorem PoleBoundary.add (hF : PoleBoundary F a k A) (hG : PoleBoundary G a k B) :
    PoleBoundary (fun s ↦ F s + G s) a k (A + B) where
  interior := hF.interior.add hG.interior
  pole := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hga₁, hFg₁⟩ := hF.pole
    obtain ⟨r₂, hr₂, g₂, hg₂, hga₂, hGg₂⟩ := hG.pole
    obtain ⟨δ, hδ, hg₁', hg₂', hball⟩ := exists_ball_analyticOnNhd_pair hr₁ hr₂ hg₁ hg₂
    refine ⟨δ, hδ, fun s ↦ g₁ s + g₂ s, hg₁'.add hg₂', by simp [hga₁, hga₂], fun s hs hre ↦ ?_⟩
    rw [hFg₁ s (hball s hs).1 hre, hGg₂ s (hball s hs).2 hre, add_div]
  away y hy := by
    obtain ⟨r₁, hr₁, g₁, hg₁, hFg₁⟩ := hF.away y hy
    obtain ⟨r₂, hr₂, g₂, hg₂, hGg₂⟩ := hG.away y hy
    obtain ⟨δ, hδ, hg₁', hg₂', hball⟩ := exists_ball_analyticOnNhd_pair hr₁ hr₂ hg₁ hg₂
    exact ⟨δ, hδ, fun s ↦ g₁ s + g₂ s, hg₁'.add hg₂',
      fun s hs hre ↦ by rw [hFg₁ s (hball s hs).1 hre, hGg₂ s (hball s hs).2 hre]⟩

/-- Subtracting two functions satisfying `PoleBoundary` at the same `(a, k)` subtracts their
leading coefficients. -/
theorem PoleBoundary.sub (hF : PoleBoundary F a k A) (hG : PoleBoundary G a k B) :
    PoleBoundary (fun s ↦ F s - G s) a k (A - B) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- **Division by the argument**: for `a > 0`, dividing by `s` keeps the pole order and divides
the leading coefficient by `a`. This is the passage from the Laplace transform `F` of a counting
function to `F s / s`. -/
theorem PoleBoundary.div_id (hF : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F s / s) a k (A / a) := by
  have hinv : AnalyticOnNhd ℂ (fun s : ℂ ↦ s⁻¹) {s : ℂ | a ≤ s.re} := fun s hs ↦
    analyticAt_inv (fun h ↦ by simp [h] at hs; linarith)
  simpa [div_eq_mul_inv] using hF.mul_analyticOnNhd hinv (C := a⁻¹) (by simp)

/-- **Rescaling the variable**: for `c > 0`, the function `s ↦ F (c s)` has a pole of the same
order at `a / c`, with leading coefficient `A / c ^ (k + 1)`. -/
theorem PoleBoundary.comp_const_mul (hF : PoleBoundary F a k A) {c : ℝ} (hc : 0 < c) :
    PoleBoundary (fun s ↦ F (c * s)) (a / c) k (A / c ^ (k + 1)) where
  interior s hs :=
    (hF.interior _ (lt_re_ofReal_mul hc hs)).comp_of_eq (analyticAt_const.mul analyticAt_id) rfl
  pole := by
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    have hca : (c : ℂ) * ((a / c : ℝ) : ℂ) = a := by
      simpa using ofReal_mul_ofReal_div_add (a := a) hc.ne' 0
    refine ⟨r / c, div_pos hr hc, fun s ↦ g (c * s) / c ^ (k + 1), fun s hs ↦ ?_, ?_,
      fun s hs hre ↦ ?_⟩
    · refine AnalyticAt.div ?_ analyticAt_const (pow_ne_zero _ (ofReal_ne_zero.2 hc.ne'))
      exact (hg _ (hca ▸ ofReal_mul_mem_ball hc hs)).comp_of_eq
        (analyticAt_const.mul analyticAt_id) rfl
    · dsimp only
      rw [hca, hga]
      simp
    · rw [hFg _ (hca ▸ ofReal_mul_mem_ball hc hs) (lt_re_ofReal_mul hc hre), div_div, ← mul_pow]
      congr 2
      rw [← hca]
      ring
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away (c * y) (mul_ne_zero hc.ne' hy)
    have hcy : (c : ℂ) * (((a / c : ℝ) : ℂ) + y * I) = a + ((c * y : ℝ) : ℂ) * I := by
      rw [ofReal_mul_ofReal_div_add hc.ne', ofReal_mul, mul_assoc]
    refine ⟨r / c, div_pos hr hc, fun s ↦ g (c * s), fun s hs ↦ ?_, fun s hs hre ↦ ?_⟩
    · exact (hg _ (hcy ▸ ofReal_mul_mem_ball hc hs)).comp_of_eq
        (analyticAt_const.mul analyticAt_id) rfl
    · exact hFg _ (hcy ▸ ofReal_mul_mem_ball hc hs) (lt_re_ofReal_mul hc hre)

/-- **Rescaling to abscissa `1`**: for `a > 0`, the function `s ↦ F (a s)` has a pole of the same
order at `1`, with leading coefficient `A / a ^ (k + 1)`. -/
theorem PoleBoundary.comp_abscissa_mul (hF : PoleBoundary F a k A) (ha : 0 < a) :
    PoleBoundary (fun s ↦ F (a * s)) 1 k (A / a ^ (k + 1)) := by
  simpa [div_self ha.ne'] using hF.comp_const_mul ha

/-- Horizontal translation `s ↦ F (s + c)` for real `c` shifts the abscissa from `a` to `a - c`
without changing the pole order or leading coefficient. -/
theorem PoleBoundary.comp_add_right (hF : PoleBoundary F a k A) (c : ℝ) :
    PoleBoundary (fun s ↦ F (s + c)) (a - c) k A := by
  have hre {s : ℂ} (hs : a - c < s.re) : a < (s + c).re := by
    simpa using sub_lt_iff_lt_add.1 hs
  have hball {r : ℝ} {z w s : ℂ} (hzw : z + c = w) (hs : s ∈ ball z r) :
      s + c ∈ ball w r := by
    simpa [← hzw, dist_add_right] using hs
  refine ⟨fun s hs ↦ (hF.interior _ (hre hs)).comp_of_eq
    (analyticAt_id.add analyticAt_const) rfl, ?_, fun y hy ↦ ?_⟩
  · obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    have hball₀ : ∀ s ∈ ball ((a - c : ℝ) : ℂ) r, s + c ∈ ball (a : ℂ) r :=
      fun s ↦ hball (by push_cast; ring)
    refine ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball₀ s hs)).comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      by simpa [sub_add_cancel] using hga, fun s hs hsre ↦ ?_⟩
    rw [hFg _ (hball₀ s hs) (hre hsre)]
    congr 2; push_cast; ring
  · obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    have hball_y : ∀ s ∈ ball (((a - c : ℝ) : ℂ) + y * I) r,
        s + c ∈ ball ((a : ℂ) + y * I) r :=
      fun s ↦ hball (by push_cast; ring)
    exact ⟨r, hr, fun s ↦ g (s + c),
      fun s hs ↦ (hg _ (hball_y s hs)).comp_of_eq (analyticAt_id.add analyticAt_const) rfl,
      fun s hs hsre ↦ hFg _ (hball_y s hs) (hre hsre)⟩

/-- **The product rule**: if `F` has a pole of order `k + 1` and `G` one of order `l + 1` at `a`,
then `F G` has a pole of order `k + l + 2` there, and the leading coefficients multiply. -/
theorem PoleBoundary.mul (hF : PoleBoundary F a k A) (hG : PoleBoundary G a l B) :
    PoleBoundary (fun s ↦ F s * G s) a (k + l + 1) (A * B) where
  interior s hs := (hF.interior s hs).mul (hG.interior s hs)
  pole := by
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    obtain ⟨ρ, hρ, h, hh, hha, hGh⟩ := hG.pole
    obtain ⟨δ, hδ, hg', hh', hball⟩ := exists_ball_analyticOnNhd_pair hr hρ hg hh
    refine ⟨δ, hδ, _, hg'.mul hh', by simp [hga, hha], fun s hs hre ↦ ?_⟩
    rw [hFg s (hball s hs).1 hre, hGh s (hball s hs).2 hre, div_mul_div_comm, ← pow_add]
    ring_nf
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    obtain ⟨ρ, hρ, h, hh, hGh⟩ := hG.away y hy
    obtain ⟨δ, hδ, hg', hh', hball⟩ := exists_ball_analyticOnNhd_pair hr hρ hg hh
    exact ⟨δ, hδ, _, hg'.mul hh',
      fun s hs hre ↦ by rw [hFg s (hball s hs).1 hre, hGh s (hball s hs).2 hre]⟩

/-- **Powers**: if `F` has a pole of order `k + 1` at `a`, then `F ^ (n + 1)` has a pole of order
`(k + 1) (n + 1)`, written `k n + k + n + 1`, with leading coefficient `A ^ (n + 1)`. -/
theorem PoleBoundary.pow (hF : PoleBoundary F a k A) (n : ℕ) :
    PoleBoundary (fun s ↦ F s ^ (n + 1)) a (k * n + k + n) (A ^ (n + 1)) := by
  induction n with
  | zero => simpa using hF
  | succ n ih =>
    have h := ih.mul hF
    rw [show k * n + k + n + k + 1 = k * (n + 1) + k + (n + 1) by ring, ← pow_succ] at h
    simpa only [← pow_succ] using h

/-- The model pole: `A / (s - a) ^ (k + 1)` satisfies `PoleBoundary` with the constant numerator
`A`, for every real `a` and `A`. -/
theorem poleBoundary_const_div_pow (a A : ℝ) (k : ℕ) :
    PoleBoundary (fun s ↦ (A : ℂ) / (s - a) ^ (k + 1)) a k A :=
  .of_analyticAt
    (fun s _ hs ↦ analyticAt_const.div (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hs)))
    ⟨1, one_pos, fun _ ↦ A, analyticOnNhd_const, rfl, fun _ _ _ ↦ rfl⟩

/-- Characterization of `PoleBoundary` for the model pole `s ↦ A / (s - a) ^ (k + 1)`. -/
@[simp]
theorem poleBoundary_const_div_pow_iff (a A B : ℝ) (k : ℕ) :
    PoleBoundary (fun s ↦ (A : ℂ) / (s - a) ^ (k + 1)) a k B ↔ B = A :=
  ⟨fun h ↦ h.unique (poleBoundary_const_div_pow a A k),
    fun h ↦ h ▸ poleBoundary_const_div_pow a A k⟩

/-- Any function holomorphic at every point of the closed right half-plane `Re s ≥ a` satisfies
`PoleBoundary F a k 0` for every `k`. -/
theorem poleBoundary_of_analyticOnNhd (hF : AnalyticOnNhd ℂ F {s : ℂ | a ≤ s.re}) (k : ℕ) :
    PoleBoundary F a k 0 := by
  obtain ⟨r, hr, hFr⟩ := (hF a (by simp)).exists_ball_analyticOnNhd
  refine .of_analyticAt (fun s hs _ ↦ hF s hs)
    ⟨r, hr, fun s ↦ F s * (s - a) ^ (k + 1),
      hFr.mul ((analyticOnNhd_id.sub analyticOnNhd_const).pow _),
      by simp [zero_pow (Nat.succ_ne_zero k)], fun s _ hre ↦ ?_⟩
  have hsa : (s - (a : ℂ)) ^ (k + 1) ≠ 0 :=
    pow_ne_zero _ (sub_ne_zero.2 fun h ↦ by simp [h] at hre)
  exact (mul_div_cancel_right₀ _ hsa).symm

/-- The zero function satisfies `PoleBoundary 0 a k A` exactly when `A = 0`: a nonzero leading
coefficient forces an actual pole. -/
@[simp]
theorem poleBoundary_zero_iff : PoleBoundary 0 a k A ↔ A = 0 := by
  have h0 : PoleBoundary 0 a k 0 := (poleBoundary_const_div_pow a 0 k).congr (by simp)
  exact ⟨fun h ↦ h.unique h0, fun h ↦ h ▸ h0⟩

/-- The Riemann zeta function has a simple pole at `1` with residue `1` and continues
holomorphically across the rest of the line `Re s = 1`. The numerator is `riemannZeta₁`, the
continuation of `(s - 1) ζ(s)` across `s = 1`. -/
theorem poleBoundary_riemannZeta : PoleBoundary riemannZeta 1 0 1 :=
  .of_analyticAt (fun s _ hs ↦ analyticOn_riemannZeta s (by simpa using hs))
    ⟨1, one_pos, riemannZeta₁, fun s _ ↦ differentiable_riemannZeta₁.analyticAt s, by simp,
      fun s _ hre ↦ by
        have hs : s ≠ 1 := fun h ↦ by simp [h] at hre
        rw [riemannZeta_eq_inv_sub_mul hs]
        simp [div_eq_inv_mul]⟩

/-- The powers `ζ ^ (n + 1)` have a pole of order `n + 1` at `1` with leading coefficient `1`. -/
theorem poleBoundary_riemannZeta_pow (n : ℕ) :
    PoleBoundary (fun s ↦ riemannZeta s ^ (n + 1)) 1 n 1 := by
  simpa using poleBoundary_riemannZeta.pow n

/-! ### Necessity of continuation away from the real pole: the dyadic denominator -/

/-- On `Re s > 1`, `1 - exp ((1 - s) * log 2)` is nonvanishing since
`‖exp ((1 - s) * log 2)‖ < 1`. -/
private theorem one_sub_cexp_log_two_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1 - cexp ((1 - s) * Real.log 2) ≠ 0 := by
  intro h
  have heq : cexp ((1 - s) * Real.log 2) = 1 := (sub_eq_zero.1 h).symm
  have hnorm : ‖cexp ((1 - s) * Real.log 2)‖ = 1 := by rw [heq, norm_one]
  rw [norm_exp] at hnorm
  have hre : ((1 - s) * Real.log 2).re < 0 := by
    rw [mul_comm, re_ofReal_mul, sub_re, one_re]
    exact mul_neg_of_pos_of_neg (Real.log_pos one_lt_two) (sub_neg.2 hs)
  have hlt : Real.exp (((1 - s) * Real.log 2).re) < 1 := Real.exp_lt_one_iff.2 hre
  linarith

/-- The dyadic sum `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` is holomorphic on `Re s > 1`, so it
satisfies the `interior` clause of `PoleBoundary` at abscissa `1`. -/
theorem analyticOnNhd_inv_one_sub_cexp_log_two :
    AnalyticOnNhd ℂ (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) {s : ℂ | 1 < s.re} := by
  refine AnalyticOnNhd.inv (analyticOnNhd_const.sub ?_) fun s hs ↦
    one_sub_cexp_log_two_ne_zero hs
  exact fun s _ ↦ ((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp

/-- Near `s = 1`, `s ↦ (1 - exp ((1 - s) * log 2))⁻¹` has the local simple-pole form
`g s / (s - 1)` on a disc about `1` with `g` holomorphic and `g 1 = (Real.log 2)⁻¹`, so it
satisfies the `pole` clause of `PoleBoundary` at `a = 1`, `k = 0`, `A = (Real.log 2)⁻¹`. -/
theorem exists_pole_germ_inv_one_sub_cexp_log_two :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (1 : ℂ) r) ∧
      g 1 = ((Real.log 2)⁻¹ : ℝ) ∧
      ∀ s ∈ ball (1 : ℂ) r, 1 < s.re →
        (1 - cexp ((1 - s) * Real.log 2))⁻¹ = g s / (s - 1) := by
  let denom : ℂ → ℂ := fun s ↦ 1 - cexp ((1 - s) * Real.log 2)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog2_ne : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 hlog2.ne'
  have hderiv : HasDerivAt denom (Real.log 2 : ℂ) 1 := by
    have h1 : HasDerivAt (fun s : ℂ ↦ (1 - s) * (Real.log 2 : ℂ)) (-(Real.log 2 : ℂ)) 1 := by
      simpa using ((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 1)).mul_const
        (Real.log 2 : ℂ)
    have h2 : HasDerivAt denom (0 - cexp ((1 - (1 : ℂ)) * Real.log 2) * -(Real.log 2 : ℂ)) 1 :=
      (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub h1.cexp
    simpa [denom] using h2
  have hdenom_an : AnalyticOnNhd ℂ denom univ := fun s _ ↦
    analyticAt_const.sub (((analyticAt_const.sub analyticAt_id).mul analyticAt_const).cexp)
  let q : ℂ → ℂ := dslope denom 1
  have hq_an : AnalyticOnNhd ℂ q univ := hdenom_an.dslope 1
  have hq1_val : q 1 = (Real.log 2 : ℂ) := by
    simp only [q, dslope_same, hderiv.deriv]
  have hq1 : q 1 ≠ 0 := hq1_val ▸ hlog2_ne
  obtain ⟨r, hr, hq_ne⟩ :=
    Metric.eventually_nhds_iff_ball.1 ((hq_an 1 (mem_univ 1)).continuousAt.eventually_ne hq1)
  refine ⟨r, hr, fun s ↦ (q s)⁻¹, (hq_an.mono (subset_univ _)).inv hq_ne,
    by simp [hq1_val], fun s _ hsre ↦ ?_⟩
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hsre
  have hsub0 : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hqs : q s = denom s / (s - 1) := by
    have hd1 : denom 1 = 0 := by simp [denom]
    simp only [q, dslope_of_ne denom hs1, slope_def_field, hd1, sub_zero]
  dsimp only [denom] at hqs ⊢
  have hd0 : 1 - cexp ((1 - s) * Real.log 2) ≠ 0 := one_sub_cexp_log_two_ne_zero hsre
  rw [hqs]
  field_simp

/-- Evaluation of `cexp ((1 - s) * log 2)` along the horizontal approach
`s = 1 + (2π / log 2) i + ε` to the off-real boundary pole `1 + (2π / log 2) i`. -/
private theorem cexp_one_sub_two_pi_div_log_two (ε : ℝ) :
    cexp ((1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2) =
      (Real.exp (-ε * Real.log 2) : ℂ) := by
  have hlog2_ne : (Real.log 2 : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.log_pos one_lt_two).ne'
  have harg : (1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2 =
      ((-ε * Real.log 2 : ℝ) : ℂ) - 2 * Real.pi * I := by
    have hy_mul : ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Real.log 2 = 2 * Real.pi := by
      push_cast
      exact div_mul_cancel₀ _ hlog2_ne
    calc
      (1 - (((1 : ℂ) + (2 * Real.pi / Real.log 2 : ℝ) * I) + ε)) * Real.log 2
          = -(ε : ℂ) * Real.log 2 - ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * Real.log 2 * I := by
        ring
      _ = ((-ε * Real.log 2 : ℝ) : ℂ) - 2 * Real.pi * I := by
        rw [hy_mul]
        push_cast
        ring
  rw [harg, Complex.exp_periodic.sub_eq, ofReal_exp]

/-- Despite being holomorphic on `Re s > 1` with a simple pole at `s = 1`, the dyadic function
`s ↦ (1 - exp ((1 - s) * log 2))⁻¹` satisfies `PoleBoundary` at abscissa `1` for **no** pole order
`k + 1` and **no** leading coefficient `A`: its pole at `1 + (2π / log 2) i` violates the `away`
condition. -/
theorem not_poleBoundary_inv_one_sub_cexp_log_two (k : ℕ) (A : ℝ) :
    ¬ PoleBoundary (fun s ↦ (1 - cexp ((1 - s) * Real.log 2))⁻¹) 1 k A := by
  intro h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  let y : ℝ := 2 * Real.pi / Real.log 2
  have hy : y ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hlog2.ne'
  obtain ⟨r, hr, g, hg, hF⟩ := h.away y hy
  let z₀ : ℂ := (1 : ℂ) + y * I
  -- Along `s_ε = z₀ + ε` (`ε → 0⁺`), `1 - exp ((1 - s_ε) * log 2) = 1 - exp (-ε * log 2) → 0`
  -- while `g (z₀ + ε) → g z₀`, so `(1 - exp (-ε * log 2)) * g (z₀ + ε)` tends both to `1` and `0`.
  have hlim_g : Tendsto (fun ε : ℝ ↦ g (z₀ + ε)) (𝓝[>] 0) (𝓝 (g z₀)) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ g (z₀ + ε)) 0 :=
      (hg z₀ (mem_ball_self hr)).continuousAt.comp_of_eq
        (continuousAt_const.add continuous_ofReal.continuousAt) (by simp)
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlim_d : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ)) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hprod0 : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim_d.mul hlim_g
  have hev_one : (fun ε : ℝ ↦ (1 - Real.exp (-ε * Real.log 2) : ℂ) * g (z₀ + ε)) =ᶠ[𝓝[>] 0]
      fun _ ↦ (1 : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with ε ⟨hε0, hεr⟩
    have hFε := hF (z₀ + ε) (by simp [z₀, dist_eq_norm, abs_of_pos hε0, hεr]) (by simp [z₀, hε0])
    rw [cexp_one_sub_two_pi_div_log_two ε] at hFε
    have hd_ne : (1 - (Real.exp (-ε * Real.log 2) : ℂ)) ≠ 0 := by
      have hlt : Real.exp (-ε * Real.log 2) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
      exact sub_ne_zero.2 (by exact_mod_cast hlt.ne')
    rw [← hFε, mul_inv_cancel₀ hd_ne]
  exact one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' hev_one.symm) hprod0)

end TauCeti.HigherPoleTauberian

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
* `PoleBoundary.unique`, `PoleBoundary.order_le_of_ne_zero` and `PoleBoundary.order_unique`: the
  leading coefficient is determined by `F`, and so is the order of the pole when the coefficient
  is nonzero.
* `poleBoundary_congr`: only the values on the open half-plane matter.
* `PoleBoundary.mul_analyticOnNhd`, `PoleBoundary.div_id`, `PoleBoundary.comp_const_mul`,
  `PoleBoundary.mul` and `PoleBoundary.pow`: multiplication by a function holomorphic on the
  closed half-plane, division by the argument, rescaling of the variable, and products, under
  which the pole orders add.
* `poleBoundary_const_div_pow`, `poleBoundary_riemannZeta` and `poleBoundary_riemannZeta_pow`:
  the model pole `A / (s - a) ^ (k + 1)`, and the Riemann zeta function and its powers at `1`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) 71 (1954),
  213–242, Théorème III (§5.2.1, pp. 235–236), of which `PoleBoundary` is the hypothesis for an
  integer exponent `k + 1`.
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

/-- Two germs holomorphic on balls about `z` multiply to a germ holomorphic on a smaller ball
about `z`, contained in both. -/
private lemma exists_ball_analyticOnNhd_mul {z : ℂ} {r ρ : ℝ} {g h : ℂ → ℂ} (hr : 0 < r)
    (hρ : 0 < ρ) (hg : AnalyticOnNhd ℂ g (ball z r)) (hh : AnalyticOnNhd ℂ h (ball z ρ)) :
    ∃ δ : ℝ, 0 < δ ∧ AnalyticOnNhd ℂ (fun s ↦ g s * h s) (ball z δ) ∧
      ∀ s ∈ ball z δ, s ∈ ball z r ∧ s ∈ ball z ρ :=
  ⟨min r ρ, lt_min hr hρ, (hg.mono (ball_subset_ball (min_le_left _ _))).mul
      (hh.mono (ball_subset_ball (min_le_right _ _))),
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

/-- If `F` has a pole of order at most `k + 1` at `a`, then it has no pole of higher order `l + 1`
with a nonzero leading coefficient there. -/
theorem PoleBoundary.order_le_of_ne_zero (hA : PoleBoundary F a k A)
    (hB : PoleBoundary F a l B) (hB0 : B ≠ 0) : l ≤ k := by
  by_contra! hkl
  have := nhdsWithin_setOfPred_lt_re_neBot (s := (a : ℂ)) (ofReal_re a).ge
  have hzero : Tendsto (fun s ↦ (s - a) ^ (l - k) * ((s - a) ^ (k + 1) * F s))
      (𝓝[{s : ℂ | a < s.re}] (a : ℂ)) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℂ ↦ (s - a) ^ (l - k)) (𝓝[{s : ℂ | a < s.re}] (a : ℂ)) (𝓝 0) := by
      have : Tendsto (fun s : ℂ ↦ (s - a) ^ (l - k)) (𝓝 (a : ℂ)) (𝓝 ((a - a) ^ (l - k))) :=
        ((continuous_id.sub continuous_const).pow _).tendsto _
      rw [sub_self, zero_pow (Nat.sub_ne_zero_of_lt hkl)] at this
      exact this.mono_left nhdsWithin_le_nhds
    simpa using h0.mul hA.tendsto_sub_pow_mul
  have hpow : (fun s : ℂ ↦ (s - a) ^ (l - k) * ((s - a) ^ (k + 1) * F s)) =
      fun s ↦ (s - a) ^ (l + 1) * F s := by
    ext s
    rw [← mul_assoc, ← pow_add]
    congr 2
    omega
  rw [hpow] at hzero
  exact hB0 (by exact_mod_cast tendsto_nhds_unique hB.tendsto_sub_pow_mul hzero)

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
    obtain ⟨δ, hδ, hgH, hball⟩ := exists_ball_analyticOnNhd_mul hr hρ hg hHρ
    refine ⟨δ, hδ, _, hgH, by simp [hga, hHa], fun s hs hre ↦ ?_⟩
    rw [hFg s (hball s hs).1 hre, div_mul_eq_mul_div]
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    obtain ⟨ρ, hρ, hHρ⟩ := (hH ((a : ℂ) + y * I) (by simp)).exists_ball_analyticOnNhd
    obtain ⟨δ, hδ, hgH, hball⟩ := exists_ball_analyticOnNhd_mul hr hρ hg hHρ
    exact ⟨δ, hδ, _, hgH, fun s hs hre ↦ by rw [hFg s (hball s hs).1 hre]⟩

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

/-- **The product rule**: if `F` has a pole of order `k + 1` and `G` one of order `l + 1` at `a`,
then `F G` has a pole of order `k + l + 2` there, and the leading coefficients multiply. -/
theorem PoleBoundary.mul (hF : PoleBoundary F a k A) (hG : PoleBoundary G a l B) :
    PoleBoundary (fun s ↦ F s * G s) a (k + l + 1) (A * B) where
  interior s hs := (hF.interior s hs).mul (hG.interior s hs)
  pole := by
    obtain ⟨r, hr, g, hg, hga, hFg⟩ := hF.pole
    obtain ⟨ρ, hρ, h, hh, hha, hGh⟩ := hG.pole
    obtain ⟨δ, hδ, hgh, hball⟩ := exists_ball_analyticOnNhd_mul hr hρ hg hh
    refine ⟨δ, hδ, _, hgh, by simp [hga, hha], fun s hs hre ↦ ?_⟩
    rw [hFg s (hball s hs).1 hre, hGh s (hball s hs).2 hre, div_mul_div_comm, ← pow_add]
    ring_nf
  away y hy := by
    obtain ⟨r, hr, g, hg, hFg⟩ := hF.away y hy
    obtain ⟨ρ, hρ, h, hh, hGh⟩ := hG.away y hy
    obtain ⟨δ, hδ, hgh, hball⟩ := exists_ball_analyticOnNhd_mul hr hρ hg hh
    exact ⟨δ, hδ, _, hgh, fun s hs hre ↦ by rw [hFg s (hball s hs).1 hre, hGh s (hball s hs).2 hre]⟩

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

end TauCeti.HigherPoleTauberian

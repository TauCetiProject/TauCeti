/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order

/-!
# The analytic order of products, power maps and derivatives

Extensions of Mathlib's analytic-order calculus: `analyticOrderNatAt` respects eventual equality,
the order is additive over finite products, composing with `q ↦ q ^ N` at `0` multiplies the order
by `N`, the power map `w ↦ w ^ m` recentred at `0` has order `m` there for `m ≠ 0`, the
recentred function `f · - f x` has order `1` at `x` exactly when `deriv f x ≠ 0`, and the order is
monotone under domination (`=O`), hence invariant under equivalence up to constant factors (`=Θ`).
The finiteness a zero count also needs is
`TauCeti.finite_setOf_mem_and_eq_zero_of_isCompact`, provided by
`TauCeti.Analysis.Analytic.IsolatedZeros`, which mentions no order.

## Main declarations

* `AnalyticAt.exists_analyticOrderAt_monomial_sub_eq_min`: outside at most two scalar
  coefficients, subtraction of a scalar monomial has the minimum of the two orders.
* `TauCeti.analyticOrderNatAt_congr`: eventual equality preserves the natural analytic order.
* `TauCeti.analyticOrderAt_prod`: the order of `∏ i ∈ s, F i` is `∑ i ∈ s`, of the orders.
* `TauCeti.analyticOrderAt_comp_pow_zero`: the order of `q ↦ f (q ^ N)` at `0` is `N` times
  the order of `f` at `0`.
* `TauCeti.analyticOrderAt_pow_sub_zero_pow`: the order of `w ↦ w ^ m - 0 ^ m` at `0` is `m`
  for `m ≠ 0`.
* `AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero`: `f · - f x` has order `1` at `x`
  exactly when `deriv f x ≠ 0`, the `iff` form of Mathlib's
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`.
* `AnalyticAt.analyticOrderAt_le_of_isBigO` and `AnalyticAt.analyticOrderAt_eq_of_isTheta`: an
  analytic function dominated by `f` vanishes to at least the order of `f`, so analytic functions
  equivalent up to constant factors have the same order.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft from which this file ports the eventual-equality,
  product, power-map and derivative lemmas onto the current Mathlib pin.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {z₀ : 𝕜}

/-- Functions that agree near a point have the same natural analytic order there. -/
theorem analyticOrderNatAt_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f g : 𝕜 → E} (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderNatAt f z₀ = analyticOrderNatAt g z₀ := by
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_congr hfg]

/-- The order is additive when taking a finite product of analytic functions. -/
theorem analyticOrderAt_prod {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜}
    (hF : ∀ i ∈ s, AnalyticAt 𝕜 (F i) z₀) :
    analyticOrderAt (∏ i ∈ s, F i) z₀ = ∑ i ∈ s, analyticOrderAt (F i) z₀ := by
  induction s using Finset.cons_induction with
  | empty => simp [analyticOrderAt_eq_zero]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      analyticOrderAt_mul (hF a (Finset.mem_cons_self a s))
        (Finset.analyticAt_prod _ fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)),
      ih fun i hi ↦ hF i (Finset.mem_cons_of_mem hi)]

/-- The analytic order of `q ↦ f (q ^ N)` at `0` is `N` times the analytic order of `f`
at `0`. -/
lemma analyticOrderAt_comp_pow_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) {N : ℕ} (hN : 0 < N) :
    analyticOrderAt (fun q : 𝕜 ↦ f (q ^ N)) 0 = analyticOrderAt f 0 * N := by
  set g : 𝕜 → 𝕜 := fun q ↦ q ^ N with hg_def
  have hzero : g 0 = 0 := zero_pow hN.ne'
  have h_sub_eq : (fun x : 𝕜 ↦ g x - 0) = (id : 𝕜 → 𝕜) ^ N := funext fun x ↦ by simp [hg_def]
  -- The composite is definitionally the power lambda; `show … from rfl` records the
  -- identification once so the composition rule applies.
  rw [show (fun q : 𝕜 ↦ f (q ^ N)) = f ∘ g from rfl,
    AnalyticAt.analyticOrderAt_comp (hzero.symm ▸ hf) (analyticAt_id.pow N), hzero, h_sub_eq,
    analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- The power map `w ↦ w ^ m`, recentred at `0`, has analytic order `m` at `0` when `m ≠ 0`. -/
theorem analyticOrderAt_pow_sub_zero_pow {m : ℕ} (hm : m ≠ 0) :
    analyticOrderAt (fun w : 𝕜 ↦ w ^ m - 0 ^ m) 0 = m := by
  have hpow : (fun w : 𝕜 ↦ w ^ m - 0 ^ m) = (· - 0) ^ m := funext fun w ↦ by simp [zero_pow hm]
  rw [hpow, analyticOrderAt_centeredMonomial]

/-- A function analytic at `x` has a simple zero of `f · - f x` at `x` exactly when its
derivative at `x` does not vanish: the `iff` form of Mathlib's
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`. -/
theorem _root_.AnalyticAt.analyticOrderAt_sub_eq_one_iff_deriv_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [CharZero 𝕜] {f : 𝕜 → E} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) :
    analyticOrderAt (f · - f x) x = 1 ↔ deriv f x ≠ 0 := by
  rw [← hf.analyticOrderAt_deriv_add_one, ← hf.deriv.analyticOrderAt_eq_zero]
  simp

/-- A function analytic at `z₀` and dominated there by `f` vanishes to at least the order of `f`
at `z₀`. No analyticity of `f` is needed: a non-analytic `f` has order `0`. -/
theorem _root_.AnalyticAt.analyticOrderAt_le_of_isBigO {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → E} {g : 𝕜 → F}
    (hg : AnalyticAt 𝕜 g z₀) (hgf : g =O[𝓝 z₀] f) :
    analyticOrderAt f z₀ ≤ analyticOrderAt g z₀ := by
  by_cases hf : AnalyticAt 𝕜 f z₀
  swap
  · simp [analyticOrderAt_of_not_analyticAt hf]
  by_cases hftop : analyticOrderAt f z₀ = ⊤
  · -- a function dominated by one vanishing near `z₀` vanishes near `z₀`
    rw [hftop, top_le_iff, analyticOrderAt_eq_top]
    exact Asymptotics.isBigO_zero_right_iff.1
      (hgf.trans_eventuallyEq (analyticOrderAt_eq_top.1 hftop))
  by_cases hgtop : analyticOrderAt g z₀ = ⊤
  · simp [hgtop]
  rw [← Nat.cast_analyticOrderNatAt hftop, ← Nat.cast_analyticOrderNatAt hgtop, Nat.cast_le]
  by_contra! hlt
  -- otherwise `(z - z₀) ^ b`, for `b` the order of `g`, would be negligible compared to itself
  have hpow : (fun z => (z - z₀) ^ analyticOrderNatAt f z₀) =o[𝓝 z₀]
      fun z => (z - z₀) ^ analyticOrderNatAt g z₀ :=
    Asymptotics.isLittleO_norm_norm.1 <| by
      simpa only [norm_pow] using Asymptotics.isLittleO_pow_sub_pow_sub z₀ hlt
  refine Asymptotics.isLittleO_irrefl' ?_ <|
    ((hg.isTheta_pow_sub hgtop).symm.isBigO.trans hgf).trans_isLittleO
      ((hf.isTheta_pow_sub hftop).isBigO.trans_isLittleO hpow)
  exact ((eventually_nhdsWithin_of_forall (s := {z₀}ᶜ) fun z hz =>
    norm_ne_zero_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hz))).frequently).filter_mono
      nhdsWithin_le_nhds

/-- Two functions analytic at `z₀` that are equivalent up to constant factors near `z₀` vanish to
the same order there. -/
theorem _root_.AnalyticAt.analyticOrderAt_eq_of_isTheta {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → E} {g : 𝕜 → F}
    (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) (hfg : f =Θ[𝓝 z₀] g) :
    analyticOrderAt f z₀ = analyticOrderAt g z₀ :=
  le_antisymm (hg.analyticOrderAt_le_of_isBigO hfg.2) (hf.analyticOrderAt_le_of_isBigO hfg.isBigO)

end TauCeti

/-- Outside zero and at most one additional scalar, subtracting an analytic germ from
a scalar multiple of a monomial has order equal to the minimum of their orders. The
exceptional scalar accounts for cancellation when the two orders coincide. -/
theorem AnalyticAt.exists_analyticOrderAt_monomial_sub_eq_min {𝕜 : Type*}
    [NontriviallyNormedField 𝕜] {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f 0) (N : ℕ) :
    ∃ b : 𝕜, ∀ c : 𝕜, c ≠ 0 → c ≠ b →
      analyticOrderAt (fun t ↦ c * t ^ N - f t) 0 = min (N : ℕ∞) (analyticOrderAt f 0) := by
  have hmono (c : 𝕜) (hc : c ≠ 0) :
      analyticOrderAt (fun t : 𝕜 ↦ c * t ^ N) 0 = N := by
    apply (analyticAt_const.mul (analyticAt_id.pow N)).analyticOrderAt_eq_natCast.2
    exact ⟨fun _ ↦ c, analyticAt_const, hc, .of_forall fun t ↦ by
      simp [smul_eq_mul, mul_comm]⟩
  by_cases heq : analyticOrderAt f 0 = N
  · obtain ⟨g, hg, -, hfg⟩ := hf.analyticOrderAt_eq_natCast.1 heq
    refine ⟨g 0, fun c _ hcb ↦ ?_⟩
    rw [heq, min_self]
    apply ((analyticAt_const.mul (analyticAt_id.pow N)).sub hf).analyticOrderAt_eq_natCast.2
    refine ⟨fun t ↦ c - g t, analyticAt_const.sub hg, sub_ne_zero.2 hcb, ?_⟩
    filter_upwards [hfg] with t ht
    simp only [sub_zero, smul_eq_mul, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] at ht ⊢
    rw [ht]
    ring
  · refine ⟨0, fun c hc _ ↦ ?_⟩
    have hne : analyticOrderAt (fun t : 𝕜 ↦ c * t ^ N) 0 ≠ analyticOrderAt (-f) 0 := by
      simpa [hmono c hc] using Ne.symm heq
    have hsum := analyticOrderAt_add_of_ne hne
    rw [analyticOrderAt_neg, hmono c hc] at hsum
    simpa only [Pi.add_def, Pi.neg_def, sub_eq_add_neg] using hsum

end

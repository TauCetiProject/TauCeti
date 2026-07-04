/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# The residue of a meromorphic function

For `f : ℂ → ℂ` and `z₀ : ℂ`, the **residue** `TauCeti.Contour.residue f z₀` is the order-`(−1)`
Laurent coefficient of `f` at `z₀` — the quantity summed in Cauchy's residue theorem. It is built
directly on Mathlib's `meromorphicOrderAt` / analytic-part API rather than a parallel
order-of-vanishing notion: writing `f z = (z − z₀) ^ n • g z` near `z₀` with `g` analytic and
`g z₀ ≠ 0` (where `n = meromorphicOrderAt f z₀`), the order-`(−1)` coefficient is the Taylor
coefficient of `g` at index `−1 − n`, i.e. `iteratedDeriv (−1 − n) g z₀ / (−1 − n)!`. The residue
is `0` at a point where `f` is analytic (`n ≥ 0`), and at a **simple pole** (`n = −1`) it is the
leading Laurent coefficient `meromorphicTrailingCoeffAt f z₀ = lim_{z→z₀} (z − z₀) · f z`.

As an unconditional value it is junk (`0`) when `f` is not meromorphic at `z₀`.

## Main definitions

* `TauCeti.Contour.residue` — the residue of `f` at `z₀`.

## Main results

* `TauCeti.Contour.residue_eq_of_order_lt_zero` — the characteristic value: from a reduced local
  presentation `f =ᶠ[𝓝[≠] z₀] (· − z₀) ^ n • g` with `g` analytic, `g z₀ ≠ 0`, and `n < 0`, the
  residue is `iteratedDeriv (−1 − n) g z₀ / (−1 − n)!`, independently of the presentation.
* `TauCeti.Contour.residue_congr_nhdsNE` — the residue depends only on the germ of `f` on a
  punctured neighborhood of `z₀`.
* `TauCeti.Contour.residue_eq_zero_of_analyticAt` — the residue vanishes where `f` is analytic.
* `TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` — at a simple pole the
  residue is the leading Laurent (trailing) coefficient.

This is a Layer 0 object of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`ForMathlib/GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`), specialised to the
raw-function design of the contour-integration roadmap and defined against Mathlib's
`meromorphicOrderAt` / `meromorphicTrailingCoeffAt` API.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- The **residue** of `f` at `z₀`: the order-`(−1)` Laurent coefficient. When `f` is meromorphic at
`z₀` with a pole (`meromorphicOrderAt f z₀ = n < 0`), it is the Taylor coefficient at index `−1 − n`
of the analytic part `g` (with `f z = (z − z₀) ^ n • g z` near `z₀`); it is `0` when `f` is analytic
at `z₀` (`n ≥ 0`) and junk (`0`) when `f` is not meromorphic at `z₀`. See
`residue_eq_of_order_lt_zero` for the characteristic value from an arbitrary presentation and
`residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one` for the simple-pole value. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  haveI : Decidable (MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0) := Classical.propDecidable _
  if h : MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0 then
    iteratedDeriv (-1 - (meromorphicOrderAt f z₀).untop₀).toNat
        ((meromorphicOrderAt_ne_top_iff h.1).1 (ne_top_of_lt h.2)).choose z₀ /
      ((-1 - (meromorphicOrderAt f z₀).untop₀).toNat.factorial : ℂ)
  else 0

/-- **Characteristic value of the residue at a pole.** If `f z = (z − z₀) ^ n • g z` near `z₀` (on
the punctured neighborhood) with `g` analytic at `z₀`, `g z₀ ≠ 0`, and `n < 0`, then the residue is
the Taylor coefficient of `g` at index `−1 − n`. This is the standard reduced analytic presentation;
the order equality `meromorphicOrderAt f z₀ = n` is derived from it, and the value is independent of
the chosen presentation `g`. -/
theorem residue_eq_of_order_lt_zero {f g : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hlt : n < 0) (hg : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n • g z) :
    residue f z₀ = iteratedDeriv (-1 - n).toNat g z₀ / ((-1 - n).toNat.factorial : ℂ) := by
  have hf : MeromorphicAt f z₀ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mpr ⟨n, g, hg, hfg⟩
  have hn : meromorphicOrderAt f z₀ = n :=
    (meromorphicOrderAt_eq_int_iff hf).mpr ⟨g, hg, hg_ne, hfg⟩
  have hlt' : meromorphicOrderAt f z₀ < 0 := by rw [hn]; exact_mod_cast hlt
  have huntop : (meromorphicOrderAt f z₀).untop₀ = n := by rw [hn, WithTop.untop₀_coe]
  rw [residue, dif_pos ⟨hf, hlt'⟩]
  set g₀ := ((meromorphicOrderAt_ne_top_iff hf).1 (ne_top_of_lt hlt')).choose with hg₀
  rw [huntop]
  obtain ⟨hg₀_an, -, hg₀_eq⟩ :=
    ((meromorphicOrderAt_ne_top_iff hf).1 (ne_top_of_lt hlt')).choose_spec
  rw [← hg₀] at hg₀_an hg₀_eq
  have hne : g₀ =ᶠ[𝓝[≠] z₀] g := by
    filter_upwards [hg₀_eq, hfg, self_mem_nhdsWithin] with z hz1 hz2 hz3
    rw [huntop] at hz1
    have hzne : (z - z₀) ^ n ≠ 0 := zpow_ne_zero n (sub_ne_zero.mpr hz3)
    have hcancel : (z - z₀) ^ n • g₀ z = (z - z₀) ^ n • g z := hz1.symm.trans hz2
    simpa only [smul_eq_mul] using mul_left_cancel₀ hzne (by simpa only [smul_eq_mul] using hcancel)
  have hnhds : g₀ =ᶠ[𝓝 z₀] g :=
    (hg₀_an.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hg.continuousAt).1 hne
  exact congrArg (· / ((-1 - n).toNat.factorial : ℂ)) (hnhds.iteratedDeriv_eq (-1 - n).toNat)

/-- If `f` is not meromorphic at `z₀`, its residue is `0` by definition. -/
@[simp]
theorem residue_of_not_meromorphicAt {f : ℂ → ℂ} {z₀ : ℂ} (h : ¬ MeromorphicAt f z₀) :
    residue f z₀ = 0 := by
  rw [residue, dif_neg]
  rintro ⟨h1, -⟩
  exact h h1

/-- The residue vanishes at a point where `f` has nonnegative meromorphic order (in particular where
`f` is analytic): there is no order-`(−1)` Laurent coefficient. -/
@[simp]
theorem residue_eq_zero_of_meromorphicOrderAt_nonneg {f : ℂ → ℂ} {z₀ : ℂ}
    (h : 0 ≤ meromorphicOrderAt f z₀) : residue f z₀ = 0 := by
  rw [residue, dif_neg]
  rintro ⟨-, h2⟩
  exact absurd h2 (not_lt.mpr h)

/-- The residue vanishes where `f` is analytic. -/
@[simp]
theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    residue f z₀ = 0 :=
  residue_eq_zero_of_meromorphicOrderAt_nonneg hf.meromorphicOrderAt_nonneg

/-- The residue depends only on the germ of `f` on a punctured neighborhood of `z₀`: functions
agreeing near (but not necessarily at) `z₀` have the same residue. -/
theorem residue_congr_nhdsNE {f g : ℂ → ℂ} {z₀ : ℂ} (h : f =ᶠ[𝓝[≠] z₀] g) :
    residue f z₀ = residue g z₀ := by
  have hord : meromorphicOrderAt f z₀ = meromorphicOrderAt g z₀ := meromorphicOrderAt_congr h
  rcases lt_or_ge (meromorphicOrderAt g z₀) 0 with hlt | hge
  · have hgm : MeromorphicAt g z₀ := meromorphicAt_of_meromorphicOrderAt_ne_zero (ne_of_lt hlt)
    have hgn : meromorphicOrderAt g z₀ = ((meromorphicOrderAt g z₀).untop₀ : WithTop ℤ) :=
      (WithTop.coe_untop₀_of_ne_top (ne_top_of_lt hlt)).symm
    have hnlt : (meromorphicOrderAt g z₀).untop₀ < 0 := by
      have h0 := hlt; rw [hgn] at h0; exact_mod_cast h0
    obtain ⟨g₀, hg₀_an, hg₀_ne, hg₀_eq⟩ := (meromorphicOrderAt_ne_top_iff hgm).1 (ne_top_of_lt hlt)
    rw [residue_eq_of_order_lt_zero hnlt hg₀_an hg₀_ne (h.trans hg₀_eq),
      residue_eq_of_order_lt_zero hnlt hg₀_an hg₀_ne hg₀_eq]
  · rw [residue_eq_zero_of_meromorphicOrderAt_nonneg (f := f) (by rw [hord]; exact hge),
      residue_eq_zero_of_meromorphicOrderAt_nonneg (f := g) hge]

/-- At a **simple pole** (`meromorphicOrderAt f z₀ = −1`), the residue is the leading Laurent
coefficient `meromorphicTrailingCoeffAt f z₀`, i.e. `lim_{z→z₀} (z − z₀) · f z`. The `n = −1`
specialization of `residue_eq_of_order_lt_zero`: the Taylor coefficient at index `−1 − (−1) = 0` of
the analytic part `g` is just `g z₀`, which is the trailing coefficient. -/
@[simp]
theorem residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one {f : ℂ → ℂ} {z₀ : ℂ}
    (hord : meromorphicOrderAt f z₀ = -1) :
    residue f z₀ = meromorphicTrailingCoeffAt f z₀ := by
  have hf : MeromorphicAt f z₀ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 (by rw [hord]; decide)
  have htc : meromorphicTrailingCoeffAt f z₀ = g z₀ :=
    hg_an.meromorphicTrailingCoeffAt_of_eq_nhdsNE hg_eq
  have huntop : (meromorphicOrderAt f z₀).untop₀ = -1 := by
    rw [hord]; exact WithTop.untop₀_coe (-1 : ℤ)
  rw [huntop] at hg_eq
  rw [residue_eq_of_order_lt_zero (by decide) hg_an hg_ne hg_eq, htc]
  norm_num [iteratedDeriv_zero]

end TauCeti.Contour

end

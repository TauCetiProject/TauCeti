/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Residue
public import Mathlib.Analysis.Meromorphic.Order

/-!
# The residue at a simple pole as a limit

For `f : ℂ → ℂ` with a **simple pole** at `z₀` (`meromorphicOrderAt f z₀ = −1`), the residue
`TauCeti.Contour.residue f z₀` is the elementary limit `lim_{z→z₀} (z − z₀) · f z` — the textbook
recipe for computing residues at simple poles, which the roadmap names as the defining property of
the simple-pole residue. This file records that limit and its converse: the residue *equals* the
limit whenever `f` is meromorphic at `z₀` and the limit exists.

The order-`(−1)` Laurent coefficient of `f` at a simple pole is the trailing coefficient
`meromorphicTrailingCoeffAt f z₀` (via
`TauCeti.Contour.residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one`),
and Mathlib records that this trailing coefficient is the limit of `(· − z₀) ^ (−order) • f`
(`MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`). Here we phrase the statement directly on
`(z − z₀) · f z`, valid whenever the pole order is at most `1` (`−1 ≤ order`, so no pole or a simple
pole): at a genuine simple pole the limit is the residue, and where `f` is analytic (or has a higher
zero) both the residue and the limit are `0`.

The converse `residue_eq_of_tendsto_sub_mul` turns the limit into a *computation* rule: if
`(z − z₀) · f z` converges as `z → z₀`, then `f` has at most a simple pole there and the residue is
exactly that limit. This is the direction one uses in practice to read off a residue.

## Main results

* `TauCeti.Contour.tendsto_sub_mul_nhds_residue_of_order_eq_neg_one` — at a simple pole
  (`meromorphicOrderAt f z₀ = −1`), `(z − z₀) · f z → residue f z₀`.
* `TauCeti.Contour.tendsto_sub_mul_nhds_residue` — the same limit whenever `−1 ≤ meromorphicOrderAt
  f z₀` (at most a simple pole); the analytic case gives the limit `0 = residue f z₀`.
* `TauCeti.Contour.residue_eq_of_tendsto_sub_mul` — the converse: if `f` is meromorphic at `z₀` and
  `(z − z₀) · f z` converges to `L`, then `residue f z₀ = L`.

## Provenance

Adapted from the AINTLIB `LeanModularForms` project (the residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean`), and built on Mathlib's trailing-coefficient
limit API (`MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`) and the order/convergence
dictionary in `Mathlib/Analysis/Meromorphic/Order.lean`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {z₀ : ℂ}

/-- The order of `(z − z₀) · f z` at `z₀` is one more than the order of `f`: multiplying by the
simple factor `(· − z₀)` (order `1`) shifts the meromorphic order up by one. -/
private theorem meromorphicOrderAt_sub_mul (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt (fun z => (z - z₀) * f z) z₀ = 1 + meromorphicOrderAt f z₀ := by
  have hid : MeromorphicAt (fun z : ℂ => z - z₀) z₀ :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have h := meromorphicOrderAt_mul hid hf
  rwa [meromorphicOrderAt_id_sub_const] at h

/-- If `-1 ≤ x` in `WithTop ℤ`, then either `x = -1` (a simple pole) or `0 ≤ x` (no pole). -/
private theorem eq_neg_one_or_zero_le {x : WithTop ℤ} (h : -1 ≤ x) : x = -1 ∨ 0 ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact Or.inr le_top
  · lift x to ℤ using hx with n
    have hc1 : (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_cast
    have hc0 : (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) := by norm_cast
    rw [hc1, WithTop.coe_le_coe] at h
    rcases eq_or_lt_of_le h with heq | hlt
    · exact Or.inl (by rw [hc1, ← heq])
    · exact Or.inr (by rw [hc0, WithTop.coe_le_coe]; omega)

/-- If `0 ≤ 1 + x` in `WithTop ℤ`, then `-1 ≤ x`. -/
private theorem neg_one_le_of_zero_le_one_add {x : WithTop ℤ} (h : 0 ≤ 1 + x) : -1 ≤ x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · exact le_top
  · lift x to ℤ using hx with n
    have hc1 : (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) := by norm_cast
    have h' : (0 : ℤ) ≤ 1 + n := by exact_mod_cast h
    rw [hc1, WithTop.coe_le_coe]
    omega

/-- **The residue at a simple pole is `lim_{z→z₀} (z − z₀) · f z`.** If `f` has a simple pole at
`z₀` (`meromorphicOrderAt f z₀ = −1`), then `(z − z₀) · f z` converges to `residue f z₀` as
`z → z₀`. The residue is the order-`(−1)` Laurent coefficient, which at a simple pole is the
trailing coefficient `g z₀` of the analytic part `g` in `f z = (z − z₀)⁻¹ · g z`; multiplying by
`(z − z₀)` cancels the pole, leaving `g`, which is continuous. -/
theorem tendsto_sub_mul_nhds_residue_of_order_eq_neg_one (hord : meromorphicOrderAt f z₀ = -1) :
    Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 (residue f z₀)) := by
  have hf : MeromorphicAt f z₀ :=
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hord]; decide)
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_ne_top_iff hf).1 (by rw [hord]; decide)
  have huntop : (meromorphicOrderAt f z₀).untop₀ = -1 := by rw [hord]; exact WithTop.untop₀_coe (-1)
  have hres : residue f z₀ = g z₀ := by
    rw [residue_eq_meromorphicTrailingCoeffAt_of_order_eq_neg_one hord,
      hg_an.meromorphicTrailingCoeffAt_of_eq_nhdsNE hg_eq]
  rw [hres]
  have hcont : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    (hg_an.continuousAt.continuousWithinAt (s := {z₀}ᶜ)).tendsto
  refine hcont.congr' ?_
  filter_upwards [hg_eq, self_mem_nhdsWithin] with z hz hz0
  rw [huntop] at hz
  have hzne : z - z₀ ≠ 0 := sub_ne_zero.mpr (by simpa using hz0)
  rw [hz, zpow_neg_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hzne, one_mul]

/-- **The residue as a limit, at most a simple pole.** If `f` has at most a simple pole at `z₀`
(`−1 ≤ meromorphicOrderAt f z₀`), then `(z − z₀) · f z → residue f z₀` as `z → z₀`. Splits into the
genuine simple pole (order `−1`, via `tendsto_sub_mul_nhds_residue_of_order_eq_neg_one`) and the
analytic case (order `≥ 0`), where both the residue and the limit vanish because `(z − z₀) → 0`
while `f` stays bounded. -/
theorem tendsto_sub_mul_nhds_residue (hf : MeromorphicAt f z₀)
    (hord : -1 ≤ meromorphicOrderAt f z₀) :
    Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 (residue f z₀)) := by
  rcases eq_neg_one_or_zero_le hord with hpole | hge
  · exact tendsto_sub_mul_nhds_residue_of_order_eq_neg_one hpole
  · rw [residue_eq_zero_of_meromorphicOrderAt_nonneg hge]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf hge
    have hsub : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
      have h0 : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 0) := by
        simpa using (continuous_sub_right z₀).tendsto z₀
      exact h0.mono_left nhdsWithin_le_nhds
    simpa using hsub.mul hc

/-- **Computing a residue as a limit (converse).** If `f` is meromorphic at `z₀` and the product
`(z − z₀) · f z` converges to `L` as `z → z₀`, then `f` has at most a simple pole and
`residue f z₀ = L`.
A finite limit for `(z − z₀) · f z` forces its order to be nonnegative, hence `f` has order `≥ −1`;
the residue is then pinned down by `tendsto_sub_mul_nhds_residue` and uniqueness of limits. -/
theorem residue_eq_of_tendsto_sub_mul {L : ℂ} (hf : MeromorphicAt f z₀)
    (h : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 L)) :
    residue f z₀ = L := by
  have hg : MeromorphicAt (fun z : ℂ => (z - z₀) * f z) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).mul hf
  have hgnn : 0 ≤ meromorphicOrderAt (fun z => (z - z₀) * f z) z₀ :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hg).1 ⟨L, h⟩
  rw [meromorphicOrderAt_sub_mul hf] at hgnn
  exact tendsto_nhds_unique (tendsto_sub_mul_nhds_residue hf (neg_one_le_of_zero_le_one_add hgnn)) h

end TauCeti.Contour

end

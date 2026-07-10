/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.ArgumentPrinciple
public import TauCeti.Analysis.Contour.ResidueSimplePole

/-!
# The residue of the logarithmic derivative is the meromorphic order

For `f : ℂ → ℂ` meromorphic at `z₀` of order `n = meromorphicOrderAt f z₀`, the residue of the
logarithmic derivative there is exactly that order:
`TauCeti.Contour.residue (logDeriv f) z₀ = n`. This is the residue-form of the argument principle,
the identity `Res_{z₀}(f'/f) = ord_{z₀} f` that the roadmap names as the local statement its
contour form (`TauCeti.Contour.argumentPrinciple`) integrates: a zero of order `k` contributes
`+k` and a pole of order `k` contributes `−k`.

The mechanism is the simple-pole splitting of the logarithmic derivative
(`TauCeti.Contour.logDeriv_eventuallyEq_principalPart`): near `z₀` there is `g` analytic and
non-vanishing with `logDeriv f = n · (· − z₀)⁻¹ + logDeriv g` on a punctured neighbourhood. The
analytic tail `logDeriv g` contributes no residue, so only the simple-pole principal part
`n · (· − z₀)⁻¹` survives, and `residue (fun z => (z − z₀)⁻¹) z₀ = 1`.

The two elementary simple-pole residues used along the way are recorded as reusable lemmas: the
residue of `(· − z₀)⁻¹` is `1`, and the residue of `c · (· − z₀)⁻¹` is `c`.

## Main results

* `TauCeti.Contour.residue_sub_inv` — `residue (fun z => (z − z₀)⁻¹) z₀ = 1`.
* `TauCeti.Contour.residue_const_mul_sub_inv` — `residue (fun z => c · (z − z₀)⁻¹) z₀ = c`.
* `TauCeti.Contour.residue_logDeriv` — `residue (logDeriv f) z₀ = n` when
  `meromorphicOrderAt f z₀ = n`: the residue of `f'/f` is the order of `f` at `z₀`.

These are Layer 2 targets of the contour-integration roadmap, feeding the argument principle and,
ultimately, the valence formula's interior-orbit sum.

## Provenance

The simple-pole splitting `logDeriv_eventuallyEq_principalPart` and the residue API are adapted from
the AINTLIB `LeanModularForms` project (the argument-principle and residue material of
`ForMathlib/GeneralizedResidueTheory/Residue.lean` and
`.../Residue/GeneralizedTheoremBase.lean`, where the residue theorem is applied to `logDeriv f`),
here specialised to Mathlib's `meromorphicOrderAt` API and the raw-function design of the
contour-integration roadmap.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

open Filter Topology Complex

namespace TauCeti.Contour

/-- The residue of the elementary simple pole `(· − z₀)⁻¹` at `z₀` is `1`: since
`(z − z₀) · (z − z₀)⁻¹ → 1` as `z → z₀`, the simple-pole limit formula gives the residue. -/
theorem residue_sub_inv (z₀ : ℂ) : residue (fun z => (z - z₀)⁻¹) z₀ = 1 := by
  have hmero : MeromorphicAt (fun z => (z - z₀)⁻¹) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  refine residue_eq_of_tendsto_sub_mul hmero (tendsto_const_nhds.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (mul_inv_cancel₀ (sub_ne_zero.2 hz)).symm

/-- The residue of `c · (· − z₀)⁻¹` at `z₀` is `c`: scaling the elementary simple pole scales its
residue. -/
theorem residue_const_mul_sub_inv (c z₀ : ℂ) :
    residue (fun z => c * (z - z₀)⁻¹) z₀ = c := by
  have hmero : MeromorphicAt (fun z => (z - z₀)⁻¹) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  rw [residue_const_mul c hmero, residue_sub_inv, mul_one]

/-- **The residue of the logarithmic derivative is the meromorphic order.** If `f` is meromorphic at
`z₀` of order `n` (`meromorphicOrderAt f z₀ = n`), then `residue (logDeriv f) z₀ = n`: the residue
of `f'/f` counts the order of `f` at `z₀` — positive at a zero, negative at a pole. This is the
local, residue-form of the argument principle `TauCeti.Contour.argumentPrinciple`, the identity
`Res_{z₀}(f'/f) = ord_{z₀} f`. -/
theorem residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ} (hf : MeromorphicAt f z₀)
    (hn : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    residue (logDeriv f) z₀ = (n : ℂ) := by
  -- Near `z₀`, `logDeriv f` splits into its simple-pole principal part `n · (· − z₀)⁻¹` plus the
  -- analytic tail `logDeriv g` (with `g` the analytic non-vanishing local factor of `f`).
  obtain ⟨g, hg_an, hg_ne, hgerm⟩ := logDeriv_eventuallyEq_principalPart hf hn
  have hlogg_an : AnalyticAt ℂ (logDeriv g) z₀ := by
    rw [logDeriv]; exact hg_an.deriv.div hg_an hg_ne
  have hmero_inv : MeromorphicAt (fun z => (z - z₀)⁻¹) z₀ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  have hA : MeromorphicAt (fun z => (n : ℂ) * (z - z₀)⁻¹) z₀ :=
    analyticAt_const.meromorphicAt.mul hmero_inv
  have hB : MeromorphicAt (logDeriv g) z₀ := hlogg_an.meromorphicAt
  -- The residue only sees the germ, so pass to the split form and add residues.
  rw [residue_congr_nhdsNE hgerm,
    show (fun z => (n : ℂ) * (z - z₀)⁻¹ + logDeriv g z)
        = (fun z => (n : ℂ) * (z - z₀)⁻¹) + logDeriv g from rfl,
    residue_add hA hB, residue_const_mul_sub_inv, residue_eq_zero_of_analyticAt hlogg_an, add_zero]

end TauCeti.Contour

end

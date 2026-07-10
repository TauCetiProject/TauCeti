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
`n · (· − z₀)⁻¹` survives, whose residue is `n` by
`TauCeti.Contour.residue_const_mul_sub_inv` (the elementary simple-pole residues live in
`TauCeti.Analysis.Contour.ResidueSimplePole`).

## Main results

* `TauCeti.Contour.residue_logDeriv_eq_meromorphicOrderAt` — `residue (logDeriv f) z₀ = n` when
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

/-- **The residue of the logarithmic derivative is the meromorphic order.** If `f` is meromorphic at
`z₀` of order `n` (`meromorphicOrderAt f z₀ = n`), then `residue (logDeriv f) z₀ = n`: the residue
of `f'/f` counts the order of `f` at `z₀` — positive at a zero, negative at a pole. This is the
local, residue-form of the argument principle `TauCeti.Contour.argumentPrinciple`, the identity
`Res_{z₀}(f'/f) = ord_{z₀} f`. -/
theorem residue_logDeriv_eq_meromorphicOrderAt {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z₀) (hn : meromorphicOrderAt f z₀ = (n : WithTop ℤ)) :
    residue (logDeriv f) z₀ = (n : ℂ) := by
  -- Near `z₀`, `logDeriv f` splits into its simple-pole principal part `n · (· − z₀)⁻¹` plus the
  -- analytic tail `logDeriv g` (with `g` the analytic non-vanishing local factor of `f`).
  obtain ⟨g, hg_an, hg_ne, hgerm⟩ := logDeriv_eventuallyEq_principalPart hf hn
  have hlogg_an : AnalyticAt ℂ (logDeriv g) z₀ := analyticAt_logDeriv_of_analyticAt hg_an hg_ne
  have hA : MeromorphicAt (fun z => (n : ℂ) * (z - z₀)⁻¹) z₀ :=
    analyticAt_const.meromorphicAt.mul (meromorphicAt_sub_inv z₀)
  have hB : MeromorphicAt (logDeriv g) z₀ := hlogg_an.meromorphicAt
  -- The residue only sees the germ, so pass to the split form and add residues.
  rw [residue_congr_nhdsNE hgerm,
    show (fun z => (n : ℂ) * (z - z₀)⁻¹ + logDeriv g z)
        = (fun z => (n : ℂ) * (z - z₀)⁻¹) + logDeriv g from rfl,
    residue_add hA hB, residue_const_mul_sub_inv, residue_eq_zero_of_analyticAt hlogg_an, add_zero]

end TauCeti.Contour

end

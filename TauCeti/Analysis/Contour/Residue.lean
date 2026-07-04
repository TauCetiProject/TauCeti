/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The residue of a function at a point

For `f : ℂ → ℂ` with an isolated singularity at `z₀`, the **residue** is the order-`(−1)` Laurent
coefficient of `f` at `z₀`. For a simple pole `f z = c / (z − z₀) + g z` with `g` analytic at `z₀`,
that coefficient is `c`, recovered as the limit
`Res(f, z₀) = lim_{z → z₀} (z − z₀) · f z`,
which is the form used here. For `f` analytic at `z₀` the limit is `0` (no pole, residue `0`);
for a pole of order `> 1` the limit diverges (`residue` then takes a junk value via `limUnder`).
The Hungerbühler–Wasem residue theorem and the valence formula only require the simple-pole case.

The definition avoids introducing a bespoke order-of-vanishing notion, deferring the order theory to
Mathlib's `meromorphicOrderAt` when it is needed.

## Main definitions

* `residue f z₀` — the residue `lim_{z → z₀} (z − z₀) · f z`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

/-- **The residue of `f` at `z₀`**: the order-`(−1)` Laurent coefficient, taken in its simple-pole
form `lim_{z → z₀} (z − z₀) · f z`. For a simple pole `f z = c / (z − z₀) + g z` (`g` analytic) this
is `c`; for `f` analytic at `z₀` it is `0`. -/
@[expose]
def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[≠] z₀) fun z => (z - z₀) * f z

end TauCeti.Contour

end

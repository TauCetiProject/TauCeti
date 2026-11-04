/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic.LinearCombination

/-!
# The sixth term of a normalised elliptic divisibility sequence

Mathlib computes the terms of `normEDS` up to the fourth (`normEDS_zero`, `normEDS_one`,
`normEDS_two`, `normEDS_three`, `normEDS_four`) and stops. This file adds the sixth,

`normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c`,

expressed through the fifth rather than expanded. The fifth term does have a closed form,
`normEDS b c d 5 = d * b ^ 4 - c ^ 3`, but the factored shape above is the one the divisibility
arguments downstream consume, so the statement keeps `normEDS _ 5` rather than substituting it.

Adapted from D. K. Angdinata's `LutzNagell/EllipticDivisibilitySequence.lean` in AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0, `main` at `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`,
path `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`), declaration
`normEDS_six`. That file's header reads `Authors: David Kurniadi Angdinata`; following this
repository's convention for adapted material, the upstream authorship is credited here rather than
in the copyright header. J. Xu is acknowledged for the surrounding LutzNagell development — he
authors `Universal.lean` and co-authors `DivisionPolynomialOmega.lean` at the same revision — as
context for this port, not as an author of the declarations above.

**Adaptations:** converted to this repository's module system, placed in the `TauCeti`
namespace as `TauCeti.normEDS_six` (its arguments are ring elements, so no Mathlib type's
namespace would give it dot notation), and restated for Mathlib's current names — the source
predates the rename of `compl₂EDS` to `complEDS₂` and of `normEDS_mul_compl₂EDS` to
`normEDS_mul_complEDS₂`. The source unfolds `compl₂EDS` and re-evaluates it at `3` from the
`preNormEDS` values; Mathlib now has the `@[simp]` lemma `complEDS₂_three`, so that evaluation is
done by `simp`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] (b c d : R)

/-- **The sixth term of a normalised elliptic divisibility sequence**, through the fifth:
`W₆ = (W₅ - d²) b c`. This continues Mathlib's `normEDS_zero` through `normEDS_four`, which stop
at the fourth term. -/
@[simp]
theorem normEDS_six : normEDS b c d 6 = (normEDS b c d 5 - d ^ 2) * b * c := by
  have h := normEDS_mul_complEDS₂ b c d 3
  simp [normEDS, Int.even_iff] at h ⊢
  linear_combination -h

end TauCeti

end

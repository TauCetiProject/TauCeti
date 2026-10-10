/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T09.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/Normed/Operator/Compact/Basic.lean`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-rank operators are compact

`ContinuousLinearMap.isCompactOperator_of_finiteDimensional_range`: a bounded
operator whose range is finite-dimensional is a compact operator.

**Mathlib does not have this**, which is the reason the module exists.  It has
`isCompactOperator_id_iff_finiteDimensional` (the identity is compact exactly on
finite-dimensional spaces) and `isCompactOperator_of_locallyCompactSpace_dom`
(any bounded map *into* a locally compact space is compact), but nothing that
turns "the range is small" into compactness for a map into a large space.

The proof is the obvious factorisation and is three lines: corestrict to the
range, where the target is finite-dimensional and therefore locally compact, and
postcompose with the inclusion.  It is short because the two Mathlib lemmas it
uses are exactly right; it is *stated* because a caller who needs it would
otherwise inline the factorisation, which is how a general fact ends up hidden
inside a specific development.

That is not hypothetical: `ApproximationNumber/Compact.lean` carried
*finite rank ⇒ compact* as an explicit hypothesis on
`isCompactOperator_of_tendsto_approximationNumber`, with a docstring saying the
lemma belonged in a module about compact operators rather than in an
operator-ideal file.  This is that module.

## Scalars

`[ProperSpace 𝕜]` is the whole scalar hypothesis: it is what makes a
finite-dimensional normed space over `𝕜` proper, hence locally compact.  It holds
over `ℝ` and `ℂ`, and so under `RCLike`, but is stated directly because nothing
here is about an inner product — and **completeness of `𝕜` is not needed**, which
the section variables show rather than assert.

## Sources

*Follows nothing in particular*: the factorisation is the standard textbook
argument.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **A bounded operator with finite-dimensional range is compact.**

The factorisation is through the range: `R` corestricted to `LinearMap.range R`
is a bounded map into a finite-dimensional — hence locally compact — space, so it
is compact by `isCompactOperator_of_locallyCompactSpace_dom`, and composing with
the inclusion preserves that. -/
theorem isCompactOperator_of_finiteDimensional_range (R : E →L[𝕜] F)
    [FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F))] :
    IsCompactOperator R := by
  have : ProperSpace (LinearMap.range (R : E →ₗ[𝕜] F)) :=
    FiniteDimensional.proper 𝕜 _
  have hmem : ∀ x, R x ∈ LinearMap.range (R : E →ₗ[𝕜] F) := fun x => ⟨x, rfl⟩
  have hcod : IsCompactOperator (R.codRestrict _ hmem) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  exact hcod.clm_comp (LinearMap.range (R : E →ₗ[𝕜] F)).subtypeL

/-- **A bounded operator of finite rank is compact.**  The `Cardinal`-valued form
of `isCompactOperator_of_finiteDimensional_range`, which is the shape the
approximation-number API produces: `aₙ` bounds are stated as `R.rank ≤ n`. -/
theorem isCompactOperator_of_rank_lt_aleph0 (R : E →L[𝕜] F)
    (hR : R.rank < Cardinal.aleph0) : IsCompactOperator R := by
  have : FiniteDimensional 𝕜 (LinearMap.range (R : E →ₗ[𝕜] F)) :=
    Module.rank_lt_aleph0_iff.mp hR
  exact R.isCompactOperator_of_finiteDimensional_range

end ContinuousLinearMap

end

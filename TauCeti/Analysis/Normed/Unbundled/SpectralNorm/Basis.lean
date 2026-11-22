/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable

import TauCeti.Analysis.Normed.Unbundled.CoordinateNorm

/-!
# Coordinate norms and weak stability

For a finite extension of an ultrametric normed field, the spectral norm is bounded above by
a constant times the coordinate norm of any basis. The reverse bound holds exactly when every
linear functional is bounded for the spectral norm. Thus over a weakly stable field the
spectral norm and every finite-basis coordinate norm are equivalent.

These comparisons express weak cartesianness without imposing a topology on the extension or
assuming completeness of the base field. In particular they apply to incomplete perfect fields.
They do not assert that the spectral norm is multiplicative, or that every extension of the
absolute value is equivalent to it.

The coordinate norm is Mathlib's `Module.Basis.norm`, and the spectral norm is Mathlib's
`spectralNorm`. No additional norm or topology instance is installed. The general seminorm and
dual-functional comparisons for `Module.Basis.norm` live in
`TauCeti.Analysis.Normed.Unbundled.CoordinateNorm`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§2.3.1 and 3.5.1–3.5.2.
-/

public section

namespace TauCeti.IsWeaklyStable

universe u

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- On every finite extension of a weakly stable field, the spectral norm is equivalent to
the coordinate norm of any finite basis. The two comparison constants may differ. -/
theorem exists_basis_norm_comparison (hK : IsWeaklyStable K)
    {L : Type u} [Field L] [Algebra K L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : Module.Basis ι K L) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x,
      b.norm x ≤ C * spectralNorm K L x ∧ spectralNorm K L x ≤ D * b.norm x := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  simpa only [spectralAlgNorm_def] using
    b.exists_norm_comparison_of_forall_exists_bound (spectralAlgNorm K L)
      ((isWeaklyStable_iff K).mp hK L)

end TauCeti.IsWeaklyStable

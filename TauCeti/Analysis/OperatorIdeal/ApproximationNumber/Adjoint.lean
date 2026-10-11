/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic

/-!
# Adjoint invariance of approximation numbers

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces over `ℝ` or `ℂ`, the operator and
its adjoint have the same approximation numbers: `aₙ(T†) = aₙ(T)`. Taking adjoints is an isometry
for the operator norm, and it preserves the maps of rank at most `n`
(`ContinuousLinearMap.rank_adjoint_le_iff`), so it carries the infimum defining `aₙ(T)` onto the
one defining `aₙ(T†)`. Summing over the first `k` indices, the Ky Fan gauges agree as well.

On finite-dimensional spaces this is the adjoint invariance of singular values; in general it is
the reason the operator ideals built from the approximation numbers are closed under adjoints.

## Main declarations

* `ContinuousLinearMap.singularValue_adjoint`: `aₙ(T†) = aₙ(T)`.
* `ContinuousLinearMap.kyFanGauge_adjoint`: `Kₖ(T†) = Kₖ(T)`.

## References

* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
* I. C. Gohberg, M. G. Krein, *Introduction to the Theory of Linear Nonselfadjoint Operators*,
  Translations of Mathematical Monographs 18, AMS (1969), Chapter II.
-/

public section

open scoped InnerProduct NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Taking adjoints does not increase approximation numbers: each approximant `R` of `T` gives
the approximant `R†` of `T†` at the same distance. -/
private theorem singularValue_adjoint_le (T : E →L[𝕜] F) (n : ℕ) :
    (T†).singularValue n ≤ T.singularValue n := by
  refine (T.isGLB_singularValue n).2 ?_
  rintro _ ⟨R, hR, rfl⟩
  refine ((T†).singularValue_le_nnnorm_sub ((rank_adjoint_le_iff R).mpr hR)).trans_eq ?_
  rw [← map_sub, LinearIsometryEquiv.nnnorm_map]

/-- **Adjoint invariance.** A bounded operator between Hilbert spaces and its adjoint have the
same approximation numbers: `aₙ(T†) = aₙ(T)`. -/
@[simp]
theorem singularValue_adjoint (T : E →L[𝕜] F) (n : ℕ) :
    (T†).singularValue n = T.singularValue n :=
  (singularValue_adjoint_le T n).antisymm (by simpa using singularValue_adjoint_le (T†) n)

/-- **Ky Fan adjoint invariance.** `Kₖ(T†) = Kₖ(T)`. -/
@[simp]
theorem kyFanGauge_adjoint (T : E →L[𝕜] F) (k : ℕ) : (T†).kyFanGauge k = T.kyFanGauge k := by
  simp [kyFanGauge_def]

end ContinuousLinearMap

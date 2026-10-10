/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Singular values of a continuous linear map

`Mathlib.Analysis.InnerProductSpace.SingularValues` defines the singular values
of a *linear* map between finite-dimensional inner product spaces, as a
`Finsupp` sequence `LinearMap.singularValues : ℕ →₀ ℝ`.  Between
finite-dimensional spaces every linear map is continuous, so the two notions
agree; but the operator-theoretic consumers — approximation numbers, Ky Fan
norms, Eckart--Young — all work with `ContinuousLinearMap`, and without an
accessor at that level every public statement about them has to spell
`T.toLinearMap.singularValues n`, leaking the coercion into the statement and
into every downstream proof.

This module supplies the accessor and the small part of the API that the
operator-theoretic layer actually uses.  Everything is definitionally the
`LinearMap` notion, so `ContinuousLinearMap.toLinearMap_singularValues` moves
freely between the two and no result is duplicated: the lemmas below are
one-line delegations kept only so that consumers never have to unfold the
accessor.

## Naming

The name stays **plural**, matching `LinearMap.singularValues`.  The
signature-polish backlog suggested
a singular `singularValue` "unless the existing Mathlib function is irrevocably
plural" — it is: the Mathlib object is the whole `ℕ →₀ ℝ` sequence, not an
individual value, and `T.singularValues n` is function application to it.  A
singular accessor would have to be a second definition wrapping the first, which
is exactly the duplication this module exists to avoid.

## Main declarations

* `ContinuousLinearMap.singularValues`: the singular-value sequence of a
  continuous linear map.
* `ContinuousLinearMap.toLinearMap_singularValues`: the bridge to
  `LinearMap.singularValues`, `simp`-normalizing towards the continuous form.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**, written per the signature-polish backlog, which
  asked for "a singular-value accessor on `ContinuousLinearMap` rather than
  `T.toLinearMap.singularValues` in public statements".
* Spectra influence: **none** — this module imports only Mathlib.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The singular values of a continuous linear map between finite-dimensional
inner product spaces: the sequence whose first `finrank 𝕜 E` entries are the
square roots of the eigenvalues of `T⋆ T` in decreasing order, repeated
according to multiplicity, and zero thereafter.

**Zero-indexed**: `T.singularValues 0` is the largest singular value, and the
positive singular values occupy `0 ≤ i < finrank 𝕜 T.range`.  This matches
`LinearMap.singularValues`, of which this is definitionally a restatement, and
it is why the approximation numbers of
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean` are indexed
the same way. -/
@[expose]
noncomputable def singularValues (T : E →L[𝕜] F) : ℕ →₀ ℝ :=
  T.toLinearMap.singularValues

/-- The singular values of a continuous linear map are those of the underlying
linear map.  Oriented towards the continuous form, so that `simp` removes the
coercion from statements rather than introducing it. -/
@[simp]
theorem toLinearMap_singularValues (T : E →L[𝕜] F) :
    (T : E →ₗ[𝕜] F).singularValues = T.singularValues := (rfl)
/-- Singular values are nonnegative. -/
theorem singularValues_nonneg (T : E →L[𝕜] F) (i : ℕ) : 0 ≤ T.singularValues i :=
  T.toLinearMap.singularValues_nonneg i

/-- Singular values are listed in decreasing order. -/
theorem singularValues_antitone (T : E →L[𝕜] F) : Antitone T.singularValues :=
  T.toLinearMap.singularValues_antitone

/-- Singular values past the dimension of the source vanish. -/
theorem singularValues_of_finrank_le (T : E →L[𝕜] F) {i : ℕ} (hi : finrank 𝕜 E ≤ i) :
    T.singularValues i = 0 :=
  T.toLinearMap.singularValues_of_finrank_le hi

/-- The zero map has all singular values zero. -/
@[simp]
theorem singularValues_zero : (0 : E →L[𝕜] F).singularValues = 0 :=
  LinearMap.singularValues_zero

/-- Conversely, vanishing singular values force the map to be zero -- the definiteness that makes
any gauge built from them a norm rather than a seminorm. -/
@[simp]
theorem singularValues_eq_zero_iff {T : E →L[𝕜] F} : T.singularValues = 0 ↔ T = 0 := by
  rw [singularValues, LinearMap.singularValues_eq_zero_iff, ← ContinuousLinearMap.toLinearMap_zero,
    ContinuousLinearMap.coe_inj]

/-- A singular value is positive exactly below the rank. -/
theorem singularValues_pos_iff_lt_finrank_range {T : E →L[𝕜] F} {n : ℕ} :
    0 < T.singularValues n ↔ n < finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) :=
  LinearMap.singularValues_pos_iff_lt_finrank_range (T : E →ₗ[𝕜] F)

end ContinuousLinearMap

end

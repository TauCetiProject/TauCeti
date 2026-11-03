/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Constructions of partial diffeomorphisms

Two basic ways of producing a `PartialDiffeomorph`: lowering the regularity of a given one, and
reading a continuous linear equivalence as one at any regularity. Mathlib's
`ContinuousLinearEquiv.toDiffeomorph` gives the latter at regularity `∞` only, so it does not cover
the analytic regularity `ω`.

## Main definitions

* `PartialDiffeomorph.ofLE`: a `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`.
* `ContinuousLinearEquiv.toPartialDiffeomorph`: a continuous linear equivalence as a `C^n` partial
  diffeomorphism defined everywhere, for any `n`.
-/

public section

noncomputable section

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {m n : WithTop ℕ∞}

namespace PartialDiffeomorph

/-- A `C^n` partial diffeomorphism as a `C^m` one, for `m ≤ n`. -/
def ofLE (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) : PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn.of_le hmn
  contMDiffOn_invFun := Φ.symm.contMDiffOn.of_le hmn

/-- Lowering the regularity keeps the underlying partial equivalence. -/
@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (hmn : m ≤ n) :
    (Φ.ofLE hmn).toPartialEquiv = Φ.toPartialEquiv :=
  (rfl)

end PartialDiffeomorph

namespace ContinuousLinearEquiv

/-- A continuous linear equivalence as a `C^n` partial diffeomorphism defined everywhere, for any
regularity `n`, including the analytic regularity `ω` not reached by
`ContinuousLinearEquiv.toDiffeomorph`. -/
def toPartialDiffeomorph (A : E ≃L[𝕜] F) : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n where
  toPartialEquiv := A.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := A.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := A.symm.contDiff.contMDiff.contMDiffOn

/-- The partial equivalence underlying `ContinuousLinearEquiv.toPartialDiffeomorph` is the
underlying equivalence, on the whole space. -/
@[simp]
theorem toPartialDiffeomorph_toPartialEquiv (A : E ≃L[𝕜] F) :
    (A.toPartialDiffeomorph (n := n)).toPartialEquiv = A.toEquiv.toPartialEquiv :=
  (rfl)

end ContinuousLinearEquiv

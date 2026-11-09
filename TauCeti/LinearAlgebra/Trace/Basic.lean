/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The trace of a module without a finite basis

Mathlib's `LinearMap.trace R M` is defined through a finite basis of `M`, and is `0` when `M` has
none. This file names that case of the definition, so that proofs need not unfold
`LinearMap.trace`.

## Main results

* `TauCeti.LinearMap.trace_eq_zero_of_not_exists_basis`: the trace vanishes on a module with no
  finite basis.
* `TauCeti.LinearMap.trace_eq_zero_of_not_finite`: the trace vanishes on a module that is not
  finite.
* `LinearMap.eq_trace_smul_one_of_finrank_eq_one`: on a free module of rank one, an
  endomorphism is its trace times the identity.
-/

public section

namespace TauCeti.LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The trace vanishes on a module with no finite basis. This is the endomorphism counterpart of
`Algebra.trace_eq_zero_of_not_exists_basis`. -/
theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset M, Nonempty (Module.Basis s R M)) :
    _root_.LinearMap.trace R M = 0 :=
  dite_eq_right fun hb ↦ (h hb).elim

/-- The trace vanishes on a module that is not finite. -/
theorem trace_eq_zero_of_not_finite (h : ¬Module.Finite R M) : _root_.LinearMap.trace R M = 0 :=
  trace_eq_zero_of_not_exists_basis fun ⟨_, ⟨b⟩⟩ ↦ h (.of_basis b)

end TauCeti.LinearMap

namespace LinearMap

/-- On a free module of rank one, an endomorphism is its trace times the identity. -/
theorem eq_trace_smul_one_of_finrank_eq_one {R V : Type*} [CommSemiring R] [StrongRankCondition R]
    [AddCommMonoid V] [Module R V] [Module.Free R V]
    (h : Module.finrank R V = 1) (f : V →ₗ[R] V) :
    f = LinearMap.trace R V f • (1 : V →ₗ[R] V) := by
  have : Module.Finite R V := Module.finite_of_finrank_pos (by omega)
  obtain ⟨c, hc, _⟩ := f.existsUnique_eq_smul_id_of_finrank_eq_one h
  let b := Module.finBasisOfFinrankEq R V h
  rw [hc]
  simp [LinearMap.trace_eq_matrix_trace R b, LinearMap.toMatrix_id, Matrix.trace,
    Module.End.one_eq_id]

end LinearMap

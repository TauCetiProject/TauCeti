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
# Basic facts about the trace

Mathlib's `LinearMap.trace R M` is defined through a finite basis of `M`, and is `0` when `M` has
none. This file names that case of the definition, so that proofs need not unfold
`LinearMap.trace`. It also computes the trace of an endomorphism whose range lies in a free
submodule with a given basis, as the trace of its matrix in that basis.

## Main results

* `TauCeti.LinearMap.trace_eq_zero_of_not_exists_basis`: the trace vanishes on a module with no
  finite basis.
* `TauCeti.LinearMap.trace_eq_zero_of_not_finite`: the trace vanishes on a module that is not
  finite.
* `LinearMap.eq_trace_smul_one_of_finrank_eq_one`: on a free module of rank one, an
  endomorphism is its trace times the identity.
* `LinearMap.trace_eq_sum_of_range_le_of_apply_single_eq`: the trace of an endomorphism whose
  range lies in a free submodule `ι → R` is the trace of its matrix there.
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

/-- **The trace of an endomorphism with range in a free submodule.** Let `φ` be an injective
linear map from `ι → R` to `M`, and let `L` be an endomorphism whose range lies in the range of `φ`
and that sends the image under `φ` of the `j`-th standard basis vector of `ι → R` to `φ (a j)`.
Then the trace of `L` is the trace `∑ j, a j j` of `a`. -/
theorem trace_eq_sum_of_range_le_of_apply_single_eq {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Fintype ι]
    [DecidableEq ι] {φ : (ι → R) →ₗ[R] M} (hφ : Function.Injective φ) {L : M →ₗ[R] M}
    (hL : LinearMap.range L ≤ LinearMap.range φ) {a : ι → ι → R}
    (hLa : ∀ j, L (φ (Pi.single j 1)) = φ (a j)) : trace R M L = ∑ j, a j j := by
  let ρ : M →ₗ[R] ι → R := (LinearEquiv.ofInjective φ hφ).symm.toLinearMap ∘ₗ
    L.codRestrict (LinearMap.range φ) fun s ↦ hL ⟨s, rfl⟩
  have hφρ : φ ∘ₗ ρ = L := LinearMap.ext fun s ↦ by
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective φ hφ).apply_symm_apply ⟨L s, hL ⟨s, rfl⟩⟩)
    rwa [LinearEquiv.ofInjective_apply] at h
  have hmat : ρ ∘ₗ φ = Matrix.toLin' (Matrix.of fun l j ↦ a j l) := by
    ext j l
    have hj : ρ (φ (Pi.single j 1)) = a j := hφ (by rw [← LinearMap.comp_apply, hφρ, hLa])
    simp [hj]
  rw [← hφρ, LinearMap.trace_comp_comm', hmat, Matrix.trace_toLin'_eq]
  simp [Matrix.trace]

end LinearMap

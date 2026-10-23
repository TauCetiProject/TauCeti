/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Trace.Defs
import TauCeti.Algebra.Ring.GeomSum
import TauCeti.LinearAlgebra.Trace.RestrictScalars

/-!
# Matrices of invertible finite order over a ring with a local retraction

Let `R` be a commutative `A`-algebra with an `A`-algebra retraction `ε : R → A` that is a local
homomorphism, i.e. `x` is a unit as soon as `ε x` is. A typical example is a group algebra
`A[Q]` of a finite `p`-group `Q` over a local ring `A` of residue characteristic `p`, with `ε` the
augmentation.

If a square matrix `M` over `R` satisfies `M ^ m = 1`, where `m` is invertible in `A`, then `M` is
conjugate to its *constant part* `N`, the matrix obtained by applying `algebraMap A R ∘ ε` to
the entries of `M`. The intertwiner is the averaging sum `T = ∑_{i < m} M ^ i * N ^ (m - 1 - i)`,
which satisfies `M * T = T * N`; its image under `ε` is `m • ε(M) ^ (m - 1)`, which is invertible,
so `T` is invertible because `ε` is local. In particular the trace of `M` lies in `A`.

In other words, a representation over `R` of a cyclic group whose order is invertible in `A` is
isomorphic to the base change along `algebraMap A R` of its image under `ε`.

## Main results

* `Matrix.exists_isUnit_mul_eq_mul_map_of_pow_eq_one`: `M` is conjugate to its constant part.
* `Matrix.trace_eq_algebraMap_of_pow_eq_one`: the trace of `M` is the constant `ε (trace M)`.
* `LinearMap.trace_eq_algebraMap_of_pow_eq_one`: the same for an endomorphism of a free module.
* `LinearMap.trace_restrictScalars_smul_of_pow_eq_one`: if moreover `R` is free over `A`, the
  `A`-trace of `c • f` is `ε (trace f) * Tr_{R/A}(c)`.
-/

public section

open Finset

namespace Matrix

variable {A R n : Type*} [CommRing A] [CommRing R] [Algebra A R] [Fintype n] [DecidableEq n]

/-- **A matrix of invertible finite order is conjugate to its constant part.** If `ε : R → A` is
a local `A`-algebra retraction and `M ^ m = 1` with `m` invertible in `A`, then `M` is conjugate,
by an invertible matrix over `R`, to the matrix of constants `algebraMap A R (ε (M i j))`. -/
theorem exists_isUnit_mul_eq_mul_map_of_pow_eq_one (M : Matrix n n R) (ε : R →ₐ[A] A)
    [IsLocalHom ε] {m : ℕ} (hm : IsUnit (m : A)) (hM : M ^ m = 1) :
    ∃ T : Matrix n n R, IsUnit T ∧ M * T = T * M.map (algebraMap A R ∘ ε) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · -- `m = 0` forces `A`, hence `R`, to be the zero ring.
    have h01 : (0 : A) = 1 := isUnit_zero_iff.mp (by simpa using hm)
    have : Subsingleton R := isUnit_zero_iff.mp (isUnit_of_map_unit ε 0 (by
      rw [map_zero, h01]; exact isUnit_one)) |> subsingleton_of_zero_eq_one
    exact ⟨1, isUnit_one, Subsingleton.elim _ _⟩
  let ψ : R →+* R := (algebraMap A R).comp ε
  set N := M.map (algebraMap A R ∘ ε) with hN
  have hNψ : N = ψ.mapMatrix M := rfl
  have hNm : N ^ m = 1 := by rw [hNψ, ← map_pow, hM, map_one]
  refine ⟨∑ i ∈ range m, M ^ i * N ^ (m - 1 - i), ?_, ?_⟩
  · -- Under `ε` the averaging sum becomes `m • ε(M) ^ (m - 1)`, which is invertible.
    have hεN : (ε : R →+* A).mapMatrix N = (ε : R →+* A).mapMatrix M := by
      ext i j
      simp [hN]
    have hεT : (ε : R →+* A).mapMatrix (∑ i ∈ range m, M ^ i * N ^ (m - 1 - i)) =
        (m : Matrix n n A) * (ε : R →+* A).mapMatrix M ^ (m - 1) := by
      simp only [map_sum, map_mul, map_pow, hεN, geom_sum₂_self]
    have hεM : IsUnit ((ε : R →+* A).mapMatrix M) :=
      IsUnit.of_pow_eq_one (by rw [← map_pow, hM, map_one]) hm0
    have hunit : IsUnit ((ε : R →+* A).mapMatrix (∑ i ∈ range m, M ^ i * N ^ (m - 1 - i))) := by
      rw [hεT]
      refine IsUnit.mul ?_ (hεM.pow _)
      rw [← map_natCast (algebraMap A (Matrix n n A))]
      exact hm.map _
    rw [isUnit_iff_isUnit_det] at hunit ⊢
    rw [← RingHom.map_det] at hunit
    exact isUnit_of_map_unit ε _ hunit
  · have h := TauCeti.mul_geom_sum₂_add_pow M N m
    rwa [hM, hNm, add_left_inj] at h

/-- **The trace of a matrix of invertible finite order is constant.** If `ε : R → A` is a local
`A`-algebra retraction and `M ^ m = 1` with `m` invertible in `A`, then the trace of `M` is the
image of `ε (trace M)` in `R`. -/
theorem trace_eq_algebraMap_of_pow_eq_one (M : Matrix n n R) (ε : R →ₐ[A] A) [IsLocalHom ε]
    {m : ℕ} (hm : IsUnit (m : A)) (hM : M ^ m = 1) : M.trace = algebraMap A R (ε M.trace) := by
  obtain ⟨T, hT, hMT⟩ := exists_isUnit_mul_eq_mul_map_of_pow_eq_one M ε hm hM
  have hconj : M = hT.unit * M.map (algebraMap A R ∘ ε) * hT.unit⁻¹ := by
    calc M = M * hT.unit * ↑hT.unit⁻¹ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      _ = _ := by rw [IsUnit.unit_spec, hMT]
  rw [hconj, trace_units_conj]
  simp [Matrix.trace]

end Matrix

namespace LinearMap

variable {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommMonoid M]
  [Module R M] [Module.Free R M]

/-- **The trace of an endomorphism of invertible finite order is constant.** If `ε : R → A` is a
local `A`-algebra retraction and `f ^ m = 1` with `m` invertible in `A`, then the trace of the
endomorphism `f` of a free `R`-module is the image of `ε (trace f)` in `R`. -/
theorem trace_eq_algebraMap_of_pow_eq_one (f : M →ₗ[R] M) (ε : R →ₐ[A] A) [IsLocalHom ε]
    {m : ℕ} (hm : IsUnit (m : A)) (hf : f ^ m = 1) :
    trace R M f = algebraMap A R (ε (trace R M f)) := by
  classical
  nontriviality R
  let ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  cases fintypeOrInfinite ι; swap
  · have hM := Module.not_finite_of_infinite_basis b
    have hM' : ¬∃ s : Finset M, Nonempty (Module.Basis s R M) :=
      fun ⟨_, ⟨b⟩⟩ ↦ hM (Module.Finite.of_basis b)
    simp [LinearMap.trace, hM']
  rw [trace_eq_matrix_trace R b]
  refine Matrix.trace_eq_algebraMap_of_pow_eq_one _ ε hm ?_
  have h := congrArg (toMatrixAlgEquiv b) hf
  rwa [map_pow, map_one] at h

/-- **The trace over `A` of a multiple of an endomorphism of invertible finite order.** If `R` is
free over `A`, `ε : R → A` is a local `A`-algebra retraction and `f ^ m = 1` with `m` invertible
in `A`, then for every `c ∈ R` the `A`-trace of `c • f` is `ε (trace f)` times the algebra trace
of `c`. -/
theorem trace_restrictScalars_smul_of_pow_eq_one [Module.Free A R]
    [Module A M] [IsScalarTower A R M] (f : M →ₗ[R] M) (ε : R →ₐ[A] A) [IsLocalHom ε] {m : ℕ}
    (hm : IsUnit (m : A)) (hf : f ^ m = 1) (c : R) :
    trace A M ((c • f).restrictScalars A) = ε (trace R M f) * Algebra.trace A R c := by
  rw [trace_restrictScalars, map_smul, trace_eq_algebraMap_of_pow_eq_one f ε hm hf]
  simp [mul_comm c, ← Algebra.smul_def]

end LinearMap

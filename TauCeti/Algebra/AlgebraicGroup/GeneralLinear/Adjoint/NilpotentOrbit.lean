/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Centralizer.Basic
public import TauCeti.LinearAlgebra.End.NilpotentCentralizer
import TauCeti.Combinatorics.Enumerative.Partition.ColumnSquares

/-!
# Centralizers and adjoint orbits of nilpotent matrices in the general linear group

Let `X` be a nilpotent `n × n` matrix over a field `k`, viewed as an element `x` of the Lie
algebra of `GLₙ` through `TauCeti.GeneralLinear.cotangentDualMatrixEquiv`. Write `λ` for the
Jordan partition of `X` and `λ'` for its conjugate. This file computes the dimensions of the
scheme-theoretic centralizer `C_GL(X)` and of the adjoint orbit of `X` from `λ`:

* the tangent space `[𝔤𝔩ₙ, x]` has dimension `n² - ∑ⱼ (λ'ⱼ)²`, over any field;
* in characteristic zero, `dim C_GL(X) = ∑ⱼ (λ'ⱼ)²`;
* over an algebraically closed field of characteristic zero, the adjoint orbit of `X` has
  dimension `n² - ∑ⱼ (λ'ⱼ)²`.

Reading off the two largest values of the orbit dimension identifies the regular and subregular
nilpotent orbits by their Jordan types: the orbit has the maximal dimension `n² - n` exactly for
the one-row partition `(n)`; every other nilpotent orbit has dimension at most `n² - n - 2`, with
equality exactly for the partition `(n - 1, 1)`. So the subregular orbit has dimension two less
than the regular one. These are the group-level counterparts of the tangent-space calculations for
`sl n` in `TauCeti.Algebra.Lie.GeneralLinear.NilpotentOrbit`.

All statements are written additively, so no truncated subtraction occurs. The Jordan partition
is that of the endomorphism `Matrix.toLinAlgEquiv' X` of `Fin n → k`.

## Main results

* `TauCeti.GeneralLinear.finrank_range_ad_add_sum_sq_conjugate_parts`: the dimension of
  `[𝔤𝔩ₙ, x]`.
* `TauCeti.GeneralLinear.ringKrullDim_quotient_centralizerHopfIdeal_eq_sum_sq_conjugate_parts`:
  the dimension of `C_GL(X)`.
* `TauCeti.GeneralLinear.topologicalKrullDim_range_projectiveOrbitMap_add_sum_sq_conjugate_parts`:
  the dimension of the adjoint orbit of `X`.
* `TauCeti.GeneralLinear.topologicalKrullDim_range_projectiveOrbitMap_add_eq_iff`: the regular
  nilpotent orbit.
* `TauCeti.GeneralLinear.topologicalKrullDim_range_projectiveOrbitMap_add_add_two_eq_iff`: the
  subregular nilpotent orbit.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §6.1, for centralizers and orbit dimensions of nilpotent matrices.
-/

public section

open Matrix Module

namespace TauCeti.GeneralLinear

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- **The tangent space of a nilpotent orbit in `𝔤𝔩ₙ`.** For a nilpotent matrix `X` with Jordan
partition `λ`, the image `[𝔤𝔩ₙ, x]` of `ad x` has dimension `n² - ∑ⱼ (λ'ⱼ)²`, where `λ'` is the
conjugate partition. -/
theorem finrank_range_ad_add_sum_sq_conjugate_parts
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    finrank k (LinearMap.range (LieAlgebra.ad k _ x)) +
        ((End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx).conjugate.parts.map
          (· ^ 2)).sum =
      n * n := by
  -- The kernel of `ad x` is carried onto the centralizer of the matrix of `x`.
  have hker : finrank k (LinearMap.ker (LieAlgebra.ad k _ x)) =
      finrank k (Subalgebra.centralizer k {cotangentDualMatrixEquiv x}) := by
    rw [← Subalgebra.finrank_toSubmodule, ← map_cotangentDualMatrixEquiv_ker_ad,
      LinearEquiv.finrank_map_eq]
  rw [← finrank_centralizer_eq_sum_sq_conjugate_jordanPartition, ← hker,
    LinearMap.finrank_range_add_finrank_ker, cotangentDualMatrixEquiv.finrank_eq]
  simp [finrank_matrix]

section CharZero

variable [CharZero k]

/-- **The centralizer of a nilpotent matrix in `GLₙ`.** Over a field of characteristic zero, the
centralizer of a nilpotent matrix `X` in `GLₙ` has dimension `∑ⱼ (λ'ⱼ)²`, where `λ'` is the
conjugate of the Jordan partition of `X`. -/
theorem ringKrullDim_quotient_centralizerHopfIdeal_eq_sum_sq_conjugate_parts
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    ringKrullDim (coordinateHopfAlgebra k n ⧸
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal) =
      (((End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx).conjugate.parts.map
        (· ^ 2)).sum : ℕ) := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_centralizer,
    finrank_centralizer_eq_sum_sq_conjugate_jordanPartition]

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

variable [IsAlgClosed k]

/-- **The dimension of a nilpotent orbit in `GLₙ`.** Over an algebraically closed field of
characteristic zero, the adjoint orbit of a nilpotent matrix `X` has dimension
`n² - ∑ⱼ (λ'ⱼ)²`, where `λ'` is the conjugate of the Jordan partition of `X`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_sum_sq_conjugate_parts
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) +
      (((End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx).conjugate.parts.map
        (· ^ 2)).sum : ℕ) = n * n := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  exact_mod_cast finrank_range_ad_add_sum_sq_conjugate_parts x hx

/-- Over an algebraically closed field of characteristic zero, the adjoint orbit of a nilpotent
matrix in `GLₙ` has dimension at most `n² - n`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_le
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n ≤ n * n := by
  have h := finrank_range_ad_add_sum_sq_conjugate_parts x hx
  have hle := (End.jordanPartition _ hx).conjugate.le_sum_sq_parts
  have hcard := finrank_fin_fun k (n := n)
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  norm_cast
  omega

/-- **The regular nilpotent orbit in `GLₙ`.** Over an algebraically closed field of
characteristic zero, the adjoint orbit of a nilpotent matrix has the maximal dimension `n² - n`
exactly when its Jordan partition is the one-row partition `(n)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_eq_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n = n * n ↔
      End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx =
        Nat.Partition.indiscrete _ := by
  have h := finrank_range_ad_add_sum_sq_conjugate_parts x hx
  have hcard := finrank_fin_fun k (n := n)
  rw [← Nat.Partition.sum_sq_conjugate_parts_eq_self_iff,
    topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  norm_cast
  omega

/-- Over an algebraically closed field of characteristic zero, the adjoint orbit of a nilpotent
matrix in `GLₙ` whose Jordan type is not regular has dimension at most `n² - n - 2`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_add_two_le
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x)))
    (hreg : End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx ≠
      Nat.Partition.indiscrete _) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n + 2 ≤ n * n := by
  have h := finrank_range_ad_add_sum_sq_conjugate_parts x hx
  have hle := Nat.Partition.add_two_le_sum_sq_conjugate_parts _ hreg
  have hcard := finrank_fin_fun k (n := n)
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  norm_cast
  omega

/-- **The subregular nilpotent orbit in `GLₙ`.** Over an algebraically closed field of
characteristic zero, the adjoint orbit of a nilpotent matrix has dimension `n² - n - 2`, two less
than the regular orbit, exactly when its Jordan partition is `(n - 1, 1)`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_add_two_eq_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv' (cotangentDualMatrixEquiv x))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n + 2 = n * n ↔
      (End.jordanPartition (toLinAlgEquiv' (cotangentDualMatrixEquiv x)) hx).parts =
        {n - 1, 1} := by
  have h := finrank_range_ad_add_sum_sq_conjugate_parts x hx
  have hcard := finrank_fin_fun k (n := n)
  have hsub := Nat.Partition.sum_sq_conjugate_parts_eq_add_two_iff (End.jordanPartition _ hx)
  -- Only the size inside the multiset `{n - 1, 1}` is rewritten, not the partition's type.
  rw [show ({finrank k (Fin n → k) - 1, 1} : Multiset ℕ) = {n - 1, 1} by rw [hcard]] at hsub
  rw [← hsub, topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad]
  norm_cast
  omega

end CharZero

end TauCeti.GeneralLinear

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Positive
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.OrderClosed

/-!
# Topology of diagonal matrices in the general linear group

The diagonal embedding `TauCeti.diagGL : (ι → Rˣ) →* GL ι R` and the central scalar embedding
`Matrix.GeneralLinearGroup.scalar ι : Rˣ →* GL ι R` are continuous over any topological semiring
(`TauCeti.continuous_diagGL`, `Matrix.GeneralLinearGroup.continuous_scalar`).

The positive diagonal matrices form a closed subgroup of the general linear group over an
ordered field with closed order and closed points. Invertibility prevents a diagonal entry
from vanishing, so nonnegative diagonal entries are positive. This includes the positive
real diagonal factor in the matrix Iwasawa decomposition.

## Main results

* `TauCeti.continuous_diagGL`: the diagonal embedding `(ι → Rˣ) → GL ι R` is continuous.
* `Matrix.GeneralLinearGroup.continuous_scalar`: the scalar embedding `Rˣ → GL ι R` is continuous.
* `TauCeti.isClosed_posDiagonalSubgroup`: positive diagonal matrices are closed among units.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312, for the positive real diagonal factor of the Iwasawa decomposition.
-/

public section

open Matrix Set Topology

namespace TauCeti

/-- The diagonal embedding `diagGL : (ι → Rˣ) → GL ι R` is continuous over any topological
semiring. -/
@[fun_prop] theorem continuous_diagGL {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    [TopologicalSpace R] : Continuous (diagGL (ι := ι) (k := R)) :=
  Units.continuous_iff.mpr
    ⟨by
      simpa only [Function.comp_def, diagGL_coe] using
        (continuous_pi fun i => Units.continuous_val.comp (continuous_apply i)).matrix_diagonal,
     by
      simpa only [Function.comp_def, ← map_inv, diagGL_coe, Pi.inv_apply] using
        (continuous_pi fun i =>
          (Units.continuous_coe_inv (M := R)).comp (continuous_apply i)).matrix_diagonal⟩

end TauCeti

namespace Matrix.GeneralLinearGroup

/-- The central scalar embedding `Matrix.GeneralLinearGroup.scalar ι : Rˣ → GL ι R` is continuous
over any topological semiring. -/
@[fun_prop] theorem continuous_scalar {ι R : Type*} [Fintype ι] [DecidableEq ι] [Semiring R]
    [TopologicalSpace R] : Continuous (scalar ι : Rˣ → GL ι R) := by
  simpa only [Function.comp_def, id_eq, TauCeti.diagGL_const] using
    (TauCeti.continuous_diagGL (ι := ι) (R := R)).comp (continuous_pi fun _ => continuous_id)

end Matrix.GeneralLinearGroup

namespace TauCeti

variable (ι 𝕜 : Type*) [Fintype ι] [DecidableEq ι] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [T1Space 𝕜] [OrderClosedTopology 𝕜]

/-- Positive diagonal matrices are closed in the general linear group. -/
instance isClosed_posDiagonalSubgroup :
    IsClosed (posDiagonalSubgroup ι 𝕜 : Set (GL ι 𝕜)) := by
  have heq : (posDiagonalSubgroup ι 𝕜 : Set (GL ι 𝕜)) =
      {g : GL ι 𝕜 | ∀ i j, i ≠ j → (g : Matrix ι ι 𝕜) i j = 0} ∩
      {g : GL ι 𝕜 | ∀ i, 0 ≤ (g : Matrix ι ι 𝕜) i i} := by
    ext g
    constructor
    · intro hg
      have hd := coe_eq_diagonal_of_mem_posDiagonalSubgroup hg
      exact ⟨fun i j hij ↦ by rw [hd, diagonal_apply_ne _ hij],
        fun i ↦ (apply_diag_pos_of_mem_posDiagonalSubgroup hg i).le⟩
    · rintro ⟨hd, hpos⟩
      have hdiag : (g : Matrix ι ι 𝕜).IsDiag := hd
      exact mem_posDiagonalSubgroup_iff.mpr ⟨_, fun i ↦
        (hpos i).lt_of_ne (isUnit_apply_of_isDiag hdiag i).ne_zero.symm,
        hdiag.diagonal_diag.symm⟩
  rw [heq]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_singleton.preimage (Units.continuous_val.matrix_elem i j)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const
      (Units.continuous_val.matrix_elem i i)

end TauCeti

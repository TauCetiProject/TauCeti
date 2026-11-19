/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit
public import TauCeti.Algebra.Lie.GeneralLinear.NilpotentOrbit
import TauCeti.Algebra.Lie.AdjointAction.Regular

/-!
# Dimensions of nilpotent centralizers and orbits in `SLₙ`

For a nilpotent element of the actual cotangent-dual Lie algebra of `SLₙ`, let `λ`
be the Jordan partition of its trace-zero matrix. In characteristic zero and positive
matrix size, its scheme-theoretic group centralizer has dimension
`∑ⱼ (λ'ⱼ)² - 1`. Over an algebraically closed field the adjoint orbit scheme has
dimension `n² - ∑ⱼ (λ'ⱼ)²`. The regular and subregular types give orbit dimensions
`n² - n` and `n² - n - 2`, respectively.

These statements concern the existing centralizer Hopf ideal and projective orbit
scheme of the actual adjoint representation, not just matrix tangent spaces. The
comparison uses `cotangentDualLieEquivSl`, Cartier smoothness of centralizers, and
the general adjoint orbit dimension theorem. All dimension equations are additive.
The orbit formulas include size zero; the zero-size centralizer is treated separately.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1, for the centralizer and orbit dimension formulas in type A.
-/

public section

open Matrix Module LieAlgebra

namespace TauCeti.SpecialLinear

universe u

variable {k : Type u} [Field k] {n : ℕ}

/-- The dimension of the scheme-theoretic centralizer in `SLₙ` equals the dimension of
its trace-zero matrix Lie centralizer. -/
theorem ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_ker_ad_sl [CharZero k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    ringKrullDim (coordinateHopfAlgebra k n ⧸
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal) =
      finrank k (LinearMap.ker
        (ad k (LieAlgebra.SpecialLinear.sl (Fin n) k) (cotangentDualLieEquivSl n x))) := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal,
    ← (cotangentDualLieEquivSl n).finrank_ker_ad_apply x]

/-- The scheme-theoretic centralizer of a nilpotent element of `Lie(SLₙ)` has dimension
`∑ⱼ (λ'ⱼ)² - 1`. Positive size is necessary for the subtraction of one. -/
theorem ringKrullDim_quotient_centralizerHopfIdeal_add_one_eq_sum_sq_conjugate_parts
    [CharZero k] (hn : n ≠ 0)
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k))) :
    ringKrullDim (coordinateHopfAlgebra k n ⧸
        (centralizerHopfIdeal (coordinateHopfAlgebra k n) x).toIdeal) + 1 =
      (((End.jordanPartition (toLinAlgEquiv'
        (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)) hx).conjugate.parts.map
          (· ^ 2)).sum : ℕ) := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_ker_ad_sl]
  exact_mod_cast finrank_ker_ad_sl_add_one_eq_sum_sq_conjugate_parts
    (by simpa using hn) (cotangentDualLieEquivSl n x) hx

/-- The zero-size special linear group has zero-dimensional centralizers. -/
@[simp]
theorem ringKrullDim_quotient_centralizerHopfIdeal_zero [CharZero k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k 0))) :
    ringKrullDim (coordinateHopfAlgebra k 0 ⧸
      (centralizerHopfIdeal (coordinateHopfAlgebra k 0) x).toIdeal) = 0 := by
  rw [ringKrullDim_quotient_centralizerHopfIdeal_eq_finrank_ker_ad_sl]
  simp [Module.finrank_eq_zero_of_subsingleton]

private theorem jordanPartition_cotangentDualLieEquivSl_zero
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k 0)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl 0 x : Matrix (Fin 0) (Fin 0) k))) :
    End.jordanPartition (toLinAlgEquiv'
      (cotangentDualLieEquivSl 0 x : Matrix (Fin 0) (Fin 0) k)) hx =
        Nat.Partition.indiscrete _ := by
  have : Subsingleton (Nat.Partition (finrank k (Fin 0 → k))) := by
    simpa using (inferInstance : Subsingleton (Nat.Partition 0))
  exact Subsingleton.elim _ _

section Orbit

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

variable [CharZero k] [IsAlgClosed k]

/-- The dimension of an adjoint orbit in `SLₙ` equals the rank of the adjoint map
on its trace-zero matrix Lie algebra. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) =
      finrank k (LinearMap.range
        (ad k (LieAlgebra.SpecialLinear.sl (Fin n) k) (cotangentDualLieEquivSl n x))) := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad,
    ← (cotangentDualLieEquivSl n).finrank_range_ad_apply x]

/-- The actual adjoint orbit of a nilpotent element of `Lie(SLₙ)` has dimension
`n² - ∑ⱼ (λ'ⱼ)²`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_sum_sq_conjugate_parts
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) +
      (((End.jordanPartition (toLinAlgEquiv'
        (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)) hx).conjugate.parts.map
          (· ^ 2)).sum : ℕ) = n ^ 2 := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl]
  norm_cast
  by_cases hn : n = 0
  · subst n
    have hparts := (Nat.Partition.sum_sq_conjugate_parts_eq_self_iff _).mpr
      (jordanPartition_cotangentDualLieEquivSl_zero x hx)
    simpa [Module.finrank_eq_zero_of_subsingleton] using hparts
  · simpa only [Fintype.card_fin] using finrank_range_ad_sl_add_sum_sq_conjugate_parts
      (by simpa using hn) (cotangentDualLieEquivSl n x) hx

/-- The adjoint orbit of a nilpotent element in `SLₙ` has dimension at most `n² - n`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_le
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n ≤ n ^ 2 := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl]
  norm_cast
  by_cases hn : n = 0
  · subst n
    simp [Module.finrank_eq_zero_of_subsingleton]
  · simpa only [Fintype.card_fin] using finrank_range_ad_sl_add_card_le
      (by simpa using hn) (cotangentDualLieEquivSl n x) hx

/-- The regular Jordan type `(n)` is characterized by adjoint orbit dimension `n² - n`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_eq_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n = n ^ 2 ↔
      End.jordanPartition (toLinAlgEquiv'
        (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)) hx =
          Nat.Partition.indiscrete _ := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl]
  norm_cast
  by_cases hn : n = 0
  · subst n
    simp [Module.finrank_eq_zero_of_subsingleton, jordanPartition_cotangentDualLieEquivSl_zero x hx]
  · simpa only [Fintype.card_fin] using finrank_range_ad_sl_add_card_eq_iff
      (by simpa using hn) (cotangentDualLieEquivSl n x) hx

/-- Away from the regular Jordan type, a nilpotent adjoint orbit in `SLₙ` has dimension
at most `n² - n - 2`. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_add_two_le
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)))
    (hreg : End.jordanPartition (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)) hx ≠
        Nat.Partition.indiscrete _) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n + 2 ≤ n ^ 2 := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl]
  norm_cast
  by_cases hn : n = 0
  · subst n
    exact (hreg (jordanPartition_cotangentDualLieEquivSl_zero x hx)).elim
  · simpa only [Fintype.card_fin] using finrank_range_ad_sl_add_card_add_two_le
      (by simpa using hn) (cotangentDualLieEquivSl n x) hx hreg

/-- The subregular Jordan type `(n - 1, 1)` is characterized by adjoint orbit dimension
`n² - n - 2`. The equivalence has no solutions at sizes zero and one. -/
theorem topologicalKrullDim_range_projectiveOrbitMap_add_add_two_eq_iff
    (x : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)))
    (hx : IsNilpotent (toLinAlgEquiv'
      (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k))) :
    topologicalKrullDim (Set.range (Comodule.projectiveOrbitMap
        (H := coordinateHopfAlgebra k n)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n)) × k)
        (Module.isUnimodular_mk_one x))) + n + 2 = n ^ 2 ↔
      (End.jordanPartition (toLinAlgEquiv'
        (cotangentDualLieEquivSl n x : Matrix (Fin n) (Fin n) k)) hx).parts = {n - 1, 1} := by
  rw [topologicalKrullDim_range_projectiveOrbitMap_eq_finrank_range_ad_sl]
  norm_cast
  by_cases hn : n = 0
  · subst n
    simp [Module.finrank_eq_zero_of_subsingleton, jordanPartition_cotangentDualLieEquivSl_zero x hx,
      Nat.Partition.indiscrete, Multiset.filter_singleton]
  · simpa only [Fintype.card_fin] using finrank_range_ad_sl_add_card_add_two_eq_iff
      (by simpa using hn) (cotangentDualLieEquivSl n x) hx

end Orbit

end TauCeti.SpecialLinear

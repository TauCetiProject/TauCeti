/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1

/-!
# Algebraic `K₁` of division rings: stabilization and comparison with fields

Extending `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant`, this file proves
stabilization invariance of `TauCeti.dieudonneDet` (`TauCeti.dieudonneDet_stabilizeGL`), the
finite-rank kernel criterion (`TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`), and
compatibility over a field with `TauCeti.AlgebraicK1.detEquiv`.

## Main results

* `TauCeti.dieudonneDet_stabilizeGL`: stabilization `u ↦ u ⊕ 1` preserves `dieudonneDet`.
* `TauCeti.AlgebraicK1.mk_eq_one_iff_mem_elementarySubgroup`: over a division ring and for `2 ≤ n`,
  a matrix in `GL (Fin n) D` represents `1` in `K₁(D)` if and only if it already lies in `Eₙ(D)`.
* `TauCeti.AlgebraicK1.divisionRingEquiv_trans_equivOfComm_symm`: over a field `F`,
  `divisionRingEquiv F` agrees with `TauCeti.AlgebraicK1.detEquiv`.

## References

* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2, Theorem 2.2.5 and
  Corollary 2.2.6.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  1.2.4 and Example 1.3.5.
-/

public section

noncomputable section

namespace TauCeti

/-- Stabilization `u ↦ u ⊕ 1` preserves the Dieudonné determinant. -/
@[simp]
theorem dieudonneDet_stabilizeGL {D : Type*} [DivisionRing D] {a b : ℕ} (h : a ≤ b)
    (u : GL (Fin a) D) :
    dieudonneDet (Fin b) D (stabilizeGL D h u) = dieudonneDet (Fin a) D u := by
  simp [dieudonneDet_fin_apply]

namespace AlgebraicK1

/-- Over a division ring and in rank `2 ≤ n`, an invertible matrix represents `1` in
`AlgebraicK1 D` if and only if it already lies in `TauCeti.elementarySubgroup (Fin n) D`. -/
theorem mk_eq_one_iff_mem_elementarySubgroup {D : Type*} [DivisionRing D] {n : ℕ} (hn : 2 ≤ n)
    {u : GL (Fin n) D} :
    mk D n u = 1 ↔ u ∈ elementarySubgroup (Fin n) D := by
  rw [← MonoidHom.mem_ker, ker_mk_eq_elementarySubgroup (hasStableRangeLE_one_of_isLocalRing D) hn]

/-- Over a field `F`, composing `divisionRingEquiv F` with the abelianization equivalence recovers
`TauCeti.AlgebraicK1.detEquiv`. -/
theorem divisionRingEquiv_trans_equivOfComm_symm (F : Type*) [Field F] :
    (divisionRingEquiv F).trans Group.Abelianization.equivOfComm.symm =
      detEquiv (specialAlgebraicK1_eq_bot_of_euclideanDomain F) := by
  ext x
  simp [divisionRingEquiv_eq_abelianizationOf_det]

end AlgebraicK1

end TauCeti

end

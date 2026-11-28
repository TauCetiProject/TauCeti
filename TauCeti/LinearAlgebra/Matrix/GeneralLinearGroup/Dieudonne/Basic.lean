/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stability.Surjective

/-!
# Further properties of the Dieudonné determinant over a division ring

Extending `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant`, this file proves
further formulas and corollaries for `TauCeti.dieudonneDet : GL n D →* Group.Abelianization Dˣ`:
membership in the elementary subgroup, scalar and block-unipotent matrices, normality of
`TauCeti.elementarySubgroup n D` at every finite matrix size, and the finite-rank quotient
isomorphism `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ`.

For stabilization invariance and further properties on `AlgebraicK₁`, see
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.AlgebraicK1`.

## Main definitions

* `TauCeti.quotientElementarySubgroupDieudonneEquiv`: the canonical isomorphism
  `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ` for `2 ≤ Fintype.card n`.

## Main results

* `TauCeti.elementarySubgroup_normal`: `TauCeti.elementarySubgroup n D` is normal in `GL n D`.
* `TauCeti.dieudonneDet_eq_one_iff`: membership in `elementarySubgroup n D` vs. `dieudonneDet = 1`.
* `TauCeti.dieudonneDet_scalar`, `Matrix.dieudonneDet_upperBlockGL`,
  `Matrix.dieudonneDet_lowerBlockGL`: values on scalar and block-unipotent matrices.

## References

* J. Dieudonné, *Les déterminants sur un corps non commutatif*, Bull. Soc. Math. France **71**
  (1943), 27–45.
* E. Artin, *Geometric Algebra*, Interscience (1957), Chapter IV, §1–§2.
* J. Rosenberg, *Algebraic K-Theory and Its Applications*, GTM 147 (1994), §2.2.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, GSM 145 (2013), Chapter III,
  1.2.4, Example 1.3.5, and Exercise 1.2.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section DivisionRing

variable {n : Type*} [Fintype n] [DecidableEq n] {D : Type*} [DivisionRing D]

/-- In rank at least two, an invertible matrix over a division ring has Dieudonné determinant `1`
if and only if it belongs to the elementary subgroup. -/
theorem dieudonneDet_eq_one_iff (hn : 2 ≤ Fintype.card n) {g : GL n D} :
    dieudonneDet n D g = 1 ↔ g ∈ elementarySubgroup n D := by
  rw [← MonoidHom.mem_ker, ker_dieudonneDet hn]

/-- A scalar matrix `scalar n u` has Dieudonné determinant
`Group.Abelianization.of u ^ Fintype.card n`. -/
@[simp]
theorem dieudonneDet_scalar (u : Dˣ) :
    dieudonneDet n D (Matrix.GeneralLinearGroup.scalar n u) =
      Group.Abelianization.of u ^ Fintype.card n := by
  rw [← AlgebraicK1.divisionRingEquiv_mkOfFintype, AlgebraicK1.mkOfFintype_scalar, map_pow,
    AlgebraicK1.divisionRingEquiv_ofUnits]

end DivisionRing

/-! ## Finite-rank quotient by the elementary subgroup -/

/-- **The elementary subgroup is normal over a division ring**, already at every finite matrix
size. -/
instance elementarySubgroup_normal {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] : (elementarySubgroup n D).Normal := by
  by_cases hn : 2 ≤ Fintype.card n
  · exact elementarySubgroup_normal_of_hasStableRangeLE (hasStableRangeLE_one_of_isLocalRing D) hn
  · have : Subsingleton n := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hbot : elementarySubgroup n D = ⊥ :=
      le_bot_iff.mp (elementarySubgroup_le_iff.2 fun i j hij _ ↦ absurd (Subsingleton.elim i j) hij)
    rw [hbot]
    infer_instance

/-- In rank at least two, the Dieudonné determinant descends to a canonical isomorphism
`GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ`. -/
def quotientElementarySubgroupDieudonneEquiv (n : Type*) [Fintype n] [DecidableEq n]
    (D : Type*) [DivisionRing D] (hn : 2 ≤ Fintype.card n) :
    GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ :=
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  QuotientGroup.liftEquiv (elementarySubgroup n D) dieudonneDet_surjective
    (ker_dieudonneDet hn).symm

/-- `TauCeti.quotientElementarySubgroupDieudonneEquiv` evaluates on a coset `QuotientGroup.mk g` as
`dieudonneDet n D g`. -/
@[simp]
theorem quotientElementarySubgroupDieudonneEquiv_mk {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (g : GL n D) :
    quotientElementarySubgroupDieudonneEquiv n D hn (QuotientGroup.mk g) =
      dieudonneDet n D g :=
  QuotientGroup.liftEquiv_mk (elementarySubgroup n D) _ _ g

/-- The inverse of `TauCeti.quotientElementarySubgroupDieudonneEquiv` sends
`Group.Abelianization.of u` to the coset of `diagGL (Pi.mulSingle i u)` at any index `i : n`. -/
theorem quotientElementarySubgroupDieudonneEquiv_symm_of {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (i : n) (u : Dˣ) :
    (quotientElementarySubgroupDieudonneEquiv n D hn).symm (Group.Abelianization.of u) =
      QuotientGroup.mk (diagGL (Pi.mulSingle i u)) := by
  rw [← dieudonneDet_diagGL_mulSingle i u,
    ← quotientElementarySubgroupDieudonneEquiv_mk hn, MulEquiv.symm_apply_apply]

end TauCeti

namespace Matrix

open TauCeti

section DivisionRing

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  {D : Type*} [DivisionRing D]

/-- Every upper block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_upperBlockGL (X : Matrix n m D) :
    dieudonneDet (n ⊕ m) D (upperBlockGL X) = 1 :=
  elementarySubgroup_le_ker_dieudonneDet (upperBlockGL_mem_elementarySubgroup X)

/-- Every lower block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_lowerBlockGL (Y : Matrix m n D) :
    dieudonneDet (n ⊕ m) D (lowerBlockGL Y) = 1 :=
  elementarySubgroup_le_ker_dieudonneDet (lowerBlockGL_mem_elementarySubgroup Y)

end DivisionRing

end Matrix

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.GaussJordan
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant

/-!
# Further properties of the Dieudonné determinant over a division ring

Extending `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DieudonneDeterminant`, this file proves
further formulas and corollaries for `TauCeti.dieudonneDet : GL n D →* Group.Abelianization Dˣ`:
membership in the elementary subgroup, scalar and block-unipotent matrices, commutator-kernel
vanishing for nontrivial `Dˣ`, naturality under `Matrix.GeneralLinearGroup.map`, and the
finite-rank quotient isomorphism
`GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ`.

For stabilization invariance and further properties on `AlgebraicK₁`, see
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Dieudonne.AlgebraicK1`.

## Main definitions

* `TauCeti.quotientElementarySubgroupDieudonneEquiv`: the canonical isomorphism
  `GL n D ⧸ TauCeti.elementarySubgroup n D ≃* Group.Abelianization Dˣ` for `2 ≤ Fintype.card n`.

## Main results

* `TauCeti.dieudonneDet_of_mem_elementarySubgroup`,
  `TauCeti.dieudonneDet_eq_one_iff`: membership in `elementarySubgroup n D` vs. `dieudonneDet = 1`.
* `TauCeti.dieudonneDet_scalar`, `TauCeti.dieudonneDet_upperBlockGL`,
  `TauCeti.dieudonneDet_lowerBlockGL`: values on scalar and block-unipotent matrices.
* `TauCeti.elementarySubgroup_le_ker_of_nontrivial`: when `Dˣ` is nontrivial, every homomorphism
  from `GL n D` to a commutative group vanishes on `elementarySubgroup n D`.
* `TauCeti.dieudonneDet_map`: naturality under `Matrix.GeneralLinearGroup.map` over fields.

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

/-- Every matrix in the elementary subgroup has Dieudonné determinant `1`. -/
theorem dieudonneDet_of_mem_elementarySubgroup {g : GL n D}
    (hg : g ∈ elementarySubgroup n D) : dieudonneDet n D g = 1 :=
  elementarySubgroup_le_ker_dieudonneDet hg

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
  rw [← diagGL_const, dieudonneDet_diagGL, Finset.prod_const, Finset.card_univ]

/-- When `Dˣ` is nontrivial, every homomorphism from `GL n D` into a commutative group vanishes on
`TauCeti.elementarySubgroup n D`. (Over `𝔽₂` in rank `2`, `GL₂(𝔽₂) = E₂(𝔽₂) ≅ S₃` admits the
nontrivial sign homomorphism to `ℤˣ`, so `[Nontrivial Dˣ]` cannot be dropped.) -/
theorem elementarySubgroup_le_ker_of_nontrivial [Nontrivial Dˣ] {G : Type*} [CommGroup G]
    (φ : GL n D →* G) :
    elementarySubgroup n D ≤ φ.ker := by
  obtain ⟨u, hu⟩ := exists_ne (1 : Dˣ)
  exact (elementarySubgroup_le_commutator_of_ne u.ne_zero
    (fun h ↦ hu (Units.ext h))).trans (Group.Abelianization.commutator_le_ker φ)

/-- Every upper block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_upperBlockGL {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix n m D) :
    dieudonneDet (n ⊕ m) D (Matrix.upperBlockGL X) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.upperBlockGL_mem_elementarySubgroup X)

/-- Every lower block-unipotent matrix has Dieudonné determinant `1`. -/
@[simp]
theorem dieudonneDet_lowerBlockGL {m : Type*} [Fintype m] [DecidableEq m] (Y : Matrix m n D) :
    dieudonneDet (n ⊕ m) D (Matrix.lowerBlockGL Y) = 1 :=
  dieudonneDet_of_mem_elementarySubgroup (Matrix.lowerBlockGL_mem_elementarySubgroup Y)

end DivisionRing

section Field

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Naturality of the Dieudonné determinant under `Matrix.GeneralLinearGroup.map` over fields. -/
@[simp]
theorem dieudonneDet_map {F K : Type*} [Field F] [Field K] (f : F →+* K) (g : GL n F) :
    dieudonneDet n K (Matrix.GeneralLinearGroup.map f g) =
      Group.Abelianization.map (Units.map (f : F →* K)) (dieudonneDet n F g) :=
  dieudonneDet_unitsMap_mapMatrix f g

end Field

/-! ## Finite-rank quotient by the elementary subgroup -/

/-- In rank at least two, the Dieudonné determinant descends to a canonical isomorphism
`GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ`. -/
def quotientElementarySubgroupDieudonneEquiv (n : Type*) [Fintype n] [DecidableEq n]
    (D : Type*) [DivisionRing D] (hn : 2 ≤ Fintype.card n) :
    GL n D ⧸ elementarySubgroup n D ≃* Group.Abelianization Dˣ :=
  haveI : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  (QuotientGroup.quotientMulEquivOfEq (ker_dieudonneDet (n := n) (D := D) hn).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (dieudonneDet n D) dieudonneDet_surjective)

/-- `TauCeti.quotientElementarySubgroupDieudonneEquiv` evaluates on a coset `QuotientGroup.mk g` as
`dieudonneDet n D g`. -/
@[simp]
theorem quotientElementarySubgroupDieudonneEquiv_mk {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (g : GL n D) :
    quotientElementarySubgroupDieudonneEquiv n D hn (QuotientGroup.mk g) =
      dieudonneDet n D g := by
  simp [quotientElementarySubgroupDieudonneEquiv, QuotientGroup.quotientKerEquivOfSurjective]

/-- The inverse of `TauCeti.quotientElementarySubgroupDieudonneEquiv` sends
`Group.Abelianization.of u` to the coset of `diagGL (Pi.mulSingle i u)` at any index `i : n`. -/
theorem quotientElementarySubgroupDieudonneEquiv_symm_of {n : Type*} [Fintype n] [DecidableEq n]
    {D : Type*} [DivisionRing D] (hn : 2 ≤ Fintype.card n) (i : n) (u : Dˣ) :
    (quotientElementarySubgroupDieudonneEquiv n D hn).symm (Group.Abelianization.of u) =
      QuotientGroup.mk (diagGL (Pi.mulSingle i u)) := by
  rw [← dieudonneDet_diagGL_mulSingle i u,
    ← quotientElementarySubgroupDieudonneEquiv_mk hn, MulEquiv.symm_apply_apply]

end TauCeti

end

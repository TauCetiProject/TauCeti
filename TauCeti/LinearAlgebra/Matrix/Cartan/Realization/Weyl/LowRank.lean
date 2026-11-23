/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.LowRank
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Rank-one and rank-two Weyl groups of Cartan realizations

Over a field of characteristic zero, combining `TauCeti.CartanRealization.weylCoxeterSystem` with
the low-rank Coxeter identifications in `TauCeti.GroupTheory.Coxeter.LowRank` yields explicit
group isomorphisms and cardinalities for rank-one and rank-two generalized Cartan matrices:

* For `[Unique I]`, `R.weylGroup _` is isomorphic to `Multiplicative (ZMod 2)` via length parity
  (`weylGroupUniqueEquivZModTwo`), specializing to type `A₁` (`weylGroupAOneEquivZModTwo`,
  `natCard_weylGroup_A_one`).
* For any `2 × 2` generalized Cartan matrix `A`, `R.weylGroup _` is isomorphic to
  `DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A 0 1)`
  (`weylGroupFinTwoEquivDihedralGroup`), covering finite dihedral Weyl groups such as `B₂` (order
  `8`) and `G₂` (order `12`) as well as the infinite dihedral Weyl group `DihedralGroup 0` of
  affine `A₁⁽¹⁾ = !![2, -2; -2, 2]` (`weylGroupTwoNegTwoEquivDihedralGroup`).

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §3.7 and Proposition 3.13.
-/

public section

open Module

namespace TauCeti.CartanRealization

section Field
variable {K H : Type*} [Field K] [AddCommGroup H] [Module K H]

/-- Explicit action of `s₀ s₁` on `α₁` for the affine `A₁⁽¹⁾` matrix `!![2, -2; -2, 2]`. -/
theorem simpleReflection_mul_root_two_neg_two
    (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → K) i i = 2) :
    (R.simpleReflection hdiag 0 * R.simpleReflection hdiag 1) (R.root 1) =
      -R.root 1 - (2 : ℤ) • R.root 0 := by
  rw [mul_apply_eq_comp, simpleReflection_root_self, map_neg, simpleReflection_root,
    Matrix.map_apply]
  have h01 : (!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -2 := by decide
  rw [h01, Int.cast_smul_eq_zsmul K (-2) (R.root 0)]
  abel

variable [CharZero K]

section Unique
variable {I : Type*} [Unique I] {A : Matrix I I ℤ}
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H) (hdiag : ∀ i, A i i = 2)

open scoped Classical in
/-- **Rank-one realizations**: the Weyl group on `[Unique I]` is isomorphic to
`Multiplicative (ZMod 2)` via length parity. -/
noncomputable def weylGroupUniqueEquivZModTwo :
    R.weylGroup (diag_map_intCast hdiag) ≃* Multiplicative (ZMod 2) :=
  let hA := Matrix.IsGeneralizedCartan.of_subsingleton hdiag
  (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm).uniqueEquivZModTwo

open scoped Classical in
@[simp]
theorem weylGroupUniqueEquivZModTwo_weylSimple (i : I) :
    R.weylGroupUniqueEquivZModTwo hdiag (R.weylSimple (diag_map_intCast hdiag) i) =
      Multiplicative.ofAdd 1 := by
  let hA := Matrix.IsGeneralizedCartan.of_subsingleton hdiag
  rw [weylGroupUniqueEquivZModTwo,
    ← R.weylCoxeterSystem_simple hA.diag hA.offDiag_nonpos hA.zero_comm]
  exact (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm).uniqueEquivZModTwo_simple i

/-- Every rank-one realization in characteristic zero has Weyl group of cardinality `2`. -/
@[simp]
theorem natCard_weylGroup_of_unique :
    Nat.card (R.weylGroup (diag_map_intCast hdiag)) = 2 := by
  classical
  let hA := Matrix.IsGeneralizedCartan.of_subsingleton hdiag
  exact (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm).natCard_eq_two

end Unique

section AOne
variable (R : CartanRealization ((CartanMatrix.A 1).map (Int.cast : ℤ → K)) H)

/-- **Type `A₁`**: the Weyl group is isomorphic to `Multiplicative (ZMod 2)` via length parity. -/
noncomputable def weylGroupAOneEquivZModTwo :
    R.weylGroup (diag_map_intCast (CartanMatrix.isGeneralizedCartan_A 1).diag) ≃*
      Multiplicative (ZMod 2) :=
  R.weylGroupUniqueEquivZModTwo (CartanMatrix.isGeneralizedCartan_A 1).diag

@[simp]
theorem weylGroupAOneEquivZModTwo_weylSimple (i : Fin 1) :
    R.weylGroupAOneEquivZModTwo
        (R.weylSimple (diag_map_intCast (CartanMatrix.isGeneralizedCartan_A 1).diag) i) =
      Multiplicative.ofAdd 1 :=
  R.weylGroupUniqueEquivZModTwo_weylSimple (CartanMatrix.isGeneralizedCartan_A 1).diag i

/-- The Weyl group of type `A₁` has cardinality `2`. -/
@[simp]
theorem natCard_weylGroup_A_one :
    Nat.card (R.weylGroup (diag_map_intCast (CartanMatrix.isGeneralizedCartan_A 1).diag)) = 2 :=
  R.natCard_weylGroup_of_unique (CartanMatrix.isGeneralizedCartan_A 1).diag

end AOne

section FinTwo
variable {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsGeneralizedCartan)
  (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)

/-- **Rank-two generalized Cartan matrices**: `R.weylGroup _` is isomorphic to
`DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A 0 1)`. -/
noncomputable def weylGroupFinTwoEquivDihedralGroup :
    R.weylGroup (diag_map_intCast hA.diag) ≃*
      DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A 0 1) :=
  (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm).finTwoEquivDihedralGroup

@[simp]
theorem weylGroupFinTwoEquivDihedralGroup_weylSimple_zero :
    R.weylGroupFinTwoEquivDihedralGroup hA (R.weylSimple (diag_map_intCast hA.diag) 0) =
      DihedralGroup.sr 0 := by
  rw [weylGroupFinTwoEquivDihedralGroup,
    ← R.weylCoxeterSystem_simple hA.diag hA.offDiag_nonpos hA.zero_comm]
  exact (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos
    hA.zero_comm).finTwoEquivDihedralGroup_simple_zero

@[simp]
theorem weylGroupFinTwoEquivDihedralGroup_weylSimple_one :
    R.weylGroupFinTwoEquivDihedralGroup hA (R.weylSimple (diag_map_intCast hA.diag) 1) =
      DihedralGroup.sr 1 := by
  rw [weylGroupFinTwoEquivDihedralGroup,
    ← R.weylCoxeterSystem_simple hA.diag hA.offDiag_nonpos hA.zero_comm]
  exact (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos
    hA.zero_comm).finTwoEquivDihedralGroup_simple_one

/-- For any rank-two generalized Cartan matrix `A`, `Nat.card (R.weylGroup _) = 2 * m₀₁`.
In the affine or hyperbolic case `coxeterMatrixOfGeneralizedCartanMatrix A 0 1 = 0`, the Weyl group
is infinite and `Nat.card` is `0`. -/
@[simp]
theorem natCard_weylGroup_fin_two :
    Nat.card (R.weylGroup (diag_map_intCast hA.diag)) =
      2 * coxeterMatrixOfGeneralizedCartanMatrix A 0 1 :=
  (R.weylCoxeterSystem hA.diag hA.offDiag_nonpos hA.zero_comm).natCard_eq_two_mul

end FinTwo

/-- The Weyl group of type `B₂` has cardinality `8`. -/
@[simp]
theorem natCard_weylGroup_B_two
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast (CartanMatrix.isGeneralizedCartan_B 2).diag)) = 8 := by
  rw [R.natCard_weylGroup_fin_two (CartanMatrix.isGeneralizedCartan_B 2),
    coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_B]
  decide

/-- The Weyl group of type `G₂` has cardinality `12`. -/
@[simp]
theorem natCard_weylGroup_G₂
    (R : CartanRealization (CartanMatrix.G₂.map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast CartanMatrix.isGeneralizedCartan_G₂.diag)) = 12 := by
  rw [R.natCard_weylGroup_fin_two CartanMatrix.isGeneralizedCartan_G₂,
    coxeterMatrixOfGeneralizedCartanMatrix_cartanMatrix_G₂]
  decide

section AffineAOne
variable (R : CartanRealization ((!![2, -2; -2, 2] : Matrix (Fin 2) (Fin 2) ℤ).map
    (Int.cast : ℤ → K)) H)

/-- **Affine `A₁⁽¹⁾`**: its Weyl group is isomorphic to the infinite dihedral group
`DihedralGroup 0`. -/
noncomputable def weylGroupTwoNegTwoEquivDihedralGroup :
    R.weylGroup (diag_map_intCast Matrix.isGeneralizedCartan_two_neg_two.diag) ≃*
      DihedralGroup 0 :=
  (R.weylGroupFinTwoEquivDihedralGroup Matrix.isGeneralizedCartan_two_neg_two).trans
    (MulEquiv.cast (M := DihedralGroup) coxeterMatrixOfGeneralizedCartanMatrix_two_neg_two_zero_one)

@[simp]
theorem weylGroupTwoNegTwoEquivDihedralGroup_weylSimple_zero :
    R.weylGroupTwoNegTwoEquivDihedralGroup
        (R.weylSimple (diag_map_intCast Matrix.isGeneralizedCartan_two_neg_two.diag) 0) =
      DihedralGroup.sr 0 := by
  simp [weylGroupTwoNegTwoEquivDihedralGroup]

@[simp]
theorem weylGroupTwoNegTwoEquivDihedralGroup_weylSimple_one :
    R.weylGroupTwoNegTwoEquivDihedralGroup
        (R.weylSimple (diag_map_intCast Matrix.isGeneralizedCartan_two_neg_two.diag) 1) =
      DihedralGroup.sr 1 := by
  simp [weylGroupTwoNegTwoEquivDihedralGroup]

/-- For affine `A₁⁽¹⁾`, `s₀ * s₁` has infinite order (`orderOf = 0`) in `R.weylGroup _`. -/
theorem orderOf_weylSimple_mul_two_neg_two :
    orderOf (R.weylSimple (diag_map_intCast Matrix.isGeneralizedCartan_two_neg_two.diag) 0 *
      R.weylSimple (diag_map_intCast Matrix.isGeneralizedCartan_two_neg_two.diag) 1) = 0 := by
  rw [R.orderOf_weylSimple_mul_weylSimple _ (Matrix.isGeneralizedCartan_two_neg_two.zero_comm 0 1),
    coxeterMatrixOfGeneralizedCartanMatrix_two_neg_two_zero_one]

end AffineAOne
end Field

end TauCeti.CartanRealization

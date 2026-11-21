/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Coxeter

/-!
# Rank-two Weyl groups as dihedral groups

For a realization `R` of a rank-two generalized Cartan matrix `A` on `{i, j}` over a
characteristic-zero field, `R.weylGroup` is canonically isomorphic to
`DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A i j)`. This specializes to:

* **Type `B₂`**: `DihedralGroup 4` of order `8` (`m₀₁ = 4`, not `3`);
* **Affine type `A₁⁽¹⁾`**: the infinite dihedral group `DihedralGroup 0`, with `s₀ s₁` of infinite
  order and `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)`.

## Main definitions

* `TauCeti.CartanRealization.dihedralGroupMulEquivWeyl`: isomorphism of a rank-two Weyl group with
  `DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A i j)`.
* `TauCeti.CartanRealization.dihedralGroupFourEquivWeylBTwo`: isomorphism
  `DihedralGroup 4 ≃* W(B₂)`.
* `TauCeti.CartanRealization.dihedralGroupZeroEquivWeylAffineAOne`: isomorphism
  `DihedralGroup 0 ≃* W(A₁⁽¹⁾)`.

## Main results

* `TauCeti.CartanRealization.card_weylGroup_B_two`: `Nat.card (W(B₂)) = 8`.
* `TauCeti.CartanRealization.orderOf_weylSimple_mul_affine_A_one` and
  `TauCeti.CartanRealization.instInfiniteWeylGroupAffineAOne`: `s₀ s₁` has infinite order and
  `W(A₁⁽¹⁾)` is infinite.
* `TauCeti.CartanRealization.weylSimple_zero_mul_one_root_one_affine_A_one`:
  `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7 and 3.13.
-/

public section

open Module

namespace TauCeti.CartanRealization

section RankTwo

/-- **Order of a product of two simple reflections in `R.weylGroup`**: `orderOf (sᵢ * sⱼ)` equals
the Coxeter matrix entry `coxeterMatrixOfGeneralizedCartanMatrix A i j`. -/
@[simp]
theorem orderOf_weylSimple_mul_weylSimple {I K H : Type*} [DecidableEq I] [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) (hoff : ∀ i j, i ≠ j → A i j ≤ 0)
    (hzero : ∀ i j, A i j = 0 ↔ A j i = 0) (i j : I) :
    orderOf (R.weylSimple (diag_map_intCast hdiag) i *
        R.weylSimple (diag_map_intCast hdiag) j) =
      coxeterMatrixOfGeneralizedCartanMatrix A i j := by
  have hcoe : orderOf (R.weylSimple (diag_map_intCast hdiag) i *
      R.weylSimple (diag_map_intCast hdiag) j) =
      orderOf (R.simpleReflection (diag_map_intCast hdiag) i *
        R.simpleReflection (diag_map_intCast hdiag) j) := by
    rw [← orderOf_injective (R.weylGroup (diag_map_intCast hdiag)).subtype
      Subtype.coe_injective (R.weylSimple (diag_map_intCast hdiag) i *
        R.weylSimple (diag_map_intCast hdiag) j),
      map_mul, Subgroup.coe_subtype, coe_weylSimple, coe_weylSimple]
  rw [hcoe]
  refine R.orderOf_simpleReflection_mul_simpleReflection (diag_map_intCast hdiag)
    (hzero i j) ?_
  rcases eq_or_ne i j with rfl | hij
  · exact mul_self_nonneg _
  · exact mul_nonneg_of_nonpos_of_nonpos (hoff i j hij) (hoff j i hij.symm)

/-- **Rank-two Weyl groups are dihedral**: for any generalized Cartan matrix on `{i, j}` over a
characteristic-zero field, `R.weylGroup` is isomorphic to
`DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A i j)` — finite of order `2 * mᵢⱼ` when
`aᵢⱼ aⱼᵢ ≤ 3`, and the infinite dihedral group `DihedralGroup 0` when `aᵢⱼ aⱼᵢ ≥ 4`. -/
noncomputable def dihedralGroupMulEquivWeyl {I K H : Type*} [DecidableEq I] [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ k, A k k = 2) (hoff : ∀ k l, k ≠ l → A k l ≤ 0)
    (hzero : ∀ k l, A k l = 0 ↔ A l k = 0) {i j : I} (hpair : ∀ k : I, k = i ∨ k = j) :
    DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix A i j) ≃*
      R.weylGroup (diag_map_intCast hdiag) := by
  have hrange : ({R.weylSimple (diag_map_intCast hdiag) i,
      R.weylSimple (diag_map_intCast hdiag) j} : Set _) =
      Set.range (R.weylSimple (diag_map_intCast hdiag)) := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun h ↦ h.elim (fun h ↦ ⟨i, h.symm⟩) (fun h ↦ ⟨j, h.symm⟩), fun ⟨k, hk⟩ ↦ ?_⟩
    rcases hpair k with rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
  exact TauCeti.dihedralGroupMulEquiv (R.weylSimple_mul_self _ i) (R.weylSimple_mul_self _ j)
    (R.weylSimple_ne_one _ i) (R.weylSimple_ne_one _ j)
    (R.orderOf_weylSimple_mul_weylSimple hdiag hoff hzero i j)
    (by rw [hrange, R.closure_range_weylSimple])

private theorem coxeterMatrix_B_two_zero_one :
    coxeterMatrixOfGeneralizedCartanMatrix (CartanMatrix.B 2) 0 1 = 4 := by
  have hprod : CartanMatrix.B 2 0 1 * CartanMatrix.B 2 1 0 = 2 := by
    rw [CartanMatrix.B_two]; decide
  rw [coxeterMatrixOfGeneralizedCartanMatrix_apply_of_lt_four _ (by decide) (by omega), hprod,
    coxeterOrder_two]

/-- **Type `B₂` Weyl group**: isomorphic to `DihedralGroup 4`. -/
noncomputable def dihedralGroupFourEquivWeylBTwo {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 4 ≃* R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2)) :=
  (by rw [coxeterMatrix_B_two_zero_one] :
      DihedralGroup 4 ≃* DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix
        (CartanMatrix.B 2) 0 1)).trans <|
    R.dihedralGroupMulEquivWeyl (CartanMatrix.B_diag 2) (CartanMatrix.B_off_diag_nonpos 2)
      (by rw [CartanMatrix.B_two]; simp [Fin.forall_fin_two])
      (i := 0) (j := 1) (fun k ↦ by fin_cases k <;> simp)

/-- **Type `B₂` cardinality check**: `|W(B₂)| = 8`. -/
theorem card_weylGroup_B_two {K H : Type*} [Field K] [CharZero K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2))) = 8 := by
  rw [← Nat.card_congr (R.dihedralGroupFourEquivWeylBTwo).toEquiv, DihedralGroup.nat_card]

private theorem coxeterMatrix_affine_A_one_zero_one :
    coxeterMatrixOfGeneralizedCartanMatrix !![(2 : ℤ), -2; -2, 2] 0 1 = 0 :=
  coxeterMatrixOfGeneralizedCartanMatrix_apply_of_four_le _ (by decide) (by decide)

/-- **Affine `A₁⁽¹⁾` Weyl group**: isomorphic to the infinite dihedral group `DihedralGroup 0`. -/
noncomputable def dihedralGroupZeroEquivWeylAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 0 ≃*
      R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) :=
  (by rw [coxeterMatrix_affine_A_one_zero_one] :
      DihedralGroup 0 ≃*
        DihedralGroup (coxeterMatrixOfGeneralizedCartanMatrix
          !![(2 : ℤ), -2; -2, 2] 0 1)).trans <|
    R.dihedralGroupMulEquivWeyl (by decide) (by simp [Fin.forall_fin_two])
      (by simp [Fin.forall_fin_two]) (i := 0) (j := 1) (fun k ↦ by fin_cases k <;> simp)

/-- **Affine `A₁⁽¹⁾` infinite-order check**: `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_weylSimple_mul_affine_A_one {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1) = 0 := by
  rw [R.orderOf_weylSimple_mul_weylSimple (by decide) (by simp [Fin.forall_fin_two])
    (by simp [Fin.forall_fin_two]) 0 1, coxeterMatrix_affine_A_one_zero_one]

/-- The Weyl group of affine `A₁⁽¹⁾` is infinite. -/
instance instInfiniteWeylGroupAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    Infinite (R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))) :=
  Infinite.of_injective _ R.dihedralGroupZeroEquivWeylAffineAOne.injective

/-- **Affine `A₁⁽¹⁾` translation check**: `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)` (`= α₁ - 2δ` for the
null root `δ = α₀ + α₁`). -/
theorem weylSimple_zero_mul_one_root_one_affine_A_one {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    ((R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1 :
        R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))) :
        Dual K H ≃ₗ[K] Dual K H) (R.root 1) =
      R.root 1 - (2 : K) • (R.root 0 + R.root 1) := by
  rw [Subgroup.coe_mul, mul_apply_eq_comp, coe_weylSimple, coe_weylSimple,
    simpleReflection_root_self, map_neg, simpleReflection_root]
  have h01 : ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) 0 1 = -2 := by simp
  rw [h01]
  module

end RankTwo

end TauCeti.CartanRealization

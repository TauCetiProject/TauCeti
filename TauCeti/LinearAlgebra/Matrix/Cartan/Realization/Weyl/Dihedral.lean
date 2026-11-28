/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Weyl.Basic

/-!
# Rank-two Weyl groups and two-reflection dihedral subgroups

For a realization `R` of any matrix `A` with diagonal `2` over any field, any pair of simple
reflections `sᵢ = R.weylSimple hdiag i` and `sⱼ = R.weylSimple hdiag j` generates a dihedral
subgroup `Subgroup.closure {sᵢ, sⱼ} ≃* DihedralGroup (orderOf (sᵢ * sⱼ))` via
`TauCeti.dihedralGroupMulEquivClosure`. When `{i, j}` exhausts the index set `I`, this identifies
the whole Weyl group `R.weylGroup hdiag` with `DihedralGroup (orderOf (sᵢ * sⱼ))`
(`TauCeti.CartanRealization.dihedralGroupMulEquivWeyl`).

* **Order-four pairs and type `B₂`**: for any `i, j` with `A i j * A j i = 2` and
  `A i j ≠ 0 ∨ A j i ≠ 0`, `sᵢ * sⱼ` has order `4` over any field
  (`TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four`), specializing in type
  `B₂` to `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four_B_two` and
  `DihedralGroup 4 ≃* W(B₂)` of order `8`.
* **Generalized Cartan matrices in characteristic zero**: `orderOf (sᵢ * sⱼ)` equals
  `coxeterMatrixOfGeneralizedCartanMatrix A i j`
  (`TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple`), which specializes in affine type
  `A₁⁽¹⁾` to the infinite dihedral group `DihedralGroup 0`, with `s₀ s₁` of infinite order and
  `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)`.

## Main definitions

* `TauCeti.CartanRealization.dihedralGroupMulEquivWeyl`: isomorphism of a rank-two Weyl group with
  `DihedralGroup n` for `n = orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j)` over any field.
* `TauCeti.CartanRealization.dihedralGroupFourEquivWeylBTwo`: isomorphism
  `DihedralGroup 4 ≃* W(B₂)` over any field.
* `TauCeti.CartanRealization.dihedralGroupZeroEquivWeylAffineAOne`: isomorphism
  `DihedralGroup 0 ≃* W(A₁⁽¹⁾)`.

## Main results

* `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four`,
  `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four_B_two`, and
  `TauCeti.CartanRealization.card_weylGroup_B_two`: `orderOf (sᵢ * sⱼ) = 4` whenever
  `A i j * A j i = 2` and `A i j ≠ 0 ∨ A j i ≠ 0`, and `Nat.card (W(B₂)) = 8` over any field.
* `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_zero_affine_A_one` and
  `TauCeti.CartanRealization.instInfiniteWeylGroupAffineAOne`: `s₀ s₁` has infinite order and
  `W(A₁⁽¹⁾)` is infinite.
* `TauCeti.CartanRealization.weylSimple_mul_weylSimple_apply_root_affine_A_one`:
  `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, Cambridge University Press, 1990,
  §§3.7 and 3.13.
-/

public section

open Module

namespace TauCeti.CartanRealization

section RankTwo

/-- **Rank-two Weyl groups are dihedral**: for a realization of a matrix `A` with diagonal `2`
whose index set is `{i, j}` (`hpair`) over any field `K`, `R.weylGroup hdiag` is isomorphic to
`DihedralGroup n` for any `n` equal to
`orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j)`. Over a characteristic-zero field,
`TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple` computes this order as
`coxeterMatrixOfGeneralizedCartanMatrix A i j` when `A` is an integral matrix satisfying
`A i j = 0 ↔ A j i = 0` and `0 ≤ A i j * A j i`. -/
noncomputable def dihedralGroupMulEquivWeyl {I K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ k, A k k = 2)
    {i j : I} (hpair : ∀ k : I, k = i ∨ k = j) {n : ℕ}
    (hn : orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j) = n) :
    DihedralGroup n ≃* R.weylGroup hdiag := by
  have hrange : ({R.weylSimple hdiag i, R.weylSimple hdiag j} : Set _) =
      Set.range (R.weylSimple hdiag) := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun h ↦ h.elim (fun h ↦ ⟨i, h.symm⟩) (fun h ↦ ⟨j, h.symm⟩), fun ⟨k, hk⟩ ↦ ?_⟩
    rcases hpair k with rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
  exact TauCeti.dihedralGroupMulEquiv (R.weylSimple_mul_self hdiag i)
    (R.weylSimple_mul_self hdiag j) (R.weylSimple_ne_one hdiag i)
    (R.weylSimple_ne_one hdiag j) hn (by rw [hrange, R.closure_range_weylSimple])

/-- `TauCeti.CartanRealization.dihedralGroupMulEquivWeyl` evaluates to `TauCeti.dihedralHom`. -/
@[simp]
theorem dihedralGroupMulEquivWeyl_apply {I K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ k, A k k = 2)
    {i j : I} (hpair : ∀ k : I, k = i ∨ k = j) {n : ℕ}
    (hn : orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j) = n)
    (x : DihedralGroup n) :
    R.dihedralGroupMulEquivWeyl hdiag hpair hn x =
      TauCeti.dihedralHom (R.weylSimple_mul_self hdiag i) (R.weylSimple_mul_self hdiag j)
        (hn ▸ pow_orderOf_eq_one _) x :=
  TauCeti.dihedralGroupMulEquiv_apply _ _ _ _ _ _ x

/-- **Order-four pair in `R.weylGroup`**: over any field `K` (including characteristic `2`),
for indices `i, j : I` with `A i j * A j i = 2` and `A i j ≠ 0 ∨ A j i ≠ 0` (which implies
`i ≠ j`), the product `R.weylSimple hdiag i * R.weylSimple hdiag j` has order `4`. -/
theorem orderOf_weylSimple_mul_weylSimple_eq_four {I K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ k, A k k = 2) {i j : I}
    (hprod : A i j * A j i = 2) (hne : A i j ≠ 0 ∨ A j i ≠ 0) :
    orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j) = 4 := by
  have hij : i ≠ j := by
    rintro rfl
    have h2 : (2 : K) * 2 = 2 := by simpa [hdiag i] using hprod
    have h2ne : (2 : K) ≠ 0 := by simpa [hdiag i] using hne
    have h21 : (2 : K) = 1 := mul_right_cancel₀ h2ne (by simpa using h2)
    exact one_ne_zero (by linear_combination h21)
  have hfi : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [hdiag i]
  have hfj : Dual.eval K H (R.coroot j) (R.root j) = 2 := by simp [hdiag j]
  have heval : Dual.eval K H (R.coroot i) (R.root j) *
      Dual.eval K H (R.coroot j) (R.root i) = 2 := by
    simpa [R.root_coroot] using hprod
  have hnc : ¬Commute (R.simpleReflection hdiag i) (R.simpleReflection hdiag j) := by
    rw [R.commute_simpleReflection_iff_eq_zero hdiag hij]
    exact fun ⟨hij0, hji0⟩ ↦ hne.elim (fun h ↦ h hij0) (fun h ↦ h hji0)
  rw [← Subgroup.orderOf_coe, Subgroup.coe_mul, coe_weylSimple, coe_weylSimple]
  rw [R.simpleReflection_eq_reflection hdiag i hfi,
    R.simpleReflection_eq_reflection hdiag j hfj] at hnc ⊢
  exact Module.orderOf_reflection_mul_reflection_eq_four_of_not_commute heval hnc

/-- **Type `B₂` product-order check**: `s₀ * s₁` has order `4` over any field. -/
theorem orderOf_weylSimple_mul_weylSimple_eq_four_B_two {K H : Type*} [Field K] [AddCommGroup H]
    [Module K H] (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 0 *
        R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 1) = 4 :=
  R.orderOf_weylSimple_mul_weylSimple_eq_four (diag_map_intCast (CartanMatrix.B_diag 2))
    (by simp [CartanMatrix.B_two]) (Or.inr (by simp [CartanMatrix.B_two]))

/-- **Type `B₂` Weyl group**: isomorphic to `DihedralGroup 4` over any field. -/
noncomputable def dihedralGroupFourEquivWeylBTwo {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 4 ≃* R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2)) :=
  R.dihedralGroupMulEquivWeyl (diag_map_intCast (CartanMatrix.B_diag 2))
    (fun k ↦ by fin_cases k <;> simp) R.orderOf_weylSimple_mul_weylSimple_eq_four_B_two

/-- `TauCeti.CartanRealization.dihedralGroupFourEquivWeylBTwo` evaluates to `TauCeti.dihedralHom`.
-/
@[simp]
theorem dihedralGroupFourEquivWeylBTwo_apply {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H)
    (x : DihedralGroup 4) :
    R.dihedralGroupFourEquivWeylBTwo x =
      TauCeti.dihedralHom (R.weylSimple_mul_self _ 0) (R.weylSimple_mul_self _ 1)
        (R.orderOf_weylSimple_mul_weylSimple_eq_four_B_two ▸ pow_orderOf_eq_one _) x :=
  R.dihedralGroupMulEquivWeyl_apply _ _ R.orderOf_weylSimple_mul_weylSimple_eq_four_B_two x

/-- **Type `B₂` cardinality check**: `|W(B₂)| = 8` over any field. -/
theorem card_weylGroup_B_two {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2))) = 8 := by
  rw [← Nat.card_congr (R.dihedralGroupFourEquivWeylBTwo).toEquiv, DihedralGroup.nat_card]

/-- **Affine `A₁⁽¹⁾` infinite-order check**: `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_weylSimple_mul_weylSimple_eq_zero_affine_A_one {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1) = 0 := by
  rw [R.orderOf_weylSimple_mul_weylSimple (by decide) (by decide) (by decide),
    coxeterMatrixOfGeneralizedCartanMatrix_apply_of_four_le _ (by decide) (by decide)]

/-- **Affine `A₁⁽¹⁾` Weyl group**: isomorphic to the infinite dihedral group `DihedralGroup 0`. -/
noncomputable def dihedralGroupZeroEquivWeylAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 0 ≃*
      R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) :=
  R.dihedralGroupMulEquivWeyl (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))
    (fun k ↦ by fin_cases k <;> simp)
    R.orderOf_weylSimple_mul_weylSimple_eq_zero_affine_A_one

/-- `TauCeti.CartanRealization.dihedralGroupZeroEquivWeylAffineAOne` evaluates to
`TauCeti.dihedralHom`. -/
@[simp]
theorem dihedralGroupZeroEquivWeylAffineAOne_apply {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H)
    (x : DihedralGroup 0) :
    R.dihedralGroupZeroEquivWeylAffineAOne x =
      TauCeti.dihedralHom
        (R.weylSimple_mul_self (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0)
        (R.weylSimple_mul_self (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1)
        (R.orderOf_weylSimple_mul_weylSimple_eq_zero_affine_A_one ▸ pow_orderOf_eq_one _) x :=
  R.dihedralGroupMulEquivWeyl_apply _ _
    R.orderOf_weylSimple_mul_weylSimple_eq_zero_affine_A_one x

/-- The Weyl group of affine `A₁⁽¹⁾` is infinite. -/
instance instInfiniteWeylGroupAffineAOne {K H : Type*} [Field K] [CharZero K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    Infinite (R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))) :=
  Infinite.of_injective _ R.dihedralGroupZeroEquivWeylAffineAOne.injective

/-- **Affine `A₁⁽¹⁾` translation check**: `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)` (`= α₁ - 2δ` for the
null root `δ = α₀ + α₁`). -/
theorem weylSimple_mul_weylSimple_apply_root_affine_A_one {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((!![(2 : ℤ), -2; -2, 2]).map (Int.cast : ℤ → K)) H) :
    ((R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
        R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1 :
        R.weylGroup (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))) :
        Dual K H ≃ₗ[K] Dual K H) (R.root 1) =
      R.root 1 - (2 : K) • (R.root 0 + R.root 1) := by
  have hf0 : Dual.eval K H (R.coroot 0) (R.root 0) = 2 := by simp [R.root_coroot]
  have hf1 : Dual.eval K H (R.coroot 1) (R.root 1) = 2 := by simp [R.root_coroot]
  have h01 : Dual.eval K H (R.coroot 0) (R.root 1) = (-2 : K) := by simp [R.root_coroot]
  have h10 : Dual.eval K H (R.coroot 1) (R.root 0) = (-2 : K) := by simp [R.root_coroot]
  have hprod : Dual.eval K H (R.coroot 0) (R.root 1) *
      Dual.eval K H (R.coroot 1) (R.root 0) = 4 := by
    rw [h01, h10]
    norm_num
  have hstep := Module.reflection_reflection_iterate hf0 hf1 hprod 1
  simp only [Function.iterate_one, LinearEquiv.trans_apply, one_nsmul, h01] at hstep
  rw [Subgroup.coe_mul, mul_apply_eq_comp, coe_weylSimple, coe_weylSimple,
    R.simpleReflection_eq_reflection _ 0 hf0, R.simpleReflection_eq_reflection _ 1 hf1, hstep]
  module

end RankTwo

end TauCeti.CartanRealization

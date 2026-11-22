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

For a realization `R` of any rank-two matrix `A` with diagonal `2` on `{i, j}` over any field,
`R.weylGroup hdiag` is canonically isomorphic to
`DihedralGroup (orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j))`.

* **Order-four pairs and type `B₂`**: for any distinct `i ≠ j` with `A i j * A j i = 2` and
  `A i j ≠ 0 ∨ A j i ≠ 0`, `sᵢ * sⱼ` has order `4` over any field
  (`TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four`), specializing in type
  `B₂` to `TauCeti.CartanRealization.orderOf_weylSimple_mul_B_two` and `DihedralGroup 4 ≃* W(B₂)`
  of order `8`.
* **Generalized Cartan matrices in characteristic zero**: `orderOf (sᵢ * sⱼ)` equals
  `coxeterMatrixOfGeneralizedCartanMatrix A i j`
  (`TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple`), which specializes in affine type
  `A₁⁽¹⁾` to the infinite dihedral group `DihedralGroup 0`, with `s₀ s₁` of infinite order and
  `(s₀ s₁)(α₁) = α₁ - 2 • (α₀ + α₁)`.

## Main definitions

* `TauCeti.CartanRealization.dihedralGroupMulEquivWeyl`: isomorphism of a rank-two Weyl group with
  `DihedralGroup (orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j))` over any field.
* `TauCeti.CartanRealization.dihedralGroupFourEquivWeylBTwo`: isomorphism
  `DihedralGroup 4 ≃* W(B₂)` over any field.
* `TauCeti.CartanRealization.dihedralGroupZeroEquivWeylAffineAOne`: isomorphism
  `DihedralGroup 0 ≃* W(A₁⁽¹⁾)`.

## Main results

* `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple_eq_four`,
  `TauCeti.CartanRealization.orderOf_weylSimple_mul_B_two`, and
  `TauCeti.CartanRealization.card_weylGroup_B_two`: `orderOf (sᵢ * sⱼ) = 4` whenever `i ≠ j`,
  `A i j * A j i = 2`, and `A i j ≠ 0 ∨ A j i ≠ 0`, and `Nat.card (W(B₂)) = 8` over any field.
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
the Coxeter matrix entry `coxeterMatrixOfGeneralizedCartanMatrix A i j` over a characteristic-zero
field whenever `A i j = 0 ↔ A j i = 0` and `0 ≤ A i j * A j i`. -/
@[simp]
theorem orderOf_weylSimple_mul_weylSimple {I K H : Type*} [DecidableEq I] [Field K] [CharZero K]
    [AddCommGroup H] [Module K H] {A : Matrix I I ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H)
    (hdiag : ∀ i, A i i = 2) {i j : I} (hzero : A i j = 0 ↔ A j i = 0)
    (hprod : 0 ≤ A i j * A j i) :
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
  exact R.orderOf_simpleReflection_mul_simpleReflection (diag_map_intCast hdiag) hzero hprod

/-- **Rank-two Weyl groups are dihedral**: for a realization of any matrix `A` with diagonal `2`
on `{i, j}` over any field `K`, `R.weylGroup hdiag` is isomorphic to
`DihedralGroup (orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j))`. Over a
characteristic-zero field, `TauCeti.CartanRealization.orderOf_weylSimple_mul_weylSimple` computes
this order as `coxeterMatrixOfGeneralizedCartanMatrix A i j` when `A` is an integral matrix
satisfying `A i j = 0 ↔ A j i = 0` and `0 ≤ A i j * A j i`. -/
noncomputable def dihedralGroupMulEquivWeyl {I K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ k, A k k = 2)
    {i j : I} (hpair : ∀ k : I, k = i ∨ k = j) :
    DihedralGroup (orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j)) ≃*
      R.weylGroup hdiag := by
  have hrange : ({R.weylSimple hdiag i, R.weylSimple hdiag j} : Set _) =
      Set.range (R.weylSimple hdiag) := by
    ext w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    refine ⟨fun h ↦ h.elim (fun h ↦ ⟨i, h.symm⟩) (fun h ↦ ⟨j, h.symm⟩), fun ⟨k, hk⟩ ↦ ?_⟩
    rcases hpair k with rfl | rfl
    · exact Or.inl hk.symm
    · exact Or.inr hk.symm
  exact TauCeti.dihedralGroupMulEquiv (R.weylSimple_mul_self hdiag i)
    (R.weylSimple_mul_self hdiag j) (R.weylSimple_ne_one hdiag i) (R.weylSimple_ne_one hdiag j)
    rfl (by rw [hrange, R.closure_range_weylSimple])

/-- **Order-four pair in `R.weylGroup`**: over any field `K` (including characteristic `2`),
for distinct indices `i ≠ j` with `A i j * A j i = 2` and `A i j ≠ 0 ∨ A j i ≠ 0`, the product
`R.weylSimple hdiag i * R.weylSimple hdiag j` has order `4`. -/
theorem orderOf_weylSimple_mul_weylSimple_eq_four {I K H : Type*} [Field K]
    [AddCommGroup H] [Module K H] {A : Matrix I I K}
    (R : CartanRealization A H) (hdiag : ∀ k, A k k = 2) {i j : I} (hij : i ≠ j)
    (hprod : A i j * A j i = 2) (hne : A i j ≠ 0 ∨ A j i ≠ 0) :
    orderOf (R.weylSimple hdiag i * R.weylSimple hdiag j) = 4 := by
  let sᵢ := R.weylSimple hdiag i
  let sⱼ := R.weylSimple hdiag j
  have hpow4 : (sᵢ * sⱼ) ^ 4 = 1 := by
    apply Subtype.ext
    have hfi : Dual.eval K H (R.coroot i) (R.root i) = 2 := by simp [hdiag i]
    have hfj : Dual.eval K H (R.coroot j) (R.root j) = 2 := by simp [hdiag j]
    have heval : Dual.eval K H (R.coroot i) (R.root j) *
        Dual.eval K H (R.coroot j) (R.root i) = 2 := by
      simpa [R.root_coroot] using hprod
    simpa [sᵢ, sⱼ, R.simpleReflection_eq_reflection hdiag i hfi,
      R.simpleReflection_eq_reflection hdiag j hfj] using
      Module.reflection_mul_reflection_pow_four_eq_one hfi hfj heval
  refine orderOf_eq_of_pow_and_pow_div_prime hpow4 fun p hp hpd ↦ ?_
  obtain rfl : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow (n := 2) hpd)
  intro hpow2
  have hcomm : sᵢ * sⱼ = sⱼ * sᵢ := by
    calc sᵢ * sⱼ = sᵢ * (sᵢ * sⱼ) ^ 2 * sⱼ := by rw [hpow2, mul_one]
      _ = (sᵢ * sᵢ) * (sⱼ * sᵢ) * (sⱼ * sⱼ) := by simp [sq, mul_assoc]
      _ = sⱼ * sᵢ := by simp [sᵢ, sⱼ]
  have hpair (φ : Dual K H) : A i j * φ (R.coroot j) = 0 ∧ A j i * φ (R.coroot i) = 0 := by
    have hφ : ((sᵢ * sⱼ : R.weylGroup hdiag) : Dual K H ≃ₗ[K] Dual K H) φ =
        ((sⱼ * sᵢ : R.weylGroup hdiag) : Dual K H ≃ₗ[K] Dual K H) φ := by
      rw [hcomm]
    simp only [sᵢ, sⱼ, Subgroup.coe_mul, mul_apply_eq_comp, coe_weylSimple,
      simpleReflection_apply, map_sub, map_smul, R.root_coroot] at hφ
    have hlin : (A i j * φ (R.coroot j)) • R.root i + (-(A j i * φ (R.coroot i))) • R.root j =
        (0 : K) • R.root i + (0 : K) • R.root j := by
      have hsub := sub_eq_zero.mpr hφ
      simp only [zero_smul, add_zero]
      rw [← hsub]
      module
    have hc := (R.linearIndependent_root_pair hij).eq_of_pair hlin
    exact ⟨hc.1, neg_eq_zero.mp hc.2⟩
  rcases hne with hne_ij | hne_ji
  · exact R.coroot_linearIndependent.ne_zero j <| (Module.forall_dual_apply_eq_zero_iff K _).mp
      fun φ ↦ (mul_eq_zero.mp (hpair φ).1).resolve_left hne_ij
  · exact R.coroot_linearIndependent.ne_zero i <| (Module.forall_dual_apply_eq_zero_iff K _).mp
      fun φ ↦ (mul_eq_zero.mp (hpair φ).2).resolve_left hne_ji

/-- **Type `B₂` product-order check**: `s₀ * s₁` has order `4` over any field. -/
theorem orderOf_weylSimple_mul_B_two {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    orderOf (R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 0 *
        R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 1) = 4 :=
  R.orderOf_weylSimple_mul_weylSimple_eq_four (diag_map_intCast (CartanMatrix.B_diag 2))
    (by decide) (by simp [CartanMatrix.B_two]) (Or.inr (by simp [CartanMatrix.B_two]))

/-- **Type `B₂` Weyl group**: isomorphic to `DihedralGroup 4` over any field. -/
noncomputable def dihedralGroupFourEquivWeylBTwo {K H : Type*} [Field K]
    [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    DihedralGroup 4 ≃* R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2)) :=
  (by rw [R.orderOf_weylSimple_mul_B_two] :
      DihedralGroup 4 ≃*
        DihedralGroup (orderOf
          (R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 0 *
            R.weylSimple (diag_map_intCast (CartanMatrix.B_diag 2)) 1))).trans <|
    R.dihedralGroupMulEquivWeyl (diag_map_intCast (CartanMatrix.B_diag 2))
      (fun k ↦ by fin_cases k <;> simp)

/-- **Type `B₂` cardinality check**: `|W(B₂)| = 8` over any field. -/
theorem card_weylGroup_B_two {K H : Type*} [Field K] [AddCommGroup H] [Module K H]
    (R : CartanRealization ((CartanMatrix.B 2).map (Int.cast : ℤ → K)) H) :
    Nat.card (R.weylGroup (diag_map_intCast (CartanMatrix.B_diag 2))) = 8 := by
  rw [← Nat.card_congr (R.dihedralGroupFourEquivWeylBTwo).toEquiv, DihedralGroup.nat_card]

/-- **Affine `A₁⁽¹⁾` infinite-order check**: `s₀ s₁` has infinite order (`orderOf = 0`). -/
theorem orderOf_weylSimple_mul_affine_A_one {K H : Type*} [Field K] [CharZero K]
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
  (by rw [R.orderOf_weylSimple_mul_affine_A_one] :
      DihedralGroup 0 ≃*
        DihedralGroup (orderOf
          (R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 0 *
            R.weylSimple (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide)) 1))).trans <|
    R.dihedralGroupMulEquivWeyl
      (diag_map_intCast (A := !![(2 : ℤ), -2; -2, 2]) (by decide))
      (fun k ↦ by fin_cases k <;> simp)

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

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.CoprodI
public import TauCeti.GroupTheory.Index.TorsionFree
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
import TauCeti.GroupTheory.TriangleGroup.FreeProduct

/-!
# Free-product structure, torsion classes, and abelianization of `PSL(2, ℤ)`

Combining the geometric presentation `PSL(2, ℤ) ≃* TriangleGroup 3 2 0` with the free-product
splitting of `Δ(a, b, 0)` identifies the projective modular group with the free product
`ℤ/2ℤ ∗ ℤ/3ℤ`, both as a binary coproduct (`TauCeti.ModularGroup.coprodEquiv`) and as an indexed
coproduct over `Fin 2` (`TauCeti.ModularGroup.coprodIEquiv`). Under this isomorphism, the order-two
generator `S` corresponds to the canonical generator of `ℤ/2ℤ`, the order-three generator `R = S T`
corresponds to the canonical generator of `ℤ/3ℤ`, and the cusp translation `T = S R` corresponds to
their product in `ℤ/2ℤ ∗ ℤ/3ℤ`.

From this decomposition we derive the fundamental group-theoretic invariants of `PSL(2, ℤ)`:

* **Abelianization**: `Additive (Group.Abelianization PSL(2, ℤ)) ≃+ ZMod 6` sending the class of
  `T` to `1`, `U = S T⁻¹` to `2`, `S` to `3`, and `R = S T` to `4`; hence the commutator subgroup
  of `PSL(2, ℤ)` has index `6`.
* **Conjugacy of order-three generators**: `R` and `R²` (and likewise `U` and `U²`, as well as `R`
  and `U`) lie in distinct conjugacy classes of `PSL(2, ℤ)`, detected by their images `4` and `2`
  in `ZMod 6`, whereas `U` is conjugate to `R²` and `R` is conjugate to `U²`.
* **Torsion classification**: every finite-order element of `PSL(2, ℤ)` has order `1`, `2`, or `3`;
  elements of order `2` form the single conjugacy class of `S`, and elements of order `3` split into
  the two conjugacy classes of `R` and `R²` (equivalently `U²` and `U`).
* **Index divisibility and sharpness**: every torsion-free subgroup of `PSL(2, ℤ)` has index
  divisible by `6`, and the commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` is itself torsion-free of
  index `6`.

## Main definitions

* `TauCeti.ModularGroup.coprodEquiv`: the isomorphism
  `PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3)`.
* `TauCeti.ModularGroup.coprodIEquiv`: the indexed-coproduct isomorphism
  `PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))`.
* `TauCeti.ModularGroup.abelianizationAddEquiv`, `TauCeti.ModularGroup.abelianizationMulEquiv`:
  the abelianization of `PSL(2, ℤ)` as `ZMod 6`.

## Main results

* `TauCeti.ModularGroup.natCard_abelianization`, `TauCeti.ModularGroup.index_commutator`,
  `TauCeti.ModularGroup.instIsMulTorsionFreeCommutator`: `Nat.card (Group.Abelianization PSL(2, ℤ))`
  and `(commutator PSL(2, ℤ)).index` equal `6`, and `commutator PSL(2, ℤ)` is torsion-free.
* `TauCeti.ModularGroup.not_isConj_coe_R_sq`, `TauCeti.ModularGroup.not_isConj_coe_U_sq`,
  `TauCeti.ModularGroup.not_isConj_coe_R_coe_U`: non-conjugacy among order-three representatives.
* `TauCeti.ModularGroup.isOfFinOrder_iff_isConj_coe_R`,
  `TauCeti.ModularGroup.isOfFinOrder_iff_isConj_coe_U`,
  `TauCeti.ModularGroup.orderOf_eq_two_iff`,
  `TauCeti.ModularGroup.orderOf_eq_three_iff_isConj_coe_R`,
  `TauCeti.ModularGroup.orderOf_eq_three_iff_isConj_coe_U`,
  `TauCeti.ModularGroup.orderOf_mem_of_isOfFinOrder`: complete torsion and order classification.
* `TauCeti.ModularGroup.six_dvd_index_of_isMulTorsionFree`,
  `TauCeti.ModularGroup.six_dvd_index_of_torsionFree`: `6` divides the index of any torsion-free
  subgroup of `PSL(2, ℤ)`.

## References

* J.-P. Serre, *Trees*, Springer Monographs in Mathematics, 1980, Chapter I, §4.2.
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1.
* J.-P. Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  Chapter VII, §1.
-/

public section

noncomputable section

open scoped MatrixGroups Monoid.Coprod

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-! ### Auxiliary projective generator identities -/

private theorem coe_R_eq_coe_S_mul_coe_T : (R : PSL(2, ℤ)) = (S : PSL(2, ℤ)) * T := by
  rw [R_def, QuotientGroup.mk_mul]

private theorem coe_U_eq_coe_S_mul_coe_T_inv :
    (U : PSL(2, ℤ)) = (S : PSL(2, ℤ)) * (T : PSL(2, ℤ))⁻¹ := by
  rw [U_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

private theorem coe_S_mul_coe_R : (S : PSL(2, ℤ)) * (R : PSL(2, ℤ)) = T := by
  rw [coe_R_eq_coe_S_mul_coe_T, ← mul_assoc, ← sq, coe_S_sq, one_mul]

/-- In `PSL(2, ℤ)`, the inverse of the order-three generator `R = S T` is `R²`. -/
theorem coe_R_inv : (R : PSL(2, ℤ))⁻¹ = (R : PSL(2, ℤ)) ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', coe_R_pow_three])

/-- In `PSL(2, ℤ)`, the inverse of the order-three generator `U = S T⁻¹` is `U²`. -/
theorem coe_U_inv : (U : PSL(2, ℤ))⁻¹ = (U : PSL(2, ℤ)) ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', coe_U_pow_three])

private theorem triangleGroupEquiv_symm_coe_R :
    triangleGroupEquiv.symm (R : PSL(2, ℤ)) = TriangleGroup.x 3 2 0 := by
  apply triangleGroupEquiv.injective
  simp [coe_R_eq_coe_S_mul_coe_T]

private theorem triangleGroupEquiv_symm_coe_S :
    triangleGroupEquiv.symm (S : PSL(2, ℤ)) = TriangleGroup.y 3 2 0 := by
  apply triangleGroupEquiv.injective
  simp

private theorem triangleGroupEquiv_symm_coe_T :
    triangleGroupEquiv.symm (T : PSL(2, ℤ)) = (TriangleGroup.z 3 2 0)⁻¹ := by
  apply triangleGroupEquiv.injective
  simp

/-! ### Free-product presentation `PSL(2, ℤ) ≃* ℤ/2ℤ ∗ ℤ/3ℤ` -/

/-- **Free-product decomposition of the modular group.** `PSL(2, ℤ)` is isomorphic to the free
product `Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3)`, sending `S` to `inl (ofAdd 1)`,
`R = S T` to `inr (ofAdd 1)`, and `T = S R` to `inl (ofAdd 1) * inr (ofAdd 1)`. -/
def coprodEquiv : PSL(2, ℤ) ≃* Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3) :=
  (triangleGroupEquiv.symm.trans (TriangleGroup.equivCoprod 3 2)).trans
    (MulEquiv.coprodComm (Multiplicative (ZMod 3)) (Multiplicative (ZMod 2)))

@[simp]
theorem coprodEquiv_coe_S : coprodEquiv (S : PSL(2, ℤ)) = Monoid.Coprod.inl (.ofAdd 1) := by
  simp [coprodEquiv, triangleGroupEquiv_symm_coe_S]

@[simp]
theorem coprodEquiv_coe_R : coprodEquiv (R : PSL(2, ℤ)) = Monoid.Coprod.inr (.ofAdd 1) := by
  simp [coprodEquiv, triangleGroupEquiv_symm_coe_R]

@[simp]
theorem coprodEquiv_coe_T :
    coprodEquiv (T : PSL(2, ℤ)) = Monoid.Coprod.inl (.ofAdd 1) * Monoid.Coprod.inr (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R, map_mul, coprodEquiv_coe_S, coprodEquiv_coe_R]

@[simp]
theorem coprodEquiv_coe_U :
    coprodEquiv (U : PSL(2, ℤ)) =
      Monoid.Coprod.inl (.ofAdd 1) * (Monoid.Coprod.inr (.ofAdd 1))⁻¹ *
        Monoid.Coprod.inl (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv, coe_S_inv, map_mul, map_mul, map_inv,
    coprodEquiv_coe_S, coprodEquiv_coe_R]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_intCast (k : ℤ) :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_intCast (k : ℤ) :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_natCast (k : ℕ) :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_natCast (k : ℕ) :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

@[simp]
theorem coprodEquiv_symm_inl_ofAdd_one :
    coprodEquiv.symm (Monoid.Coprod.inl (.ofAdd 1)) = (S : PSL(2, ℤ)) := by
  simp [coprodEquiv]

@[simp]
theorem coprodEquiv_symm_inr_ofAdd_one :
    coprodEquiv.symm (Monoid.Coprod.inr (.ofAdd 1)) = (R : PSL(2, ℤ)) := by
  simp [coprodEquiv, coe_R_eq_coe_S_mul_coe_T]

/-- **Indexed free-product decomposition of the modular group.** `PSL(2, ℤ)` is isomorphic to the
indexed coproduct `Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))` over
`Fin 2`. -/
def coprodIEquiv :
    PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)) :=
  coprodEquiv.trans
    (Monoid.CoprodI.finTwoEquivCoprod fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm

@[simp]
theorem coprodIEquiv_coe_S :
    coprodIEquiv (S : PSL(2, ℤ)) =
      Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 0)
        ((Multiplicative.ofAdd (α := ZMod 2)) 1) := by
  change (Monoid.CoprodI.finTwoEquivCoprod
      fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm (coprodEquiv (S : PSL(2, ℤ))) = _
  rw [coprodEquiv_coe_S]
  exact Monoid.CoprodI.finTwoEquivCoprod_symm_inl
    (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)))
    ((Multiplicative.ofAdd (α := ZMod 2)) 1)

@[simp]
theorem coprodIEquiv_coe_R :
    coprodIEquiv (R : PSL(2, ℤ)) =
      Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 1)
        ((Multiplicative.ofAdd (α := ZMod 3)) 1) := by
  change (Monoid.CoprodI.finTwoEquivCoprod
      fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))).symm (coprodEquiv (R : PSL(2, ℤ))) = _
  rw [coprodEquiv_coe_R]
  exact Monoid.CoprodI.finTwoEquivCoprod_symm_inr
    (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i)))
    ((Multiplicative.ofAdd (α := ZMod 3)) 1)

/-- `coprodIEquiv.symm` sends the generator of the `i = 0` factor `ZMod 2` to `S`.

Not `@[simp]`: `Matrix.cons_val_zero` reduces `![2, 3] 0` inside the `DFunLike.coe` domain of
`Monoid.CoprodI.of`. -/
theorem coprodIEquiv_symm_of_zero_ofAdd_one :
    coprodIEquiv.symm
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 0)
          ((Multiplicative.ofAdd (α := ZMod 2)) 1)) = (S : PSL(2, ℤ)) :=
  coprodIEquiv.symm_apply_eq.mpr coprodIEquiv_coe_S.symm

/-- `coprodIEquiv.symm` sends the generator of the `i = 1` factor `ZMod 3` to `R`.

Not `@[simp]`: `Matrix.cons_val_one` reduces `![2, 3] 1` inside the `DFunLike.coe` domain of
`Monoid.CoprodI.of`. -/
theorem coprodIEquiv_symm_of_one_ofAdd_one :
    coprodIEquiv.symm
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (![2, 3] i))) (i := 1)
          ((Multiplicative.ofAdd (α := ZMod 3)) 1)) = (R : PSL(2, ℤ)) :=
  coprodIEquiv.symm_apply_eq.mpr coprodIEquiv_coe_R.symm

/-! ### Abelianization of `PSL(2, ℤ)` and index of the commutator subgroup -/

/-- **Additive abelianization of `PSL(2, ℤ)`.** The abelianization of the modular group is cyclic of
order `6`, canonically normalized so that the cusp translation `T` maps to `1 : ZMod 6` (and hence
`U = S T⁻¹ ↦ 2`, `S ↦ 3`, and `R = S T ↦ 4`). -/
def abelianizationAddEquiv : Additive (Group.Abelianization PSL(2, ℤ)) ≃+ ZMod 6 :=
  (triangleGroupEquiv.symm.abelianizationCongr.toAdditive.trans
    (TriangleGroup.abelianizationAddEquivProd 3 2)).trans
    (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)).symm.toAddEquiv

@[simp]
theorem abelianizationAddEquiv_ofMul_of_coe_R :
    abelianizationAddEquiv (.ofMul (Group.Abelianization.of (R : PSL(2, ℤ)))) = 4 := by
  simp only [abelianizationAddEquiv, AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, Group.abelianizationCongr_of, triangleGroupEquiv_symm_coe_R,
    TriangleGroup.abelianizationAddEquivProd_ofMul_of_x]
  exact (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)).symm_apply_eq.mpr (by decide)

@[simp]
theorem abelianizationAddEquiv_ofMul_of_coe_S :
    abelianizationAddEquiv (.ofMul (Group.Abelianization.of (S : PSL(2, ℤ)))) = 3 := by
  simp only [abelianizationAddEquiv, AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    toMul_ofMul, Group.abelianizationCongr_of, triangleGroupEquiv_symm_coe_S,
    TriangleGroup.abelianizationAddEquivProd_ofMul_of_y]
  exact (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)).symm_apply_eq.mpr (by decide)

@[simp]
theorem abelianizationAddEquiv_ofMul_of_coe_T :
    abelianizationAddEquiv (.ofMul (Group.Abelianization.of (T : PSL(2, ℤ)))) = 1 := by
  rw [← coe_S_mul_coe_R, map_mul, ofMul_mul, map_add, abelianizationAddEquiv_ofMul_of_coe_S,
    abelianizationAddEquiv_ofMul_of_coe_R]
  decide

@[simp]
theorem abelianizationAddEquiv_ofMul_of_coe_U :
    abelianizationAddEquiv (.ofMul (Group.Abelianization.of (U : PSL(2, ℤ)))) = 2 := by
  rw [coe_U_eq_coe_S_mul_coe_T_inv, map_mul, map_inv, ofMul_mul, ofMul_inv, map_add, map_neg,
    abelianizationAddEquiv_ofMul_of_coe_S, abelianizationAddEquiv_ofMul_of_coe_T]
  decide

@[simp]
theorem abelianizationAddEquiv_symm_one :
    abelianizationAddEquiv.symm 1 = .ofMul (Group.Abelianization.of (T : PSL(2, ℤ))) :=
  abelianizationAddEquiv.symm_apply_eq.mpr abelianizationAddEquiv_ofMul_of_coe_T.symm

@[simp]
theorem abelianizationAddEquiv_symm_intCast (k : ℤ) :
    abelianizationAddEquiv.symm (k : ZMod 6) =
      .ofMul (Group.Abelianization.of ((T : PSL(2, ℤ)) ^ k)) := by
  rw [← zsmul_one k, map_zsmul, abelianizationAddEquiv_symm_one, map_zpow, ofMul_zpow]

/-- **Multiplicative abelianization of `PSL(2, ℤ)`.** `Group.Abelianization PSL(2, ℤ)` is isomorphic
to `Multiplicative (ZMod 6)`. -/
def abelianizationMulEquiv : Group.Abelianization PSL(2, ℤ) ≃* Multiplicative (ZMod 6) :=
  abelianizationAddEquiv.toMultiplicativeRight

@[simp]
theorem abelianizationMulEquiv_of_coe_T :
    abelianizationMulEquiv (Group.Abelianization.of (T : PSL(2, ℤ))) = .ofAdd 1 := by
  simp [abelianizationMulEquiv]

@[simp]
theorem abelianizationMulEquiv_of_coe_U :
    abelianizationMulEquiv (Group.Abelianization.of (U : PSL(2, ℤ))) = .ofAdd 2 := by
  simp [abelianizationMulEquiv]

@[simp]
theorem abelianizationMulEquiv_of_coe_S :
    abelianizationMulEquiv (Group.Abelianization.of (S : PSL(2, ℤ))) = .ofAdd 3 := by
  simp [abelianizationMulEquiv]

@[simp]
theorem abelianizationMulEquiv_of_coe_R :
    abelianizationMulEquiv (Group.Abelianization.of (R : PSL(2, ℤ))) = .ofAdd 4 := by
  simp [abelianizationMulEquiv]

/-- The abelianization of `PSL(2, ℤ)` has order `6`. -/
@[simp]
theorem natCard_abelianization : Nat.card (Group.Abelianization PSL(2, ℤ)) = 6 := by
  rw [Nat.card_congr abelianizationMulEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

/-- The commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` has index `6` in `PSL(2, ℤ)`. -/
@[simp]
theorem index_commutator : (commutator PSL(2, ℤ)).index = 6 :=
  natCard_abelianization

/-! ### Conjugacy of order-three generators and torsion classification -/

/-- In `PSL(2, ℤ)`, `U = S T⁻¹` is conjugate to `R² = (S T)⁻¹` (namely by `S`). -/
theorem isConj_coe_U_coe_R_sq : IsConj (U : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := by
  rw [← coe_R_inv]
  exact (isConj_iff.mpr ⟨(S : PSL(2, ℤ)), coe_S_mul_coe_R_inv_mul_coe_S_inv⟩).symm

/-- In `PSL(2, ℤ)`, `R = S T` is conjugate to `U² = (S T⁻¹)⁻¹` (namely by `S`). -/
theorem isConj_coe_R_coe_U_sq : IsConj (R : PSL(2, ℤ)) ((U : PSL(2, ℤ)) ^ 2) := by
  rw [← coe_U_inv]
  refine isConj_iff.mpr ⟨(S : PSL(2, ℤ)), ?_⟩
  rw [coe_U_eq_coe_S_mul_coe_T_inv, mul_inv_rev, inv_inv, coe_S_inv, coe_R_eq_coe_S_mul_coe_T,
    ← mul_assoc, ← sq, coe_S_sq, one_mul]

/-- In `PSL(2, ℤ)`, `R` is not conjugate to `R²`, since their images in `ZMod 6` are `4` and `2`. -/
theorem not_isConj_coe_R_sq : ¬ IsConj (R : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := by
  intro h
  have hab : Group.Abelianization.of (R : PSL(2, ℤ)) =
      Group.Abelianization.of ((R : PSL(2, ℤ)) ^ 2) :=
    isConj_iff_eq.mp (Group.Abelianization.of.map_isConj h)
  have hval := congrArg (fun z ↦ abelianizationAddEquiv (.ofMul z)) hab
  simp only [map_pow, ofMul_pow, map_nsmul, abelianizationAddEquiv_ofMul_of_coe_R] at hval
  revert hval
  decide

/-- In `PSL(2, ℤ)`, `U` is not conjugate to `U²`, since their images in `ZMod 6` are `2` and `4`. -/
theorem not_isConj_coe_U_sq : ¬ IsConj (U : PSL(2, ℤ)) ((U : PSL(2, ℤ)) ^ 2) := by
  intro h
  have hab : Group.Abelianization.of (U : PSL(2, ℤ)) =
      Group.Abelianization.of ((U : PSL(2, ℤ)) ^ 2) :=
    isConj_iff_eq.mp (Group.Abelianization.of.map_isConj h)
  have hval := congrArg (fun z ↦ abelianizationAddEquiv (.ofMul z)) hab
  simp only [map_pow, ofMul_pow, map_nsmul, abelianizationAddEquiv_ofMul_of_coe_U] at hval
  revert hval
  decide

/-- In `PSL(2, ℤ)`, `R = S T` and `U = S T⁻¹` are not conjugate, since their images in `ZMod 6` are
`4` and `2`. -/
theorem not_isConj_coe_R_coe_U : ¬ IsConj (R : PSL(2, ℤ)) (U : PSL(2, ℤ)) := by
  intro h
  have hab : Group.Abelianization.of (R : PSL(2, ℤ)) = Group.Abelianization.of (U : PSL(2, ℤ)) :=
    isConj_iff_eq.mp (Group.Abelianization.of.map_isConj h)
  have hval := congrArg (fun z ↦ abelianizationAddEquiv (.ofMul z)) hab
  rw [abelianizationAddEquiv_ofMul_of_coe_R, abelianizationAddEquiv_ofMul_of_coe_U] at hval
  revert hval
  decide

/-- **Torsion classification in `PSL(2, ℤ)` (in terms of `S` and `R`).** An element of `PSL(2, ℤ)`
has finite order if and only if it is `1` or conjugate to `S`, `R`, or `R²`. -/
theorem isOfFinOrder_iff_isConj_coe_R {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔
      g = 1 ∨ IsConj g (S : PSL(2, ℤ)) ∨ IsConj g (R : PSL(2, ℤ)) ∨
        IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  rw [← triangleGroupEquiv.symm.injective.isOfFinOrder_iff
      (f := triangleGroupEquiv.symm.toMonoidHom),
    MulEquiv.coe_toMonoidHom, TriangleGroup.isOfFinOrder_iff_of_neZero]
  refine ⟨?_, ?_⟩
  · rintro (⟨k, hk, hconj⟩ | ⟨k, hk, hconj⟩)
    · have hc := triangleGroupEquiv.toMonoidHom.map_isConj hconj
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_pow,
        triangleGroupEquiv_x, ← coe_R_eq_coe_S_mul_coe_T] at hc
      interval_cases k
      · exact Or.inl (by simpa using hc)
      · rw [pow_one] at hc; exact Or.inr (Or.inr (Or.inl hc))
      · exact Or.inr (Or.inr (Or.inr hc))
    · have hc := triangleGroupEquiv.toMonoidHom.map_isConj hconj
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_pow,
        triangleGroupEquiv_y] at hc
      interval_cases k
      · exact Or.inl (by simpa using hc)
      · rw [pow_one] at hc; exact Or.inr (Or.inl hc)
  · rintro (rfl | hc | hc | hc)
    · exact Or.inl ⟨0, by omega, by simp⟩
    · refine Or.inr ⟨1, by omega, ?_⟩
      have h1 := triangleGroupEquiv.symm.toMonoidHom.map_isConj hc
      rwa [MulEquiv.coe_toMonoidHom, triangleGroupEquiv_symm_coe_S,
        ← pow_one (TriangleGroup.y 3 2 0)] at h1
    · refine Or.inl ⟨1, by omega, ?_⟩
      have h1 := triangleGroupEquiv.symm.toMonoidHom.map_isConj hc
      rwa [MulEquiv.coe_toMonoidHom, triangleGroupEquiv_symm_coe_R,
        ← pow_one (TriangleGroup.x 3 2 0)] at h1
    · refine Or.inl ⟨2, by omega, ?_⟩
      have h1 := triangleGroupEquiv.symm.toMonoidHom.map_isConj hc
      rwa [MulEquiv.coe_toMonoidHom, map_pow, triangleGroupEquiv_symm_coe_R] at h1

/-- **Torsion classification in `PSL(2, ℤ)` (in terms of `S` and `U`).** An element of `PSL(2, ℤ)`
has finite order if and only if it is `1` or conjugate to `S`, `U`, or `U²`. -/
theorem isOfFinOrder_iff_isConj_coe_U {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔
      g = 1 ∨ IsConj g (S : PSL(2, ℤ)) ∨ IsConj g (U : PSL(2, ℤ)) ∨
        IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [isOfFinOrder_iff_isConj_coe_R]
  refine ⟨?_, ?_⟩
  · rintro (rfl | hc | hc | hc)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inr (hc.trans isConj_coe_R_coe_U_sq)))
    · exact Or.inr (Or.inr (Or.inl (hc.trans isConj_coe_U_coe_R_sq.symm)))
  · rintro (rfl | hc | hc | hc)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr (Or.inr (hc.trans isConj_coe_U_coe_R_sq)))
    · exact Or.inr (Or.inr (Or.inl (hc.trans isConj_coe_R_coe_U_sq.symm)))

/-- An element of `PSL(2, ℤ)` has order `2` if and only if it is conjugate to `S`. -/
theorem orderOf_eq_two_iff {g : PSL(2, ℤ)} :
    orderOf g = 2 ↔ IsConj g (S : PSL(2, ℤ)) := by
  refine ⟨fun hg ↦ ?_, fun ⟨_, hc⟩ ↦ by rw [hc.orderOf_eq, orderOf_coe_S]⟩
  have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
  rcases isOfFinOrder_iff_isConj_coe_R.mp hfin with rfl | hc | ⟨_, hc⟩ | ⟨_, hc⟩
  · simp at hg
  · exact hc
  · rw [hc.orderOf_eq, orderOf_coe_R] at hg; omega
  · rw [hc.orderOf_eq, ← coe_R_inv, orderOf_inv, orderOf_coe_R] at hg; omega

/-- An element of `PSL(2, ℤ)` has order `3` if and only if it is conjugate to `R` or `R²`. -/
theorem orderOf_eq_three_iff_isConj_coe_R {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (R : PSL(2, ℤ)) ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff_isConj_coe_R.mp hfin with rfl | ⟨_, hc⟩ | hc | hc
    · simp at hg
    · rw [hc.orderOf_eq, orderOf_coe_S] at hg; omega
    · exact Or.inl hc
    · exact Or.inr hc
  · rintro (⟨_, hc⟩ | ⟨_, hc⟩)
    · rw [hc.orderOf_eq, orderOf_coe_R]
    · rw [hc.orderOf_eq, ← coe_R_inv, orderOf_inv, orderOf_coe_R]

/-- An element of `PSL(2, ℤ)` has order `3` if and only if it is conjugate to `U` or `U²`. -/
theorem orderOf_eq_three_iff_isConj_coe_U {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (U : PSL(2, ℤ)) ∨ IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [orderOf_eq_three_iff_isConj_coe_R]
  exact ⟨fun h ↦ h.elim (fun hc ↦ Or.inr (hc.trans isConj_coe_R_coe_U_sq))
      (fun hc ↦ Or.inl (hc.trans isConj_coe_U_coe_R_sq.symm)),
    fun h ↦ h.elim (fun hc ↦ Or.inr (hc.trans isConj_coe_U_coe_R_sq))
      (fun hc ↦ Or.inl (hc.trans isConj_coe_R_coe_U_sq.symm))⟩

/-- Every finite-order element of `PSL(2, ℤ)` has order `1`, `2`, or `3`. -/
theorem orderOf_mem_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) :
    orderOf g ∈ ({1, 2, 3} : Set ℕ) := by
  rcases isOfFinOrder_iff_isConj_coe_R.mp hg with rfl | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩
  · simp
  · simp [hc.orderOf_eq]
  · simp [hc.orderOf_eq]
  · simp [hc.orderOf_eq, ← coe_R_inv]

/-- Every nonidentity finite-order element of `PSL(2, ℤ)` has nontrivial image in the
abelianization (`3`, `4`, or `2` in `ZMod 6`). -/
theorem abelianization_of_ne_one_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g)
    (hne : g ≠ 1) : Group.Abelianization.of g ≠ 1 := by
  intro hab
  have hzero : abelianizationAddEquiv (.ofMul (Group.Abelianization.of g)) = 0 := by simp [hab]
  rcases isOfFinOrder_iff_isConj_coe_R.mp hg with rfl | hc | hc | hc
  · exact hne rfl
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    rw [heq, abelianizationAddEquiv_ofMul_of_coe_S] at hzero
    revert hzero; decide
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    rw [heq, abelianizationAddEquiv_ofMul_of_coe_R] at hzero
    revert hzero; decide
  · have heq := isConj_iff_eq.mp (Group.Abelianization.of.map_isConj hc)
    simp only [heq, map_pow, ofMul_pow, map_nsmul, abelianizationAddEquiv_ofMul_of_coe_R] at hzero
    revert hzero; decide

/-! ### Index divisibility for torsion-free subgroups and the commutator subgroup -/

/-- **The commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` is torsion-free.** Together with
`index_commutator`, this shows the divisibility bound `6 ∣ Γ'.index` below is sharp. -/
instance instIsMulTorsionFreeCommutator : IsMulTorsionFree (commutator PSL(2, ℤ)) :=
  IsMulTorsionFree.of_not_isOfFinOrder fun ⟨g, hg⟩ hne hfin ↦ by
    have hne' : g ≠ 1 := fun h1 ↦ hne (Subtype.ext h1)
    have hker : Group.Abelianization.of g = 1 :=
      MonoidHom.mem_ker.mp ((Group.Abelianization.ker_of PSL(2, ℤ)).symm ▸ hg)
    exact abelianization_of_ne_one_of_isOfFinOrder
      ((commutator PSL(2, ℤ)).subtype.isOfFinOrder hfin) hne' hker

/-- Every torsion-free subgroup `Γ' ≤ PSL(2, ℤ)` has index divisible by `6`. -/
theorem six_dvd_index_of_isMulTorsionFree (Γ' : Subgroup PSL(2, ℤ)) [IsMulTorsionFree Γ'] :
    6 ∣ Γ'.index := by
  have hS : IsOfFinOrder (S : PSL(2, ℤ)) := orderOf_pos_iff.mp (by simp)
  have hR : IsOfFinOrder (R : PSL(2, ℤ)) := orderOf_pos_iff.mp (by simp)
  have h2 : 2 ∣ Γ'.index := by
    simpa [orderOf_coe_S] using Γ'.orderOf_dvd_index_of_isMulTorsionFree hS
  have h3 : 3 ∣ Γ'.index := by
    simpa [orderOf_coe_R] using Γ'.orderOf_dvd_index_of_isMulTorsionFree hR
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide : Nat.Coprime 2 3) h2 h3

/-- Predicate-form version of `six_dvd_index_of_isMulTorsionFree`: if `Γ' ≤ PSL(2, ℤ)` contains no
nontrivial finite-order elements, then `6 ∣ Γ'.index`. -/
theorem six_dvd_index_of_torsionFree {Γ' : Subgroup PSL(2, ℤ)}
    (h : ∀ g ∈ Γ', IsOfFinOrder g → g = 1) : 6 ∣ Γ'.index := by
  have : IsMulTorsionFree Γ' := IsMulTorsionFree.of_not_isOfFinOrder fun ⟨g, hg⟩ hne hfin ↦
    hne (Subtype.ext (h g hg (Γ'.subtype.isOfFinOrder hfin)))
  exact six_dvd_index_of_isMulTorsionFree Γ'

end TauCeti.ModularGroup

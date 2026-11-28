/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.CoprodI
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Algebra.Group.Submonoid.Torsion
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Triangle.Group
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.GroupTheory.Index.Torsion
import TauCeti.GroupTheory.TriangleGroup.FreeProduct

/-!
# Free-product decomposition and subgroup index divisibility for `PSL(2, ℤ)`

Combining Poincaré's triangle presentation `PSL(2, ℤ) ≃* Δ(3, 2, ∞)`
(`TauCeti.ModularGroup.triangleGroupEquiv`) with the free-product decomposition of `Δ(a, b, 0)`
(`TauCeti.TriangleGroup.equivCoprod`) identifies the projective modular group with the free product
`ℤ/2ℤ ∗ ℤ/3ℤ`, both in binary form (`Monoid.Coprod`) and in indexed form (`Monoid.CoprodI` over
`Fin 2`), sending the involution `S` to the generator of `ℤ/2ℤ` and `R = S * T` to the generator of
`ℤ/3ℤ`.

Applying the general coset-action divisibility theorem
(`Subgroup.orderOf_dvd_index_of_forall_isOfFinOrder_eq_one`) to the torsion elements `S` of order
`2` and `R` of order `3` yields `6 ∣ Γ.index` for every torsion-free subgroup `Γ ≤ PSL(2, ℤ)`
(including infinite index, encoded by `0`).

## Main declarations

* `TauCeti.ModularGroup.psl2zEquivCoprod`:
  `PSL(2, ℤ) ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 3))`.
* `TauCeti.ModularGroup.psl2zEquivCoprodI`,
  `TauCeti.ModularGroup.finTwoEquivCoprod_psl2zEquivCoprodI`:
  `PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))`, and
  its comparison with `psl2zEquivCoprod`.
* `Subgroup.six_dvd_index_of_forall_isOfFinOrder_eq_one_psl2z`,
  `Subgroup.six_dvd_index_of_isMulTorsionFree_psl2z`: `6 ∣ Γ.index` for torsion-free `Γ`.

## References

* Jean-Pierre Serre, *A Course in Arithmetic*, Graduate Texts in Mathematics 7, Springer, 1973,
  Chapter VII, §1.
* Jean-Pierre Serre, *Trees*, Springer Monographs in Mathematics, Springer, 2003, §I.4.2, §I.5.3.
* Roger C. Lyndon and Paul E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1.
-/

public section

noncomputable section

open Matrix
open scoped MatrixGroups

namespace TauCeti.ModularGroup

open _root_.ModularGroup

/-! ### Free-product decompositions of `PSL(2, ℤ)` -/

/-- **Free-product decomposition of `PSL(2, ℤ)`.** The projective modular group is isomorphic to
the free product `Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3)`, sending `S` to
`inl (ofAdd 1)` and `R = S * T` to `inr (ofAdd 1)`. -/
def psl2zEquivCoprod :
    PSL(2, ℤ) ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 3)) :=
  triangleGroupEquiv.symm.trans
    ((TriangleGroup.equivCoprod 3 2).trans (MulEquiv.coprodComm _ _))

/-- `psl2zEquivCoprod` maps `S` to the generator `inl (ofAdd 1)` of `ℤ/2ℤ`. -/
@[simp]
theorem psl2zEquivCoprod_coe_S :
    psl2zEquivCoprod (S : PSL(2, ℤ)) = .inl (.ofAdd 1) := by
  simp [psl2zEquivCoprod, MulEquiv.trans_apply, triangleGroupEquiv_symm_coe_S]

/-- `psl2zEquivCoprod` maps `R = S * T` to the generator `inr (ofAdd 1)` of `ℤ/3ℤ`. -/
@[simp]
theorem psl2zEquivCoprod_coe_R :
    psl2zEquivCoprod (R : PSL(2, ℤ)) = .inr (.ofAdd 1) := by
  simp [psl2zEquivCoprod, MulEquiv.trans_apply, triangleGroupEquiv_symm_coe_R]

/-- `psl2zEquivCoprod` maps the cusp translation `T` to `inl (ofAdd 1) * inr (ofAdd 1)`. -/
@[simp]
theorem psl2zEquivCoprod_coe_T :
    psl2zEquivCoprod (T : PSL(2, ℤ)) = .inl (.ofAdd 1) * .inr (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R]
  simp [-coe_S_mul_coe_R]

/-- `psl2zEquivCoprod` maps `U = S * T⁻¹` to `inl (ofAdd 1) * inr (ofAdd (-1)) * inl (ofAdd 1)`. -/
@[simp]
theorem psl2zEquivCoprod_coe_U :
    psl2zEquivCoprod (U : PSL(2, ℤ)) =
      .inl (.ofAdd 1) * .inr (.ofAdd (-1)) * .inl (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv]
  simp

/-- The inverse of `psl2zEquivCoprod` sends `inl (ofAdd 1)` to `S`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inl_ofAdd_one :
    psl2zEquivCoprod.symm (.inl (.ofAdd 1)) = (S : PSL(2, ℤ)) :=
  psl2zEquivCoprod.symm_apply_eq.mpr psl2zEquivCoprod_coe_S.symm

/-- The inverse of `psl2zEquivCoprod` sends `inr (ofAdd 1)` to `R`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inr_ofAdd_one :
    psl2zEquivCoprod.symm (.inr (.ofAdd 1)) = (R : PSL(2, ℤ)) :=
  psl2zEquivCoprod.symm_apply_eq.mpr psl2zEquivCoprod_coe_R.symm

/-- The inverse of `psl2zEquivCoprod` sends `inl (ofAdd k)` to `S ^ k`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inl_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprod.symm (.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  rw [Multiplicative.ofAdd_intCast, map_zpow, map_zpow, psl2zEquivCoprod_symm_inl_ofAdd_one]

/-- The inverse of `psl2zEquivCoprod` sends `inr (ofAdd k)` to `R ^ k`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inr_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprod.symm (.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  rw [Multiplicative.ofAdd_intCast, map_zpow, map_zpow, psl2zEquivCoprod_symm_inr_ofAdd_one]

/-- The orders `2` and `3` of the cyclic free-product factors of `PSL(2, ℤ)` indexed by `Fin 2`. -/
@[expose]
def psl2zCoprodOrder : Fin 2 → ℕ
  | 0 => 2
  | 1 => 3

/-- **Indexed free-product decomposition of `PSL(2, ℤ)`.** Identifies `PSL(2, ℤ)` with the indexed
coproduct `Monoid.CoprodI` of `Multiplicative (ZMod 2)` and `Multiplicative (ZMod 3)` over
`Fin 2`. -/
def psl2zEquivCoprodI :
    PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i)) :=
  psl2zEquivCoprod.trans
    (Monoid.CoprodI.finTwoEquivCoprod
      fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm

/-- Applying `Monoid.CoprodI.finTwoEquivCoprod` to `psl2zEquivCoprodI g` yields
`psl2zEquivCoprod g`. -/
@[simp]
theorem finTwoEquivCoprod_psl2zEquivCoprodI (g : PSL(2, ℤ)) :
    Monoid.CoprodI.finTwoEquivCoprod
        (fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))) (psl2zEquivCoprodI g) =
      psl2zEquivCoprod g :=
  (Monoid.CoprodI.finTwoEquivCoprod _).apply_symm_apply _

/-- `psl2zEquivCoprodI` maps `S` to the generator of the factor at `0 : Fin 2`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_S :
    psl2zEquivCoprodI (S : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) := by
  apply (Monoid.CoprodI.finTwoEquivCoprod _).injective
  rw [finTwoEquivCoprod_psl2zEquivCoprodI, psl2zEquivCoprod_coe_S,
    Monoid.CoprodI.finTwoEquivCoprod_of_zero]
  -- `psl2zCoprodOrder 0 = 2` and `psl2zCoprodOrder 1 = 3` hold definitionally.
  rfl

/-- `psl2zEquivCoprodI` maps `R` to the generator of the factor at `1 : Fin 2`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_R :
    psl2zEquivCoprodI (R : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1) := by
  apply (Monoid.CoprodI.finTwoEquivCoprod _).injective
  rw [finTwoEquivCoprod_psl2zEquivCoprodI, psl2zEquivCoprod_coe_R,
    Monoid.CoprodI.finTwoEquivCoprod_of_one]
  -- `psl2zCoprodOrder 0 = 2` and `psl2zCoprodOrder 1 = 3` hold definitionally.
  rfl

/-- `psl2zEquivCoprodI` maps the cusp translation `T` to
`of 0 (ofAdd 1) * of 1 (ofAdd 1)`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_T :
    psl2zEquivCoprodI (T : PSL(2, ℤ)) =
      Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) *
        Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R]
  simp [-coe_S_mul_coe_R]

/-- `psl2zEquivCoprodI` maps `U = S * T⁻¹` to
`of 0 (ofAdd 1) * of 1 (ofAdd (-1)) * of 0 (ofAdd 1)`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_U :
    psl2zEquivCoprodI (U : PSL(2, ℤ)) =
      Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) *
        Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd (-1)) *
        Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) := by
  rw [← coe_S_mul_coe_R_inv_mul_coe_S_inv]
  simp

/-- The inverse of `psl2zEquivCoprodI` maps the generator at `0 : Fin 2` to `S`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_zero_ofAdd_one :
    psl2zEquivCoprodI.symm (Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1)) =
      (S : PSL(2, ℤ)) :=
  psl2zEquivCoprodI.symm_apply_eq.mpr psl2zEquivCoprodI_coe_S.symm

/-- The inverse of `psl2zEquivCoprodI` maps the generator at `1 : Fin 2` to `R`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_one_ofAdd_one :
    psl2zEquivCoprodI.symm (Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1)) =
      (R : PSL(2, ℤ)) :=
  psl2zEquivCoprodI.symm_apply_eq.mpr psl2zEquivCoprodI_coe_R.symm

/-- The inverse of `psl2zEquivCoprodI` maps `ofAdd (k : ZMod (psl2zCoprodOrder 0))` at `0 : Fin 2`
to `S ^ k`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_zero_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprodI.symm
        (Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd (k : ZMod (psl2zCoprodOrder 0)))) =
      (S : PSL(2, ℤ)) ^ k := by
  rw [Multiplicative.ofAdd_intCast, map_zpow, map_zpow,
    psl2zEquivCoprodI_symm_of_zero_ofAdd_one]

/-- The inverse of `psl2zEquivCoprodI` maps `ofAdd (k : ZMod (psl2zCoprodOrder 1))` at `1 : Fin 2`
to `R ^ k`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_one_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprodI.symm
        (Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd (k : ZMod (psl2zCoprodOrder 1)))) =
      (R : PSL(2, ℤ)) ^ k := by
  rw [Multiplicative.ofAdd_intCast, map_zpow, map_zpow,
    psl2zEquivCoprodI_symm_of_one_ofAdd_one]

/-! ### Subgroup index divisibility for torsion-free subgroups -/

/-- If `Γ ≤ PSL(2, ℤ)` contains no nontrivial element of finite order, then `6 ∣ Γ.index`
(including when `Γ` has infinite index, where `Γ.index = 0`). -/
theorem _root_.Subgroup.six_dvd_index_of_forall_isOfFinOrder_eq_one_psl2z (Γ : Subgroup PSL(2, ℤ))
    (hΓ : ∀ g ∈ Γ, IsOfFinOrder g → g = 1) :
    6 ∣ Γ.index := by
  have h2 : 2 ∣ Γ.index := by
    have h := Γ.orderOf_dvd_index_of_forall_isOfFinOrder_eq_one hΓ isOfFinOrder_coe_S
    rwa [orderOf_coe_S] at h
  have h3 : 3 ∣ Γ.index := by
    have h := Γ.orderOf_dvd_index_of_forall_isOfFinOrder_eq_one hΓ isOfFinOrder_coe_R
    rwa [orderOf_coe_R] at h
  exact (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3

/-- If `Γ ≤ PSL(2, ℤ)` is torsion-free, then `6 ∣ Γ.index`. -/
theorem _root_.Subgroup.six_dvd_index_of_isMulTorsionFree_psl2z (Γ : Subgroup PSL(2, ℤ))
    [IsMulTorsionFree Γ] :
    6 ∣ Γ.index :=
  Γ.six_dvd_index_of_forall_isOfFinOrder_eq_one_psl2z
    fun _ hg hg_fin ↦ Γ.toSubmonoid.eq_one_of_isOfFinOrder_mem hg hg_fin

end TauCeti.ModularGroup

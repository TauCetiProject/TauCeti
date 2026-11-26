/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.CoprodI.Basic
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Algebra.Group.Submonoid.Torsion
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Triangle.Group
import TauCeti.Data.ZMod.MonoidHomEquiv
import TauCeti.GroupTheory.Index.Torsion
import TauCeti.GroupTheory.OrderOfElement.Basic
import TauCeti.GroupTheory.TriangleGroup.FreeProduct
import TauCeti.NumberTheory.Modular.Abelianization
import TauCeti.NumberTheory.Modular.Torsion

/-!
# Free-product decomposition and torsion/abelianization corollaries for `PSL(2, ℤ)`

Combining Poincaré's triangle presentation `PSL(2, ℤ) ≃* Δ(3, 2, ∞)`
(`TauCeti.ModularGroup.triangleGroupEquiv`) with the free-product decomposition of `Δ(a, b, 0)`
(`TauCeti.TriangleGroup.equivCoprod`) identifies the projective modular group with the free product
`ℤ/2ℤ ∗ ℤ/3ℤ`, both in binary form (`Monoid.Coprod`) and in indexed form (`Monoid.CoprodI` over
`Fin 2`), sending the involution `S` to the generator of `ℤ/2ℤ` and `R = S * T` to the generator of
`ℤ/3ℤ`.

Together with the torsion classification (`TauCeti.NumberTheory.Modular.Torsion`) and
abelianization (`TauCeti.NumberTheory.Modular.Abelianization`), this yields:

* **Torsion conjugacy classes**: the non-conjugacy of `S` with `R`, `R²`, `U`, `U²` and of `U`
  with `U²`, together with the `U = S * T⁻¹` forms of the torsion and order-`3` classifications
  and the set of possible finite orders `{1, 2, 3}`.
* **Index divisibility**: for any torsion-free subgroup `Γ ≤ PSL(2, ℤ)`, `6 ∣ Γ.index` (including
  infinite index, encoded by `0`).
* **Abelianization cardinality and commutator index**:
  `Nat.card (Group.Abelianization PSL(2, ℤ)) = 6` and `(commutator PSL(2, ℤ)).index = 6`.

## Main declarations

* `TauCeti.ModularGroup.psl2zEquivCoprod`:
  `PSL(2, ℤ) ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 3))`.
* `TauCeti.ModularGroup.psl2zEquivCoprodI`,
  `TauCeti.ModularGroup.finTwoEquivCoprod_psl2zEquivCoprodI`:
  `PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))`, and
  its comparison with `psl2zEquivCoprod`.
* `TauCeti.ModularGroup.not_isConj_coe_S_coe_R`, `TauCeti.ModularGroup.not_isConj_coe_U_coe_U_sq`:
  pairwise non-conjugacy of the remaining elliptic representatives.
* `TauCeti.ModularGroup.isOfFinOrder_iff_coe_U`,
  `TauCeti.ModularGroup.orderOf_eq_one_or_two_or_three_of_isOfFinOrder`,
  `TauCeti.ModularGroup.orderOf_eq_three_iff_coe_U`: `U`-form torsion and order-`3`
  classifications and finite-order values in `PSL(2, ℤ)`.
* `Subgroup.six_dvd_index_of_forall_isOfFinOrder_eq_one_psl2z`,
  `Subgroup.six_dvd_index_of_isMulTorsionFree_psl2z`: `6 ∣ Γ.index` for torsion-free `Γ`.
* `TauCeti.ModularGroup.natCard_abelianization_psl2z`,
  `TauCeti.ModularGroup.index_commutator_psl2z`: abelianization cardinality `6` and commutator
  index `6`.

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

/-- The inverse of `psl2zEquivCoprod` sends `inl (ofAdd k)` to `S ^ k`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inl_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprod.symm (.inl (.ofAdd (k : ZMod 2))) = (S : PSL(2, ℤ)) ^ k := by
  simp [psl2zEquivCoprod, MulEquiv.symm_trans_apply]

/-- The inverse of `psl2zEquivCoprod` sends `inr (ofAdd k)` to `R ^ k`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inr_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprod.symm (.inr (.ofAdd (k : ZMod 3))) = (R : PSL(2, ℤ)) ^ k := by
  simp [psl2zEquivCoprod, MulEquiv.symm_trans_apply, coe_S_mul_coe_T]

/-- The inverse of `psl2zEquivCoprod` sends `inl (ofAdd 1)` to `S`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inl_ofAdd_one :
    psl2zEquivCoprod.symm (.inl (.ofAdd 1)) = (S : PSL(2, ℤ)) := by
  simpa using psl2zEquivCoprod_symm_inl_ofAdd_intCast 1

/-- The inverse of `psl2zEquivCoprod` sends `inr (ofAdd 1)` to `R`. -/
@[simp]
theorem psl2zEquivCoprod_symm_inr_ofAdd_one :
    psl2zEquivCoprod.symm (.inr (.ofAdd 1)) = (R : PSL(2, ℤ)) := by
  simpa using psl2zEquivCoprod_symm_inr_ofAdd_intCast 1

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
    psl2zEquivCoprodI (S : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) :=
  (congrArg (Monoid.CoprodI.finTwoEquivCoprod
      fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm
    psl2zEquivCoprod_coe_S).trans
    (Monoid.CoprodI.finTwoEquivCoprod_symm_inl
      (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))) (.ofAdd 1))

/-- `psl2zEquivCoprodI` maps `R` to the generator of the factor at `1 : Fin 2`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_R :
    psl2zEquivCoprodI (R : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1) :=
  (congrArg (Monoid.CoprodI.finTwoEquivCoprod
      fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm
    psl2zEquivCoprod_coe_R).trans
    (Monoid.CoprodI.finTwoEquivCoprod_symm_inr
      (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))) (.ofAdd 1))

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
  simpa [psl2zEquivCoprodI_symm_of_zero_ofAdd_one] using
    zmodMonoidHom_map_ofAdd_intCast
      (psl2zEquivCoprodI.symm.toMonoidHom.comp
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i)))
          (i := (0 : Fin 2)))) k

/-- The inverse of `psl2zEquivCoprodI` maps `ofAdd (k : ZMod (psl2zCoprodOrder 1))` at `1 : Fin 2`
to `R ^ k`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_one_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprodI.symm
        (Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd (k : ZMod (psl2zCoprodOrder 1)))) =
      (R : PSL(2, ℤ)) ^ k := by
  simpa [psl2zEquivCoprodI_symm_of_one_ofAdd_one] using
    zmodMonoidHom_map_ofAdd_intCast
      (psl2zEquivCoprodI.symm.toMonoidHom.comp
        (Monoid.CoprodI.of (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i)))
          (i := (1 : Fin 2)))) k

/-! ### Conjugacy classes and orders of torsion elements in `PSL(2, ℤ)` -/

/-- `S` and `R` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_R : ¬IsConj (S : PSL(2, ℤ)) (R : PSL(2, ℤ)) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `S` and `R²` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_R_sq : ¬IsConj (S : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `S` and `U` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_U : ¬IsConj (S : PSL(2, ℤ)) (U : PSL(2, ℤ)) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `S` and `U²` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_U_sq : ¬IsConj (S : PSL(2, ℤ)) ((U : PSL(2, ℤ)) ^ 2) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `U` and `U²` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_U_coe_U_sq : ¬IsConj (U : PSL(2, ℤ)) ((U : PSL(2, ℤ)) ^ 2) := fun h ↦
  not_isConj_coe_R_coe_R_sq <|
    isConj_coe_U_sq_coe_R.symm.trans (h.symm.trans isConj_coe_U_coe_R_sq)

/-- Conjugacy to `R` or `R²` in `PSL(2, ℤ)` is equivalent to conjugacy to `U` or `U²`. -/
theorem isConj_coe_R_or_sq_iff_coe_U_or_sq {g : PSL(2, ℤ)} :
    (IsConj g (R : PSL(2, ℤ)) ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2)) ↔
      (IsConj g (U : PSL(2, ℤ)) ∨ IsConj g ((U : PSL(2, ℤ)) ^ 2)) := by
  constructor
  · rintro (hR | hR2)
    · exact Or.inr (hR.trans isConj_coe_U_sq_coe_R.symm)
    · exact Or.inl (hR2.trans isConj_coe_U_coe_R_sq.symm)
  · rintro (hU | hU2)
    · exact Or.inr (hU.trans isConj_coe_U_coe_R_sq)
    · exact Or.inl (hU2.trans isConj_coe_U_sq_coe_R)

/-- **Classification of torsion elements in `PSL(2, ℤ)`** (with `U = S * T⁻¹`): an element of
`PSL(2, ℤ)` has finite order if and only if it is `1` or conjugate to `S`, `U`, or `U²`. -/
theorem isOfFinOrder_iff_coe_U {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔
      g = 1 ∨ IsConj g (S : PSL(2, ℤ)) ∨ IsConj g (U : PSL(2, ℤ)) ∨
        IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [isOfFinOrder_iff_eq_one_or_isConj, isConj_coe_R_or_sq_iff_coe_U_or_sq]

/-- Every element of finite order in `PSL(2, ℤ)` has order `1`, `2`, or `3`. -/
theorem orderOf_eq_one_or_two_or_three_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  rcases isOfFinOrder_iff_eq_one_or_isConj.mp hg with rfl | hS | hR | hR2
  · exact Or.inl orderOf_one
  · exact Or.inr (Or.inl (hS.orderOf_eq.trans orderOf_coe_S))
  · exact Or.inr (Or.inr (hR.orderOf_eq.trans orderOf_coe_R))
  · exact Or.inr (Or.inr (hR2.orderOf_eq.trans orderOf_coe_R_sq))

/-- Elements of order `3` in `PSL(2, ℤ)` form the two conjugacy classes of `U` and `U²`. -/
theorem orderOf_eq_three_iff_coe_U {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (U : PSL(2, ℤ)) ∨ IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [orderOf_eq_three_iff_isConj, isConj_coe_R_or_sq_iff_coe_U_or_sq]

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

/-! ### Abelianization cardinality and commutator index of `PSL(2, ℤ)` -/

/-- The abelianization of `PSL(2, ℤ)` has cardinality `6`. -/
@[simp]
theorem natCard_abelianization_psl2z :
    Nat.card (Group.Abelianization PSL(2, ℤ)) = 6 := by
  rw [Nat.card_congr abelianizationMulEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

/-- The commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` has index `6` in `PSL(2, ℤ)`. -/
@[simp]
theorem index_commutator_psl2z :
    (commutator PSL(2, ℤ)).index = 6 := by
  rw [Subgroup.index_eq_card,
    Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq (Group.Abelianization.ker_of PSL(2, ℤ)).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _
          (Group.Abelianization.surjective_of PSL(2, ℤ)))).toEquiv,
    natCard_abelianization_psl2z]

end TauCeti.ModularGroup

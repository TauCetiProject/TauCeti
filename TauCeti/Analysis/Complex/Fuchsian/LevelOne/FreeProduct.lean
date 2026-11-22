/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Index
public import TauCeti.NumberTheory.Modular.Generators
import TauCeti.Algebra.Group.Conj
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.TriangleGroup
import TauCeti.GroupTheory.Coprod.Conj
import TauCeti.GroupTheory.Coprod.Torsion
import TauCeti.GroupTheory.CoprodI
import TauCeti.GroupTheory.Index.Torsion
import TauCeti.GroupTheory.TriangleGroup.FreeProduct

/-!
# Free-product decomposition, torsion classes, and abelianization of `PSL(2, ℤ)`

Combining Poincaré's triangle presentation `PSL(2, ℤ) ≃* Δ(3, 2, ∞)`
(`TauCeti.ModularGroup.triangleGroupEquiv`) with the free-product decomposition of `Δ(a, b, 0)`
(`TauCeti.TriangleGroup.equivCoprod`) identifies the projective modular group with the free product
`ℤ/2ℤ ∗ ℤ/3ℤ`, both in binary form (`Monoid.Coprod`) and in indexed form (`Monoid.CoprodI` over
`Fin 2`), sending the involution `S` to the generator of `ℤ/2ℤ` and `R = S * T` to the generator of
`ℤ/3ℤ`.

Applying the normal-form theory of torsion and conjugacy in free products (`Monoid.Coprod`) yields
the algebraic structure of finite-order elements and characters of `PSL(2, ℤ)`:

* **Torsion conjugacy classes**: every element of finite order in `PSL(2, ℤ)` is equal to `1` or
  conjugate to one of `S`, `R`, `R²` (equivalently `S`, `U`, `U²`, where `U = S * T⁻¹`), and these
  three nontrivial classes are pairwise non-conjugate.
* **Orders of torsion elements**: every element of finite order in `PSL(2, ℤ)` has order `1`, `2`,
  or `3`; elements of order `2` form the single conjugacy class of `S`, and elements of order `3`
  form the two conjugacy classes of `R` and `R²` (or `U` and `U²`).
* **Index divisibility**: for any torsion-free subgroup `Γ ≤ PSL(2, ℤ)`, `6 ∣ Γ.index` (including
  infinite index, encoded by `0`).
* **Abelianization**: `Additive (Group.Abelianization PSL(2, ℤ)) ≃+ ZMod 6`, normalized so that the
  cusp translation `T` maps to `1`, `U` to `2`, `S` to `3`, and `R` to `4`; consequently
  `(commutator PSL(2, ℤ)).index = 6`.

## Main declarations

* `TauCeti.ModularGroup.psl2zEquivCoprod`:
  `PSL(2, ℤ) ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 3))`.
* `TauCeti.ModularGroup.psl2zEquivCoprodI`:
  `PSL(2, ℤ) ≃* Monoid.CoprodI fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))`.
* `TauCeti.ModularGroup.isOfFinOrder_iff`, `TauCeti.ModularGroup.isOfFinOrder_iff_coe_U`:
  classification of torsion elements up to conjugacy.
* `TauCeti.ModularGroup.not_isConj_coe_S_coe_R`, `TauCeti.ModularGroup.not_isConj_coe_R_coe_R_sq`,
  `TauCeti.ModularGroup.not_isConj_coe_U_coe_U_sq`: pairwise non-conjugacy of the elliptic
  representatives.
* `TauCeti.ModularGroup.orderOf_eq_two_iff`, `TauCeti.ModularGroup.orderOf_eq_three_iff`:
  conjugacy characterization of elements of order `2` and `3`.
* `Subgroup.six_dvd_index_of_forall_isOfFinOrder_eq_one`,
  `Subgroup.six_dvd_index_of_isMulTorsionFree`: `6 ∣ Γ.index` for torsion-free `Γ`.
* `TauCeti.ModularGroup.psl2zAbelianizationAddEquiv`,
  `TauCeti.ModularGroup.psl2zAbelianizationMulEquiv`,
  `TauCeti.ModularGroup.index_commutator_psl2z`: abelianization `≃ ZMod 6` and commutator index `6`.

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

/-- `psl2zEquivCoprodI` maps `S` to the generator of the factor at `0 : Fin 2`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_S :
    psl2zEquivCoprodI (S : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) := by
  calc psl2zEquivCoprodI (S : PSL(2, ℤ))
    _ = (Monoid.CoprodI.finTwoEquivCoprod
          fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm
          (psl2zEquivCoprod (S : PSL(2, ℤ))) := rfl
    _ = (Monoid.CoprodI.finTwoEquivCoprod
          fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm (.inl (.ofAdd 1)) :=
        congrArg _ psl2zEquivCoprod_coe_S
    _ = Monoid.CoprodI.of (i := (0 : Fin 2)) (.ofAdd 1) :=
        Monoid.CoprodI.finTwoEquivCoprod_symm_inl
          (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))) (.ofAdd 1)

/-- `psl2zEquivCoprodI` maps `R` to the generator of the factor at `1 : Fin 2`. -/
@[simp]
theorem psl2zEquivCoprodI_coe_R :
    psl2zEquivCoprodI (R : PSL(2, ℤ)) = Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1) := by
  calc psl2zEquivCoprodI (R : PSL(2, ℤ))
    _ = (Monoid.CoprodI.finTwoEquivCoprod
          fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm
          (psl2zEquivCoprod (R : PSL(2, ℤ))) := rfl
    _ = (Monoid.CoprodI.finTwoEquivCoprod
          fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))).symm (.inr (.ofAdd 1)) :=
        congrArg _ psl2zEquivCoprod_coe_R
    _ = Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd 1) :=
        Monoid.CoprodI.finTwoEquivCoprod_symm_inr
          (M := fun i : Fin 2 ↦ Multiplicative (ZMod (psl2zCoprodOrder i))) (.ofAdd 1)

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
  rw [← zsmul_one k, ofAdd_zsmul, map_zpow, map_zpow, psl2zEquivCoprodI_symm_of_zero_ofAdd_one]

/-- The inverse of `psl2zEquivCoprodI` maps `ofAdd (k : ZMod (psl2zCoprodOrder 1))` at `1 : Fin 2`
to `R ^ k`. -/
@[simp]
theorem psl2zEquivCoprodI_symm_of_one_ofAdd_intCast (k : ℤ) :
    psl2zEquivCoprodI.symm
        (Monoid.CoprodI.of (i := (1 : Fin 2)) (.ofAdd (k : ZMod (psl2zCoprodOrder 1)))) =
      (R : PSL(2, ℤ)) ^ k := by
  rw [← zsmul_one k, ofAdd_zsmul, map_zpow, map_zpow, psl2zEquivCoprodI_symm_of_one_ofAdd_one]

/-! ### Conjugacy classes and orders of torsion elements in `PSL(2, ℤ)` -/

/-- `S` and `R` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_R : ¬IsConj (S : PSL(2, ℤ)) (R : PSL(2, ℤ)) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `S` and `R²` are not conjugate in `PSL(2, ℤ)`. -/
theorem not_isConj_coe_S_coe_R_sq : ¬IsConj (S : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := fun h ↦ by
  have hord := h.orderOf_eq
  simp at hord

/-- `R` and `R²` are not conjugate in `PSL(2, ℤ)`, although both have order `3`. -/
theorem not_isConj_coe_R_coe_R_sq : ¬IsConj (R : PSL(2, ℤ)) ((R : PSL(2, ℤ)) ^ 2) := fun h ↦ by
  have hmap := psl2zEquivCoprod.toMonoidHom.map_isConj h
  rw [MulEquiv.coe_toMonoidHom, map_pow, psl2zEquivCoprod_coe_R, ← map_pow,
    Monoid.Coprod.isConj_inr_iff, isConj_iff_eq] at hmap
  have hadd : (1 : ZMod 3) = 2 := by
    simpa [← ofAdd_nsmul] using congrArg Multiplicative.toAdd hmap
  exact absurd hadd (by decide)

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

/-- **Classification of torsion elements in `PSL(2, ℤ)`** (with `R = S * T`): an element of
`PSL(2, ℤ)` has finite order if and only if it is `1` or conjugate to `S`, `R`, or `R²`. -/
theorem isOfFinOrder_iff {g : PSL(2, ℤ)} :
    IsOfFinOrder g ↔
      g = 1 ∨ IsConj g (S : PSL(2, ℤ)) ∨ IsConj g (R : PSL(2, ℤ)) ∨
        IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  constructor
  · intro hg
    have hg' : IsOfFinOrder (psl2zEquivCoprod g) :=
      psl2zEquivCoprod.toMonoidHom.isOfFinOrder hg
    rcases Monoid.Coprod.exists_isConj_inl_or_inr_of_isOfFinOrder hg' with
      ⟨u, hconj, -⟩ | ⟨v, hconj, -⟩
    · obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective u
      have ha : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      rcases ha a with rfl | rfl
      · rw [ofAdd_zero, map_one, isConj_one_left] at hconj
        exact Or.inl (psl2zEquivCoprod.injective (hconj.trans (map_one _).symm))
      · rw [← psl2zEquivCoprod_coe_S] at hconj
        have hgS := psl2zEquivCoprod.symm.toMonoidHom.map_isConj hconj
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hgS
        exact Or.inr (Or.inl hgS)
    · obtain ⟨b, rfl⟩ := Multiplicative.ofAdd.surjective v
      have hb : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases hb b with rfl | rfl | rfl
      · rw [ofAdd_zero, map_one, isConj_one_left] at hconj
        exact Or.inl (psl2zEquivCoprod.injective (hconj.trans (map_one _).symm))
      · rw [← psl2zEquivCoprod_coe_R] at hconj
        have hgR := psl2zEquivCoprod.symm.toMonoidHom.map_isConj hconj
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hgR
        exact Or.inr (Or.inr (Or.inl hgR))
      · have h2 : Monoid.Coprod.inr (M := Multiplicative (ZMod 2))
            (Multiplicative.ofAdd (2 : ZMod 3)) = psl2zEquivCoprod ((R : PSL(2, ℤ)) ^ 2) := by
          rw [map_pow, psl2zEquivCoprod_coe_R, ← map_pow, ← ofAdd_nsmul]
          rfl
        rw [h2] at hconj
        have hgR2 := psl2zEquivCoprod.symm.toMonoidHom.map_isConj hconj
        simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hgR2
        exact Or.inr (Or.inr (Or.inr hgR2))
  · rintro (rfl | h | h | h)
    · exact IsOfFinOrder.one
    · exact h.symm.isOfFinOrder isOfFinOrder_coe_S
    · exact h.symm.isOfFinOrder isOfFinOrder_coe_R
    · exact h.symm.isOfFinOrder isOfFinOrder_coe_R_sq

/-- Conjugacy to `R` or `R²` in `PSL(2, ℤ)` is equivalent to conjugacy to `U` or `U²`. -/
theorem isConj_coe_R_or_sq_iff_coe_U {g : PSL(2, ℤ)} :
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
  rw [isOfFinOrder_iff, isConj_coe_R_or_sq_iff_coe_U]

/-- Every element of finite order in `PSL(2, ℤ)` has order `1`, `2`, or `3`. -/
theorem orderOf_eq_one_or_two_or_three_of_isOfFinOrder {g : PSL(2, ℤ)} (hg : IsOfFinOrder g) :
    orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 3 := by
  rcases isOfFinOrder_iff.mp hg with rfl | hS | hR | hR2
  · exact Or.inl orderOf_one
  · exact Or.inr (Or.inl (hS.orderOf_eq.trans orderOf_coe_S))
  · exact Or.inr (Or.inr (hR.orderOf_eq.trans orderOf_coe_R))
  · exact Or.inr (Or.inr (hR2.orderOf_eq.trans orderOf_coe_R_sq))

/-- Elements of order `2` in `PSL(2, ℤ)` form a single conjugacy class, that of `S`. -/
theorem orderOf_eq_two_iff {g : PSL(2, ℤ)} :
    orderOf g = 2 ↔ IsConj g (S : PSL(2, ℤ)) := by
  constructor
  · intro hord
    have hg : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff.mp hg with rfl | hS | hR | hR2
    · simp at hord
    · exact hS
    · have := hR.orderOf_eq; simp [hord] at this
    · have := hR2.orderOf_eq; simp [hord] at this
  · intro hS
    exact hS.orderOf_eq.trans orderOf_coe_S

/-- Elements of order `3` in `PSL(2, ℤ)` form the two conjugacy classes of `R` and `R²`. -/
theorem orderOf_eq_three_iff {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (R : PSL(2, ℤ)) ∨ IsConj g ((R : PSL(2, ℤ)) ^ 2) := by
  constructor
  · intro hord
    have hg : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff.mp hg with rfl | hS | hR | hR2
    · simp at hord
    · have := hS.orderOf_eq; simp [hord] at this
    · exact Or.inl hR
    · exact Or.inr hR2
  · rintro (hR | hR2)
    · exact hR.orderOf_eq.trans orderOf_coe_R
    · exact hR2.orderOf_eq.trans orderOf_coe_R_sq

/-- Elements of order `3` in `PSL(2, ℤ)` form the two conjugacy classes of `U` and `U²`. -/
theorem orderOf_eq_three_iff_coe_U {g : PSL(2, ℤ)} :
    orderOf g = 3 ↔ IsConj g (U : PSL(2, ℤ)) ∨ IsConj g ((U : PSL(2, ℤ)) ^ 2) := by
  rw [orderOf_eq_three_iff, isConj_coe_R_or_sq_iff_coe_U]

/-! ### Subgroup index divisibility for torsion-free subgroups -/

/-- If `Γ ≤ PSL(2, ℤ)` contains no nontrivial element of finite order, then `6 ∣ Γ.index`
(including when `Γ` has infinite index, where `Γ.index = 0`). -/
theorem _root_.Subgroup.six_dvd_index_of_forall_isOfFinOrder_eq_one (Γ : Subgroup PSL(2, ℤ))
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
theorem _root_.Subgroup.six_dvd_index_of_isMulTorsionFree (Γ : Subgroup PSL(2, ℤ))
    [IsMulTorsionFree Γ] :
    6 ∣ Γ.index :=
  Γ.six_dvd_index_of_forall_isOfFinOrder_eq_one
    fun _ hg hg_fin ↦ Γ.toSubmonoid.eq_one_of_isOfFinOrder_mem hg hg_fin

/-! ### Abelianization of `PSL(2, ℤ)` -/

/-- **Additive abelianization of `PSL(2, ℤ)`.** The abelianization of `PSL(2, ℤ)`, written
additively, is canonically isomorphic to `ZMod 6`, normalized so that the cusp translation `T` maps
to `1`, `U = S * T⁻¹` maps to `2`, `S` maps to `3`, and `R = S * T` maps to `4`. -/
def psl2zAbelianizationAddEquiv :
    Additive (Group.Abelianization PSL(2, ℤ)) ≃+ ZMod 6 :=
  triangleGroupEquiv.symm.abelianizationCongr.toAdditive.trans
    (TriangleGroup.abelianizationZeroAddEquivZMod (by decide : Nat.Coprime 3 2))

/-- `psl2zAbelianizationAddEquiv` sends the class of `S` to `3`. -/
@[simp]
theorem psl2zAbelianizationAddEquiv_coe_S :
    psl2zAbelianizationAddEquiv (.ofMul (.of (S : PSL(2, ℤ)))) = 3 := by
  apply (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)).injective
  have h3 : (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)) 3 = (0, 1) := by decide
  rw [h3, psl2zAbelianizationAddEquiv, AddEquiv.trans_apply,
    TriangleGroup.chineseRemainder_abelianizationZeroAddEquivZMod]
  simp [triangleGroupEquiv_symm_coe_S]

/-- `psl2zAbelianizationAddEquiv` sends the class of `R = S * T` to `4`. -/
@[simp]
theorem psl2zAbelianizationAddEquiv_coe_R :
    psl2zAbelianizationAddEquiv (.ofMul (.of (R : PSL(2, ℤ)))) = 4 := by
  apply (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)).injective
  have h4 : (ZMod.chineseRemainder (by decide : Nat.Coprime 3 2)) 4 = (1, 0) := by decide
  rw [h4, psl2zAbelianizationAddEquiv, AddEquiv.trans_apply,
    TriangleGroup.chineseRemainder_abelianizationZeroAddEquivZMod]
  simp [triangleGroupEquiv_symm_coe_R]

/-- `psl2zAbelianizationAddEquiv` sends the class of the cusp translation `T` to `1`. -/
@[simp]
theorem psl2zAbelianizationAddEquiv_coe_T :
    psl2zAbelianizationAddEquiv (.ofMul (.of (T : PSL(2, ℤ)))) = 1 := by
  rw [← coe_S_mul_coe_R]
  simp +decide [-coe_S_mul_coe_R]

/-- `psl2zAbelianizationAddEquiv` sends the class of `U = S * T⁻¹` to `2`. -/
@[simp]
theorem psl2zAbelianizationAddEquiv_coe_U :
    psl2zAbelianizationAddEquiv (.ofMul (.of (U : PSL(2, ℤ)))) = 2 := by
  rw [U_def]
  simp +decide

/-- The inverse of `psl2zAbelianizationAddEquiv` maps `1` to the class of `T`. -/
@[simp]
theorem psl2zAbelianizationAddEquiv_symm_one :
    psl2zAbelianizationAddEquiv.symm 1 = .ofMul (.of (T : PSL(2, ℤ))) := by
  apply psl2zAbelianizationAddEquiv.injective
  rw [AddEquiv.apply_symm_apply, psl2zAbelianizationAddEquiv_coe_T]

/-- **Multiplicative abelianization of `PSL(2, ℤ)`.** Identifies `Group.Abelianization PSL(2, ℤ)`
with `Multiplicative (ZMod 6)`, sending `Group.Abelianization.of (T : PSL(2, ℤ))` to
`Multiplicative.ofAdd 1`. -/
def psl2zAbelianizationMulEquiv :
    Group.Abelianization PSL(2, ℤ) ≃* Multiplicative (ZMod 6) :=
  psl2zAbelianizationAddEquiv.toMultiplicative

/-- `psl2zAbelianizationMulEquiv` sends the class of `S` to `ofAdd 3`. -/
@[simp]
theorem psl2zAbelianizationMulEquiv_coe_S :
    psl2zAbelianizationMulEquiv (.of (S : PSL(2, ℤ))) = .ofAdd 3 :=
  congrArg Multiplicative.ofAdd psl2zAbelianizationAddEquiv_coe_S

/-- `psl2zAbelianizationMulEquiv` sends the class of `R` to `ofAdd 4`. -/
@[simp]
theorem psl2zAbelianizationMulEquiv_coe_R :
    psl2zAbelianizationMulEquiv (.of (R : PSL(2, ℤ))) = .ofAdd 4 :=
  congrArg Multiplicative.ofAdd psl2zAbelianizationAddEquiv_coe_R

/-- `psl2zAbelianizationMulEquiv` sends the class of `T` to `ofAdd 1`. -/
@[simp]
theorem psl2zAbelianizationMulEquiv_coe_T :
    psl2zAbelianizationMulEquiv (.of (T : PSL(2, ℤ))) = .ofAdd 1 :=
  congrArg Multiplicative.ofAdd psl2zAbelianizationAddEquiv_coe_T

/-- `psl2zAbelianizationMulEquiv` sends the class of `U` to `ofAdd 2`. -/
@[simp]
theorem psl2zAbelianizationMulEquiv_coe_U :
    psl2zAbelianizationMulEquiv (.of (U : PSL(2, ℤ))) = .ofAdd 2 :=
  congrArg Multiplicative.ofAdd psl2zAbelianizationAddEquiv_coe_U

/-- The inverse of `psl2zAbelianizationMulEquiv` maps `ofAdd 1` to the class of `T`. -/
@[simp]
theorem psl2zAbelianizationMulEquiv_symm_ofAdd_one :
    psl2zAbelianizationMulEquiv.symm (.ofAdd 1) = .of (T : PSL(2, ℤ)) := by
  apply psl2zAbelianizationMulEquiv.injective
  rw [MulEquiv.apply_symm_apply, psl2zAbelianizationMulEquiv_coe_T]

/-- The abelianization of `PSL(2, ℤ)` has cardinality `6`. -/
@[simp]
theorem natCard_abelianization_psl2z :
    Nat.card (Group.Abelianization PSL(2, ℤ)) = 6 := by
  rw [Nat.card_congr psl2zAbelianizationMulEquiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

/-- The commutator subgroup `[PSL(2, ℤ), PSL(2, ℤ)]` has index `6` in `PSL(2, ℤ)`. -/
@[simp]
theorem index_commutator_psl2z :
    (commutator PSL(2, ℤ)).index = 6 :=
  natCard_abelianization_psl2z

end TauCeti.ModularGroup

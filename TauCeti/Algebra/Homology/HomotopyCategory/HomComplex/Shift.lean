/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# The normalized identification of cochains between shifted complexes

For cochain complexes `K` and `L` and shifts `r` and `s`, the cochains of degree `n + (s - r)`
from `K` to `L` are identified with the cochains of degree `n` from `K⟦r⟧` to `L⟦s⟧`.  This file
records the **normalized** such identification: it sends a cochain `z` to the cochain whose
component `K⟦r⟧^i ⟶ L⟦s⟧^j` is `(-1)^(r * n)` times the component `K^(i + r) ⟶ L^(j + s)` of
`z`, and it intertwines the differential `δ` of the target with `(-1)^(s - r) δ` on the source.

It is assembled from Mathlib's `CochainComplex.HomComplex.Cochain.rightShift` and
`CochainComplex.HomComplex.Cochain.leftShift`, which together differ from it by the sign
`(-1)^(r * (r - 1) / 2)` depending only on the source shift.  This is the sign convention of the
shift closure of a differential graded category.

## Main definitions

* `TauCeti.cochainShiftLinearEquiv`: the normalized identification
  `Cochain K L (n + (s - r)) ≃ₗ[R] Cochain (K⟦r⟧) (L⟦s⟧) n`.

## Main results

* `TauCeti.cochainShiftLinearEquiv_v`: the identification multiplies the underlying components
  by `(-1)^(r * n)`.
* `TauCeti.δ_cochainShiftLinearEquiv`: the identification intertwines `δ` with
  `(-1)^(s - r) δ`.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory CochainComplex.HomComplex

namespace TauCeti

universe v u

variable (R : Type v) [Ring R] {V : Type u} [Category.{v} V] [Preadditive V] [Linear R V]

/-- The **normalized identification** of the cochains of degree `n + (s - r)` from `K` to `L`
with the cochains of degree `n` from `K⟦r⟧` to `L⟦s⟧`, assembled from Mathlib's right and left
shifts of cochains and the sign `(-1)^(r * (r - 1) / 2)`.  Its components are computed by
`TauCeti.cochainShiftLinearEquiv_v`. -/
noncomputable def cochainShiftLinearEquiv (K L : CochainComplex V ℤ) (r s n : ℤ) :
    Cochain K L (n + (s - r)) ≃ₗ[R] Cochain (K⟦r⟧) (L⟦s⟧) n :=
  ((Cochain.rightShiftLinearEquiv R K L (n + (s - r)) s (n - r) (by omega)).trans
    (Cochain.leftShiftLinearEquiv R K (L⟦s⟧) (n - r) r n (by omega))).trans
      (DistribMulAction.toLinearEquiv R _ (r * (r - 1) / 2).negOnePow)

/-- The normalized identification multiplies the underlying cochain by `(-1)^(r * n)`: its
component `K⟦r⟧^i ⟶ L⟦s⟧^j` is `(-1)^(r * n)` times the component `K^(i + r) ⟶ L^(j + s)`. -/
@[simp]
theorem cochainShiftLinearEquiv_v (K L : CochainComplex V ℤ) (r s n : ℤ)
    (z : Cochain K L (n + (s - r))) (i j : ℤ) (hij : i + n = j) :
    (cochainShiftLinearEquiv R K L r s n z).v i j hij =
      (r * n).negOnePow • z.v (i + r) (j + s) (by omega) := by
  simp only [cochainShiftLinearEquiv, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_apply, Cochain.rightShiftLinearEquiv_apply,
    Cochain.leftShiftLinearEquiv_apply, Cochain.units_smul_v]
  rw [Cochain.leftShift_v _ r n (by omega) i j hij (i + r) (by omega),
    Cochain.rightShift_v _ s (n - r) (by omega) (i + r) j (by omega) (j + s) (by omega)]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Iso.refl_inv, Category.comp_id, smul_smul, ← Int.negOnePow_add]
  congr 1
  · rw [Int.negOnePow_eq_iff]
    exact ⟨r * (r - 1) / 2, by ring⟩
  · exact Category.id_comp _

/-- The normalized identification intertwines the differential `δ` of cochains between the
shifted complexes with `(-1)^(s - r) δ` on cochains between the unshifted ones. -/
theorem δ_cochainShiftLinearEquiv (K L : CochainComplex V ℤ) (r s n m : ℤ) (hnm : n + 1 = m)
    (z : Cochain K L (n + (s - r))) :
    δ n m (cochainShiftLinearEquiv R K L r s n z) =
      cochainShiftLinearEquiv R K L r s m
        ((s - r).negOnePow • δ (n + (s - r)) (m + (s - r)) z) := by
  subst hnm
  simp only [cochainShiftLinearEquiv, LinearEquiv.trans_apply,
    DistribMulAction.toLinearEquiv_apply, Cochain.rightShiftLinearEquiv_apply,
    Cochain.leftShiftLinearEquiv_apply, δ_units_smul, Cochain.rightShift_units_smul,
    Cochain.leftShift_units_smul]
  rw [Cochain.δ_leftShift _ r n (n + 1) (by omega) (n + 1 - r) (by omega),
    Cochain.δ_rightShift _ s (n - r) (n + 1 - r) (by omega) (n + 1 + (s - r)) (by omega),
    Cochain.leftShift_units_smul, smul_smul, smul_smul, smul_smul, Int.negOnePow_sub,
    mul_comm s.negOnePow, mul_assoc]

end TauCeti

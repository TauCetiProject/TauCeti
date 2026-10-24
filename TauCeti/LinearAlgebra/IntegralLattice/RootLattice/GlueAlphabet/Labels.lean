/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Conway--Sloane labels for component glue alphabets

The printed labels of a glue alphabet are bounded natural numbers. For `Aₙ`, `E₆`, `E₇`,
and `E₈` they enumerate the cyclic alphabet in its usual order. For `Dₙ` the labels are
`0`, spinor, vector, cospinor, in that order. In even rank this means `0`, `(0,1)`,
`(1,0)`, `(1,1)` in the existing Klein four model, whose first generator is the vector
class. In odd rank the labels enumerate the cyclic group of order four.

`glueLabelEquiv` identifies these bounded labels with the existing finite quadratic module;
it is an equivalence of types, not an assertion that digit addition is cyclic in even rank.
These labels allow finite glue words to be checked before using them in discriminant groups.

Reference: Conway and Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4 §3
and Chapter 16 §1.
-/

public section

namespace TauCeti.DynkinType

/-- The number of Conway--Sloane glue labels, with zero for non-simply-laced types. -/
@[simp] abbrev glueLabelCount : DynkinType → ℕ
  | A n => n + 1
  | D _ => 4
  | E6 => 3
  | E7 => 2
  | E8 => 1
  | _ => 0

/-- The Conway--Sloane digit labels identify the elements of the component glue alphabet.
For even `Dₙ`, the digits `1`, `2`, `3` denote spinor, vector, cospinor, respectively. -/
def glueLabelEquiv : (t : DynkinType) → (ht : t.IsSimplyLaced) →
    Fin t.glueLabelCount ≃ t.glueAlphabet ht
  | A n, _ => (ZMod.finEquiv (n + 1)).toEquiv
  | D n, ht =>
    if hn : Even n then
      ((finProdFinEquiv (m := 2) (n := 2)).symm.trans
        ((ZMod.finEquiv 2).toEquiv.prodCongr (ZMod.finEquiv 2).toEquiv)).trans
        (Equiv.cast (congrArg (fun A : FiniteQuadraticModule ↦ A.carrier)
          (glueAlphabet_D_of_even n ht hn).symm))
    else
      (ZMod.finEquiv 4).toEquiv.trans
        (Equiv.cast (congrArg (fun A : FiniteQuadraticModule ↦ A.carrier)
          (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn)).symm))
  | E6, _ => (ZMod.finEquiv 3).toEquiv
  | E7, _ => (ZMod.finEquiv 2).toEquiv
  | E8, _ => (ZMod.finEquiv 1).toEquiv
  | B n, h => absurd h (not_isSimplyLaced_B n)
  | C n, h => absurd h (not_isSimplyLaced_C n)
  | F4, h => absurd h not_isSimplyLaced_F4
  | G2, h => absurd h not_isSimplyLaced_G2

/-- In a cyclic type-`A` alphabet the label is its natural-number residue. -/
@[simp] theorem glueLabelEquiv_A (n : ℕ) (ht : (A n).IsSimplyLaced)
    (i : Fin (n + 1)) : (A n).glueLabelEquiv ht i = (i.val : ZMod (n + 1)) := by
  simp only [glueLabelEquiv]
  exact (Fin.cast_val_eq_self i).symm

/-- In even rank, the label is the binary pair with the vector bit first. -/
@[simp] theorem glueLabelEquiv_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Even n)
    (i : Fin 4) :
    FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn)
      ((D n).glueLabelEquiv ht i) =
        (((i.val / 2 : ℕ) : ZMod 2), ((i.val % 2 : ℕ) : ZMod 2)) := by
  simp only [glueLabelEquiv, dite_eq_left hn, Equiv.trans_apply,
    FiniteQuadraticModule.Isometry.ofEq_apply]
  have hx : ((ZMod.finEquiv 2).toEquiv.prodCongr (ZMod.finEquiv 2).toEquiv)
      ((finProdFinEquiv (m := 2) (n := 2)).symm i) =
      (((i.val / 2 : ℕ) : ZMod 2), ((i.val % 2 : ℕ) : ZMod 2)) :=
    Prod.ext (Fin.cast_val_eq_self (i.divNat (m := 2) (n := 2))).symm
      (Fin.cast_val_eq_self (i.modNat (m := 2) (n := 2))).symm
  apply eq_of_heq
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (heq_of_eq hx))

/-- In odd rank, type-`D` labels enumerate the cyclic group of order four. -/
@[simp] theorem glueLabelEquiv_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Odd n)
    (i : Fin 4) :
    FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn)
      ((D n).glueLabelEquiv ht i) = (i.val : ZMod 4) := by
  simp only [glueLabelEquiv, dite_eq_right (Nat.not_even_iff_odd.mpr hn), Equiv.trans_apply,
    FiniteQuadraticModule.Isometry.ofEq_apply]
  apply eq_of_heq
  exact (cast_heq _ _).trans ((cast_heq _ _).trans
    (heq_of_eq (Fin.cast_val_eq_self i).symm))

/-- Exceptional cyclic alphabets use their natural residue labels. -/
@[simp] theorem glueLabelEquiv_E6 (ht : E6.IsSimplyLaced) (i : Fin 3) :
    E6.glueLabelEquiv ht i = (i.val : ZMod 3) := by
  simp only [glueLabelEquiv]
  exact (Fin.cast_val_eq_self i).symm

/-- The two labels of `E₇` are the natural residues modulo two. -/
@[simp] theorem glueLabelEquiv_E7 (ht : E7.IsSimplyLaced) (i : Fin 2) :
    E7.glueLabelEquiv ht i = (i.val : ZMod 2) := by
  simp only [glueLabelEquiv]
  exact (Fin.cast_val_eq_self i).symm

/-- The only label of `E₈` is the zero class. -/
@[simp] theorem glueLabelEquiv_E8 (ht : E8.IsSimplyLaced) (i : Fin 1) :
    E8.glueLabelEquiv ht i = 0 := Subsingleton.elim _ _

/-- Every simply-laced component has at least the zero label. -/
theorem glueLabelCount_pos (t : DynkinType) (ht : t.IsSimplyLaced) :
    0 < t.glueLabelCount := by
  cases t <;> simp_all

/-- The label zero denotes the zero class. -/
@[simp] theorem glueLabelEquiv_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
    t.glueLabelEquiv ht ⟨0, t.glueLabelCount_pos ht⟩ = 0 := by
  cases t with
  | A n => rw [glueLabelEquiv_A]; rfl
  | D n =>
    by_cases hn : Even n
    · apply (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn)).injective
      exact (glueLabelEquiv_D_of_even n ht hn _).trans (by
        rw [map_zero]
        exact Prod.ext (by norm_num; rfl) (by norm_num; rfl))
    · apply (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn))).injective
      exact (glueLabelEquiv_D_of_odd n ht (Nat.not_even_iff_odd.mp hn) _).trans
        (map_zero _).symm
  | E6 => rw [glueLabelEquiv_E6]; rfl
  | E7 => rw [glueLabelEquiv_E7]; rfl
  | E8 => exact glueLabelEquiv_E8 ht _
  | B n => exact (not_isSimplyLaced_B n ht).elim
  | C n => exact (not_isSimplyLaced_C n ht).elim
  | F4 => exact (not_isSimplyLaced_F4 ht).elim
  | G2 => exact (not_isSimplyLaced_G2 ht).elim

end TauCeti.DynkinType

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
-- Carrier-only casts keep the equivalence computable; bundled isometries retain the
-- noncomputable quadratic-module data.
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

/-- In a cyclic type-`A` alphabet the label of a class is its canonical residue. -/
@[simp] theorem glueLabelEquiv_A_symm_apply (n : ℕ) (ht : (A n).IsSimplyLaced)
    (x : ZMod (n + 1)) : ((A n).glueLabelEquiv ht).symm x = ⟨x.val, ZMod.val_lt x⟩ :=
  ((A n).glueLabelEquiv ht).symm_apply_eq.mpr
    ((glueLabelEquiv_A n ht _).trans (ZMod.natCast_zmod_val x)).symm

/-- In even rank, the label is the binary pair with the vector bit first. -/
@[simp] theorem glueLabelEquiv_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Even n)
    (i : Fin 4) :
    FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn)
      ((D n).glueLabelEquiv ht i) =
        (((i.val / 2 : ℕ) : ZMod 2), ((i.val % 2 : ℕ) : ZMod 2)) := by
  simp only [glueLabelEquiv, dite_eq_left hn, Equiv.trans_apply,
    FiniteQuadraticModule.Isometry.ofEq_apply]
  -- The model carrier is semireducible, so cast cancellation needs `erw` transparency.
  erw [Equiv.cast_apply, cast_cast, cast_eq]
  exact Prod.ext (Fin.cast_val_eq_self (i.divNat (m := 2) (n := 2))).symm
    (Fin.cast_val_eq_self (i.modNat (m := 2) (n := 2))).symm

/-- In odd rank, type-`D` labels enumerate the cyclic group of order four. -/
@[simp] theorem glueLabelEquiv_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Odd n)
    (i : Fin 4) :
    FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn)
      ((D n).glueLabelEquiv ht i) = (i.val : ZMod 4) := by
  simp only [glueLabelEquiv, dite_eq_right (Nat.not_even_iff_odd.mpr hn), Equiv.trans_apply,
    FiniteQuadraticModule.Isometry.ofEq_apply]
  -- The model carrier is semireducible, so cast cancellation needs `erw` transparency.
  erw [Equiv.cast_apply, cast_cast, cast_eq]
  exact (Fin.cast_val_eq_self i).symm

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
  | A n => rw [glueLabelEquiv_A]; exact @Nat.cast_zero (ZMod (n + 1)) _
  | D n =>
    by_cases hn : Even n
    · rw [← (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_even n ht hn)).symm_apply_apply
          ((D n).glueLabelEquiv ht ⟨0, (D n).glueLabelCount_pos ht⟩),
        glueLabelEquiv_D_of_even n ht hn]
      simp only [Nat.zero_div, Nat.zero_mod, Nat.cast_zero]
      exact map_zero (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_even n ht hn)).symm
    · rw [← (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn))).symm_apply_apply
          ((D n).glueLabelEquiv ht ⟨0, (D n).glueLabelCount_pos ht⟩),
        glueLabelEquiv_D_of_odd n ht (Nat.not_even_iff_odd.mp hn)]
      simp only [Nat.cast_zero]
      exact map_zero (FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn))).symm
  | E6 => rw [glueLabelEquiv_E6]; exact @Nat.cast_zero (ZMod 3) _
  | E7 => rw [glueLabelEquiv_E7]; exact @Nat.cast_zero (ZMod 2) _
  | E8 => exact glueLabelEquiv_E8 ht _
  | B n => exact (not_isSimplyLaced_B n ht).elim
  | C n => exact (not_isSimplyLaced_C n ht).elim
  | F4 => exact (not_isSimplyLaced_F4 ht).elim
  | G2 => exact (not_isSimplyLaced_G2 ht).elim

-- Specify the concrete finite codomains so simp indexes the inverse rules without the
-- unreduced matcher of `glueLabelCount` in their implicit type arguments.
/-- The inverse type-`A` label is the least natural residue. -/
@[simp] theorem glueLabelEquiv_symm_A (n : ℕ) (ht : (A n).IsSimplyLaced)
    (x : (A n).glueAlphabet ht) :
    let y : ZMod (n + 1) := x
    @Equiv.symm (Fin (n + 1)) ((A n).glueAlphabet ht)
      ((A n).glueLabelEquiv ht) x = ⟨y.val, y.val_lt⟩ := by
  simp only [glueLabelEquiv]
  let y : ZMod (n + 1) := x
  exact (Fin.eta y y.val_lt).symm

/-- In even type `D`, recover the digit from the vector and spinor bits. -/
@[simp] theorem glueLabelEquiv_symm_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced)
    (hn : Even n) (x : (D n).glueAlphabet ht) :
    let y : ZMod 2 × ZMod 2 :=
      FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn) x
    @Equiv.symm (Fin 4) ((D n).glueAlphabet ht) ((D n).glueLabelEquiv ht) x =
      ⟨y.2.val + 2 * y.1.val, by
        have := y.1.val_lt
        have := y.2.val_lt
        omega⟩ := by
  apply Fin.ext
  simp only [glueLabelEquiv, dite_eq_left hn]
  erw [Equiv.symm_trans_apply, Equiv.symm_trans_apply]
  simp only [FiniteQuadraticModule.Isometry.ofEq_apply]
  -- Both casts use the same equality; `finProdFinEquiv` computes the displayed digit.
  rfl

/-- In odd type `D`, the inverse label is the least residue in the cyclic model. -/
@[simp] theorem glueLabelEquiv_symm_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced)
    (hn : Odd n) (x : (D n).glueAlphabet ht) :
    let y : ZMod 4 := FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn) x
    @Equiv.symm (Fin 4) ((D n).glueAlphabet ht)
      ((D n).glueLabelEquiv ht) x = ⟨y.val, y.val_lt⟩ := by
  apply Fin.ext
  simp only [glueLabelEquiv, dite_eq_right (Nat.not_even_iff_odd.mpr hn)]
  erw [Equiv.symm_trans_apply]
  simp only [FiniteQuadraticModule.Isometry.ofEq_apply]
  -- Both casts use the same equality, and the cyclic label is the residue itself.
  rfl

/-- The inverse `E₆` label is the least residue modulo three. -/
@[simp] theorem glueLabelEquiv_symm_E6 (ht : E6.IsSimplyLaced) (x : E6.glueAlphabet ht) :
    let y : ZMod 3 := x
    @Equiv.symm (Fin 3) (E6.glueAlphabet ht)
      (E6.glueLabelEquiv ht) x = ⟨y.val, y.val_lt⟩ := by
  simp only [glueLabelEquiv]
  let y : ZMod 3 := x
  exact (Fin.eta y y.val_lt).symm

/-- The inverse `E₇` label is the least residue modulo two. -/
@[simp] theorem glueLabelEquiv_symm_E7 (ht : E7.IsSimplyLaced) (x : E7.glueAlphabet ht) :
    let y : ZMod 2 := x
    @Equiv.symm (Fin 2) (E7.glueAlphabet ht)
      (E7.glueLabelEquiv ht) x = ⟨y.val, y.val_lt⟩ := by
  simp only [glueLabelEquiv]
  let y : ZMod 2 := x
  exact (Fin.eta y y.val_lt).symm

/-- The only inverse label for `E₈` is zero. -/
@[simp] theorem glueLabelEquiv_symm_E8 (ht : E8.IsSimplyLaced) (x : E8.glueAlphabet ht) :
    (E8.glueLabelEquiv ht).symm x = ⟨0, E8.glueLabelCount_pos ht⟩ :=
  Subsingleton.elim _ _

/-- The zero class has label zero in every simply-laced component. -/
@[simp] theorem glueLabelEquiv_symm_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
    (t.glueLabelEquiv ht).symm 0 = ⟨0, t.glueLabelCount_pos ht⟩ := by
  apply (t.glueLabelEquiv ht).symm_apply_eq.mpr
  exact (glueLabelEquiv_zero t ht).symm

end TauCeti.DynkinType

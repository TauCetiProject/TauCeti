/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Glued
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.Dual

/-!
# Explicit dual-lattice representatives of glue labels and glue words

A Conway--Sloane glue label `a` of a valid simply-laced Dynkin type `t` names a discriminant class
in `A_Q = Q^∨ / Q` for the root lattice `Q = t.rootLattice ht`, via `t.glueLabelEquiv` and
`t.glueAlphabetIsometry`.  `TauCeti.DynkinType.isLeast_glueMinimum` establishes that the least norm
`μ_t(a)` of a dual vector in that coset is attained, and
`TauCeti.DynkinType.isLeast_sum_glueMinimum` lifts attainment to glue words across an orthogonal
sum of ADE root lattices.

This file constructs canonical, computable rational simple-root coordinate representatives for every
glue label and every glue word, in Bourbaki numbering on `Fin t.rank → ℚ`:

* For `Aₙ`, label `a` (`0 ≤ a ≤ n`) is represented by the vector whose `j`-th simple-root coordinate
  is `min (j + 1) a - (j + 1) a / (n + 1)`.  Under `typeAIsometryZeroSumLattice`, its classical
  zero-sum coordinates in `ℚ^{n+1}` have `1 - a / (n + 1)` in the first `a` positions and
  `-a / (n + 1)` in the remaining `n + 1 - a` positions; at `a = 1` it is the first fundamental
  weight `ω₁`.
* For `Dₙ` (`4 ≤ n`), labels `1`, `2`, `3` are represented by the simple-root coordinate vectors of
  the Conway--Sloane checkerboard spinor `s = (1/2, …, 1/2)`, vector `v = (0, …, 0, 1)` and cospinor
  `c = (1/2, …, 1/2, -1/2)` under `rootLatticeIsometryCheckerboard`, namely the fundamental weight
  `ϖₙ`, the weight in the vector coset of `eₙ`, and the fundamental weight `ϖₙ₋₁`.
* For `E₆`, labels `1` and `2` are the minuscule weights `ϖ₁` and `-ϖ₁`.
* For `E₇`, label `1` is the minuscule weight `ϖ₇`.
* Label `0` in every type (and the sole label of `E₈`) is `0`.

Each representative is proved to lie in the dual lattice `Q^∨`, to project under
`Submodule.Quotient.mk` to the discriminant class named by its label, to attain the coset minimum
norm `μ_t(a)`, and to realize the polar bilinear pairing on `t.glueAlphabet ht` as the rational
ambient pairing reduced modulo `ℤ`.

Assembling the component representatives coordinatewise gives the computable representative
`TauCeti.DynkinType.glueWordVector` of a glue word `w` in `∀ i, Fin (t i).rank → ℚ`.  It lies in
the dual of the orthogonal sum of root lattices, represents `glueWordIsometry t ht hv w`, attains
the word minimum `∑ i, μ_(t i)(w_i)`, and supplies explicit coset decompositions and generator spans
for every glued lattice `TauCeti.DynkinType.gluedLattice`.

## Main declarations

* `TauCeti.DynkinType.glueLabelVector`: the computable simple-root coordinate vector of a printed
  Conway--Sloane label `a : ℕ`.
* `TauCeti.DynkinType.typeAIsometryZeroSumLattice_glueLabelVector_apply`,
  `TauCeti.DynkinType.typeARootLattice_form_glueLabelVector_self`,
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_one`,
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_two`,
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_three`: images and
  self-pairing of the `Aₙ` and `Dₙ` label representatives in the classical zero-sum and checkerboard
  models.
* `TauCeti.DynkinType.glueVector`, `TauCeti.DynkinType.glueDualVector`: the representative of an
  element of `t.glueAlphabet ht` in the ambient space and in `(t.rootLattice ht).dualCarrier`.
* `TauCeti.DynkinType.mk_glueVector`, `TauCeti.DynkinType.mk_glueDualVector`,
  `TauCeti.DynkinType.rootLattice_form_glueVector_self`,
  `TauCeti.DynkinType.pairing_glueAlphabet_eq_form_glueVector`: each representative lies in the
  expected discriminant coset, attains `glueMinimum`, and computes the polar pairing modulo `ℤ`.
* `TauCeti.DynkinType.glueWordVector`, `TauCeti.DynkinType.glueWordDualVector`: the coordinatewise
  representative of a glue word across a family of simply-laced components.
* `TauCeti.DynkinType.mk_glueWordVector`, `TauCeti.DynkinType.mk_glueWordDualVector`,
  `TauCeti.DynkinType.pi_rootLattice_form_glueWordVector_self`,
  `TauCeti.DynkinType.pairing_pi_glueAlphabet_eq_form_glueWordVector`: coset class, norm attainment,
  and polar pairing for glue words.
* `TauCeti.DynkinType.mem_gluedLattice_carrier_iff_exists`,
  `TauCeti.DynkinType.gluedLattice_carrier_eq_sup_span_glueWordVector`: explicit coset decomposition
  and generator span of `gluedLattice`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I--VII.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Chapter 4,
  §§3, 6--8, and Chapter 16, §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice Finset

/-! ## Simple-root coordinate representatives of printed labels -/

/-- **The canonical simple-root coordinate vector of a Conway--Sloane glue label** `a : ℕ` on
`Fin t.rank → ℚ`, in Bourbaki numbering.

For `Aₙ`, label `a` has `j`-th coordinate `min (j + 1) a - (j + 1) a / (n + 1)`.  For `Dₙ`, labels
`1`, `2`, `3` are the simple-root coordinates of the checkerboard spinor, vector and cospinor
representatives.  For `E₆` and `E₇`, the nonzero labels are `±ϖ₁` and `ϖ₇`.  Label `0`, `E₈`,
out-of-range labels of `D` and `E`, and non-simply-laced types evaluate to `0`. -/
@[expose] def glueLabelVector : (t : DynkinType) → ℕ → Fin t.rank → ℚ
  | A n, a => fun j ↦ ((min (j.val + 1) a : ℕ) : ℚ) - ((j.val + 1 : ℕ) * a : ℚ) / (n + 1)
  | D n, 1 => fun j ↦
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then ((n : ℚ) - 2) / 4
      else (n : ℚ) / 4
  | D n, 2 => fun j ↦
      if j.val + 2 = n then -(1 / 2)
      else if j.val + 1 = n then 1 / 2
      else 0
  | D n, 3 => fun j ↦
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then (n : ℚ) / 4
      else ((n : ℚ) - 2) / 4
  | E6, 1 => fun j ↦ match j.val with
      | 0 => 4 / 3 | 1 => 1 | 2 => 5 / 3 | 3 => 2 | 4 => 4 / 3 | _ => 2 / 3
  | E6, 2 => fun j ↦ match j.val with
      | 0 => -(4 / 3) | 1 => -1 | 2 => -(5 / 3) | 3 => -2 | 4 => -(4 / 3) | _ => -(2 / 3)
  | E7, 1 => fun j ↦ match j.val with
      | 0 => 1 | 1 => 3 / 2 | 2 => 2 | 3 => 3 | 4 => 5 / 2 | 5 => 2 | _ => 3 / 2
  | _, _ => 0

/-- The `j`-th simple-root coordinate of label `a` of `Aₙ`. -/
@[simp] theorem glueLabelVector_A_apply (n a : ℕ) (j : Fin n) :
    (A n).glueLabelVector a j =
      ((min (j.val + 1) a : ℕ) : ℚ) - ((j.val + 1 : ℕ) * a : ℚ) / (n + 1) := (rfl)

/-- The `j`-th simple-root coordinate of the spinor label `1` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_one_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 1 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then ((n : ℚ) - 2) / 4 else (n : ℚ) / 4 := (rfl)

/-- The `j`-th simple-root coordinate of the vector label `2` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_two_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 2 j =
      if j.val + 2 = n then -(1 / 2) else if j.val + 1 = n then 1 / 2 else 0 := (rfl)

/-- The `j`-th simple-root coordinate of the cospinor label `3` of `Dₙ`. -/
@[simp] theorem glueLabelVector_D_three_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 3 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then (n : ℚ) / 4 else ((n : ℚ) - 2) / 4 := (rfl)

/-- The `j`-th simple-root coordinate of label `1` (`ϖ₁`) of `E₆`. -/
@[simp] theorem glueLabelVector_E6_one_apply (j : Fin 6) :
    E6.glueLabelVector 1 j = ((![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) j : ℚ) / 3 := by
  fin_cases j <;> norm_num [glueLabelVector]

/-- The `j`-th simple-root coordinate of label `2` (`-ϖ₁`) of `E₆`. -/
@[simp] theorem glueLabelVector_E6_two_apply (j : Fin 6) :
    E6.glueLabelVector 2 j = -(((![4, 3, 5, 6, 4, 2] : Fin 6 → ℤ) j : ℚ) / 3) := by
  fin_cases j <;> norm_num [glueLabelVector]

/-- The `j`-th simple-root coordinate of label `1` (`ϖ₇`) of `E₇`. -/
@[simp] theorem glueLabelVector_E7_one_apply (j : Fin 7) :
    E7.glueLabelVector 1 j = ((![2, 3, 4, 6, 5, 4, 3] : Fin 7 → ℤ) j : ℚ) / 2 := by
  fin_cases j <;> norm_num [glueLabelVector]

/-- Label `1` of `E₆` is the minuscule weight `ϖ₁`. -/
theorem glueLabelVector_E6_one : (E6.glueLabelVector 1 : Fin 6 → ℚ) = typeE₆MinusculeWeight :=
  funext fun j ↦ (glueLabelVector_E6_one_apply j).trans (typeE₆MinusculeWeight_apply j).symm

/-- Label `2` of `E₆` is `-ϖ₁`. -/
theorem glueLabelVector_E6_two : (E6.glueLabelVector 2 : Fin 6 → ℚ) = -typeE₆MinusculeWeight :=
  funext fun j ↦ (glueLabelVector_E6_two_apply j).trans
    (congrArg Neg.neg (typeE₆MinusculeWeight_apply j).symm)

/-- Label `1` of `E₇` is the minuscule weight `ϖ₇`. -/
theorem glueLabelVector_E7_one : (E7.glueLabelVector 1 : Fin 7 → ℚ) = typeE₇MinusculeWeight :=
  funext fun j ↦ (glueLabelVector_E7_one_apply j).trans (typeE₇MinusculeWeight_apply j).symm

/-- Out-of-range labels `4 ≤ a` of `Dₙ` evaluate to `0`. -/
@[simp] theorem glueLabelVector_D_of_ge (n : ℕ) {a : ℕ} (ha : 4 ≤ a) :
    (D n).glueLabelVector a = 0 := by
  match a with | 0 | 1 | 2 | 3 => omega | _ + 4 => rfl

/-- Out-of-range labels `3 ≤ a` of `E₆` evaluate to `0`. -/
@[simp] theorem glueLabelVector_E6_of_ge {a : ℕ} (ha : 3 ≤ a) : E6.glueLabelVector a = 0 := by
  match a with | 0 | 1 | 2 => omega | _ + 3 => rfl

/-- Out-of-range labels `2 ≤ a` of `E₇` evaluate to `0`. -/
@[simp] theorem glueLabelVector_E7_of_ge {a : ℕ} (ha : 2 ≤ a) : E7.glueLabelVector a = 0 := by
  match a with | 0 | 1 => omega | _ + 2 => rfl

/-- Every label of `E₈` has representative `0`. -/
@[simp] theorem glueLabelVector_E8 (a : ℕ) : E8.glueLabelVector a = 0 := (rfl)

/-- Every label of `Bₙ` evaluates to `0`. -/
@[simp] theorem glueLabelVector_B (n a : ℕ) : (B n).glueLabelVector a = 0 := (rfl)

/-- Every label of `Cₙ` evaluates to `0`. -/
@[simp] theorem glueLabelVector_C (n a : ℕ) : (C n).glueLabelVector a = 0 := (rfl)

/-- Every label of `F₄` evaluates to `0`. -/
@[simp] theorem glueLabelVector_F4 (a : ℕ) : F4.glueLabelVector a = 0 := (rfl)

/-- Every label of `G₂` evaluates to `0`. -/
@[simp] theorem glueLabelVector_G2 (a : ℕ) : G2.glueLabelVector a = 0 := (rfl)

/-- **The zero label is represented by the zero vector in every Dynkin type.** -/
@[simp] theorem glueLabelVector_zero (t : DynkinType) : t.glueLabelVector 0 = 0 := by
  cases t with
  | A n =>
    refine funext fun (j : Fin n) ↦ ?_
    rw [glueLabelVector_A_apply]
    simp only [Nat.min_zero, CharP.cast_eq_zero, mul_zero, zero_div, sub_self]
    rfl
  | D _ | E6 | E7 | E8 | B _ | C _ | F4 | G2 => rfl

/-- Label `1` of `Aₙ` is the first fundamental weight `ω₁`. -/
theorem glueLabelVector_A_one (n : ℕ) :
    ((A n).glueLabelVector 1 : Fin n → ℚ) = typeAFundamentalWeight n := by
  refine funext fun (j : Fin n) ↦ ?_
  have hmin : min (j.val + 1) 1 = 1 := Nat.min_eq_right (Nat.succ_le_succ (Nat.zero_le _))
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [glueLabelVector_A_apply, hmin, typeAFundamentalWeight_apply]
  push_cast; field_simp; ring

/-- Label `n + 1` of `Aₙ` evaluates to the zero vector. -/
theorem glueLabelVector_A_succ (n : ℕ) : ((A n).glueLabelVector (n + 1) : Fin n → ℚ) = 0 := by
  refine funext fun (j : Fin n) ↦ ?_
  have hj : j.val < n := j.isLt
  have hmin : min (j.val + 1) (n + 1) = j.val + 1 := Nat.min_eq_left (by omega)
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hlhs : (A n).glueLabelVector (n + 1) j = 0 := by
    rw [glueLabelVector_A_apply, hmin]; push_cast; field_simp; ring
  exact hlhs.trans rfl

/-- In type `Dₙ`, the cospinor representative is the spinor representative minus the vector
representative at every rank. -/
theorem glueLabelVector_D_three_eq_sub (n : ℕ) :
    (D n).glueLabelVector 3 = (D n).glueLabelVector 1 - (D n).glueLabelVector 2 := by
  refine funext fun (j : Fin n) ↦ ?_
  have hj : j.val < n := j.isLt
  have hsub : ((D n).glueLabelVector 1 - (D n).glueLabelVector 2) j =
      (D n).glueLabelVector 1 j - (D n).glueLabelVector 2 j := rfl
  rw [hsub, glueLabelVector_D_three_apply, glueLabelVector_D_one_apply, glueLabelVector_D_two_apply]
  by_cases h2 : j.val + 2 < n
  · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
  · by_cases heq2 : j.val + 2 = n
    · rw [ite_eq_right h2, ite_eq_left heq2, ite_eq_right h2, ite_eq_left heq2, ite_eq_left heq2]
      ring
    · rw [ite_eq_right h2, ite_eq_right heq2, ite_eq_right h2, ite_eq_right heq2,
        ite_eq_right heq2, ite_eq_left (by omega)]
      ring

/-- Transporting along an equality of simply-laced Dynkin types preserves `glueLabelVector`. -/
theorem rootLatticeIsometryOfEq_glueLabelVector {t s : DynkinType} (ht : t.IsSimplyLaced)
    (h : t = s) (hs : s.IsSimplyLaced) (a : ℕ) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueLabelVector a) = s.glueLabelVector a := by
  subst h; rw [rootLatticeIsometryOfEq_rfl, Isometry.refl_apply]

/-! ## Classical coordinate images for `Aₙ` and `Dₙ` -/

/-- **Classical zero-sum coordinates of the `Aₙ` label representative**: for `0 ≤ a ≤ n + 1`,
`typeAIsometryZeroSumLattice` carries `(A n).glueLabelVector a` to the vector in `ℚ^{n+1}` with
`1 - a / (n + 1)` in the first `a` positions and `-a / (n + 1)` in the remaining positions. -/
theorem typeAIsometryZeroSumLattice_glueLabelVector_apply (n : ℕ) {a : ℕ} (ha : a ≤ n + 1)
    (r : Fin (n + 1)) :
    (typeAIsometryZeroSumLattice n ((A n).glueLabelVector a) : Fin (n + 1) → ℚ) r =
      (if r.val < a then 1 else 0) - (a : ℚ) / (n + 1) := by
  let v : Fin n → ℚ := (A n).glueLabelVector a
  set w : Fin (n + 1) → ℚ := fun r ↦ (if r.val < a then 1 else 0) - (a : ℚ) / (n + 1)
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hw : w ∈ singleParityCheckCode ℚ (Fin (n + 1)) := by
    rw [mem_singleParityCheckCode]
    simp only [w, sum_sub_distrib, sum_boole, Fin.card_filter_val_lt, min_eq_right ha, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have key : (typeAIsometryZeroSumLattice n v : Fin (n + 1) → ℚ) = w := by
    rw [← sum_smul_zeroSumSimpleRoot n hw]
    conv_lhs =>
      rw [← sum_smul_typeASimpleRoot v, map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul,
      typeAIsometryZeroSumLattice_typeASimpleRoot]
    refine sum_congr rfl fun k _ ↦ congrArg (· • zeroSumSimpleRoot n k) ?_
    have hk : k.val < n := k.isLt
    have hfilter :
        (Iic k.castSucc).filter (fun j ↦ j.val < a) =
          univ.filter (fun j : Fin (n + 1) ↦ j.val < min (k.val + 1) a) := by
      ext j
      simp only [mem_filter, mem_Iic, mem_univ, true_and, Fin.le_def, Fin.val_castSucc,
        Nat.lt_min]
      omega
    have hmin_le : min (k.val + 1) a ≤ n + 1 :=
      (Nat.min_le_left _ _).trans (by omega)
    simp only [w, v, sum_sub_distrib, sum_boole, hfilter, Fin.card_filter_val_lt,
      min_eq_right hmin_le, sum_const, Fin.card_Iic, Fin.val_castSucc, nsmul_eq_mul,
      glueLabelVector_A_apply]
    push_cast
    ring
  exact congrFun key r

/-- For `0 ≤ a ≤ n + 1`, the `Aₙ` representative lies in the dual of `typeARootLattice n`. -/
theorem glueLabelVector_A_mem_dualCarrier (n : ℕ) {a : ℕ} (ha : a ≤ n + 1) :
    ((A n).glueLabelVector a : Fin n → ℚ) ∈ (typeARootLattice n).dualCarrier := by
  refine (mem_dualCarrier_typeARootLattice_iff (n := n)
    ((A n).glueLabelVector a)).mpr fun i j ↦ ?_
  refine ⟨(if i.val < a then 1 else 0) - if j.val < a then 1 else 0, ?_⟩
  simp only [typeAIsometryZeroSumLattice_glueLabelVector_apply n ha, Int.cast_sub, Int.cast_ite,
    Int.cast_one, Int.cast_zero]
  ring

/-- For `0 ≤ a ≤ n + 1`, the `Aₙ` representative has squared norm `a (n + 1 - a) / (n + 1)` in
`typeARootLattice n`. -/
theorem typeARootLattice_form_glueLabelVector_self (n : ℕ) {a : ℕ} (ha : a ≤ n + 1) :
    (typeARootLattice n).form ((A n).glueLabelVector a) ((A n).glueLabelVector a) =
      (a : ℚ) * (n + 1 - a) / (n + 1) := by
  let v : Fin n → ℚ := (A n).glueLabelVector a
  refine (typeARootLattice_form_self_eq_dotProduct v).trans ?_
  set e := typeAIsometryZeroSumLattice n
  have hsum := (mem_singleParityCheckCode ℚ (Fin (n + 1))).mp (e v).2
  have hcoord := typeAIsometryZeroSumLattice_glueLabelVector_apply n ha
  exact (dotProduct_self_eq_mul_sub_div_iff (k := a) hsum fun r ↦
    ⟨if r.val < a then 1 else 0, by simp [e, v, hcoord r]⟩).mpr fun r ↦ by
    by_cases hr : r.val < a <;> simp [e, v, hcoord r, hr]

/-- **In type `Dₙ` (`4 ≤ n`), label `1` maps to the Conway--Sloane checkerboard spinor
representative `s = (1/2, …, 1/2)`.** -/
theorem rootLatticeIsometryCheckerboard_glueLabelVector_one (n : ℕ) (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    rootLatticeIsometryCheckerboard n hn ht ((D n).glueLabelVector 1) =
      checkerboardSpinor n := by
  refine rootLatticeIsometryCheckerboard_eq_of_repr n hn ht fun k ↦ ?_
  rw [glueLabelVector_D_one_apply, typeDSimpleRootBasis_repr_apply]
  by_cases hk2 : k.val + 2 < n
  · rw [ite_eq_left hk2, ite_eq_left hk2]
    simp only [checkerboardSpinor_apply, sum_const, Fin.card_Iic, nsmul_eq_mul]
    push_cast
    ring
  · by_cases hk1 : k.val + 1 < n
    · have heq2 : k.val + 2 = n := by omega
      rw [ite_eq_right hk2, ite_eq_left heq2, ite_eq_right hk2, ite_eq_left hk1,
        sum_checkerboardSpinor, checkerboardSpinor_apply, invOf_eq_inv]
      ring
    · have hne2 : k.val + 2 ≠ n := by omega
      rw [ite_eq_right hk2, ite_eq_right hne2, ite_eq_right hk2, ite_eq_right hk1,
        sum_checkerboardSpinor, invOf_eq_inv]
      ring

/-- **In type `Dₙ` (`4 ≤ n`), label `2` maps to the Conway--Sloane checkerboard vector
representative `v = eₙ`.** -/
theorem rootLatticeIsometryCheckerboard_glueLabelVector_two (n : ℕ) [NeZero n] (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    rootLatticeIsometryCheckerboard n hn ht ((D n).glueLabelVector 2) =
      checkerboardVector n := by
  refine rootLatticeIsometryCheckerboard_eq_of_repr n hn ht fun k ↦ ?_
  have hlast : (⟨n - 1, by omega⟩ : Fin n) = ⊤ := Fin.ext (Fin.val_top n).symm
  rw [glueLabelVector_D_two_apply, typeDSimpleRootBasis_repr_apply]
  by_cases hk2 : k.val + 2 < n
  · have hne2 : k.val + 2 ≠ n := by omega
    have hne1 : k.val + 1 ≠ n := by omega
    rw [ite_eq_right hne2, ite_eq_right hne1, ite_eq_left hk2]
    symm
    refine sum_eq_zero fun j hj ↦ ?_
    rw [mem_Iic] at hj
    have hjtop : j ≠ ⊤ := by
      intro htop
      have htop_val : j.val = n - 1 := htop ▸ Fin.val_top n
      have : j.val ≤ k.val := hj
      omega
    simp [checkerboardVector_apply, hjtop]
  · by_cases hk1 : k.val + 1 < n
    · have heq2 : k.val + 2 = n := by omega
      rw [ite_eq_left heq2, ite_eq_right hk2, ite_eq_left hk1, sum_checkerboardVector, hlast,
        checkerboardVector_top, invOf_eq_inv]
      norm_num
    · have hne2 : k.val + 2 ≠ n := by omega
      have heq1 : k.val + 1 = n := by omega
      rw [ite_eq_right hne2, ite_eq_left heq1, ite_eq_right hk2, ite_eq_right hk1,
        sum_checkerboardVector, invOf_eq_inv]
      norm_num

/-- **In type `Dₙ` (`4 ≤ n`), label `3` maps to the Conway--Sloane checkerboard cospinor
representative `c = s - eₙ`.** -/
theorem rootLatticeIsometryCheckerboard_glueLabelVector_three (n : ℕ) [NeZero n] (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    rootLatticeIsometryCheckerboard n hn ht ((D n).glueLabelVector 3) =
      checkerboardCospinor n := by
  rw [glueLabelVector_D_three_eq_sub, map_sub,
    rootLatticeIsometryCheckerboard_glueLabelVector_one n hn ht,
    rootLatticeIsometryCheckerboard_glueLabelVector_two n hn ht]
  ext j
  simp

/-! ## Representatives of elements of the glue alphabet -/

/-- **The canonical ambient representative of a glue-alphabet class**, obtained by reading its
Conway--Sloane label via `glueLabelEquiv` and evaluating `glueLabelVector`.  Because
`glueLabelEquiv` and `glueLabelVector` are computable, `glueVector` is computable as well. -/
def glueVector (t : DynkinType) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) : Fin t.rank → ℚ :=
  t.glueLabelVector ((t.glueLabelEquiv ht).symm x).val

/-- Expanding `glueVector` in terms of `glueLabelVector` and `glueLabelEquiv`. -/
theorem glueVector_def (t : DynkinType) (ht : t.IsSimplyLaced) (x : t.glueAlphabet ht) :
    t.glueVector ht x = t.glueLabelVector ((t.glueLabelEquiv ht).symm x).val :=
  (rfl)

/-- Evaluating `glueVector` on the class of a bounded label `a` returns `t.glueLabelVector a`. -/
@[simp] theorem glueVector_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : Fin t.glueLabelCount) :
    t.glueVector ht (t.glueLabelEquiv ht a) = t.glueLabelVector a.val := by
  rw [glueVector_def, Equiv.symm_apply_apply]

/-- **The zero class in the glue alphabet is represented by `0`.** -/
@[simp] theorem glueVector_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
    t.glueVector ht 0 = 0 := by
  rw [glueVector_def, glueLabelEquiv_symm_zero, glueLabelVector_zero]

/-- **Naturality of `glueVector` along equal Dynkin types.** -/
theorem rootLatticeIsometryOfEq_glueVector {t s : DynkinType} (ht : t.IsSimplyLaced) (h : t = s)
    (hs : s.IsSimplyLaced) (x : t.glueAlphabet ht) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueVector ht x) =
      s.glueVector hs (FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_congr h ht hs) x) := by
  rw [glueVector_def, glueVector_def, val_glueLabelEquiv_symm_ofEq h ht hs x,
    rootLatticeIsometryOfEq_glueLabelVector]

/-! ## Dual-lattice membership, discriminant classes, norms, and polar pairing -/

/-- **Every valid Conway--Sloane label representative lies in the dual of the root lattice.** -/
theorem glueLabelVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    {a : ℕ} (ha : a < t.glueLabelCount) :
    t.glueLabelVector a ∈ (t.rootLattice ht).dualCarrier := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [glueLabelVector_zero]
    exact zero_mem _
  cases t with
  | A n =>
    have ha' : a ≤ n + 1 := by simp only [glueLabelCount] at ha; omega
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_A n ht)).symm ▸
      glueLabelVector_A_mem_dualCarrier n ha'
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    have : NeZero n := ⟨by omega⟩
    rw [← (rootLatticeIsometryCheckerboard n hn4 ht).apply_mem_dualCarrier_iff]
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_one n hn4 ht]
      exact checkerboardSpinor_mem_dualCarrier
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_two n hn4 ht]
      exact checkerboardVector_mem_dualCarrier
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_three n hn4 ht]
      exact checkerboardCospinor_mem_dualCarrier
  | E6 =>
    have hmem : (E6.glueLabelVector a : Fin 6 → ℚ) ∈ typeE₆RootLattice.dualCarrier := by
      simp only [glueLabelCount] at ha
      interval_cases a
      · rw [glueLabelVector_E6_one]
        exact typeE₆MinusculeWeight_mem_dualCarrier
      · rw [glueLabelVector_E6_two]
        exact neg_mem typeE₆MinusculeWeight_mem_dualCarrier
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_E6 ht)).symm ▸ hmem
  | E7 =>
    obtain rfl : a = 1 := by simp only [glueLabelCount] at ha; omega
    have hmem : (E7.glueLabelVector 1 : Fin 7 → ℚ) ∈ typeE₇RootLattice.dualCarrier := by
      rw [glueLabelVector_E7_one]
      exact typeE₇MinusculeWeight_mem_dualCarrier
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_E7 ht)).symm ▸ hmem
  | E8 => simp only [glueLabelCount] at ha; omega
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **The representative of every glue-alphabet class lies in the dual of the root lattice.** -/
theorem glueVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    t.glueVector ht x ∈ (t.rootLattice ht).dualCarrier := by
  rw [glueVector_def]
  exact t.glueLabelVector_mem_dualCarrier hv ht ((t.glueLabelEquiv ht).symm x).isLt

/-- **The canonical dual-lattice representative of a glue-alphabet class**, bundling `glueVector`
into `(t.rootLattice ht).dualCarrier`. -/
noncomputable def glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) : (t.rootLattice ht).dualCarrier :=
  ⟨t.glueVector ht x, t.glueVector_mem_dualCarrier hv ht x⟩

/-- Coercing `glueDualVector` to the ambient space recovers `glueVector`. -/
@[simp] theorem coe_glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    (t.glueDualVector hv ht x : Fin t.rank → ℚ) = t.glueVector ht x :=
  (rfl)

/-- The dual representative of the zero glue label is `0`. -/
@[simp] theorem glueDualVector_zero (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    t.glueDualVector hv ht 0 = 0 :=
  Subtype.ext (by rw [coe_glueDualVector, Submodule.coe_zero, glueVector_zero])

/-- Regardless of parity, `rootLatticeIsometryCheckerboard` maps the class of label `1` of `Dₙ` to
`checkerboardSpinorClass n`. -/
private theorem discriminantGroupEquiv_mk_glueLabelVector_D_one (n : ℕ) (hv : (D n).Valid)
    (ht : (D n).IsSimplyLaced) (h1 : 1 < (D n).glueLabelCount) :
    (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).discriminantGroupEquiv
        (Submodule.Quotient.mk ⟨(D n).glueLabelVector 1,
          (D n).glueLabelVector_mem_dualCarrier hv ht h1⟩) =
      checkerboardSpinorClass n := by
  rw [Isometry.discriminantGroupEquiv_mk, mk_eq_checkerboardSpinorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply,
    rootLatticeIsometryCheckerboard_glueLabelVector_one n (valid_D.mp hv) ht, sub_self]
  exact zero_mem _

/-- Regardless of parity, `rootLatticeIsometryCheckerboard` maps the class of label `2` of `Dₙ` to
`checkerboardVectorClass n`. -/
private theorem discriminantGroupEquiv_mk_glueLabelVector_D_two (n : ℕ) [NeZero n]
    (hv : (D n).Valid) (ht : (D n).IsSimplyLaced) (h2 : 2 < (D n).glueLabelCount) :
    (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).discriminantGroupEquiv
        (Submodule.Quotient.mk ⟨(D n).glueLabelVector 2,
          (D n).glueLabelVector_mem_dualCarrier hv ht h2⟩) =
      checkerboardVectorClass n := by
  rw [Isometry.discriminantGroupEquiv_mk, mk_eq_checkerboardVectorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply,
    rootLatticeIsometryCheckerboard_glueLabelVector_two n (valid_D.mp hv) ht, sub_self]
  exact zero_mem _

/-- Regardless of parity, `rootLatticeIsometryCheckerboard` maps the class of label `3` of `Dₙ` to
`checkerboardCospinorClass n`. -/
private theorem discriminantGroupEquiv_mk_glueLabelVector_D_three (n : ℕ) [NeZero n]
    (hv : (D n).Valid) (ht : (D n).IsSimplyLaced) (h3 : 3 < (D n).glueLabelCount) :
    (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).discriminantGroupEquiv
        (Submodule.Quotient.mk ⟨(D n).glueLabelVector 3,
          (D n).glueLabelVector_mem_dualCarrier hv ht h3⟩) =
      checkerboardCospinorClass n := by
  rw [Isometry.discriminantGroupEquiv_mk, mk_eq_checkerboardCospinorClass_iff,
    Isometry.coe_dualCarrierEquiv_apply,
    rootLatticeIsometryCheckerboard_glueLabelVector_three n (valid_D.mp hv) ht, sub_self]
  exact zero_mem _

/-- Helper: in `Dₙ`, the quotient class of `glueLabelVector a` for a positive label `a` matches
`glueAlphabetIsometry` on `glueLabelEquiv ht a`. -/
private theorem mk_glueLabelVector_D (n : ℕ) (hv : (D n).Valid) (ht : (D n).IsSimplyLaced)
    (a : Fin 4) (hapos : 0 < a.val) :
    Submodule.Quotient.mk ⟨(D n).glueLabelVector a.val,
        (D n).glueLabelVector_mem_dualCarrier hv ht a.isLt⟩ =
      (D n).glueAlphabetIsometry hv ht ((D n).glueLabelEquiv ht a) := by
  have hn4 : 4 ≤ n := valid_D.mp hv
  have : NeZero n := ⟨by omega⟩
  obtain ⟨k, hk⟩ := a
  dsimp only at hapos
  apply (rootLatticeIsometryCheckerboard n hn4 ht).discriminantGroupEquiv.injective
  rcases Nat.even_or_odd n with hpar | hpar
  · rw [glueAlphabetIsometry_D_apply_of_even n hv ht hpar, Isometry.discriminantGroupEquiv_symm,
      LinearEquiv.apply_symm_apply, glueLabelEquiv_D_of_even n ht hpar]
    dsimp only
    interval_cases k
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_one n hv ht hk).trans <|
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one n hpar).symm.trans
          (congrArg _ (by decide))
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_two n hv ht hk).trans <|
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero n hpar).symm.trans
          (congrArg _ (by decide))
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_three n hv ht hk).trans <|
        (zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one n hpar).symm.trans
          (congrArg _ (by decide))
  · rw [glueAlphabetIsometry_D_apply_of_odd n hv ht hpar, Isometry.discriminantGroupEquiv_symm,
      LinearEquiv.apply_symm_apply, glueLabelEquiv_D_of_odd n ht hpar]
    dsimp only
    interval_cases k
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_one n hv ht hk).trans
        (zmodFourAddEquivCheckerboardDiscriminantGroup_apply_one n hpar).symm
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_two n hv ht hk).trans
        (zmodFourAddEquivCheckerboardDiscriminantGroup_apply_two n hpar).symm
    · exact (discriminantGroupEquiv_mk_glueLabelVector_D_three n hv ht hk).trans
        (zmodFourAddEquivCheckerboardDiscriminantGroup_apply_three n hpar).symm

/-- **The representative of a bounded printed label projects to the discriminant class named by
that label.** -/
theorem mk_glueLabelVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : Fin t.glueLabelCount) :
    Submodule.Quotient.mk ⟨t.glueLabelVector a.val,
        t.glueLabelVector_mem_dualCarrier hv ht a.isLt⟩ =
      t.glueAlphabetIsometry hv ht (t.glueLabelEquiv ht a) := by
  rcases eq_or_ne a ⟨0, t.glueLabelCount_pos ht⟩ with rfl | hne
  · rw [glueLabelEquiv_zero, map_zero]
    exact (discriminantGroup_mk_eq_zero_iff _ _).mpr (by simp [glueLabelVector_zero])
  have hapos : 0 < a.val := Nat.pos_of_ne_zero fun h0 ↦ hne (Fin.ext h0)
  cases t with
  | A n =>
    refine Eq.trans ?_ (glueAlphabetIsometry_A_apply n hv ht ((A n).glueLabelEquiv ht a)).symm
    have hmk : (Submodule.Quotient.mk
        ⟨(A n).glueLabelVector a.val, glueLabelVector_A_mem_dualCarrier n a.isLt.le⟩ :
        (typeARootLattice n).DiscriminantGroup) = a.val • typeAFundamentalWeightClass n := by
      rw [← natCast_zsmul, mk_eq_zsmul_typeAFundamentalWeightClass_iff_forall_exists_intCast_sub]
      intro r
      refine ⟨if r.val < a.val then 1 else 0, ?_⟩
      simp only [typeAIsometryZeroSumLattice_glueLabelVector_apply n a.isLt.le r, Int.cast_ite,
        Int.cast_one, Int.cast_zero, Int.cast_natCast]
    rw [glueLabelEquiv_A, typeADiscriminantGroupEquiv_apply, ZMod.val_natCast_of_lt a.isLt, ← hmk]
    exact Isometry.mk_eq_discriminantGroupEquiv_ofEq_mk (rootLattice_A n ht).symm _ _ rfl
  | D n => exact mk_glueLabelVector_D n hv ht a hapos
  | E6 =>
    obtain ⟨k, hk⟩ := a
    have hk3 : k < 3 := hk
    dsimp only at hapos
    interval_cases k
    · refine Eq.trans ?_ (glueAlphabetIsometry_E6_apply hv ht (E6.glueLabelEquiv ht ⟨1, hk⟩)).symm
      have hd : ((1 : ℕ) : ZMod 3) = 1 := rfl
      rw [glueLabelEquiv_E6, hd, typeE₆DiscriminantGroupEquiv_apply_one,
        ← mk_typeE₆MinusculeWeightDual]
      exact Isometry.mk_eq_discriminantGroupEquiv_ofEq_mk (rootLattice_E6 ht).symm _ _
        (glueLabelVector_E6_one.trans coe_typeE₆MinusculeWeightDual.symm)
    · refine Eq.trans ?_ (glueAlphabetIsometry_E6_apply hv ht (E6.glueLabelEquiv ht ⟨2, hk⟩)).symm
      have hd : ((2 : ℕ) : ZMod 3) = -1 := by decide
      rw [glueLabelEquiv_E6, hd, map_neg, typeE₆DiscriminantGroupEquiv_apply_one,
        ← mk_typeE₆MinusculeWeightDual, ← Submodule.Quotient.mk_neg]
      exact Isometry.mk_eq_discriminantGroupEquiv_ofEq_mk (rootLattice_E6 ht).symm _ _
        (glueLabelVector_E6_two.trans
          ((congrArg Neg.neg coe_typeE₆MinusculeWeightDual).symm.trans
            (Submodule.coe_neg _ _).symm))
  | E7 =>
    obtain ⟨k, hk⟩ := a
    obtain rfl : k = 1 := by simp only [glueLabelCount] at hk; dsimp only at hapos; omega
    refine Eq.trans ?_ (glueAlphabetIsometry_E7_apply hv ht (E7.glueLabelEquiv ht ⟨1, hk⟩)).symm
    have hd : ((1 : ℕ) : ZMod 2) = 1 := rfl
    rw [glueLabelEquiv_E7, hd, typeE₇DiscriminantGroupEquiv_apply_one,
      ← mk_typeE₇MinusculeWeightDual]
    exact Isometry.mk_eq_discriminantGroupEquiv_ofEq_mk (rootLattice_E7 ht).symm _ _
      (glueLabelVector_E7_one.trans coe_typeE₇MinusculeWeightDual.symm)
  | E8 => have hk1 : a.val < 1 := a.isLt; omega
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **The dual representative of `x : t.glueAlphabet ht` projects to `glueAlphabetIsometry x`.** -/
@[simp] theorem mk_glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    Submodule.Quotient.mk (t.glueDualVector hv ht x) = t.glueAlphabetIsometry hv ht x := by
  have h := t.mk_glueLabelVector hv ht ((t.glueLabelEquiv ht).symm x)
  rw [Equiv.apply_symm_apply] at h
  exact (congrArg Submodule.Quotient.mk
    (Subtype.ext ((t.coe_glueDualVector hv ht x).trans (t.glueVector_def ht x)))).trans h

/-- Any dual bundling of `t.glueVector ht x` projects to `t.glueAlphabetIsometry hv ht x`. -/
@[simp] theorem mk_glueVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) (hx : t.glueVector ht x ∈ (t.rootLattice ht).dualCarrier) :
    Submodule.Quotient.mk ⟨t.glueVector ht x, hx⟩ = t.glueAlphabetIsometry hv ht x :=
  (congrArg Submodule.Quotient.mk
    (Subtype.ext (t.coe_glueDualVector hv ht x).symm)).trans (t.mk_glueDualVector hv ht x)

/-- Reading the glue label of `glueDualVector` back through `glueAlphabetIsometry.symm` recovers
the label. -/
theorem glueAlphabetIsometry_symm_mk_glueDualVector (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (x : t.glueAlphabet ht) :
    (t.glueAlphabetIsometry hv ht).symm (Submodule.Quotient.mk (t.glueDualVector hv ht x)) = x := by
  rw [mk_glueDualVector, QuadraticMap.IsometryEquiv.symm_apply_apply]

/-- A dual vector `y` lies in the discriminant coset named by `x` if and only if `y - glueVector x`
lies in the root lattice. -/
theorem sub_glueVector_mem_rootLattice_carrier_iff (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (y : (t.rootLattice ht).dualCarrier) (x : t.glueAlphabet ht) :
    (y : Fin t.rank → ℚ) - t.glueVector ht x ∈ (t.rootLattice ht).carrier ↔
      Submodule.Quotient.mk y = t.glueAlphabetIsometry hv ht x := by
  rw [← t.mk_glueDualVector hv ht x, discriminantGroup_mk_eq_iff, Submodule.coe_sub,
    coe_glueDualVector]

/-- Representatives add up to a vector of the root lattice: `glueVector (x + y)` differs from
`glueVector x + glueVector y` by an element of `t.rootLattice ht`. -/
theorem glueVector_add_sub_mem_rootLattice_carrier (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (x y : t.glueAlphabet ht) :
    t.glueVector ht (x + y) - (t.glueVector ht x + t.glueVector ht y) ∈
      (t.rootLattice ht).carrier := by
  have h : (Submodule.Quotient.mk (t.glueDualVector hv ht (x + y)) :
      (t.rootLattice ht).DiscriminantGroup) =
      Submodule.Quotient.mk (t.glueDualVector hv ht x + t.glueDualVector hv ht y) := by
    rw [Submodule.Quotient.mk_add (R := ℤ), mk_glueDualVector, mk_glueDualVector,
      mk_glueDualVector, map_add]
    rfl
  simpa only [discriminantGroup_mk_eq_iff, Submodule.coe_sub, Submodule.coe_add,
    coe_glueDualVector] using h

/-- **Every valid Conway--Sloane label representative attains the coset minimum norm
`glueLabelMinimum`.** -/
@[simp] theorem rootLattice_form_glueLabelVector_self (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) {a : ℕ} (ha : a < t.glueLabelCount) :
    (t.rootLattice ht).form (t.glueLabelVector a) (t.glueLabelVector a) =
      t.glueLabelMinimum a := by
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [glueLabelVector_zero, map_zero]
    cases t <;> simp [glueLabelMinimum]
  cases t with
  | A n =>
    have ha' : a ≤ n + 1 := by simp only [glueLabelCount] at ha; omega
    refine (congrArg (fun L : IntegralLattice (Fin n → ℚ) ↦
      L.form ((A n).glueLabelVector a) ((A n).glueLabelVector a)) (rootLattice_A n ht)).trans ?_
    rw [typeARootLattice_form_glueLabelVector_self n ha', glueLabelMinimum_A]
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    have : NeZero n := ⟨by omega⟩
    rw [← (rootLatticeIsometryCheckerboard n hn4 ht).map_app]
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_one n hn4 ht,
        checkerboardLattice_form_checkerboardSpinor_self]
      simp
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_two n hn4 ht,
        checkerboardLattice_form_checkerboardVector_self]
      simp
    · rw [rootLatticeIsometryCheckerboard_glueLabelVector_three n hn4 ht,
        checkerboardLattice_form_checkerboardCospinor_self]
      simp
  | E6 =>
    refine (congrArg (fun L : IntegralLattice (Fin 6 → ℚ) ↦
      L.form (E6.glueLabelVector a) (E6.glueLabelVector a)) (rootLattice_E6 ht)).trans ?_
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [glueLabelVector_E6_one, form_typeE₆MinusculeWeight_self]
      simp [glueLabelMinimum]
    · rw [glueLabelVector_E6_two, map_neg, LinearMap.map_neg, LinearMap.neg_apply, neg_neg,
        form_typeE₆MinusculeWeight_self]
      simp [glueLabelMinimum]
  | E7 =>
    obtain rfl : a = 1 := by simp only [glueLabelCount] at ha; omega
    refine (congrArg (fun L : IntegralLattice (Fin 7 → ℚ) ↦
      L.form (E7.glueLabelVector 1) (E7.glueLabelVector 1)) (rootLattice_E7 ht)).trans ?_
    rw [glueLabelVector_E7_one, form_typeE₇MinusculeWeight_self]
    simp [glueLabelMinimum]
  | E8 => simp only [glueLabelCount] at ha; omega
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Every glue-alphabet representative attains the coset minimum norm `glueMinimum`.** -/
@[simp] theorem rootLattice_form_glueVector_self (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (x : t.glueAlphabet ht) :
    (t.rootLattice ht).form (t.glueVector ht x) (t.glueVector ht x) = t.glueMinimum ht x := by
  rw [glueVector_def, t.rootLattice_form_glueLabelVector_self hv ht
    ((t.glueLabelEquiv ht).symm x).isLt, ← t.glueMinimum_glueLabelEquiv ht, Equiv.apply_symm_apply]

/-- Only the zero glue-alphabet element has representative `0`. -/
@[simp] theorem glueVector_eq_zero_iff (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    {x : t.glueAlphabet ht} :
    t.glueVector ht x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ t.glueVector_zero ht⟩
  have hmin : t.glueMinimum ht x = 0 := by
    rw [← t.rootLattice_form_glueVector_self hv ht x, h, map_zero]
  exact (t.glueMinimum_eq_zero_iff hv ht).mp hmin

/-- Only the zero glue-alphabet element has dual representative `0`. -/
@[simp] theorem glueDualVector_eq_zero_iff (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    {x : t.glueAlphabet ht} :
    t.glueDualVector hv ht x = 0 ↔ x = 0 := by
  rw [← Subtype.coe_inj, coe_glueDualVector, Submodule.coe_zero, t.glueVector_eq_zero_iff hv ht]

/-- Distinct elements of the glue alphabet have distinct canonical dual representatives. -/
theorem glueDualVector_injective (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Function.Injective (t.glueDualVector hv ht) := by
  intro x y hxy
  have hmk := congrArg (Submodule.Quotient.mk : _ → (t.rootLattice ht).DiscriminantGroup) hxy
  rw [mk_glueDualVector, mk_glueDualVector] at hmk
  exact (t.glueAlphabetIsometry hv ht).injective hmk

/-- Distinct elements of the glue alphabet have distinct canonical representatives. -/
theorem glueVector_injective (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Function.Injective (t.glueVector ht) :=
  fun x y hxy ↦ t.glueDualVector_injective hv ht
    (Subtype.ext ((t.coe_glueDualVector hv ht x).trans
      (hxy.trans (t.coe_glueDualVector hv ht y).symm)))

/-- **The polar bilinear pairing on the glue alphabet is the ambient pairing of representatives
modulo `ℤ`.** -/
theorem pairing_glueAlphabet_eq_form_glueVector (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (x y : t.glueAlphabet ht) :
    (t.glueAlphabet ht).toFiniteBilinearModule.pairing x y =
      ((t.rootLattice ht).form (t.glueVector ht x) (t.glueVector ht y) : AddCircle (1 : ℚ)) := by
  rw [← (t.glueAlphabetIsometry hv ht).toHom.map_pairing x y,
    FiniteQuadraticModule.Isometry.toHom_apply, FiniteQuadraticModule.Isometry.toHom_apply,
    ← t.mk_glueDualVector hv ht x, ← t.mk_glueDualVector hv ht y]
  exact ((t.rootLattice ht).discriminantBilinearModule_pairing _ _).trans
    (discriminantPairing_mk _ _ _)

/-! ## Glue words and glued lattices -/

section GlueWord

universe v

variable {ι : Type v} (t : ι → DynkinType) (ht : ∀ i, (t i).IsSimplyLaced)

/-- **The canonical computable coordinate vector of a glue word**, assembling `glueVector`
componentwise in `∀ i, Fin (t i).rank → ℚ`. -/
def glueWordVector (w : ∀ i, (t i).glueAlphabet (ht i)) : ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueVector (ht i) (w i)

/-- Expanding `glueWordVector` as the componentwise assembly of `glueVector`. -/
theorem glueWordVector_def (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t ht w = fun i ↦ (t i).glueVector (ht i) (w i) :=
  (rfl)

/-- Evaluating `glueWordVector` at component `i` gives `(t i).glueVector` of the `i`-th label. -/
@[simp] theorem glueWordVector_apply (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    glueWordVector t ht w i = (t i).glueVector (ht i) (w i) :=
  (rfl)

/-- **The zero glue word is represented by the zero vector.** -/
@[simp] theorem glueWordVector_zero : glueWordVector t ht 0 = 0 := by
  funext i
  simp

/-- Only the zero glue word has representative `0`. -/
@[simp] theorem glueWordVector_eq_zero_iff (hv : ∀ i, (t i).Valid)
    {w : ∀ i, (t i).glueAlphabet (ht i)} :
    glueWordVector t ht w = 0 ↔ w = 0 := by
  simp only [funext_iff, glueWordVector_apply, Pi.zero_apply,
    glueVector_eq_zero_iff _ (hv _) (ht _)]

/-- Distinct glue words have distinct canonical representatives. -/
theorem glueWordVector_injective (hv : ∀ i, (t i).Valid) :
    Function.Injective (glueWordVector t ht) :=
  fun _ _ h ↦ funext fun i ↦ (t i).glueVector_injective (hv i) (ht i) (congrFun h i)

variable [Fintype ι]

/-- **Naturality of `glueWordVector` along reindexing to an equal family of components.** -/
theorem glueWordVector_piGlueAlphabetCongr {κ : Type*} [Fintype κ] {s : κ → DynkinType}
    (hs : ∀ k, (s k).IsSimplyLaced) (σ : κ ≃ ι) (h : ∀ k, t (σ k) = s k)
    (w : ∀ i, (t i).glueAlphabet (ht i)) (k : κ) :
    glueWordVector s hs (piGlueAlphabetCongr t ht σ h w) k =
      (t (σ k)).rootLatticeIsometryOfEq (ht (σ k)) (h k) (hs k)
        (glueWordVector t ht w (σ k)) := by
  rw [glueWordVector_apply, piGlueAlphabetCongr_apply, glueWordVector_apply,
    rootLatticeIsometryOfEq_glueVector]

/-- **Every glue-word representative lies in the dual of the orthogonal sum of root lattices.** -/
theorem glueWordVector_mem_dualCarrier (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
  rw [mem_dualCarrier_pi_iff]
  exact fun i ↦ (t i).glueVector_mem_dualCarrier (hv i) (ht i) (w i)

/-- **The canonical dual-lattice representative of a glue word**, bundled in the dual carrier of
the orthogonal sum of component root lattices. -/
noncomputable def glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  ⟨glueWordVector t ht w, glueWordVector_mem_dualCarrier t ht hv w⟩

/-- Coercing `glueWordDualVector` to the ambient space recovers `glueWordVector`. -/
@[simp] theorem coe_glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (glueWordDualVector t ht hv w : ∀ i, Fin (t i).rank → ℚ) = glueWordVector t ht w :=
  (rfl)

/-- The dual representative of the zero glue word is `0`. -/
@[simp] theorem glueWordDualVector_zero (hv : ∀ i, (t i).Valid) :
    glueWordDualVector t ht hv 0 = 0 :=
  Subtype.ext (by rw [coe_glueWordDualVector, Submodule.coe_zero, glueWordVector_zero])

/-- Only the zero glue word has dual representative `0`. -/
@[simp] theorem glueWordDualVector_eq_zero_iff (hv : ∀ i, (t i).Valid)
    {w : ∀ i, (t i).glueAlphabet (ht i)} :
    glueWordDualVector t ht hv w = 0 ↔ w = 0 := by
  rw [← Subtype.coe_inj, coe_glueWordDualVector, Submodule.coe_zero,
    glueWordVector_eq_zero_iff t ht hv]

/-- Distinct glue words have distinct canonical dual representatives. -/
theorem glueWordDualVector_injective (hv : ∀ i, (t i).Valid) :
    Function.Injective (glueWordDualVector t ht hv) :=
  fun x y hxy ↦ glueWordVector_injective t ht hv
    ((coe_glueWordDualVector t ht hv x).symm.trans
      ((congrArg Subtype.val hxy).trans (coe_glueWordDualVector t ht hv y)))

/-- **The dual representative of a glue word `w` projects to `glueWordIsometry t ht hv w`.** -/
@[simp] theorem mk_glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    Submodule.Quotient.mk (glueWordDualVector t ht hv w) = glueWordIsometry t ht hv w := by
  apply (discriminantGroupPiEquiv _).injective
  funext i
  rw [discriminantGroupPiEquiv_mk, discriminantGroupPiEquiv_glueWordIsometry,
    ← (t i).mk_glueDualVector (hv i) (ht i) (w i)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun j ↦ by simp))

/-- Any dual-carrier bundling of `glueWordVector t ht w` projects to
`glueWordIsometry t ht hv w`. -/
@[simp] theorem mk_glueWordVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i))
    (hx : glueWordVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier) :
    Submodule.Quotient.mk ⟨glueWordVector t ht w, hx⟩ = glueWordIsometry t ht hv w :=
  (congrArg Submodule.Quotient.mk
    (Subtype.ext (coe_glueWordDualVector t ht hv w).symm)).trans
      (mk_glueWordDualVector t ht hv w)

/-- Reading the glue word of `glueWordDualVector` back through `glueWordIsometry.symm` recovers
the word. -/
theorem glueWordIsometry_symm_mk_glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (glueWordIsometry t ht hv).symm (Submodule.Quotient.mk (glueWordDualVector t ht hv w)) = w := by
  rw [mk_glueWordDualVector, QuadraticMap.IsometryEquiv.symm_apply_apply]

/-- A dual vector `x` of the orthogonal sum of root lattices lies in the coset named by the glue
word `w` if and only if `x - glueWordVector w` lies in the orthogonal sum of root lattices. -/
theorem sub_glueWordVector_mem_pi_rootLattice_carrier_iff (hv : ∀ i, (t i).Valid)
    (x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (x : ∀ i, Fin (t i).rank → ℚ) - glueWordVector t ht w ∈
        (pi fun i ↦ (t i).rootLattice (ht i)).carrier ↔
      Submodule.Quotient.mk x = glueWordIsometry t ht hv w := by
  rw [← mk_glueWordDualVector t ht hv w, discriminantGroup_mk_eq_iff, Submodule.coe_sub,
    coe_glueWordDualVector]

/-- Glue-word representatives add up to a vector of the orthogonal sum of root lattices. -/
theorem glueWordVector_add_sub_mem_pi_rootLattice_carrier (hv : ∀ i, (t i).Valid)
    (v w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t ht (v + w) - (glueWordVector t ht v + glueWordVector t ht w) ∈
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [mem_pi_carrier_iff]
  intro i
  simp only [Pi.sub_apply, Pi.add_apply, glueWordVector_apply]
  exact (t i).glueVector_add_sub_mem_rootLattice_carrier (hv i) (ht i) (v i) (w i)

/-- **Every glue-word representative attains the coset minimum norm `∑ i, μ_(t i)(w_i)`.** -/
theorem pi_rootLattice_form_glueWordVector_self (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).form (glueWordVector t ht w) (glueWordVector t ht w) =
      ∑ i, (t i).glueMinimum (ht i) (w i) := by
  rw [pi_form, piForm_apply]
  exact sum_congr rfl fun i _ ↦ (t i).rootLattice_form_glueVector_self (hv i) (ht i) (w i)

/-- **The polar bilinear pairing on glue words is the ambient pairing of `glueWordVector`
modulo `ℤ`.** -/
theorem pairing_pi_glueAlphabet_eq_form_glueWordVector (hv : ∀ i, (t i).Valid)
    (v w : ∀ i, (t i).glueAlphabet (ht i)) :
    (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).toFiniteBilinearModule.pairing
        v w =
      (((pi fun i ↦ (t i).rootLattice (ht i)).form
        (glueWordVector t ht v) (glueWordVector t ht w) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [← (glueWordIsometry t ht hv).toHom.map_pairing v w,
    FiniteQuadraticModule.Isometry.toHom_apply, FiniteQuadraticModule.Isometry.toHom_apply,
    ← mk_glueWordDualVector t ht hv v, ← mk_glueWordDualVector t ht hv w]
  exact ((pi fun i ↦ (t i).rootLattice (ht i)).discriminantBilinearModule_pairing _ _).trans
    (discriminantPairing_mk _ _ _)

/-! ### Explicit coset decomposition and generators of glued lattices -/

section GluedLattice

variable (hv : ∀ i, (t i).Valid)
  (H : AddSubgroup (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)))
  (hH : (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).IsIsotropic H)

/-- **The canonical representative of a glue word `w` lies in the glued lattice if and only if
`w ∈ H`.** -/
@[simp] theorem glueWordVector_mem_gluedLattice_carrier_iff
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t ht w ∈ (gluedLattice t ht hv H hH).carrier ↔ w ∈ H := by
  rw [mem_gluedLattice_carrier_iff]
  have hsymm : (glueWordIsometry t ht hv).toAddEquiv.symm
      (glueWordIsometry t ht hv w) = w :=
    (glueWordIsometry t ht hv).toAddEquiv.symm_apply_apply w
  refine ⟨fun ⟨hx, hw⟩ ↦ ?_, fun hw ↦ ⟨glueWordVector_mem_dualCarrier t ht hv w, ?_⟩⟩
  · rwa [mk_glueWordVector t ht hv w hx, hsymm] at hw
  · rwa [mk_glueWordVector t ht hv w, hsymm]

/-- **Explicit coset decomposition of a glued lattice**: a vector `x` lies in `gluedLattice`
if and only if it differs from the canonical representative `glueWordVector t ht w` of some glue
word `w ∈ H` by a vector of the orthogonal sum of root lattices. -/
theorem mem_gluedLattice_carrier_iff_exists (x : ∀ i, Fin (t i).rank → ℚ) :
    x ∈ (gluedLattice t ht hv H hH).carrier ↔
      ∃ w ∈ H, x - glueWordVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).carrier := by
  rw [mem_gluedLattice_carrier_iff]
  constructor
  · rintro ⟨hx, hw⟩
    refine ⟨_, hw, ?_⟩
    rw [sub_glueWordVector_mem_pi_rootLattice_carrier_iff t ht hv ⟨x, hx⟩]
    exact ((glueWordIsometry t ht hv).toAddEquiv.apply_symm_apply _).symm
  · rintro ⟨w, hw, hsub⟩
    have hx : x ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier := by
      have hroot := (pi fun i ↦ (t i).rootLattice (ht i)).le_dualCarrier hsub
      simpa only [sub_add_cancel] using
        Submodule.add_mem _ hroot (glueWordVector_mem_dualCarrier t ht hv w)
    refine ⟨hx, ?_⟩
    have hmk := (sub_glueWordVector_mem_pi_rootLattice_carrier_iff t ht hv ⟨x, hx⟩ w).mp hsub
    have hsymm : (glueWordIsometry t ht hv).toAddEquiv.symm
        (glueWordIsometry t ht hv w) = w :=
      (glueWordIsometry t ht hv).toAddEquiv.symm_apply_apply w
    rwa [hmk, hsymm]

/-- **Constructive generator theorem for a glued lattice**: if `G` generates the glue subgroup `H`,
then `gluedLattice` is spanned over `ℤ` by the orthogonal sum of root lattices together with the
explicit shortest representatives `glueWordVector t ht w` for `w ∈ G`. -/
theorem gluedLattice_carrier_eq_sup_span_glueWordVector
    {G : Set (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i))}
    (hG : AddSubgroup.closure G = H) :
    (gluedLattice t ht hv H hH).carrier =
      (pi fun i ↦ (t i).rootLattice (ht i)).carrier ⊔
        Submodule.span ℤ (glueWordVector t ht '' G) := by
  simpa only [coe_glueWordDualVector] using
    gluedLattice_carrier_eq_sup_span t ht hv H hH hG (glueWordDualVector t ht hv)
      fun w _ ↦ mk_glueWordDualVector t ht hv w

end GluedLattice

end GlueWord

end TauCeti.DynkinType

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.Glued

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
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_one`,
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_two`,
  `TauCeti.DynkinType.rootLatticeIsometryCheckerboard_glueLabelVector_three`: images of the
  `Aₙ` and `Dₙ` label representatives in the classical zero-sum and checkerboard models.
* `TauCeti.DynkinType.glueVector`, `TauCeti.DynkinType.glueDualVector`: the representative of an
  element of `t.glueAlphabet ht` in the ambient space and in `(t.rootLattice ht).dualCarrier`.
* `TauCeti.DynkinType.mk_glueDualVector`, `TauCeti.DynkinType.rootLattice_form_glueVector_self`,
  `TauCeti.DynkinType.pairing_glueAlphabet_eq_form_glueVector`: each representative lies in the
  expected discriminant coset, attains `glueMinimum`, and computes the polar pairing modulo `ℤ`.
* `TauCeti.DynkinType.glueWordVector`, `TauCeti.DynkinType.glueWordDualVector`: the coordinatewise
  representative of a glue word across a family of simply-laced components.
* `TauCeti.DynkinType.mk_glueWordDualVector`,
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
  | E6, 1 => typeE₆MinusculeWeight
  | E6, 2 => -typeE₆MinusculeWeight
  | E7, 1 => typeE₇MinusculeWeight
  | _, _ => 0

/-- The `j`-th simple-root coordinate of label `a` of `Aₙ`. -/
@[simp]
theorem glueLabelVector_A_apply (n a : ℕ) (j : Fin n) :
    (A n).glueLabelVector a j =
      ((min (j.val + 1) a : ℕ) : ℚ) - ((j.val + 1 : ℕ) * a : ℚ) / (n + 1) :=
  (rfl)

/-- The `j`-th simple-root coordinate of the spinor label `1` of `Dₙ`. -/
@[simp]
theorem glueLabelVector_D_one_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 1 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then ((n : ℚ) - 2) / 4
      else (n : ℚ) / 4 :=
  (rfl)

/-- The `j`-th simple-root coordinate of the vector label `2` of `Dₙ`. -/
@[simp]
theorem glueLabelVector_D_two_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 2 j =
      if j.val + 2 = n then -(1 / 2)
      else if j.val + 1 = n then 1 / 2
      else 0 :=
  (rfl)

/-- The `j`-th simple-root coordinate of the cospinor label `3` of `Dₙ`. -/
@[simp]
theorem glueLabelVector_D_three_apply (n : ℕ) (j : Fin n) :
    (D n).glueLabelVector 3 j =
      if j.val + 2 < n then ((j.val + 1 : ℕ) : ℚ) / 2
      else if j.val + 2 = n then (n : ℚ) / 4
      else ((n : ℚ) - 2) / 4 :=
  (rfl)

/-- Label `1` of `E₆` is the minuscule weight `ϖ₁`. -/
theorem glueLabelVector_E6_one :
    (E6.glueLabelVector 1 : Fin 6 → ℚ) = typeE₆MinusculeWeight :=
  (rfl)

/-- Label `2` of `E₆` is `-ϖ₁`. -/
theorem glueLabelVector_E6_two :
    (E6.glueLabelVector 2 : Fin 6 → ℚ) = -typeE₆MinusculeWeight :=
  (rfl)

/-- Label `1` of `E₇` is the minuscule weight `ϖ₇`. -/
theorem glueLabelVector_E7_one :
    (E7.glueLabelVector 1 : Fin 7 → ℚ) = typeE₇MinusculeWeight :=
  (rfl)

/-- Every label of `E₈` has representative `0`. -/
@[simp]
theorem glueLabelVector_E8_apply (a : ℕ) (j : Fin 8) : E8.glueLabelVector a j = 0 :=
  (rfl)

/-- **The zero label is represented by the zero vector in every Dynkin type.** -/
@[simp]
theorem glueLabelVector_zero (t : DynkinType) : t.glueLabelVector 0 = 0 := by
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
  push_cast
  field_simp
  ring

/-- Label `n + 1` of `Aₙ` evaluates to the zero vector. -/
theorem glueLabelVector_A_succ (n : ℕ) :
    ((A n).glueLabelVector (n + 1) : Fin n → ℚ) = 0 := by
  refine funext fun (j : Fin n) ↦ ?_
  have hj : j.val < n := j.isLt
  have hmin : min (j.val + 1) (n + 1) = j.val + 1 := Nat.min_eq_left (by omega)
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hlhs : (A n).glueLabelVector (n + 1) j = 0 := by
    rw [glueLabelVector_A_apply, hmin]
    push_cast
    field_simp
    ring
  exact hlhs.trans rfl

/-- In type `Dₙ`, the cospinor representative is the spinor representative minus the vector
representative at every rank. -/
theorem glueLabelVector_D_three_eq_sub (n : ℕ) :
    (D n).glueLabelVector 3 = (D n).glueLabelVector 1 - (D n).glueLabelVector 2 := by
  refine funext fun (j : Fin n) ↦ ?_
  have hj : j.val < n := j.isLt
  have hsub : ((D n).glueLabelVector 1 - (D n).glueLabelVector 2) j =
      (D n).glueLabelVector 1 j - (D n).glueLabelVector 2 j := rfl
  rw [hsub, glueLabelVector_D_three_apply, glueLabelVector_D_one_apply,
    glueLabelVector_D_two_apply]
  by_cases h2 : j.val + 2 < n
  · have hne2 : j.val + 2 ≠ n := by omega
    have hne1 : j.val + 1 ≠ n := by omega
    rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right hne2, ite_eq_right hne1, sub_zero]
  · by_cases heq2 : j.val + 2 = n
    · rw [ite_eq_right h2, ite_eq_left heq2, ite_eq_right h2, ite_eq_left heq2, ite_eq_left heq2]
      ring
    · have heq1 : j.val + 1 = n := by omega
      rw [ite_eq_right h2, ite_eq_right heq2, ite_eq_right h2, ite_eq_right heq2,
        ite_eq_right heq2, ite_eq_left heq1]
      ring

/-- Transporting along an equality of simply-laced Dynkin types preserves `glueLabelVector`. -/
theorem rootLatticeIsometryOfEq_glueLabelVector {t s : DynkinType} (ht : t.IsSimplyLaced)
    (h : t = s) (hs : s.IsSimplyLaced) (a : ℕ) :
    t.rootLatticeIsometryOfEq ht h hs (t.glueLabelVector a) = s.glueLabelVector a := by
  subst h
  rw [rootLatticeIsometryOfEq_rfl, Isometry.refl_apply]

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

/-- The `Aₙ` representative for label `a ≤ n + 1` differs from `a • ω₁` by a vector of the root
lattice. -/
private theorem glueLabelVector_A_sub_nsmul_mem_carrier (n : ℕ) {a : ℕ} (ha : a ≤ n + 1) :
    (fun j : Fin n ↦ (A n).glueLabelVector a j) - (a : ℤ) • typeAFundamentalWeight n ∈
      (typeARootLattice n).carrier := by
  rw [← (typeAIsometryZeroSumLattice n).apply_mem_carrier_iff, mem_zeroSumLattice_carrier_iff]
  intro r
  refine ⟨(if r.val < a then 1 else 0) - (a : ℤ) * if r = 0 then 1 else 0, ?_⟩
  rw [map_sub, map_zsmul, Submodule.coe_sub, Submodule.coe_smul_of_tower, Pi.sub_apply,
    Pi.smul_apply, typeAIsometryZeroSumLattice_glueLabelVector_apply n ha r,
    typeAIsometryZeroSumLattice_typeAFundamentalWeight_apply, zsmul_eq_mul]
  push_cast
  split_ifs <;> ring

/-- Helper relating `rootLatticeIsometryCheckerboard` to `typeDSimpleRootBasis.repr` on `ℚⁿ`. -/
private theorem rootLatticeIsometryCheckerboard_eq_of_repr (n : ℕ) (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) {x y : Fin n → ℚ}
    (h : letI : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
      ∀ k : Fin n, x k = (typeDSimpleRootBasis ℚ n hn).repr y k) :
    rootLatticeIsometryCheckerboard n hn ht x = y := by
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  let f : (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) :=
    (rootLatticeIsometryCheckerboard n hn ht : (Fin (D n).rank → ℚ) ≃ₗ[ℚ] (Fin n → ℚ)).toLinearMap
  have hx : x = ∑ k : Fin n, x k • Pi.single k (1 : ℚ) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc
    f x = ∑ k : Fin n, x k • f (Pi.single k 1) := by
      conv_lhs => rw [hx]
      rw [map_sum]
      exact sum_congr rfl fun k _ ↦ map_smul f _ _
    _ = ∑ k : Fin n, (typeDSimpleRootBasis ℚ n hn).repr y k • typeDSimpleRootBasis ℚ n hn k := by
      refine sum_congr rfl fun k _ ↦ ?_
      have hf : f (Pi.single k 1) = typeDSimpleRootBasis ℚ n hn k := by
        refine (rootLatticeIsometryCheckerboard_single n hn ht k).trans ?_
        rw [typeDSimpleRootBasis_apply]
        exact funext (checkerboardSimpleRoot_apply hn k)
      rw [h k, hf]
    _ = y := (typeDSimpleRootBasis ℚ n hn).sum_repr y

/-- **In type `Dₙ` (`4 ≤ n`), label `1` maps to the Conway--Sloane checkerboard spinor
representative `s = (1/2, …, 1/2)`.** -/
theorem rootLatticeIsometryCheckerboard_glueLabelVector_one (n : ℕ) (hn : 4 ≤ n)
    (ht : (D n).IsSimplyLaced) :
    rootLatticeIsometryCheckerboard n hn ht ((D n).glueLabelVector 1) =
      checkerboardSpinor n := by
  refine rootLatticeIsometryCheckerboard_eq_of_repr n hn ht fun k ↦ ?_
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
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
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
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
@[expose] def glueVector (t : DynkinType) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) : Fin t.rank → ℚ :=
  t.glueLabelVector ((t.glueLabelEquiv ht).symm x).val

/-- Expanding `glueVector` in terms of `glueLabelVector` and `glueLabelEquiv`. -/
theorem glueVector_def (t : DynkinType) (ht : t.IsSimplyLaced) (x : t.glueAlphabet ht) :
    t.glueVector ht x = t.glueLabelVector ((t.glueLabelEquiv ht).symm x).val :=
  (rfl)

/-- Evaluating `glueVector` on the class of a bounded label `a` returns `t.glueLabelVector a`. -/
@[simp]
theorem glueVector_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : Fin t.glueLabelCount) :
    t.glueVector ht (t.glueLabelEquiv ht a) = t.glueLabelVector a.val := by
  rw [glueVector_def, Equiv.symm_apply_apply]

/-- **The zero class in the glue alphabet is represented by `0`.** -/
@[simp]
theorem glueVector_zero (t : DynkinType) (ht : t.IsSimplyLaced) :
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
  cases t with
  | A n =>
    have ha' : a ≤ n + 1 := by simp only [glueLabelCount] at ha; omega
    have hmem : (fun j : Fin n ↦ (A n).glueLabelVector a j) ∈ (typeARootLattice n).dualCarrier := by
      have hsub := (typeARootLattice n).le_dualCarrier
        (glueLabelVector_A_sub_nsmul_mem_carrier n ha')
      have hw : (a : ℤ) • typeAFundamentalWeight n ∈ (typeARootLattice n).dualCarrier :=
        Submodule.smul_mem _ _ (typeAFundamentalWeight_mem_dualCarrier n)
      have hadd := Submodule.add_mem _ hsub hw
      rwa [sub_add_cancel] at hadd
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_A n ht)).symm ▸ hmem
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    have : NeZero n := ⟨by omega⟩
    rw [← (rootLatticeIsometryCheckerboard n hn4 ht).apply_mem_dualCarrier_iff]
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [glueLabelVector_zero, map_zero]
      exact zero_mem _
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
      · have h0 : (E6.glueLabelVector 0 : Fin 6 → ℚ) = 0 := rfl
        rw [h0]
        exact zero_mem _
      · rw [glueLabelVector_E6_one]
        exact typeE₆MinusculeWeight_mem_dualCarrier
      · rw [glueLabelVector_E6_two]
        exact neg_mem typeE₆MinusculeWeight_mem_dualCarrier
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_E6 ht)).symm ▸ hmem
  | E7 =>
    have hmem : (E7.glueLabelVector a : Fin 7 → ℚ) ∈ typeE₇RootLattice.dualCarrier := by
      simp only [glueLabelCount] at ha
      interval_cases a
      · have h0 : (E7.glueLabelVector 0 : Fin 7 → ℚ) = 0 := rfl
        rw [h0]
        exact zero_mem _
      · rw [glueLabelVector_E7_one]
        exact typeE₇MinusculeWeight_mem_dualCarrier
    exact (congrArg IntegralLattice.dualCarrier (rootLattice_E7 ht)).symm ▸ hmem
  | E8 =>
    simp only [glueLabelCount] at ha
    obtain rfl : a = 0 := by omega
    rw [glueLabelVector_zero]
    exact zero_mem _
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **The representative of every glue-alphabet class lies in the dual of the root lattice.** -/
theorem glueVector_mem_dualCarrier (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    t.glueVector ht x ∈ (t.rootLattice ht).dualCarrier :=
  t.glueLabelVector_mem_dualCarrier hv ht ((t.glueLabelEquiv ht).symm x).isLt

/-- **The canonical dual-lattice representative of a glue-alphabet class**, bundling `glueVector`
into `(t.rootLattice ht).dualCarrier`. -/
noncomputable def glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) : (t.rootLattice ht).dualCarrier :=
  ⟨t.glueVector ht x, t.glueVector_mem_dualCarrier hv ht x⟩

/-- Coercing `glueDualVector` to the ambient space recovers `glueVector`. -/
@[simp]
theorem coe_glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    (t.glueDualVector hv ht x : Fin t.rank → ℚ) = t.glueVector ht x :=
  (rfl)

/-- The dual representative of the zero glue label is `0`. -/
@[simp]
theorem glueDualVector_zero (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    t.glueDualVector hv ht 0 = 0 :=
  Subtype.ext (t.glueVector_zero ht)

/-- Helper: in `Dₙ`, the quotient class of `glueLabelVector a` matches `glueAlphabetIsometry` on
`glueLabelEquiv ht a`. -/
private theorem mk_glueLabelVector_D (n : ℕ) (hv : (D n).Valid) (ht : (D n).IsSimplyLaced)
    (a : Fin 4) :
    Submodule.Quotient.mk ⟨(D n).glueLabelVector a.val,
        (D n).glueLabelVector_mem_dualCarrier hv ht a.isLt⟩ =
      (D n).glueAlphabetIsometry hv ht ((D n).glueLabelEquiv ht a) := by
  have hn4 : 4 ≤ n := valid_D.mp hv
  have : NeZero n := ⟨by omega⟩
  set e := rootLatticeIsometryCheckerboard n hn4 ht
  have hcoe (k : Fin 4) :
      (e.dualCarrierEquiv ⟨(D n).glueLabelVector k.val,
        (D n).glueLabelVector_mem_dualCarrier hv ht k.isLt⟩ : Fin n → ℚ) =
        e ((D n).glueLabelVector k.val) :=
    e.coe_dualCarrierEquiv_apply _
  obtain ⟨k, hk⟩ := a
  rcases Nat.even_or_odd n with hpar | hpar
  · refine Eq.trans ?_ (glueAlphabetIsometry_D_apply_of_even n hv ht hpar _).symm
    apply e.discriminantGroupEquiv.injective
    rw [Isometry.discriminantGroupEquiv_mk, Isometry.discriminantGroupEquiv_symm,
      LinearEquiv.apply_symm_apply, glueLabelEquiv_D_of_even n ht hpar]
    interval_cases k
    · have hd : (((0 / 2 : ℕ) : ZMod 2), ((0 % 2 : ℕ) : ZMod 2)) = 0 := by decide
      rw [hd, map_zero, Submodule.Quotient.mk_eq_zero, mem_carrierInDual_iff, hcoe ⟨0, hk⟩,
        glueLabelVector_zero, map_zero]
      exact zero_mem _
    · have hd : (((1 / 2 : ℕ) : ZMod 2), ((1 % 2 : ℕ) : ZMod 2)) = (0, 1) := by decide
      rw [hd, zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_zero_one,
        mk_eq_checkerboardSpinorClass_iff, hcoe ⟨1, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_one n hn4 ht, sub_self]
      exact zero_mem _
    · have hd : (((2 / 2 : ℕ) : ZMod 2), ((2 % 2 : ℕ) : ZMod 2)) = (1, 0) := by decide
      rw [hd, zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_zero,
        mk_eq_checkerboardVectorClass_iff, hcoe ⟨2, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_two n hn4 ht, sub_self]
      exact zero_mem _
    · have hd : (((3 / 2 : ℕ) : ZMod 2), ((3 % 2 : ℕ) : ZMod 2)) = (1, 1) := by decide
      rw [hd, zmodTwoProdAddEquivCheckerboardDiscriminantGroup_apply_one_one,
        mk_eq_checkerboardCospinorClass_iff, hcoe ⟨3, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_three n hn4 ht, sub_self]
      exact zero_mem _
  · refine Eq.trans ?_ (glueAlphabetIsometry_D_apply_of_odd n hv ht hpar _).symm
    apply e.discriminantGroupEquiv.injective
    rw [Isometry.discriminantGroupEquiv_mk, Isometry.discriminantGroupEquiv_symm,
      LinearEquiv.apply_symm_apply, glueLabelEquiv_D_of_odd n ht hpar]
    interval_cases k
    · have hd : ((0 : ℕ) : ZMod 4) = 0 := by decide
      rw [hd, map_zero, Submodule.Quotient.mk_eq_zero, mem_carrierInDual_iff, hcoe ⟨0, hk⟩,
        glueLabelVector_zero, map_zero]
      exact zero_mem _
    · have hd : ((1 : ℕ) : ZMod 4) = 1 := by decide
      rw [hd, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_one,
        mk_eq_checkerboardSpinorClass_iff, hcoe ⟨1, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_one n hn4 ht, sub_self]
      exact zero_mem _
    · have hd : ((2 : ℕ) : ZMod 4) = 2 := by decide
      rw [hd, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_two,
        mk_eq_checkerboardVectorClass_iff, hcoe ⟨2, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_two n hn4 ht, sub_self]
      exact zero_mem _
    · have hd : ((3 : ℕ) : ZMod 4) = 3 := by decide
      rw [hd, zmodFourAddEquivCheckerboardDiscriminantGroup_apply_three,
        mk_eq_checkerboardCospinorClass_iff, hcoe ⟨3, hk⟩,
        rootLatticeIsometryCheckerboard_glueLabelVector_three n hn4 ht, sub_self]
      exact zero_mem _

/-- **The representative of a bounded printed label projects to the discriminant class named by
that label.** -/
theorem mk_glueLabelVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : Fin t.glueLabelCount) :
    Submodule.Quotient.mk ⟨t.glueLabelVector a.val,
        t.glueLabelVector_mem_dualCarrier hv ht a.isLt⟩ =
      t.glueAlphabetIsometry hv ht (t.glueLabelEquiv ht a) := by
  cases t with
  | A n =>
    refine Eq.trans ?_ (glueAlphabetIsometry_A_apply n hv ht ((A n).glueLabelEquiv ht a)).symm
    let e := Isometry.ofEq (rootLattice_A n ht).symm
    have hmem :
        (fun j : Fin n ↦ (A n).glueLabelVector a.val j) ∈ (typeARootLattice n).dualCarrier := by
      have hsub := (typeARootLattice n).le_dualCarrier
        (glueLabelVector_A_sub_nsmul_mem_carrier n a.isLt.le)
      have hw : (a.val : ℤ) • typeAFundamentalWeight n ∈ (typeARootLattice n).dualCarrier :=
        Submodule.smul_mem _ _ (typeAFundamentalWeight_mem_dualCarrier n)
      have hadd := Submodule.add_mem _ hsub hw
      rwa [sub_add_cancel] at hadd
    have hmkA : (Submodule.Quotient.mk ⟨fun j : Fin n ↦ (A n).glueLabelVector a.val j, hmem⟩ :
        (typeARootLattice n).DiscriminantGroup) =
        typeADiscriminantGroupEquiv n ((A n).glueLabelEquiv ht a) := by
      rw [glueLabelEquiv_A, typeADiscriminantGroupEquiv_apply, ZMod.val_natCast_of_lt a.isLt,
        ← natCast_zsmul, mk_eq_zsmul_typeAFundamentalWeightClass_iff]
      exact glueLabelVector_A_sub_nsmul_mem_carrier n a.isLt.le
    rw [← hmkA]
    refine Eq.trans ?_ (e.discriminantGroupEquiv_mk _).symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext
      ((e.coe_dualCarrierEquiv_apply ⟨fun j : Fin n ↦ (A n).glueLabelVector a.val j, hmem⟩).trans
        (Isometry.ofEq_apply (rootLattice_A n ht).symm _)).symm)
  | D n => exact mk_glueLabelVector_D n hv ht a
  | E6 =>
    refine Eq.trans ?_ (glueAlphabetIsometry_E6_apply hv ht (E6.glueLabelEquiv ht a)).symm
    let e := Isometry.ofEq (rootLattice_E6 ht).symm
    obtain ⟨k, hk⟩ := a
    simp only [glueLabelCount] at hk
    rw [glueLabelEquiv_E6]
    interval_cases k
    · have hd : ((0 : ℕ) : ZMod 3) = 0 := by decide
      rw [hd, map_zero, map_zero]
      have hzero : (⟨E6.glueLabelVector (⟨0, hk⟩ : Fin E6.glueLabelCount).val,
          E6.glueLabelVector_mem_dualCarrier hv ht hk⟩ : (E6.rootLattice ht).dualCarrier) = 0 :=
        Subtype.ext (glueLabelVector_zero E6)
      exact (congrArg Submodule.Quotient.mk hzero).trans (Submodule.Quotient.mk_zero _)
    · have hd : ((1 : ℕ) : ZMod 3) = 1 := by decide
      rw [hd, typeE₆DiscriminantGroupEquiv_apply_one, ← mk_typeE₆MinusculeWeightDual]
      refine Eq.trans ?_ (e.discriminantGroupEquiv_mk _).symm
      exact congrArg Submodule.Quotient.mk (Subtype.ext
        ((e.coe_dualCarrierEquiv_apply typeE₆MinusculeWeightDual).trans
          ((Isometry.ofEq_apply (rootLattice_E6 ht).symm _).trans
            coe_typeE₆MinusculeWeightDual)).symm)
    · have hd : ((2 : ℕ) : ZMod 3) = -1 := by decide
      rw [hd, map_neg, typeE₆DiscriminantGroupEquiv_apply_one, ← mk_typeE₆MinusculeWeightDual,
        ← Submodule.Quotient.mk_neg]
      refine Eq.trans ?_ (e.discriminantGroupEquiv_mk _).symm
      exact congrArg Submodule.Quotient.mk (Subtype.ext
        ((e.coe_dualCarrierEquiv_apply (-typeE₆MinusculeWeightDual)).trans
          ((Isometry.ofEq_apply (rootLattice_E6 ht).symm _).trans
            ((Submodule.coe_neg typeE₆RootLattice.dualCarrier typeE₆MinusculeWeightDual).trans
              (congrArg Neg.neg coe_typeE₆MinusculeWeightDual)))).symm)
  | E7 =>
    refine Eq.trans ?_ (glueAlphabetIsometry_E7_apply hv ht (E7.glueLabelEquiv ht a)).symm
    let e := Isometry.ofEq (rootLattice_E7 ht).symm
    obtain ⟨k, hk⟩ := a
    simp only [glueLabelCount] at hk
    rw [glueLabelEquiv_E7]
    interval_cases k
    · have hd : ((0 : ℕ) : ZMod 2) = 0 := by decide
      rw [hd, map_zero, map_zero]
      have hzero : (⟨E7.glueLabelVector (⟨0, hk⟩ : Fin E7.glueLabelCount).val,
          E7.glueLabelVector_mem_dualCarrier hv ht hk⟩ : (E7.rootLattice ht).dualCarrier) = 0 :=
        Subtype.ext (glueLabelVector_zero E7)
      exact (congrArg Submodule.Quotient.mk hzero).trans (Submodule.Quotient.mk_zero _)
    · have hd : ((1 : ℕ) : ZMod 2) = 1 := by decide
      rw [hd, typeE₇DiscriminantGroupEquiv_apply_one, ← mk_typeE₇MinusculeWeightDual]
      refine Eq.trans ?_ (e.discriminantGroupEquiv_mk _).symm
      exact congrArg Submodule.Quotient.mk (Subtype.ext
        ((e.coe_dualCarrierEquiv_apply typeE₇MinusculeWeightDual).trans
          ((Isometry.ofEq_apply (rootLattice_E7 ht).symm _).trans
            coe_typeE₇MinusculeWeightDual)).symm)
  | E8 =>
    obtain ⟨k, hk⟩ := a
    simp only [glueLabelCount] at hk
    obtain rfl : k = 0 := by omega
    have hzero : (⟨E8.glueLabelVector (⟨0, hk⟩ : Fin E8.glueLabelCount).val,
        E8.glueLabelVector_mem_dualCarrier hv ht hk⟩ : (E8.rootLattice ht).dualCarrier) = 0 :=
      Subtype.ext (glueLabelVector_zero E8)
    have hrhs : E8.glueAlphabetIsometry hv ht (E8.glueLabelEquiv ht ⟨0, hk⟩) = 0 := by
      rw [glueLabelEquiv_E8, map_zero]
    exact ((congrArg Submodule.Quotient.mk hzero).trans (Submodule.Quotient.mk_zero _)).trans
      hrhs.symm
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **The dual representative of `x : t.glueAlphabet ht` projects to `glueAlphabetIsometry x`.** -/
@[simp]
theorem mk_glueDualVector (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    Submodule.Quotient.mk (t.glueDualVector hv ht x) = t.glueAlphabetIsometry hv ht x := by
  have h := t.mk_glueLabelVector hv ht ((t.glueLabelEquiv ht).symm x)
  rwa [Equiv.apply_symm_apply] at h

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
@[simp]
theorem rootLattice_form_glueLabelVector_self (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) {a : ℕ} (ha : a < t.glueLabelCount) :
    (t.rootLattice ht).form (t.glueLabelVector a) (t.glueLabelVector a) =
      t.glueLabelMinimum a := by
  cases t with
  | A n =>
    let v : Fin n → ℚ := (A n).glueLabelVector a
    refine (congrArg (fun L : IntegralLattice (Fin n → ℚ) ↦ L.form v v)
      (rootLattice_A n ht)).trans ?_
    rw [typeARootLattice_form_self_eq_dotProduct, glueLabelMinimum_A]
    have ha' : a ≤ n + 1 := by simp only [glueLabelCount] at ha; omega
    set e := typeAIsometryZeroSumLattice n
    have hsum := (mem_singleParityCheckCode ℚ (Fin (n + 1))).mp (e v).2
    have hcoord := typeAIsometryZeroSumLattice_glueLabelVector_apply n ha'
    exact (dotProduct_self_eq_mul_sub_div_iff (k := a) hsum fun r ↦
      ⟨if r.val < a then 1 else 0, by simp [e, v, hcoord r]⟩).mpr fun r ↦ by
      by_cases hr : r.val < a <;> simp [e, v, hcoord r, hr]
  | D n =>
    have hn4 : 4 ≤ n := valid_D.mp hv
    have : NeZero n := ⟨by omega⟩
    rw [← (rootLatticeIsometryCheckerboard n hn4 ht).map_app]
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [glueLabelVector_zero, map_zero, map_zero]
      simp
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
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [glueLabelVector_zero, map_zero]
      simp
    · refine (congrArg
        (fun L : IntegralLattice (Fin 6 → ℚ) ↦ L.form typeE₆MinusculeWeight typeE₆MinusculeWeight)
        (rootLattice_E6 ht)).trans ?_
      rw [form_typeE₆MinusculeWeight_self]
      simp [glueLabelMinimum]
    · refine (congrArg
        (fun L : IntegralLattice (Fin 6 → ℚ) ↦
          L.form (-typeE₆MinusculeWeight) (-typeE₆MinusculeWeight))
        (rootLattice_E6 ht)).trans ?_
      rw [map_neg, LinearMap.map_neg, LinearMap.neg_apply, neg_neg,
        form_typeE₆MinusculeWeight_self]
      simp [glueLabelMinimum]
  | E7 =>
    simp only [glueLabelCount] at ha
    interval_cases a
    · rw [glueLabelVector_zero, map_zero]
      simp
    · refine (congrArg
        (fun L : IntegralLattice (Fin 7 → ℚ) ↦ L.form typeE₇MinusculeWeight typeE₇MinusculeWeight)
        (rootLattice_E7 ht)).trans ?_
      rw [form_typeE₇MinusculeWeight_self]
      simp [glueLabelMinimum]
  | E8 =>
    simp only [glueLabelCount] at ha
    obtain rfl : a = 0 := by omega
    rw [glueLabelVector_zero, map_zero, glueLabelMinimum_E8]
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Every glue-alphabet representative attains the coset minimum norm `glueMinimum`.** -/
@[simp]
theorem rootLattice_form_glueVector_self (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (x : t.glueAlphabet ht) :
    (t.rootLattice ht).form (t.glueVector ht x) (t.glueVector ht x) = t.glueMinimum ht x := by
  rw [glueVector_def, t.rootLattice_form_glueLabelVector_self hv ht
    ((t.glueLabelEquiv ht).symm x).isLt, ← t.glueMinimum_glueLabelEquiv ht, Equiv.apply_symm_apply]

/-- Only the zero glue-alphabet element has representative `0`. -/
@[simp]
theorem glueVector_eq_zero_iff (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    {x : t.glueAlphabet ht} :
    t.glueVector ht x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ t.glueVector_zero ht⟩
  have hmin : t.glueMinimum ht x = 0 := by
    rw [← t.rootLattice_form_glueVector_self hv ht x, h, map_zero]
  exact (t.glueMinimum_eq_zero_iff hv ht).mp hmin

/-- Distinct elements of the glue alphabet have distinct canonical representatives. -/
theorem glueVector_injective (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced) :
    Function.Injective (t.glueVector ht) := by
  intro x y hxy
  have hmk : (Submodule.Quotient.mk (t.glueDualVector hv ht x) :
      (t.rootLattice ht).DiscriminantGroup) =
      Submodule.Quotient.mk (t.glueDualVector hv ht y) :=
    congrArg Submodule.Quotient.mk (Subtype.ext hxy)
  rw [mk_glueDualVector, mk_glueDualVector] at hmk
  exact (t.glueAlphabetIsometry hv ht).injective hmk

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
@[expose] def glueWordVector (w : ∀ i, (t i).glueAlphabet (ht i)) : ∀ i, Fin (t i).rank → ℚ :=
  fun i ↦ (t i).glueVector (ht i) (w i)

/-- Evaluating `glueWordVector` at component `i` gives `(t i).glueVector` of the `i`-th label. -/
@[simp]
theorem glueWordVector_apply (w : ∀ i, (t i).glueAlphabet (ht i)) (i : ι) :
    glueWordVector t ht w i = (t i).glueVector (ht i) (w i) :=
  (rfl)

/-- **The zero glue word is represented by the zero vector.** -/
@[simp]
theorem glueWordVector_zero : glueWordVector t ht 0 = 0 := by
  funext i
  simp

/-- Only the zero glue word has representative `0`. -/
@[simp]
theorem glueWordVector_eq_zero_iff (hv : ∀ i, (t i).Valid)
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
    glueWordVector t ht w ∈ (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  (mem_dualCarrier_pi_iff _ _).mpr fun i ↦ (t i).glueVector_mem_dualCarrier (hv i) (ht i) (w i)

/-- **The canonical dual-lattice representative of a glue word**, bundled in the dual carrier of
the orthogonal sum of component root lattices. -/
noncomputable def glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier :=
  ⟨glueWordVector t ht w, glueWordVector_mem_dualCarrier t ht hv w⟩

/-- Coercing `glueWordDualVector` to the ambient space recovers `glueWordVector`. -/
@[simp]
theorem coe_glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (glueWordDualVector t ht hv w : ∀ i, Fin (t i).rank → ℚ) = glueWordVector t ht w :=
  (rfl)

/-- The dual representative of the zero glue word is `0`. -/
@[simp]
theorem glueWordDualVector_zero (hv : ∀ i, (t i).Valid) :
    glueWordDualVector t ht hv 0 = 0 :=
  Subtype.ext (glueWordVector_zero t ht)

/-- **The dual representative of a glue word `w` projects to `glueWordIsometry t ht hv w`.** -/
@[simp]
theorem mk_glueWordDualVector (hv : ∀ i, (t i).Valid)
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    Submodule.Quotient.mk (glueWordDualVector t ht hv w) = glueWordIsometry t ht hv w := by
  apply (discriminantGroupPiEquiv _).injective
  funext i
  rw [discriminantGroupPiEquiv_mk, discriminantGroupPiEquiv_glueWordIsometry,
    ← (t i).mk_glueDualVector (hv i) (ht i) (w i)]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (coe_piDualCarrierEquiv_apply _ _ _))

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
@[simp]
theorem glueWordVector_mem_gluedLattice_carrier_iff (w : ∀ i, (t i).glueAlphabet (ht i)) :
    glueWordVector t ht w ∈ (gluedLattice t ht hv H hH).carrier ↔ w ∈ H := by
  rw [mem_gluedLattice_carrier_iff]
  have hsymm : (glueWordIsometry t ht hv).toAddEquiv.symm
      (glueWordIsometry t ht hv w) = w :=
    (glueWordIsometry t ht hv).toAddEquiv.symm_apply_apply w
  refine ⟨fun ⟨hx, hw⟩ ↦ ?_, fun hw ↦ ⟨glueWordVector_mem_dualCarrier t ht hv w, ?_⟩⟩
  · have hmk : (Submodule.Quotient.mk ⟨glueWordVector t ht w, hx⟩ :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        Submodule.Quotient.mk (glueWordDualVector t ht hv w) := rfl
    rwa [hmk, mk_glueWordDualVector, hsymm] at hw
  · have hmk : (Submodule.Quotient.mk
        (⟨glueWordVector t ht w, glueWordVector_mem_dualCarrier t ht hv w⟩ :
          (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier) :
        (pi fun i ↦ (t i).rootLattice (ht i)).DiscriminantGroup) =
        Submodule.Quotient.mk (glueWordDualVector t ht hv w) := rfl
    rwa [hmk, mk_glueWordDualVector, hsymm]

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
        Submodule.span ℤ (glueWordVector t ht '' G) :=
  gluedLattice_carrier_eq_sup_span t ht hv H hH hG (glueWordDualVector t ht hv)
    fun w _ ↦ mk_glueWordDualVector t ht hv w

end GluedLattice

end GlueWord

end TauCeti.DynkinType

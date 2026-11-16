/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic

/-!
# Faithful column and row root subgroups of Steinberg groups

For a finite index type `ι`, an associative unital ring `R`, and a fixed index `t : ι`, the column
generators `xᵢₜ(a)` (`i ≠ t`) pairwise commute and assemble via `MonoidHom.noncommPiCoprod` into a
homomorphism `colHom R t : ({i : ι // i ≠ t} → Multiplicative R) →* SteinbergGroup ι R` whose matrix
image under `toGL` is `1 + ∑_{i ≠ t} vᵢ Eᵢₜ`. Dually, the row generators `xₜᵢ(a)` (`i ≠ t`)
assemble into `rowHom R t` with matrix image `1 + ∑_{i ≠ t} vᵢ Eₜᵢ`.

Reading off the off-diagonal entries in column `t` or row `t` shows that `toGL ∘ colHom R t` and
`toGL ∘ rowHom R t` are injective, so both root subgroups are faithful in `SteinbergGroup ι R` and
remain faithful in `GL ι R`. Conjugating `colHom R t` or `rowHom R t` by a generator `xₐᵦ(c)`
avoiding `t` (`a, b ≠ t`) shears the coordinate vector by left or right multiplication by `c`.
Consequently, any element of `SteinbergGroup ι R` supported on indices avoiding `t` normalizes the
column and row root subgroups at `t`, and if its image in `GL ι R` is `1`, faithfulness forces it
to commute with every root generator and therefore to lie in the center of `SteinbergGroup ι R`.

## Main definitions

* `TauCeti.SteinbergGroup.colHom`: the column root subgroup homomorphism `v ↦ ∏_{i ≠ t} xᵢₜ(vᵢ)`.
* `TauCeti.SteinbergGroup.rowHom`: the row root subgroup homomorphism `v ↦ ∏_{i ≠ t} xₜᵢ(vᵢ)`.

## Main results

* `TauCeti.SteinbergGroup.coe_toGL_colHom`, `TauCeti.SteinbergGroup.coe_toGL_rowHom`: matrix
  formulas `1 + ∑_{i ≠ t} vᵢ Eᵢₜ` and `1 + ∑_{i ≠ t} vᵢ Eₜᵢ`.
* `TauCeti.SteinbergGroup.toGL_comp_colHom_injective`,
  `TauCeti.SteinbergGroup.toGL_comp_rowHom_injective`: faithfulness of the column and row root
  subgroups after mapping to `GL ι R`.
* `TauCeti.SteinbergGroup.of_mul_colHom_mul_inv`, `TauCeti.SteinbergGroup.of_mul_rowHom_mul_inv`:
  conjugation of column and row vectors by `xₐᵦ(c)` (`a, b ≠ t`).
* `TauCeti.SteinbergGroup.commute_colHom_of_mem_ker_toGL`,
  `TauCeti.SteinbergGroup.commute_rowHom_of_mem_ker_toGL`: an element of `ker (toGL ι R)` that
  normalizes a column or row root subgroup centralizes it.
* `TauCeti.SteinbergGroup.reindex_mem_center_of_toGL_eq_one`: any element reindexed from a proper
  subset of `ι` that maps to `1` in `GL ι R` is central in `SteinbergGroup ι R`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Lemma 5.1.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1 and Exercise 5.2.
-/

public section

open Matrix

open scoped commutatorElement

namespace TauCeti

namespace SteinbergGroup

variable {ι : Type*} {R : Type*} [Ring R]

section Finite

variable [Fintype ι] [DecidableEq ι]

/-! ## Column root subgroups -/

omit [Fintype ι] [DecidableEq ι] in
private theorem colHom_pairwise (t : ι) :
    Pairwise fun i j : {i : ι // i ≠ t} =>
      ∀ x y : Multiplicative R, Commute (ofHom i.2 x) (ofHom j.2 y) :=
  fun i j _ a b => by
    rw [ofHom_apply, ofHom_apply]
    exact commute_of i.2 j.2 j.2.symm i.2 a.toAdd b.toAdd

variable (R) in
/-- The **column root subgroup homomorphism** at index `t`: sends a vector `(vᵢ)_{i ≠ t}` to the
product `∏_{i ≠ t} xᵢₜ(vᵢ)` of pairwise commuting root generators. -/
def colHom (t : ι) : ({i : ι // i ≠ t} → Multiplicative R) →* SteinbergGroup ι R :=
  MonoidHom.noncommPiCoprod (fun i => ofHom i.2) (colHom_pairwise t)

/-- Evaluating `colHom t` on a single-entry vector yields the corresponding root generator. -/
@[simp]
theorem colHom_mulSingle (t : ι) (i : {i : ι // i ≠ t}) (a : R) :
    colHom R t (Pi.mulSingle i (Multiplicative.ofAdd a)) = of i.2 a := by
  dsimp only [colHom]
  rw [MonoidHom.noncommPiCoprod_mulSingle, ofHom_apply]
  rfl

/-- Auxiliary invertible column matrix `1 + ∑_{i ≠ t} vᵢ Eᵢₜ`. -/
private def colMatrixHom (t : ι) : ({i : ι // i ≠ t} → Multiplicative R) →* GL ι R where
  toFun v :=
    { val := 1 + ∑ i : {i : ι // i ≠ t}, Matrix.single i.1 t (v i).toAdd
      inv := 1 + ∑ i : {i : ι // i ≠ t}, Matrix.single i.1 t (-(v i).toAdd)
      val_inv := by
        simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
        have hzero : ∀ i j : {i : ι // i ≠ t},
            Matrix.single i.1 t (v i).toAdd * Matrix.single j.1 t (-(v j).toAdd) = 0 :=
          fun i j => Matrix.single_mul_single_of_ne _ i.1 t j.1 j.2.symm _
        simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
          ← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
      inv_val := by
        simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
        have hzero : ∀ i j : {i : ι // i ≠ t},
            Matrix.single i.1 t (-(v i).toAdd) * Matrix.single j.1 t (v j).toAdd = 0 :=
          fun i j => Matrix.single_mul_single_of_ne _ i.1 t j.1 j.2.symm _
        simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
          ← Matrix.single_add, neg_add_cancel, Matrix.single_zero] }
  map_one' := Units.ext (by simp)
  map_mul' v w := Units.ext <| by
    simp only [Units.val_mul, add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
    have hzero : ∀ i j : {i : ι // i ≠ t},
        Matrix.single i.1 t (v i).toAdd * Matrix.single j.1 t (w j).toAdd = 0 :=
      fun i j => Matrix.single_mul_single_of_ne _ i.1 t j.1 j.2.symm _
    simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
      ← Matrix.single_add, Pi.mul_apply, toAdd_mul]

/-- The matrix image of `colHom t v` is `1 + ∑_{i ≠ t} vᵢ Eᵢₜ`. -/
theorem coe_toGL_colHom (t : ι) (v : {i : ι // i ≠ t} → Multiplicative R) :
    (toGL ι R (colHom R t v) : Matrix ι ι R) =
      1 + ∑ i : {i : ι // i ≠ t}, Matrix.single i.1 t (v i).toAdd := by
  have heq : (toGL ι R).comp (colHom R t) = colMatrixHom t := by
    refine MonoidHom.pi_ext fun i a => ?_
    rw [MonoidHom.comp_apply]
    have hmul : colHom R t (Pi.mulSingle i a) = of i.2 a.toAdd := by
      simpa using colHom_mulSingle t i a.toAdd
    rw [hmul, toGL_of]
    ext p q
    simp only [colMatrixHom, coe_transvectionUnit_eq_one_add_single, MonoidHom.coe_mk,
      OneHom.coe_mk, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Pi.mulSingle_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      simp [hci]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact congrArg Units.val (DFunLike.congr_fun heq v)

/-- The composite `toGL ∘ colHom t` is injective: each coordinate `vᵢ` is recovered as the
`(i, t)` entry of the image matrix. -/
theorem toGL_comp_colHom_injective (t : ι) :
    Function.Injective ((toGL ι R).comp (colHom R t)) := by
  intro v w hvw
  funext i
  apply Multiplicative.toAdd.injective
  have hentry := congrArg (fun u : GL ι R => (u : Matrix ι ι R) i.1 t) hvw
  simp only [MonoidHom.comp_apply, coe_toGL_colHom, Matrix.add_apply, Matrix.one_apply, i.2,
    ↓reduceIte, zero_add, Matrix.sum_apply, Matrix.single_apply, and_true, Subtype.coe_inj,
    Finset.sum_ite_eq', Finset.mem_univ] at hentry
  exact hentry

/-- The column root subgroup homomorphism `colHom t` is injective. -/
theorem colHom_injective (t : ι) : Function.Injective (colHom R t) :=
  Function.Injective.of_comp (f := toGL ι R) (toGL_comp_colHom_injective t)

/-- Conjugating a column root element `colHom t v` by `xₐᵦ(c)` (`a, b ≠ t`, `a ≠ b`) adds
`c * vᵦ` to the `a`-th coordinate. -/
theorem of_mul_colHom_mul_inv {t a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (c : R)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    of hab c * colHom R t v * (of hab c)⁻¹ =
      colHom R t (v * Pi.mulSingle (M := fun _ : {i : ι // i ≠ t} => Multiplicative R)
        ⟨a, hat⟩ (Multiplicative.ofAdd (c * (v ⟨b, hbt⟩).toAdd))) := by
  let a' : {i : ι // i ≠ t} := ⟨a, hat⟩
  let b' : {i : ι // i ≠ t} := ⟨b, hbt⟩
  let shear : ({i : ι // i ≠ t} → Multiplicative R) →* ({i : ι // i ≠ t} → Multiplicative R) :=
    { toFun := fun w => w * Pi.mulSingle a' (Multiplicative.ofAdd (c * (w b').toAdd))
      map_one' := by simp
      map_mul' := fun w₁ w₂ => by
        funext k
        simp only [Pi.mul_apply, toAdd_mul, mul_add, ofAdd_add]
        by_cases hk : k = a'
        · subst hk
          simp only [Pi.mulSingle_eq_same]
          exact mul_mul_mul_comm _ _ _ _
        · simp [Pi.mulSingle_eq_of_ne hk] }
  have heq : (MulAut.conj (of hab c)).toMonoidHom.comp (colHom R t) = (colHom R t).comp shear := by
    refine MonoidHom.pi_ext fun k x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmul : colHom R t (Pi.mulSingle k x) = of k.2 x.toAdd := by
      simpa using colHom_mulSingle t k x.toAdd
    by_cases hkb : k = b'
    · subst hkb
      rw [hmul, conj_of_right hab hbt hat]
      simp only [shear, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_same, map_mul, hmul,
        colHom_mulSingle]
      exact (commute_of hat hbt hbt.symm hat _ _).eq
    · have hbk : b ≠ k.1 := fun h => hkb (Subtype.ext h.symm)
      rw [hmul, (commute_of hab k.2 hbk hat c x.toAdd).eq, mul_inv_cancel_right]
      simp [shear, Pi.mulSingle_eq_of_ne (Ne.symm hkb), hmul]
  exact DFunLike.congr_fun heq v

/-- Column root subgroups commute with ring homomorphisms. -/
theorem map_colHom {S : Type*} [Ring S] (f : R →+* S) (t : ι)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    map f (colHom R t v) = colHom S t (fun i => Multiplicative.ofAdd (f (v i).toAdd)) := by
  let fVec : ({i : ι // i ≠ t} → Multiplicative R) →* ({i : ι // i ≠ t} → Multiplicative S) :=
    { toFun := fun w i => Multiplicative.ofAdd (f (w i).toAdd)
      map_one' := by ext i; simp
      map_mul' := fun w₁ w₂ => by ext i; simp [← ofAdd_add] }
  have heq : (map f).comp (colHom R t) = (colHom S t).comp fVec := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hmul : colHom R t (Pi.mulSingle k x) = of k.2 x.toAdd := by
      simpa using colHom_mulSingle t k x.toAdd
    have hf : fVec (Pi.mulSingle k x) = Pi.mulSingle k (Multiplicative.ofAdd (f x.toAdd)) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [fVec]
      · simp [fVec, Pi.mulSingle_eq_of_ne hj]
    simp [hmul, hf]
  exact DFunLike.congr_fun heq v

/-! ## Row root subgroups -/

omit [Fintype ι] [DecidableEq ι] in
private theorem rowHom_pairwise (t : ι) :
    Pairwise fun i j : {i : ι // i ≠ t} =>
      ∀ x y : Multiplicative R, Commute (ofHom i.2.symm x) (ofHom j.2.symm y) :=
  fun i j _ a b => by
    rw [ofHom_apply, ofHom_apply]
    exact commute_of i.2.symm j.2.symm i.2 j.2.symm a.toAdd b.toAdd

variable (R) in
/-- The **row root subgroup homomorphism** at index `t`: sends a vector `(vᵢ)_{i ≠ t}` to the
product `∏_{i ≠ t} xₜᵢ(vᵢ)` of pairwise commuting root generators. -/
def rowHom (t : ι) : ({i : ι // i ≠ t} → Multiplicative R) →* SteinbergGroup ι R :=
  MonoidHom.noncommPiCoprod (fun i => ofHom i.2.symm) (rowHom_pairwise t)

/-- Evaluating `rowHom t` on a single-entry vector yields the corresponding root generator. -/
@[simp]
theorem rowHom_mulSingle (t : ι) (i : {i : ι // i ≠ t}) (a : R) :
    rowHom R t (Pi.mulSingle i (Multiplicative.ofAdd a)) = of i.2.symm a := by
  dsimp only [rowHom]
  rw [MonoidHom.noncommPiCoprod_mulSingle, ofHom_apply]
  rfl

/-- Auxiliary invertible row matrix `1 + ∑_{i ≠ t} vᵢ Eₜᵢ`. -/
private def rowMatrixHom (t : ι) : ({i : ι // i ≠ t} → Multiplicative R) →* GL ι R where
  toFun v :=
    { val := 1 + ∑ i : {i : ι // i ≠ t}, Matrix.single t i.1 (v i).toAdd
      inv := 1 + ∑ i : {i : ι // i ≠ t}, Matrix.single t i.1 (-(v i).toAdd)
      val_inv := by
        simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
        have hzero : ∀ i j : {i : ι // i ≠ t},
            Matrix.single t i.1 (v i).toAdd * Matrix.single t j.1 (-(v j).toAdd) = 0 :=
          fun i j => Matrix.single_mul_single_of_ne _ t i.1 t i.2 _
        simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
          ← Matrix.single_add, add_neg_cancel, Matrix.single_zero]
      inv_val := by
        simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
        have hzero : ∀ i j : {i : ι // i ≠ t},
            Matrix.single t i.1 (-(v i).toAdd) * Matrix.single t j.1 (v j).toAdd = 0 :=
          fun i j => Matrix.single_mul_single_of_ne _ t i.1 t i.2 _
        simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
          ← Matrix.single_add, neg_add_cancel, Matrix.single_zero] }
  map_one' := Units.ext (by simp)
  map_mul' v w := Units.ext <| by
    simp only [Units.val_mul, add_mul, mul_add, one_mul, mul_one, Finset.sum_mul, Finset.mul_sum]
    have hzero : ∀ i j : {i : ι // i ≠ t},
        Matrix.single t i.1 (v i).toAdd * Matrix.single t j.1 (w j).toAdd = 0 :=
      fun i j => Matrix.single_mul_single_of_ne _ t i.1 t i.2 _
    simp only [hzero, Finset.sum_const_zero, add_zero, add_assoc, ← Finset.sum_add_distrib,
      ← Matrix.single_add, Pi.mul_apply, toAdd_mul]

/-- The matrix image of `rowHom t v` is `1 + ∑_{i ≠ t} vᵢ Eₜᵢ`. -/
theorem coe_toGL_rowHom (t : ι) (v : {i : ι // i ≠ t} → Multiplicative R) :
    (toGL ι R (rowHom R t v) : Matrix ι ι R) =
      1 + ∑ i : {i : ι // i ≠ t}, Matrix.single t i.1 (v i).toAdd := by
  have heq : (toGL ι R).comp (rowHom R t) = rowMatrixHom t := by
    refine MonoidHom.pi_ext fun i a => ?_
    rw [MonoidHom.comp_apply]
    have hmul : rowHom R t (Pi.mulSingle i a) = of i.2.symm a.toAdd := by
      simpa using rowHom_mulSingle t i a.toAdd
    rw [hmul, toGL_of]
    ext p q
    simp only [rowMatrixHom, coe_transvectionUnit_eq_one_add_single, MonoidHom.coe_mk,
      OneHom.coe_mk, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply, Pi.mulSingle_apply]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      simp [hci]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  exact congrArg Units.val (DFunLike.congr_fun heq v)

/-- The composite `toGL ∘ rowHom t` is injective: each coordinate `vᵢ` is recovered as the
`(t, i)` entry of the image matrix. -/
theorem toGL_comp_rowHom_injective (t : ι) :
    Function.Injective ((toGL ι R).comp (rowHom R t)) := by
  intro v w hvw
  funext i
  apply Multiplicative.toAdd.injective
  have hentry := congrArg (fun u : GL ι R => (u : Matrix ι ι R) t i.1) hvw
  simp only [MonoidHom.comp_apply, coe_toGL_rowHom, Matrix.add_apply, Matrix.one_apply, i.2.symm,
    ↓reduceIte, zero_add, Matrix.sum_apply, Matrix.single_apply, true_and, Subtype.coe_inj,
    Finset.sum_ite_eq', Finset.mem_univ] at hentry
  exact hentry

/-- The row root subgroup homomorphism `rowHom t` is injective. -/
theorem rowHom_injective (t : ι) : Function.Injective (rowHom R t) :=
  Function.Injective.of_comp (f := toGL ι R) (toGL_comp_rowHom_injective t)

/-- Conjugating a row root element `rowHom t v` by `xₐᵦ(c)` (`a, b ≠ t`, `a ≠ b`) adds
`-(vₐ * c)` to the `b`-th coordinate. -/
theorem of_mul_rowHom_mul_inv {t a b : ι} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (c : R)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    of hab c * rowHom R t v * (of hab c)⁻¹ =
      rowHom R t (v * Pi.mulSingle (M := fun _ : {i : ι // i ≠ t} => Multiplicative R)
        ⟨b, hbt⟩ (Multiplicative.ofAdd (-((v ⟨a, hat⟩).toAdd * c)))) := by
  let a' : {i : ι // i ≠ t} := ⟨a, hat⟩
  let b' : {i : ι // i ≠ t} := ⟨b, hbt⟩
  let shear : ({i : ι // i ≠ t} → Multiplicative R) →* ({i : ι // i ≠ t} → Multiplicative R) :=
    { toFun := fun w => w * Pi.mulSingle b' (Multiplicative.ofAdd (-((w a').toAdd * c)))
      map_one' := by simp
      map_mul' := fun w₁ w₂ => by
        funext k
        simp only [Pi.mul_apply, toAdd_mul, add_mul, neg_add, ofAdd_add]
        by_cases hk : k = b'
        · subst hk
          simp only [Pi.mulSingle_eq_same]
          exact mul_mul_mul_comm _ _ _ _
        · simp [Pi.mulSingle_eq_of_ne hk] }
  have heq : (MulAut.conj (of hab c)).toMonoidHom.comp (rowHom R t) = (rowHom R t).comp shear := by
    refine MonoidHom.pi_ext fun k x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmul : rowHom R t (Pi.mulSingle k x) = of k.2.symm x.toAdd := by
      simpa using rowHom_mulSingle t k x.toAdd
    by_cases hka : k = a'
    · subst hka
      rw [hmul, conj_of_left hab hat.symm hbt.symm]
      simp only [shear, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_same, map_mul, hmul,
        rowHom_mulSingle]
      exact (commute_of hbt.symm hat.symm hbt hat.symm _ _).eq
    · have hak : a ≠ k.1 := fun h => hka (Subtype.ext h.symm)
      rw [hmul, (commute_of hab k.2.symm hbt hak c x.toAdd).eq, mul_inv_cancel_right]
      simp [shear, Pi.mulSingle_eq_of_ne (Ne.symm hka), hmul]
  exact DFunLike.congr_fun heq v

/-- Row root subgroups commute with ring homomorphisms. -/
theorem map_rowHom {S : Type*} [Ring S] (f : R →+* S) (t : ι)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    map f (rowHom R t v) = rowHom S t (fun i => Multiplicative.ofAdd (f (v i).toAdd)) := by
  let fVec : ({i : ι // i ≠ t} → Multiplicative R) →* ({i : ι // i ≠ t} → Multiplicative S) :=
    { toFun := fun w i => Multiplicative.ofAdd (f (w i).toAdd)
      map_one' := by ext i; simp
      map_mul' := fun w₁ w₂ => by ext i; simp [← ofAdd_add] }
  have heq : (map f).comp (rowHom R t) = (rowHom S t).comp fVec := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hmul : rowHom R t (Pi.mulSingle k x) = of k.2.symm x.toAdd := by
      simpa using rowHom_mulSingle t k x.toAdd
    have hf : fVec (Pi.mulSingle k x) = Pi.mulSingle k (Multiplicative.ofAdd (f x.toAdd)) := by
      ext j
      by_cases hj : j = k
      · subst hj; simp [fVec]
      · simp [fVec, Pi.mulSingle_eq_of_ne hj]
    simp [hmul, hf]
  exact DFunLike.congr_fun heq v

/-! ## Stabilization of column and row root subgroups -/

/-- Stabilization extends a column root vector by zero (`1` in `Multiplicative R`) on the new
indices. -/
theorem stabilize_colHom {m n : ℕ} (h : m ≤ n) (t : Fin m)
    (v : {i : Fin m // i ≠ t} → Multiplicative R) :
    stabilize R h (colHom R t v) =
      colHom R (Fin.castLE h t) (fun i =>
        if hi : (i.1 : ℕ) < m then
          v ⟨⟨i.1, hi⟩, fun heq => i.2 (Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq))⟩
        else 1) := by
  let extVec : ({i : Fin m // i ≠ t} → Multiplicative R) →*
      ({i : Fin n // i ≠ Fin.castLE h t} → Multiplicative R) :=
    { toFun := fun w i =>
        if hi : (i.1 : ℕ) < m then
          w ⟨⟨i.1, hi⟩, fun heq => i.2 (Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq))⟩
        else 1
      map_one' := funext fun i => by split_ifs <;> rfl
      map_mul' := fun w₁ w₂ => funext fun i => by dsimp only [Pi.mul_apply]; split_ifs <;> simp }
  have heq : (stabilize R h).comp (colHom R t) = (colHom R (Fin.castLE h t)).comp extVec := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hmul : colHom R t (Pi.mulSingle k x) = of k.2 x.toAdd := by
      simpa using colHom_mulSingle t k x.toAdd
    let k' : {i : Fin n // i ≠ Fin.castLE h t} :=
      ⟨Fin.castLE h k.1, (Fin.castLE_injective h).ne k.2⟩
    have hext : extVec (Pi.mulSingle k x) = Pi.mulSingle k' x := by
      funext j
      by_cases hjk : j = k'
      · subst hjk
        simp [extVec, k', k.1.isLt]
      · simp only [extVec, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_of_ne hjk]
        split_ifs with hj
        · apply Pi.mulSingle_eq_of_ne
          intro heq
          exact hjk (Subtype.ext (Fin.ext (congrArg (fun p : {i : Fin m // i ≠ t} => p.1.1) heq)))
        · rfl
    have hmul' : colHom R (Fin.castLE h t) (Pi.mulSingle k' x) = of k'.2 x.toAdd := by
      simpa using colHom_mulSingle (Fin.castLE h t) k' x.toAdd
    simp [hmul, hext, hmul', k']
  exact DFunLike.congr_fun heq v

/-- Stabilization extends a row root vector by zero (`1` in `Multiplicative R`) on the new
indices. -/
theorem stabilize_rowHom {m n : ℕ} (h : m ≤ n) (t : Fin m)
    (v : {i : Fin m // i ≠ t} → Multiplicative R) :
    stabilize R h (rowHom R t v) =
      rowHom R (Fin.castLE h t) (fun i =>
        if hi : (i.1 : ℕ) < m then
          v ⟨⟨i.1, hi⟩, fun heq => i.2 (Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq))⟩
        else 1) := by
  let extVec : ({i : Fin m // i ≠ t} → Multiplicative R) →*
      ({i : Fin n // i ≠ Fin.castLE h t} → Multiplicative R) :=
    { toFun := fun w i =>
        if hi : (i.1 : ℕ) < m then
          w ⟨⟨i.1, hi⟩, fun heq => i.2 (Fin.ext (congrArg (Fin.val : Fin m → ℕ) heq))⟩
        else 1
      map_one' := funext fun i => by split_ifs <;> rfl
      map_mul' := fun w₁ w₂ => funext fun i => by dsimp only [Pi.mul_apply]; split_ifs <;> simp }
  have heq : (stabilize R h).comp (rowHom R t) = (rowHom R (Fin.castLE h t)).comp extVec := by
    refine MonoidHom.pi_ext fun k x => ?_
    have hmul : rowHom R t (Pi.mulSingle k x) = of k.2.symm x.toAdd := by
      simpa using rowHom_mulSingle t k x.toAdd
    let k' : {i : Fin n // i ≠ Fin.castLE h t} :=
      ⟨Fin.castLE h k.1, (Fin.castLE_injective h).ne k.2⟩
    have hext : extVec (Pi.mulSingle k x) = Pi.mulSingle k' x := by
      funext j
      by_cases hjk : j = k'
      · subst hjk
        simp [extVec, k', k.1.isLt]
      · simp only [extVec, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_eq_of_ne hjk]
        split_ifs with hj
        · apply Pi.mulSingle_eq_of_ne
          intro heq
          exact hjk (Subtype.ext (Fin.ext (congrArg (fun p : {i : Fin m // i ≠ t} => p.1.1) heq)))
        · rfl
    have hmul' : rowHom R (Fin.castLE h t) (Pi.mulSingle k' x) = of k'.2.symm x.toAdd := by
      simpa using rowHom_mulSingle (Fin.castLE h t) k' x.toAdd
    simp [hmul, hext, hmul', k']
  exact DFunLike.congr_fun heq v

/-! ## Normalizer invariance and centrality via root subgroups -/

/-- An element of `ker (toGL ι R)` that conjugates a column root element into the column root
subgroup commutes with that element. -/
theorem commute_colHom_of_mem_ker_toGL {z : SteinbergGroup ι R} (hz : toGL ι R z = 1) {t : ι}
    {v : {i : ι // i ≠ t} → Multiplicative R}
    (hconj : z * colHom R t v * z⁻¹ ∈ (colHom R t).range) :
    Commute z (colHom R t v) := by
  obtain ⟨w, hw⟩ := hconj
  have hgl : toGL ι R (colHom R t w) = toGL ι R (colHom R t v) := by
    rw [hw, map_mul, map_mul, map_inv, hz, one_mul, inv_one, mul_one]
  have hwv : w = v := toGL_comp_colHom_injective t hgl
  subst hwv
  exact mul_inv_eq_iff_eq_mul.mp hw.symm

/-- An element of `ker (toGL ι R)` that conjugates a row root element into the row root subgroup
commutes with that element. -/
theorem commute_rowHom_of_mem_ker_toGL {z : SteinbergGroup ι R} (hz : toGL ι R z = 1) {t : ι}
    {v : {i : ι // i ≠ t} → Multiplicative R}
    (hconj : z * rowHom R t v * z⁻¹ ∈ (rowHom R t).range) :
    Commute z (rowHom R t v) := by
  obtain ⟨w, hw⟩ := hconj
  have hgl : toGL ι R (rowHom R t w) = toGL ι R (rowHom R t v) := by
    rw [hw, map_mul, map_mul, map_inv, hz, one_mul, inv_one, mul_one]
  have hwv : w = v := toGL_comp_rowHom_injective t hgl
  subst hwv
  exact mul_inv_eq_iff_eq_mul.mp hw.symm

/-- Every element reindexed along an injection `e : κ → ι` avoiding `t` normalizes the column root
subgroup at `t`. -/
theorem reindex_mul_colHom_mul_inv_mem_range {κ : Type*} (e : κ → ι) (he : Function.Injective e)
    {t : ι} (ht : ∀ k, e k ≠ t) (w : SteinbergGroup κ R)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    reindex R e he w * colHom R t v * (reindex R e he w)⁻¹ ∈ (colHom R t).range := by
  induction w using SteinbergGroup.induction generalizing v with
  | one =>
    refine ⟨v, ?_⟩
    simp
  | of hij a =>
    rw [reindex_of, of_mul_colHom_mul_inv (he.ne hij) (ht _) (ht _) a v]
    exact ⟨_, rfl⟩
  | mul w₁ w₂ hw₁ hw₂ =>
    obtain ⟨v', hv'⟩ := hw₂ v
    have hassoc : reindex R e he (w₁ * w₂) * colHom R t v * (reindex R e he (w₁ * w₂))⁻¹ =
        reindex R e he w₁ * (reindex R e he w₂ * colHom R t v * (reindex R e he w₂)⁻¹) *
          (reindex R e he w₁)⁻¹ := by
      simp [mul_assoc]
    rw [hassoc, ← hv']
    exact hw₁ v'

/-- Every element reindexed along an injection `e : κ → ι` avoiding `t` normalizes the row root
subgroup at `t`. -/
theorem reindex_mul_rowHom_mul_inv_mem_range {κ : Type*} (e : κ → ι) (he : Function.Injective e)
    {t : ι} (ht : ∀ k, e k ≠ t) (w : SteinbergGroup κ R)
    (v : {i : ι // i ≠ t} → Multiplicative R) :
    reindex R e he w * rowHom R t v * (reindex R e he w)⁻¹ ∈ (rowHom R t).range := by
  induction w using SteinbergGroup.induction generalizing v with
  | one =>
    refine ⟨v, ?_⟩
    simp
  | of hij a =>
    rw [reindex_of, of_mul_rowHom_mul_inv (he.ne hij) (ht _) (ht _) a v]
    exact ⟨_, rfl⟩
  | mul w₁ w₂ hw₁ hw₂ =>
    obtain ⟨v', hv'⟩ := hw₂ v
    have hassoc : reindex R e he (w₁ * w₂) * rowHom R t v * (reindex R e he (w₁ * w₂))⁻¹ =
        reindex R e he w₁ * (reindex R e he w₂ * rowHom R t v * (reindex R e he w₂)⁻¹) *
          (reindex R e he w₁)⁻¹ := by
      simp [mul_assoc]
    rw [hassoc, ← hv']
    exact hw₁ v'

/-- **Milnor's centrality lemma at finite rank**: if `e : κ → ι` is an injection missing at least
one index `t : ι`, then any element `reindex R e he w` lying in `ker (toGL ι R)` is central in
`SteinbergGroup ι R`. -/
theorem reindex_mem_center_of_toGL_eq_one {κ : Type*} (e : κ → ι) (he : Function.Injective e)
    (ht : ∃ t : ι, ∀ k, e k ≠ t) {w : SteinbergGroup κ R}
    (hw : toGL ι R (reindex R e he w) = 1) :
    reindex R e he w ∈ Subgroup.center (SteinbergGroup ι R) := by
  obtain ⟨t, ht⟩ := ht
  have hcol : ∀ {i : ι} (hit : i ≠ t) (a : R), Commute (reindex R e he w) (of hit a) := by
    intro i hit a
    rw [← colHom_mulSingle t ⟨i, hit⟩ a]
    exact commute_colHom_of_mem_ker_toGL hw (reindex_mul_colHom_mul_inv_mem_range e he ht w _)
  have hrow : ∀ {j : ι} (htj : t ≠ j) (a : R), Commute (reindex R e he w) (of htj a) := by
    intro j htj a
    rw [← rowHom_mulSingle t ⟨j, htj.symm⟩ a]
    exact commute_rowHom_of_mem_ker_toGL hw (reindex_mul_rowHom_mul_inv_mem_range e he ht w _)
  have hcomm : ∀ y : SteinbergGroup ι R, Commute (reindex R e he w) y := by
    intro y
    induction y using SteinbergGroup.induction with
    | one => simp
    | @of i j hij a =>
      by_cases hjt : j = t
      · subst hjt
        exact hcol hij a
      · by_cases hit : i = t
        · subst hit
          exact hrow hij a
        · have hrepr : of hij a = ⁅of hit a, of (Ne.symm hjt) 1⁆ := by
            rw [commutatorElement_of hit (Ne.symm hjt) hij, mul_one]
          rw [hrepr, commutatorElement_def]
          have hc₁ := hcol hit a
          have hc₂ := hrow (Ne.symm hjt) 1
          exact ((hc₁.mul_right hc₂).mul_right hc₁.inv_right).mul_right hc₂.inv_right
    | mul y₁ y₂ hy₁ hy₂ => exact hy₁.mul_right hy₂
  exact Subgroup.mem_center_iff.mpr fun y => (hcomm y).symm.eq

end Finite

end SteinbergGroup

end TauCeti

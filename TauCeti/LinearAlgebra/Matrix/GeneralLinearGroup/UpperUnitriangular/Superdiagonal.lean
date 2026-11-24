/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `superdiagonalSubgroup` occurs in the statement of `ker_superdiagonalHom`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Nilpotent
-- `transvection` occurs in the statement of `superdiagonalHom_transvection`.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Transvection
-- `Fin.orderSucc_castSucc` and `Finset.Ioo_succ_right_eq_Ioc_of_not_isMax` identify the empty
-- interval `Ioo i.castSucc i.succ` in the proof of `mul_apply_castSucc_succ`.
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Order.SuccPred.Fin

/-!
# The first superdiagonal of the upper-unitriangular group

Let `R` be a ring. The entries on the first superdiagonal of the upper-unitriangular matrices
`Uₙ₊₁(R)` add up under multiplication: no index lies strictly between `i` and `i + 1`, so the
products through intermediate indices in the entry formula for a product of matrices vanish.
Reading the first superdiagonal off is therefore a homomorphism
`TauCeti.UpperUnitriangularGroup.superdiagonalHom` onto `Fin n → R`: the upper-unitriangular matrix
with prescribed entries has arbitrary first superdiagonal. Its kernel is `superdiagonalSubgroup 2`:
an upper-unitriangular matrix has vanishing first superdiagonal exactly when it differs from the
identity only on the second and higher superdiagonals.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.mul_apply_castSucc_succ`: on the first superdiagonal, a product
  of upper-unitriangular matrices has the sum of the entries of its factors.
* `TauCeti.UpperUnitriangularGroup.superdiagonalHom`: the first superdiagonal, as a homomorphism
  to `Fin n → R`.
* `TauCeti.UpperUnitriangularGroup.superdiagonalHom_apply` and
  `TauCeti.UpperUnitriangularGroup.toAdd_superdiagonalHom`: the first superdiagonal of a matrix,
  entry by entry and as a function.
* `TauCeti.UpperUnitriangularGroup.superdiagonalHom_transvection`: the first superdiagonal of a
  transvection.
* `TauCeti.UpperUnitriangularGroup.superdiagonalHom_surjective`: every tuple is the first
  superdiagonal of an upper-unitriangular matrix.
* `TauCeti.UpperUnitriangularGroup.ker_superdiagonalHom`: the kernel is `superdiagonalSubgroup 2`.

## References

* R. W. Carter, *Finite Groups of Lie Type*, Chapter 5.
* F. Digne, J. Michel, *Representations of Finite Groups of Lie Type*, Cambridge University Press,
  1991, §9.1.
-/

public section

open Matrix

namespace TauCeti.UpperUnitriangularGroup

universe u

variable {R : Type u} [Ring R] {n : ℕ}

/-- On the first superdiagonal, a product of upper-unitriangular matrices has the sum of the entries
of its factors: no index lies strictly between `i.castSucc` and `i.succ`. -/
theorem mul_apply_castSucc_succ (g h : upperUnitriangularGroup (Fin (n + 1)) R) (i : Fin n) :
    (((g * h : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ =
      ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ +
        ((h : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ := by
  rw [mul_apply_of_lt g h i.castSucc_lt_succ, ← Fin.orderSucc_castSucc,
    Finset.Ioo_succ_right_eq_Ioc_of_not_isMax (not_isMax_of_lt Fin.castSucc_lt_succ),
    Finset.Ioc_self, Finset.sum_empty, add_zero]

/-- The entries on the first superdiagonal of an upper-unitriangular `(n + 1) × (n + 1)` matrix,
as a homomorphism to the additive group of `Fin n → R`. -/
def superdiagonalHom : upperUnitriangularGroup (Fin (n + 1)) R →* Multiplicative (Fin n → R) where
  toFun u i := ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ
  map_one' := by
    funext i
    simp only [Subgroup.coe_one, Units.val_one, Matrix.one_apply,
      ite_eq_right (Fin.castSucc_lt_succ (i := i)).ne]
    rfl
  map_mul' u v := by
    funext i
    exact congrArg Multiplicative.ofAdd (mul_apply_castSucc_succ u v i)

@[simp]
theorem superdiagonalHom_apply (u : upperUnitriangularGroup (Fin (n + 1)) R) (i : Fin n) :
    superdiagonalHom u i =
      ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ :=
  (rfl)

/-- The first superdiagonal of `u`, as a function on the simple roots. -/
theorem toAdd_superdiagonalHom (u : upperUnitriangularGroup (Fin (n + 1)) R) :
    Multiplicative.toAdd (superdiagonalHom u) = fun i =>
      ((u : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc i.succ :=
  funext fun i => superdiagonalHom_apply u i

/-- The first superdiagonal of a transvection: its entry `c` when the transvection sits on the
first superdiagonal at `(k.castSucc, k.succ)`, and zero otherwise. -/
theorem superdiagonalHom_transvection {i j : Fin (n + 1)} (hij : i < j) (c : R) (k : Fin n) :
    superdiagonalHom (transvection hij c) k = if (i, j) = (k.castSucc, k.succ) then c else 0 := by
  rw [superdiagonalHom_apply, coe_transvection, coe_transvectionUnit_eq_one_add_single]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Prod.mk.injEq,
    ite_eq_right (Fin.castSucc_lt_succ (i := k)).ne, zero_add]

/-- Every tuple is the first superdiagonal of an upper-unitriangular matrix. -/
theorem superdiagonalHom_surjective :
    Function.Surjective (superdiagonalHom (R := R) (n := n)) := by
  intro b
  refine ⟨upperUnitriangularOfEntries fun p =>
    if h : (p : Fin (n + 1) × Fin (n + 1)).2.val = (p : Fin (n + 1) × Fin (n + 1)).1.val + 1 then
      b ⟨(p : Fin (n + 1) × Fin (n + 1)).1.val, by
        have := (p : Fin (n + 1) × Fin (n + 1)).2.isLt
        omega⟩
    else 0, ?_⟩
  funext k
  rw [superdiagonalHom_apply, coe_upperUnitriangularOfEntries_apply,
    unitDiagonalMatrixOfEntries_apply_of_mem _ _ (Fin.castSucc_lt_succ (i := k)).ne
      (Fin.castSucc_lt_succ (i := k))]
  simp

/-- The kernel of `superdiagonalHom` is `U²`: an upper-unitriangular matrix has vanishing first
superdiagonal exactly when it differs from the identity only on the second and higher
superdiagonals. -/
theorem ker_superdiagonalHom :
    (superdiagonalHom (R := R) (n := n)).ker = superdiagonalSubgroup 2 := by
  ext g
  rw [MonoidHom.mem_ker, mem_superdiagonalSubgroup_iff]
  constructor
  · intro hg i j hij
    have hzero (k : Fin n) : ((g : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        k.castSucc k.succ = 0 := by
      rw [← superdiagonalHom_apply, hg]
      rfl
    by_cases hji : j < i
    · rw [isUpperTriangular g hji, Matrix.one_apply_ne (ne_of_gt hji)]
    · by_cases hij' : i = j
      · subst hij'
        rw [apply_diag, Matrix.one_apply_eq]
      · have hj' : j.val = i.val + 1 := by omega
        have hi : i.val < n := by
          have := j.isLt
          omega
        have hi' : i = (⟨i.val, hi⟩ : Fin n).castSucc := Fin.ext rfl
        have hj'' : j = (⟨i.val, hi⟩ : Fin n).succ := Fin.ext hj'
        rw [hi', hj'', hzero _, Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := ⟨i.val, hi⟩)).ne]
  · intro hg
    refine (funext_iff).mpr fun k => ?_
    have hv : (k.succ : Fin (n + 1)).val < (k.castSucc : Fin (n + 1)).val + 2 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [superdiagonalHom_apply, hg k.castSucc k.succ hv,
      Matrix.one_apply_ne (Fin.castSucc_lt_succ (i := k)).ne]
    rfl

end TauCeti.UpperUnitriangularGroup

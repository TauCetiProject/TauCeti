/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Finite
public import TauCeti.Algebra.TypeAHeckeAlgebra.GroupAlgebra

/-!
# The additive Jucys–Murphy elements at the group-algebra fibers

Under the canonical group-algebra comparison at `q = q⁻¹`, the additive element on
strand `k` is `q⁻¹` times the sum of the transpositions `(j,k)` for `j < k`. In particular,
at `q = 1` these are the ordinary Jucys–Murphy elements, not a specialization obtained by
dividing by `q² - 1`. At `q = -1` the same comparison gives their negatives.

The comparison is over an arbitrary commutative ring, including characteristic two.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

open BraidGroup

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}

/-- At `q = q⁻¹`, the additive Jucys–Murphy element is `q⁻¹` times the sum of the
transpositions joining its strand to each earlier strand. At `q = 1` this is the ordinary
Jucys–Murphy element; at `q = -1` it is its negative.

Use this comparison by rewriting: adding the hypothesis `q = q⁻¹` to a simp set can
rewrite the parameter repeatedly underneath inverses. -/
theorem groupAlgebraEquiv_additiveJucysMurphy (hq : q = q⁻¹) (k : Fin n) :
    groupAlgebraEquiv (permCoxeterSystem n) hq (additiveJucysMurphy q k) =
      ∑ j : Fin k.val, MonoidAlgebra.single
        (Equiv.swap (j.castLE (Nat.le_of_lt k.isLt)) k) (↑q⁻¹ : R) := by
  cases n with
  | zero => exact Fin.elim0 k
  | succ n =>
    induction k using Fin.induction with
    | zero =>
      rw [additiveJucysMurphy_zero, map_zero]
      exact (Finset.sum_eq_zero fun j _ ↦ Fin.elim0 j).symm
    | succ i ih =>
      rw [additiveJucysMurphy_succ, map_add, map_mul, map_mul, map_smul, ih]
      simp only [groupAlgebraEquiv_T, permCoxeterSystem_simple, Fin.val_succ,
        Fin.sum_univ_castSucc, Finset.mul_sum, Finset.sum_mul,
        MonoidAlgebra.single_mul_single, one_mul, mul_one]
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        have hj : j.castLE (Nat.le_of_lt i.castSucc.isLt) ≠ i.castSucc := by
          intro h
          exact (Nat.ne_of_lt j.isLt) (congrArg Fin.val h)
        have hj' : j.castLE (Nat.le_of_lt i.castSucc.isLt) ≠ i.succ := by
          intro h
          have hv := congrArg Fin.val h
          have hjlt := j.isLt
          simp only [Fin.val_castLE, Fin.val_succ, Fin.val_castSucc] at hv hjlt
          omega
        have hc : transposition (n := n + 1) i *
            Equiv.swap (j.castLE (Nat.le_of_lt i.castSucc.isLt)) i.castSucc *
              transposition (n := n + 1) i =
            Equiv.swap (j.castSucc.castLE (Nat.le_of_lt i.succ.isLt)) i.succ := by
          rw [Equiv.mul_swap_eq_swap_mul, mul_assoc, transposition_mul_self, mul_one]
          simp only [transposition_eq_swap_castSucc_succ,
            Equiv.swap_apply_of_ne_of_ne hj hj', Equiv.swap_apply_left,
            Fin.castLE_castSucc]
        exact congrArg (fun w ↦ MonoidAlgebra.single w (↑q⁻¹ : R)) hc
      · have hlast : (Fin.last i.val).castLE (Nat.le_of_lt i.succ.isLt) =
            i.castSucc := Fin.ext (by simp)
        simp only [MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
          transposition_eq_swap_castSucc_succ, hlast]

end TauCeti.TypeAHeckeAlgebra

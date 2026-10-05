/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.RootsBelow
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import TauCeti.Algebra.MvPolynomial.Rename
import TauCeti.RingTheory.Polynomial.Reductum
import TauCeti.RingTheory.Polynomial.Subresultant.CauchyIndex

/-!
# Root counts of polynomial families are semialgebraic

A polynomial `P : (MvPolynomial σ R)[X]` is a family of univariate polynomials
`P.map (MvPolynomial.eval x)` parametrized by `x : σ → R`. This file shows that the number of
distinct roots of the specialized polynomial, and the number of its distinct roots below a point
`t = T(x)` given by a polynomial `T`, are described by finitely many polynomial sign conditions on
the parameters. So the sets of parameters with a prescribed count are semialgebraic. In the
cylinder coordinates of `TauCeti.cylinder`, this describes, without any projection, the loci of a
family over `R ^ n` where the distinguished coordinate is a root, respectively not a root, with a
prescribed number of roots below it. Over base points where the family does not specialize to zero,
these are the graph of the `i`-th distinct root and the `j`-th sector, where the sectors are counted
from below and include the two unbounded outer sectors.

The specialized degree is described by the vanishing of the coefficients of `P`. Where it equals
`d`, the specialization is the specialization of the reductum of `P` below `d + 1`, and the formal
bounds `d` and `d - 1` of this reductum and its derivative are the actual degrees there. Their
signed principal subresultant coefficients are polynomials in the parameters, and the number of
distinct roots is the permanences minus variations of their values
(`Polynomial.card_roots_toFinset_eq_permanencesMinusVariations_signedPsc`). Roots below `t` are
counted as roots of `p.comp (C t - X ^ 2)` (`Polynomial.card_roots_toFinset_comp_C_sub_X_sq`),
whose coefficients are again polynomials in the parameters.

Zero specializations, whose zero set is the whole line, are separated explicitly. By convention
their `Polynomial.roots` is empty, so they lie in the sets with count zero.

## Main declarations

* `TauCeti.isSemialgebraic_setOf_map_eval_eq_zero`,
  `TauCeti.isSemialgebraic_setOf_natDegree_map_eval_eq`: the parameters with a zero specialization,
  and with a prescribed specialized degree.
* `TauCeti.isSemialgebraic_setOf_card_roots_map_eval`: the parameters whose specialization has a
  prescribed number of distinct roots.
* `TauCeti.isSemialgebraic_setOf_card_roots_map_eval_lt`: the parameters whose specialization has a
  prescribed number of distinct roots below `T(x)`.
* `TauCeti.isSemialgebraic_setOf_isRoot_card_roots_lt`,
  `TauCeti.isSemialgebraic_setOf_not_isRoot_card_roots_lt`: the root locus with `i` roots below
  and the non-root locus with `j` roots below of a family over `R ^ n`, as subsets of
  `R ^ (n + 1)`. Over nonzero fibers these are the graph of the `i`-th root and the `j`-th sector.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapters 4 and 10 (root counting by signed subresultants and uniform sign
descriptions).
-/

public section

open Polynomial Set

namespace TauCeti

section CommRing

variable {σ R : Type*} [CommRing R] [LinearOrder R]

/-- The parameters at which a polynomial family specializes to zero form a semialgebraic set. -/
theorem isSemialgebraic_setOf_map_eval_eq_zero (P : (MvPolynomial σ R)[X]) :
    IsSemialgebraic {x : σ → R | P.map (MvPolynomial.eval x) = 0} := by
  simpa [Polynomial.ext_iff] using isSemialgebraic_setOf_forall_coeff_eq_zero P univ

/-- The parameters at which the specialization of a polynomial family has degree at most `d` form
a semialgebraic set. -/
theorem isSemialgebraic_setOf_natDegree_map_eval_le (P : (MvPolynomial σ R)[X]) (d : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).natDegree ≤ d} := by
  simpa [natDegree_le_iff_coeff_eq_zero] using isSemialgebraic_setOf_forall_coeff_eq_zero P (Ioi d)

/-- The parameters at which the specialization of a polynomial family has degree exactly `d` form
a semialgebraic set. The zero specializations have degree `0`. -/
theorem isSemialgebraic_setOf_natDegree_map_eval_eq (P : (MvPolynomial σ R)[X]) (d : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).natDegree = d} := by
  cases d with
  | zero => simpa using isSemialgebraic_setOf_natDegree_map_eval_le P 0
  | succ d =>
    convert (isSemialgebraic_setOf_natDegree_map_eval_le P (d + 1)).sdiff
      (isSemialgebraic_setOf_natDegree_map_eval_le P d) using 1
    ext x
    simp only [mem_ofPred_eq, mem_sdiff]
    omega

end CommRing

section RealClosed

variable {σ R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **Uniform root count.** The parameters at which the specialization of a polynomial family has
exactly `k` distinct roots form a semialgebraic set. A zero specialization has no roots in
`Polynomial.roots`, so it counts towards `k = 0`; the zero specializations themselves form the
semialgebraic set of `TauCeti.isSemialgebraic_setOf_map_eval_eq_zero`. -/
theorem isSemialgebraic_setOf_card_roots_map_eval (P : (MvPolynomial σ R)[X]) (k : ℕ) :
    IsSemialgebraic {x : σ → R | (P.map (MvPolynomial.eval x)).roots.toFinset.card = k} := by
  -- The signed principal subresultant coefficients of the reductum below `d + 1` and its
  -- derivative, at the formal degrees `d` and `d - 1`.
  set s : ℕ → ℕ → MvPolynomial σ R := fun d =>
    signedPsc (P.reductum (d + 1)) (derivative (P.reductum (d + 1))) d (d - 1)
  have hcount (x : σ → R) {d : ℕ} (hd : (P.map (MvPolynomial.eval x)).natDegree = d) :
      ((P.map (MvPolynomial.eval x)).roots.toFinset.card : ℤ) =
        (((List.range (d + 1)).reverse.map (s d)).map
          (MvPolynomial.eval x)).permanencesMinusVariations := by
    rw [card_roots_toFinset_eq_permanencesMinusVariations_signedPsc, natDegree_derivative, hd]
    have hP : P.map (MvPolynomial.eval x) = (P.reductum (d + 1)).map (MvPolynomial.eval x) := by
      rw [← hd, map_reductum_natDegree_map_add_one]
    have hs : signedPsc ((P.reductum (d + 1)).map (MvPolynomial.eval x))
        ((derivative (P.reductum (d + 1))).map (MvPolynomial.eval x)) d (d - 1) =
          fun j => MvPolynomial.eval x (s d j) :=
      funext fun j => signedPsc_map_map _ _ _ _ _ _
    rw [hP, derivative_map, hs, List.map_map, Function.comp_def]
  have : {x : σ → R | (P.map (MvPolynomial.eval x)).roots.toFinset.card = k} =
      ⋃ d ∈ Iic P.natDegree, {x | (P.map (MvPolynomial.eval x)).natDegree = d} ∩
        {x | (((List.range (d + 1)).reverse.map (s d)).map
          (MvPolynomial.eval x)).permanencesMinusVariations = k} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_Iic, exists_prop]
    constructor
    · intro h
      refine ⟨_, natDegree_map_le, rfl, ?_⟩
      rw [← hcount x rfl, h]
    · rintro ⟨d, -, hd, h⟩
      exact_mod_cast (hcount x hd).trans h
  rw [this]
  exact .biUnion (finite_Iic _) fun d _ => (isSemialgebraic_setOf_natDegree_map_eval_eq P d).inter
    (isSemialgebraic_setOf_permanencesMinusVariations_eval _ _)

/-- **Uniform count of the roots below a point.** For polynomials `P` and `T`, the parameters `x`
at which the specialization of `P` has exactly `k` distinct roots below `T(x)` form a semialgebraic
set. A zero specialization has no roots in `Polynomial.roots`, so it counts towards `k = 0`. -/
theorem isSemialgebraic_setOf_card_roots_map_eval_lt (P : (MvPolynomial σ R)[X])
    (T : MvPolynomial σ R) (k : ℕ) :
    IsSemialgebraic
      {x : σ → R | {r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset |
        r < MvPolynomial.eval x T}.card = k} := by
  classical
  -- The roots of the specialization below `T(x)` are counted by the roots of the specialization
  -- of `P.comp (C T - X ^ 2)` and by whether `T(x)` is itself a root.
  set Q := P.comp (C T - X ^ 2)
  have hQ (x : σ → R) : Q.map (MvPolynomial.eval x) =
      (P.map (MvPolynomial.eval x)).comp (C (MvPolynomial.eval x T) - X ^ 2) := by
    simp [Q, Polynomial.map_comp]
  -- Zero specializations count towards `k = 0` only; elsewhere the count is read off from the
  -- root count of the specialization of `Q` and whether `T(x)` is a root.
  have : {x : σ → R | {r ∈ (P.map (MvPolynomial.eval x)).roots.toFinset |
        r < MvPolynomial.eval x T}.card = k} =
      {x | P.map (MvPolynomial.eval x) = 0 ∧ k = 0} ∪
        {x | P.map (MvPolynomial.eval x) = 0}ᶜ ∩
          ({x | MvPolynomial.eval x (P.eval T) = 0} ∩
              {x | (Q.map (MvPolynomial.eval x)).roots.toFinset.card = 2 * k + 1} ∪
            {x | MvPolynomial.eval x (P.eval T) ≠ 0} ∩
              {x | (Q.map (MvPolynomial.eval x)).roots.toFinset.card = 2 * k}) := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases h0 : P.map (MvPolynomial.eval x) = 0
    · simp [h0, eq_comm]
    have hroot : (P.map (MvPolynomial.eval x)).IsRoot (MvPolynomial.eval x T) ↔
        MvPolynomial.eval x (P.eval T) = 0 := by
      rw [IsRoot.def, eval_map_apply]
    rw [hQ, card_roots_toFinset_comp_C_sub_X_sq h0]
    by_cases hr : MvPolynomial.eval x (P.eval T) = 0
    · simp only [h0, hr, hroot.mpr hr, ↓reduceIte, false_and, false_or, not_false_eq_true,
        true_and, ne_eq, not_true_eq_false, or_false]
      omega
    · simp only [h0, hr, mt hroot.mp hr, ↓reduceIte, false_and, false_or, not_false_eq_true,
        true_and, ne_eq]
      omega
  have hZ := isSemialgebraic_setOf_map_eval_eq_zero P
  rw [this]
  refine .union ?_ (hZ.compl.inter
    (((isSemialgebraic_eval_eq_zero _).inter (isSemialgebraic_setOf_card_roots_map_eval Q _)).union
      ((isSemialgebraic_eval_ne_zero _).inter (isSemialgebraic_setOf_card_roots_map_eval Q _))))
  rcases eq_or_ne k 0 with rfl | hk
  · simpa using hZ
  · simp [hk]

/-! ### Roots and sectors in cylinder coordinates

A family `P : (MvPolynomial (Fin n) R)[X]` over `R ^ n` has its root graphs and sectors in
`R ^ (n + 1)`, with the distinguished coordinate `0` as for `TauCeti.cylinder`. Over a base point
where the specialization at `Fin.tail y` is nonzero, a point `y` lies on the graph of the `i`-th
distinct root of `P` (counted from `0`) when `y 0` is a root with exactly `i` roots below it, and in
the `j`-th sector when `y 0` is not a root and has exactly `j` roots below it. The sectors are
counted from below: sector `0` lies below the smallest root, the last one above the largest root,
and over a fiber without roots sector `0` is the whole fiber. Over a base point where `P`
specializes to zero, the root predicate holds on the whole fiber for `i = 0` and nowhere else, and
the non-root predicate holds nowhere. -/

variable {n : ℕ}

/-- **The root locus with `i` roots below.** The points of `R ^ (n + 1)` whose coordinate `0` is a
root of the specialization of `P` at the remaining coordinates, with exactly `i` distinct roots
below it, form a semialgebraic set. Over a base point where `P` does not specialize to zero, this is
the graph of the `i`-th distinct root (counted from `0`). Over a base point where `P` specializes to
zero, it is the whole fiber for `i = 0` and empty otherwise. -/
theorem isSemialgebraic_setOf_isRoot_card_roots_lt (P : (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R | (P.map (MvPolynomial.eval (Fin.tail y))).IsRoot (y 0) ∧
      {r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | r < y 0}.card = i} := by
  -- The family over `R ^ (n + 1)` whose specialization at `y` is that of `P` at `Fin.tail y`.
  set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert (isSemialgebraic_eval_eq_zero (Q.eval (MvPolynomial.X 0))).inter
    (isSemialgebraic_setOf_card_roots_map_eval_lt Q (MvPolynomial.X 0) i) using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, IsRoot.def, ← eval_map_apply, Q, map_eval_map_rename,
    MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

/-- **The non-root locus with `j` roots below.** The points of `R ^ (n + 1)` whose coordinate `0`
is not a root of the specialization of `P` at the remaining coordinates, with exactly `j` distinct
roots below it, form a semialgebraic set. Over a base point where `P` does not specialize to zero,
this is the `j`-th sector counted from below, including the unbounded sectors below the smallest
and above the largest root. Over a base point where `P` specializes to zero there are no such
points. -/
theorem isSemialgebraic_setOf_not_isRoot_card_roots_lt (P : (MvPolynomial (Fin n) R)[X])
    (j : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      ¬ (P.map (MvPolynomial.eval (Fin.tail y))).IsRoot (y 0) ∧
      {r ∈ (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset | r < y 0}.card = j} := by
  -- The family over `R ^ (n + 1)` whose specialization at `y` is that of `P` at `Fin.tail y`.
  set Q := P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert (isSemialgebraic_eval_ne_zero (Q.eval (MvPolynomial.X 0))).inter
    (isSemialgebraic_setOf_card_roots_map_eval_lt Q (MvPolynomial.X 0) j) using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, IsRoot.def, ← eval_map_apply, Q, map_eval_map_rename,
    MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

end RealClosed

end TauCeti

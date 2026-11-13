/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.IsoClass
public import TauCeti.GroupTheory.Perm.TransitiveCount
import TauCeti.GroupTheory.Finiteness
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Counting connected triples and marked classes

A permutation triple of degree `m` is a pair of permutations of `Fin m`, that is, a
representation of the free group of rank two on `Fin m`, and it is connected exactly when
that representation is transitive. Splitting a pair of permutations of `Fin (n + 1)` along the
monodromy orbit of `0` therefore gives the recursion

```text
((n + 1)!)² = ∑_{k=0}^{n} C(n, k) · #ConnectedTriple (k + 1) · ((n - k)!)²
```

which determines the number of connected triples in every degree. Relabeling acts freely on
connected triples with a marked sheet (`TauCeti.MarkedIsoClass.natCard_mul_factorial`), so
the number `a_m` of marked classes of degree `m` satisfies Hall's recursion

```text
(n + 1) · (n + 1)! = ∑_{k=0}^{n} a_{k+1} · (n - k)!
```

and the first values are `1, 3, 13, 71, 461`. Marked classes of degree `m` are the
combinatorial invariant of pointed connected `m`-sheeted covers of the thrice-punctured
sphere, and so correspond to the subgroups of index `m` of its fundamental group, a free group
of rank two; these are Hall's numbers of such subgroups.

## Main results

* `TauCeti.ConnectedTriple.sum_choose_mul_card_mul_factorial_sq`: the recursion for the number
  of connected triples.
* `TauCeti.MarkedIsoClass.sum_natCard_mul_factorial`: Hall's recursion for the number of
  marked classes.
* `TauCeti.MarkedIsoClass.natCard_two`, …, `TauCeti.MarkedIsoClass.natCard_five`: there are
  `3`, `13`, `71` and `461` marked classes in degrees two to five.

## References

* M. Hall, Jr., *Subgroups of finite index in free groups*, Canad. J. Math. 1 (1949), 187–190.
-/

public section

open Equiv Finset MulAction

namespace TauCeti

/-- Connected triples of positive degree are the transitive representations of the free group
of rank two, sending the two generators to the first two components. -/
private def connectedTripleEquiv (k : ℕ) :
    ConnectedTriple (k + 1) ≃
      {ρ : FreeGroup (Fin 2) →* Perm (Fin (k + 1)) // IsPretransitive ρ.range (Fin (k + 1))} :=
  ((PermutationTriple.equivPair (k + 1)).trans
    ((piFinTwoEquiv fun _ => Perm (Fin (k + 1))).symm.trans FreeGroup.lift)).subtypeEquiv
    fun t => by
      have hrange : (FreeGroup.lift ((piFinTwoEquiv fun _ => Perm (Fin (k + 1))).symm
          (t.σ0, t.σ1))).range = t.monodromyGroup := by
        rw [FreeGroup.range_lift_eq_closure, ← PermutationTriple.closure_pair_eq_monodromyGroup]
        congr 1
        ext σ
        simp
      rw [Equiv.trans_apply, Equiv.trans_apply, PermutationTriple.equivPair_apply, hrange,
        PermutationTriple.isConnected_iff]
      simp

namespace ConnectedTriple

/-- **The orbit recursion for connected triples.** A pair of permutations of `Fin (n + 1)` is
determined by the monodromy orbit of `0`, of some size `k + 1`, a connected triple on that
orbit, and an arbitrary pair of permutations of the remaining `n - k` sheets. -/
theorem sum_choose_mul_card_mul_factorial_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k *
      (Fintype.card (ConnectedTriple (k + 1)) * (n - k).factorial ^ 2) =
        (n + 1).factorial ^ 2 := by
  -- A pair of permutations of `Fin m` is a representation of the free group of rank two.
  have hpairs (m : ℕ) : Nat.card (FreeGroup (Fin 2) →* Perm (Fin m)) = m.factorial ^ 2 := by
    simp [FreeGroup.natCard_monoidHom, Fintype.card_perm]
  rw [← hpairs, natCard_monoidHom_perm_fin_succ_eq_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [← Nat.card_eq_fintype_card, Nat.card_congr (connectedTripleEquiv k), hpairs]

end ConnectedTriple

namespace MarkedIsoClass

/-- **Hall's recursion** for the number of marked classes of connected triples: with `a_m` the
number of marked classes of degree `m`, `∑_{k=0}^{n} a_{k+1} · (n - k)! = (n + 1) · (n + 1)!`.
Through `TauCeti.MarkedIsoClass.subgroupEquiv`, `a_m` is also the number of subgroups of index
`m` of the fundamental group of the thrice-punctured sphere. -/
theorem sum_natCard_mul_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), Nat.card (MarkedIsoClass (k + 1)) * (n - k).factorial =
      (n + 1) * (n + 1).factorial := by
  -- Each term of the recursion for connected triples is `n!` times the corresponding term here.
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      n.choose k * (Fintype.card (ConnectedTriple (k + 1)) * (n - k).factorial ^ 2) =
        n.factorial * (Nat.card (MarkedIsoClass (k + 1)) * (n - k).factorial) := by
    have hk : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    have hfree := natCard_mul_factorial (n := k + 1)
    rw [Nat.factorial_succ, mul_left_comm, mul_comm (Nat.card _)] at hfree
    rw [← Nat.choose_mul_factorial_mul_factorial hk,
      ← Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hfree]
    ring
  have h := ConnectedTriple.sum_choose_mul_card_mul_factorial_sq n
  rw [sum_congr rfl hterm, ← mul_sum, Nat.factorial_succ (n := n), sq] at h
  refine Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos n) ?_
  rw [h, Nat.factorial_succ]
  ring

/-- There is one marked class of degree one. -/
theorem natCard_one : Nat.card (MarkedIsoClass 1) = 1 := by
  simpa using sum_natCard_mul_factorial 0

/-- There are three marked classes of degree two. -/
theorem natCard_two : Nat.card (MarkedIsoClass 2) = 3 := by
  have h := sum_natCard_mul_factorial 1
  simp [sum_range_succ, Nat.factorial, natCard_one] at h
  omega

/-- There are thirteen marked classes of degree three. -/
theorem natCard_three : Nat.card (MarkedIsoClass 3) = 13 := by
  have h := sum_natCard_mul_factorial 2
  simp [sum_range_succ, Nat.factorial, natCard_one, natCard_two] at h
  omega

/-- There are seventy-one marked classes of degree four. -/
theorem natCard_four : Nat.card (MarkedIsoClass 4) = 71 := by
  have h := sum_natCard_mul_factorial 3
  simp [sum_range_succ, Nat.factorial, natCard_one, natCard_two, natCard_three] at h
  omega

/-- There are four hundred sixty-one marked classes of degree five. -/
theorem natCard_five : Nat.card (MarkedIsoClass 5) = 461 := by
  have h := sum_natCard_mul_factorial 4
  simp [sum_range_succ, Nat.factorial, natCard_one, natCard_two, natCard_three,
    natCard_four] at h
  omega

end MarkedIsoClass

end TauCeti

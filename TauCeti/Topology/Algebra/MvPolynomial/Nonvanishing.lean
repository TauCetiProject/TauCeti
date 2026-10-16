/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Topology.Perfect

/-!
# Density of polynomial nonvanishing

A nonzero multivariate polynomial over a domain with a perfect T1 topology is nonzero on
a dense set of assignments. This includes infinitely many variables: every nonempty open
set contains a box restricting only finitely many coordinates, with infinite sides.
No continuity of the ring operations is needed for density.

Applied to the first nonzero homogeneous Taylor component, this lets one choose directions
detecting ambient polynomial order inside any nonempty open set.
The algebraic input is Mathlib's `MvPolynomial.funext_set`.
-/

public section

open Set

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R]
  [T1Space R] [PerfectSpace R]

/-- A nonzero polynomial is nonzero on a dense set, even with infinitely many variables.
Only the perfect T1 topology on the coefficient domain is needed. -/
theorem dense_setOf_eval_ne_zero (p : MvPolynomial σ R) (hp : p ≠ 0) :
    Dense {x : σ → R | eval x p ≠ 0} := by
  classical
  refine dense_iff_inter_open.2 fun U hU ⟨a, ha⟩ ↦ ?_
  obtain ⟨I, s, hs, hsU⟩ := isOpen_pi_iff.1 hU a ha
  let t (i : σ) : Set R := if i ∈ I then s i else univ
  have ht (i : σ) : (t i).Infinite := by
    by_cases hi : i ∈ I
    · exact infinite_of_mem_nhds (a i) (by simpa [t, hi] using
        ((hs i hi).1.mem_nhds (hs i hi).2))
    · simpa [t, hi] using infinite_of_mem_nhds (0 : R) Filter.univ_mem
  have hbox : univ.pi t ⊆ U := by
    simpa only [t, ← Finset.mem_coe, univ_pi_ite] using hsU
  by_contra h
  apply hp
  apply funext_set t ht
  intro x hx
  have hzero : eval x p = 0 := by
    by_contra hne
    exact h ⟨x, hbox hx, hne⟩
  simpa using hzero

end MvPolynomial

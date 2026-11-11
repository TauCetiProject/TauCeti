/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Finiteness
import TauCeti.Data.Finsupp.Weight
import Mathlib.Algebra.Group.Submonoid.Finsupp
import Mathlib.Tactic.Positivity

/-!
# Positive integral degrees on finitely generated additive monoids

An integral additive functional strictly positive on the nonzero elements of a finitely
generated additive submonoid has finite sublevel sets. Thus finite generation supplies the
finiteness needed to truncate a grading, without any freeness or lattice hypothesis.

We also compare two integral functionals on such a monoid: if the second is strictly
positive away from zero, then a fixed natural multiple of it bounds the first. Applied to
a functional pulled back along a homomorphism, this gives linear cutoff moduli for maps
of positive gradings.

The finite-sublevel proof uses Mathlib's finite sets of bounded-degree exponent vectors;
zero generators are removed before bounding the number of summands.
-/

public section

namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M] {P : AddSubmonoid M}

/-- A finitely generated additive submonoid with an integral degree strictly positive away
from zero has finite degree cutoffs. The ambient monoid need not be cancellative. -/
theorem FG.finite_degree_le (hP : P.FG) (δ : M →+ ℤ)
    (hδ : ∀ x ∈ P, x ≠ 0 → 0 < δ x) (k : ℕ) :
    {x : M | x ∈ P ∧ δ x ≤ k}.Finite := by
  classical
  obtain ⟨s, hs, hfin⟩ := (fg_iff P).mp hP
  let t := s \ {0}
  have ht : closure t = P := by
    simpa [t] using (closure_sdiff_singleton_zero s).trans hs
  have htfin : t.Finite := hfin.subset Set.sdiff_subset
  let : Finite t := htfin.to_subtype
  let a : t → M := Subtype.val
  have ha : ∀ i, 1 ≤ δ (a i) := by
    intro i
    have hi : a i ∈ P := ht ▸ subset_closure i.property
    have hne : a i ≠ 0 := i.property.2
    exact hδ _ hi hne
  have hbound (u : t →₀ ℕ) :
      (u.degree : ℤ) ≤ δ (Finsupp.linearCombination ℕ a u) := by
    rw [← Finsupp.weight_comp_eq_apply_linearCombination δ a u]
    simp only [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum,
      nsmul_eq_mul, Function.comp_apply]
    exact Finset.sum_le_sum fun i _ ↦ le_mul_of_one_le_right (by positivity) (ha i)
  refine ((Finsupp.finite_of_degree_le (σ := t) k).image
    (Finsupp.linearCombination ℕ a)).subset ?_
  rintro x ⟨hx, hk⟩
  have hx' : x ∈ closure (Set.range a) := by
    simpa [a, ht] using hx
  obtain ⟨u, hu⟩ := mem_closure_range_iff.mp hx'
  have hu' : Finsupp.linearCombination ℕ a u = x := by
    simpa [Finsupp.linearCombination_apply] using hu.symm
  refine ⟨u, ?_, hu'⟩
  have hb := hbound u
  rw [hu'] at hb
  exact_mod_cast hb.trans hk

/-- On a finitely generated additive submonoid, an integral functional strictly positive
away from zero dominates every integral functional up to a fixed natural factor.
No sign condition is needed on the functional being bounded. -/
theorem FG.exists_degree_le_mul (hP : P.FG) (δ ε : M →+ ℤ)
    (hε : ∀ x ∈ P, x ≠ 0 → 0 < ε x) :
    ∃ c : ℕ, ∀ x ∈ P, δ x ≤ (c : ℤ) * ε x := by
  classical
  obtain ⟨s, hs⟩ := isAddFG_iff.mp hP
  let c := s.sup fun x ↦ (δ x).toNat
  refine ⟨c, ?_⟩
  intro x hx
  have hx' : x ∈ closure (s : Set M) := hs ▸ hx
  clear hx
  induction hx' using closure_induction with
  | mem x hx =>
      by_cases hzero : x = 0
      · simp [hzero]
      have hpos : 1 ≤ ε x := hε x (hs ▸ subset_closure hx) hzero
      have hle : (δ x).toNat ≤ c := Finset.le_sup (f := fun x ↦ (δ x).toNat) hx
      calc
        δ x ≤ ((δ x).toNat : ℤ) := by omega
        _ ≤ (c : ℤ) := by exact_mod_cast hle
        _ ≤ (c : ℤ) * ε x := le_mul_of_one_le_right (by positivity) hpos
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using add_le_add hx hy

end AddSubmonoid

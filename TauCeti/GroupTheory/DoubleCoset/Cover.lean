/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Basic
public import Mathlib.GroupTheory.Index

/-!
# Double-coset covers certified by generator transitions

A finite list of double cosets does not by itself bound a subgroup's index: the list must
cover the actual ambient group. Here coverage follows from an identity cell and transitions
under generators and their inverses. Transitions are checked on the left cosets within each
double coset, indexed by `H ⧸ (w H w⁻¹).subgroupOf H`. Thus a transition proof may use
subgroup normal forms instead of listing all ambient elements.

The resulting index bound is the sum of these intersection indices. Neither the ambient
group nor the subgroup is assumed finite, and double-coset representatives may repeat.
Applied to a presented group, the transition equations must hold in that presented group;
checking them only in a finite image does not certify an upper bound.

## References

* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*, Chapter 5,
  for coset enumeration and subgroup-based enumeration methods.
-/

public section

open scoped Pointwise

namespace Subgroup

variable {G ι : Type*} [Group G] (H : Subgroup G) (w : ι → G)

/-- Generator transitions on the cosets within the proposed double cosets imply coverage.
The signed generator set is `S ∪ S⁻¹`; no finiteness assumption is needed for this step. -/
theorem exists_mem_doubleCoset_of_generator_transitions (S : Set G)
    (hS : closure S = ⊤) (h1 : ∃ i, (1 : G) ∈ DoubleCoset.doubleCoset (w i) H H)
    (hstep : ∀ s ∈ S ∪ S⁻¹, ∀ i,
      ∀ q : H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H,
        ∃ j, s * (q.out : G) * w i ∈ DoubleCoset.doubleCoset (w j) H H) :
    ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H := by
  have step (s : G) (hs : s ∈ S ∪ S⁻¹) (g : G)
      (hg : ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
      ∃ i, s * g ∈ DoubleCoset.doubleCoset (w i) H H := by
    obtain ⟨i, hi⟩ := hg
    rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hi
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hi
    obtain ⟨h, hh, rfl⟩ := Set.mem_smul_set.mp hq
    obtain ⟨j, hj⟩ := hstep s hs i q
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mem_doubleCoset.mp hj
    refine ⟨j, DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * h, H.mul_mem hb hh, ?_⟩⟩
    simpa only [smul_eq_mul, mul_assoc] using congrArg (· * h) hab
  intro g
  exact closure_induction_left (p := fun x _ ↦ ∃ i, x ∈ DoubleCoset.doubleCoset (w i) H H) h1
    (fun s hs g _ hg ↦ step s (Or.inl hs) g hg)
    (fun s hs g _ hg ↦ step s⁻¹ (Or.inr (by simpa using hs)) g hg)
    (hS ▸ mem_top g)

/-- A double-coset cover gives a surjection onto the coset space, indexed by the cosets of
`H ∩ w H w⁻¹` in `H`. This retains the representatives used to compute the index bound. -/
theorem surjective_sigma_quotient_mul_of_doubleCoset_cover
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
    Function.Surjective (fun p : Σ i, H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H ↦
      (((p.2.out : H) : G) * w p.1 : G ⧸ H)) := by
  intro q
  obtain ⟨i, hi⟩ := hcover q.out
  rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hi
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hi
  obtain ⟨h, hh, heq⟩ := Set.mem_smul_set.mp hr
  refine ⟨⟨i, r⟩, ?_⟩
  rw [← QuotientGroup.out_eq' q, QuotientGroup.eq]
  rw [← heq]
  simpa [smul_eq_mul, mul_assoc] using hh

/-- A finite double-coset cover with finite intersection indices proves finite index in the
actual ambient group, without assuming that ambient group finite. -/
theorem finiteIndex_of_doubleCoset_cover [Finite ι]
    [∀ i, ((ConjAct.toConjAct (w i) • H).subgroupOf H).FiniteIndex]
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) : H.FiniteIndex := by
  have : Finite (G ⧸ H) := Finite.of_surjective _
    (H.surjective_sigma_quotient_mul_of_doubleCoset_cover w hcover)
  exact H.finiteIndex_of_finite_quotient

/-- The index of a subgroup covered by finitely many double cosets is bounded by the sum of
the corresponding intersection indices. Overlaps and repeated representatives are allowed. -/
theorem index_le_sum_of_doubleCoset_cover [Fintype ι]
    [∀ i, ((ConjAct.toConjAct (w i) • H).subgroupOf H).FiniteIndex]
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
    H.index ≤ ∑ i, ((ConjAct.toConjAct (w i) • H).subgroupOf H).index := by
  simpa only [index_eq_card, Nat.card_sigma] using
    Nat.card_le_card_of_surjective _ (H.surjective_sigma_quotient_mul_of_doubleCoset_cover w hcover)

end Subgroup

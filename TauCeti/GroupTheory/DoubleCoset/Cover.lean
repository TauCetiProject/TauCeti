/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import TauCeti.Algebra.Group.Subgroup.Pointwise
import TauCeti.GroupTheory.DoubleCoset.Map

/-!
# Double-coset covers certified by generator transitions

A finite list of double cosets does not by itself bound a subgroup's index: the list must
cover the actual ambient group. Here coverage follows from an identity cell and transitions
under generators and their inverses. Transitions are checked on `h * w` for `h ∈ H`, so a
transition proof may use subgroup normal forms instead of listing all ambient elements.
The counting map allows any chosen representatives of `H ⧸ (w H w⁻¹).subgroupOf H`.

The resulting index bound is the sum of these intersection indices. Neither the ambient
group nor the subgroup is assumed finite, and double-coset representatives may repeat.
Applied to a presented group, the transition equations must hold in that presented group;
checking them only in a finite image does not certify an upper bound.

An exact count needs representatives without repeats. When the representatives `xᵢ ∈ P` of
`T \ P / Q` meet each double coset exactly once, the map `(i, t) ↦ t xᵢ` from the cosets of
`T ∩ xᵢQxᵢ⁻¹` in `T` to `P ⧸ (Q ∩ P)` is a bijection
(`Subgroup.bijective_sigma_quotient_mul_of_existsUnique_doubleCoset`); the chosen
representatives of the double coset quotient `T \ P / Q` are such a family
(`Subgroup.existsUnique_mem_doubleCoset_out`).

## References

* D. F. Holt, B. Eick, E. A. O'Brien, *Handbook of Computational Group Theory*, Chapter 5,
  for coset enumeration and subgroup-based enumeration methods.
-/

public section

open scoped Pointwise

namespace Subgroup

variable {G ι : Type*} [Group G] (H : Subgroup G) (w : ι → G)

/-- Generator transitions on the cosets within the proposed double cosets imply coverage.
The signed generator set is `S ∪ S⁻¹`; no finiteness assumption is needed for this step.
Transitions are stated for all `h : H`, independently of any choice of quotient representatives. -/
theorem exists_mem_doubleCoset_of_generator_transitions (S : Set G)
    (hS : closure S = ⊤) (h1 : ∃ i, (1 : G) ∈ DoubleCoset.doubleCoset (w i) H H)
    (hstep : ∀ s ∈ S ∪ S⁻¹, ∀ i, ∀ h : H,
      ∃ j, s * h * w i ∈ DoubleCoset.doubleCoset (w j) H H) :
    ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H := by
  have step (s : G) (hs : s ∈ S ∪ S⁻¹) (g : G)
      (hg : ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
      ∃ i, s * g ∈ DoubleCoset.doubleCoset (w i) H H := by
    obtain ⟨i, hi⟩ := hg
    obtain ⟨x, hx, h, hh, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hi
    obtain ⟨j, hj⟩ := hstep s hs i ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mem_doubleCoset.mp hj
    refine ⟨j, DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b * h, H.mul_mem hb hh, ?_⟩⟩
    simpa only [mul_assoc] using congrArg (· * h) hab
  intro g
  exact closure_induction_left (p := fun x _ ↦ ∃ i, x ∈ DoubleCoset.doubleCoset (w i) H H) h1
    (fun s hs g _ hg ↦ step s (Or.inl hs) g hg)
    (fun s hs g _ hg ↦ step s⁻¹ (Or.inr (by simpa using hs)) g hg)
    (hS ▸ mem_top g)

/-- A double-coset cover gives a surjection onto the coset space, indexed by the cosets of
`H ∩ w H w⁻¹` in `H`. The sections `r` may be any user-supplied quotient representatives. -/
theorem surjective_sigma_quotient_mul_of_doubleCoset_cover
    (r : ∀ i, H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H → H)
    (hr : ∀ i q, (r i q : H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H) = q)
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
    Function.Surjective (fun p : Σ i, H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H ↦
      ((r p.1 p.2 : G) * w p.1 : G ⧸ H)) := by
  intro q
  obtain ⟨i, hi⟩ := hcover q.out
  obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mem_doubleCoset.mp hi
  let x : H := ⟨a, ha⟩
  let c : H ⧸ (ConjAct.toConjAct (w i) • H).subgroupOf H := x
  have hc := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp (hr i c))
  have hm : (w i)⁻¹ * ((r i c : G)⁻¹ * a) * w i ∈ H := by
    simpa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, mul_assoc, x]
      using hc
  refine ⟨⟨i, c⟩, ?_⟩
  rw [← QuotientGroup.out_eq' q, QuotientGroup.eq, hab]
  simpa [mul_assoc] using H.mul_mem hm hb

/-- **A transversal adapted to the double cosets `T \ P / Q`.** For subgroups `T ≤ P` and `Q`,
and elements `xᵢ ∈ P` meeting each double coset `T x Q` in `P` exactly once, the elements `t xᵢ`,
for `t` running over the chosen representatives of `T ⧸ (T ∩ xᵢQxᵢ⁻¹)`, enumerate `P ⧸ (Q ∩ P)`
bijectively. -/
theorem bijective_sigma_quotient_mul_of_existsUnique_doubleCoset {T Q P : Subgroup G}
    (hTP : T ≤ P) (x : ι → P) (hx : ∀ y ∈ P, ∃! i, y ∈ DoubleCoset.doubleCoset (x i : G) T Q) :
    Function.Bijective (fun p : Σ i, T ⧸ (MulAut.conj (x i : G) • Q).subgroupOf T ↦
      ((⟨(p.2.out : G) * x p.1, P.mul_mem (hTP p.2.out.property) (x p.1).property⟩ : P) :
        P ⧸ Q.subgroupOf P)) := by
  refine ⟨fun ⟨i, j⟩ ⟨i', j'⟩ h => ?_, fun c => ?_⟩
  · rw [QuotientGroup.eq, mem_subgroupOf] at h
    simp only [coe_mul, InvMemClass.coe_inv, mul_inv_rev] at h
    have hi : i' = i := by
      refine (hx _ (x i').property).unique (DoubleCoset.mem_doubleCoset_self _ _ _) ?_
      refine DoubleCoset.mem_doubleCoset.2 ⟨(j'.out : G)⁻¹ * j.out,
        T.mul_mem (T.inv_mem j'.out.property) j.out.property, _, h, ?_⟩
      group
    subst hi
    refine Sigma.ext rfl (heq_of_eq ?_)
    rw [← QuotientGroup.out_eq' j, ← QuotientGroup.out_eq' j', QuotientGroup.eq,
      mem_subgroupOf, TauCeti.mem_conj_smul]
    simpa [mul_assoc] using h
  · obtain ⟨i, hi, -⟩ := hx _ c.out.property
    obtain ⟨t, ht, q, hq, hy⟩ := DoubleCoset.mem_doubleCoset.1 hi
    let j : T ⧸ (MulAut.conj (x i : G) • Q).subgroupOf T := (⟨t, ht⟩ : T)
    have hj : (x i : G)⁻¹ * ((j.out : G)⁻¹ * t) * x i ∈ Q := by
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' j)
      rwa [mem_subgroupOf, TauCeti.mem_conj_smul] at this
    refine ⟨⟨i, j⟩, ?_⟩
    rw [← QuotientGroup.out_eq' c, QuotientGroup.eq, mem_subgroupOf]
    simp only [coe_mul, InvMemClass.coe_inv, mul_inv_rev, hy]
    convert Q.mul_mem hj hq using 1
    group

/-- For `T ≤ P`, the chosen representatives of the double cosets `T \ P / Q` meet each double
coset `T y Q` with `y ∈ P` exactly once, as required by
`Subgroup.bijective_sigma_quotient_mul_of_existsUnique_doubleCoset`. -/
theorem existsUnique_mem_doubleCoset_out {T Q P : Subgroup G} (hTP : T ≤ P) {y : G}
    (hy : y ∈ P) : ∃! q : DoubleCoset.Quotient (T.subgroupOf P : Set P) (Q.subgroupOf P),
      y ∈ DoubleCoset.doubleCoset (q.out : G) T Q := by
  refine ⟨DoubleCoset.mk _ _ ⟨y, hy⟩, ?_, fun q hq => ?_⟩
  · exact (mem_doubleCoset_subgroupOf_iff hTP (y := ⟨y, hy⟩)).1
      ((DoubleCoset.mem_quotToDoubleCoset_iff _ _).2 rfl)
  · exact ((DoubleCoset.mem_quotToDoubleCoset_iff q ⟨y, hy⟩).1
      ((mem_doubleCoset_subgroupOf_iff hTP).2 hq)).symm

/-- A finite double-coset cover with finite intersection indices proves finite index in the
actual ambient group, without assuming that ambient group finite. -/
theorem finiteIndex_of_doubleCoset_cover [Finite ι]
    [∀ i, (ConjAct.toConjAct (w i) • H).IsFiniteRelIndex H]
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) : H.FiniteIndex := by
  have : Finite (G ⧸ H) := Finite.of_surjective _
    (H.surjective_sigma_quotient_mul_of_doubleCoset_cover w (fun _ q ↦ q.out)
      (fun _ q ↦ QuotientGroup.out_eq' q) hcover)
  exact H.finiteIndex_of_finite_quotient

/-- The index of a subgroup covered by finitely many double cosets is bounded by the sum of
the corresponding relative indices. Overlaps and repeated representatives are allowed.
No finite-index assumption is needed: an infinite index is represented by zero. -/
theorem index_le_sum_of_doubleCoset_cover [Fintype ι]
    (hcover : ∀ g : G, ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H) :
    H.index ≤ ∑ i, (ConjAct.toConjAct (w i) • H).relIndex H := by
  classical
  by_cases hH : H.FiniteIndex
  · let := hH
    have hi (i : ι) : (ConjAct.toConjAct (w i) • H).FiniteIndex := by
      have he : (ConjAct.toConjAct (w i) • H).index = H.index := by
        simpa using relIndex_pointwise_smul (ConjAct.toConjAct (w i)) H ⊤
      exact ⟨he ▸ H.index_ne_zero⟩
    let := hi
    simpa only [relIndex, index_eq_card, Nat.card_sigma] using
      Nat.card_le_card_of_surjective _
        (H.surjective_sigma_quotient_mul_of_doubleCoset_cover w (fun _ q ↦ q.out)
          (fun _ q ↦ QuotientGroup.out_eq' q) hcover)
  · simp [not_finiteIndex_iff.mp hH]

end Subgroup

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Hensel
public import TauCeti.RingTheory.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Finite ball partitions and root counts

Over a discrete valuation ring with finite residue field, every valuation sphere of order `s`
is a finite disjoint union of balls of order `r > s`, with centres on that sphere. In particular,
the uniformizers admit such a partition whenever `2 ≤ r`.

If the roots of a polynomial lie on a sphere and the derivative order at each root is less than
`r`, every ball in a partition of order `r` contains at most one root, and all rational roots
are simple. Its root count is consequently the sum of the indicators of the balls containing
a root. The partition can be chosen once for an entire family of polynomials; only
the derivative bound and the location of the roots vary with the polynomial. This is the finite
sum used to integrate root counts by local fibre computations.

No completeness or topology is needed for either assertion.

## References

* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036, §3.
-/

public section

open IsLocalRing Polynomial
open IsDiscreteValuationRing

namespace TauCeti

variable {A : Type*} [CommRing A] [IsDomain A] [_root_.IsDiscreteValuationRing A]

/-- A valuation sphere is a finite disjoint union of smaller balls, with centres on the sphere.
For `s = 1`, this partitions the uniformizers. The same partition is available independently of
any polynomial whose roots will subsequently be counted. -/
theorem exists_finset_addVal_eq_biUnion [Finite (ResidueField A)] {s r : ℕ} (hsr : s < r) :
    ∃ C : Finset A, (∀ c ∈ C, addVal A c = s) ∧
      {x : A | addVal A x = s} = ⋃ c ∈ C, {x : A | (r : ℕ∞) ≤ addVal A (x - c)} ∧
      (C : Set A).PairwiseDisjoint (fun c ↦ {x : A | (r : ℕ∞) ≤ addVal A (x - c)}) := by
  classical
  let I := maximalIdeal A ^ r
  have hcard : Nat.card (A ⧸ I) = Nat.card (ResidueField A) ^ r := by
    rw [← Submodule.cardQuot_apply, cardQuot_pow_of_prime
      (_root_.IsDiscreteValuationRing.not_a_field A), Submodule.cardQuot_apply]
    rfl
  have : Finite (A ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero r Nat.card_pos.ne')
  let f := Ideal.Quotient.mk I
  obtain ⟨S, hS, hinj, himage⟩ :=
    (Set.surjOn_image f {x : A | addVal A x = s}).exists_subset_injOn_image_eq
  have hfin : S.Finite := (Set.toFinite (f '' S)).of_finite_image hinj
  have heq (x y : A) : f x = f y ↔ (r : ℕ∞) ≤ addVal A (x - y) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]
  refine ⟨hfin.toFinset, fun c hc ↦ hS (hfin.mem_toFinset.mp hc), ?_, ?_⟩
  · ext x
    simp only [Set.mem_ofPred, Set.mem_iUnion, hfin.mem_toFinset]
    constructor
    · intro hx
      obtain ⟨c, hc, hcx⟩ := himage.symm.subset (Set.mem_image_of_mem f hx)
      exact ⟨c, hc, (heq x c).mp hcx.symm⟩
    · rintro ⟨c, hc, hxc⟩
      have hlt : addVal A c < addVal A (x - c) := by
        rw [hS hc]
        exact (ENat.natCast_lt_natCast.mpr hsr).trans_le hxc
      simpa only [add_sub_cancel] using
        ((addVal A).map_add_eq_of_lt_left hlt).trans (hS hc)
  · intro c hc d hd hcd
    simp only [Finset.mem_coe, hfin.mem_toFinset] at hc hd
    refine Set.disjoint_left.mpr fun x hxc hxd ↦ hcd (hinj hc hd ?_)
    exact ((heq x c).mpr hxc).symm.trans ((heq x d).mpr hxd)

open Classical in
/-- Count roots by a finite disjoint family of balls covering them. If the derivative order at
each root is smaller than the ball order, each occupied ball contributes exactly one root.
The derivative bound also excludes repeated rational roots, so no separability hypothesis is
needed. -/
theorem _root_.Polynomial.card_roots_eq_sum_ite_of_addVal_lt (F : A[X])
    (C : Finset A) {r : ℕ}
    (hcover : ∀ x ∈ F.roots, ∃ c ∈ C, (r : ℕ∞) ≤ addVal A (x - c))
    (hdisj : (C : Set A).PairwiseDisjoint
      (fun c ↦ {x : A | (r : ℕ∞) ≤ addVal A (x - c)}))
    (hder : ∀ x ∈ F.roots, addVal A (F.derivative.eval x) < r) :
    F.roots.card = ∑ c ∈ C,
      if ∃ x ∈ F.roots, (r : ℕ∞) ≤ addVal A (x - c) then 1 else 0 := by
  classical
  have hF : F.roots.Nodup := F.nodup_roots_of_forall_derivative_eval_ne_zero fun x hx hzero ↦ by
    simpa [hzero] using hder x hx
  let B (c : A) := F.roots.toFinset.filter fun x ↦ (r : ℕ∞) ≤ addVal A (x - c)
  have hB (c : A) : (B c).card =
      if ∃ x ∈ F.roots, (r : ℕ∞) ≤ addVal A (x - c) then 1 else 0 := by
    have hle : (B c).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun x hx y hy ↦ ?_
      obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
      obtain ⟨hy, hyc⟩ := Finset.mem_filter.mp hy
      have hx' := Multiset.mem_toFinset.mp hx
      have hy' := Multiset.mem_toFinset.mp hy
      have hxy : (r : ℕ∞) ≤ addVal A (y - x) := by
        simpa only [sub_sub_sub_cancel_right] using
          (le_min hyc hxc).trans ((addVal A).map_sub (y - c) (x - c))
      exact (F.eq_of_isRoot_of_addVal_lt (Polynomial.isRoot_of_mem_roots hx')
        (Polynomial.isRoot_of_mem_roots hy') ((hder x hx').trans_le hxy)).symm
    have hpos : (B c).Nonempty ↔ ∃ x ∈ F.roots, (r : ℕ∞) ≤ addVal A (x - c) := by
      simp [B, Finset.nonempty_def]
    split_ifs with h
    · have := Finset.card_pos.mpr (hpos.mpr h)
      omega
    · exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp (mt hpos.mp h))
  have hunion : C.biUnion B = F.roots.toFinset := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Multiset.mem_toFinset, B]
    constructor
    · rintro ⟨c, _, hx, _⟩
      exact hx
    · intro hx
      obtain ⟨c, hc, hxc⟩ := hcover x hx
      exact ⟨c, hc, hx, hxc⟩
  have hpair : (C : Set A).PairwiseDisjoint B := by
    intro c hc d hd hcd
    refine Finset.disjoint_left.mpr fun x hxc hxd ↦ ?_
    exact Set.disjoint_left.mp (hdisj hc hd hcd)
      (Finset.mem_filter.mp hxc).2 (Finset.mem_filter.mp hxd).2
  rw [← Multiset.toFinset_card_of_nodup hF, ← hunion, Finset.card_biUnion hpair]
  exact Finset.sum_congr rfl fun c _ ↦ hB c

end TauCeti

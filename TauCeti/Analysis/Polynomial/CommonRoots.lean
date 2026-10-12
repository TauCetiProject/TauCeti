/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.GCD

import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# Common root matching for finite families of polynomials

Let `F k x`, for `k` in a finite index type, be polynomials over a proper algebraically closed
normed field whose coefficients depend continuously on a parameter `x`, each of fixed degree.
For a single member, `Polynomial.eventually_exists_bijOn_roots_toFinset` matches the distinct roots
of `F k x` with those of `F k x₀`, preserving multiplicities, as long as the number of distinct
roots does not increase near `x₀`. Separate matchings need not be compatible: two members sharing
a root at `x₀` could have nearby roots that drift apart.

This file shows that if, in addition, the degree of the gcd of every pair of members is locally
constant, then one bijection between the union of the distinct roots of the members at `x₀` and
at `x` works for all members simultaneously. It moves each root by less than a prescribed `ε` and
preserves its multiplicity in every member; in particular it preserves membership in every root
set. Consequently the total number of distinct roots of the family is locally constant.

Only pairwise gcd data are needed. The persistence of a common root of two members comes from
`TauCeti.eventually_exists_common_root_norm_sub_lt`; the individual matchings then force every
nearby common root to be the partner of the central root in both members.

## Main results

* `Polynomial.eventually_exists_bijOn_biUnion_roots_toFinset`: the family matching lemma.
* `Polynomial.eventually_card_biUnion_roots_toFinset_eq`: local constancy of the number of
  distinct roots of the family.

## References

* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Springer, 2006, §5.1 (continuity of roots and delineability).
-/

public section

open Filter Metric Topology TauCeti

namespace Polynomial

variable {K : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K] {B : Type*}
  [TopologicalSpace B] {ι : Type*} [Fintype ι] {F : ι → B → K[X]} {x₀ : B} {d : ι → ℕ}

open scoped Classical in
/-- **Family matching lemma.** Let `F k x` be polynomials of degree `d k` near `x₀`, for `k` in a
finite index type, whose coefficients of index at most `d k` are continuous at `x₀`. Suppose that
near `x₀` no member has more distinct roots than at `x₀`, and that the degree of the gcd of every
pair of distinct members is the same as at `x₀`. Then for `x` near `x₀` there is a single
bijection `e` from the distinct roots of all the `F k x₀` onto those of all the `F k x` that moves
each root by less than `ε` and preserves its multiplicity in every member. -/
theorem eventually_exists_bijOn_biUnion_roots_toFinset
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).roots.toFinset.card ≤ (F k x₀).roots.toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ e : K → K,
      Set.BijOn e (Finset.univ.biUnion fun k => (F k x₀).roots.toFinset)
        (Finset.univ.biUnion fun k => (F k x).roots.toFinset) ∧
      ∀ z ∈ Finset.univ.biUnion (fun k => (F k x₀).roots.toFinset), ‖e z - z‖ < ε ∧
        ∀ k, (F k x).rootMultiplicity (e z) = (F k x₀).rootMultiplicity z := by
  -- Outline: separate the distinct roots of the family at `x₀` by discs of radius `ρ ≤ ε`, take
  -- the individual matchings `e k` and the persistence of pairwise common roots at radius `ρ`,
  -- show that a root of `F k x` in the disc around `z` must be `e k z`, deduce that the `e k`
  -- agree on common roots, and glue them into a single map `E`.
  set T := Finset.univ.biUnion fun k => (F k x₀).roots.toFinset
  have hT (k : ι) : (F k x₀).roots.toFinset ⊆ T :=
    Finset.subset_biUnion_of_mem (fun k => (F k x₀).roots.toFinset) (Finset.mem_univ k)
  -- shrink `ε` so that the discs around the distinct roots of the family are pairwise disjoint
  obtain ⟨r, hr, -, hsep⟩ := exists_pos_closedBall_subset_and_lt_dist
    (T := T) (U := fun _ => Set.univ) fun _ _ => univ_mem
  set ρ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  have hsep' : ∀ z ∈ T, ∀ w ∈ T, z ≠ w → 2 * ρ < dist z w := fun z hz w hw hzw => by
    linarith [hsep z hz w hw hzw, min_le_right ε r]
  have hmatch : ∀ᶠ x in 𝓝 x₀, ∀ k, ∃ e : K → K,
      Set.BijOn e (F k x₀).roots.toFinset (F k x).roots.toFinset ∧
        ∀ z ∈ (F k x₀).roots,
          ‖e z - z‖ < ρ ∧ (F k x).rootMultiplicity (e z) = (F k x₀).rootMultiplicity z :=
    eventually_all.2 fun k => eventually_exists_bijOn_roots_toFinset (hF k) (hdeg k) (hcard k) hρ
  have hcommon : ∀ᶠ x in 𝓝 x₀, ∀ k l, k ≠ l → ∀ z, (F k x₀).IsRoot z → (F l x₀).IsRoot z →
      ∃ w, (F k x).IsRoot w ∧ (F l x).IsRoot w ∧ ‖w - z‖ < ρ := by
    refine eventually_all.2 fun k => eventually_all.2 fun l => ?_
    by_cases hkl : k = l
    · exact Eventually.of_forall fun _ h => absurd hkl h
    · exact (eventually_exists_common_root_norm_sub_lt (hF k) (hF l) (hdeg k) (hdeg l)
        (hgcd hkl) hρ).mono fun _ h _ => h
  filter_upwards [hmatch, hcommon, eventually_all.2 hdeg] with x hm hc hx
  choose e he hed using hm
  have hne (k : ι) (y : B) (hy : (F k y).degree = d k) : F k y ≠ 0 := by
    rintro h
    simp [h] at hy
  -- a root of `F k x` near a point of `T` is the partner of that point under `e k`
  have huniq (k : ι) {z w : K} (hz : z ∈ T) (hw : w ∈ (F k x).roots) (hwz : ‖w - z‖ < ρ) :
      z ∈ (F k x₀).roots ∧ e k z = w := by
    obtain ⟨z', hz', rfl⟩ := (he k).surjOn (Finset.mem_coe.2 (Multiset.mem_toFinset.2 hw))
    have hz'k : z' ∈ (F k x₀).roots := Multiset.mem_toFinset.1 hz'
    obtain rfl : z = z' := eq_of_dist_lt_of_dist_lt (hsep' z hz z' (hT k hz'))
      (by rwa [dist_eq_norm]) (by rw [dist_eq_norm]; exact (hed k z' hz'k).1)
    exact ⟨hz'k, rfl⟩
  -- the matchings of two members agree at a common root
  have hagree (k l : ι) {z : K} (hk : z ∈ (F k x₀).roots) (hl : z ∈ (F l x₀).roots) :
      e k z = e l z := by
    by_cases hkl : k = l
    · rw [hkl]
    have hz : z ∈ T := hT k (Multiset.mem_toFinset.2 hk)
    obtain ⟨w, hwk, hwl, hwz⟩ := hc k l hkl z ((mem_roots (hne k x₀ (hdeg k).self_of_nhds)).1 hk)
      ((mem_roots (hne l x₀ (hdeg l).self_of_nhds)).1 hl)
    rw [(huniq k hz ((mem_roots (hne k x (hx k))).2 hwk) hwz).2,
      (huniq l hz ((mem_roots (hne l x (hx l))).2 hwl) hwz).2]
  have hmemT {z : K} (hz : z ∈ T) : ∃ k, z ∈ (F k x₀).roots := by
    simpa [T] using hz
  let E : K → K := fun z => if h : ∃ k, z ∈ (F k x₀).roots then e h.choose z else z
  have hE {k : ι} {z : K} (hz : z ∈ (F k x₀).roots) : E z = e k z := by
    have h : ∃ k, z ∈ (F k x₀).roots := ⟨k, hz⟩
    simp only [E, h, ↓reduceDIte]
    exact hagree _ _ h.choose_spec hz
  have hEclose {z : K} (hz : z ∈ T) : ‖E z - z‖ < ρ := by
    obtain ⟨k, hk⟩ := hmemT hz
    rw [hE hk]
    exact (hed k z hk).1
  refine ⟨E, ⟨fun z hz => ?_, fun z hz z' hz' hzz' => ?_, fun w hw => ?_⟩, fun z hz =>
    ⟨(hEclose hz).trans_le (min_le_left ε r), fun k => ?_⟩⟩
  · obtain ⟨k, hk⟩ := hmemT hz
    rw [hE hk]
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _,
      Finset.mem_coe.1 ((he k).mapsTo (Multiset.mem_toFinset.2 hk))⟩)
  · exact eq_of_dist_lt_of_dist_lt (hsep' z hz z' hz') (y := E z)
      (by rw [dist_eq_norm]; exact hEclose hz) (by rw [dist_eq_norm, hzz']; exact hEclose hz')
  · obtain ⟨k, -, hwk⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hw)
    obtain ⟨z, hz, rfl⟩ := (he k).surjOn hwk
    have hzk : z ∈ (F k x₀).roots := Multiset.mem_toFinset.1 hz
    exact ⟨z, Finset.mem_coe.2 (hT k hz), hE hzk⟩
  · by_cases hk : z ∈ (F k x₀).roots
    · rw [hE hk]
      exact (hed k z hk).2
    · rw [rootMultiplicity_eq_zero fun h => hk ((mem_roots (hne k x₀ (hdeg k).self_of_nhds)).2 h)]
      refine rootMultiplicity_eq_zero fun h => hk ?_
      exact (huniq k hz ((mem_roots (hne k x (hx k))).2 h) (hEclose hz)).1

open scoped Classical in
/-- **Local constancy of the number of distinct roots of a family.** Under the hypotheses of the
family matching lemma, the members of the family have, together, as many distinct roots near
`x₀` as at `x₀`. -/
theorem eventually_card_biUnion_roots_toFinset_eq
    (hF : ∀ k, ∀ i ≤ d k, ContinuousAt (fun x => (F k x).coeff i) x₀)
    (hdeg : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).degree = d k)
    (hcard : ∀ k, ∀ᶠ x in 𝓝 x₀, (F k x).roots.toFinset.card ≤ (F k x₀).roots.toFinset.card)
    (hgcd : Pairwise fun k l => ∀ᶠ x in 𝓝 x₀, (EuclideanDomain.gcd (F k x) (F l x)).natDegree =
      (EuclideanDomain.gcd (F k x₀) (F l x₀)).natDegree) :
    ∀ᶠ x in 𝓝 x₀, (Finset.univ.biUnion fun k => (F k x).roots.toFinset).card =
      (Finset.univ.biUnion fun k => (F k x₀).roots.toFinset).card := by
  filter_upwards [eventually_exists_bijOn_biUnion_roots_toFinset hF hdeg hcard hgcd one_pos]
    with x ⟨e, he, _⟩
  exact (Finset.card_nbij e he.mapsTo he.injOn he.surjOn).symm

end Polynomial

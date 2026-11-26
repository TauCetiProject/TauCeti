/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Order.Filter.Basic

/-!
# Multiplicities of labelled roots

If a finite family enumerates a polynomial's roots with multiplicity, the multiplicity
at each label depends only on which labels coincide. Consequently an eventually constant
collision relation gives eventually constant multiplicities, without any continuity or
splitting assumptions on the polynomial family.

We also count the root zero: it occurs in `f.roots` with multiplicity the order of vanishing
`f.natTrailingDegree`, so the roots satisfying a predicate that holds at zero number
`f.natTrailingDegree` plus the nonzero roots satisfying it. Over any integral domain, summing
`f.rootMultiplicity` over any finite set of points never exceeds `f.natDegree`
(`Polynomial.sum_rootMultiplicity_le_natDegree`), including for `f = 0`, and summing it over the
distinct roots gives the number of roots counted with multiplicity
(`Polynomial.sum_rootMultiplicity_roots_toFinset_eq_card_roots`). So if
`k ≤ f.rootMultiplicity a` for every `a` in a finite set `s`, then `k * #s ≤ f.natDegree`
(`Polynomial.mul_card_le_natDegree_of_le_rootMultiplicity`).

Over an arbitrary commutative ring, distinct points are not enough (in `ZMod 4`, `2 * X` has the
simple roots `0` and `2` but degree `1`), but points whose pairwise differences are units are: the
powers `(X - a) ^ f.rootMultiplicity a` at such points are pairwise coprime, so their product
divides `f` (`Polynomial.sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub`).

Finally, a nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a`
occurs at least `k` times in `E` (`Polynomial.X_sub_C_pow_dvd_smul_multiset_prod_iff`).
-/

public section

open Filter Polynomial

namespace TauCeti

/-- A finite enumeration of roots with an eventually constant collision relation has
eventually constant multiplicity at each label. The parameter filter is arbitrary, and
the root enumeration at the reference parameter is supplied separately. -/
theorem eventually_rootMultiplicity_eq_of_roots_eq_map
    {K B ι : Type*} [CommRing K] [IsDomain K]
    {I : Finset ι} {f : ι → B → K} {Q : B → Polynomial K} {x₀ : B} {l : Filter B}
    (hroots₀ : (Q x₀).roots = I.val.map (fun i ↦ f i x₀))
    (hroots : ∀ᶠ x in l, (Q x).roots = I.val.map (fun i ↦ f i x))
    (hrel : ∀ᶠ x in l, ∀ i ∈ I, ∀ j ∈ I, f i x = f j x ↔ f i x₀ = f j x₀) :
    ∀ᶠ x in l, ∀ i ∈ I, (Q x).rootMultiplicity (f i x) =
      (Q x₀).rootMultiplicity (f i x₀) := by
  classical
  filter_upwards [hrel, hroots] with x hx hxroots i hi
  rw [← count_roots, ← count_roots, hxroots, hroots₀,
    Multiset.count_map, Multiset.count_map]
  exact congrArg _ (Multiset.filter_congr fun j hj ↦ hx i hi j (Finset.mem_val.mp hj))

end TauCeti

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The root zero occurs in `f.roots` with multiplicity the order of vanishing of `f` at zero. -/
theorem count_zero_roots [DecidableEq R] (f : R[X]) : f.roots.count 0 = f.natTrailingDegree := by
  rw [count_roots, rootMultiplicity_eq_natTrailingDegree']

/-- The number of roots satisfying a predicate that holds at zero is the order of vanishing at
zero plus the number of nonzero roots satisfying it. -/
theorem card_filter_roots_eq_natTrailingDegree_add [DecidableEq R] (f : R[X]) {q : R → Prop}
    [DecidablePred q] (hq : q 0) :
    (f.roots.filter q).card =
      f.natTrailingDegree + (f.roots.filter fun α => α ≠ 0 ∧ q α).card := by
  have hsplit : f.roots.filter q =
      f.roots.filter (· = 0) + f.roots.filter fun α => α ≠ 0 ∧ q α := by
    rw [← Multiset.filter_add_not (· = 0) (f.roots.filter q), Multiset.filter_filter,
      Multiset.filter_filter]
    congr 1
    exact Multiset.filter_congr fun α _ => ⟨And.left, fun h => ⟨h, h ▸ hq⟩⟩
  rw [hsplit, Multiset.card_add, Multiset.filter_eq', Multiset.card_replicate, count_zero_roots]

/-- Over a domain, the root multiplicities of `f` at its distinct roots add up to the number of
roots of `f` counted with multiplicity. -/
@[simp]
theorem sum_rootMultiplicity_roots_toFinset_eq_card_roots [DecidableEq R] (f : R[X]) :
    ∑ a ∈ f.roots.toFinset, f.rootMultiplicity a = f.roots.card := by
  simpa only [count_roots] using Multiset.toFinset_sum_count_eq f.roots

/-- Over a domain, the sum of root multiplicities of a polynomial `f` across any finite set of
points is at most `f.natDegree` (also when `f = 0`, where every multiplicity vanishes). -/
theorem sum_rootMultiplicity_le_natDegree (f : R[X]) (s : Finset R) :
    ∑ a ∈ s, f.rootMultiplicity a ≤ f.natDegree := by
  classical
  calc ∑ a ∈ s, f.rootMultiplicity a
      = ∑ a ∈ s, f.roots.count a := Finset.sum_congr rfl fun _ _ ↦ (count_roots f).symm
    _ ≤ ∑ a ∈ f.roots.toFinset, f.roots.count a :=
        Finset.sum_le_sum_of_ne_zero fun _ _ ha ↦
          Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero ha))
    _ = f.roots.card := Multiset.toFinset_sum_count_eq f.roots
    _ ≤ f.natDegree := card_roots' f

/-- **The root-count inequality.** Over a domain, if `k ≤ f.rootMultiplicity a` for every `a` in
a finite set `s`, then `k * #s ≤ f.natDegree`. -/
theorem mul_card_le_natDegree_of_le_rootMultiplicity {f : R[X]} {s : Finset R} {k : ℕ}
    (h : ∀ a ∈ s, k ≤ f.rootMultiplicity a) : k * s.card ≤ f.natDegree := by
  rw [mul_comm, ← smul_eq_mul]
  exact (Finset.card_nsmul_le_sum s _ k h).trans (sum_rootMultiplicity_le_natDegree f s)

omit [IsDomain R] in
/-- **Counting roots at points with unit differences.** Over any commutative ring, if the pairwise
differences of the points `a i`, `i ∈ s`, are units, then the root multiplicities of `f` at these
points add up to at most `f.natDegree` (also when `f = 0`, where every multiplicity vanishes). -/
theorem sum_rootMultiplicity_le_natDegree_of_pairwise_isUnit_sub {ι : Type*} {s : Finset ι}
    {a : ι → R} (ha : (s : Set ι).Pairwise fun i j ↦ IsUnit (a i - a j)) (f : R[X]) :
    ∑ i ∈ s, f.rootMultiplicity (a i) ≤ f.natDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have : Nontrivial R := nontrivial_iff.mp (nontrivial_of_ne f 0 hf)
  have hmonic : ∀ i ∈ s, ((X - C (a i)) ^ f.rootMultiplicity (a i)).Monic :=
    fun i _ ↦ (monic_X_sub_C (a i)).pow _
  -- the powers `(X - a i) ^ mᵢ` are pairwise coprime divisors of `f`, so their product divides it
  have hdvd : ∏ i ∈ s, (X - C (a i)) ^ f.rootMultiplicity (a i) ∣ f :=
    Finset.prod_dvd_of_coprime
      (fun _ hi _ hj hij ↦ (isCoprime_X_sub_C_of_isUnit_sub (ha hi hj hij)).pow)
      fun i _ ↦ pow_rootMultiplicity_dvd f (a i)
  calc ∑ i ∈ s, f.rootMultiplicity (a i)
      = (∏ i ∈ s, (X - C (a i)) ^ f.rootMultiplicity (a i)).natDegree := by
        rw [natDegree_prod_of_monic _ _ hmonic]
        simp only [(monic_X_sub_C _).natDegree_pow, natDegree_X_sub_C, mul_one]
    _ ≤ f.natDegree := (monic_prod_of_monic _ _ hmonic).natDegree_le_of_dvd hf hdvd

/-- A nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a` occurs
at least `k` times in `E`. -/
theorem X_sub_C_pow_dvd_smul_multiset_prod_iff [DecidableEq R] {E : Multiset R} {a c : R}
    (hc : c ≠ 0) {k : ℕ} :
    (X - C a) ^ k ∣ c • (E.map fun b ↦ X - C b).prod ↔ k ≤ E.count a := by
  rw [← le_rootMultiplicity_iff (smul_ne_zero hc (monic_multisetProd_X_sub_C E).ne_zero),
    ← count_roots, roots_smul_of_ne_zero _ hc, roots_multiset_prod_X_sub_C]

end Polynomial

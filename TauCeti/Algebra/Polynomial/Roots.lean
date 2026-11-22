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
(`Polynomial.sum_rootMultiplicity_le_natDegree`, and
`Polynomial.sum_rootMultiplicity_comp_le_natDegree` for indexed evaluation points injective on the
indexing set), including for `f = 0`, and summing it over the distinct roots gives the number of
roots counted with multiplicity
(`Polynomial.sum_rootMultiplicity_roots_toFinset_eq_card_roots`). So if
`k ≤ f.rootMultiplicity a` for every `a` in a finite set `s`, then `k * #s ≤ f.natDegree`
(`Polynomial.mul_card_le_natDegree_of_le_rootMultiplicity`).

Finally, a nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a`
occurs at least `k` times in `E` (`Polynomial.X_sub_C_pow_dvd_smul_multiset_prod_iff`), and
`Polynomial.cappedRootMultiplicity` caps the root multiplicity at `N` (taking value `N` on `0`),
so `k ≤ p.cappedRootMultiplicity a N ↔ (X - C a) ^ k ∣ p` for all `k ≤ N`.
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
  congr 1
  exact Multiset.filter_congr fun j hj ↦ hx i hi j (Finset.mem_val.mp hj)

end TauCeti

namespace Polynomial

section

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
theorem sum_rootMultiplicity_roots_toFinset_eq_card_roots [DecidableEq R] (f : R[X]) :
    ∑ a ∈ f.roots.toFinset, f.rootMultiplicity a = f.roots.card := by
  rw [← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun a _ ↦ (count_roots f).symm

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

/-- Over a domain, the sum of root multiplicities of a polynomial `f` over an indexed finite set
with evaluation points injective on the set is at most `f.natDegree`. -/
theorem sum_rootMultiplicity_comp_le_natDegree {ι : Type*} (f : R[X]) (s : Finset ι)
    {β : ι → R} (hβ : Set.InjOn β s) :
    ∑ i ∈ s, f.rootMultiplicity (β i) ≤ f.natDegree := by
  classical
  calc ∑ i ∈ s, f.rootMultiplicity (β i)
      = ∑ b ∈ s.image β, f.rootMultiplicity b :=
        (Finset.sum_image (f := fun b ↦ f.rootMultiplicity b) fun _ hx _ hy h ↦ hβ hx hy h).symm
    _ ≤ f.natDegree := f.sum_rootMultiplicity_le_natDegree (s.image β)

/-- **The root-count inequality.** Over a domain, if `k ≤ f.rootMultiplicity a` for every `a` in
a finite set `s`, then `k * #s ≤ f.natDegree`. -/
theorem mul_card_le_natDegree_of_le_rootMultiplicity {f : R[X]} {s : Finset R} {k : ℕ}
    (h : ∀ a ∈ s, k ≤ f.rootMultiplicity a) : k * s.card ≤ f.natDegree := by
  rw [mul_comm, ← smul_eq_mul]
  exact (Finset.card_nsmul_le_sum s _ k h).trans (sum_rootMultiplicity_le_natDegree f s)

/-- A nonzero constant multiple of a product of linear factors vanishes exactly at the
`r i`. -/
theorem isRoot_C_mul_prod_X_sub_C_iff {ι : Type*} [Fintype ι] {l : R} (hl : l ≠ 0)
    (r : ι → R) (z : R) : (C l * ∏ i, (X - C (r i))).IsRoot z ↔ ∃ i, r i = z := by
  rw [root_mul, iff_false_intro (not_isRoot_C _ z hl), false_or, isRoot_prod]
  simp [sub_eq_zero, eq_comm]

/-- A nonzero multiple of `∏_{b ∈ E} (X - b)` is divisible by `(X - a)^k` exactly when `a` occurs
at least `k` times in `E`. -/
theorem X_sub_C_pow_dvd_smul_multiset_prod_iff [DecidableEq R] {E : Multiset R} {a c : R}
    (hc : c ≠ 0) {k : ℕ} :
    (X - C a) ^ k ∣ c • (E.map fun b ↦ X - C b).prod ↔ k ≤ E.count a := by
  rw [← le_rootMultiplicity_iff (smul_ne_zero hc (monic_multisetProd_X_sub_C E).ne_zero),
    ← count_roots, roots_smul_of_ne_zero _ hc, roots_multiset_prod_X_sub_C]

end

section

variable {R : Type*} [Ring R]

/-- The root multiplicity of `p` at `a`, capped at `N` (equal to `N` when `p = 0`).
This satisfies `k ≤ p.cappedRootMultiplicity a N ↔ (X - C a) ^ k ∣ p` for all `k ≤ N`,
including `p = 0`, and is subadditive under multiplication. -/
noncomputable def cappedRootMultiplicity (p : R[X]) (a : R) (N : ℕ) : ℕ :=
  letI := Classical.propDecidable
  if p = 0 then N else min N (p.rootMultiplicity a)

/-- `p.cappedRootMultiplicity a N` never exceeds the cap `N`. -/
theorem cappedRootMultiplicity_le (p : R[X]) (a : R) (N : ℕ) :
    p.cappedRootMultiplicity a N ≤ N := by
  dsimp [cappedRootMultiplicity]
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The capped root multiplicity of `0` is the cap `N`. -/
@[simp]
theorem cappedRootMultiplicity_zero (a : R) (N : ℕ) :
    (0 : R[X]).cappedRootMultiplicity a N = N := by
  simp [cappedRootMultiplicity]

/-- The capped root multiplicity with cap `0` is `0`. -/
@[simp]
theorem cappedRootMultiplicity_zero_right (p : R[X]) (a : R) :
    p.cappedRootMultiplicity a 0 = 0 := by
  simpa using Nat.le_zero.mp (p.cappedRootMultiplicity_le a 0)

/-- For nonzero `p`, `p.cappedRootMultiplicity a N = min N (p.rootMultiplicity a)`. -/
theorem cappedRootMultiplicity_of_ne_zero {p : R[X]} (hp : p ≠ 0) (a : R) (N : ℕ) :
    p.cappedRootMultiplicity a N = min N (p.rootMultiplicity a) := by
  simp [cappedRootMultiplicity, hp]

/-- The capped root multiplicity of a nonzero constant polynomial is `0`. -/
@[simp]
theorem cappedRootMultiplicity_C {c : R} (hc : c ≠ 0) (a : R) (N : ℕ) :
    (C c).cappedRootMultiplicity a N = 0 := by
  simp [cappedRootMultiplicity_of_ne_zero (C_ne_zero.mpr hc), rootMultiplicity_C]

end

section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Every unit polynomial has capped root multiplicity `0` at every point. -/
theorem cappedRootMultiplicity_of_isUnit {u : R[X]} (hu : IsUnit u) (a : R) (N : ℕ) :
    u.cappedRootMultiplicity a N = 0 := by
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
  exact cappedRootMultiplicity_C hc.ne_zero a N

/-- Over an integral domain, `cappedRootMultiplicity` of a product is the capped sum of the
factors' capped root multiplicities. -/
theorem cappedRootMultiplicity_mul (p q : R[X]) (a : R) (N : ℕ) :
    (p * q).cappedRootMultiplicity a N =
      min N (p.cappedRootMultiplicity a N + q.cappedRootMultiplicity a N) := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  rw [cappedRootMultiplicity_of_ne_zero hpq, cappedRootMultiplicity_of_ne_zero hp,
    cappedRootMultiplicity_of_ne_zero hq, rootMultiplicity_mul hpq]
  omega

/-- `cappedRootMultiplicity` is subadditive under polynomial multiplication. -/
theorem cappedRootMultiplicity_mul_le (p q : R[X]) (a : R) (N : ℕ) :
    (p * q).cappedRootMultiplicity a N ≤
      p.cappedRootMultiplicity a N + q.cappedRootMultiplicity a N := by
  rw [cappedRootMultiplicity_mul]
  exact min_le_right _ _

end

section

variable {R : Type*} [CommRing R]

/-- For `k ≤ N`, `k ≤ p.cappedRootMultiplicity a N` if and only if `(X - C a) ^ k ∣ p`
(including when `p = 0`). -/
theorem le_cappedRootMultiplicity_iff {p : R[X]} {a : R} {N k : ℕ} (hk : k ≤ N) :
    k ≤ p.cappedRootMultiplicity a N ↔ (X - C a) ^ k ∣ p := by
  by_cases hp : p = 0
  · simp [hp, hk]
  · rw [cappedRootMultiplicity_of_ne_zero hp, le_min_iff, iff_true_intro hk, true_and,
      le_rootMultiplicity_iff hp]

/-- `p.cappedRootMultiplicity a N = N` if and only if `(X - C a) ^ N ∣ p`
(including when `p = 0`). -/
theorem cappedRootMultiplicity_eq_self_iff {p : R[X]} {a : R} {N : ℕ} :
    p.cappedRootMultiplicity a N = N ↔ (X - C a) ^ N ∣ p := by
  rw [← le_cappedRootMultiplicity_iff le_rfl, le_antisymm_iff,
    iff_true_intro (p.cappedRootMultiplicity_le a N), true_and]

end

end Polynomial

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Convolution of Novikov series

Let `H` be an additive monoid with a period homomorphism `N : H →+ ℝ`. The product of two
Novikov series `a` and `b` is their convolution
`(a * b).coeff h = ∑ a.coeff u * b.coeff v`, the sum running over the pairs `(u, v)` with
`u + v = h` and both coefficients nonzero. There are only finitely many such pairs
(`NovikovSeries.finite_setOf_add_eq`), because the periods of each support are bounded below and
only finitely many exponents of a series lie below any period cutoff. With this product the
Novikov series form a ring, the Novikov completion of the group ring `R[H]` along the period
filtration: it is the coefficient ring of the Novikov complex of a closed one-form and of capped
Hamiltonian Floer complexes.

All ring laws are proved by finite-support arguments. The basic tool is
`NovikovSeries.coeff_mul_eq_sum`: a coefficient of a product may be computed as a sum over any
finite set of pairs adding up to the exponent which contains every pair of support exponents.
Associativity rests on the uniform cutoff lemma `NovikovSeries.finite_setOf_period_add_add_lt`
for triples of support exponents.

The arrangement of the instances follows Mathlib's `HahnSeries` in
`Mathlib/RingTheory/HahnSeries/Multiplication.lean`; the support arguments are different, since
`H` carries no order here.

## Main definitions

* `TauCeti.NovikovSeries.instMul`: the convolution product.
* `TauCeti.NovikovSeries.instSemiring`, `TauCeti.NovikovSeries.instCommRing`, ...: the
  (commutative) (semi)ring structures, with unit the monomial `single 0 1`.
* `TauCeti.NovikovSeries.instAlgebra`: for an `S`-algebra `R`, Novikov series over `R` form an
  `S`-algebra, with `algebraMap S _ s = single 0 (algebraMap S R s)`.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra`: the group ring `R[H]` as a subring of Novikov
  series, by its coefficient map.

## Main results

* `TauCeti.NovikovSeries.coeff_mul_eq_sum`: computing a coefficient of a product over any finite
  set of pairs containing the pairs of support exponents.
* `TauCeti.NovikovSeries.support_mul_subset`: the support of a product lies in the sum of the
  supports.
* `TauCeti.NovikovSeries.single_mul_single`: monomials multiply by adding exponents.
* `TauCeti.NovikovSeries.isUnit_single`: over an additive group, a monomial with unit coefficient
  is a unit, with inverse the monomial at the negated exponent.
* `TauCeti.NovikovSeries.ofAddMonoidAlgebra_injective`: the group ring embeds into Novikov series;
  by `TauCeti.NovikovSeries.ofFinsupp_surjective_iff` this embedding is onto exactly when `N = 0`
  (for nontrivial `R`).

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
-/

public section

noncomputable section

open Finset Function

open scoped Pointwise

namespace TauCeti

namespace NovikovSeries

variable {R S T H : Type*}

section Finite

variable [Zero R] [Zero S] [Zero T] [AddZeroClass H] {N : H →+ ℝ}

/-- Uniform cutoff finiteness for triple products: for Novikov series `a`, `b` and `c`, only
finitely many triples `(u, v, w)` of support exponents have `N (u + v + w) < C`. -/
theorem finite_setOf_period_add_add_lt (a : NovikovSeries R H N) (b : NovikovSeries S H N)
    (c : NovikovSeries T H N) (C : ℝ) :
    {t : H × H × H | N (t.1 + t.2.1 + t.2.2) < C ∧ a.coeff t.1 ≠ 0 ∧ b.coeff t.2.1 ≠ 0 ∧
      c.coeff t.2.2 ≠ 0}.Finite := by
  obtain ⟨ma, hma⟩ := a.bddBelow_image_support
  obtain ⟨mb, hmb⟩ := b.bddBelow_image_support
  obtain ⟨mc, hmc⟩ := c.bddBelow_image_support
  refine ((a.finite_lt (C - mb - mc)).prod
    ((b.finite_lt (C - ma - mc)).prod (c.finite_lt (C - ma - mb)))).subset ?_
  rintro ⟨u, v, w⟩ ⟨huvw, hu, hv, hw⟩
  have hu' : ma ≤ N u := hma ⟨u, mem_support.2 hu, rfl⟩
  have hv' : mb ≤ N v := hmb ⟨v, mem_support.2 hv, rfl⟩
  have hw' : mc ≤ N w := hmc ⟨w, mem_support.2 hw, rfl⟩
  rw [map_add, map_add] at huvw
  exact ⟨⟨hu, by linarith⟩, ⟨hv, by linarith⟩, ⟨hw, by linarith⟩⟩

/-- For Novikov series `a`, `b` and `c` and an exponent `h`, only finitely many triples
`(u, v, w)` with `u + v + w = h` have all three coefficients nonzero. -/
theorem finite_setOf_add_add_eq (a : NovikovSeries R H N) (b : NovikovSeries S H N)
    (c : NovikovSeries T H N) (h : H) :
    {t : H × H × H | t.1 + t.2.1 + t.2.2 = h ∧ a.coeff t.1 ≠ 0 ∧ b.coeff t.2.1 ≠ 0 ∧
      c.coeff t.2.2 ≠ 0}.Finite :=
  (finite_setOf_period_add_add_lt a b c (N h + 1)).subset fun t ht =>
    ⟨by rw [ht.1]; exact lt_add_one _, ht.2⟩

end Finite

section Mul

variable [AddZeroClass H] {N : H →+ ℝ} [NonUnitalNonAssocSemiring R]

/-- The convolution product of Novikov series: the coefficient of `a * b` at `h` is the finite
sum of `a.coeff u * b.coeff v` over the pairs `(u, v)` of support exponents with `u + v = h`. -/
instance instMul : Mul (NovikovSeries R H N) where
  mul a b :=
    { coeff h := ∑ p ∈ (finite_setOf_add_eq a b h).toFinset, a.coeff p.1 * b.coeff p.2
      finite_lt C := ((finite_setOf_period_add_lt a b C).image fun p => p.1 + p.2).subset <| by
        rintro h ⟨hh, hC⟩
        obtain ⟨p, hp, -⟩ := exists_ne_zero_of_sum_ne_zero hh
        rw [Set.Finite.mem_toFinset] at hp
        exact ⟨p, ⟨by rw [hp.1]; exact hC, hp.2⟩, hp.1⟩ }

/-- The coefficient of `a * b` at `h`, as a sum over the finite set of pairs of support exponents
adding up to `h`. -/
theorem coeff_mul (a b : NovikovSeries R H N) (h : H) :
    (a * b).coeff h = ∑ p ∈ (finite_setOf_add_eq a b h).toFinset, a.coeff p.1 * b.coeff p.2 :=
  rfl

/-- A coefficient of a product is the sum of `a.coeff p.1 * b.coeff p.2` over any finite set of
pairs `p` with `p.1 + p.2 = h` containing every such pair of support exponents. -/
theorem coeff_mul_eq_sum {a b : NovikovSeries R H N} {h : H} {s : Finset (H × H)}
    (hs : ∀ p ∈ s, p.1 + p.2 = h)
    (hab : ∀ u v, u + v = h → a.coeff u ≠ 0 → b.coeff v ≠ 0 → (u, v) ∈ s) :
    (a * b).coeff h = ∑ p ∈ s, a.coeff p.1 * b.coeff p.2 := by
  rw [coeff_mul]
  refine sum_subset (fun p hp => ?_) fun p hps hp => ?_
  · rw [Set.Finite.mem_toFinset] at hp
    exact hab p.1 p.2 hp.1 hp.2.1 hp.2.2
  · rw [Set.Finite.mem_toFinset] at hp
    by_cases ha : a.coeff p.1 = 0
    · rw [ha, zero_mul]
    by_cases hb : b.coeff p.2 = 0
    · rw [hb, mul_zero]
    exact absurd ⟨hs p hps, ha, hb⟩ hp

/-- A nonzero coefficient of a product comes from a pair of support exponents. -/
theorem exists_add_eq_of_coeff_mul_ne_zero {a b : NovikovSeries R H N} {h : H}
    (hab : (a * b).coeff h ≠ 0) : ∃ u v, u + v = h ∧ a.coeff u ≠ 0 ∧ b.coeff v ≠ 0 := by
  obtain ⟨p, hp, -⟩ := exists_ne_zero_of_sum_ne_zero hab
  rw [Set.Finite.mem_toFinset] at hp
  exact ⟨p.1, p.2, hp⟩

/-- The support of a product lies in the sum of the supports. -/
theorem support_mul_subset (a b : NovikovSeries R H N) :
    (a * b).support ⊆ a.support + b.support := fun h hh => by
  obtain ⟨u, v, huv, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero (mem_support.1 hh)
  exact ⟨u, mem_support.2 hu, v, mem_support.2 hv, huv⟩

/-- Monomials multiply by adding exponents. -/
@[simp]
theorem single_mul_single (g g' : H) (r r' : R) :
    (single g r * single g' r' : NovikovSeries R H N) = single (g + g') (r * r') := by
  classical
  ext h
  rw [coeff_mul_eq_sum (s := ({(g, g')} : Finset (H × H)).filter fun p => p.1 + p.2 = h)
    (fun p hp => (mem_filter.1 hp).2) fun u v huv hu hv => ?_]
  · by_cases hh : h = g + g'
    · subst hh
      rw [filter_true_of_mem fun p hp => by rw [mem_singleton.1 hp], sum_singleton,
        coeff_single_same, coeff_single_same, coeff_single_same]
    · rw [coeff_single_of_ne hh]
      simp [filter_singleton, Ne.symm hh]
  · have hu : u = g := by_contra fun hug => hu (coeff_single_of_ne hug r)
    have hv : v = g' := by_contra fun hvg => hv (coeff_single_of_ne hvg r')
    subst hu hv
    exact mem_filter.2 ⟨mem_singleton_self _, huv⟩

/-- Multiplying by a constant series `single 0 r` multiplies each coefficient on the left. -/
theorem coeff_single_zero_mul (r : R) (a : NovikovSeries R H N) (h : H) :
    (single 0 r * a).coeff h = r * a.coeff h := by
  rw [coeff_mul_eq_sum (s := {(0, h)}) (fun p hp => by rw [mem_singleton.1 hp, zero_add])
    fun u v huv hu _ => ?_, sum_singleton, coeff_single_same]
  have hu : u = 0 := by_contra fun hu0 => hu (coeff_single_of_ne hu0 r)
  subst hu
  rw [zero_add] at huv
  rw [huv, mem_singleton]

/-- Multiplying by a constant series `single 0 r` multiplies each coefficient on the right. -/
@[simp]
theorem coeff_mul_single_zero (a : NovikovSeries R H N) (r : R) (h : H) :
    (a * single 0 r).coeff h = a.coeff h * r := by
  rw [coeff_mul_eq_sum (s := {(h, 0)}) (fun p hp => by rw [mem_singleton.1 hp, add_zero])
    fun u v huv _ hv => ?_, sum_singleton, coeff_single_same]
  have hv : v = 0 := by_contra fun hv0 => hv (coeff_single_of_ne hv0 r)
  subst hv
  rw [add_zero] at huv
  rw [huv, mem_singleton]

/-- Convolution distributes over addition. -/
instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (NovikovSeries R H N) where
  left_distrib a b c := by
    classical
    ext h
    have hs : ∀ p ∈ (finite_setOf_add_eq a b h).toFinset ∪ (finite_setOf_add_eq a c h).toFinset,
        p.1 + p.2 = h := fun p hp => by
      rcases mem_union.1 hp with hp | hp <;> exact ((Set.Finite.mem_toFinset _).1 hp).1
    have hmem (u v : H) (huv : u + v = h) (hu : a.coeff u ≠ 0)
        (hv : b.coeff v ≠ 0 ∨ c.coeff v ≠ 0) :
        (u, v) ∈ (finite_setOf_add_eq a b h).toFinset ∪ (finite_setOf_add_eq a c h).toFinset := by
      rcases hv with hv | hv
      · exact mem_union_left _ ((Set.Finite.mem_toFinset _).2 ⟨huv, hu, hv⟩)
      · exact mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨huv, hu, hv⟩)
    rw [coeff_add, coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv hu (Or.inl hv),
      coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv hu (Or.inr hv),
      coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv hu <| by
        by_contra! hbc
        exact hv (by rw [coeff_add, hbc.1, hbc.2, add_zero]),
      ← sum_add_distrib]
    simp only [coeff_add, mul_add]
  right_distrib a b c := by
    classical
    ext h
    have hs : ∀ p ∈ (finite_setOf_add_eq a c h).toFinset ∪ (finite_setOf_add_eq b c h).toFinset,
        p.1 + p.2 = h := fun p hp => by
      rcases mem_union.1 hp with hp | hp <;> exact ((Set.Finite.mem_toFinset _).1 hp).1
    have hmem (u v : H) (huv : u + v = h) (hu : a.coeff u ≠ 0 ∨ b.coeff u ≠ 0)
        (hv : c.coeff v ≠ 0) :
        (u, v) ∈ (finite_setOf_add_eq a c h).toFinset ∪ (finite_setOf_add_eq b c h).toFinset := by
      rcases hu with hu | hu
      · exact mem_union_left _ ((Set.Finite.mem_toFinset _).2 ⟨huv, hu, hv⟩)
      · exact mem_union_right _ ((Set.Finite.mem_toFinset _).2 ⟨huv, hu, hv⟩)
    rw [coeff_add, coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv (Or.inl hu) hv,
      coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv (Or.inr hu) hv,
      coeff_mul_eq_sum hs fun u v huv hu hv => hmem u v huv (by
        by_contra! hab
        exact hu (by rw [coeff_add, hab.1, hab.2, add_zero])) hv,
      ← sum_add_distrib]
    simp only [coeff_add, add_mul]
  zero_mul a := by
    ext h
    simp [coeff_mul]
  mul_zero a := by
    ext h
    simp [coeff_mul]

end Mul

section Semiring

section AddZeroClass

variable [AddZeroClass H] {N : H →+ ℝ}

/-- The unit of convolution is the monomial `single 0 1`. -/
instance instOne [Zero R] [One R] : One (NovikovSeries R H N) where
  one := single 0 1

theorem one_def [Zero R] [One R] :
    (1 : NovikovSeries R H N) = single 0 1 :=
  rfl

instance instNonAssocSemiring [NonAssocSemiring R] :
    NonAssocSemiring (NovikovSeries R H N) where
  one_mul a := by
    ext h
    rw [one_def, coeff_single_zero_mul, one_mul]
  mul_one a := by
    ext h
    rw [one_def, coeff_mul_single_zero, mul_one]

/-- Multiplying by a constant series is scalar multiplication. -/
@[simp]
theorem single_zero_mul_eq_smul [NonAssocSemiring R] (r : R)
    (a : NovikovSeries R H N) : single 0 r * a = r • a := by
  ext h
  rw [coeff_single_zero_mul, coeff_smul, smul_eq_mul]

instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (NovikovSeries R H N) where

instance instNonAssocRing [NonAssocRing R] :
    NonAssocRing (NovikovSeries R H N) where

end AddZeroClass

section AddMonoid

variable [AddMonoid H] {N : H →+ ℝ}

/-- The coefficient at `h` of a triple product `a * b * c` is the sum of
`a.coeff u * b.coeff v * c.coeff w` over the finitely many triples of support exponents with
`u + v + w = h`. -/
private theorem coeff_mul_mul_eq_sum [NonUnitalSemiring R] (a b c : NovikovSeries R H N) (h : H) :
    (a * b * c).coeff h = ∑ t ∈ (finite_setOf_add_add_eq a b c h).toFinset,
      a.coeff t.1 * b.coeff t.2.1 * c.coeff t.2.2 := by
  classical
  set T := (finite_setOf_add_add_eq a b c h).toFinset
  have hT (t : H × H × H) : t ∈ T ↔ t.1 + t.2.1 + t.2.2 = h ∧ a.coeff t.1 ≠ 0 ∧
      b.coeff t.2.1 ≠ 0 ∧ c.coeff t.2.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  -- Group the triples by the outer pair `(u + v, w)`.
  have hs : ∀ p ∈ T.image fun t => (t.1 + t.2.1, t.2.2), p.1 + p.2 = h := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    exact ((hT t).1 ht).1
  have habc : ∀ w z, w + z = h → (a * b).coeff w ≠ 0 → c.coeff z ≠ 0 →
      (w, z) ∈ T.image fun t => (t.1 + t.2.1, t.2.2) := by
    intro w z hwz hw hz
    obtain ⟨u, v, huv, hu, hv⟩ := exists_add_eq_of_coeff_mul_ne_zero hw
    exact mem_image.2 ⟨(u, v, z), (hT _).2 ⟨by rw [huv, hwz], hu, hv, hz⟩, by rw [huv]⟩
  rw [coeff_mul_eq_sum hs habc]
  refine sum_image' _ fun t ht => ?_
  -- The inner coefficient `(a * b).coeff (u + v)` is a sum over the fibre through `t`.
  set F := T.filter fun t' => (t'.1 + t'.2.1, t'.2.2) = (t.1 + t.2.1, t.2.2)
  have hF (t' : H × H × H) (ht' : t' ∈ F) : t'.1 + t'.2.1 = t.1 + t.2.1 ∧ t'.2.2 = t.2.2 :=
    Prod.ext_iff.1 (mem_filter.1 ht').2
  have hs' : ∀ p ∈ F.image fun t' => (t'.1, t'.2.1), p.1 + p.2 = t.1 + t.2.1 := by
    intro p hp
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hp
    exact (hF t' ht').1
  have hab : ∀ u v, u + v = t.1 + t.2.1 → a.coeff u ≠ 0 → b.coeff v ≠ 0 →
      (u, v) ∈ F.image fun t' => (t'.1, t'.2.1) := by
    intro u v huv hu hv
    refine mem_image.2 ⟨(u, v, t.2.2), mem_filter.2 ⟨(hT _).2 ⟨?_, hu, hv, ((hT t).1 ht).2.2.2⟩,
      by rw [huv]⟩, rfl⟩
    rw [huv]
    exact ((hT t).1 ht).1
  have hinj : Set.InjOn (fun t' : H × H × H => (t'.1, t'.2.1)) F := by
    intro t₁ ht₁ t₂ ht₂ h₁₂
    simp only [Prod.mk.injEq] at h₁₂
    exact Prod.ext h₁₂.1 (Prod.ext h₁₂.2 ((hF t₁ ht₁).2.trans (hF t₂ ht₂).2.symm))
  rw [coeff_mul_eq_sum hs' hab, sum_image hinj, sum_mul]
  exact sum_congr rfl fun t' ht' => by rw [(hF t' ht').2]

/-- The coefficient at `h` of a triple product `a * (b * c)` is the sum of
`a.coeff u * (b.coeff v * c.coeff w)` over the finitely many triples of support exponents with
`u + v + w = h`. -/
private theorem coeff_mul_mul_eq_sum' [NonUnitalSemiring R] (a b c : NovikovSeries R H N)
    (h : H) :
    (a * (b * c)).coeff h = ∑ t ∈ (finite_setOf_add_add_eq a b c h).toFinset,
      a.coeff t.1 * (b.coeff t.2.1 * c.coeff t.2.2) := by
  classical
  set T := (finite_setOf_add_add_eq a b c h).toFinset
  have hT (t : H × H × H) : t ∈ T ↔ t.1 + t.2.1 + t.2.2 = h ∧ a.coeff t.1 ≠ 0 ∧
      b.coeff t.2.1 ≠ 0 ∧ c.coeff t.2.2 ≠ 0 :=
    Set.Finite.mem_toFinset _
  -- Group the triples by the outer pair `(u, v + w)`.
  have hs : ∀ p ∈ T.image fun t => (t.1, t.2.1 + t.2.2), p.1 + p.2 = h := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [← add_assoc]
    exact ((hT t).1 ht).1
  have habc : ∀ u w, u + w = h → a.coeff u ≠ 0 → (b * c).coeff w ≠ 0 →
      (u, w) ∈ T.image fun t => (t.1, t.2.1 + t.2.2) := by
    intro u w huw hu hw
    obtain ⟨v, z, hvz, hv, hz⟩ := exists_add_eq_of_coeff_mul_ne_zero hw
    exact mem_image.2 ⟨(u, v, z), (hT _).2 ⟨by rw [add_assoc, hvz, huw], hu, hv, hz⟩,
      by rw [hvz]⟩
  rw [coeff_mul_eq_sum hs habc]
  refine sum_image' _ fun t ht => ?_
  -- The inner coefficient `(b * c).coeff (v + w)` is a sum over the fibre through `t`.
  set F := T.filter fun t' => (t'.1, t'.2.1 + t'.2.2) = (t.1, t.2.1 + t.2.2)
  have hF (t' : H × H × H) (ht' : t' ∈ F) : t'.1 = t.1 ∧ t'.2.1 + t'.2.2 = t.2.1 + t.2.2 :=
    Prod.ext_iff.1 (mem_filter.1 ht').2
  have hs' : ∀ p ∈ F.image fun t' => t'.2, p.1 + p.2 = t.2.1 + t.2.2 := by
    intro p hp
    obtain ⟨t', ht', rfl⟩ := mem_image.1 hp
    exact (hF t' ht').2
  have hbc : ∀ v z, v + z = t.2.1 + t.2.2 → b.coeff v ≠ 0 → c.coeff z ≠ 0 →
      (v, z) ∈ F.image fun t' => t'.2 := by
    intro v z hvz hv hz
    refine mem_image.2 ⟨(t.1, v, z), mem_filter.2 ⟨(hT _).2 ⟨?_, ((hT t).1 ht).2.1, hv, hz⟩,
      by rw [hvz]⟩, rfl⟩
    rw [add_assoc, hvz, ← add_assoc]
    exact ((hT t).1 ht).1
  have hinj : Set.InjOn (fun t' : H × H × H => t'.2) F :=
    fun t₁ ht₁ t₂ ht₂ h₁₂ => Prod.ext ((hF t₁ ht₁).1.trans (hF t₂ ht₂).1.symm) h₁₂
  rw [coeff_mul_eq_sum hs' hbc, sum_image hinj, mul_sum]
  exact sum_congr rfl fun t' ht' => by rw [(hF t' ht').1]

/-- Convolution is associative, by the uniform cutoff lemma
`NovikovSeries.finite_setOf_period_add_add_lt`. -/
instance instNonUnitalSemiring [NonUnitalSemiring R] :
    NonUnitalSemiring (NovikovSeries R H N) where
  mul_assoc a b c := by
    ext h
    rw [coeff_mul_mul_eq_sum, coeff_mul_mul_eq_sum']
    exact sum_congr rfl fun t _ => mul_assoc _ _ _

instance instSemiring [Semiring R] : Semiring (NovikovSeries R H N) where

instance instNonUnitalRing [NonUnitalRing R] :
    NonUnitalRing (NovikovSeries R H N) where

instance instRing [Ring R] : Ring (NovikovSeries R H N) where

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid H] {N : H →+ ℝ}

instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] :
    NonUnitalCommSemiring (NovikovSeries R H N) where
  mul_comm a b := by
    classical
    ext h
    set F := (finite_setOf_add_eq a b h).toFinset
    have hF (p : H × H) : p ∈ F ↔ p.1 + p.2 = h ∧ a.coeff p.1 ≠ 0 ∧ b.coeff p.2 ≠ 0 :=
      Set.Finite.mem_toFinset _
    have hs : ∀ p ∈ F.image Prod.swap, p.1 + p.2 = h := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := mem_image.1 hp
      rw [Prod.fst_swap, Prod.snd_swap, add_comm]
      exact ((hF q).1 hq).1
    have hba : ∀ v u, v + u = h → b.coeff v ≠ 0 → a.coeff u ≠ 0 → (v, u) ∈ F.image Prod.swap :=
      fun v u hvu hv hu => mem_image.2 ⟨(u, v), (hF _).2 ⟨by rw [add_comm, hvu], hu, hv⟩, rfl⟩
    rw [coeff_mul a b, coeff_mul_eq_sum hs hba, sum_image Prod.swap_injective.injOn]
    exact sum_congr rfl fun p _ => mul_comm _ _

instance instCommSemiring [CommSemiring R] :
    CommSemiring (NovikovSeries R H N) where

instance instNonUnitalCommRing [NonUnitalCommRing R] :
    NonUnitalCommRing (NovikovSeries R H N) where

instance instCommRing [CommRing R] : CommRing (NovikovSeries R H N) where

end AddCommMonoid

end Semiring

section Group

variable [AddGroup H] {N : H →+ ℝ}

/-- Multiplying by a monomial shifts the exponents. -/
theorem coeff_single_mul [NonUnitalNonAssocSemiring R] (g : H) (r : R)
    (a : NovikovSeries R H N) (h : H) : (single g r * a).coeff h = r * a.coeff (-g + h) := by
  rw [coeff_mul_eq_sum (s := {(g, -g + h)}) (fun p hp => by
      rw [mem_singleton.1 hp, add_neg_cancel_left])
    fun u v huv hu _ => ?_, sum_singleton, coeff_single_same]
  have hu : u = g := by_contra fun hug => hu (coeff_single_of_ne hug r)
  subst hu
  rw [mem_singleton, eq_neg_add_of_add_eq huv]

/-- Multiplying by a monomial shifts the exponents. -/
theorem coeff_mul_single [NonUnitalNonAssocSemiring R] (a : NovikovSeries R H N) (g : H) (r : R)
    (h : H) : (a * single g r).coeff h = a.coeff (h - g) * r := by
  rw [coeff_mul_eq_sum (s := {(h - g, g)}) (fun p hp => by
      rw [mem_singleton.1 hp, sub_add_cancel])
    fun u v huv _ hv => ?_, sum_singleton, coeff_single_same]
  have hv : v = g := by_contra fun hvg => hv (coeff_single_of_ne hvg r)
  subst hv
  rw [mem_singleton, eq_sub_of_add_eq huv]

/-- A monomial `r e^g` with unit coefficient is a unit, with inverse `r⁻¹ e^(-g)`. -/
theorem isUnit_single [Semiring R] (g : H) {r : R} (hr : IsUnit r) :
    IsUnit (single g r : NovikovSeries R H N) := by
  obtain ⟨u, rfl⟩ := hr
  exact ⟨⟨single g u, single (-g) ↑u⁻¹, by simp [one_def], by simp [one_def]⟩, rfl⟩

end Group

section Algebra

variable [AddMonoid H] {N : H →+ ℝ} [CommSemiring S] [Semiring R] [Algebra S R]

/-- For an `S`-algebra `R`, Novikov series over `R` form an `S`-algebra: a scalar `s` acts as
the constant series `single 0 (algebraMap S R s)`. -/
instance instAlgebra : Algebra S (NovikovSeries R H N) where
  algebraMap :=
    { toFun s := single 0 (algebraMap S R s)
      map_one' := by rw [map_one, one_def]
      map_mul' s s' := by rw [map_mul, single_mul_single, add_zero]
      map_zero' := by rw [map_zero, single_zero]
      map_add' s s' := by rw [map_add, single_add] }
  commutes' s a := by
    ext h
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [coeff_single_zero_mul, coeff_mul_single_zero, Algebra.commutes]
  smul_def' s a := by
    ext h
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [coeff_single_zero_mul, coeff_smul, Algebra.smul_def]

@[simp]
theorem algebraMap_apply (s : S) :
    algebraMap S (NovikovSeries R H N) s = single 0 (algebraMap S R s) :=
  rfl

end Algebra

section AddMonoidAlgebra

variable [AddMonoid H] {N : H →+ ℝ} [Semiring R]

open AddMonoidAlgebra in
/-- The group ring `R[H]` as a subring of Novikov series: an element is sent to the Novikov
series with the same (finitely supported) coefficients. -/
def ofAddMonoidAlgebra : R[H] →+* NovikovSeries R H N where
  toFun x := ofFinsupp x.coeff
  map_one' := by
    rw [one_def, ← ofFinsupp_single]
    rfl
  map_mul' x y := by
    classical
    ext h
    rw [coeff_ofFinsupp, coeff_mul_eq_sum
      (s := (x.coeff.support ×ˢ y.coeff.support).filter fun p => p.1 + p.2 = h)
      (fun p hp => (mem_filter.1 hp).2) fun u v huv hu hv => mem_filter.2
        ⟨mem_product.2 ⟨Finsupp.mem_support_iff.2 (by rwa [coeff_ofFinsupp] at hu),
          Finsupp.mem_support_iff.2 (by rwa [coeff_ofFinsupp] at hv)⟩, huv⟩]
    simp only [coeff_ofFinsupp]
    rw [sum_filter, sum_product, AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
  map_zero' := map_zero ofFinsupp
  map_add' x y := map_add ofFinsupp x.coeff y.coeff

@[simp]
theorem coeff_ofAddMonoidAlgebra (x : AddMonoidAlgebra R H) :
    (ofAddMonoidAlgebra x : NovikovSeries R H N).coeff = x.coeff :=
  coeff_ofFinsupp x.coeff

@[simp]
theorem ofAddMonoidAlgebra_single (h : H) (r : R) :
    (ofAddMonoidAlgebra (AddMonoidAlgebra.single h r) : NovikovSeries R H N) = single h r :=
  ofFinsupp_single h r

theorem ofAddMonoidAlgebra_injective :
    Injective (ofAddMonoidAlgebra : AddMonoidAlgebra R H → NovikovSeries R H N) :=
  fun _ _ hxy => AddMonoidAlgebra.coeff_injective (ofFinsupp_injective hxy)

end AddMonoidAlgebra

end NovikovSeries

end TauCeti

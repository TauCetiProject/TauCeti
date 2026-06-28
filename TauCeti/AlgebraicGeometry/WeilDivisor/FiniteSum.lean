/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Indicator
public import TauCeti.AlgebraicGeometry.WeilDivisor

/-!
# Finite sums of point divisors

This file adds an API for the effective Weil divisors represented by finitely supported
natural-number multiplicities and by named finite-set constructors. These are the formal
Layer A divisor objects that later receive geometric restrictions from symmetric powers and
relative effective divisors: before any scheme-level construction exists, a finite collection
of points gives the divisor `Σ nₓ[x]`.

The API records the coefficient, support, degree, weighted degree, pushforward, and degree-zero
normal forms needed by the existing Abel-Jacobi and linear-system files.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve:
Weil divisors `⊕_x ℤ`" and "Degree", and supplies a clean formal prerequisite for the Layer C/D
Abel-map lane `D ↦ 𝒪_X(D - d·x₀)` from symmetric powers. No external mathematics is vendored;
the proofs use Tau Ceti's `WeilDivisor.ofPoint`, `degree`, `weightedDegree`, and `pushforward`
API together with Mathlib's finite-sum lemmas.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

private lemma coeff_zsmul_ofPoint (n : ℤ) (y x : X) :
    coeff (n • ofPoint y : WeilDivisor X) x = n * coeff (ofPoint y) x := by
  simp [coeff]

private lemma coeff_sum_zsmul_ofPoint_of_mem {s : Finset X} {a : X → ℤ} {x : X}
    (hxs : x ∈ s) :
    coeff (∑ y ∈ s, a y • ofPoint y : WeilDivisor X) x = a x := by
  classical
  rw [coeff]
  rw [Finset.sum_apply', Finset.sum_eq_single x]
  · rw [← coeff, coeff_zsmul_ofPoint, coeff_ofPoint_self, mul_one]
  · intro y hy hyx
    have hxy : x ≠ y := fun h => hyx h.symm
    rw [← coeff, coeff_zsmul_ofPoint, coeff_ofPoint_of_ne hxy, mul_zero]
  · intro hx
    exact (hx hxs).elim

private lemma coeff_sum_zsmul_ofPoint_of_notMem {s : Finset X} {a : X → ℤ} {x : X}
    (hxs : x ∉ s) :
    coeff (∑ y ∈ s, a y • ofPoint y : WeilDivisor X) x = 0 := by
  classical
  rw [coeff, Finset.sum_apply']
  exact Finset.sum_eq_zero fun y hy => by
    have hxy : x ≠ y := fun h => hxs (h.symm ▸ hy)
    rw [← coeff, coeff_zsmul_ofPoint, coeff_ofPoint_of_ne hxy, mul_zero]

/-! ### Finitely supported multiplicities via `Finsupp.mapRange` -/

/-- Coefficients of `Finsupp.mapRange` from natural multiplicities are the multiplicities. -/
@[simp]
lemma coeff_mapRange_natCast (m : X →₀ ℕ) (x : X) :
    coeff (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) x =
      m x := by
  simp [coeff]

/-- Finitely supported natural multiplicities give effective divisors. -/
@[simp]
lemma isEffective_mapRange_natCast (m : X →₀ ℕ) :
    IsEffective (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) := by
  rw [isEffective_iff]
  intro x
  simp

/-- The divisor from finitely supported multiplicities is the corresponding sum of point
divisors over the support. -/
lemma mapRange_natCast_eq_sum (m : X →₀ ℕ) :
    (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) • ofPoint x := by
  classical
  ext x
  by_cases hxs : x ∈ m.support
  · rw [coeff_mapRange_natCast, coeff_sum_zsmul_ofPoint_of_mem hxs]
  · have hmx : m x = 0 := by
      simpa [Finsupp.mem_support_iff] using hxs
    rw [coeff_mapRange_natCast, coeff_sum_zsmul_ofPoint_of_notMem hxs, hmx]
    simp

/-- The support of the divisor from finitely supported natural multiplicities is the support
of those multiplicities. -/
@[simp]
lemma support_mapRange_natCast (m : X →₀ ℕ) :
    (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X).support =
      m.support := by
  classical
  ext x
  rw [mem_support_iff, coeff_mapRange_natCast, Finsupp.mem_support_iff]
  exact Int.natCast_ne_zero

/-- The degree of a divisor from finitely supported multiplicities is the sum over the support. -/
@[simp]
lemma degree_mapRange_natCast (m : X →₀ ℕ) :
    degree (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) := by
  classical
  simp [mapRange_natCast_eq_sum]

/-- The weighted degree of a divisor from finitely supported multiplicities is the weighted
sum over the support. -/
@[simp]
lemma weightedDegree_mapRange_natCast (w : X → ℤ) (m : X →₀ ℕ) :
    weightedDegree w
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) * w x := by
  classical
  simp [mapRange_natCast_eq_sum, mul_comm]

/-- Pushing forward a divisor from finitely supported multiplicities applies the map to each
point in the support sum. -/
@[simp]
lemma pushforward_mapRange_natCast (f : X → Y) (m : X →₀ ℕ) :
    pushforward f
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m : WeilDivisor X) =
      ∑ x ∈ m.support, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [mapRange_natCast_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-! ### Finite-set multiplicities via `Finsupp.indicator` -/

/-- Coefficient formula for `Finsupp.indicator` with natural-number multiplicities. -/
@[simp]
lemma coeff_indicator_nat [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) x =
      if x ∈ s then m x else 0 := by
  simp [coeff, Finsupp.indicator_apply]

/-- The `Finsupp.indicator` divisor with multiplicities agrees with the corresponding finite sum
of point divisors. -/
lemma indicator_nat_eq_sum (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  classical
  ext x
  by_cases hxs : x ∈ s
  · rw [coeff_indicator_nat, coeff_sum_zsmul_ofPoint_of_mem hxs, if_pos hxs]
  · rw [coeff_indicator_nat, coeff_sum_zsmul_ofPoint_of_notMem hxs, if_neg hxs]
    simp

/-- The `Finsupp.indicator` divisor with natural multiplicities over the empty set is zero. -/
@[simp]
lemma indicator_nat_empty (m : X → ℕ) :
    (Finsupp.indicator (∅ : Finset X) (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 := by
  classical
  ext x
  simp

/-- Inserting a new point in `Finsupp.indicator` splits off its weighted point divisor. -/
@[simp]
lemma indicator_nat_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    (Finsupp.indicator (insert x s) (fun y _ => (m y : ℤ)) : WeilDivisor X) =
      (m x : ℤ) • ofPoint x + Finsupp.indicator s (fun y _ => (m y : ℤ)) := by
  rw [indicator_nat_eq_sum, indicator_nat_eq_sum]
  simp [hx]

/-- `Finsupp.indicator` with natural-number multiplicities is an effective divisor. -/
@[simp]
lemma isEffective_indicator_nat (s : Finset X) (m : X → ℕ) :
    IsEffective (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) := by
  classical
  rw [isEffective_iff]
  intro x
  simp only [coeff_indicator_nat]
  split_ifs <;> simp

/-- `Finsupp.indicator` with natural-number multiplicities belongs to the effective divisor
submonoid. -/
@[simp]
lemma indicator_nat_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_indicator_nat s m)

/-- The support of `Finsupp.indicator` with multiplicities is contained in the chosen finite set.
Points in the set whose multiplicity is zero may drop out of the support. -/
lemma support_indicator_nat_subset (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X).support ⊆ s :=
  Finsupp.support_indicator_subset s (fun x _ => (m x : ℤ))

/-- A point is in the support of `Finsupp.indicator` with multiplicities exactly when it is
selected and has nonzero multiplicity. -/
@[simp]
lemma mem_support_indicator_nat_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X).support ↔
      x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_indicator_nat]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of `Finsupp.indicator` with multiplicities is the sum of the multiplicities. -/
@[simp]
lemma degree_indicator_nat (s : Finset X) (m : X → ℕ) :
    degree (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [indicator_nat_eq_sum]

/-- The weighted degree of `Finsupp.indicator` with multiplicities is the corresponding weighted
finite sum. -/
@[simp]
lemma weightedDegree_indicator_nat (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [indicator_nat_eq_sum, mul_comm]

/-- Pushing forward `Finsupp.indicator` with multiplicities applies the map to each point in the
finite sum. -/
@[simp]
lemma pushforward_indicator_nat (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [indicator_nat_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights at the selected points with nonzero multiplicity, an indicator divisor
with multiplicities has weighted degree zero exactly when every selected multiplicity vanishes. -/
lemma weightedDegree_indicator_nat_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (m : X → ℕ) (hw : ∀ x ∈ s, m x ≠ 0 → 0 < w x) :
    weightedDegree w (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 ↔
      ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    have hzero :
        (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 :=
      (isEffective_indicator_nat s m).eq_zero_of_weightedDegree_eq_zero_of_pos_on_support
        (fun y hy => by
          obtain ⟨hys, hmy⟩ := mem_support_indicator_nat_iff.mp hy
          exact hw y hys hmy)
        hdeg
    have hcoeff := congrArg (fun D : WeilDivisor X => coeff D x) hzero
    simpa [coeff_indicator_nat, hx] using hcoeff
  · intro hm
    rw [weightedDegree_indicator_nat]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- An indicator divisor with positive weights at selected points with nonzero multiplicity lies
in the weighted degree-zero subgroup exactly when all selected multiplicities vanish. -/
lemma indicator_nat_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (m : X → ℕ) (hw : ∀ x ∈ s, m x ≠ 0 → 0 < w x) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈
        weightedDegreeZeroSubgroup w ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup, weightedDegree_indicator_nat_eq_zero_iff_of_pos s m hw]

/-- An indicator divisor with multiplicities has unweighted degree zero exactly when every
selected multiplicity vanishes. -/
lemma indicator_nat_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈ degreeZeroSubgroup X ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_indicator_nat_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) s m (fun _ _ _ => zero_lt_one)

/-! ### Finite sums with coefficient one via `Finsupp.indicator` -/

/-- The coefficient-one `Finsupp.indicator` divisor is the corresponding finite sum of point
divisors. -/
lemma indicator_one_eq_sum (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) = ∑ x ∈ s, ofPoint x := by
  simpa using indicator_nat_eq_sum (s := s) (m := fun _ : X => 1)

/-- The coefficient-one `Finsupp.indicator` divisor over the empty set is zero. -/
@[simp]
lemma indicator_one_empty :
    (Finsupp.indicator (∅ : Finset X) (fun _ _ => (1 : ℤ)) : WeilDivisor X) = 0 := by
  simpa using indicator_nat_empty (X := X) (fun _ : X => 1)

/-- Inserting a new point in a coefficient-one indicator splits off its point divisor. -/
@[simp]
lemma indicator_one_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    (Finsupp.indicator (insert x s) (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ofPoint x + Finsupp.indicator s (fun _ _ => (1 : ℤ)) := by
  simpa using indicator_nat_insert (s := s) (x := x) hx (fun _ : X => 1)

/-- Coefficients of the coefficient-one indicator divisor are `1` on the set and `0` off it. -/
@[simp]
lemma coeff_indicator_one [DecidableEq X] (s : Finset X) (x : X) :
    coeff (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) x =
      if x ∈ s then 1 else 0 := by
  simp [coeff, Finsupp.indicator_apply]

/-- The coefficient-one indicator divisor is effective. -/
@[simp]
lemma isEffective_indicator_one (s : Finset X) :
    IsEffective (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) := by
  classical
  simpa using isEffective_indicator_nat (X := X) s (fun _ => 1)

/-- The coefficient-one indicator divisor belongs to the effective divisor submonoid. -/
@[simp]
lemma indicator_one_mem_effectiveSubmonoid (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_indicator_one s)

/-- The support of the coefficient-one indicator divisor is exactly the chosen finite set. -/
@[simp]
lemma support_indicator_one (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X).support = s := by
  classical
  ext x
  simp

/-- The degree of the coefficient-one indicator divisor is the finite set's cardinality. -/
@[simp]
lemma degree_indicator_one (s : Finset X) :
    degree (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) = s.card := by
  classical
  simpa using degree_indicator_nat (s := s) (m := fun _ : X => 1)

/-- The weighted degree of the coefficient-one indicator divisor is the sum of weights on it. -/
@[simp]
lemma weightedDegree_indicator_one (w : X → ℤ) (s : Finset X) :
    weightedDegree w (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, w x := by
  classical
  simpa using weightedDegree_indicator_nat (w := w) (s := s) (m := fun _ : X => 1)

/-- Pushing forward the coefficient-one indicator divisor applies the map to each point. -/
@[simp]
lemma pushforward_indicator_one (f : X → Y) (s : Finset X) :
    pushforward f (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, ofPoint (f x) := by
  classical
  simpa using pushforward_indicator_nat (f := f) (s := s) (m := fun _ : X => 1)

private lemma forall_mem_one_eq_zero_iff_empty (s : Finset X) :
    (∀ x ∈ s, (1 : ℕ) = 0) ↔ s = ∅ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      exact (one_ne_zero (h x hx)).elim
    · intro hx
      exact (Finset.notMem_empty x hx).elim
  · intro hs x hx
    simp [hs] at hx

/-- For positive weights, a coefficient-one indicator divisor lies in the weighted degree-zero
subgroup exactly when the finite set is empty. -/
lemma indicator_one_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈
        weightedDegreeZeroSubgroup w ↔
      s = ∅ := by
  classical
  exact (indicator_nat_mem_weightedDegreeZeroSubgroup_iff_of_pos s
    (fun _ : X => 1) (fun x hx _ => hw x hx)).trans
    (forall_mem_one_eq_zero_iff_empty s)

/-- A coefficient-one indicator divisor has unweighted degree zero exactly when the set is empty. -/
lemma indicator_one_mem_degreeZeroSubgroup_iff (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈ degreeZeroSubgroup X ↔
      s = ∅ := by
  classical
  exact (indicator_nat_mem_degreeZeroSubgroup_iff (s := s) (m := fun _ : X => 1)).trans
    (forall_mem_one_eq_zero_iff_empty s)

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti

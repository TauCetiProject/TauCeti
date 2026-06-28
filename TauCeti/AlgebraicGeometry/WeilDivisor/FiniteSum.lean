/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor

/-!
# Finite sums of point divisors

This file adds constructors for the effective Weil divisors represented by a finite set of
points, or by a finite set together with natural-number multiplicities.  These are the formal
Layer A divisor objects that later receive geometric restrictions from symmetric powers and
relative effective divisors: before any scheme-level construction exists, a finite collection of
points gives the divisor `Σ nₓ[x]`.

The API records the coefficient, support, degree, weighted degree, pushforward, and degree-zero
normal forms needed by the existing Abel-Jacobi and linear-system files.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, "Divisors on a curve:
Weil divisors `⊕_x ℤ`" and "Degree", and supplies a clean formal prerequisite for the Layer C/D
Abel-map lane `D ↦ 𝒪_X(D - d·x₀)` from symmetric powers.  No external mathematics is vendored;
the proofs use Tau Ceti's `WeilDivisor.ofPoint`, `degree`, `weightedDegree`, and `pushforward`
API together with Mathlib's finite-sum lemmas.
-/

public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

/-! ### Finite sums with multiplicity -/

/-- The effective divisor `Σ x ∈ s, m x • [x]` attached to a finite set of points and
natural-number multiplicities.  Points outside `s` have coefficient zero. -/
def ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) : WeilDivisor X :=
  ∑ x ∈ s, (m x : ℤ) • ofPoint x

@[simp]
lemma ofFinsetWithMultiplicity_empty (m : X → ℕ) :
    ofFinsetWithMultiplicity (∅ : Finset X) m = 0 := by
  simp [ofFinsetWithMultiplicity]

@[simp]
lemma ofFinsetWithMultiplicity_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    ofFinsetWithMultiplicity (insert x s) m =
      (m x : ℤ) • ofPoint x + ofFinsetWithMultiplicity s m := by
  simp [ofFinsetWithMultiplicity, hx]

/-- Coefficient formula for a finite point divisor with multiplicities. -/
@[simp]
lemma coeff_ofFinsetWithMultiplicity [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (ofFinsetWithMultiplicity s m) x = if x ∈ s then m x else 0 := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | insert y s hy ih =>
      rw [ofFinsetWithMultiplicity_insert hy, coeff_add]
      by_cases hxy : x = y
      · subst y
        have hsx : (ofFinsetWithMultiplicity s m) x = 0 := by
          simpa [coeff, hy] using ih
        have hpoint : (ofPoint x : WeilDivisor X) x = 1 := by
          simpa [coeff] using coeff_ofPoint_self x
        rw [show coeff ((m x : ℤ) • ofPoint x) x = (m x : ℤ) by simp [coeff, hpoint]]
        rw [show coeff (ofFinsetWithMultiplicity s m) x = 0 by simpa [coeff] using hsx]
        simp
      · have hsx : (ofFinsetWithMultiplicity s m) x = if x ∈ s then m x else 0 := by
          simpa [coeff] using ih
        have hpoint : (ofPoint y : WeilDivisor X) x = 0 := by
          simpa [coeff] using coeff_ofPoint_of_ne (x := y) (y := x) hxy
        rw [show coeff ((m y : ℤ) • ofPoint y) x = 0 by simp [coeff, hpoint]]
        rw [show coeff (ofFinsetWithMultiplicity s m) x =
          (if x ∈ s then (m x : ℤ) else 0) by simpa [coeff] using hsx]
        simp [hxy]

/-- Finite point divisors with natural multiplicities are effective. -/
@[simp]
lemma isEffective_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    IsEffective (ofFinsetWithMultiplicity s m) := by
  classical
  rw [isEffective_iff]
  intro x
  rw [coeff_ofFinsetWithMultiplicity]
  split
  · exact Int.natCast_nonneg _
  · rfl

@[simp]
lemma ofFinsetWithMultiplicity_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinsetWithMultiplicity s m)

/-- The support of a finite point divisor with multiplicities is contained in the chosen
finite set.  Points in `s` whose multiplicity is zero may drop out of the support. -/
lemma support_ofFinsetWithMultiplicity_subset (s : Finset X) (m : X → ℕ) :
    (ofFinsetWithMultiplicity s m).support ⊆ s := by
  classical
  intro x hx
  rw [mem_support_iff, coeff_ofFinsetWithMultiplicity] at hx
  by_contra hxs
  simp [hxs] at hx

lemma mem_support_ofFinsetWithMultiplicity_iff {s : Finset X} {m : X → ℕ}
    {x : X} :
    x ∈ (ofFinsetWithMultiplicity s m).support ↔ x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_ofFinsetWithMultiplicity]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of `Σ x ∈ s, m x • [x]` is the sum of the multiplicities. -/
@[simp]
lemma degree_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    degree (ofFinsetWithMultiplicity s m) = ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [ofFinsetWithMultiplicity]

/-- The weighted degree of `Σ x ∈ s, m x • [x]` is the corresponding weighted finite sum. -/
@[simp]
lemma weightedDegree_ofFinsetWithMultiplicity (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [ofFinsetWithMultiplicity, mul_comm]

/-- Pushing forward a finite point divisor applies the map to each point in the finite sum. -/
@[simp]
lemma pushforward_ofFinsetWithMultiplicity (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsetWithMultiplicity, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights, a finite point divisor has weighted degree zero exactly when every
selected point has zero multiplicity. -/
lemma weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) = 0 ↔ ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    have hzero : ofFinsetWithMultiplicity s m = 0 :=
      (isEffective_ofFinsetWithMultiplicity s m).eq_zero_of_weightedDegree_eq_zero_of_pos hw
        hdeg
    have hcoeff := congr_arg (fun D : WeilDivisor X => coeff D x) hzero
    simpa [hx] using hcoeff
  · intro hm
    rw [weightedDegree_ofFinsetWithMultiplicity]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- A finite point divisor with positive weights lies in the weighted degree-zero subgroup
exactly when all selected multiplicities vanish. -/
lemma ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ weightedDegreeZeroSubgroup w ↔ ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup,
    weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos hw]

/-! ### Finite sums with coefficient one -/

/-- The effective divisor `Σ x ∈ s, [x]` attached to a finite set of points. -/
def ofFinset (s : Finset X) : WeilDivisor X :=
  ofFinsetWithMultiplicity s fun _ => 1

@[simp]
lemma ofFinset_empty : ofFinset (∅ : Finset X) = 0 := by
  simp [ofFinset]

@[simp]
lemma ofFinset_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    ofFinset (insert x s) = ofPoint x + ofFinset s := by
  simp [ofFinset, hx]

@[simp]
lemma coeff_ofFinset [DecidableEq X] (s : Finset X) (x : X) :
    coeff (ofFinset s) x = if x ∈ s then 1 else 0 := by
  simp [ofFinset]

@[simp]
lemma isEffective_ofFinset (s : Finset X) : IsEffective (ofFinset s) := by
  classical
  simp [ofFinset]

@[simp]
lemma ofFinset_mem_effectiveSubmonoid (s : Finset X) :
    ofFinset s ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinset s)

@[simp]
lemma support_ofFinset (s : Finset X) : (ofFinset s).support = s := by
  classical
  ext x
  rw [ofFinset, mem_support_ofFinsetWithMultiplicity_iff]
  simp

@[simp]
lemma degree_ofFinset (s : Finset X) : degree (ofFinset s) = s.card := by
  classical
  simp [ofFinset]

@[simp]
lemma weightedDegree_ofFinset (w : X → ℤ) (s : Finset X) :
    weightedDegree w (ofFinset s) = ∑ x ∈ s, w x := by
  classical
  simp [ofFinset]

@[simp]
lemma pushforward_ofFinset (f : X → Y) (s : Finset X) :
    pushforward f (ofFinset s) = ∑ x ∈ s, ofPoint (f x) := by
  classical
  rw [ofFinset, pushforward_ofFinsetWithMultiplicity]
  simp

/-- For positive weights, a finite set divisor lies in the weighted degree-zero subgroup exactly
when the finite set is empty. -/
lemma ofFinset_mem_weightedDegreeZeroSubgroup_iff_of_pos
    {w : X → ℤ} (hw : ∀ x, 0 < w x) (s : Finset X) :
    ofFinset s ∈ weightedDegreeZeroSubgroup w ↔ s = ∅ := by
  classical
  rw [ofFinset, ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos hw]
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

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.Indicator
public import TauCeti.AlgebraicGeometry.WeilDivisor

/-!
# Finite sums of point divisors

This file adds constructors for the effective Weil divisors represented by finitely supported
natural-number multiplicities, together with their finite-set specializations via
`Finsupp.indicator`. These are the formal Layer A divisor objects that later receive geometric
restrictions from symmetric powers and relative effective divisors: before any scheme-level
construction exists, a finite collection of points gives the divisor `Σ nₓ[x]`.

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

/-! ### Finitely supported multiplicities -/

/-- The effective divisor with finitely supported natural-number multiplicities. -/
def ofFinsuppMultiplicity (m : X →₀ ℕ) : WeilDivisor X :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) (by simp) m

@[simp]
lemma coeff_ofFinsuppMultiplicity (m : X →₀ ℕ) (x : X) :
    coeff (ofFinsuppMultiplicity m) x = m x := by
  simp [ofFinsuppMultiplicity, coeff]

/-- Finitely supported natural multiplicities give effective divisors. -/
@[simp]
lemma isEffective_ofFinsuppMultiplicity (m : X →₀ ℕ) :
    IsEffective (ofFinsuppMultiplicity m) := by
  rw [isEffective_iff]
  intro x
  simp

/-- The divisor from finitely supported multiplicities is the corresponding sum of point
divisors over the support. -/
lemma ofFinsuppMultiplicity_eq_sum (m : X →₀ ℕ) :
    ofFinsuppMultiplicity m = ∑ x ∈ m.support, (m x : ℤ) • ofPoint x := by
  classical
  apply Finsupp.ext
  intro x
  simp only [ofFinsuppMultiplicity, Finsupp.mapRange_apply]
  by_cases hxs : x ∈ m.support
  · simp_rw [Finset.sum_apply']
    change (m x : ℤ) = ∑ y ∈ m.support, (((m y : ℤ) • ofPoint y : WeilDivisor X) x)
    rw [Finset.sum_eq_single x]
    · have hpoint : (ofPoint x : WeilDivisor X) x = 1 := by
        simpa [coeff] using coeff_ofPoint_self x
      simp [hpoint]
    · intro y hy hyx
      have hxy : x ≠ y := fun h => hyx h.symm
      have hpoint : (ofPoint y : WeilDivisor X) x = 0 := by
        simpa [coeff] using coeff_ofPoint_of_ne (x := y) (y := x) hxy
      simp [hpoint]
    · intro hx
      exact (hx hxs).elim
  · have hmx : m x = 0 := by
      by_contra hmx
      exact hxs (Finsupp.mem_support_iff.mpr hmx)
    rw [hmx]
    simp_rw [Finset.sum_apply']
    change (0 : ℤ) = ∑ y ∈ m.support, (((m y : ℤ) • ofPoint y : WeilDivisor X) x)
    exact (Finset.sum_eq_zero fun y hy => by
      have hxy : x ≠ y := fun h => hxs (h.symm ▸ hy)
      have hpoint : (ofPoint y : WeilDivisor X) x = 0 := by
        simpa [coeff] using coeff_ofPoint_of_ne (x := y) (y := x) hxy
      simp [hpoint]).symm

/-- The support of the divisor from finitely supported natural multiplicities is the support
of those multiplicities. -/
@[simp]
lemma support_ofFinsuppMultiplicity (m : X →₀ ℕ) :
    (ofFinsuppMultiplicity m).support = m.support := by
  classical
  ext x
  rw [mem_support_iff, coeff_ofFinsuppMultiplicity, Finsupp.mem_support_iff]
  constructor
  · intro h hx
    exact h (by simp [hx])
  · intro h hx
    apply h
    exact_mod_cast hx

/-- The degree of a divisor from finitely supported multiplicities is the sum over the support. -/
@[simp]
lemma degree_ofFinsuppMultiplicity (m : X →₀ ℕ) :
    degree (ofFinsuppMultiplicity m) = ∑ x ∈ m.support, (m x : ℤ) := by
  classical
  simp [ofFinsuppMultiplicity_eq_sum]

/-- The weighted degree of a divisor from finitely supported multiplicities is the weighted
sum over the support. -/
@[simp]
lemma weightedDegree_ofFinsuppMultiplicity (w : X → ℤ) (m : X →₀ ℕ) :
    weightedDegree w (ofFinsuppMultiplicity m) =
      ∑ x ∈ m.support, (m x : ℤ) * w x := by
  classical
  simp [ofFinsuppMultiplicity_eq_sum, mul_comm]

/-- Pushing forward a divisor from finitely supported multiplicities applies the map to each
point in the support sum. -/
@[simp]
lemma pushforward_ofFinsuppMultiplicity (f : X → Y) (m : X →₀ ℕ) :
    pushforward f (ofFinsuppMultiplicity m) =
      ∑ x ∈ m.support, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsuppMultiplicity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-! ### Finite-set specializations -/

/-- Coefficient formula for the `Finsupp.indicator` specialization of finitely supported
multiplicities. -/
@[simp]
lemma coeff_ofFinsuppMultiplicity_indicator [DecidableEq X] (s : Finset X) (m : X → ℕ)
    (x : X) :
    coeff (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) x =
      if x ∈ s then m x else 0 := by
  simp [Finsupp.indicator_apply]

/-- The `Finsupp.indicator` specialization agrees with the finite sum of point divisors. -/
lemma ofFinsuppMultiplicity_indicator_eq_sum (s : Finset X) (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  classical
  apply Finsupp.ext
  intro x
  simp only [ofFinsuppMultiplicity, Finsupp.mapRange_apply, Finsupp.indicator_apply]
  by_cases hxs : x ∈ s
  · rw [dif_pos hxs]
    simp_rw [Finset.sum_apply']
    change (m x : ℤ) = ∑ y ∈ s, (((m y : ℤ) • ofPoint y : WeilDivisor X) x)
    rw [Finset.sum_eq_single x]
    · have hpoint : (ofPoint x : WeilDivisor X) x = 1 := by
        simpa [coeff] using coeff_ofPoint_self x
      simp [hpoint]
    · intro y hy hyx
      have hxy : x ≠ y := fun h => hyx h.symm
      have hpoint : (ofPoint y : WeilDivisor X) x = 0 := by
        simpa [coeff] using coeff_ofPoint_of_ne (x := y) (y := x) hxy
      simp [hpoint]
    · intro hx
      exact (hx hxs).elim
  · rw [dif_neg hxs]
    simp_rw [Finset.sum_apply']
    change (0 : ℤ) = ∑ y ∈ s, (((m y : ℤ) • ofPoint y : WeilDivisor X) x)
    exact (Finset.sum_eq_zero fun y hy => by
      have hxy : x ≠ y := fun h => hxs (h.symm ▸ hy)
      have hpoint : (ofPoint y : WeilDivisor X) x = 0 := by
        simpa [coeff] using coeff_ofPoint_of_ne (x := y) (y := x) hxy
      simp [hpoint]).symm

@[simp]
lemma ofFinsuppMultiplicity_indicator_empty (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator (∅ : Finset X) fun x _ => m x) = 0 := by
  classical
  ext x
  rw [coeff_ofFinsuppMultiplicity_indicator]
  simp

@[simp]
lemma ofFinsuppMultiplicity_indicator_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator (insert x s) fun y _ => m y) =
      (m x : ℤ) • ofPoint x +
        ofFinsuppMultiplicity (Finsupp.indicator s fun y _ => m y) := by
  rw [ofFinsuppMultiplicity_indicator_eq_sum, ofFinsuppMultiplicity_indicator_eq_sum]
  simp [hx]

/-- The `Finsupp.indicator` specialization of finitely supported multiplicities is effective. -/
@[simp]
lemma isEffective_ofFinsuppMultiplicity_indicator (s : Finset X) (m : X → ℕ) :
    IsEffective (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) := by
  classical
  simp

@[simp]
lemma ofFinsuppMultiplicity_indicator_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x) ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinsuppMultiplicity_indicator s m)

/-- The support of an indicator-specialized divisor is contained in the chosen finite set.
Points in `s` whose multiplicity is zero may drop out of the support. -/
lemma support_ofFinsuppMultiplicity_indicator_subset (s : Finset X) (m : X → ℕ) :
    (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)).support ⊆ s := by
  classical
  intro x hx
  rw [mem_support_iff, coeff_ofFinsuppMultiplicity_indicator] at hx
  by_contra hxs
  simp [hxs] at hx

/-- A point is in the support of an indicator-specialized divisor exactly when it is selected
and has nonzero multiplicity. -/
lemma mem_support_ofFinsuppMultiplicity_indicator_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)).support ↔
      x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_ofFinsuppMultiplicity_indicator]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of an indicator-specialized divisor is the sum of the multiplicities. -/
@[simp]
lemma degree_ofFinsuppMultiplicity_indicator (s : Finset X) (m : X → ℕ) :
    degree (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) =
      ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [ofFinsuppMultiplicity_indicator_eq_sum]

/-- The weighted degree of an indicator-specialized divisor is the corresponding weighted
finite sum. -/
@[simp]
lemma weightedDegree_ofFinsuppMultiplicity_indicator (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [ofFinsuppMultiplicity_indicator_eq_sum, mul_comm]

/-- Pushing forward an indicator-specialized divisor applies the map to each point in the
finite sum. -/
@[simp]
lemma pushforward_ofFinsuppMultiplicity_indicator (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsuppMultiplicity_indicator_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights on the selected set, an indicator-specialized divisor has weighted
degree zero exactly when every selected point has zero multiplicity. -/
lemma weightedDegree_ofFinsuppMultiplicity_indicator_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    weightedDegree w (ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)) = 0 ↔
      ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    rw [weightedDegree_ofFinsuppMultiplicity_indicator] at hdeg
    have hterm :
        (m x : ℤ) * w x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y hy => mul_nonneg (Int.natCast_nonneg _) (le_of_lt (hw y hy)))).mp
          hdeg x hx
    rcases mul_eq_zero.mp hterm with hmx | hwx
    · exact_mod_cast hmx
    · exact False.elim ((ne_of_gt (hw x hx)) hwx)
  · intro hm
    rw [weightedDegree_ofFinsuppMultiplicity_indicator]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- An indicator-specialized divisor with positive weights on the selected set lies in the
weighted degree-zero subgroup exactly when all selected multiplicities vanish. -/
lemma ofFinsuppMultiplicity_indicator_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x) ∈
      weightedDegreeZeroSubgroup w ↔ ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup,
    weightedDegree_ofFinsuppMultiplicity_indicator_eq_zero_iff_of_pos s hw]

/-- An indicator-specialized divisor has unweighted degree zero exactly when every selected
multiplicity vanishes. -/
lemma ofFinsuppMultiplicity_indicator_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x) ∈ degreeZeroSubgroup X ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_ofFinsuppMultiplicity_indicator_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) s (fun _ _ => zero_lt_one) m

/-! ### Finite sums with coefficient one -/

/-- The effective divisor `Σ x ∈ s, [x]` attached to a finite set of points. -/
def ofFinset (s : Finset X) : WeilDivisor X :=
  ofFinsuppMultiplicity (Finsupp.indicator s fun _ _ => 1)

@[simp]
lemma ofFinset_empty : ofFinset (∅ : Finset X) = 0 := by
  simp [ofFinset]

@[simp]
lemma ofFinset_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    ofFinset (insert x s) = ofPoint x + ofFinset s := by
  simp [ofFinset, hx]

/-- Coefficients of the divisor attached to a finite set are `1` on the set and `0` off it. -/
@[simp]
lemma coeff_ofFinset [DecidableEq X] (s : Finset X) (x : X) :
    coeff (ofFinset s) x = if x ∈ s then 1 else 0 := by
  simp [ofFinset]

/-- The divisor attached to a finite set is effective. -/
@[simp]
lemma isEffective_ofFinset (s : Finset X) : IsEffective (ofFinset s) := by
  classical
  simp [ofFinset]

@[simp]
lemma ofFinset_mem_effectiveSubmonoid (s : Finset X) :
    ofFinset s ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinset s)

/-- The support of the coefficient-one divisor attached to a finite set is exactly that set. -/
@[simp]
lemma support_ofFinset (s : Finset X) : (ofFinset s).support = s := by
  classical
  ext x
  rw [ofFinset, mem_support_ofFinsuppMultiplicity_indicator_iff]
  simp

/-- The degree of the coefficient-one divisor attached to a finite set is its cardinality. -/
@[simp]
lemma degree_ofFinset (s : Finset X) : degree (ofFinset s) = s.card := by
  classical
  rw [ofFinset, degree_ofFinsuppMultiplicity_indicator]
  simp

/-- The weighted degree of the divisor attached to a finite set is the sum of weights on it. -/
@[simp]
lemma weightedDegree_ofFinset (w : X → ℤ) (s : Finset X) :
    weightedDegree w (ofFinset s) = ∑ x ∈ s, w x := by
  classical
  rw [ofFinset, weightedDegree_ofFinsuppMultiplicity_indicator]
  simp

/-- Pushing forward the divisor attached to a finite set applies the map to each point. -/
@[simp]
lemma pushforward_ofFinset (f : X → Y) (s : Finset X) :
    pushforward f (ofFinset s) = ∑ x ∈ s, ofPoint (f x) := by
  classical
  rw [ofFinset, pushforward_ofFinsuppMultiplicity_indicator]
  simp

/-- For positive weights, a finite set divisor lies in the weighted degree-zero subgroup exactly
when the finite set is empty. -/
lemma ofFinset_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    ofFinset s ∈ weightedDegreeZeroSubgroup w ↔ s = ∅ := by
  classical
  rw [ofFinset, ofFinsuppMultiplicity_indicator_mem_weightedDegreeZeroSubgroup_iff_of_pos s hw]
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

/-- A coefficient-one finite set divisor has unweighted degree zero exactly when the set is
empty. -/
lemma ofFinset_mem_degreeZeroSubgroup_iff (s : Finset X) :
    ofFinset s ∈ degreeZeroSubgroup X ↔ s = ∅ := by
  classical
  rw [ofFinset, ofFinsuppMultiplicity_indicator_mem_degreeZeroSubgroup_iff]
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

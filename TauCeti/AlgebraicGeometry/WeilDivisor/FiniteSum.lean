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
natural-number multiplicities and by finite sets with multiplicities. These are the formal
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

private lemma coeff_sum_zsmul_ofPoint_of_mem {s : Finset X} {a : X → ℤ} {x : X}
    (hxs : x ∈ s) :
    coeff (∑ y ∈ s, a y • ofPoint y : WeilDivisor X) x = a x := by
  classical
  rw [coeff]
  rw [Finset.sum_apply', Finset.sum_eq_single x]
  -- After unfolding `coeff`, the goal is pointwise evaluation of a `Finsupp` `ℤ`-smul.
  · change a x * (ofPoint x : WeilDivisor X) x = a x
    rw [show (ofPoint x : WeilDivisor X) x = coeff (ofPoint x) x from rfl,
      coeff_ofPoint_self, mul_one]
  · intro y hy hyx
    have hxy : x ≠ y := fun h => hyx h.symm
    change a y * (ofPoint y : WeilDivisor X) x = 0
    rw [show (ofPoint y : WeilDivisor X) x = coeff (ofPoint y) x from rfl,
      coeff_ofPoint_of_ne hxy, mul_zero]
  · intro hx
    exact (hx hxs).elim

private lemma coeff_sum_zsmul_ofPoint_of_notMem {s : Finset X} {a : X → ℤ} {x : X}
    (hxs : x ∉ s) :
    coeff (∑ y ∈ s, a y • ofPoint y : WeilDivisor X) x = 0 := by
  classical
  rw [coeff, Finset.sum_apply']
  exact Finset.sum_eq_zero fun y hy => by
    have hxy : x ≠ y := fun h => hxs (h.symm ▸ hy)
    -- After unfolding `coeff`, the goal is pointwise evaluation of a `Finsupp` `ℤ`-smul.
    change a y * (ofPoint y : WeilDivisor X) x = 0
    rw [show (ofPoint y : WeilDivisor X) x = coeff (ofPoint y) x from rfl,
      coeff_ofPoint_of_ne hxy, mul_zero]

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
  ext x
  by_cases hxs : x ∈ m.support
  · rw [coeff_ofFinsuppMultiplicity, coeff_sum_zsmul_ofPoint_of_mem hxs]
  · have hmx : m x = 0 := by
      simpa [Finsupp.mem_support_iff] using hxs
    rw [coeff_ofFinsuppMultiplicity, coeff_sum_zsmul_ofPoint_of_notMem hxs, hmx]
    simp

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

/-- With strictly positive weights on the support, an effective divisor has weighted degree
zero iff it is zero. -/
lemma IsEffective.weightedDegree_eq_zero_iff_of_pos_on_support {w : X → ℤ}
    {D : WeilDivisor X} (hD : IsEffective D) (hw : ∀ x ∈ D.support, 0 < w x) :
    weightedDegree w D = 0 ↔ D = 0 := by
  constructor
  · intro hdeg
    by_contra hD0
    obtain ⟨x, hxpos⟩ := hD.exists_pos_coeff_of_ne_zero hD0
    have hxs : x ∈ D.support := Finsupp.mem_support_iff.mpr (ne_of_gt hxpos)
    have hsum_pos : 0 < D.sum fun y n => n * w y := by
      exact Finsupp.sum_pos'
        (fun y hy => mul_nonneg ((isEffective_iff D).mp hD y) (le_of_lt (hw y hy)))
        ⟨x, hxs, mul_pos hxpos (hw x hxs)⟩
    rw [← weightedDegree_apply] at hsum_pos
    exact (ne_of_gt hsum_pos) hdeg
  · intro h
    simp [h]

/-- With strictly positive weights on the support, an effective divisor of weighted degree zero
is zero. -/
lemma IsEffective.eq_zero_of_weightedDegree_eq_zero_of_pos_on_support {w : X → ℤ}
    {D : WeilDivisor X} (hD : IsEffective D) (hw : ∀ x ∈ D.support, 0 < w x)
    (hdeg : weightedDegree w D = 0) : D = 0 :=
  (hD.weightedDegree_eq_zero_iff_of_pos_on_support hw).mp hdeg

/-! ### Finite-set multiplicities -/

/-- The effective divisor with natural-number multiplicities on a chosen finite set. Points
outside the set have multiplicity zero. -/
def ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) : WeilDivisor X :=
  ofFinsuppMultiplicity (Finsupp.indicator s fun x _ => m x)

/-- Coefficient formula for a finite-set divisor with multiplicities. -/
@[simp]
lemma coeff_ofFinsetWithMultiplicity [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (ofFinsetWithMultiplicity s m) x = if x ∈ s then m x else 0 := by
  simp [ofFinsetWithMultiplicity, Finsupp.indicator_apply]

/-- The finite-set multiplicity divisor agrees with the corresponding finite sum of point
divisors. -/
lemma ofFinsetWithMultiplicity_eq_sum (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m = ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  classical
  ext x
  by_cases hxs : x ∈ s
  · rw [coeff_ofFinsetWithMultiplicity, coeff_sum_zsmul_ofPoint_of_mem hxs, if_pos hxs]
  · rw [coeff_ofFinsetWithMultiplicity, coeff_sum_zsmul_ofPoint_of_notMem hxs, if_neg hxs]
    simp

@[simp]
lemma ofFinsetWithMultiplicity_empty (m : X → ℕ) :
    ofFinsetWithMultiplicity (∅ : Finset X) m = 0 := by
  classical
  ext x
  simp

@[simp]
lemma ofFinsetWithMultiplicity_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    ofFinsetWithMultiplicity (insert x s) m =
      (m x : ℤ) • ofPoint x + ofFinsetWithMultiplicity s m := by
  rw [ofFinsetWithMultiplicity_eq_sum, ofFinsetWithMultiplicity_eq_sum]
  simp [hx]

/-- Finite-set divisors with natural-number multiplicities are effective. -/
@[simp]
lemma isEffective_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    IsEffective (ofFinsetWithMultiplicity s m) := by
  classical
  simp [ofFinsetWithMultiplicity]

@[simp]
lemma ofFinsetWithMultiplicity_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinsetWithMultiplicity s m)

/-- The support of a finite-set divisor with multiplicities is contained in the chosen finite
set. Points in the set whose multiplicity is zero may drop out of the support. -/
lemma support_ofFinsetWithMultiplicity_subset (s : Finset X) (m : X → ℕ) :
    (ofFinsetWithMultiplicity s m).support ⊆ s := by
  classical
  intro x hx
  rw [mem_support_iff, coeff_ofFinsetWithMultiplicity] at hx
  by_contra hxs
  simp [hxs] at hx

/-- A point is in the support of a finite-set divisor with multiplicities exactly when it is
selected and has nonzero multiplicity. -/
@[simp]
lemma mem_support_ofFinsetWithMultiplicity_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (ofFinsetWithMultiplicity s m).support ↔ x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_ofFinsetWithMultiplicity]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of a finite-set divisor with multiplicities is the sum of the multiplicities. -/
@[simp]
lemma degree_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    degree (ofFinsetWithMultiplicity s m) = ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [ofFinsetWithMultiplicity_eq_sum]

/-- The weighted degree of a finite-set divisor with multiplicities is the corresponding
weighted finite sum. -/
@[simp]
lemma weightedDegree_ofFinsetWithMultiplicity (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [ofFinsetWithMultiplicity_eq_sum, mul_comm]

/-- Pushing forward a finite-set divisor with multiplicities applies the map to each point in
the finite sum. -/
@[simp]
lemma pushforward_ofFinsetWithMultiplicity (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [ofFinsetWithMultiplicity_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights on the selected set, a finite-set divisor with multiplicities has
weighted degree zero exactly when every selected multiplicity vanishes. -/
lemma weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) = 0 ↔ ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    have hzero : ofFinsetWithMultiplicity s m = 0 :=
      (isEffective_ofFinsetWithMultiplicity s m).eq_zero_of_weightedDegree_eq_zero_of_pos_on_support
        (fun y hy => hw y (support_ofFinsetWithMultiplicity_subset s m hy)) hdeg
    have hcoeff := congrArg (fun D : WeilDivisor X => coeff D x) hzero
    simpa [coeff_ofFinsetWithMultiplicity, hx] using hcoeff
  · intro hm
    rw [weightedDegree_ofFinsetWithMultiplicity]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- A finite-set divisor with positive weights on the selected set lies in the weighted
degree-zero subgroup exactly when all selected multiplicities vanish. -/
lemma ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ weightedDegreeZeroSubgroup w ↔ ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup,
    weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos s hw]

/-- A finite-set divisor with multiplicities has unweighted degree zero exactly when every
selected multiplicity vanishes. -/
lemma ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ degreeZeroSubgroup X ↔ ∀ x ∈ s, m x = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) s (fun _ _ => zero_lt_one) m

/-! ### Finite sums with coefficient one -/

/-- The effective divisor `Σ x ∈ s, [x]` attached to a finite set of points. -/
def ofFinset (s : Finset X) : WeilDivisor X :=
  ofFinsetWithMultiplicity s fun _ => 1

/-- The coefficient-one finite-set divisor is the corresponding finite sum of point divisors. -/
lemma ofFinset_eq_sum (s : Finset X) :
    ofFinset s = ∑ x ∈ s, ofPoint x := by
  rw [ofFinset, ofFinsetWithMultiplicity_eq_sum]
  simp

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
  rw [ofFinset, mem_support_ofFinsetWithMultiplicity_iff]
  simp

/-- The degree of the coefficient-one divisor attached to a finite set is its cardinality. -/
@[simp]
lemma degree_ofFinset (s : Finset X) : degree (ofFinset s) = s.card := by
  classical
  rw [ofFinset, degree_ofFinsetWithMultiplicity]
  simp

/-- The weighted degree of the divisor attached to a finite set is the sum of weights on it. -/
@[simp]
lemma weightedDegree_ofFinset (w : X → ℤ) (s : Finset X) :
    weightedDegree w (ofFinset s) = ∑ x ∈ s, w x := by
  classical
  rw [ofFinset, weightedDegree_ofFinsetWithMultiplicity]
  simp

/-- Pushing forward the divisor attached to a finite set applies the map to each point. -/
@[simp]
lemma pushforward_ofFinset (f : X → Y) (s : Finset X) :
    pushforward f (ofFinset s) = ∑ x ∈ s, ofPoint (f x) := by
  classical
  rw [ofFinset, pushforward_ofFinsetWithMultiplicity]
  simp

/-- For positive weights, a finite set divisor lies in the weighted degree-zero subgroup exactly
when the finite set is empty. -/
lemma ofFinset_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    ofFinset s ∈ weightedDegreeZeroSubgroup w ↔ s = ∅ := by
  classical
  rw [ofFinset, ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos s hw]
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
  rw [ofFinset, ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff]
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

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

/-! ### Finite-set multiplicities via `Finsupp.indicator` -/

/-- The effective divisor whose coefficients on `s` are the natural-number multiplicities `m`
and whose coefficients off `s` are zero. -/
def ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) : WeilDivisor X :=
  Finsupp.indicator s (fun x _ => (m x : ℤ))

/-- Coefficient formula for `Finsupp.indicator` with natural-number multiplicities. -/
@[simp]
private lemma coeff_indicator_nat [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) x =
      if x ∈ s then m x else 0 := by
  simp [coeff, Finsupp.indicator_apply]

/-- The `Finsupp.indicator` divisor with multiplicities agrees with the corresponding finite sum
of point divisors. -/
private lemma indicator_nat_eq_sum (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  classical
  ext x
  by_cases hxs : x ∈ s
  · rw [coeff_indicator_nat, coeff_sum_zsmul_ofPoint_of_mem hxs, if_pos hxs]
  · rw [coeff_indicator_nat, coeff_sum_zsmul_ofPoint_of_notMem hxs, if_neg hxs]
    simp

@[simp]
private lemma indicator_nat_empty (m : X → ℕ) :
    (Finsupp.indicator (∅ : Finset X) (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 := by
  classical
  ext x
  simp

@[simp]
private lemma indicator_nat_insert [DecidableEq X] {s : Finset X} {x : X}
    (hx : x ∉ s) (m : X → ℕ) :
    (Finsupp.indicator (insert x s) (fun y _ => (m y : ℤ)) : WeilDivisor X) =
      (m x : ℤ) • ofPoint x + Finsupp.indicator s (fun y _ => (m y : ℤ)) := by
  rw [indicator_nat_eq_sum, indicator_nat_eq_sum]
  simp [hx]

/-- `Finsupp.indicator` with natural-number multiplicities is an effective divisor. -/
@[simp]
private lemma isEffective_indicator_nat (s : Finset X) (m : X → ℕ) :
    IsEffective (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) := by
  classical
  rw [isEffective_iff]
  intro x
  simp only [coeff_indicator_nat]
  split_ifs <;> simp

@[simp]
private lemma indicator_nat_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_indicator_nat s m)

/-- The support of `Finsupp.indicator` with multiplicities is contained in the chosen finite set.
Points in the set whose multiplicity is zero may drop out of the support. -/
private lemma support_indicator_nat_subset (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X).support ⊆ s :=
  Finsupp.support_indicator_subset s (fun x _ => (m x : ℤ))

/-- A point is in the support of `Finsupp.indicator` with multiplicities exactly when it is
selected and has nonzero multiplicity. -/
@[simp]
private lemma mem_support_indicator_nat_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X).support ↔
      x ∈ s ∧ m x ≠ 0 := by
  classical
  rw [mem_support_iff, coeff_indicator_nat]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The degree of `Finsupp.indicator` with multiplicities is the sum of the multiplicities. -/
@[simp]
private lemma degree_indicator_nat (s : Finset X) (m : X → ℕ) :
    degree (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) := by
  classical
  simp [indicator_nat_eq_sum]

/-- The weighted degree of `Finsupp.indicator` with multiplicities is the corresponding weighted
finite sum. -/
@[simp]
private lemma weightedDegree_indicator_nat (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  classical
  simp [indicator_nat_eq_sum, mul_comm]

/-- Pushing forward `Finsupp.indicator` with multiplicities applies the map to each point in the
finite sum. -/
@[simp]
private lemma pushforward_indicator_nat (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  classical
  rw [indicator_nat_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [map_zsmul, pushforward_ofPoint]

/-- With positive weights on the selected set, an indicator divisor with multiplicities has
weighted degree zero exactly when every selected multiplicity vanishes. -/
private lemma weightedDegree_indicator_nat_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    weightedDegree w (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 ↔
      ∀ x ∈ s, m x = 0 := by
  classical
  constructor
  · intro hdeg x hx
    have hzero :
        (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) = 0 :=
      (isEffective_indicator_nat s m).eq_zero_of_weightedDegree_eq_zero_of_pos_on_support
        (fun y hy => hw y (support_indicator_nat_subset s m hy)) hdeg
    have hcoeff := congrArg (fun D : WeilDivisor X => coeff D x) hzero
    simpa [coeff_indicator_nat, hx] using hcoeff
  · intro hm
    rw [weightedDegree_indicator_nat]
    exact Finset.sum_eq_zero fun x hx => by simp [hm x hx]

/-- An indicator divisor with positive weights on the selected set lies in the weighted
degree-zero subgroup exactly when all selected multiplicities vanish. -/
private lemma indicator_nat_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈
        weightedDegreeZeroSubgroup w ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_weightedDegreeZeroSubgroup, weightedDegree_indicator_nat_eq_zero_iff_of_pos s hw]

/-- An indicator divisor with multiplicities has unweighted degree zero exactly when every
selected multiplicity vanishes. -/
private lemma indicator_nat_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) ∈ degreeZeroSubgroup X ↔
      ∀ x ∈ s, m x = 0 := by
  rw [mem_degreeZeroSubgroup, ← weightedDegree_one_eq_degree]
  exact weightedDegree_indicator_nat_eq_zero_iff_of_pos
    (w := fun _ : X => (1 : ℤ)) s (fun _ _ => zero_lt_one) m

/-! ### Named finite-set multiplicity divisors -/

private lemma ofFinsetWithMultiplicity_eq_indicator (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m =
      (Finsupp.indicator s (fun x _ => (m x : ℤ)) : WeilDivisor X) :=
  rfl

/-- Coefficients of `ofFinsetWithMultiplicity s m` are `m x` on `s` and zero off `s`. -/
@[simp]
lemma coeff_ofFinsetWithMultiplicity [DecidableEq X] (s : Finset X) (m : X → ℕ) (x : X) :
    coeff (ofFinsetWithMultiplicity s m) x = if x ∈ s then m x else 0 := by
  simp [ofFinsetWithMultiplicity]

/-- `ofFinsetWithMultiplicity s m` is the finite sum of point divisors with coefficients `m`. -/
lemma ofFinsetWithMultiplicity_eq_sum (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m = ∑ x ∈ s, (m x : ℤ) • ofPoint x := by
  simpa [ofFinsetWithMultiplicity] using indicator_nat_eq_sum (s := s) (m := m)

@[simp]
lemma ofFinsetWithMultiplicity_empty (m : X → ℕ) :
    ofFinsetWithMultiplicity (∅ : Finset X) m = 0 := by
  simp [ofFinsetWithMultiplicity]

@[simp]
lemma ofFinsetWithMultiplicity_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s)
    (m : X → ℕ) :
    ofFinsetWithMultiplicity (insert x s) m =
      (m x : ℤ) • ofPoint x + ofFinsetWithMultiplicity s m := by
  simpa [ofFinsetWithMultiplicity] using indicator_nat_insert (s := s) (x := x) hx m

/-- `ofFinsetWithMultiplicity s m` is effective. -/
@[simp]
lemma isEffective_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    IsEffective (ofFinsetWithMultiplicity s m) := by
  simp [ofFinsetWithMultiplicity]

@[simp]
lemma ofFinsetWithMultiplicity_mem_effectiveSubmonoid (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinsetWithMultiplicity s m)

/-- The support of `ofFinsetWithMultiplicity s m` is contained in `s`. -/
lemma support_ofFinsetWithMultiplicity_subset (s : Finset X) (m : X → ℕ) :
    (ofFinsetWithMultiplicity s m).support ⊆ s := by
  simpa [ofFinsetWithMultiplicity] using support_indicator_nat_subset (s := s) (m := m)

/-- A point is in the support of `ofFinsetWithMultiplicity s m` exactly when it lies in `s`
and has nonzero multiplicity. -/
@[simp]
lemma mem_support_ofFinsetWithMultiplicity_iff {s : Finset X} {m : X → ℕ} {x : X} :
    x ∈ (ofFinsetWithMultiplicity s m).support ↔ x ∈ s ∧ m x ≠ 0 := by
  simpa [ofFinsetWithMultiplicity] using
    mem_support_indicator_nat_iff (s := s) (m := m) (x := x)

/-- The degree of `ofFinsetWithMultiplicity s m` is the sum of the selected multiplicities. -/
@[simp]
lemma degree_ofFinsetWithMultiplicity (s : Finset X) (m : X → ℕ) :
    degree (ofFinsetWithMultiplicity s m) = ∑ x ∈ s, (m x : ℤ) := by
  simp [ofFinsetWithMultiplicity]

/-- The weighted degree of `ofFinsetWithMultiplicity s m` is the selected weighted sum. -/
@[simp]
lemma weightedDegree_ofFinsetWithMultiplicity (w : X → ℤ) (s : Finset X) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) * w x := by
  simp [ofFinsetWithMultiplicity]

/-- Pushing forward `ofFinsetWithMultiplicity s m` applies the map to each selected point. -/
@[simp]
lemma pushforward_ofFinsetWithMultiplicity (f : X → Y) (s : Finset X) (m : X → ℕ) :
    pushforward f (ofFinsetWithMultiplicity s m) =
      ∑ x ∈ s, (m x : ℤ) • ofPoint (f x) := by
  simpa [ofFinsetWithMultiplicity] using pushforward_indicator_nat (f := f) (s := s) (m := m)

/-- With positive weights on `s`, `ofFinsetWithMultiplicity s m` has weighted degree zero
exactly when every selected multiplicity vanishes. -/
lemma weightedDegree_ofFinsetWithMultiplicity_eq_zero_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    weightedDegree w (ofFinsetWithMultiplicity s m) = 0 ↔ ∀ x ∈ s, m x = 0 := by
  simpa [ofFinsetWithMultiplicity] using
    weightedDegree_indicator_nat_eq_zero_iff_of_pos (s := s) (w := w) hw m

/-- With positive weights on `s`, `ofFinsetWithMultiplicity s m` lies in the weighted
degree-zero subgroup exactly when every selected multiplicity vanishes. -/
lemma ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ weightedDegreeZeroSubgroup w ↔ ∀ x ∈ s, m x = 0 := by
  simpa [ofFinsetWithMultiplicity] using
    indicator_nat_mem_weightedDegreeZeroSubgroup_iff_of_pos (s := s) (w := w) hw m

/-- `ofFinsetWithMultiplicity s m` has unweighted degree zero exactly when every selected
multiplicity vanishes. -/
lemma ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff (s : Finset X) (m : X → ℕ) :
    ofFinsetWithMultiplicity s m ∈ degreeZeroSubgroup X ↔ ∀ x ∈ s, m x = 0 := by
  simpa [ofFinsetWithMultiplicity] using
    indicator_nat_mem_degreeZeroSubgroup_iff (s := s) (m := m)

/-! ### Finite sums with coefficient one via `Finsupp.indicator` -/

/-- The effective divisor that puts coefficient one on every point of `s` and zero elsewhere. -/
def ofFinset (s : Finset X) : WeilDivisor X :=
  ofFinsetWithMultiplicity s (fun _ => 1)

/-- The coefficient-one `Finsupp.indicator` divisor is the corresponding finite sum of point
divisors. -/
private lemma indicator_one_eq_sum (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) = ∑ x ∈ s, ofPoint x := by
  simpa using indicator_nat_eq_sum (s := s) (m := fun _ : X => 1)

@[simp]
private lemma indicator_one_empty :
    (Finsupp.indicator (∅ : Finset X) (fun _ _ => (1 : ℤ)) : WeilDivisor X) = 0 := by
  simpa using indicator_nat_empty (X := X) (fun _ : X => 1)

@[simp]
private lemma indicator_one_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    (Finsupp.indicator (insert x s) (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ofPoint x + Finsupp.indicator s (fun _ _ => (1 : ℤ)) := by
  simpa using indicator_nat_insert (s := s) (x := x) hx (fun _ : X => 1)

/-- Coefficients of the coefficient-one indicator divisor are `1` on the set and `0` off it. -/
@[simp]
private lemma coeff_indicator_one [DecidableEq X] (s : Finset X) (x : X) :
    coeff (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) x =
      if x ∈ s then 1 else 0 := by
  simp [coeff, Finsupp.indicator_apply]

/-- The coefficient-one indicator divisor is effective. -/
@[simp]
private lemma isEffective_indicator_one (s : Finset X) :
    IsEffective (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) := by
  classical
  simpa using isEffective_indicator_nat (X := X) s (fun _ => 1)

@[simp]
private lemma indicator_one_mem_effectiveSubmonoid (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_indicator_one s)

/-- The support of the coefficient-one indicator divisor is exactly the chosen finite set. -/
@[simp]
private lemma support_indicator_one (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X).support = s := by
  classical
  ext x
  simp

/-- The degree of the coefficient-one indicator divisor is the finite set's cardinality. -/
@[simp]
private lemma degree_indicator_one (s : Finset X) :
    degree (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) = s.card := by
  classical
  simpa using degree_indicator_nat (s := s) (m := fun _ : X => 1)

/-- The weighted degree of the coefficient-one indicator divisor is the sum of weights on it. -/
@[simp]
private lemma weightedDegree_indicator_one (w : X → ℤ) (s : Finset X) :
    weightedDegree w (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, w x := by
  classical
  simpa using weightedDegree_indicator_nat (w := w) (s := s) (m := fun _ : X => 1)

/-- Pushing forward the coefficient-one indicator divisor applies the map to each point. -/
@[simp]
private lemma pushforward_indicator_one (f : X → Y) (s : Finset X) :
    pushforward f (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) =
      ∑ x ∈ s, ofPoint (f x) := by
  classical
  simpa using pushforward_indicator_nat (f := f) (s := s) (m := fun _ : X => 1)

/-- For positive weights, a coefficient-one indicator divisor lies in the weighted degree-zero
subgroup exactly when the finite set is empty. -/
private lemma indicator_one_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈
        weightedDegreeZeroSubgroup w ↔
      s = ∅ := by
  classical
  rw [show ((Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈
      weightedDegreeZeroSubgroup w ↔ ∀ x ∈ s, (fun _ : X => 1) x = 0) from
    indicator_nat_mem_weightedDegreeZeroSubgroup_iff_of_pos s hw (fun _ : X => 1)]
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

/-- A coefficient-one indicator divisor has unweighted degree zero exactly when the set is empty. -/
private lemma indicator_one_mem_degreeZeroSubgroup_iff (s : Finset X) :
    (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈ degreeZeroSubgroup X ↔
      s = ∅ := by
  classical
  rw [show ((Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) ∈
      degreeZeroSubgroup X ↔ ∀ x ∈ s, (fun _ : X => 1) x = 0) from
    indicator_nat_mem_degreeZeroSubgroup_iff (s := s) (m := fun _ : X => 1)]
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

/-! ### Named finite-set divisors -/

private lemma ofFinset_eq_indicator (s : Finset X) :
    ofFinset s = (Finsupp.indicator s (fun _ _ => (1 : ℤ)) : WeilDivisor X) :=
  rfl

/-- `ofFinset s` is the finite sum of the point divisors at the points of `s`. -/
lemma ofFinset_eq_sum (s : Finset X) :
    ofFinset s = ∑ x ∈ s, ofPoint x := by
  simpa [ofFinset] using
    ofFinsetWithMultiplicity_eq_sum (s := s) (m := fun _ : X => 1)

@[simp]
lemma ofFinset_empty : ofFinset (∅ : Finset X) = 0 := by
  simp [ofFinset]

@[simp]
lemma ofFinset_insert [DecidableEq X] {s : Finset X} {x : X} (hx : x ∉ s) :
    ofFinset (insert x s) = ofPoint x + ofFinset s := by
  simpa [ofFinset] using
    ofFinsetWithMultiplicity_insert (s := s) (x := x) hx (fun _ : X => 1)

/-- Coefficients of `ofFinset s` are `1` on `s` and `0` off `s`. -/
@[simp]
lemma coeff_ofFinset [DecidableEq X] (s : Finset X) (x : X) :
    coeff (ofFinset s) x = if x ∈ s then 1 else 0 := by
  simp [ofFinset]

/-- `ofFinset s` is effective. -/
@[simp]
lemma isEffective_ofFinset (s : Finset X) :
    IsEffective (ofFinset s) := by
  simp [ofFinset]

@[simp]
lemma ofFinset_mem_effectiveSubmonoid (s : Finset X) :
    ofFinset s ∈ effectiveSubmonoid X :=
  (mem_effectiveSubmonoid _).mpr (isEffective_ofFinset s)

/-- The support of `ofFinset s` is exactly `s`. -/
@[simp]
lemma support_ofFinset (s : Finset X) :
    (ofFinset s).support = s := by
  rw [ofFinset]
  ext x
  rw [mem_support_ofFinsetWithMultiplicity_iff]
  simp

/-- The degree of `ofFinset s` is the cardinality of `s`. -/
@[simp]
lemma degree_ofFinset (s : Finset X) :
    degree (ofFinset s) = s.card := by
  simp [ofFinset]

/-- The weighted degree of `ofFinset s` is the sum of the weights on `s`. -/
@[simp]
lemma weightedDegree_ofFinset (w : X → ℤ) (s : Finset X) :
    weightedDegree w (ofFinset s) = ∑ x ∈ s, w x := by
  simp [ofFinset]

/-- Pushing forward `ofFinset s` applies the map to each selected point. -/
@[simp]
lemma pushforward_ofFinset (f : X → Y) (s : Finset X) :
    pushforward f (ofFinset s) = ∑ x ∈ s, ofPoint (f x) := by
  simpa [ofFinset] using
    pushforward_ofFinsetWithMultiplicity (f := f) (s := s) (m := fun _ : X => 1)

/-- With positive weights on `s`, `ofFinset s` lies in the weighted degree-zero subgroup exactly
when `s` is empty. -/
lemma ofFinset_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s : Finset X) {w : X → ℤ} (hw : ∀ x ∈ s, 0 < w x) :
    ofFinset s ∈ weightedDegreeZeroSubgroup w ↔ s = ∅ := by
  rw [ofFinset]
  rw [ofFinsetWithMultiplicity_mem_weightedDegreeZeroSubgroup_iff_of_pos
    (s := s) (w := w) hw (fun _ : X => 1)]
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

/-- `ofFinset s` has unweighted degree zero exactly when `s` is empty. -/
lemma ofFinset_mem_degreeZeroSubgroup_iff (s : Finset X) :
    ofFinset s ∈ degreeZeroSubgroup X ↔ s = ∅ := by
  rw [ofFinset]
  rw [ofFinsetWithMultiplicity_mem_degreeZeroSubgroup_iff (s := s) (m := fun _ : X => 1)]
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

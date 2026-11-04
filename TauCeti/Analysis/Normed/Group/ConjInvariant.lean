/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import TauCeti.Data.List.Rotate

/-!
# Conjugation-invariant group seminorms and norms

The algebraic conjugation identities hold for group seminorms. A group norm is conjugation
invariant exactly when its associated left-invariant metric is also right invariant.
Such seminorms give orientation-independent seminorms of products around loops:
cyclically rotating the factors, or reversing them and inverting each factor, preserves the norm.
These identities are useful for holonomy with noncommutative coefficients.

The metric is Mathlib's `GroupNorm.toNormedGroup`; no metric instance is installed globally.
Conversely, `GroupNorm.ofLeftInvariantMetric` uses `NormedGroup.ofMulDist'` and `normGroupNorm`
to recover a group norm from a left-invariant metric.
-/

public section

namespace GroupSeminorm

variable {G : Type*} [Group G]

/-- Reversing a word and inverting each letter preserves its seminorm, even without conjugation
invariance. Reversing the word alone need not preserve the seminorm. -/
@[simp] theorem map_prod_inv_reverse (ℓ : GroupSeminorm G) (l : List G) :
    ℓ (l.map (fun g => g⁻¹)).reverse.prod = ℓ l.prod := by
  rw [← List.prod_inv_reverse, map_inv_eq_map]

/-- A group seminorm is conjugation invariant if conjugating an element preserves its seminorm. -/
def IsConjInvariant (ℓ : GroupSeminorm G) : Prop :=
  ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g

/-- A seminorm is conjugation invariant exactly when it preserves every conjugate. -/
theorem isConjInvariant_iff (ℓ : GroupSeminorm G) :
    ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g :=
  Iff.rfl

/-- Conjugation invariance is equivalent to invariance under exchanging two factors. -/
theorem isConjInvariant_iff_mul_comm (ℓ : GroupSeminorm G) :
    ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (g * h) = ℓ (h * g) := by
  constructor
  · intro hℓ g h
    simpa [mul_assoc] using hℓ (h * g) g
  · intro hℓ g h
    simpa [mul_assoc] using hℓ h (g * h⁻¹)

namespace IsConjInvariant

variable {ℓ : GroupSeminorm G} (hℓ : ℓ.IsConjInvariant)

include hℓ

/-- A cyclic exchange of two blocks of factors preserves a conjugation-invariant seminorm. -/
theorem map_mul_comm (g h : G) : ℓ (g * h) = ℓ (h * g) :=
  (isConjInvariant_iff_mul_comm ℓ).mp hℓ g h

/-- Conjugating an element preserves its seminorm. -/
@[simp] theorem map_conj (g h : G) : ℓ (h * g * h⁻¹) = ℓ g :=
  hℓ g h

/-- Conjugation by the inverse of an element also preserves the seminorm. -/
@[simp] theorem map_inv_mul_mul (g h : G) : ℓ (h⁻¹ * g * h) = ℓ g := by
  simpa using hℓ g h⁻¹

/-- The seminorm of a list product is invariant under any cyclic rotation. -/
theorem map_prod_rotate (l : List G) (n : ℕ) : ℓ (l.rotate n).prod = ℓ l.prod := by
  exact List.IsRotated.apply_prod_eq hℓ.map_mul_comm (List.IsRotated.forall l n)

end IsConjInvariant

/-- Every group seminorm on a commutative group is conjugation invariant. -/
theorem isConjInvariant_of_commGroup {A : Type*} [CommGroup A] (ℓ : GroupSeminorm A) :
    ℓ.IsConjInvariant := by
  intro g h
  simp [mul_comm h g, mul_assoc]

end GroupSeminorm

namespace GroupNorm

variable {G : Type*} [Group G]

/-- The associated metric is right invariant exactly when the norm is conjugation invariant.
Left invariance is already supplied by `GroupNorm.toNormedGroup`. -/
theorem isConjInvariant_iff_dist_mul_right (ℓ : GroupNorm G) :
    ℓ.toGroupSeminorm.IsConjInvariant ↔
      letI := ℓ.toNormedGroup
      ∀ g h k : G, dist (g * k) (h * k) = dist g h := by
  let := ℓ.toNormedGroup
  simp +zetaDelta only [dist_eq_norm_inv_mul, norm]
  constructor
  · intro hℓ g h k
    simpa [mul_assoc] using hℓ.map_inv_mul_mul (g⁻¹ * h) k
  · intro hdist g h
    simpa [mul_assoc] using hdist 1 g h⁻¹

section Metric

variable [MetricSpace G]

/-- A left-invariant metric gives the group norm `g ↦ dist 1 g`.
This packages Mathlib's `NormedGroup.ofMulDist'` and `normGroupNorm`. -/
def ofLeftInvariantMetric (hleft : ∀ g h k : G, dist (k * g) (k * h) = dist g h) :
    GroupNorm G := by
  letI : Norm G := ⟨fun g => dist 1 g⟩
  letI := NormedGroup.ofMulDist' (fun _ => rfl) (fun g h k => (hleft g h k).le)
  exact normGroupNorm G

@[simp] theorem ofLeftInvariantMetric_apply
    (hleft : ∀ g h k : G, dist (k * g) (k * h) = dist g h) (g : G) :
    ofLeftInvariantMetric hleft g = dist 1 g := by
  rfl

/-- The metric reconstructed from a left-invariant metric agrees with the original distance. -/
theorem ofLeftInvariantMetric_dist
    (hleft : ∀ g h k : G, dist (k * g) (k * h) = dist g h) (g h : G) :
    ofLeftInvariantMetric hleft (g⁻¹ * h) = dist g h := by
  simpa using hleft g h g⁻¹

/-- For a bi-invariant metric, the recovered group norm is conjugation invariant. -/
theorem isConjInvariant_ofLeftInvariantMetric
    (hleft : ∀ g h k : G, dist (k * g) (k * h) = dist g h)
    (hright : ∀ g h k : G, dist (g * k) (h * k) = dist g h) :
    (ofLeftInvariantMetric hleft).toGroupSeminorm.IsConjInvariant := by
  intro g h
  simp only [toGroupSeminorm_eq_coe, ofLeftInvariantMetric_apply]
  calc
    dist 1 (h * g * h⁻¹) = dist h (h * g) := by
      simpa using hright h (h * g) h⁻¹
    _ = dist 1 g := by simpa using hleft 1 g h

end Metric

/-- Recovering a norm from its associated metric returns the original norm. -/
@[simp] theorem ofLeftInvariantMetric_toNormedGroup (ℓ : GroupNorm G) :
    letI := ℓ.toNormedGroup
    ofLeftInvariantMetric (fun g h k => by simp [dist_eq_norm_inv_mul, mul_assoc]) = ℓ := by
  ext g
  simp [dist_eq_norm_inv_mul, norm]

end GroupNorm

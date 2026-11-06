/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Conjugation-invariant group norms and bi-invariant metrics

A group norm `ℓ` on a group `G` is conjugation invariant (`GroupNorm.IsConjInvariant`) when
`ℓ (h * g * h⁻¹) = ℓ g`. Equivalently `ℓ (g * h) = ℓ (h * g)`, so the norm of a product of a
list does not change under cyclic rotation of the list. Every group norm, conjugation invariant
or not, is unchanged by reversing a list and inverting each factor. These are the facts that make
the norm of the holonomy of a triangle independent of the starting vertex and of the direction
of travel.

The metric of a group norm is Mathlib's `GroupNorm.toNormedGroup`, with
`dist g h = ℓ (g⁻¹ * h)` (`GroupNorm.dist_toNormedGroup`); Mathlib supplies its symmetry,
triangle inequality, separation, and invariance under left multiplication. It is also invariant
under right multiplication exactly when `ℓ` is conjugation invariant
(`GroupNorm.isConjInvariant_iff_isIsometricSMul_right`).

Conversely, a left-invariant metric gives the group norm `GroupNorm.ofMulDist G : g ↦ dist 1 g`.
The two constructions are mutually inverse (`GroupNorm.ofMulDist_toNormedGroup` and
`GroupNorm.toMetricSpace_toNormedGroup_ofMulDist`), and the norm is conjugation invariant exactly
when the metric is also right invariant (`GroupNorm.isConjInvariant_ofMulDist_iff`). Hence
conjugation-invariant group norms correspond to bi-invariant metrics.

These norms are the coefficient norms of coboundary expansion with nonabelian coefficients, for
example the moved-point norm on permutations used by Chapman and Lubotzky, *Stability of
homomorphisms, coverings and cocycles II* (arXiv:2311.06706), equation (2.8).
-/

public section

namespace GroupNorm

variable {G : Type*} [Group G]

/-- A group norm is conjugation invariant when `ℓ (h * g * h⁻¹) = ℓ g` for all `g` and `h`. -/
def IsConjInvariant (ℓ : GroupNorm G) : Prop :=
  ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g

variable {ℓ : GroupNorm G}

/-- Unfold conjugation invariance. -/
theorem isConjInvariant_iff : ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g :=
  Iff.rfl

namespace IsConjInvariant

/-- A conjugation-invariant group norm takes the same value on `g` and on `h * g * h⁻¹`. -/
theorem map_conj (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (h * g * h⁻¹) = ℓ g :=
  hℓ g h

/-- A conjugation-invariant group norm takes the same value on `g` and on `h⁻¹ * g * h`. -/
theorem map_inv_mul_mul (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (h⁻¹ * g * h) = ℓ g := by
  simpa using hℓ g h⁻¹

/-- A conjugation-invariant group norm does not see the order of two factors. -/
theorem map_mul_comm (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (g * h) = ℓ (h * g) := by
  simpa [mul_assoc] using hℓ (h * g) g

/-- The norm of a list product is invariant under cyclic rotation of the list. -/
theorem map_prod_rotate (hℓ : ℓ.IsConjInvariant) (l : List G) (n : ℕ) :
    ℓ (l.rotate n).prod = ℓ l.prod := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append, hℓ.map_mul_comm, ← List.prod_append,
    List.take_append_drop]

end IsConjInvariant

/-- A group norm is conjugation invariant exactly when it does not see the order of two
factors. -/
theorem isConjInvariant_iff_map_mul_comm :
    ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (g * h) = ℓ (h * g) := by
  refine ⟨IsConjInvariant.map_mul_comm, fun h g k ↦ ?_⟩
  rw [mul_assoc, h, inv_mul_cancel_right]

/-- Every group norm on a commutative group is conjugation invariant. -/
theorem isConjInvariant_of_commGroup {G : Type*} [CommGroup G] (ℓ : GroupNorm G) :
    ℓ.IsConjInvariant :=
  isConjInvariant_iff_map_mul_comm.mpr fun g h ↦ by rw [mul_comm]

/-- The norm of a list product is unchanged by reversing the list and inverting each factor. -/
theorem map_prod_reverse_map_inv (ℓ : GroupNorm G) (l : List G) :
    ℓ (l.map (·⁻¹)).reverse.prod = ℓ l.prod := by
  rw [← List.prod_inv_reverse, map_inv_eq_map]

/-! ### The metric of a group norm -/

/-- The distance of the metric of a group norm is `dist g h = ℓ (g⁻¹ * h)`. -/
theorem dist_toNormedGroup (ℓ : GroupNorm G) (g h : G) :
    letI := ℓ.toNormedGroup
    dist g h = ℓ (g⁻¹ * h) :=
  (rfl)

/-- The metric of a group norm is invariant under right multiplication exactly when the norm is
conjugation invariant. Mathlib supplies its invariance under left multiplication. -/
theorem isConjInvariant_iff_isIsometricSMul_right :
    ℓ.IsConjInvariant ↔
      letI := ℓ.toNormedGroup
      IsIsometricSMul Gᵐᵒᵖ G := by
  let := ℓ.toNormedGroup
  refine ⟨fun hℓ ↦ ⟨fun a ↦ Isometry.of_dist_eq fun g h ↦ ?_⟩, fun _ g h ↦ ?_⟩
  · rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, dist_toNormedGroup,
      dist_toNormedGroup, ← hℓ.map_inv_mul_mul (g⁻¹ * h) a.unop]
    group
  · simpa [dist_toNormedGroup, mul_assoc] using dist_mul_right 1 g h⁻¹

/-! ### The group norm of a left-invariant metric -/

section OfMulDist

variable (G) [MetricSpace G] [IsIsometricSMul G G]

/-- The group norm `g ↦ dist 1 g` of a metric on a group invariant under left multiplication. -/
noncomputable def ofMulDist : GroupNorm G where
  toFun := dist 1
  map_one' := dist_self 1
  mul_le' g h :=
    (dist_triangle 1 g (g * h)).trans_eq (by rw [← dist_mul_left g 1 h, mul_one])
  inv' g := by rw [← dist_mul_left g, mul_one, mul_inv_cancel, dist_comm]
  eq_one_of_map_eq_zero' _ h := (dist_eq_zero.mp h).symm

/-- The group norm of a left-invariant metric is the distance from `1`. -/
@[simp]
theorem ofMulDist_apply (g : G) : ofMulDist G g = dist 1 g :=
  (rfl)

/-- A left-invariant metric is recovered from its group norm: `dist g h = ofMulDist G (g⁻¹ * h)`.
-/
theorem dist_eq_ofMulDist (g h : G) : dist g h = ofMulDist G (g⁻¹ * h) := by
  rw [ofMulDist_apply, ← dist_mul_left g⁻¹ g h, inv_mul_cancel]

/-- The metric of the group norm of a left-invariant metric is the original metric. -/
theorem toMetricSpace_toNormedGroup_ofMulDist :
    (ofMulDist G).toNormedGroup.toMetricSpace = ‹MetricSpace G› := by
  exact MetricSpace.ext <| congrArg Dist.mk <| funext₂ fun g h ↦ (dist_eq_ofMulDist G g h).symm

/-- The group norm of a left-invariant metric is conjugation invariant exactly when the metric is
also invariant under right multiplication. -/
theorem isConjInvariant_ofMulDist_iff :
    (ofMulDist G).IsConjInvariant ↔ IsIsometricSMul Gᵐᵒᵖ G := by
  refine ⟨fun hℓ ↦ ⟨fun a ↦ Isometry.of_dist_eq fun g h ↦ ?_⟩, fun _ g h ↦ ?_⟩
  · rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, dist_eq_ofMulDist G (g * _),
      dist_eq_ofMulDist G g, ← hℓ.map_inv_mul_mul (g⁻¹ * h) a.unop]
    group
  · rw [ofMulDist_apply, ofMulDist_apply, ← dist_mul_left h⁻¹, ← dist_mul_right 1 g h⁻¹]
    simp [mul_assoc]

end OfMulDist

/-- The group norm of the metric of a group norm is the original group norm. -/
theorem ofMulDist_toNormedGroup (ℓ : GroupNorm G) :
    letI := ℓ.toNormedGroup
    ofMulDist G = ℓ := by
  let := ℓ.toNormedGroup
  ext g
  rw [ofMulDist_apply, dist_toNormedGroup, inv_one, one_mul]

end GroupNorm

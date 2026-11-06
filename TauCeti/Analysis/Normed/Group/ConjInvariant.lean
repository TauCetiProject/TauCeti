/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Data.List.Rotate

/-!
# Conjugation-invariant group norms

A group norm `ℓ` on a group `G` is conjugation invariant when `ℓ (h * g * h⁻¹) = ℓ g`. Such norms
are the coefficient norms of nonabelian coboundary expansion: the norm of the holonomy of a
cochain around a triangle then depends neither on the starting vertex nor on the direction of
travel, and constant gauges do not change the cost of a cochain.

Mathlib's `GroupNorm.toNormedGroup` equips `G` with the metric `dist g h = ℓ (g⁻¹ * h)`; it is
always invariant under left multiplication (`NormedGroup.to_isIsometricSMul`). We show that it
is invariant under right multiplication exactly when `ℓ` is conjugation invariant. Conversely,
`GroupNorm.ofMulDist` turns a left-invariant metric into the group norm `g ↦ dist 1 g`, which is
conjugation invariant when the metric is also right invariant, and the two constructions are
mutually inverse. So conjugation-invariant group norms are the same as bi-invariant metrics.

## Main definitions

* `GroupNorm.IsConjInvariant`: the norm of an element is unchanged by conjugation.
* `GroupNorm.ofMulDist`: the group norm `g ↦ dist 1 g` of a left-invariant metric.
* `GroupNorm.comp`: the pullback of a group norm along an injective homomorphism; along the
  inclusion of a subgroup, this is the restricted norm.
* `GroupNorm.smulOfPos`: a group norm multiplied by a positive real number.

## Main statements

* `GroupNorm.isConjInvariant_iff_map_mul_comm`: conjugation invariance is `ℓ (g * h) = ℓ (h * g)`.
* `GroupNorm.IsConjInvariant.map_prod_rotate`: the norm of a product is invariant under cyclic
  rotation of the factors; `GroupNorm.map_prod_map_inv_reverse`: and under reversal with
  inversion of each factor, for every group norm.
* `GroupNorm.isConjInvariant_iff_isIsometricSMul_mulOpposite`: conjugation invariance is right
  invariance of the metric `dist g h = ℓ (g⁻¹ * h)`.
* `GroupNorm.ofMulDist_toNormedGroup` and `GroupNorm.toMetricSpace_ofMulDist`: the round trips
  between group norms and left-invariant metrics.
* `GroupNorm.IsConjInvariant.comp`, `GroupNorm.IsConjInvariant.smulOfPos`,
  `GroupNorm.IsConjInvariant.add` and `GroupNorm.IsConjInvariant.sup`: the constructions preserve
  conjugation invariance.
-/

public section

open Function

namespace GroupNorm

variable {G H : Type*} [Group G] [Group H]

/-- A group norm is conjugation invariant when `ℓ (h * g * h⁻¹) = ℓ g` for all `g` and `h`. -/
def IsConjInvariant (ℓ : GroupNorm G) : Prop :=
  ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g

/-- Unfold conjugation invariance into its defining equation. -/
theorem isConjInvariant_iff {ℓ : GroupNorm G} :
    ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (h * g * h⁻¹) = ℓ g :=
  Iff.rfl

/-- Every group norm on a commutative group is conjugation invariant. -/
theorem isConjInvariant_of_commGroup {A : Type*} [CommGroup A] (ℓ : GroupNorm A) :
    ℓ.IsConjInvariant := fun g h ↦ by
  rw [mul_inv_cancel_comm]

namespace IsConjInvariant

variable {ℓ : GroupNorm G}

/-- A conjugation-invariant norm takes the same value on `g` and on `h * g * h⁻¹`. -/
@[simp]
theorem map_conj (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (h * g * h⁻¹) = ℓ g :=
  hℓ g h

/-- A conjugation-invariant norm takes the same value on `g` and on `h⁻¹ * g * h`. -/
@[simp]
theorem map_inv_mul_mul (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (h⁻¹ * g * h) = ℓ g := by
  simpa using hℓ g h⁻¹

/-- A conjugation-invariant norm does not see the order of the two factors of a product. -/
theorem map_mul_comm (hℓ : ℓ.IsConjInvariant) (g h : G) : ℓ (g * h) = ℓ (h * g) := by
  simpa [mul_assoc] using hℓ (h * g) g

end IsConjInvariant

/-- A group norm is conjugation invariant exactly when it does not see the order of the two
factors of a product. -/
theorem isConjInvariant_iff_map_mul_comm {ℓ : GroupNorm G} :
    ℓ.IsConjInvariant ↔ ∀ g h : G, ℓ (g * h) = ℓ (h * g) := by
  refine ⟨IsConjInvariant.map_mul_comm, fun h g k ↦ ?_⟩
  rw [h, inv_mul_cancel_left]

/-- The norm of a product is invariant under reversing the factors and inverting each of them.
This holds for every group norm, since the reversed product is the inverse of the original. -/
@[simp]
theorem map_prod_map_inv_reverse (ℓ : GroupNorm G) (l : List G) :
    ℓ (l.map (·⁻¹)).reverse.prod = ℓ l.prod := by
  rw [← List.prod_inv_reverse, map_inv_eq_map]

/-- Under a conjugation-invariant norm, the norm of a product is invariant under cyclic rotation
of the factors. -/
@[simp]
theorem IsConjInvariant.map_prod_rotate {ℓ : GroupNorm G} (hℓ : ℓ.IsConjInvariant) (l : List G)
    (n : ℕ) : ℓ (l.rotate n).prod = ℓ l.prod := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append, hℓ.map_mul_comm,
    List.prod_take_mul_prod_drop]

/-! ### Bi-invariant metrics -/

/-- The norm of the normed group structure `ℓ.toNormedGroup` is `ℓ`. -/
@[simp]
theorem norm_toNormedGroup (ℓ : GroupNorm G) (g : G) : letI := ℓ.toNormedGroup; ‖g‖ = ℓ g :=
  (rfl)

/-- The metric of the normed group structure `ℓ.toNormedGroup` is `dist g h = ℓ (g⁻¹ * h)`. -/
theorem dist_toNormedGroup (ℓ : GroupNorm G) (g h : G) :
    letI := ℓ.toNormedGroup; dist g h = ℓ (g⁻¹ * h) :=
  (rfl)

variable (G) in
/-- The group norm `g ↦ dist 1 g` of a metric invariant under left multiplication. -/
def ofMulDist [MetricSpace G] [IsIsometricSMul G G] : GroupNorm G where
  toFun := dist 1
  map_one' := dist_self 1
  mul_le' g h := by
    rw [← dist_mul_left g 1 h, mul_one]
    exact dist_triangle 1 g (g * h)
  inv' g := by
    rw [← dist_mul_left g, mul_one, mul_inv_cancel, dist_comm]
  eq_one_of_map_eq_zero' _ h := (dist_eq_zero.mp h).symm

section ofMulDist

variable [MetricSpace G] [IsIsometricSMul G G]

@[simp]
theorem ofMulDist_apply (g : G) : ofMulDist G g = dist 1 g :=
  (rfl)

/-- The metric is recovered from its group norm as `dist g h = ofMulDist G (g⁻¹ * h)`. -/
theorem ofMulDist_inv_mul (g h : G) : ofMulDist G (g⁻¹ * h) = dist g h := by
  rw [ofMulDist_apply, ← dist_mul_left g, mul_one, mul_inv_cancel_left]

/-- The group norm of a metric invariant under left and right multiplication is conjugation
invariant. -/
theorem isConjInvariant_ofMulDist [IsIsometricSMul Gᵐᵒᵖ G] : (ofMulDist G).IsConjInvariant :=
  fun g h ↦ by
    rw [ofMulDist_apply, ofMulDist_apply, ← dist_mul_left h⁻¹, ← dist_mul_right _ _ h]
    simp [mul_assoc]

/-- Passing from a left-invariant metric to its group norm and back gives the original metric. -/
theorem toMetricSpace_ofMulDist :
    (ofMulDist G).toNormedGroup.toMetricSpace = ‹MetricSpace G› :=
  MetricSpace.ext <| Dist.ext <| funext₂ fun g h ↦
    (dist_toNormedGroup _ g h).trans (ofMulDist_inv_mul g h)

end ofMulDist

/-- Passing from a group norm to its metric and back gives the original norm. -/
theorem ofMulDist_toNormedGroup (ℓ : GroupNorm G) :
    letI := ℓ.toNormedGroup; ofMulDist G = ℓ := by
  let _ := ℓ.toNormedGroup
  ext g
  rw [ofMulDist_apply, dist_one_left, norm_toNormedGroup]

/-- The metric `dist g h = ℓ (g⁻¹ * h)` of a group norm is invariant under right multiplication
exactly when the norm is conjugation invariant. -/
theorem isConjInvariant_iff_isIsometricSMul_mulOpposite (ℓ : GroupNorm G) :
    ℓ.IsConjInvariant ↔ letI := ℓ.toNormedGroup; IsIsometricSMul Gᵐᵒᵖ G := by
  let _ := ℓ.toNormedGroup
  refine ⟨fun hℓ ↦ ⟨fun c ↦ Isometry.of_dist_eq fun g h ↦ ?_⟩, fun _ ↦ ?_⟩
  · rw [MulOpposite.smul_eq_mul_unop, MulOpposite.smul_eq_mul_unop, dist_toNormedGroup,
      dist_toNormedGroup]
    simpa [mul_assoc] using hℓ.map_inv_mul_mul (g⁻¹ * h) c.unop
  · rw [← ofMulDist_toNormedGroup ℓ]
    exact isConjInvariant_ofMulDist

/-! ### Constructions -/

/-- The pullback of a group norm along an injective homomorphism. Along the inclusion of a
subgroup `K`, `ℓ.comp K.subtype_injective` is the restriction of the norm to `K`. -/
def comp (ℓ : GroupNorm G) {f : H →* G} (hf : Injective f) : GroupNorm H where
  toGroupSeminorm := ℓ.toGroupSeminorm.comp f
  eq_one_of_map_eq_zero' _ h := hf <| by
    rw [map_one]
    exact eq_one_of_map_eq_zero ℓ h

@[simp]
theorem comp_apply (ℓ : GroupNorm G) {f : H →* G} (hf : Injective f) (x : H) :
    ℓ.comp hf x = ℓ (f x) :=
  (rfl)

/-- The pullback of a conjugation-invariant norm is conjugation invariant. -/
theorem IsConjInvariant.comp {ℓ : GroupNorm G} (hℓ : ℓ.IsConjInvariant) {f : H →* G}
    (hf : Injective f) : (ℓ.comp hf).IsConjInvariant := fun g h ↦ by
  simp [hℓ.map_conj]

/-- A group norm multiplied by a positive real number. -/
def smulOfPos (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) : GroupNorm G where
  toGroupSeminorm := (show NNReal from ⟨r, hr.le⟩) • ℓ.toGroupSeminorm
  eq_one_of_map_eq_zero' _ h :=
    eq_one_of_map_eq_zero ℓ <| (mul_eq_zero.mp h).resolve_left hr.ne'

@[simp]
theorem smulOfPos_apply (ℓ : GroupNorm G) {r : ℝ} (hr : 0 < r) (g : G) :
    ℓ.smulOfPos hr g = r * ℓ g :=
  (rfl)

/-- A positive multiple of a conjugation-invariant norm is conjugation invariant. -/
theorem IsConjInvariant.smulOfPos {ℓ : GroupNorm G} (hℓ : ℓ.IsConjInvariant) {r : ℝ}
    (hr : 0 < r) : (ℓ.smulOfPos hr).IsConjInvariant := fun g h ↦ by
  simp [hℓ.map_conj]

/-- The sum of two conjugation-invariant norms is conjugation invariant. -/
theorem IsConjInvariant.add {ℓ ℓ' : GroupNorm G} (hℓ : ℓ.IsConjInvariant)
    (hℓ' : ℓ'.IsConjInvariant) : (ℓ + ℓ').IsConjInvariant := fun g h ↦ by
  simp [hℓ.map_conj, hℓ'.map_conj]

/-- The pointwise maximum of two conjugation-invariant norms is conjugation invariant. -/
theorem IsConjInvariant.sup {ℓ ℓ' : GroupNorm G} (hℓ : ℓ.IsConjInvariant)
    (hℓ' : ℓ'.IsConjInvariant) : (ℓ ⊔ ℓ').IsConjInvariant := fun g h ↦ by
  simp [hℓ.map_conj, hℓ'.map_conj]

end GroupNorm

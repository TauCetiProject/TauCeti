/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Weight
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Weil divisors as finite integer combinations of points

This file provides the first, purely combinatorial piece of the Jacobian roadmap's Layer A:
Weil divisors are finite formal integer sums of points.  The scheme-theoretic predicates
which decide which points are codimension-one points, the principal-divisor map, and the
comparison with Cartier divisors are deliberately not bundled here; those are later geometric
constructions.

The API here records the free-abelian-group operations needed before that geometry exists:
point divisors, effectivity, pushforward of formal sums along a map of point sets, and both
the unweighted degree and the weighted degree used for curves over a field.

For a curve over `k`, the intended weighted degree has weight
`x ↦ [κ(x) : k]`; this file only supplies the formal finite-sum operation against an arbitrary
integer-valued weight.

This advances the Tau Ceti Jacobian roadmap, Layer A, "Divisors on a curve: Weil divisors
`⊕_x ℤ`" and "Degree".
-/

namespace TauCeti

namespace AlgebraicGeometry

/-- A Weil divisor on a type of points `X` is a finite formal integer sum of points of `X`. -/
abbrev WeilDivisor (X : Type*) : Type _ :=
  X →₀ ℤ

namespace WeilDivisor

variable {X Y Z : Type*}

noncomputable section

/-- The coefficient of a point in a Weil divisor. -/
def coeff (D : WeilDivisor X) (x : X) : ℤ :=
  D x

@[simp]
lemma coeff_zero (x : X) : coeff (0 : WeilDivisor X) x = 0 :=
  rfl

@[simp]
lemma coeff_add (D E : WeilDivisor X) (x : X) :
    coeff (D + E) x = coeff D x + coeff E x :=
  rfl

@[simp]
lemma coeff_neg (D : WeilDivisor X) (x : X) : coeff (-D) x = -coeff D x :=
  rfl

@[simp]
lemma coeff_sub (D E : WeilDivisor X) (x : X) :
    coeff (D - E) x = coeff D x - coeff E x :=
  rfl

@[ext]
lemma ext {D E : WeilDivisor X} (h : ∀ x, coeff D x = coeff E x) : D = E :=
  Finsupp.ext h

/-- The prime/point divisor supported at a single point with coefficient `1`. -/
noncomputable def ofPoint [DecidableEq X] (x : X) : WeilDivisor X :=
  Finsupp.single x 1

@[simp]
lemma coeff_ofPoint_self [DecidableEq X] (x : X) : coeff (ofPoint x) x = 1 := by
  simp [coeff, ofPoint]

@[simp]
lemma coeff_ofPoint_of_ne [DecidableEq X] {x y : X} (h : y ≠ x) :
    coeff (ofPoint x) y = 0 := by
  simp [coeff, ofPoint, h]

@[simp]
lemma support_ofPoint [DecidableEq X] (x : X) : (ofPoint x).support = {x} := by
  ext y
  by_cases h : y = x <;> simp [ofPoint, h]

/-- A divisor is effective when every coefficient is nonnegative. -/
def IsEffective (D : WeilDivisor X) : Prop :=
  ∀ x, 0 ≤ coeff D x

lemma isEffective_iff (D : WeilDivisor X) : IsEffective D ↔ ∀ x, 0 ≤ coeff D x :=
  Iff.rfl

@[simp]
lemma isEffective_zero : IsEffective (0 : WeilDivisor X) := by
  intro x
  simp

lemma IsEffective.add {D E : WeilDivisor X} (hD : IsEffective D) (hE : IsEffective E) :
    IsEffective (D + E) := by
  intro x
  simpa [IsEffective] using add_nonneg (hD x) (hE x)

lemma IsEffective.nsmul {D : WeilDivisor X} (hD : IsEffective D) (n : ℕ) :
    IsEffective (n • D) := by
  intro x
  simpa [IsEffective, coeff] using nsmul_nonneg (hD x) n

@[simp]
lemma isEffective_ofPoint [DecidableEq X] (x : X) : IsEffective (ofPoint x) := by
  intro y
  by_cases h : y = x
  · subst h
    simp
  · simp [coeff_ofPoint_of_ne h]

/-- Effective Weil divisors form an additive submonoid of the group of all Weil divisors. -/
def effectiveSubmonoid (X : Type*) : AddSubmonoid (WeilDivisor X) where
  carrier := {D | IsEffective D}
  zero_mem' := isEffective_zero
  add_mem' := by
    intro D E hD hE
    exact IsEffective.add hD hE

@[simp]
lemma mem_effectiveSubmonoid (D : WeilDivisor X) :
    D ∈ effectiveSubmonoid X ↔ IsEffective D :=
  show IsEffective D ↔ IsEffective D from Iff.rfl

/-- Push forward a formal divisor along a map of point sets by summing coefficients over
fibres.  Geometric pushforward of Weil divisors will specialize this once the relevant point
maps and residue-degree factors are available. -/
noncomputable def pushForward (f : X → Y) : WeilDivisor X →+ WeilDivisor Y :=
  (Finsupp.lmapDomain ℤ ℤ f).toAddMonoidHom

@[simp]
lemma pushForward_apply (f : X → Y) (D : WeilDivisor X) :
    pushForward f D = D.mapDomain f :=
  rfl

@[simp]
lemma pushForward_zero (f : X → Y) : pushForward f (0 : WeilDivisor X) = 0 :=
  map_zero (pushForward f)

@[simp]
lemma pushForward_add (f : X → Y) (D E : WeilDivisor X) :
    pushForward f (D + E) = pushForward f D + pushForward f E :=
  map_add (pushForward f) D E

@[simp]
lemma pushForward_ofPoint [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    pushForward f (ofPoint x) = ofPoint (f x) := by
  simp [pushForward, ofPoint]

@[simp]
lemma pushForward_id : pushForward (fun x : X => x) = AddMonoidHom.id (WeilDivisor X) := by
  ext D x
  simp [pushForward, coeff]

lemma pushForward_comp (g : Y → Z) (f : X → Y) :
    pushForward (g ∘ f) = (pushForward g).comp (pushForward f) := by
  ext D z
  simp [pushForward, Function.comp_def]

/-- The unweighted degree of a Weil divisor, summing its coefficients.  On a curve over a
non-algebraically-closed field, use `weightedDegree` with residue-field degrees instead. -/
noncomputable def degree : WeilDivisor X →+ ℤ :=
  Finsupp.degree

lemma degree_apply (D : WeilDivisor X) : degree D = ∑ x ∈ D.support, D x :=
  rfl

@[simp]
lemma degree_zero : degree (0 : WeilDivisor X) = 0 :=
  map_zero degree

@[simp]
lemma degree_add (D E : WeilDivisor X) : degree (D + E) = degree D + degree E :=
  map_add degree D E

@[simp]
lemma degree_neg (D : WeilDivisor X) : degree (-D) = -degree D :=
  map_neg degree D

@[simp]
lemma degree_sub (D E : WeilDivisor X) : degree (D - E) = degree D - degree E :=
  map_sub degree D E

@[simp]
lemma degree_ofPoint [DecidableEq X] (x : X) : degree (ofPoint x) = 1 := by
  simp [degree, ofPoint]

@[simp]
lemma degree_pushForward (f : X → Y) (D : WeilDivisor X) :
    degree (pushForward f D) = degree D := by
  simp [degree, pushForward, Finsupp.degree_mapDomain]

/-- The weighted degree of a Weil divisor against an integer-valued weight on points.

For a curve over `k`, the intended weight is `x ↦ [κ(x) : k]`. -/
noncomputable def weightedDegree (w : X → ℤ) : WeilDivisor X →+ ℤ :=
  (Finsupp.linearCombination ℤ w).toAddMonoidHom

lemma weightedDegree_apply (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w D = D.sum fun x n => n * w x := by
  simp [weightedDegree, Finsupp.linearCombination_apply]

@[simp]
lemma weightedDegree_zero (w : X → ℤ) : weightedDegree w (0 : WeilDivisor X) = 0 :=
  map_zero (weightedDegree w)

@[simp]
lemma weightedDegree_add (w : X → ℤ) (D E : WeilDivisor X) :
    weightedDegree w (D + E) = weightedDegree w D + weightedDegree w E :=
  map_add (weightedDegree w) D E

@[simp]
lemma weightedDegree_neg (w : X → ℤ) (D : WeilDivisor X) :
    weightedDegree w (-D) = -weightedDegree w D :=
  map_neg (weightedDegree w) D

@[simp]
lemma weightedDegree_sub (w : X → ℤ) (D E : WeilDivisor X) :
    weightedDegree w (D - E) = weightedDegree w D - weightedDegree w E :=
  map_sub (weightedDegree w) D E

@[simp]
lemma weightedDegree_ofPoint [DecidableEq X] (w : X → ℤ) (x : X) :
    weightedDegree w (ofPoint x) = w x := by
  simp [weightedDegree, ofPoint]

lemma weightedDegree_pushForward (wY : Y → ℤ) (f : X → Y) (D : WeilDivisor X) :
    weightedDegree wY (pushForward f D) = weightedDegree (wY ∘ f) D := by
  simp [weightedDegree, pushForward, Finsupp.linearCombination_mapDomain]

@[simp]
lemma weightedDegree_one (D : WeilDivisor X) :
    weightedDegree (fun _ : X => (1 : ℤ)) D = degree D := by
  rw [weightedDegree_apply, degree_apply]
  simp [Finsupp.sum]

end

end WeilDivisor

end AlgebraicGeometry

end TauCeti

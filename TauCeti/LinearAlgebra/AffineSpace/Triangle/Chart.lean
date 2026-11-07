/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The affine chart of the plane of a triangle

For three points `a`, `b`, `c` of an affine space `P` over a commutative ring `k`,
`TauCeti.triangleChart k a b c` is the affine map `(s, t) ↦ a + s • (b - a) + t • (c - a)` from the
coordinate plane `k × k` to `P`.
It sends `(0, 0)`, `(1, 0)` and `(0, 1)` to `a`, `b` and `c`, and the midpoints of the sides of the
standard triangle to the midpoints of the sides of `abc`. It is injective when `a`, `b`, `c` are
affinely independent, so incidence questions about a triangle and its subdivisions can be decided
in the coordinate plane.

Three points of the coordinate plane over a field are affinely independent exactly when the
determinant of the two difference vectors is nonzero (`TauCeti.affineIndependent_iff_det_ne_zero`).

If the sides `b - a` and `d - a` of a parallelogram `abcd` are linearly independent, then three of
its vertices `b`, `d`, `c = b + (d - a)` are affinely independent
(`LinearIndependent.affineIndependent_vsub_vadd`).

## Main definitions

* `TauCeti.triangleChart`: the affine chart of the plane through three points.

## Main results

* `TauCeti.triangleChart_injective`: the chart of an affinely independent triple is injective.
* `TauCeti.affineIndependent_iff_det_ne_zero`: three points of `k × k` are affinely independent iff
  `det (y - x, z - x) ≠ 0`.
* `LinearIndependent.affineIndependent_vsub_vadd`: if `b - a`, `d - a` are linearly independent,
  then `b`, `d`, `b + (d - a)` (three vertices of the parallelogram `abcd`) are affinely
  independent.
-/

public section

open Function

namespace TauCeti

section Chart

variable (k : Type*) {V P : Type*} [CommRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/-- The affine chart `(s, t) ↦ a + s • (b - a) + t • (c - a)` of the plane through `a`, `b`, `c`,
sending `(0, 0)`, `(1, 0)` and `(0, 1)` to `a`, `b` and `c`. -/
def triangleChart (a b c : P) : k × k →ᵃ[k] P :=
  (AffineEquiv.vaddConst k a).toAffineMap.comp
    ((LinearMap.fst k k k).smulRight (b -ᵥ a) +
      (LinearMap.snd k k k).smulRight (c -ᵥ a)).toAffineMap

variable {k}

@[simp]
theorem triangleChart_apply (a b c : P) (x : k × k) :
    triangleChart k a b c x = (x.1 • (b -ᵥ a) + x.2 • (c -ᵥ a)) +ᵥ a :=
  (rfl)

theorem triangleChart_apply_zero_zero (a b c : P) : triangleChart k a b c (0, 0) = a := by
  simp

theorem triangleChart_apply_one_zero (a b c : P) : triangleChart k a b c (1, 0) = b := by
  simp

theorem triangleChart_apply_zero_one (a b c : P) : triangleChart k a b c (0, 1) = c := by
  simp

/-- The chart of the plane of an affinely independent triple is injective. -/
theorem triangleChart_injective {a b c : P} (h : AffineIndependent k ![a, b, c]) :
    Injective (triangleChart k a b c) := by
  have hli : LinearIndependent k ![b -ᵥ a, c -ᵥ a] := by
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0] at h
    convert h.comp ![⟨1, by decide⟩, ⟨2, by decide⟩] (by decide) using 1
    ext j
    fin_cases j <;> rfl
  intro x y hxy
  rw [triangleChart_apply, triangleChart_apply, vadd_right_cancel_iff, ← sub_eq_zero] at hxy
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 hli (x.1 - y.1) (x.2 - y.2) (by
    rw [← hxy]
    module)
  exact Prod.ext (sub_eq_zero.1 h₁) (sub_eq_zero.1 h₂)

end Chart

section Midpoint

variable {k : Type*} {V P : Type*} [Field k] [Invertible (2 : k)] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem triangleChart_apply_half_zero (a b c : P) :
    triangleChart k a b c (1 / 2, 0) = midpoint k a b := by
  simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv]

theorem triangleChart_apply_zero_half (a b c : P) :
    triangleChart k a b c (0, 1 / 2) = midpoint k a c := by
  simp [midpoint, AffineMap.lineMap_apply, invOf_eq_inv]

theorem triangleChart_apply_half_half (a b c : P) :
    triangleChart k a b c (1 / 2, 1 / 2) = midpoint k c b := by
  simp only [triangleChart_apply, midpoint, AffineMap.lineMap_apply, eq_vadd_iff_vsub_eq,
    vadd_vsub_assoc, ← vsub_sub_vsub_cancel_right b c a, ← neg_vsub_eq_vsub_rev c a, invOf_eq_inv]
  have : (2 : k) ≠ 0 := Invertible.ne_zero 2
  match_scalars <;> field_simp
  ring

end Midpoint

section Independent

variable {k : Type*} [Field k]

/-- Three points of the coordinate plane are affinely independent if and only if the determinant
`det (y - x, z - x)` of their difference vectors is nonzero. -/
theorem affineIndependent_iff_det_ne_zero {x y z : k × k} :
    AffineIndependent k ![x, y, z] ↔
      (y.1 - x.1) * (z.2 - x.2) - (y.2 - x.2) * (z.1 - x.1) ≠ 0 := by
  have hli : AffineIndependent k ![x, y, z] ↔ LinearIndependent k ![y - x, z - x] := by
    rw [affineIndependent_iff_linearIndependent_vsub k _ 0,
      ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
    convert Iff.rfl using 2
    funext j
    fin_cases j <;> rfl
  rw [hli, LinearIndependent.pair_iff]
  constructor
  · -- A vanishing determinant gives a nontrivial relation between the two difference vectors.
    intro h hdet
    have key : ∀ s t : k, s * (y.1 - x.1) + t * (z.1 - x.1) = 0 →
        s * (y.2 - x.2) + t * (z.2 - x.2) = 0 → s = 0 ∧ t = 0 := fun s t e₁ e₂ =>
      h s t (Prod.ext (by simpa using e₁) (by simpa using e₂))
    obtain ⟨h₁, h₂⟩ := key (z.2 - x.2) (-(y.2 - x.2)) (by linear_combination hdet) (by ring)
    obtain ⟨-, h₄⟩ := key (z.1 - x.1) (-(y.1 - x.1)) (by ring)
      (by linear_combination -(z.1 - x.1) * h₂ - (y.1 - x.1) * h₁)
    exact one_ne_zero (key 1 0 (by linear_combination -h₄) (by linear_combination -h₂)).1
  · intro h s t hst
    have h₁ := congrArg Prod.fst hst
    have h₂ := congrArg Prod.snd hst
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul, Prod.fst_zero, Prod.snd_zero] at h₁ h₂
    constructor
    · refine (mul_eq_zero.1 ?_).resolve_right h
      linear_combination (z.2 - x.2) * h₁ - (z.1 - x.1) * h₂
    · refine (mul_eq_zero.1 ?_).resolve_right h
      linear_combination (y.1 - x.1) * h₂ - (y.2 - x.2) * h₁

end Independent

end TauCeti

section Parallelogram

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- If the sides `b - a` and `d - a` are linearly independent, then the points `b`, `d`,
`c = b + (d - a)` (three vertices of the parallelogram `abcd`) are affinely independent. -/
theorem LinearIndependent.affineIndependent_vsub_vadd {a b d : P}
    (hli : LinearIndependent R ![b -ᵥ a, d -ᵥ a]) :
    AffineIndependent R ![b, d, (d -ᵥ a) +ᵥ b] := by
  rw [affineIndependent_iff_linearIndependent_vsub R _ 0,
    ← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  have hdb : d -ᵥ b = (d -ᵥ a) - (b -ᵥ a) := (vsub_sub_vsub_cancel_right d b a).symm
  have hcb : ((d -ᵥ a) +ᵥ b) -ᵥ b = d -ᵥ a := vadd_vsub _ _
  have hli' : LinearIndependent R ![(d -ᵥ a) - (b -ᵥ a), d -ᵥ a] := by
    simpa only [sub_eq_add_neg, add_comm (d -ᵥ a), LinearIndependent.pair_add_left_iff,
      LinearIndependent.pair_neg_left_iff] using hli
  convert hli' using 1
  ext j
  fin_cases j
  · exact hdb
  · exact hcb

end Parallelogram

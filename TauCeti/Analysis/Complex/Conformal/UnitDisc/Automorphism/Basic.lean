/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Moebius
public import TauCeti.Analysis.Complex.UnitDisc.Basic

/-!
# Standard automorphisms of the complex unit disc

This file adds the rotation factor in the standard disc-automorphism formula
`z ↦ u * (z - a) / (1 - conj a * z)`, with `u` on the unit circle and `a` in the
unit disc.  The previous Moebius file supplies the factor sending `a` to `0`; this file
composes it with Mathlib's `Circle` action on `Complex.UnitDisc`.

This advances the conformal-mapping roadmap's L2 disc-automorphism target.  It reuses
Mathlib's `Circle` action on `Complex.UnitDisc` and Tau Ceti's `unitDiscMoebiusEquiv`.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only adds the small discoverable API around `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open _root_.Complex
open scoped ComplexConjugate

/--
The standard automorphism of the complex unit disc
`z ↦ u * (z - a) / (1 - conj a * z)`.

The center-removing factor is `unitDiscMoebiusEquiv a`; the circle element `u` supplies the
rotation factor in the usual classification formula for disc automorphisms.
-/
noncomputable def unitDiscStandardAutomorphismEquiv (u : Circle) (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ Complex.UnitDisc :=
  (unitDiscMoebiusEquiv a).trans (MulAction.toPerm u : Equiv.Perm Complex.UnitDisc)

/-- The standard automorphism applies by first sending `a` to `0`, then rotating. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a z = u • unitDiscMoebius a z :=
  by simp [unitDiscStandardAutomorphismEquiv]

/-- The scalar formula for the standard disc automorphism. -/
@[norm_cast]
lemma coe_unitDiscStandardAutomorphismEquiv_apply (u : Circle) (a z : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a z : ℂ) =
      (u : ℂ) *
        (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ))) := by
  simp [unitDiscStandardAutomorphismEquiv]

/-- With zero center, the standard automorphism is just rotation. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_zero (u : Circle) :
    unitDiscStandardAutomorphismEquiv u 0 =
      (MulAction.toPerm u : Equiv.Perm Complex.UnitDisc) := by
  ext z
  simp [unitDiscStandardAutomorphismEquiv]

/-- With unit rotation factor, the standard automorphism is the Moebius equivalence. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_one (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv 1 a = unitDiscMoebiusEquiv a := by
  ext z
  simp [unitDiscStandardAutomorphismEquiv]

/-- The standard automorphism sends its center to zero. -/
lemma unitDiscStandardAutomorphismEquiv_self (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a a = 0 := by
  simp

/-- The standard automorphism sends zero to `-u * a`. -/
lemma unitDiscStandardAutomorphismEquiv_apply_zero (u : Circle) (a : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a 0 = u • (-a) := by
  simp [unitDiscStandardAutomorphismEquiv]

/-- The norm of a standard automorphism value is the pseudo-hyperbolic expression. -/
lemma norm_unitDiscStandardAutomorphismEquiv (u : Circle) (a z : Complex.UnitDisc) :
    ‖(unitDiscStandardAutomorphismEquiv u a z : ℂ)‖ = pseudoHyperbolicExpr (z : ℂ) (a : ℂ) := by
  rw [unitDiscStandardAutomorphismEquiv_apply, Complex.UnitDisc.coe_circle_smul, norm_mul,
    Circle.norm_coe, one_mul, norm_unitDiscMoebius]

/-- A standard disc automorphism vanishes exactly at its center. -/
lemma unitDiscStandardAutomorphismEquiv_eq_zero_iff (u : Circle) (a z : Complex.UnitDisc) :
    unitDiscStandardAutomorphismEquiv u a z = 0 ↔ z = a := by
  simp

/-- The scalar formula of a standard automorphism is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscStandardAutomorphismFormula_of_norm_lt_one
    (u : ℂ) {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        u * ((z - a) / (1 - (starRingEnd ℂ) a * z)))
      (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_const (c := u)).mul
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha)

/-- The scalar formula of the standard automorphism is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscStandardAutomorphismFormula (u : Circle) (a : Complex.UnitDisc) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        (u : ℂ) *
          ((z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z)))
      (Metric.ball (0 : ℂ) 1) :=
  differentiableOn_unitDiscStandardAutomorphismFormula_of_norm_lt_one (u : ℂ) a.norm_lt_one

/-- A standard disc-automorphism formula `w ↦ u * (w - c) / (1 - conj c * w)` that fixes three
distinct points at which its denominator does not vanish is the identity: `c = 0` and `u = 1`. -/
lemma eq_zero_and_eq_one_of_unitDiscStandardAutomorphismFormula_eq_self {u c w₁ w₂ w₃ : ℂ}
    (h₁₂ : w₁ ≠ w₂) (h₁₃ : w₁ ≠ w₃) (h₂₃ : w₂ ≠ w₃) (hd₁ : 1 - (starRingEnd ℂ) c * w₁ ≠ 0)
    (hd₂ : 1 - (starRingEnd ℂ) c * w₂ ≠ 0) (hd₃ : 1 - (starRingEnd ℂ) c * w₃ ≠ 0)
    (h₁ : u * ((w₁ - c) / (1 - (starRingEnd ℂ) c * w₁)) = w₁)
    (h₂ : u * ((w₂ - c) / (1 - (starRingEnd ℂ) c * w₂)) = w₂)
    (h₃ : u * ((w₃ - c) / (1 - (starRingEnd ℂ) c * w₃)) = w₃) :
    c = 0 ∧ u = 1 := by
  -- each fixed point is a root of the quadratic `conj c * w ^ 2 + (u - 1) * w - u * c`
  have e (w : ℂ) (hd : 1 - (starRingEnd ℂ) c * w ≠ 0)
      (h : u * ((w - c) / (1 - (starRingEnd ℂ) c * w)) = w) :
      (starRingEnd ℂ) c * w ^ 2 + (u - 1) * w - u * c = 0 := by
    rw [mul_div_assoc', div_eq_iff hd] at h
    linear_combination h
  have e₁ := e w₁ hd₁ h₁
  have e₂ := e w₂ hd₂ h₂
  have e₃ := e w₃ hd₃ h₃
  have a₁₂ : (starRingEnd ℂ) c * (w₁ + w₂) + (u - 1) = 0 :=
    (mul_eq_zero.mp (by linear_combination e₁ - e₂ :
      (w₁ - w₂) * ((starRingEnd ℂ) c * (w₁ + w₂) + (u - 1)) = 0)).resolve_left
        (sub_ne_zero.mpr h₁₂)
  have a₁₃ : (starRingEnd ℂ) c * (w₁ + w₃) + (u - 1) = 0 :=
    (mul_eq_zero.mp (by linear_combination e₁ - e₃ :
      (w₁ - w₃) * ((starRingEnd ℂ) c * (w₁ + w₃) + (u - 1)) = 0)).resolve_left
        (sub_ne_zero.mpr h₁₃)
  have hc : (starRingEnd ℂ) c = 0 :=
    (mul_eq_zero.mp (by linear_combination a₁₂ - a₁₃ :
      (w₂ - w₃) * (starRingEnd ℂ) c = 0)).resolve_left (sub_ne_zero.mpr h₂₃)
  exact ⟨(map_eq_zero _).mp hc, by linear_combination a₁₂ - (w₁ + w₂) * hc⟩

/-- The inverse of a standard automorphism as a composition of the inverse rotation and
the inverse Moebius factor. -/
@[simp]
lemma unitDiscStandardAutomorphismEquiv_symm (u : Circle) (a : Complex.UnitDisc) :
    (unitDiscStandardAutomorphismEquiv u a).symm =
      (MulAction.toPerm u⁻¹ : Equiv.Perm Complex.UnitDisc).trans (unitDiscMoebiusEquiv (-a)) :=
  by
    ext z
    simp [unitDiscStandardAutomorphismEquiv]

end TauCeti

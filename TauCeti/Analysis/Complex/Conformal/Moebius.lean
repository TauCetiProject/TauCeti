/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import TauCeti.Analysis.Complex.Conformal.PseudoHyperbolic

/-!
# Unit-disc Moebius factors

This file packages the standard Moebius factor
`z ↦ (z - a) / (1 - conj a * z)` as a bundled self-map of the complex unit disc.  It is
the elementary automorphism API used by the Schwarz--Pick and disc-automorphism layer of
the conformal-mapping roadmap: the map sends `a` to `0`, its norm is the
pseudo-hyperbolic expression from `z` to `a`, and the inverse is the factor with center
`-a`.

This L2 material is coordinated with the upstream Mathlib RMT effort in
leanprover-community/mathlib4#33505.  Mathlib already contains the preceding human-curated
work in `Analysis/Complex/RiemannMapping.lean` and `Analysis/Complex/BranchLogRoot.lean`;
this file only adds the small discoverable API around `Complex.UnitDisc`.
-/

public section

namespace TauCeti

open Complex Metric
open scoped ComplexConjugate

/-- The standard Moebius factor of the unit disc sending `a` to `0`. -/
noncomputable def unitDiscMoebius (a z : Complex.UnitDisc) : Complex.UnitDisc :=
  Complex.UnitDisc.mk
    (((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)))
    (by
      have h := pseudoHyperbolicExpr_lt_one_unitDisc z a
      rw [pseudoHyperbolicExpr_def] at h
      simpa using h)

/-- The defining formula for the unit-disc Moebius factor. -/
@[simp, norm_cast]
lemma coe_unitDiscMoebius (a z : Complex.UnitDisc) :
    (unitDiscMoebius a z : ℂ) =
      ((z : ℂ) - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ)) :=
  by simp [unitDiscMoebius]

/-- The unit-disc Moebius factor centered at zero is the identity. -/
@[simp]
lemma unitDiscMoebius_zero (z : Complex.UnitDisc) :
    unitDiscMoebius 0 z = z := by
  ext
  simp

/-- The unit-disc Moebius factor sends its center to zero. -/
@[simp]
lemma unitDiscMoebius_self (a : Complex.UnitDisc) :
    unitDiscMoebius a a = 0 := by
  ext
  simp

/-- The unit-disc Moebius factor sends zero to the negative of its center. -/
@[simp]
lemma unitDiscMoebius_apply_zero (a : Complex.UnitDisc) :
    unitDiscMoebius a 0 = -a := by
  ext
  simp

/-- The norm of the Moebius factor is the pseudo-hyperbolic expression. -/
@[simp]
lemma norm_unitDiscMoebius (a z : Complex.UnitDisc) :
    ‖(unitDiscMoebius a z : ℂ)‖ = pseudoHyperbolicExpr (z : ℂ) (a : ℂ) :=
  (pseudoHyperbolicExpr_def (z : ℂ) (a : ℂ)).symm

/-- A unit-disc Moebius factor vanishes exactly at its center. -/
@[simp]
lemma unitDiscMoebius_eq_zero_iff (a z : Complex.UnitDisc) :
    unitDiscMoebius a z = 0 ↔ z = a := by
  rw [← Complex.UnitDisc.coe_inj, Complex.UnitDisc.coe_zero, norm_eq_zero.symm,
    norm_unitDiscMoebius]
  exact pseudoHyperbolicExpr_eq_zero_iff_unitDisc z a

/-- The scalar Moebius formula with center of norm less than one is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ
      (fun z : ℂ => (z - a) / (1 - (starRingEnd ℂ) a * z))
      (ball (0 : ℂ) 1) := by
  intro z hz
  have hden :
      1 - (starRingEnd ℂ) a * z ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one
      (by simpa [mem_ball_zero_iff] using hz) ha
  have hnum :
      DifferentiableWithinAt ℂ (fun z : ℂ => z - a) (ball (0 : ℂ) 1) z :=
    differentiableWithinAt_id.sub (differentiableWithinAt_const (c := a))
  have hden_diff :
      DifferentiableWithinAt ℂ
        (fun z : ℂ => 1 - (starRingEnd ℂ) a * z) (ball (0 : ℂ) 1) z :=
    (differentiableWithinAt_const (c := (1 : ℂ))).sub
      ((differentiableWithinAt_const (c := (starRingEnd ℂ) a)).mul
        differentiableWithinAt_id)
  exact hnum.div hden_diff hden

/-- The scalar formula of the unit-disc Moebius factor is holomorphic on the unit disc. -/
lemma differentiableOn_unitDiscMoebiusFormula (a : Complex.UnitDisc) :
    DifferentiableOn ℂ
      (fun z : ℂ => (z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z))
      (ball (0 : ℂ) 1) :=
  differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one a.norm_lt_one

private lemma unitDiscMoebius_neg_apply_unitDiscMoebius_apply_scalar {a z : ℂ}
    (hden : 1 - (starRingEnd ℂ) a * z ≠ 0)
    (hnorm : 1 - (starRingEnd ℂ) a * a ≠ 0) :
    (((z - a) / (1 - (starRingEnd ℂ) a * z) + a) /
        (1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)))) = z := by
  have hden₂_eq :
      1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) =
        (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * z) := by
    field_simp [hden]
    ring
  have hden₂ :
      1 + (starRingEnd ℂ) a * ((z - a) / (1 - (starRingEnd ℂ) a * z)) ≠ 0 := by
    rw [hden₂_eq]
    exact div_ne_zero hnorm hden
  have hden_comm : 1 - z * (starRingEnd ℂ) a ≠ 0 := by
    simpa [mul_comm] using hden
  have hnorm_comm : 1 - a * (starRingEnd ℂ) a ≠ 0 := by
    simpa [mul_comm] using hnorm
  rw [hden₂_eq]
  field_simp [hden_comm, hnorm_comm]
  ring_nf

private lemma unitDiscMoebius_neg_apply_unitDiscMoebius_apply (a z : Complex.UnitDisc) :
    unitDiscMoebius (-a) (unitDiscMoebius a z) = z := by
  ext
  have hden₁ :
      1 - (starRingEnd ℂ) (a : ℂ) * (z : ℂ) ≠ 0 :=
    one_sub_conj_mul_ne_zero_unitDisc z a
  have hnorm :
      1 - (starRingEnd ℂ) (a : ℂ) * (a : ℂ) ≠ 0 :=
    one_sub_conj_mul_ne_zero_unitDisc a a
  simp only [coe_unitDiscMoebius, Complex.UnitDisc.coe_neg, map_neg]
  simpa [sub_neg_eq_add] using
    unitDiscMoebius_neg_apply_unitDiscMoebius_apply_scalar hden₁ hnorm

/-- The inverse of the unit-disc Moebius factor centered at `a` is the factor centered at `-a`. -/
@[simp]
lemma unitDiscMoebius_neg_comp_unitDiscMoebius (a : Complex.UnitDisc) :
    unitDiscMoebius (-a) ∘ unitDiscMoebius a = id := by
  funext z
  exact unitDiscMoebius_neg_apply_unitDiscMoebius_apply a z

/-- The unit-disc Moebius factors centered at `a` and `-a` compose in the other order too. -/
@[simp]
lemma unitDiscMoebius_comp_unitDiscMoebius_neg (a : Complex.UnitDisc) :
    unitDiscMoebius a ∘ unitDiscMoebius (-a) = id := by
  simpa using unitDiscMoebius_neg_comp_unitDiscMoebius (-a)

/-- The standard Moebius self-equivalence of the unit disc sending `a` to `0`. -/
noncomputable def unitDiscMoebiusEquiv (a : Complex.UnitDisc) :
    Complex.UnitDisc ≃ Complex.UnitDisc where
  toFun := unitDiscMoebius a
  invFun := unitDiscMoebius (-a)
  left_inv z := by
    exact congr_fun (unitDiscMoebius_neg_comp_unitDiscMoebius a) z
  right_inv z := by
    exact congr_fun (unitDiscMoebius_comp_unitDiscMoebius_neg a) z

/-- The equivalence applies by the unit-disc Moebius formula. -/
@[simp]
lemma unitDiscMoebiusEquiv_apply (a z : Complex.UnitDisc) :
    unitDiscMoebiusEquiv a z = unitDiscMoebius a z :=
  by simp [unitDiscMoebiusEquiv]

/-- The inverse equivalence is the Moebius equivalence centered at `-a`. -/
@[simp]
lemma unitDiscMoebiusEquiv_symm (a : Complex.UnitDisc) :
    (unitDiscMoebiusEquiv a).symm = unitDiscMoebiusEquiv (-a) :=
  Equiv.ext fun _ => rfl

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzPick
public import TauCeti.Analysis.Complex.Conformal.UnitDiscAutomorphism

/-!
# Disc automorphisms are pseudo-hyperbolic isometries

The Schwarz--Pick contraction estimate `pseudoHyperbolicExpr_map_le` says a holomorphic
self-map of the unit disc does not increase the pseudo-hyperbolic expression
`pseudoHyperbolicExpr z w = ‖(z - w) / (1 - conj w * z)‖`.  A holomorphic self-map that
additionally has a holomorphic self-map inverse must then *preserve* the expression: applying
the estimate to the map and to its inverse forces equality.  This file records that equality
and specializes it to the concrete disc automorphisms.

The results are:

* `pseudoHyperbolicExpr_const_mul` — rotation invariance, `‖c‖ = 1 ⇒
  pseudoHyperbolicExpr (c * z) (c * w) = pseudoHyperbolicExpr z w` (an algebraic identity,
  the rotation half of the automorphism group);
* `pseudoHyperbolicExpr_map_eq` — the Schwarz--Pick equality for any holomorphic self-map of
  the disc with a holomorphic self-map left inverse;
* `pseudoHyperbolicExpr_unitDiscMoebiusFormula` / `pseudoHyperbolicExpr_unitDiscMoebius` —
  the Moebius factor `z ↦ (z - a) / (1 - conj a * z)` is a pseudo-hyperbolic isometry, in
  scalar and bundled `Complex.UnitDisc` form;
* `pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv` — every standard disc automorphism
  `z ↦ u * (z - a) / (1 - conj a * z)` is a pseudo-hyperbolic isometry.

Together these say that the pseudo-hyperbolic expression is a conformal invariant: the disc
automorphism group `Aut(𝔻)` acts by isometries of the pseudo-hyperbolic (hence hyperbolic)
metric, the geometric content behind the Schwarz--Pick lemma.

This advances the conformal-mapping roadmap's L2 Schwarz--Pick / disc-automorphism target,
building directly on Tau Ceti's `pseudoHyperbolicExpr_map_le` (Mathlib's Schwarz lemma) and
the unit-disc Moebius / automorphism API.  As with the rest of the L0--L3 conformal-mapping
material, it is coordinated with the upstream Mathlib RMT effort
leanprover-community/mathlib4#33505 and should be refactored to upstream API if that work
lands a human-curated Schwarz--Pick theorem.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-- **Rotation invariance.** Multiplying both arguments by a unit-modulus constant leaves the
pseudo-hyperbolic expression unchanged.  This is the rotation half of the disc-automorphism
group; unlike the general isometry statement below it is a purely algebraic identity valid
for all `z`, `w`. -/
theorem pseudoHyperbolicExpr_const_mul {c : ℂ} (hc : ‖c‖ = 1) (z w : ℂ) :
    pseudoHyperbolicExpr (c * z) (c * w) = pseudoHyperbolicExpr z w := by
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  have hden : (starRingEnd ℂ) (c * w) * (c * z) = (starRingEnd ℂ) w * z := by
    rw [map_mul]
    calc (starRingEnd ℂ) c * (starRingEnd ℂ) w * (c * z)
        = ((starRingEnd ℂ) c * c) * ((starRingEnd ℂ) w * z) := by ring
      _ = (starRingEnd ℂ) w * z := by rw [hcc, one_mul]
  rw [pseudoHyperbolicExpr_def, pseudoHyperbolicExpr_def,
    show c * z - c * w = c * (z - w) by ring,
    show (1 : ℂ) - (starRingEnd ℂ) (c * w) * (c * z) = 1 - (starRingEnd ℂ) w * z by rw [hden],
    mul_div_assoc, norm_mul, hc, one_mul]

/-- **Schwarz--Pick equality.** A holomorphic self-map of the unit disc that admits a
holomorphic self-map left inverse preserves the pseudo-hyperbolic expression: the Schwarz--Pick
contraction, applied to the map and to its inverse, forces equality. -/
theorem pseudoHyperbolicExpr_map_eq {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1)) (hfmaps : MapsTo f (ball 0 1) (ball 0 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1)) (hgmaps : MapsTo g (ball 0 1) (ball 0 1))
    (hgf : LeftInvOn g f (ball 0 1))
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr (f z) (f w) = pseudoHyperbolicExpr z w := by
  refine le_antisymm (pseudoHyperbolicExpr_map_le hf hfmaps hz hw) ?_
  have h := pseudoHyperbolicExpr_map_le hg hgmaps (hfmaps hz) (hfmaps hw)
  rwa [hgf hz, hgf hw] at h

/-- **Moebius invariance (scalar form).** The Moebius factor `z ↦ (z - a) / (1 - conj a * z)`
with `‖a‖ < 1` is a pseudo-hyperbolic isometry of the open unit disc. -/
theorem pseudoHyperbolicExpr_unitDiscMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1)
    {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    pseudoHyperbolicExpr ((z - a) / (1 - (starRingEnd ℂ) a * z))
        ((w - a) / (1 - (starRingEnd ℂ) a * w))
      = pseudoHyperbolicExpr z w := by
  have ha' : ‖-a‖ < 1 := by rwa [norm_neg]
  refine pseudoHyperbolicExpr_map_eq
    (f := fun z => (z - a) / (1 - (starRingEnd ℂ) a * z))
    (g := fun z => (z - (-a)) / (1 - (starRingEnd ℂ) (-a) * z))
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha)
    (differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha')
    (mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha') ?_ hz hw
  intro ζ hζ
  have hζn : ‖ζ‖ < 1 := mem_ball_zero_iff.mp hζ
  have h := congrArg (fun u : Complex.UnitDisc => (u : ℂ))
    (congr_fun (unitDiscMoebius_neg_comp_unitDiscMoebius (Complex.UnitDisc.mk a ha))
      (Complex.UnitDisc.mk ζ hζn))
  simpa [coe_unitDiscMoebius, Complex.UnitDisc.coe_neg, Complex.UnitDisc.coe_mk, map_neg,
    neg_mul, sub_neg_eq_add] using h

/-- **Moebius invariance (bundled form).** The bundled unit-disc Moebius factor
`unitDiscMoebius a` preserves the pseudo-hyperbolic expression. -/
theorem pseudoHyperbolicExpr_unitDiscMoebius (a z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (unitDiscMoebius a z : ℂ) (unitDiscMoebius a w : ℂ)
      = pseudoHyperbolicExpr (z : ℂ) (w : ℂ) := by
  rw [coe_unitDiscMoebius, coe_unitDiscMoebius]
  exact pseudoHyperbolicExpr_unitDiscMoebiusFormula a.norm_lt_one z.property w.property

/-- **Automorphism invariance.** Every standard disc automorphism
`z ↦ u * (z - a) / (1 - conj a * z)` is a pseudo-hyperbolic isometry: the disc automorphism
group acts by isometries of the pseudo-hyperbolic metric. -/
theorem pseudoHyperbolicExpr_unitDiscStandardAutomorphismEquiv
    (u : Circle) (a z w : Complex.UnitDisc) :
    pseudoHyperbolicExpr (unitDiscStandardAutomorphismEquiv u a z : ℂ)
        (unitDiscStandardAutomorphismEquiv u a w : ℂ)
      = pseudoHyperbolicExpr (z : ℂ) (w : ℂ) := by
  rw [coe_unitDiscStandardAutomorphismEquiv_apply,
    coe_unitDiscStandardAutomorphismEquiv_apply,
    pseudoHyperbolicExpr_const_mul (Circle.norm_coe u)]
  exact pseudoHyperbolicExpr_unitDiscMoebiusFormula a.norm_lt_one z.property w.property

end TauCeti

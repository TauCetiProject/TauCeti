/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1

/-!
# The Gelfand radius of idempotents and of nonunital elements

The Gelfand radius `gelfandRadius a` of an element of a normed ring is the limit of
`‖a ^ k‖ ^ (1 / k)`. A nonzero idempotent has Gelfand radius one, whatever its norm, since all
of its positive powers coincide with it.

A nonunital algebra has no powers `a ^ 0`, so its Gelfand radius is computed in the ℓ¹
unitization `WithLp 1 (Unitization ℂ A)`, into which `A` embeds isometrically. Gelfand's formula
holds there: the spectral radius of `a`, the supremum of the moduli of its quasispectrum, is the
Gelfand radius of its image in the unitization. Together these give a lower bound on spectral
radii of elements of nonunital Banach algebras near a nonzero idempotent, which is how
idempotents obstruct the separating spaces of algebra homomorphisms.

## Main results

* `IsIdempotentElem.gelfandRadius_eq_one`: a nonzero idempotent has Gelfand radius one.
* `IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse`: a lower bound on the Gelfand radius
  of elements of the corner `p R p`.
* `TauCeti.spectralRadius_eq_gelfandRadius_toLp_inr`: Gelfand's formula for a nonunital complex
  Banach algebra, through its ℓ¹ unitization.
-/

public section

open Filter Topology

/-- A nonzero idempotent has Gelfand radius one: all its positive powers are equal to it, so
`‖p ^ k‖ ^ (1 / k) = ‖p‖ ^ (1 / k)` tends to one. No normalization of the norm is needed. -/
theorem IsIdempotentElem.gelfandRadius_eq_one {A : Type*} [NormedRing A] {p : A}
    (hp : IsIdempotentElem p) (h0 : p ≠ 0) : gelfandRadius p = 1 := by
  refine tendsto_nhds_unique (tendsto_gelfandRadius p) ?_
  have h : Tendsto (fun k : ℕ ↦ ‖p‖ ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
    ((Real.continuous_const_rpow (norm_ne_zero_iff.2 h0)).tendsto' 0 1
      (Real.rpow_zero _)).comp tendsto_inv_atTop_nhds_zero_nat
  refine h.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  rw [hp.pow_eq hk]

/-- Elements of the corner `p R p` of a nonzero idempotent `p` are bounded away from
quasinilpotence near `p`. If `p * y = y = y * p` and `1 - p + y` is a unit, then `y` is
`p * (1 - p + y)`, and the Gelfand radius of `y` is at least `‖(1 - p + y)⁻¹‖⁻¹`. As `y`
tends to `p`, this lower bound tends to `‖1‖⁻¹`. -/
theorem IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse {R : Type*} [NormedRing R]
    {p y : R} (hp : IsIdempotentElem p) (h0 : p ≠ 0) (hpy : p * y = y) (hyp : y * p = y)
    (hu : IsUnit (1 - p + y)) : 1 ≤ gelfandRadius y * ‖Ring.inverse (1 - p + y)‖ := by
  obtain ⟨w, hw⟩ := hu
  have hyw : y = p * w := by rw [hw, mul_add, mul_sub, mul_one, hp.eq, sub_self, zero_add, hpy]
  have hcomm : Commute y (w⁻¹ : Rˣ) := by
    refine Commute.units_inv_right ?_
    rw [hw]
    exact ((Commute.one_right y).sub_right (hpy.trans hyp.symm).symm).add_right (Commute.refl y)
  rw [← hw, Ring.inverse_unit, ← hp.gelfandRadius_eq_one h0]
  calc gelfandRadius p = gelfandRadius (y * (w⁻¹ : Rˣ)) := by
        rw [hyw, mul_assoc, w.mul_inv, mul_one]
    _ ≤ gelfandRadius y * gelfandRadius ((w⁻¹ : Rˣ) : R) := hcomm.gelfandRadius_mul_le
    _ ≤ gelfandRadius y * ‖((w⁻¹ : Rˣ) : R)‖ := by grw [gelfandRadius_le_norm ((w⁻¹ : Rˣ) : R)]

namespace TauCeti

variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

/-- **Gelfand's formula** in a nonunital complex Banach algebra: the spectral radius of `a`,
computed from its quasispectrum, is the Gelfand radius of its image in the ℓ¹ unitization. -/
theorem spectralRadius_eq_gelfandRadius_toLp_inr (a : A) :
    spectralRadius ℂ a = ENNReal.ofReal (gelfandRadius (WithLp.toLp 1 (a : Unitization ℂ A))) := by
  rw [← spectrum.spectralRadius_eq_gelfandRadius, spectralRadius_eq_of_unital,
    ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv (𝕜 := ℂ) (A := A) ℂ),
    WithLp.unitizationAlgEquiv_apply,
    WithLp.ofLp_toLp, ← Unitization.quasispectrum_eq_spectrum_inr, spectralRadius]

end TauCeti

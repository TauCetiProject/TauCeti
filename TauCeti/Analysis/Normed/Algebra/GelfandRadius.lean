/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm

import TauCeti.Analysis.Normed.Ring.Ultra

/-!
# The Gelfand radius of idempotents, nonunital elements, and ultrametric rings

The Gelfand radius `gelfandRadius a` of an element of a normed ring is the limit of
`‖a ^ k‖ ^ (1 / k)`. A nonzero idempotent has Gelfand radius one, whatever its norm, since all
of its positive powers coincide with it.

A nonunital algebra has no powers `a ^ 0`, so its Gelfand radius is computed in the ℓ¹
unitization `WithLp 1 (Unitization ℂ A)`, into which `A` embeds isometrically. Gelfand's formula
holds there: the spectral radius of `a`, the supremum of the moduli of its quasispectrum, is the
Gelfand radius of its image in the unitization. Together these give a lower bound on spectral
radii of elements of nonunital Banach algebras near a nonzero idempotent, which is how
idempotents obstruct the separating spaces of algebra homomorphisms.

In any seminormed commutative ring `A`, `gelfandRadius` agrees with Mathlib's smoothing seminorm
`smoothingFun (normRingSeminorm A)` and forms a power-multiplicative `RingSeminorm A`
(`TauCeti.gelfandRadiusRingSeminorm`) without requiring `‖(1 : A)‖ ≤ 1`. When `A` is ultrametric,
`gelfandRadius` is moreover nonarchimedean (`Commute.gelfandRadius_add_le_max`,
`TauCeti.isNonarchimedean_gelfandRadius`).

## Main results

* `IsIdempotentElem.gelfandRadius_eq_one`: a nonzero idempotent has Gelfand radius one.
* `IsIdempotentElem.one_le_gelfandRadius_mul_norm_inverse`: a lower bound on the Gelfand radius
  of elements of the corner `p R p`.
* `TauCeti.spectralRadius_eq_gelfandRadius_toLp_inr`: Gelfand's formula for a nonunital complex
  Banach algebra, through its ℓ¹ unitization.
* `Commute.gelfandRadius_add_le_max` and `TauCeti.isNonarchimedean_gelfandRadius`: ultrametric
  subadditivity of `gelfandRadius` without `‖1‖ ≤ 1`.
* `TauCeti.smoothingFun_normRingSeminorm_eq_gelfandRadius` and
  `TauCeti.gelfandRadiusRingSeminorm`: identification with `smoothingFun (normRingSeminorm A)` and
  `RingSeminorm` bundling.
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

/-- In an ultrametric seminormed ring, the Gelfand radius of a sum of commuting elements is at most
the maximum of their Gelfand radii. No normalization on `‖1‖` is needed. -/
theorem Commute.gelfandRadius_add_le_max {A : Type*} [SeminormedRing A] [IsUltrametricDist A]
    {a b : A} (h : Commute a b) :
    gelfandRadius (a + b) ≤ max (gelfandRadius a) (gelfandRadius b) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  have ha_lt : gelfandRadius a < r := (le_max_left _ _).trans_lt hr
  have hb_lt : gelfandRadius b < r := (le_max_right _ _).trans_lt hr
  have hr0 : 0 < r := (gelfandRadius_nonneg a).trans_lt ha_lt
  obtain ⟨Ca, hCa, ha⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt a ha_lt
  obtain ⟨Cb, hCb, hb⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt b hb_lt
  refine gelfandRadius_le_of_bound hr0.le (C := Ca * Cb * ‖(1 : A)‖) fun n ↦ ?_
  rw [h.add_pow]
  obtain ⟨k, hk, hle⟩ := IsUltrametricDist.isNonarchimedean_norm.finset_image_add_of_nonempty
    (fun k ↦ a ^ k * b ^ (n - k) * (n.choose k : A)) (Finset.nonempty_range_add_one)
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hnat : ‖(n.choose k : A)‖ ≤ ‖(1 : A)‖ := by
    simpa using IsUltrametricDist.norm_nsmul_le (1 : A) (n.choose k)
  calc
    ‖∑ m ∈ Finset.range (n + 1), a ^ m * b ^ (n - m) * (n.choose m : A)‖
        ≤ ‖a ^ k * b ^ (n - k) * (n.choose k : A)‖ := hle
    _ ≤ ‖a ^ k‖ * ‖b ^ (n - k)‖ * ‖(n.choose k : A)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖ := by
      gcongr
      · exact ha k
      · exact hb (n - k)
    _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by
      have hrpow : r ^ k * r ^ (n - k) = r ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]
      calc
        (Ca * r ^ k) * (Cb * r ^ (n - k)) * ‖(1 : A)‖
            = Ca * Cb * ‖(1 : A)‖ * (r ^ k * r ^ (n - k)) := by ring
        _ = Ca * Cb * ‖(1 : A)‖ * r ^ n := by rw [hrpow]

namespace TauCeti

section NonUnital

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

end NonUnital

/-- In any seminormed commutative ring, `smoothingFun (normRingSeminorm A)` agrees with Mathlib's
`gelfandRadius`, without requiring `‖(1 : A)‖ ≤ 1`. -/
theorem smoothingFun_normRingSeminorm_eq_gelfandRadius {A : Type*} [SeminormedCommRing A] (a : A) :
    smoothingFun (normRingSeminorm A) a = gelfandRadius a := by
  have hnorm (x : A) : normRingSeminorm A x = ‖x‖ := rfl
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto' (tendsto_gelfandRadius' a) fun k ↦ ?_
    have hk : smoothingFun (normRingSeminorm A) a ≤
        normRingSeminorm A (a ^ (k : ℕ)) ^ (1 / (k : ℝ)) :=
      ciInf_le (smoothingSeminormSeq_bddBelow (normRingSeminorm A) a) k
    rwa [hnorm, one_div] at hk
  · refine le_ciInf fun k ↦ ?_
    rw [hnorm, one_div]
    exact gelfandRadius_le_norm_pow a k.ne_zero

/-- `smoothingFun (normRingSeminorm A) a ≤ ‖a‖` in any seminormed commutative ring. -/
theorem smoothingFun_normRingSeminorm_le_norm {A : Type*} [SeminormedCommRing A] (a : A) :
    smoothingFun (normRingSeminorm A) a ≤ ‖a‖ := by
  rw [smoothingFun_normRingSeminorm_eq_gelfandRadius]
  exact gelfandRadius_le_norm a

/-- In an ultrametric seminormed commutative ring, `gelfandRadius` is nonarchimedean. -/
theorem isNonarchimedean_gelfandRadius {A : Type*} [SeminormedCommRing A] [IsUltrametricDist A] :
    IsNonarchimedean (gelfandRadius : A → ℝ) := fun a b ↦
  (Commute.all a b).gelfandRadius_add_le_max

/-- In any seminormed commutative ring, `gelfandRadius` bundled as a `RingSeminorm`, without
requiring `‖(1 : A)‖ ≤ 1`. -/
noncomputable def gelfandRadiusRingSeminorm (A : Type*) [SeminormedCommRing A] :
    RingSeminorm A where
  toFun := gelfandRadius
  map_zero' := gelfandRadius_zero
  add_le' := gelfandRadius_add_le
  neg' := gelfandRadius_neg
  mul_le' := gelfandRadius_mul_le

/-- `gelfandRadiusRingSeminorm A` evaluates to `gelfandRadius`. -/
@[simp]
theorem gelfandRadiusRingSeminorm_apply {A : Type*} [SeminormedCommRing A] (a : A) :
    gelfandRadiusRingSeminorm A a = gelfandRadius a := (rfl)

/-- `gelfandRadiusRingSeminorm A` is power-multiplicative. -/
theorem isPowMul_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A] :
    IsPowMul (gelfandRadiusRingSeminorm A) := fun a _n hn ↦
  gelfandRadius_pow_of_ne_zero a (Nat.one_le_iff_ne_zero.mp hn)

/-- In an ultrametric seminormed commutative ring, `gelfandRadiusRingSeminorm A` is
nonarchimedean. -/
theorem isNonarchimedean_gelfandRadiusRingSeminorm {A : Type*} [SeminormedCommRing A]
    [IsUltrametricDist A] : IsNonarchimedean (gelfandRadiusRingSeminorm A) :=
  isNonarchimedean_gelfandRadius

end TauCeti

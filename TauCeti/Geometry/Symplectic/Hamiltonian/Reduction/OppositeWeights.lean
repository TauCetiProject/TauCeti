/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.WeightModel.Basic

import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Singular reduction of `ℂ²` by the circle with weights `1` and `-1`

The circle acts on `ℂ²` with the weights `1` and `-1`,
`ξ • (z₀, z₁) = (e^{iξ} z₀, e^{-iξ} z₁)`, with moment map
`μ = -½ (|z₀|² - |z₁|²)`. In Tau Ceti's weight model these are `TauCeti.weightRotation` and
`TauCeti.weightMomentMap` for the weights `![id, -id]` on `ℝ`, in the real coordinates
`z_j = q_j + i p_j` of `EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)`. The value `0` is a
singular value of `μ`: the origin is a fixed point lying on the zero level. This file computes the
singular reduced space `μ⁻¹(0) / S¹` and its stratification.

The zero level is the cone `|z₀| = |z₁|`
(`TauCeti.weightMomentMap_id_neg_id_eq_zero_iff`). The product `w = z₀ z₁`
(`TauCeti.oppositeWeightInvariant`) is invariant under the action
(`TauCeti.oppositeWeightInvariant_weightRotation`), and on the zero level its fibres are exactly
the orbits (`TauCeti.exists_weightRotation_id_neg_id_apply_eq_iff`): if `z₀ z₁ = z₀' z₁'` with
`|z₀| = |z₁|` and `|z₀'| = |z₁'|`, then `|z₀'| = |z₀|`, and the rotation by the argument `ξ` of
`z₀' / z₀` carries `(z₀, z₁)` to `(z₀', z₁')`. Every `w ∈ ℂ` is reached, by `z₀ = z₁ = √w`. On the
level `|w| = |z₀|²`, so the restriction of `w` to the level is a proper map, hence closed, hence a
quotient map (`TauCeti.isQuotientMap_oppositeWeightInvariant_comp_val`). So **the reduced space is
the plane**:

`μ⁻¹(0) / S¹ ≃ₜ ℂ`, `[z₀, z₁] ↦ z₀ z₁` (`TauCeti.oppositeWeightReducedHomeomorph`).

The orbit types stratify it into two pieces. The origin is the only fixed point
(`TauCeti.forall_weightRotation_id_neg_id_apply_eq_self_iff`), and away from it the action is free
(`TauCeti.weightRotation_id_neg_id_apply_eq_self_iff`). Its orbit is the only one mapped to
`0 ∈ ℂ` (`TauCeti.oppositeWeightReducedHomeomorph_eq_zero_iff`), so the strata are the point
`{0}`, coming from the fixed point with its quadratic weight model, and `ℂ ∖ {0}`, the free orbits.

On the free stratum the reduced symplectic form is computed pointwise. Let `x ≠ 0` lie on the zero
level and let `v`, `w` be tangent to the level at `x`, that is in the kernel of `dμ_x`
(`TauCeti.fderiv_weightMomentMap_id_neg_id_apply_eq_zero_iff`). Then

`ω(v, w) = Im (conj (dΦ v) dΦ w) / (2 |Φ x|)`

(`TauCeti.stdSymplecticForm_eq_div_of_fderiv_weightMomentMap_id_neg_id_eq_zero`), where `Φ` is the
invariant `z₀ z₁` and `Im (conj c d) = dx ∧ dy (c, d)` is the area form of the plane. So the reduced
form on `ℂ ∖ {0}` is `dx ∧ dy / (2 |w|)`. As `dΦ_x` maps the tangent space of the level onto `ℂ`
(`TauCeti.exists_fderiv_weightMomentMap_id_neg_id_eq_zero_and_fderiv_eq`), this is the only
form on `T_w ℂ` whose pullback is the restriction of `ω`
(`TauCeti.forall_stdSymplecticForm_eq_iff_of_weightMomentMap_id_neg_id`). Its density
`1 / (2 |w|)` is unbounded near the singular stratum `{0}`. The proof writes `v₀ = z₀ p` and
`v₁ = z₁ q`: tangency to the level says `Re p = Re q`, and both sides equal
`|z₀|² Im (conj p p' + conj q q')`.

For the weights `1` and `1` the zero level is the origin alone
(`TauCeti.weightMomentMap_id_id_eq_zero_iff`), so the reduced space at `0` is a point.

## Main definitions

* `TauCeti.oppositeWeightInvariant x`: the invariant `z₀ z₁`.
* `TauCeti.oppositeWeightOrbitSetoid`: the orbit relation of the action on the zero level.
* `TauCeti.oppositeWeightReducedHomeomorph`: the homeomorphism `μ⁻¹(0) / S¹ ≃ₜ ℂ`.

## Main results

* `TauCeti.weightMomentMap_id_neg_id_eq_zero_iff`: the zero level is the cone `|z₀| = |z₁|`.
* `TauCeti.exists_weightRotation_id_neg_id_apply_eq_iff`: on the zero level, two points lie in one
  orbit exactly when they have the same invariant.
* `TauCeti.isQuotientMap_oppositeWeightInvariant_comp_val`: the invariant is a quotient map from
  the zero level onto `ℂ`.
* `TauCeti.oppositeWeightReducedHomeomorph_eq_zero_iff`: the singular stratum is the orbit of the
  origin.
* `TauCeti.stdSymplecticForm_eq_div_of_fderiv_weightMomentMap_id_neg_id_eq_zero`,
  `TauCeti.forall_stdSymplecticForm_eq_iff_of_weightMomentMap_id_neg_id`: the reduced form on the
  free stratum is `dx ∧ dy / (2 |w|)`.

## References

* L. Bates and E. Lerman, *Proper group actions and symplectic stratified spaces*, Pacific Journal
  of Mathematics 181 (1997), 201–229, Section 3 (singular reduction and its strata).
* R. Sjamaar and E. Lerman, *Stratified symplectic spaces and reduction*, Annals of Mathematics 134
  (1991), 375–422 (the orbit-type stratification of a singular reduced space).
-/

public section

noncomputable section

namespace TauCeti

open Real ComplexConjugate

/-! ### The moment map and its zero level -/

/-- **The zero level is a cone.** For the weights `1` and `-1`, the zero level of the moment map
is the cone `|z₀| = |z₁|`. -/
theorem weightMomentMap_id_neg_id_eq_zero_iff
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} :
    weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0 ↔
      x.1 0 ^ 2 + x.2 0 ^ 2 = x.1 1 ^ 2 + x.2 1 ^ 2 := by
  rw [ContinuousLinearMap.ext_ring_iff, weightMomentMap_id_neg_id_apply,
    zero_apply]
  constructor <;> intro h <;> linarith

/-- Tangency to the zero level. The differential of the moment map at `x` vanishes on `v` exactly
when `Re (conj z₀ v₀) = Re (conj z₁ v₁)`. -/
theorem fderiv_weightMomentMap_id_neg_id_apply_eq_zero_iff
    (x v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ]) x v = 0 ↔
      x.1 0 * v.1 0 + x.2 0 * v.2 0 = x.1 1 * v.1 1 + x.2 1 * v.2 1 := by
  rw [(hasFDerivAt_weightMomentMap _ x).fderiv, ContinuousLinearMap.ext_ring_iff]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    add_apply, ContinuousLinearMap.smulRight_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd', PiLp.proj_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst', smul_neg, ContinuousLinearMap.id_apply, mul_one, neg_neg,
    zero_apply]
  constructor <;> intro h <;> linarith

/-! ### The invariant `z₀ z₁` -/

/-- The invariant `w = z₀ z₁` of the circle action on `ℂ²` with the weights `1` and `-1`, in the
real coordinates `z_j = q_j + i p_j`. -/
def oppositeWeightInvariant (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (complexEuclideanEquivRealProd (Fin 2)).symm x 0 *
    (complexEuclideanEquivRealProd (Fin 2)).symm x 1

/-- The invariant `z₀ z₁` in the real coordinates `z_j = q_j + i p_j`. -/
theorem oppositeWeightInvariant_def (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    oppositeWeightInvariant x =
      (x.1 0 + x.2 0 * Complex.I) * (x.1 1 + x.2 1 * Complex.I) := by
  simp only [oppositeWeightInvariant, complexEuclideanEquivRealProd_symm_apply]

/-- In the complex coordinates, the rotation by `ξ` multiplies `z₀` by `cos ξ + i sin ξ`. -/
private theorem symm_weightRotation_id_neg_id_apply_zero (ξ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    (complexEuclideanEquivRealProd (Fin 2)).symm (weightRotation
      (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x) 0 =
      (cos ξ + sin ξ * Complex.I) * (complexEuclideanEquivRealProd (Fin 2)).symm x 0 := by
  rw [complexEuclideanEquivRealProd_symm_weightRotation_apply]
  simp

/-- In the complex coordinates, the rotation by `ξ` multiplies `z₁` by `cos ξ - i sin ξ`. -/
private theorem symm_weightRotation_id_neg_id_apply_one (ξ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    (complexEuclideanEquivRealProd (Fin 2)).symm (weightRotation
      (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x) 1 =
      (cos ξ - sin ξ * Complex.I) * (complexEuclideanEquivRealProd (Fin 2)).symm x 1 := by
  rw [complexEuclideanEquivRealProd_symm_weightRotation_apply]
  simp [sub_eq_add_neg]

/-- The invariant is unchanged by the action: `(e^{iξ} z₀)(e^{-iξ} z₁) = z₀ z₁`. -/
@[simp]
theorem oppositeWeightInvariant_weightRotation (ξ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    oppositeWeightInvariant (weightRotation
      (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x) =
      oppositeWeightInvariant x := by
  rw [oppositeWeightInvariant, symm_weightRotation_id_neg_id_apply_zero,
    symm_weightRotation_id_neg_id_apply_one, oppositeWeightInvariant]
  -- The two rotation factors `e^{iξ}` and `e^{-iξ}` multiply to `cos² ξ + sin² ξ = 1`.
  have h : (cos ξ : ℂ) ^ 2 + (sin ξ : ℂ) ^ 2 = 1 := by exact_mod_cast cos_sq_add_sin_sq ξ
  linear_combination ((complexEuclideanEquivRealProd (Fin 2)).symm x 0 *
    (complexEuclideanEquivRealProd (Fin 2)).symm x 1) * (h - (sin ξ : ℂ) ^ 2 * Complex.I_sq)

/-- A point is the origin exactly when its four real coordinates vanish. -/
private theorem eq_zero_iff_coords {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} :
    x = 0 ↔ x.1 0 = 0 ∧ x.2 0 = 0 ∧ x.1 1 = 0 ∧ x.2 1 = 0 := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  ext i <;> fin_cases i <;> simp [h]

/-- A point is determined by its two complex coordinates. -/
private theorem eq_iff_symm_apply_eq {x y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} :
    x = y ↔ (complexEuclideanEquivRealProd (Fin 2)).symm x 0 =
        (complexEuclideanEquivRealProd (Fin 2)).symm y 0 ∧
      (complexEuclideanEquivRealProd (Fin 2)).symm x 1 =
        (complexEuclideanEquivRealProd (Fin 2)).symm y 1 := by
  refine ⟨fun h ↦ h ▸ ⟨rfl, rfl⟩, fun ⟨h0, h1⟩ ↦
    (complexEuclideanEquivRealProd (Fin 2)).symm.injective ?_⟩
  ext j
  fin_cases j
  exacts [h0, h1]

/-- On the zero level, the two complex coordinates have the same squared modulus
`|z₀|² = |z₁|²`. -/
private theorem normSq_symm_zero_eq_normSq_symm_one
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0) :
    Complex.normSq ((complexEuclideanEquivRealProd (Fin 2)).symm x 0) =
      Complex.normSq ((complexEuclideanEquivRealProd (Fin 2)).symm x 1) := by
  simp only [complexEuclideanEquivRealProd_symm_apply, Complex.normSq_add_mul_I]
  exact weightMomentMap_id_neg_id_eq_zero_iff.1 hx

/-- On the zero level, the modulus of the invariant `z₀ z₁` is `|z₀|² = |z₁|²`. -/
theorem norm_oppositeWeightInvariant {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0) :
    ‖oppositeWeightInvariant x‖ = x.1 0 ^ 2 + x.2 0 ^ 2 := by
  rw [oppositeWeightInvariant, Complex.norm_mul, Complex.norm_def, Complex.norm_def,
    ← normSq_symm_zero_eq_normSq_symm_one hx, Real.mul_self_sqrt (Complex.normSq_nonneg _),
    complexEuclideanEquivRealProd_symm_apply, Complex.normSq_add_mul_I]

/-- On the zero level, the invariant vanishes only at the origin. -/
theorem oppositeWeightInvariant_eq_zero_iff
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0) :
    oppositeWeightInvariant x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_oppositeWeightInvariant hx]
  rw [weightMomentMap_id_neg_id_eq_zero_iff] at hx
  rw [eq_zero_iff_coords]
  refine ⟨fun h ↦ ?_, fun ⟨h0, h1, _, _⟩ ↦ by simp [h0, h1]⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (x.1 0), sq_nonneg (x.2 0),
    sq_nonneg (x.1 1), sq_nonneg (x.2 1)]

/-- Away from the origin, the invariant of a point of the zero level is nonzero. -/
theorem oppositeWeightInvariant_ne_zero {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0)
    (hx0 : x ≠ 0) : oppositeWeightInvariant x ≠ 0 :=
  mt (oppositeWeightInvariant_eq_zero_iff hx).1 hx0

/-! ### Orbits on the zero level -/

/-- The complex arithmetic behind the orbits of the zero level: if `a b = a' b' ≠ 0` with
`|a| = |b|` and `|a'| = |b'|`, then `a' = e^{iξ} a` and `b' = e^{-iξ} b` for the argument `ξ` of
`a' / a`. -/
private theorem exists_rotation_of_mul_eq {a b a' b' : ℂ} (hab : a * b = a' * b')
    (hxab : Complex.normSq a = Complex.normSq b) (hyab : Complex.normSq a' = Complex.normSq b')
    (hΦ : a * b ≠ 0) :
    ∃ ξ : ℝ, (cos ξ + sin ξ * Complex.I) * a = a' ∧ (cos ξ - sin ξ * Complex.I) * b = b' := by
  have ha : a ≠ 0 := left_ne_zero_of_mul hΦ
  have ha' : a' ≠ 0 := left_ne_zero_of_mul (hab ▸ hΦ)
  -- The first coordinates have the same modulus, since `|a|² = |a b| = |a' b'| = |a'|²`.
  have hnorm : Complex.normSq a' = Complex.normSq a := by
    have h2 := congrArg Complex.normSq hab
    rw [map_mul, map_mul, ← hxab, ← hyab] at h2
    nlinarith [Complex.normSq_nonneg a, Complex.normSq_nonneg a']
  -- The unit `u = a' / a` is `cos ξ + i sin ξ` for its argument `ξ`.
  obtain ⟨u, hu_def⟩ : ∃ u, u = a' / a := ⟨_, rfl⟩
  have hu : Complex.normSq u = 1 := by
    rw [hu_def, map_div₀, hnorm, div_self (Complex.normSq_pos.2 ha).ne']
  have hnu : ‖u‖ = 1 := by rw [Complex.norm_def, hu, Real.sqrt_one]
  have hcos : (cos (Complex.arg u) : ℂ) + sin (Complex.arg u) * Complex.I = u := by
    simpa [hnu] using Complex.norm_mul_cos_add_sin_mul_I u
  -- Its inverse is its conjugate `cos ξ - i sin ξ`.
  have hcos' : (cos (Complex.arg u) : ℂ) - sin (Complex.arg u) * Complex.I = u⁻¹ := by
    rw [Complex.inv_eq_conj hnu, ← congrArg conj hcos]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  refine ⟨Complex.arg u, ?_, ?_⟩
  · rw [hcos, hu_def, div_mul_cancel₀ _ ha]
  · rw [hcos', hu_def, inv_div, div_mul_eq_mul_div, hab, mul_div_cancel_left₀ _ ha']

/-- **The orbits on the zero level are the fibres of the invariant.** Two points of the cone
`|z₀| = |z₁|` lie in one orbit of the circle action with the weights `1` and `-1` exactly when
they have the same product `z₀ z₁`. -/
theorem exists_weightRotation_id_neg_id_apply_eq_iff
    {x y : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0)
    (hy : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] y = 0) :
    (∃ ξ : ℝ, weightRotation
        (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x = y) ↔
      oppositeWeightInvariant x = oppositeWeightInvariant y := by
  refine ⟨fun ⟨ξ, h⟩ ↦ h ▸ (oppositeWeightInvariant_weightRotation ξ x).symm, fun h ↦ ?_⟩
  by_cases hx0 : x = 0
  · -- Over `0` the fibre is the fixed point.
    have hy0 : y = 0 := (oppositeWeightInvariant_eq_zero_iff hy).1
      (h ▸ (oppositeWeightInvariant_eq_zero_iff hx).2 hx0)
    exact ⟨0, by rw [weightRotation_map_zero_apply, hx0, hy0]⟩
  obtain ⟨ξ, h0, h1⟩ := exists_rotation_of_mul_eq h (normSq_symm_zero_eq_normSq_symm_one hx)
    (normSq_symm_zero_eq_normSq_symm_one hy) (oppositeWeightInvariant_ne_zero hx hx0)
  exact ⟨ξ, eq_iff_symm_apply_eq.2 ⟨by rw [symm_weightRotation_id_neg_id_apply_zero, h0],
    by rw [symm_weightRotation_id_neg_id_apply_one, h1]⟩⟩

/-- **Every point of the plane is reached.** Every `w ∈ ℂ` is the invariant `z₀ z₁` of a point of
the zero level, for instance of `z₀ = z₁ = √w`. -/
theorem exists_weightMomentMap_id_neg_id_eq_zero_and_oppositeWeightInvariant_eq (w : ℂ) :
    ∃ x, weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0 ∧
      oppositeWeightInvariant x = w := by
  refine ⟨complexEuclideanEquivRealProd (Fin 2)
    (WithLp.toLp 2 ![w ^ ((2 : ℕ) : ℂ)⁻¹, w ^ ((2 : ℕ) : ℂ)⁻¹]), ?_, ?_⟩
  · rw [weightMomentMap_id_neg_id_eq_zero_iff]
    simp
  · simpa [oppositeWeightInvariant, sq] using Complex.cpow_nat_inv_pow w two_ne_zero

/-- **The origin is the only fixed point.** -/
theorem forall_weightRotation_id_neg_id_apply_eq_self_iff
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} :
    (∀ ξ : ℝ, weightRotation
        (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x = x) ↔
      x = 0 := by
  rw [forall_weightRotation_apply_eq_self_iff]
  refine ⟨fun h ↦ ?_, fun h j _ ↦ by simp [h]⟩
  have hid : ContinuousLinearMap.id ℝ ℝ ≠ 0 := fun h ↦ one_ne_zero (congrArg (· 1) h)
  have h0 := h 0 hid
  have h1 := h 1 (neg_ne_zero.2 hid)
  exact eq_zero_iff_coords.2 ⟨h0.1, h0.2, h1.1, h1.2⟩

/-- **The action is free away from the origin.** At a point `x ≠ 0`, the rotation by `ξ` fixes `x`
exactly when `ξ ∈ 2πℤ`, that is when it is the identity element of the circle. -/
theorem weightRotation_id_neg_id_apply_eq_self_iff
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) (ξ : ℝ) :
    weightRotation (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x = x ↔
      ∃ k : ℤ, k * (2 * π) = ξ := by
  rw [weightRotation_apply_eq_self_iff, Fin.forall_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ContinuousLinearMap.id_apply, neg_apply]
  have hx' : (x.1 0 ≠ 0 ∨ x.2 0 ≠ 0) ∨ (x.1 1 ≠ 0 ∨ x.2 1 ≠ 0) := by
    rw [Ne, eq_zero_iff_coords] at hx
    tauto
  refine ⟨fun ⟨h0, h1⟩ ↦ hx'.elim h0 fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨fun _ ↦ ⟨k, hk⟩, fun _ ↦
    ⟨-k, by push_cast; linear_combination -hk⟩⟩⟩
  obtain ⟨k, hk⟩ := h1 h
  exact ⟨-k, by push_cast; linear_combination -hk⟩

/-! ### The derivative of the invariant -/

/-- The invariant `z₀ z₁` has derivative `z₀ dz₁ + z₁ dz₀`, by the product rule for the two
coordinate projections `dz_j : v ↦ v_j`. -/
theorem hasFDerivAt_oppositeWeightInvariant
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    HasFDerivAt oppositeWeightInvariant
      ((complexEuclideanEquivRealProd (Fin 2)).symm x 0 •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) 1).comp
            (complexEuclideanEquivRealProd (Fin 2)).symm.toContinuousLinearMap +
        (complexEuclideanEquivRealProd (Fin 2)).symm x 1 •
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) 0).comp
            (complexEuclideanEquivRealProd (Fin 2)).symm.toContinuousLinearMap) x := by
  -- `Φ` is the product of the two coordinate projections `x ↦ z₀` and `x ↦ z₁`.
  convert ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) 0).comp
      (complexEuclideanEquivRealProd (Fin 2)).symm.toContinuousLinearMap).hasFDerivAt.fun_mul
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℂ) 1).comp
      (complexEuclideanEquivRealProd (Fin 2)).symm.toContinuousLinearMap).hasFDerivAt using 1
  · funext y
    simp [oppositeWeightInvariant]
  · simp

/-- The invariant `z₀ z₁` is differentiable. -/
@[fun_prop]
theorem differentiable_oppositeWeightInvariant : Differentiable ℝ oppositeWeightInvariant :=
  fun x ↦ (hasFDerivAt_oppositeWeightInvariant x).differentiableAt

/-- The invariant `z₀ z₁` is continuous. -/
@[fun_prop]
theorem continuous_oppositeWeightInvariant : Continuous oppositeWeightInvariant :=
  differentiable_oppositeWeightInvariant.continuous

/-- The derivative of the invariant `z₀ z₁` in the direction `v` is `v₀ z₁ + z₀ v₁`. -/
theorem fderiv_oppositeWeightInvariant_apply
    (x v : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ oppositeWeightInvariant x v =
      (complexEuclideanEquivRealProd (Fin 2)).symm v 0 *
          (complexEuclideanEquivRealProd (Fin 2)).symm x 1 +
        (complexEuclideanEquivRealProd (Fin 2)).symm x 0 *
          (complexEuclideanEquivRealProd (Fin 2)).symm v 1 := by
  rw [(hasFDerivAt_oppositeWeightInvariant x).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply, smul_eq_mul,
    ContinuousLinearEquiv.coe_coe]
  ring

/-- The derivative of the invariant kills the generator of the action: the orbit directions are
in its kernel. -/
theorem fderiv_oppositeWeightInvariant_weightGenerator (ξ : ℝ)
    (x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :
    fderiv ℝ oppositeWeightInvariant x
      (weightGenerator (fun j ↦ ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] j ξ) x) =
      0 := by
  rw [fderiv_oppositeWeightInvariant_apply]
  apply Complex.ext <;> simp <;> ring

/-! ### The reduced space -/

/-- The orbit relation of the circle action with the weights `1` and `-1` on the zero level of its
moment map: two points are related when a rotation carries one to the other
(`TauCeti.weightOrbitSetoid_apply`). -/
abbrev oppositeWeightOrbitSetoid :
    Setoid {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
      weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0} :=
  weightOrbitSetoid ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] 0

/-- Two points of the zero level are in one orbit exactly when they have the same invariant
`z₀ z₁`. -/
theorem oppositeWeightOrbitSetoid_rel_iff
    {x y : {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
      weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0}} :
    oppositeWeightOrbitSetoid x y ↔ oppositeWeightInvariant x.val = oppositeWeightInvariant y.val :=
  weightOrbitSetoid_apply.trans (exists_weightRotation_id_neg_id_apply_eq_iff x.property y.property)

/-- **The invariant is a quotient map on the zero level.** The restriction of `z₀ z₁` to the cone
`|z₀| = |z₁|` is onto `ℂ`, and proper since `|z₀ z₁| = |z₀|² = |z₁|²` there, hence closed. So `ℂ`
carries the quotient topology of the zero level. -/
theorem isQuotientMap_oppositeWeightInvariant_comp_val :
    Topology.IsQuotientMap (fun x : {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
      weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0} ↦
        oppositeWeightInvariant x.val) := by
  have hc : Continuous (fun x : {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
      weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0} ↦
        oppositeWeightInvariant x.val) := by fun_prop
  refine IsClosedMap.isQuotientMap (isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK ↦ ?_⟩
    |>.isClosedMap) hc fun w ↦ ?_
  · -- The preimage of `K` in the level is closed and bounded in `ℂ²`.
    refine Subtype.isCompact_iff.2 ?_
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    refine Metric.isCompact_of_isClosed_isBounded ?_ (isBounded_iff_forall_norm_le.2
      ⟨√(2 * R), ?_⟩)
    · rw [show Subtype.val '' ((fun x : {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
          weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0} ↦
            oppositeWeightInvariant x.val) ⁻¹' K) =
          weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] ⁻¹' {0} ∩
            oppositeWeightInvariant ⁻¹' K by ext; simp [and_comm]]
      exact ((isClosed_singleton.preimage (continuous_weightMomentMap _)).inter
        (hK.isClosed.preimage continuous_oppositeWeightInvariant))
    · rintro _ ⟨x, hx, rfl⟩
      have hRx := hR _ hx
      rw [norm_oppositeWeightInvariant x.property] at hRx
      have hlevel := weightMomentMap_id_neg_id_eq_zero_iff.1 x.property
      have hn (y : EuclideanSpace ℝ (Fin 2)) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
        simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      rw [Prod.norm_def, max_le_iff]
      constructor <;> refine Real.le_sqrt_of_sq_le ?_ <;> rw [hn] <;>
        nlinarith [sq_nonneg (x.val.1 0), sq_nonneg (x.val.1 1), sq_nonneg (x.val.2 0),
          sq_nonneg (x.val.2 1)]
  · obtain ⟨x, hx, rfl⟩ :=
      exists_weightMomentMap_id_neg_id_eq_zero_and_oppositeWeightInvariant_eq w
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The map `[z₀, z₁] ↦ z₀ z₁` from the orbits of the zero level to `ℂ`. -/
private def oppositeWeightReducedMap : Quotient oppositeWeightOrbitSetoid → ℂ :=
  Quotient.lift (fun x ↦ oppositeWeightInvariant x.val)
    fun _ _ h ↦ oppositeWeightOrbitSetoid_rel_iff.1 h

private theorem isHomeomorph_oppositeWeightReducedMap :
    IsHomeomorph oppositeWeightReducedMap :=
  isHomeomorph_iff_isQuotientMap_injective.2
    ⟨Topology.IsQuotientMap.of_comp continuous_quot_mk
      (continuous_quot_lift _ isQuotientMap_oppositeWeightInvariant_comp_val.continuous)
      isQuotientMap_oppositeWeightInvariant_comp_val,
    fun p q ↦ Quotient.inductionOn₂ p q fun _ _ h ↦
      Quotient.sound (oppositeWeightOrbitSetoid_rel_iff.2 h)⟩

/-- **The singular reduced space is the plane.** For the circle action on `ℂ²` with the weights `1`
and `-1`, the reduced space `μ⁻¹(0) / S¹` at the singular value `0` is homeomorphic to `ℂ`, by
`[z₀, z₁] ↦ z₀ z₁`. -/
def oppositeWeightReducedHomeomorph : Quotient oppositeWeightOrbitSetoid ≃ₜ ℂ :=
  isHomeomorph_oppositeWeightReducedMap.homeomorph

@[simp]
theorem oppositeWeightReducedHomeomorph_mk
    (x : {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) //
      weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0}) :
    oppositeWeightReducedHomeomorph (Quotient.mk _ x) = oppositeWeightInvariant x.val := by
  simp [oppositeWeightReducedHomeomorph, IsHomeomorph.homeomorph_apply, oppositeWeightReducedMap]

/-- **The singular stratum.** The only orbit of the zero level mapped to `0 ∈ ℂ` is the fixed
point `0`. -/
theorem oppositeWeightReducedHomeomorph_eq_zero_iff (q : Quotient oppositeWeightOrbitSetoid) :
    oppositeWeightReducedHomeomorph q = 0 ↔
      q = Quotient.mk _ ⟨0, weightMomentMap_zero _⟩ := by
  rw [← oppositeWeightReducedHomeomorph.injective.eq_iff, oppositeWeightReducedHomeomorph_mk]
  simp [oppositeWeightInvariant_def]

/-! ### The reduced form on the free stratum -/

/-- **The reduced symplectic form on the free stratum.** At a point `x ≠ 0` of the zero level,
for tangent vectors `v`, `w` of the level, the standard symplectic form is the pullback of
`dx ∧ dy / (2 |w|)` along the invariant `Φ = z₀ z₁`:
`ω(v, w) = Im (conj (dΦ v) dΦ w) / (2 |Φ x|)`. -/
theorem stdSymplecticForm_eq_div_of_fderiv_weightMomentMap_id_neg_id_eq_zero
    {x v w : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0)
    (hx0 : x ≠ 0)
    (hv : fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ])
      x v = 0)
    (hw : fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ])
      x w = 0) :
    stdSymplecticForm v w =
      (conj (fderiv ℝ oppositeWeightInvariant x v) * fderiv ℝ oppositeWeightInvariant x w).im /
        (2 * ‖oppositeWeightInvariant x‖) := by
  have hΦ := oppositeWeightInvariant_ne_zero hx hx0
  rw [eq_div_iff (by positivity), norm_oppositeWeightInvariant hx,
    fderiv_oppositeWeightInvariant_apply, fderiv_oppositeWeightInvariant_apply]
  rw [fderiv_weightMomentMap_id_neg_id_apply_eq_zero_iff] at hv hw
  have hL := weightMomentMap_id_neg_id_eq_zero_iff.1 hx
  simp only [stdSymplecticForm_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_two, complexEuclideanEquivRealProd_symm_apply, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, map_add, map_mul]
  -- Writing `v₀ = z₀ p`, `v₁ = z₁ q`, tangency says `Re p = Re q`, and both sides reduce to
  -- `|z₀|² Im (conj p p' + conj q q')`; the defect is a combination of the three constraints.
  linear_combination
    ((x.1 0 * w.2 0 - x.2 0 * w.1 0) - (x.1 1 * w.2 1 - x.2 1 * w.1 1)) * hv -
      ((x.1 0 * v.2 0 - x.2 0 * v.1 0) - (x.1 1 * v.2 1 - x.2 1 * v.1 1)) * hw +
      (v.1 0 * w.2 0 - v.2 0 * w.1 0 + v.1 1 * w.2 1 - v.2 1 * w.1 1) * hL

/-- At a point `x ≠ 0` of the zero level, the differential of the invariant `Φ = z₀ z₁` maps the
tangent space of the level onto `ℂ`: the vector `(z₀ p, z₁ p)` with `p = c / (2 z₀ z₁)` is tangent
and is sent to `c`. -/
theorem exists_fderiv_weightMomentMap_id_neg_id_eq_zero_and_fderiv_eq
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0)
    (hx0 : x ≠ 0) (c : ℂ) :
    ∃ v, fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ])
        x v = 0 ∧ fderiv ℝ oppositeWeightInvariant x v = c := by
  have hΦ := oppositeWeightInvariant_ne_zero hx hx0
  obtain ⟨a, ha⟩ : ∃ a, (complexEuclideanEquivRealProd (Fin 2)).symm x 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, (complexEuclideanEquivRealProd (Fin 2)).symm x 1 = b := ⟨_, rfl⟩
  have hab : a * b ≠ 0 := by rw [← ha, ← hb]; exact hΦ
  obtain ⟨p, hp⟩ : ∃ p, c / (2 * (a * b)) = p := ⟨_, rfl⟩
  refine ⟨complexEuclideanEquivRealProd (Fin 2) (WithLp.toLp 2 ![a * p, b * p]), ?_, ?_⟩
  · rw [fderiv_weightMomentMap_id_neg_id_apply_eq_zero_iff]
    have hL := weightMomentMap_id_neg_id_eq_zero_iff.1 hx
    rw [complexEuclideanEquivRealProd_symm_apply] at ha hb
    simp only [complexEuclideanEquivRealProd_apply_fst, complexEuclideanEquivRealProd_apply_snd,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.mul_re,
      Complex.mul_im, ← ha, ← hb, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linear_combination p.re * hL
  · rw [fderiv_oppositeWeightInvariant_apply, ContinuousLinearEquiv.symm_apply_apply, ha, hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.1 hab
    rw [← hp]
    field_simp
    ring

/-- **Uniqueness of the reduced form on the free stratum.** At a point `x ≠ 0` of the zero level,
a bilinear form `β` on `T_(Φ x) ℂ = ℂ` pulls back along the invariant `Φ = z₀ z₁` to the
restriction of the standard symplectic form to the level exactly when it is
`dx ∧ dy / (2 |Φ x|)`, that is `β(c, d) = Im (conj c d) / (2 |Φ x|)`. -/
theorem forall_stdSymplecticForm_eq_iff_of_weightMomentMap_id_neg_id
    {x : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)}
    (hx : weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ] x = 0)
    (hx0 : x ≠ 0) (β : LinearMap.BilinForm ℝ ℂ) :
    (∀ v w,
      fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ]) x v =
          0 →
        fderiv ℝ (weightMomentMap ![ContinuousLinearMap.id ℝ ℝ, -ContinuousLinearMap.id ℝ ℝ]) x
            w = 0 →
          stdSymplecticForm v w =
            β (fderiv ℝ oppositeWeightInvariant x v) (fderiv ℝ oppositeWeightInvariant x w)) ↔
      ∀ c d, β c d = (conj c * d).im / (2 * ‖oppositeWeightInvariant x‖) := by
  refine ⟨fun h c d ↦ ?_, fun h v w hv hw ↦ ?_⟩
  · obtain ⟨v, hv, rfl⟩ := exists_fderiv_weightMomentMap_id_neg_id_eq_zero_and_fderiv_eq hx hx0 c
    obtain ⟨w, hw, rfl⟩ := exists_fderiv_weightMomentMap_id_neg_id_eq_zero_and_fderiv_eq hx hx0 d
    rw [← h v w hv hw,
      stdSymplecticForm_eq_div_of_fderiv_weightMomentMap_id_neg_id_eq_zero hx hx0 hv hw]
  · rw [h, stdSymplecticForm_eq_div_of_fderiv_weightMomentMap_id_neg_id_eq_zero hx hx0 hv hw]

end TauCeti

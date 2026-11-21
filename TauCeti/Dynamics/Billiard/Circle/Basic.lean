/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.NumberTheory.Real.Irrational
public import TauCeti.Analysis.Calculus.DifferentialForm.Exact
public import TauCeti.Analysis.Calculus.DifferentialForm.Plane
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Dynamics.Billiard.NextCollision
public import TauCeti.Geometry.Euclidean.Circle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Billiard dynamics on a circle

For a circular billiard table of center `c` and radius `R > 0` in an oriented Euclidean plane `E`,
the positively oriented arclength parametrization `Orientation.circleCurve` (from
`TauCeti.Geometry.Euclidean.Circle`),

`χ(s) = c + R • (cos (s / R) • e + sin (s / R) • J e) = c + R • o.rotation (s / R) e`

of period `L = 2 π R`, makes the next-collision map completely integrable: the tangential velocity
`v ∈ (-1, 1)` is conserved at every bounce and the arclength parameter advances by `2 R arccos v`.
This file constructs the circular billiard table, computes its strip and quotient billiard maps,
proves the chord-length primitive identity and invariant-measure properties, and establishes the
rational-rotation periodicity criterion and irrational-rotation density. Explicit inscribed `N`-gon
perimeter maximizers and reflection-law checks for `N = 2, 3, 4` live in
`TauCeti.Dynamics.Billiard.Circle.Polygon`.

## Main definitions

* `Orientation.circleBilliardTable`: the circular `TauCeti.StrictConvexBilliardTable` of center `c`,
  starting unit radial vector `e`, and radius `R > 0`, with boundary length `2 π R`.
* `TauCeti.circleBilliardQuotient`: the quotient billiard homeomorphism
  `(q, v) ↦ (q + ↑(2 R arccos v), v)` on `AddCircle (2 π R) × Ioo (-1) 1`.

## Main results

* `Orientation.circleBilliardTable_nextCollision`,
  `Orientation.circleBilliardTable_norm_nextParam_sub`: on `ℝ × Ioo (-1) 1`, the next-collision map
  is `(s, v) ↦ (s + 2 R arccos v, v)` and the chord length to the next collision is
  `ℓ(s, v) = 2 R √(1 - v ^ 2)`.
* `Orientation.circleBilliardTable_pullback_liouvilleForm_sub`,
  `Orientation.circleBilliardTable_pullback_symplecticForm`: the exactness identity
  `β*(v ds) - v ds = dℓ` and area preservation `β*(ds ∧ dv) = ds ∧ dv` on the open strip.
* `TauCeti.measurePreserving_circleBilliardQuotient`,
  `TauCeti.isPeriodicPt_circleBilliardQuotient_iff`,
  `TauCeti.minimalPeriod_circleBilliardQuotient`,
  `TauCeti.denseRange_zsmul_circleBilliardQuotient_iff`: the quotient billiard map preserves the
  product of Haar measure on `AddCircle (2 π R)` with any vertical measure (of total mass
  `4 π R = 2 L` for Lebesgue measure on `(-1, 1)`), `(q, v)` is `n`-periodic if and only if
  `n arccos v` is an integer multiple of `π`, and the angular orbit is dense if and only if
  `arccos v / π` is irrational.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapters 3 and 6.
-/

public section

noncomputable section

open Function Set Filter Topology Module MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-! ### The circular billiard table -/

namespace Orientation

open TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-- The circular billiard table of center `c`, starting unit radial vector `e`, and radius `R > 0`
in the plane `E` oriented by `o`, with boundary length `2 π R`. -/
def circleBilliardTable (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) : StrictConvexBilliardTable o where
  toFun := o.circleCurve c e R
  period := 2 * Real.pi * R
  period_pos := by positivity
  periodic := o.periodic_circleCurve c e R
  norm_deriv := o.norm_deriv_circleCurve c e he hR.ne'
  injOn := o.injOn_circleCurve_Ico c (norm_ne_zero_iff.1 (he.trans_ne one_ne_zero)) R
  areaForm_pos s t hne := by
    rw [o.areaForm_deriv_circleCurve_sub c e R s t]
    have hpos : 0 < ‖o.circleCurve c e R t - o.circleCurve c e R s‖ :=
      norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity

@[simp]
theorem coe_circleBilliardTable (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) :
    ⇑(o.circleBilliardTable c e R he hR) = o.circleCurve c e R :=
  (rfl)

@[simp]
theorem circleBilliardTable_period (o : Orientation ℝ E (Fin 2)) (c e : E) (R : ℝ) (he : ‖e‖ = 1)
    (hR : 0 < R) :
    (o.circleBilliardTable c e R he hR).period = 2 * Real.pi * R :=
  (rfl)

/-! ### Next-collision map, chord length, and exactness on the strip -/

/-- On the circular billiard table, the outgoing velocity at `(s, v)` is the unit tangent vector at
angle `s / R + arccos v`. -/
private theorem circleBilliardTable_outgoingDir_eq (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Icc (-1) 1) :
    (o.circleBilliardTable c e R he hR).outgoingDir s v =
      o.rightAngleRotation (o.rotation (s / R + Real.arccos v : ℝ) e) := by
  set α := Real.arccos v
  have hv_sin : √(1 - v ^ 2) = Real.Angle.sin (α : Real.Angle) := by
    rw [Real.Angle.sin_coe, Real.sin_arccos]
  have hv_cos : v = Real.Angle.cos (α : Real.Angle) := by
    rw [Real.Angle.cos_coe, Real.cos_arccos hv.1 hv.2]
  rw [StrictConvexBilliardTable.outgoingDir_def, coe_circleBilliardTable,
    o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR.ne',
    hv_sin, hv_cos, ← map_smul o.rightAngleRotation, ← map_smul o.rightAngleRotation,
    ← map_add o.rightAngleRotation, ← o.rotation_apply, o.rotation_rotation,
    ← Real.Angle.coe_add, add_comm α (s / R)]

/-- On the circle of radius `R`, the next collision from `(s, v)` with `v ∈ (-1, 1)` occurs at
arclength parameter `s + 2 R arccos v`. -/
@[simp]
theorem circleBilliardTable_nextParam (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextParam s v = s + 2 * R * Real.arccos v := by
  have hα_pos : 0 < Real.arccos v := Real.arccos_pos.2 hv.2
  have hα_lt : Real.arccos v < Real.pi := Real.arccos_lt_pi.2 hv.1
  refine ((o.circleBilliardTable c e R he hR).eq_nextParam_of_areaForm_eq_zero hv ?_ ?_).symm
  · rw [circleBilliardTable_period]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [coe_circleBilliardTable, o.circleBilliardTable_outgoingDir_eq c e he hR ⟨hv.1.le, hv.2.le⟩,
      o.circleCurve_add_two_mul_sub c e R s (Real.arccos v), map_smul,
      o.areaForm_apply_self, smul_zero]

/-- On the circle of radius `R`, the Euclidean length of the chord from `(s, v)` with `v ∈ (-1, 1)`
to the next collision is `2 R √(1 - v ^ 2)`. -/
theorem circleBilliardTable_norm_nextParam_sub (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam s v) -
        o.circleCurve c e R s‖ =
      2 * R * √(1 - v ^ 2) := by
  have hsqrt : 0 ≤ 2 * R * √(1 - v ^ 2) := by positivity
  rw [o.circleBilliardTable_nextParam c e he hR hv,
    o.circleCurve_add_two_mul_sub c e R s (Real.arccos v), Real.sin_arccos, norm_smul,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, he, mul_one,
    Real.norm_of_nonneg hsqrt]

/-- On the circle, the tangential component `v ∈ (-1, 1)` is conserved at the next collision. -/
@[simp]
theorem circleBilliardTable_nextTangential (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextTangential s v = v := by
  let α := Real.arccos v
  let u := o.rotation (s / R + α : ℝ) e
  have hu : ⟪u, u⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, LinearIsometryEquiv.norm_map, he, one_pow]
  have hJu : ⟪u, o.rightAngleRotation u⟫ = 0 := by
    rw [real_inner_comm, o.inner_rightAngleRotation_self]
  have hdiv : (s + 2 * R * α) / R = α + (s / R + α) := by field_simp; ring
  rw [StrictConvexBilliardTable.nextTangential_def, o.circleBilliardTable_nextParam c e he hR hv,
    coe_circleBilliardTable, o.circleBilliardTable_outgoingDir_eq c e he hR ⟨hv.1.le, hv.2.le⟩,
    o.deriv_circleCurve_eq_rightAngleRotation_rotation c e hR.ne',
    LinearIsometryEquiv.inner_map_map, hdiv, Real.Angle.coe_add α (s / R + α),
    ← o.rotation_rotation (α : Real.Angle) (s / R + α : ℝ) e,
    o.rotation_apply (α : Real.Angle) u, Real.Angle.cos_coe, Real.Angle.sin_coe, inner_add_right,
    real_inner_smul_right, real_inner_smul_right, hu, hJu, mul_one, mul_zero, add_zero,
    Real.cos_arccos hv.1.le hv.2.le]

/-- **The next-collision map of a circle.** On `ℝ × Ioo (-1) 1`, the strip billiard map of a circle
of radius `R` is `(s, v) ↦ (s + 2 R arccos v, v)`. -/
theorem circleBilliardTable_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    (o.circleBilliardTable c e R he hR).nextCollision (s, v) =
      (s + 2 * R * Real.arccos v, v) := by
  rw [StrictConvexBilliardTable.nextCollision_apply, o.circleBilliardTable_nextParam c e he hR hv,
    o.circleBilliardTable_nextTangential c e he hR hv]

/-- The `n`-th iterate of the strip billiard map on the circle advances `s` by `2 n R arccos v` and
preserves `v`. -/
theorem circleBilliardTable_iterate_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) (n : ℕ) {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    ((o.circleBilliardTable c e R he hR).nextCollision^[n]) (s, v) =
      (s + n * (2 * R * Real.arccos v), v) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, o.circleBilliardTable_nextCollision c e he hR hv, ih]
    refine Prod.ext ?_ rfl
    push_cast
    ring

/-- Fréchet derivative of the strip billiard map of the circle at an interior collision state
`x = (s, v)` with `v ∈ (-1, 1)`. -/
theorem hasFDerivAt_circleBilliardTable_nextCollision (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt (o.circleBilliardTable c e R he hR).nextCollision
      ((ContinuousLinearMap.fst ℝ ℝ ℝ -
          (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
  have harc : HasDerivAt Real.arccos (-(1 / √(1 - x.2 ^ 2))) x.2 :=
    Real.hasDerivAt_arccos hx.1.ne' hx.2.ne
  have hg1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)).add
    ((harc.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℝ))).const_mul (2 * R))
  have hg : HasFDerivAt (fun y : ℝ × ℝ ↦ (y.1 + 2 * R * Real.arccos y.2, y.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ -
          (2 * R / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) x := by
    refine (hg1.prodMk (hasFDerivAt_snd (𝕜 := ℝ))).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun y ↦ Prod.ext (by simp; ring) rfl
  refine hg.congr_of_eventuallyEq ?_
  have hnhds : (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1 ∈ 𝓝 x :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx⟩
  filter_upwards [hnhds] with ⟨s, v⟩ hsv
  exact o.circleBilliardTable_nextCollision c e he hR hsv.2

/-- Fréchet derivative of the chord-length function `ℓ(s, v) = 2 R √(1 - v ^ 2)` on the open strip
`v ∈ (-1, 1)`. -/
theorem hasFDerivAt_circleBilliardTable_norm_nextParam_sub (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt
      (fun y : ℝ × ℝ ↦
        ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam y.1 y.2) -
          o.circleCurve c e R y.1‖)
      (-(2 * R * x.2 / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hpos : 0 < 1 - x.2 ^ 2 := by nlinarith [hx.1, hx.2]
  have hpoly : HasDerivAt (fun v : ℝ ↦ 1 - v ^ 2) (-2 * x.2) x.2 := by
    simpa using (hasDerivAt_pow 2 x.2).const_sub 1
  have hsqrt : HasDerivAt (fun v : ℝ ↦ 2 * R * √(1 - v ^ 2))
      (2 * R * ((-2 * x.2) / (2 * √(1 - x.2 ^ 2)))) x.2 :=
    (hpoly.sqrt hpos.ne').const_mul (2 * R)
  have hg : HasFDerivAt (fun y : ℝ × ℝ ↦ 2 * R * √(1 - y.2 ^ 2))
      (-(2 * R * x.2 / √(1 - x.2 ^ 2)) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    refine (hsqrt.comp_hasFDerivAt x (hasFDerivAt_snd (𝕜 := ℝ))).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun y ↦ by simp; ring
  refine hg.congr_of_eventuallyEq ?_
  have hnhds : (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1 ∈ 𝓝 x :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hx⟩
  filter_upwards [hnhds] with ⟨s, v⟩ hsv
  exact o.circleBilliardTable_norm_nextParam_sub c e he hR hsv.2

/-- **Chord-length primitive formula on the circle.** With `λ = v ds` (`x.2 • Prod.realPlaneDx x`)
and `ℓ(s, v) = ‖χ(nextParam s v) - χ(s)‖` the chord length to the next collision, the strip
billiard map `β` of the circle satisfies `β*λ - λ = dℓ` at every `x = (s, v)` with
`v ∈ (-1, 1)`. -/
theorem circleBilliardTable_pullback_liouvilleForm_sub (o : Orientation ℝ E (Fin 2)) (c e : E)
    {R : ℝ} (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    ContinuousAlternatingMap.compContinuousLinearMap
        (((o.circleBilliardTable c e R he hR).nextCollision x).2 •
          Prod.realPlaneDx ((o.circleBilliardTable c e R he hR).nextCollision x))
        (fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x) -
      x.2 • Prod.realPlaneDx x =
      differentialOneForm ℝ
        (fun y : ℝ × ℝ ↦
          ‖o.circleCurve c e R ((o.circleBilliardTable c e R he hR).nextParam y.1 y.2) -
            o.circleCurve c e R y.1‖) x := by
  have hβ := (o.hasFDerivAt_circleBilliardTable_nextCollision c e he hR hx).fderiv
  have hℓ := (o.hasFDerivAt_circleBilliardTable_norm_nextParam_sub c e he hR hx).fderiv
  have hnext : (o.circleBilliardTable c e R he hR).nextCollision x =
      (x.1 + 2 * R * Real.arccos x.2, x.2) :=
    o.circleBilliardTable_nextCollision c e he hR (s := x.1) hx
  ext u
  rw [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.smul_apply,
    differentialOneForm_apply, hnext, hβ, hℓ]
  simp only [Prod.realPlaneDx_apply, Function.comp_apply, ContinuousLinearMap.prod_apply,
    FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **Area preservation on the strip.** The strip billiard map `β` of the circle preserves the
two-form `ω = ds ∧ dv` at every `x = (s, v)` with `v ∈ (-1, 1)`. -/
theorem circleBilliardTable_pullback_symplecticForm (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ}
    (he : ‖e‖ = 1) (hR : 0 < R) {x : ℝ × ℝ} (hx : x.2 ∈ Ioo (-1) 1) :
    ContinuousAlternatingMap.compContinuousLinearMap
        ((Prod.realPlaneDx ((o.circleBilliardTable c e R he hR).nextCollision x)).wedge
          (Prod.realPlaneDy ((o.circleBilliardTable c e R he hR).nextCollision x)))
        (fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x) =
      (Prod.realPlaneDx x).wedge (Prod.realPlaneDy x) := by
  have hβ := (o.hasFDerivAt_circleBilliardTable_nextCollision c e he hR hx).fderiv
  ext u
  have hu : u = ![u 0, u 1] := by funext i; fin_cases i <;> rfl
  have hcomp : fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x ∘ ![u 0, u 1] =
      ![fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x (u 0),
        fderiv ℝ (o.circleBilliardTable c e R he hR).nextCollision x (u 1)] := by
    funext i; fin_cases i <;> rfl
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hu, hcomp,
    ContinuousAlternatingMap.wedge_apply_one_one, ContinuousAlternatingMap.wedge_apply_one_one, hβ]
  simp only [Prod.realPlaneDx_apply, Prod.realPlaneDy_apply, Matrix.cons_val_zero,
    ContinuousLinearMap.prod_apply, FunLike.coe_sub, Pi.sub_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

end Orientation

/-! ### The quotient billiard map, its invariant measure, and rational-rotation periodicity -/

namespace TauCeti

/-- **The quotient billiard homeomorphism of a circle of radius `R`.** On the topological phase
space `AddCircle (2 π R) × Ioo (-1) 1`, it sends `(q, v)` to `(q + ↑(2 R arccos v), v)`. -/
def circleBilliardQuotient (R : ℝ) :
    AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1 ≃ₜ
      AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1 where
  toFun p := (p.1 + ↑(2 * R * Real.arccos p.2.val), p.2)
  invFun p := (p.1 - ↑(2 * R * Real.arccos p.2.val), p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_fst.add
      (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtypeVal.comp continuous_snd))))
  continuous_invFun := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_fst.sub
      (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtypeVal.comp continuous_snd))))

@[simp]
theorem circleBilliardQuotient_apply (R : ℝ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    circleBilliardQuotient R p = (p.1 + ↑(2 * R * Real.arccos p.2.val), p.2) :=
  (rfl)

@[simp]
theorem circleBilliardQuotient_symm_apply (R : ℝ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (circleBilliardQuotient R).symm p = (p.1 - ↑(2 * R * Real.arccos p.2.val), p.2) :=
  (rfl)

end TauCeti

namespace Orientation

open TauCeti

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

/-- `TauCeti.circleBilliardQuotient R` is the quotient of
`(o.circleBilliardTable c e R he hR).nextCollision` modulo deck translations by `2 π R`. -/
theorem circleBilliardQuotient_coe (o : Orientation ℝ E (Fin 2)) (c e : E) {R : ℝ} (he : ‖e‖ = 1)
    (hR : 0 < R) (s : ℝ) (v : Ioo (-1 : ℝ) 1) :
    circleBilliardQuotient R (↑s, v) =
      (↑((o.circleBilliardTable c e R he hR).nextParam s v.val),
        ⟨(o.circleBilliardTable c e R he hR).nextTangential s v.val,
          (o.circleBilliardTable c e R he hR).nextTangential_mem_Ioo v.property⟩) := by
  ext
  · simp [o.circleBilliardTable_nextParam c e he hR v.property, QuotientAddGroup.mk_add]
  · simp [o.circleBilliardTable_nextTangential c e he hR v.property]

end Orientation

namespace TauCeti

/-- **Measure preservation on the quotient.** For any measure `ν` on `Ioo (-1) 1` (in particular
Lebesgue measure), `circleBilliardQuotient R` preserves the product of the Haar measure `volume` on
`AddCircle (2 π R)` with `ν`. -/
theorem measurePreserving_circleBilliardQuotient (R : ℝ) [Fact (0 < 2 * Real.pi * R)]
    (ν : Measure (Ioo (-1 : ℝ) 1)) :
    MeasurePreserving (circleBilliardQuotient R) (volume.prod ν) (volume.prod ν) := by
  by_cases hν : SFinite ν
  · have hgm : Measurable (uncurry fun (v : Ioo (-1 : ℝ) 1) (q : AddCircle (2 * Real.pi * R)) ↦
        q + (↑(2 * R * Real.arccos v.val) : AddCircle (2 * Real.pi * R))) :=
      (continuous_snd.add (QuotientAddGroup.continuous_mk.comp
        (continuous_const.mul (Real.continuous_arccos.comp
          (continuous_subtypeVal.comp continuous_fst))))).measurable
    have hshear := MeasurePreserving.skew_product
      (g := fun (v : Ioo (-1 : ℝ) 1) (q : AddCircle (2 * Real.pi * R)) ↦
        q + (↑(2 * R * Real.arccos v.val) : AddCircle (2 * Real.pi * R)))
      (MeasurePreserving.id ν) hgm
      (Eventually.of_forall fun v ↦
        map_add_right_eq_self (volume : Measure (AddCircle (2 * Real.pi * R)))
          (↑(2 * R * Real.arccos v.val) : AddCircle (2 * Real.pi * R)))
    convert Measure.measurePreserving_swap.comp (hshear.comp Measure.measurePreserving_swap)
    ext ⟨q, v⟩ <;> rfl
  · rw [Measure.prod_eq_zero_of_not_sfinite hν]
    exact ⟨(circleBilliardQuotient R).continuous.measurable, Measure.map_zero _⟩

/-- Total mass `4 π R = 2 L` of the product of `volume` on `AddCircle (2 π R)` with Lebesgue
measure `Measure.comap Subtype.val volume` on `Ioo (-1) 1`. -/
theorem measure_univ_circleBilliardPhaseSpace (R : ℝ) [hL : Fact (0 < 2 * Real.pi * R)] :
    ((volume : Measure (AddCircle (2 * Real.pi * R))).prod
        (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume)) univ =
      ENNReal.ofReal (4 * Real.pi * R) := by
  have hIoo : (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume) univ =
      ENNReal.ofReal 2 := by
    rw [← Measure.Subtype.volume_def,
      Measure.Subtype.volume_univ isOpen_Ioo.measurableSet.nullMeasurableSet, Real.volume_Ioo]
    norm_num
  have : IsFiniteMeasure (Measure.comap (Subtype.val : Ioo (-1 : ℝ) 1 → ℝ) volume) :=
    ⟨by rw [hIoo]; exact ENNReal.ofReal_lt_top⟩
  have hR_nonneg : 0 ≤ 2 * Real.pi * R := hL.out.le
  rw [← univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ, hIoo,
    ← ENNReal.ofReal_mul hR_nonneg]
  congr 1
  ring

/-- The `n`-th forward iterate of `circleBilliardQuotient R` rotates the first coordinate by
`n • ↑(2 R arccos v)` and fixes `v`. -/
@[simp]
theorem iterate_circleBilliardQuotient (R : ℝ) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    ((circleBilliardQuotient R)^[n]) p =
      (p.1 + n • (↑(2 * R * Real.arccos p.2.val) : AddCircle (2 * Real.pi * R)), p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    simp [succ_nsmul', add_assoc]

/-- The `n`-th backward iterate of `circleBilliardQuotient R` subtracts `n • ↑(2 R arccos v)` from
the first coordinate and fixes `v`. -/
@[simp]
theorem iterate_circleBilliardQuotient_symm (R : ℝ) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (((circleBilliardQuotient R).symm)^[n]) p =
      (p.1 - n • (↑(2 * R * Real.arccos p.2.val) : AddCircle (2 * Real.pi * R)), p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, ih]
    refine Prod.ext ?_ rfl
    simp only [circleBilliardQuotient_symm_apply, succ_nsmul', sub_eq_add_neg, neg_add_rev]
    abel

/-- **Rational-rotation periodicity criterion.** For `R ≠ 0`, a quotient collision state
`p = (q, v)` has period `n` under `circleBilliardQuotient R` if and only if `n * arccos v` is an
integer multiple of `π`. -/
theorem isPeriodicPt_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0) (n : ℕ)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    IsPeriodicPt (circleBilliardQuotient R) n p ↔
      ∃ k : ℤ, (n : ℝ) * Real.arccos p.2.val = k * Real.pi := by
  rw [IsPeriodicPt, IsFixedPt, iterate_circleBilliardQuotient, Prod.ext_iff]
  simp only [and_true, add_eq_left, ← AddCircle.coe_nsmul, nsmul_eq_mul,
    AddCircle.coe_eq_zero_iff, zsmul_eq_mul]
  refine exists_congr fun k ↦ ⟨fun h ↦ ?_, fun h ↦ by linear_combination -2 * R * h⟩
  have hmul : (2 * R) * ((n : ℝ) * Real.arccos p.2.val - k * Real.pi) = 0 := by linarith
  linarith [(mul_eq_zero.1 hmul).resolve_left (mul_ne_zero two_ne_zero hR)]

/-- A state `p = (q, v)` lies on a periodic orbit of `circleBilliardQuotient R` (`R ≠ 0`) if and
only if `arccos v` is a rational multiple of `π`. -/
theorem exists_pos_isPeriodicPt_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    (∃ n > 0, IsPeriodicPt (circleBilliardQuotient R) n p) ↔
      ∃ r : ℚ, Real.arccos p.2.val = r * Real.pi := by
  constructor
  · rintro ⟨n, hn, hper⟩
    obtain ⟨k, hk⟩ := (isPeriodicPt_circleBilliardQuotient_iff hR n p).1 hper
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨(k : ℚ) / (n : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hn']
    linarith
  · rintro ⟨r, hr⟩
    refine ⟨r.den, r.pos, (isPeriodicPt_circleBilliardQuotient_iff hR r.den p).2 ⟨r.num, ?_⟩⟩
    have hden : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.2 r.pos.ne'
    have hrat : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den r).symm
    rw [hr, hrat]
    field_simp

/-- **Exact least period under coprime rotation number.** If `n * arccos v = k * π` with `n > 0`
and `k` coprime to `n`, then the least period of `(q, v)` under `circleBilliardQuotient R` (`R ≠ 0`)
is `n`. -/
theorem minimalPeriod_circleBilliardQuotient {R : ℝ} (hR : R ≠ 0) {n : ℕ} (hn : 0 < n) {k : ℤ}
    {p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1}
    (hk : (n : ℝ) * Real.arccos p.2.val = k * Real.pi) (hcop : IsCoprime k (n : ℤ)) :
    minimalPeriod (circleBilliardQuotient R) p = n := by
  have hper_n : IsPeriodicPt (circleBilliardQuotient R) n p :=
    (isPeriodicPt_circleBilliardQuotient_iff hR n p).2 ⟨k, hk⟩
  refine le_antisymm (hper_n.minimalPeriod_le hn) ?_
  set m := minimalPeriod (circleBilliardQuotient R) p
  have hm : 0 < m := hper_n.minimalPeriod_pos hn
  have hper_m : IsPeriodicPt (circleBilliardQuotient R) m p := isPeriodicPt_minimalPeriod _ _
  obtain ⟨l, hl⟩ := (isPeriodicPt_circleBilliardQuotient_iff hR m p).1 hper_m
  have hreal : ((m : ℤ) * k : ℝ) * Real.pi = ((n : ℤ) * l : ℝ) * Real.pi := by
    calc
      ((m : ℤ) * k : ℝ) * Real.pi = (m : ℝ) * ((n : ℝ) * Real.arccos p.2.val) := by
        push_cast; linear_combination (m : ℝ) * hk.symm
      _ = (n : ℝ) * ((m : ℝ) * Real.arccos p.2.val) := by ring
      _ = ((n : ℤ) * l : ℝ) * Real.pi := by
        push_cast; linear_combination (n : ℝ) * hl
  have hint : (m : ℤ) * k = (n : ℤ) * l := by
    exact_mod_cast mul_right_cancel₀ Real.pi_ne_zero hreal
  have hdvd : (n : ℤ) ∣ (m : ℤ) :=
    hcop.symm.dvd_of_dvd_mul_right ⟨l, hint⟩
  exact Nat.le_of_dvd hm (Int.ofNat_dvd.1 hdvd)

/-- A diameter billiard state (`v = 0`) on `circleBilliardQuotient R` (`R ≠ 0`) has least period
`2`. -/
theorem minimalPeriod_circleBilliardQuotient_zero {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : (0 : ℝ) ∈ Ioo (-1) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨0, hv⟩) = 2 := by
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [Real.arccos_zero]
  push_cast
  ring

/-- An equilateral-triangle billiard state (`v = 1 / 2`) on `circleBilliardQuotient R` (`R ≠ 0`)
has least period `3`. -/
theorem minimalPeriod_circleBilliardQuotient_half {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : (1 / 2 : ℝ) ∈ Ioo (-1) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨1 / 2, hv⟩) = 3 := by
  have harc : Real.arccos (1 / 2) = Real.pi / 3 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_three.symm
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [harc]
  push_cast
  ring

/-- Although not a global perimeter maximizer, the inscribed square corresponds to a quotient
billiard state `(q, √2 / 2)` of genuine least period `4` (`R ≠ 0`). -/
theorem minimalPeriod_circleBilliardQuotient_sqrt_two_div_two {R : ℝ} (hR : R ≠ 0)
    (q : AddCircle (2 * Real.pi * R)) {hv : √2 / 2 ∈ Ioo (-1 : ℝ) 1} :
    minimalPeriod (circleBilliardQuotient R) (q, ⟨√2 / 2, hv⟩) = 4 := by
  have harc : Real.arccos (√2 / 2) = Real.pi / 4 :=
    Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) Real.cos_pi_div_four.symm
  refine minimalPeriod_circleBilliardQuotient hR (by decide) (k := 1) ?_ isCoprime_one_left
  simp only [harc]
  push_cast
  ring

/-- **Irrational-rotation density.** For `R ≠ 0`, the two-sided angular orbit
`z ↦ q + z • ↑(2 R arccos v)` is dense in `AddCircle (2 π R)` if and only if `arccos v / π` is
irrational. -/
theorem denseRange_zsmul_circleBilliardQuotient_iff {R : ℝ} (hR : R ≠ 0)
    (p : AddCircle (2 * Real.pi * R) × Ioo (-1 : ℝ) 1) :
    DenseRange
        (fun z : ℤ ↦ p.1 + z • (↑(2 * R * Real.arccos p.2.val) : AddCircle (2 * Real.pi * R))) ↔
      Irrational (Real.arccos p.2.val / Real.pi) := by
  let e := Homeomorph.addLeft p.1
  have hiff : DenseRange
      (fun z : ℤ ↦ e (z • (↑(2 * R * Real.arccos p.2.val) : AddCircle (2 * Real.pi * R)))) ↔
      DenseRange (fun z : ℤ ↦ z • (↑(2 * R * Real.arccos p.2.val) : AddCircle (2 * Real.pi * R))) :=
    ⟨fun h ↦ by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
        e.symm.surjective.denseRange.comp h e.symm.continuous,
     fun h ↦ e.surjective.denseRange.comp h e.continuous⟩
  have hdiv :
      (2 * R * Real.arccos p.2.val) / (2 * Real.pi * R) = Real.arccos p.2.val / Real.pi := by
    field_simp
  exact hiff.trans (AddCircle.denseRange_zsmul_coe_iff.trans (by rw [hdiv]))

end TauCeti

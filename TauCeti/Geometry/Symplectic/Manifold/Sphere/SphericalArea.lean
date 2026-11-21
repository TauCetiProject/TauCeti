/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Absolute
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.HalfSqRadius

/-!
# The symplectic area of spheres in the two-sphere

Let `S² ⊂ ℝ³` be the unit sphere with its area form `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.sphereAreaForm`), of total area `4π`. This file computes the integral of `σ` over the
second homotopy group (`TauCeti.sphereIntegral`): it is injective on `π₂(S², x)`, with image the
multiples of `4π`, at every base point `x`
(`TauCeti.sphereIntegral_sphereAreaForm_injective`, `TauCeti.range_sphereIntegral_sphereAreaForm`).
In particular the tautological sphere `TauCeti.sphereGenLoop 2`, whose Hurewicz class generates
`H₂(S²; ℤ)`, has area `±4π` (`TauCeti.abs_sphereIntegral_sphereAreaForm_sphereGenLoop`).

Since `S²` is simply connected, the Hurewicz map `π₂(S², x) → H₂(S²; ℤ)` is an isomorphism, so the
area descends to a homomorphism `TauCeti.sphereAreaHom : H₂(S²; ℤ) → ℝ` that agrees with the
integral of `σ` on the Hurewicz class of every sphere, at every base point
(`TauCeti.sphereAreaHom_hurewiczIntHom`). This is the area period of the two-sphere in the form
that capped Hamiltonian Floer theory takes it: a homomorphism on `H₂(M; ℤ)` together with its
agreement with the sphere integral.

The computation uses one explicit sphere. On the plane put `a = p₁² + p₂²`, let
`G(a) = β(1 - a)` for the smooth transition `β` (so `G > 0` for `a < 1` and `G = 0` for `a ≥ 1`),
and let

`Φ(p) = (2 G p₁, 2 G p₂, a - G²) / (a + G²)`.

This is a smooth map of the plane into `S²`. It sends the outside of the open unit disc to the
north pole, and the open disc bijectively onto the rest of the sphere: there it is the inverse
stereographic projection of `p / G(a)`. Writing `Φ(p) = (A(a) p, B(a))`, the identity
`A² a + B² = 1` and its derivative show that `Φ` pulls `σ` back to `-2 B'(a) dp₁ ∧ dp₂`. Pushing
planar Lebesgue measure forward along `a / 2` (`TauCeti.map_volume_half_sq_add_sq`), its integral
is `-2π (B(1) - B(0)) = -4π`. Precomposed with `z ↦ 2 z - 1` it gives a generalized loop of the
unit square, of area `-4π`.

Its class generates `π₂(S²)`. Composing `Φ` with the radial homeomorphism that takes the square
`max(|p₁|, |p₂|) ≤ 1` onto the closed unit disc (`ContinuousLinearEquiv.unitBallHomeomorph`) gives
a generalized loop identifying only points of the boundary of the cube, which therefore has a
generating Hurewicz class (`GenLoop.isIso_hurewicz_of_bijective_toSphere`). The straight-line
homotopy between the two maps keeps the boundary of the cube at the north pole. By the Hurewicz
theorem every class of `π₂(S²)` is an integer multiple of this one, and its area is the
corresponding multiple of `-4π`.

## Main definitions

* `TauCeti.sphereAreaHom`: the area of the round two-sphere as a homomorphism on `H₂(S²; ℤ)`.

## Main results

* `TauCeti.sphereIntegral_sphereAreaForm_injective`: a sphere class in `S²` is determined by its
  area.
* `TauCeti.range_sphereIntegral_sphereAreaForm`: the areas of the sphere classes in `S²` are the
  multiples of `4π`.
* `TauCeti.abs_sphereIntegral_sphereAreaForm_sphereGenLoop`: the tautological sphere has area
  `±4π`.
* `TauCeti.sphereAreaHom_hurewiczIntHom`: the area homomorphism on `H₂(S²; ℤ)` agrees with the
  integral of `σ` on Hurewicz classes.
* `TauCeti.abs_sphereAreaHom_hurewicz_sphereGenLoop`: its value on the generator of `H₂(S²; ℤ)`
  is `±4π`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and the Novikov ring of `CP¹`).
* A. Hatcher, *Algebraic Topology*, Section 4.2 (the Hurewicz theorem).
-/

public section

noncomputable section

open Metric Module MeasureTheory Set Real Matrix AlgebraicTopology HomotopyGroup
open scoped Manifold ContDiff EuclideanSpace unitInterval Topology Topology.Homotopy

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

/-! ### The radial profile -/

/-- The radial profile `G(a) = β(1 - a)`: positive for `a < 1`, zero for `a ≥ 1`, and `1` for
`a ≤ 0`. -/
private def discProfile (a : ℝ) : ℝ := smoothTransition (1 - a)

/-- The horizontal factor `A(a) = 2 G / (a + G²)` of the collapse map. -/
private def horizontalFactor (a : ℝ) : ℝ := 2 * discProfile a / (a + discProfile a ^ 2)

/-- The height `B(a) = (a - G²) / (a + G²)` of the collapse map. -/
private def heightProfile (a : ℝ) : ℝ := (a - discProfile a ^ 2) / (a + discProfile a ^ 2)

private theorem discProfile_of_nonpos {a : ℝ} (ha : a ≤ 0) : discProfile a = 1 :=
  smoothTransition.one_of_one_le (by linarith)

private theorem discProfile_of_one_le {a : ℝ} (ha : 1 ≤ a) : discProfile a = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

private theorem discProfile_pos {a : ℝ} (ha : a < 1) : 0 < discProfile a :=
  smoothTransition.pos_of_pos (by linarith)

private theorem add_discProfile_sq_pos {a : ℝ} (ha : -1 < a) : 0 < a + discProfile a ^ 2 := by
  rcases le_or_gt a 0 with h | h
  · rw [discProfile_of_nonpos h]
    linarith
  · positivity

private theorem contDiff_discProfile : ContDiff ℝ ∞ discProfile :=
  smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

private theorem contDiffAt_horizontalFactor {a : ℝ} (ha : -1 < a) :
    ContDiffAt ℝ ∞ horizontalFactor a :=
  ((contDiff_const.mul contDiff_discProfile).contDiffAt).div
    ((contDiff_id.add (contDiff_discProfile.pow 2)).contDiffAt) (add_discProfile_sq_pos ha).ne'

private theorem contDiffAt_heightProfile {a : ℝ} (ha : -1 < a) : ContDiffAt ℝ ∞ heightProfile a :=
  ((contDiff_id.sub (contDiff_discProfile.pow 2)).contDiffAt).div
    ((contDiff_id.add (contDiff_discProfile.pow 2)).contDiffAt) (add_discProfile_sq_pos ha).ne'

private theorem horizontalFactor_sq_mul_add_heightProfile_sq {a : ℝ} (ha : -1 < a) :
    horizontalFactor a ^ 2 * a + heightProfile a ^ 2 = 1 := by
  have := (add_discProfile_sq_pos ha).ne'
  simp only [horizontalFactor, heightProfile]
  field_simp
  ring

private theorem horizontalFactor_of_one_le {a : ℝ} (ha : 1 ≤ a) : horizontalFactor a = 0 := by
  simp [horizontalFactor, discProfile_of_one_le ha]

private theorem heightProfile_of_one_le {a : ℝ} (ha : 1 ≤ a) : heightProfile a = 1 := by
  simp [heightProfile, discProfile_of_one_le ha, (by linarith : (0 : ℝ) < a).ne']

private theorem heightProfile_zero : heightProfile 0 = -1 := by
  simp [heightProfile, discProfile_of_nonpos le_rfl]

/-- The derivative of `A² a + B² = 1`. -/
private theorem horizontalFactor_sq_add_deriv {a : ℝ} (ha : -1 < a) :
    horizontalFactor a ^ 2 + 2 * a * horizontalFactor a * deriv horizontalFactor a +
      2 * heightProfile a * deriv heightProfile a = 0 := by
  have hA := ((contDiffAt_horizontalFactor ha).differentiableAt (by simp)).hasDerivAt
  have hB := ((contDiffAt_heightProfile ha).differentiableAt (by simp)).hasDerivAt
  have hc : (fun x ↦ horizontalFactor x ^ 2 * id x + heightProfile x ^ 2) =ᶠ[nhds a]
      fun _ ↦ 1 := by
    filter_upwards [Ioi_mem_nhds ha] with x hx using
      horizontalFactor_sq_mul_add_heightProfile_sq hx
  have := (((hA.pow 2).mul (hasDerivAt_id a)).add (hB.pow 2)).unique
    ((hasDerivAt_const a (1 : ℝ)).congr_of_eventuallyEq hc)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, id, mul_one, Pi.pow_apply] at this
  linear_combination this

private theorem deriv_heightProfile_of_one_lt {a : ℝ} (ha : 1 < a) : deriv heightProfile a = 0 := by
  have h : heightProfile =ᶠ[nhds a] fun _ ↦ 1 := by
    filter_upwards [Ioi_mem_nhds ha] with x hx using heightProfile_of_one_le hx.le
  rw [h.deriv_eq, deriv_const]

private theorem heightProfile_lt_one {a : ℝ} (h0 : -1 < a) (h1 : a < 1) : heightProfile a < 1 := by
  have hd := add_discProfile_sq_pos h0
  have hg := discProfile_pos h1
  rw [heightProfile, div_lt_one hd]
  nlinarith

private theorem horizontalFactor_pos {a : ℝ} (h0 : -1 < a) (h1 : a < 1) : 0 < horizontalFactor a :=
  div_pos (by linarith [discProfile_pos h1]) (add_discProfile_sq_pos h0)

private theorem strictMonoOn_heightProfile : StrictMonoOn heightProfile (Icc 0 1) := by
  intro a ha b hb hab
  have hga := discProfile_pos (hab.trans_le hb.2)
  have hgb : 0 ≤ discProfile b := smoothTransition.nonneg _
  have hgab : discProfile b ≤ discProfile a := smoothTransition.monotone (by linarith)
  rw [heightProfile, heightProfile, div_lt_div_iff₀ (add_discProfile_sq_pos (by linarith [ha.1]))
    (add_discProfile_sq_pos (by linarith [hb.1]))]
  have h1 : discProfile b ^ 2 ≤ discProfile a ^ 2 := pow_le_pow_left₀ hgb hgab 2
  have h2 : 0 < discProfile a ^ 2 := by positivity
  nlinarith [ha.1, mul_le_mul_of_nonneg_left h1 ha.1]

private theorem continuousAt_deriv_heightProfile {a : ℝ} (ha : -1 < a) :
    ContinuousAt (deriv heightProfile) a :=
  ((contDiffAt_heightProfile ha).continuousAt_fderiv (by simp)).clm_apply continuousAt_const

/-! ### The collapse map of the plane onto the sphere -/

/-- The squared Euclidean norm `p₁² + p₂²` of a point of the plane. -/
private def radSq (p : ℝ × ℝ) : ℝ := p.1 ^ 2 + p.2 ^ 2

private theorem radSq_nonneg (p : ℝ × ℝ) : 0 ≤ radSq p := by
  unfold radSq
  positivity

private theorem neg_one_lt_radSq (p : ℝ × ℝ) : -1 < radSq p := by
  linarith [radSq_nonneg p]

/-- The collapse map `Φ(p) = (A(a) p, B(a))`, `a = p₁² + p₂²`, read in `ℝ³`. -/
private def collapseVec (p : ℝ × ℝ) : ℝ³ :=
  WithLp.toLp 2 ![horizontalFactor (radSq p) * p.1, horizontalFactor (radSq p) * p.2,
    heightProfile (radSq p)]

private theorem collapseVec_mem_sphere (p : ℝ × ℝ) : collapseVec p ∈ S² := by
  have h : ‖collapseVec p‖ ^ 2 = 1 := by
    have h1 := horizontalFactor_sq_mul_add_heightProfile_sq (neg_one_lt_radSq p)
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [radSq] at h1
    simp only [collapseVec, radSq, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    linear_combination h1
  rw [mem_sphere_zero_iff_norm]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

private theorem hasFDerivAt_radSq (p : ℝ × ℝ) :
    HasFDerivAt radSq ((2 * p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  unfold radSq
  convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).pow 2).add
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2) using 1
  ext <;> simp

private theorem contDiff_collapseVec : ContDiff ℝ ∞ collapseVec := by
  have hr : ContDiff ℝ ∞ radSq := (contDiff_fst.pow 2).add (contDiff_snd.pow 2)
  refine contDiff_iff_contDiffAt.2 fun p ↦ (contDiffAt_piLp 2).2 fun i ↦ ?_
  have hA := (contDiffAt_horizontalFactor (neg_one_lt_radSq p)).comp p hr.contDiffAt
  fin_cases i
  · exact hA.mul contDiffAt_fst
  · exact hA.mul contDiffAt_snd
  · exact (contDiffAt_heightProfile (neg_one_lt_radSq p)).comp p hr.contDiffAt

private theorem fderiv_collapseVec_apply (p v : ℝ × ℝ) :
    fderiv ℝ collapseVec p v = WithLp.toLp 2
      ![deriv horizontalFactor (radSq p) * (2 * (p.1 * v.1 + p.2 * v.2)) * p.1 +
          horizontalFactor (radSq p) * v.1,
        deriv horizontalFactor (radSq p) * (2 * (p.1 * v.1 + p.2 * v.2)) * p.2 +
          horizontalFactor (radSq p) * v.2,
        deriv heightProfile (radSq p) * (2 * (p.1 * v.1 + p.2 * v.2))] := by
  have hd := (contDiff_collapseVec.differentiable (by simp) p).hasFDerivAt
  have hA := ((contDiffAt_horizontalFactor (neg_one_lt_radSq p)).differentiableAt
    (by simp)).hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_radSq p)
  have hB := ((contDiffAt_heightProfile (neg_one_lt_radSq p)).differentiableAt
    (by simp)).hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_radSq p)
  have key (i : Fin 3) (D : ℝ × ℝ →L[ℝ] ℝ) (hD : HasFDerivAt (fun x ↦ collapseVec x i) D p) :
      fderiv ℝ collapseVec p v i = D v :=
    congrArg (· v) (((EuclideanSpace.proj i : ℝ³ →L[ℝ] ℝ).hasFDerivAt.comp p hd).unique hD)
  ext i
  fin_cases i
  · refine (key 0 _ (hA.mul hasFDerivAt_fst)).trans ?_
    simp only [Function.comp_apply, smul_add, add_apply, smul_apply, ContinuousLinearMap.coe_fst',
      smul_eq_mul, ContinuousLinearMap.coe_snd', Fin.zero_eta, cons_val_zero]
    ring
  · refine (key 1 _ (hA.mul hasFDerivAt_snd)).trans ?_
    simp only [Function.comp_apply, smul_add, add_apply, smul_apply, ContinuousLinearMap.coe_snd',
      smul_eq_mul, ContinuousLinearMap.coe_fst', Fin.mk_one, cons_val_one, cons_val_zero]
    ring
  · refine (key 2 _ hB).trans ?_
    simp only [smul_add, add_apply, smul_apply, ContinuousLinearMap.coe_fst', smul_eq_mul,
      ContinuousLinearMap.coe_snd', Fin.reduceFinMk, cons_val]
    ring

/-- The triple product of the collapse map with two of its derivatives: `Φ` pulls the area form
back to `-2 B'(a) dp₁ ∧ dp₂`. -/
private theorem dotProduct_cross_fderiv_collapseVec (p v w : ℝ × ℝ) :
    (collapseVec p).ofLp ⬝ᵥ (fderiv ℝ collapseVec p v).ofLp ⨯₃ (fderiv ℝ collapseVec p w).ofLp =
      -2 * deriv heightProfile (radSq p) * (v.1 * w.2 - v.2 * w.1) := by
  have h1 := horizontalFactor_sq_mul_add_heightProfile_sq (neg_one_lt_radSq p)
  have h2 := horizontalFactor_sq_add_deriv (neg_one_lt_radSq p)
  rw [fderiv_collapseVec_apply, fderiv_collapseVec_apply]
  simp only [collapseVec, radSq, cross_apply, dotProduct, Fin.sum_univ_three, PiLp.toLp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h1 h2 ⊢
  linear_combination (v.1 * w.2 - v.2 * w.1) *
    (-2 * deriv heightProfile (p.1 ^ 2 + p.2 ^ 2) * h1 + heightProfile (p.1 ^ 2 + p.2 ^ 2) * h2)

/-- The collapse map as a map to the sphere. -/
private def collapse (p : ℝ × ℝ) : S² := ⟨collapseVec p, collapseVec_mem_sphere p⟩

private theorem coe_collapse (p : ℝ × ℝ) : (collapse p : ℝ³) = collapseVec p := (rfl)

private theorem continuous_collapse : Continuous collapse :=
  contDiff_collapseVec.continuous.subtype_mk _

private theorem collapse_eq_sphereNorthPole_iff {p : ℝ × ℝ} :
    collapse p = sphereNorthPole 2 ↔ 1 ≤ radSq p := by
  refine ⟨fun h ↦ not_lt.1 fun hp ↦ ?_, fun h ↦ Subtype.ext ?_⟩
  · have h3 := eq_sphereNorthPole_iff.1 h
    simp only [coe_collapse, collapseVec, PiLp.toLp_apply] at h3
    exact (heightProfile_lt_one (neg_one_lt_radSq p) hp).ne (by simpa using h3)
  · rw [coe_collapse, coe_sphereNorthPole]
    ext i
    fin_cases i <;> simp [collapseVec, horizontalFactor_of_one_le h, heightProfile_of_one_le h]

private theorem collapse_injOn : InjOn collapse {p | radSq p < 1} := by
  intro p (hp : radSq p < 1) q (hq : radSq q < 1) h
  have h' (i : Fin 3) := congrArg (fun x : S² ↦ (x : ℝ³) i) h
  simp only [coe_collapse, collapseVec, PiLp.toLp_apply] at h'
  have hr : radSq p = radSq q := strictMonoOn_heightProfile.injOn
    ⟨radSq_nonneg p, hp.le⟩ ⟨radSq_nonneg q, hq.le⟩ (by simpa using h' 2)
  have hA := horizontalFactor_pos (neg_one_lt_radSq p) hp
  have h0 : horizontalFactor (radSq p) * p.1 = horizontalFactor (radSq p) * q.1 := by
    simpa [hr] using h' 0
  have h1 : horizontalFactor (radSq p) * p.2 = horizontalFactor (radSq p) * q.2 := by
    simpa [hr] using h' 1
  exact Prod.ext (mul_left_cancel₀ hA.ne' h0) (mul_left_cancel₀ hA.ne' h1)

/-- The collapse map takes the open unit disc onto the complement of the north pole. -/
private theorem exists_collapse_eq {s : S²} (hs : s ≠ sphereNorthPole 2) :
    ∃ p, radSq p < 1 ∧ collapse p = s := by
  have hs3 : (s : ℝ³) 2 < 1 := apply_last_lt_one_iff_ne_sphereNorthPole.2 hs
  have hnorm : (s : ℝ³) 0 ^ 2 + (s : ℝ³) 1 ^ 2 + (s : ℝ³) 2 ^ 2 = 1 := by
    have := EuclideanSpace.real_norm_sq_eq (s : ℝ³)
    rw [norm_eq_of_mem_sphere, Fin.sum_univ_three] at this
    linarith
  have hge : -1 ≤ (s : ℝ³) 2 := by nlinarith [sq_nonneg ((s : ℝ³) 0), sq_nonneg ((s : ℝ³) 1)]
  -- The height is reached at a radius `a < 1`, and the horizontal part is then rescaled by `A(a)`.
  obtain ⟨a, ha, hta⟩ := intermediate_value_Icc zero_le_one
    (fun a ha ↦ (contDiffAt_heightProfile (by linarith [ha.1])).continuousAt.continuousWithinAt)
    (show (s : ℝ³) 2 ∈ Icc (heightProfile 0) (heightProfile 1) by
      rw [heightProfile_zero, heightProfile_of_one_le le_rfl]
      exact ⟨hge, hs3.le⟩)
  have ha1 : a < 1 := lt_of_le_of_ne ha.2 fun h ↦ by
    rw [h, heightProfile_of_one_le le_rfl] at hta
    exact hs3.ne hta.symm
  have hA := horizontalFactor_pos (by linarith [ha.1]) ha1
  have hid := horizontalFactor_sq_mul_add_heightProfile_sq (by linarith [ha.1] : -1 < a)
  have hrad : radSq ((s : ℝ³) 0 / horizontalFactor a, (s : ℝ³) 1 / horizontalFactor a) = a := by
    simp only [radSq, div_pow]
    field_simp
    rw [hta] at hid
    nlinarith
  refine ⟨((s : ℝ³) 0 / horizontalFactor a, (s : ℝ³) 1 / horizontalFactor a), hrad.symm ▸ ha1,
    Subtype.ext ?_⟩
  rw [coe_collapse]
  ext i
  fin_cases i <;> simp [collapseVec, hrad, hta, mul_div_cancel₀ _ hA.ne']

/-! ### The smooth sphere and its area -/

/-- The affine map `z ↦ 2 z - 1`, carrying the unit square onto `[-1, 1]²`. -/
private def squareCoord (z : ℝ × ℝ) : ℝ × ℝ := (2 * z.1 - 1, 2 * z.2 - 1)

private theorem contDiff_squareCoord : ContDiff ℝ ∞ squareCoord :=
  ((contDiff_const.mul contDiff_fst).sub contDiff_const).prodMk
    ((contDiff_const.mul contDiff_snd).sub contDiff_const)

private theorem fderiv_squareCoord_apply (z w : ℝ × ℝ) :
    fderiv ℝ squareCoord z w = (2 * w.1, 2 * w.2) := by
  have h : HasFDerivAt squareCoord ((2 : ℝ) • ContinuousLinearMap.id ℝ (ℝ × ℝ)) z := by
    unfold squareCoord
    convert ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).const_mul (2 : ℝ)).sub_const 1 |>.prodMk
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_mul (2 : ℝ)).sub_const 1) using 1
    ext <;> simp
  rw [h.fderiv]
  ext <;> simp

/-- The smooth sphere `z ↦ Φ(2 z - 1)` of the plane; it sends the boundary of the unit square to the
north pole. -/
private def collapseSphere (z : ℝ × ℝ) : S² := collapse (squareCoord z)

private theorem contMDiff_collapseSphere : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞ collapseSphere :=
  ContMDiff.codRestrict_sphere (contDiff_collapseVec.comp contDiff_squareCoord).contMDiff
    fun z ↦ collapseVec_mem_sphere (squareCoord z)

private theorem mvfderiv_coe_mfderiv_collapseSphere (z w : ℝ × ℝ) :
    mvfderiv (𝓡 2) ((↑) : S² → ℝ³) (collapseSphere z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) collapseSphere z w) =
        fderiv ℝ collapseVec (squareCoord z) (2 * w.1, 2 * w.2) := by
  rw [← mvfderiv_comp_apply z ((contMDiff_coe_sphere (n := 2) (m := 1) _).mdifferentiableAt
      one_ne_zero) ((contMDiff_collapseSphere z).mdifferentiableAt (by simp)) w,
    mvfderiv_eq_fderiv_apply (((↑) : S² → ℝ³) ∘ collapseSphere) z w]
  have hcomp : ((↑) : S² → ℝ³) ∘ collapseSphere = collapseVec ∘ squareCoord := (rfl)
  rw [hcomp, fderiv_comp z (contDiff_collapseVec.differentiable (by simp) _)
    (contDiff_squareCoord.differentiable (by simp) _), ContinuousLinearMap.comp_apply,
    fderiv_squareCoord_apply]

private theorem sphereAreaForm_apply_mfderiv_collapseSphere (z : ℝ × ℝ) :
    sphereAreaForm.val (collapseSphere z) ![mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) collapseSphere z (1, 0),
      mfderiv 𝓘(ℝ, ℝ × ℝ) (𝓡 2) collapseSphere z (0, 1)] =
        -8 * deriv heightProfile (radSq (squareCoord z)) := by
  rw [← SmoothBundleForm.eval₂_apply, eval₂_sphereAreaForm, mvfderiv_coe_mfderiv_collapseSphere,
    mvfderiv_coe_mfderiv_collapseSphere, collapseSphere, coe_collapse,
    dotProduct_cross_fderiv_collapseVec]
  ring

private theorem one_lt_radSq_squareCoord {z : ℝ × ℝ} (hz : z ∉ Icc ((0 : ℝ), (0 : ℝ)) (1, 1)) :
    1 < radSq (squareCoord z) := by
  simp only [mem_Icc, Prod.le_def, not_and_or, not_le] at hz
  simp only [radSq, squareCoord]
  rcases hz with (h | h) | (h | h) <;>
    nlinarith [sq_nonneg (2 * z.1 - 1), sq_nonneg (2 * z.2 - 1)]

private theorem integral_comp_squareCoord (f : ℝ × ℝ → ℝ) :
    ∫ z, f (squareCoord z) = 4⁻¹ * ∫ p, f p := by
  have h (z : ℝ × ℝ) : squareCoord z = (2 : ℝ) • z - (1, 1) := by
    ext <;> simp [squareCoord]
  simp_rw [h]
  rw [Measure.integral_comp_smul volume (fun y ↦ f (y - (1, 1))) 2, integral_sub_right_eq_self,
    Module.finrank_prod, Module.finrank_self, smul_eq_mul]
  norm_num

/-- `∫₀^∞ B'(2 s) ds = (B(1) - B(0)) / 2 = 1`. -/
private theorem integral_deriv_heightProfile_two_mul :
    ∫ s in Ici (0 : ℝ), deriv heightProfile (2 * s) = 1 := by
  have hsplit : ∫ s in Ici (0 : ℝ), deriv heightProfile (2 * s) =
      ∫ s in Ioc (0 : ℝ) (1 / 2), deriv heightProfile (2 * s) := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun s hs ↦ deriv_heightProfile_of_one_lt ?_
    simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at hs
    linarith [hs.2 hs.1]
  rw [hsplit, ← intervalIntegral.integral_of_le (by norm_num)]
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) (1 / 2),
      HasDerivAt (fun s ↦ heightProfile (2 * s) / 2) (deriv heightProfile (2 * s)) s :=
    fun s hs ↦ by
      rw [uIcc_of_le (by norm_num)] at hs
      refine ((((contDiffAt_heightProfile (a := 2 * s) (by linarith [hs.1])).differentiableAt
        (by simp)).hasDerivAt.comp s ((hasDerivAt_id' s).const_mul 2)).div_const 2).congr_deriv ?_
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv, mul_zero, heightProfile_zero,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, heightProfile_of_one_le le_rfl]
  · norm_num
  · refine ContinuousOn.intervalIntegrable fun s hs ↦ ?_
    rw [uIcc_of_le (by norm_num)] at hs
    exact ((continuousAt_deriv_heightProfile (a := 2 * s) (by linarith [hs.1])).comp
      (continuous_const_mul 2).continuousAt).continuousWithinAt

/-- `∫ B'(p₁² + p₂²) dp = 2π ∫₀^∞ B'(2 s) ds = 2π`: half the squared radius pushes planar Lebesgue
measure forward to `2π` times Lebesgue measure on `[0, ∞)`. -/
private theorem integral_deriv_heightProfile_radSq :
    ∫ p, deriv heightProfile (radSq p) = 2 * π := by
  have h (p : ℝ × ℝ) : deriv heightProfile (radSq p) =
      deriv heightProfile (2 * ((p.1 ^ 2 + p.2 ^ 2) / 2)) := by
    rw [radSq, mul_div_cancel₀ _ two_ne_zero]
  simp_rw [h]
  rw [← integral_map (f := fun s ↦ deriv heightProfile (2 * s))
      (by fun_prop : Measurable fun p : ℝ × ℝ ↦ (p.1 ^ 2 + p.2 ^ 2) / 2).aemeasurable
      ((measurable_deriv heightProfile).comp (measurable_const_mul 2)).aestronglyMeasurable,
    map_volume_half_sq_add_sq, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_deriv_heightProfile_two_mul, smul_eq_mul, mul_one]

/-- **The smooth sphere has area `-4π`.** -/
private theorem rectangleIntegral_collapseSphere :
    rectangleIntegral sphereAreaForm.val collapseSphere (0, 0) (1, 1) = -4 * π := by
  rw [← IsSmoothForm.setIntegral_eq_rectangleIntegral (sphereAreaForm.isSmoothForm.of_le
    (by simp)) (contMDiff_collapseSphere.of_le (by simp)) (by simp [Prod.le_def])]
  simp_rw [sphereAreaForm_apply_mfderiv_collapseSphere]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      rw [deriv_heightProfile_of_one_lt (one_lt_radSq_squareCoord hz), mul_zero],
    integral_comp_squareCoord (fun p ↦ -8 * deriv heightProfile (radSq p)), integral_const_mul,
    integral_deriv_heightProfile_radSq]
  ring

/-! ### From the square to the disc -/

private theorem norm_sq_le_radSq (p : ℝ × ℝ) : ‖p‖ ^ 2 ≤ radSq p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, radSq]
  rcases le_total |p.1| |p.2| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg p.1]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg p.2]

private theorem radSq_smul (c : ℝ) (p : ℝ × ℝ) : radSq (c • p) = c ^ 2 * radSq p := by
  simp only [radSq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The identity of `ℝ × ℝ`, from the sup norm to the Euclidean norm. -/
private def euclideanPlane : (ℝ × ℝ) ≃L[ℝ] WithLp 2 (ℝ × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).symm

/-- The radial homeomorphism of the plane taking the square `‖p‖ ≤ 1` of the sup norm onto the
closed unit disc. -/
private def squareToDisc : ℝ × ℝ ≃ₜ ℝ × ℝ :=
  euclideanPlane.unitBallHomeomorph.trans euclideanPlane.symm.toHomeomorph

private theorem radSq_squareToDisc (p : ℝ × ℝ) :
    radSq (squareToDisc p) = ‖euclideanPlane.unitBallHomeomorph p‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [radSq, squareToDisc, euclideanPlane, ContinuousLinearEquiv.symm_symm,
    Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph,
    WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_fst, WithLp.ofLp_snd, norm_eq_abs, sq_abs]

private theorem one_le_radSq_squareToDisc_iff {p : ℝ × ℝ} :
    1 ≤ radSq (squareToDisc p) ↔ 1 ≤ ‖p‖ := by
  rw [radSq_squareToDisc, one_le_sq_iff_one_le_abs, abs_norm, ← not_lt, ← not_lt,
    ContinuousLinearEquiv.norm_unitBallHomeomorph_lt_one_iff]

/-- `squareToDisc` rescales each point of the plane by a nonnegative factor. -/
private theorem exists_squareToDisc_eq_smul (p : ℝ × ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ squareToDisc p = c • p := by
  rw [squareToDisc, Homeomorph.trans_apply, ContinuousLinearEquiv.unitBallHomeomorph_apply,
    gaugeRescale_def, ContinuousLinearEquiv.coe_toHomeomorph, map_smul,
    ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨_, div_nonneg (gauge_nonneg _) (gauge_nonneg _), rfl⟩

/-! ### The two generalized loops -/

/-- A point of the cube `I²` as a point of the plane. -/
private def cubePoint (y : Fin 2 → I) : ℝ × ℝ := ((y 0 : ℝ), (y 1 : ℝ))

private theorem continuous_cubePoint : Continuous cubePoint := by
  unfold cubePoint
  fun_prop

private theorem norm_squareCoord_cubePoint_le (y : Fin 2 → I) :
    ‖squareCoord (cubePoint y)‖ ≤ 1 := by
  have h (a : I) : |2 * (a : ℝ) - 1| ≤ 1 :=
    abs_le.2 ⟨by linarith [a.property.1], by linarith [a.property.2]⟩
  simpa [squareCoord, cubePoint, Prod.norm_def] using ⟨h (y 0), h (y 1)⟩

private theorem one_le_norm_squareCoord_cubePoint_iff {y : Fin 2 → I} :
    1 ≤ ‖squareCoord (cubePoint y)‖ ↔ y ∈ Cube.boundary (Fin 2) := by
  have h (a : I) : 1 ≤ |2 * (a : ℝ) - 1| ↔ a = 0 ∨ a = 1 := by
    rw [le_abs', Subtype.ext_iff, Subtype.ext_iff, Set.Icc.coe_zero, Set.Icc.coe_one]
    constructor
    · rintro (h | h)
      · exact Or.inl (le_antisymm (by linarith) a.property.1)
      · exact Or.inr (le_antisymm a.property.2 (by linarith))
    · rintro (h | h) <;> norm_num [h]
  simp only [squareCoord, cubePoint, Prod.norm_def, Real.norm_eq_abs, le_max_iff, h,
    Cube.boundary, mem_ofPred_eq, Fin.exists_fin_two]

private theorem norm_squareCoord_cubePoint_of_mem_boundary {y : Fin 2 → I}
    (hy : y ∈ Cube.boundary (Fin 2)) : ‖squareCoord (cubePoint y)‖ = 1 :=
  le_antisymm (norm_squareCoord_cubePoint_le y) (one_le_norm_squareCoord_cubePoint_iff.2 hy)

private theorem squareCoord_cubePoint_injective :
    Function.Injective fun y : Fin 2 → I ↦ squareCoord (cubePoint y) := by
  intro y z h
  simp only [squareCoord, cubePoint, Prod.mk.injEq] at h
  ext i
  fin_cases i
  · simpa using h.1
  · simpa using h.2

/-- The generalized loop of the smooth sphere `collapseSphere`. -/
private def collapseLoop : Ω^ (Fin 2) S² (sphereNorthPole 2) :=
  ⟨⟨fun y ↦ collapseSphere (cubePoint y),
      contMDiff_collapseSphere.continuous.comp continuous_cubePoint⟩,
    fun y hy ↦ collapse_eq_sphereNorthPole_iff.2 (by
      nlinarith [norm_sq_le_radSq (squareCoord (cubePoint y)),
        norm_squareCoord_cubePoint_of_mem_boundary hy])⟩

/-- The generalized loop `y ↦ Φ(squareToDisc (2 y - 1))`, which identifies only points of the
boundary of the cube. -/
private def discLoop : Ω^ (Fin 2) S² (sphereNorthPole 2) :=
  ⟨⟨fun y ↦ collapse (squareToDisc (squareCoord (cubePoint y))), continuous_collapse.comp
      (squareToDisc.continuous.comp (contDiff_squareCoord.continuous.comp continuous_cubePoint))⟩,
    fun _ hy ↦ collapse_eq_sphereNorthPole_iff.2
      (one_le_radSq_squareToDisc_iff.2 (norm_squareCoord_cubePoint_of_mem_boundary hy).ge)⟩

private theorem discLoop_apply (y : Fin 2 → I) :
    discLoop y = collapse (squareToDisc (squareCoord (cubePoint y))) :=
  (rfl)

/-- The straight-line homotopy from the plane map to its composite with `squareToDisc` keeps the
boundary of the cube at the north pole. -/
private theorem homotopic_collapseLoop_discLoop : GenLoop.Homotopic collapseLoop discLoop := by
  refine ⟨{
    toFun := fun q ↦ collapse (((1 : ℝ) - q.1) • squareCoord (cubePoint q.2) +
      (q.1 : ℝ) • squareToDisc (squareCoord (cubePoint q.2)))
    continuous_toFun := by
      have hP : Continuous fun q : I × (Fin 2 → I) ↦ squareCoord (cubePoint q.2) :=
        contDiff_squareCoord.continuous.comp (continuous_cubePoint.comp continuous_snd)
      exact continuous_collapse.comp
        (((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).smul hP).add
          ((continuous_subtypeVal.comp continuous_fst).smul (squareToDisc.continuous.comp hP)))
    map_zero_left := fun y ↦ by simp [collapseLoop, collapseSphere]
    map_one_left := fun y ↦ by simp [discLoop_apply]
    prop' := fun t y hy ↦ ?_ }⟩
  simp only [ContinuousMap.coe_mk]
  rw [collapseLoop.property y hy, collapse_eq_sphereNorthPole_iff]
  -- On the boundary `‖P‖ = 1`, and `squareToDisc P = c • P` lies on the unit circle with
  -- `0 ≤ c ≤ 1`, so the segment from `P` to it stays outside the open disc.
  set P := squareCoord (cubePoint y)
  have hP : ‖P‖ = 1 := norm_squareCoord_cubePoint_of_mem_boundary hy
  have hrP : 1 ≤ radSq P := by nlinarith [norm_sq_le_radSq P]
  obtain ⟨c, hc0, hc⟩ := exists_squareToDisc_eq_smul P
  have hcP : c ^ 2 * radSq P = 1 := by
    rw [← radSq_smul, ← hc, radSq_squareToDisc,
      euclideanPlane.norm_unitBallHomeomorph_eq_one_iff.2 hP, one_pow]
  have hc1 : c ≤ 1 := by nlinarith
  have hk : c ≤ 1 - t + t * c := by nlinarith [t.property.1, t.property.2]
  rw [hc, smul_smul, ← add_smul, radSq_smul]
  calc 1 = c ^ 2 * radSq P := hcP.symm
    _ ≤ (1 - t + t * c) ^ 2 * radSq P := by gcongr

private theorem bijective_toSphere_discLoop : Function.Bijective (GenLoop.toSphere discLoop) := by
  refine ⟨(GenLoop.injective_toSphere_iff _).2 fun y z hyz ↦ ?_,
    (GenLoop.surjective_toSphere_iff _).2 fun s ↦ ?_⟩
  · -- Points sent to the north pole lie on the boundary; elsewhere `collapse` and `squareToDisc`
    -- are injective.
    rw [discLoop_apply, discLoop_apply] at hyz
    by_cases hN : collapse (squareToDisc (squareCoord (cubePoint y))) = sphereNorthPole 2
    · have hN' := hyz ▸ hN
      rw [collapse_eq_sphereNorthPole_iff, one_le_radSq_squareToDisc_iff] at hN hN'
      exact Or.inr ⟨one_le_norm_squareCoord_cubePoint_iff.1 hN,
        one_le_norm_squareCoord_cubePoint_iff.1 hN'⟩
    · have hN' : ¬ collapse (squareToDisc (squareCoord (cubePoint z))) = sphereNorthPole 2 :=
        hyz ▸ hN
      rw [collapse_eq_sphereNorthPole_iff, not_le] at hN hN'
      exact Or.inl (squareCoord_cubePoint_injective
        (squareToDisc.injective (collapse_injOn hN hN' hyz)))
  · by_cases hs : s = sphereNorthPole 2
    · exact ⟨0, hs ▸ discLoop.property 0 ⟨0, Or.inl rfl⟩⟩
    obtain ⟨q, hq, rfl⟩ := exists_collapse_eq hs
    obtain ⟨p, rfl⟩ := squareToDisc.surjective q
    have hp1 : ‖p‖ < 1 := not_le.1 fun h ↦ hq.not_ge (one_le_radSq_squareToDisc_iff.2 h)
    have h1 := abs_lt.1 ((norm_fst_le p).trans_lt hp1)
    have h2 := abs_lt.1 ((norm_snd_le p).trans_lt hp1)
    refine ⟨![⟨(p.1 + 1) / 2, by constructor <;> linarith⟩,
      ⟨(p.2 + 1) / 2, by constructor <;> linarith⟩], ?_⟩
    rw [discLoop_apply]
    congr 2
    ext
    · simp only [squareCoord, cubePoint, Matrix.cons_val_zero]
      ring
    · simp only [squareCoord, cubePoint, Matrix.cons_val_one, Matrix.cons_val_zero]
      ring

/-! ### A generator of `π₂(S²)` and its area -/

/-- The two-sphere is simply connected, in the form of the hypothesis of the Hurewicz theorem. -/
private theorem subsingleton_homotopyGroup_of_lt (k : ℕ) (hk : k < 0 + 2) :
    Subsingleton (HomotopyGroup (Fin k) S² (sphereNorthPole 2)) :=
  subsingleton_homotopyGroup_sphere_of_lt (n := 2) finrank_euclideanSpace_fin (by simpa using hk) _

/-- The class of `discLoop`, a generator of `π₂(S²)`. -/
private def discClass : HomotopyGroup (Fin 2) S² (sphereNorthPole 2) := ⟦discLoop⟧

/-- Every class of `π₂(S²)` is a unique integer multiple of `discClass`. -/
private theorem bijective_zmultiplesHom_discClass :
    Function.Bijective (zmultiplesHom (Additive (π_ 2 S² (sphereNorthPole 2)))
      (Additive.ofMul discClass)) :=
  (isIso_hurewicz_iff_bijective_zmultiplesHom (n := 0) subsingleton_homotopyGroup_of_lt
    discLoop).1 (GenLoop.isIso_hurewicz_of_bijective_toSphere _ bijective_toSphere_discLoop)

private theorem exists_eq_zsmul_discClass (a : HomotopyGroup (Fin 2) S² (sphereNorthPole 2)) :
    ∃ k : ℤ, a = (k • Additive.ofMul discClass).toMul := by
  obtain ⟨k, hk⟩ := bijective_zmultiplesHom_discClass.2 (Additive.ofMul a)
  exact ⟨k, by rw [← zmultiplesHom_apply, hk, toMul_ofMul]⟩

private theorem sphereIntegral_zsmul_discClass (k : ℤ) :
    sphereIntegral sphereAreaForm.val (sphereNorthPole 2) (k • Additive.ofMul discClass).toMul =
      -4 * π * k := by
  have h1 : sphereIntegral sphereAreaForm.val (sphereNorthPole 2) discClass = -4 * π := by
    rw [discClass, ← Quotient.sound homotopic_collapseLoop_discLoop,
      sphereIntegral_mk_of_contMDiff isSmoothForm_sphereAreaForm mextDeriv_sphereAreaForm
        contMDiff_collapseSphere (fun _ ↦ rfl), rectangleIntegral_collapseSphere]
  have h := (sphereIntegralHom (sphereNorthPole 2) isSmoothForm_sphereAreaForm
    mextDeriv_sphereAreaForm).map_zsmul k (Additive.ofMul discClass)
  rw [sphereIntegralHom_apply isSmoothForm_sphereAreaForm mextDeriv_sphereAreaForm,
    sphereIntegralHom_apply isSmoothForm_sphereAreaForm mextDeriv_sphereAreaForm,
    toMul_ofMul, h1] at h
  rw [h, zsmul_eq_mul]
  ring

/-- Moving the base point along a path does not change the sphere integral. -/
private theorem sphereIntegral_sphereAreaForm_eq_comp (x : S²) :
    sphereIntegral sphereAreaForm.val x = sphereIntegral sphereAreaForm.val (sphereNorthPole 2) ∘
      homotopyGroupEquivOfPath (PathConnectedSpace.somePath x (sphereNorthPole 2)) := by
  funext a
  rw [Function.comp_apply, homotopyGroupEquivOfPath_apply, sphereIntegral_homotopyGroupTransport
    isSmoothForm_sphereAreaForm mextDeriv_sphereAreaForm]

/-! ### Main results -/

/-- **A sphere class in the two-sphere is determined by its area.** The integral of the area form
of `S²` over the second homotopy group is injective, at every base point. -/
theorem sphereIntegral_sphereAreaForm_injective (x : S²) :
    Function.Injective (sphereIntegral sphereAreaForm.val x) := by
  rw [sphereIntegral_sphereAreaForm_eq_comp]
  refine Function.Injective.comp (fun a b hab ↦ ?_) (Equiv.injective _)
  obtain ⟨k, rfl⟩ := exists_eq_zsmul_discClass a
  obtain ⟨m, rfl⟩ := exists_eq_zsmul_discClass b
  rw [sphereIntegral_zsmul_discClass, sphereIntegral_zsmul_discClass] at hab
  have hkm : k = m := by exact_mod_cast mul_left_cancel₀ (by positivity : -4 * π ≠ 0) hab
  rw [hkm]

/-- **The areas of the sphere classes in the two-sphere are the multiples of `4π`**, at every base
point. -/
theorem range_sphereIntegral_sphereAreaForm (x : S²) :
    Set.range (sphereIntegral sphereAreaForm.val x) = AddSubgroup.zmultiples (4 * π) := by
  rw [sphereIntegral_sphereAreaForm_eq_comp, (Equiv.surjective _).range_comp]
  ext r
  simp only [Set.mem_range, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨k, rfl⟩ := exists_eq_zsmul_discClass a
    refine ⟨-k, ?_⟩
    rw [sphereIntegral_zsmul_discClass, zsmul_eq_mul]
    push_cast
    ring
  · rintro ⟨m, rfl⟩
    refine ⟨((-m) • Additive.ofMul discClass).toMul, ?_⟩
    rw [sphereIntegral_zsmul_discClass, zsmul_eq_mul]
    push_cast
    ring

/-- **The tautological sphere has area `±4π`.** The class of `TauCeti.sphereGenLoop 2`, which
generates `π₂(S²)`, has area `4π` or `-4π` for the area form of `S²`. -/
theorem abs_sphereIntegral_sphereAreaForm_sphereGenLoop :
    |sphereIntegral sphereAreaForm.val (sphereNorthPole 2) ⟦sphereGenLoop 2⟧| = 4 * π := by
  -- Both classes generate `π₂(S²)` freely, so each is `±1` times the other.
  have hg := (isIso_hurewicz_iff_bijective_zmultiplesHom (n := 0)
    subsingleton_homotopyGroup_of_lt (sphereGenLoop 2)).1 inferInstance
  obtain ⟨k, hk⟩ := bijective_zmultiplesHom_discClass.2
    (Additive.ofMul (⟦sphereGenLoop 2⟧ : HomotopyGroup (Fin 2) S² (sphereNorthPole 2)))
  obtain ⟨m, hm⟩ := hg.2 (Additive.ofMul discClass)
  simp only [zmultiplesHom_apply] at hk hm
  have hkm : k * m = 1 := by
    apply bijective_zmultiplesHom_discClass.1
    simp only [zmultiplesHom_apply]
    rw [mul_comm, mul_smul, hk, hm, one_smul]
  have hS : sphereIntegral sphereAreaForm.val (sphereNorthPole 2)
      (⟦sphereGenLoop 2⟧ : HomotopyGroup (Fin 2) S² (sphereNorthPole 2)) = -4 * π * k := by
    rw [← sphereIntegral_zsmul_discClass, hk]
    exact congrArg (sphereIntegral sphereAreaForm.val (sphereNorthPole 2)) (toMul_ofMul _).symm
  rw [hS, abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hkm with rfl | rfl <;> norm_num

/-- **The area of the two-sphere on `H₂(S²; ℤ)`.** The integral of the area form of `S²` over
`π₂(S², N)`, transported to `H₂(S²; ℤ)` along the Hurewicz isomorphism of the simply connected
sphere. It agrees with the integral of the area form on the Hurewicz class of every sphere, at every
base point (`TauCeti.sphereAreaHom_hurewiczIntHom`). -/
def sphereAreaHom :
    ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of S²) →+
      ℝ :=
  (sphereIntegralHom (sphereNorthPole 2) isSmoothForm_sphereAreaForm
    mextDeriv_sphereAreaForm).comp
    (hurewiczAddEquiv (n := 0) subsingleton_homotopyGroup_of_lt).symm.toAddMonoidHom

/-- **The area homomorphism of the two-sphere is the sphere integral on Hurewicz classes**, at
every base point. This is the hypothesis under which the capped action of the area form descends to
cap classes (`TauCeti.Floer.SphericalCapClass.action`). -/
@[simp]
theorem sphereAreaHom_hurewiczIntHom (x : S²) (a : Additive (HomotopyGroup (Fin 2) S² x)) :
    sphereAreaHom (hurewiczIntHom S² x 1 a) =
      sphereIntegralHom x isSmoothForm_sphereAreaForm mextDeriv_sphereAreaForm a := by
  let γ : Path x (sphereNorthPole 2) := PathConnectedSpace.somePath _ _
  rw [sphereIntegralHom_apply, ← sphereIntegral_homotopyGroupTransport isSmoothForm_sphereAreaForm
    mextDeriv_sphereAreaForm γ,
    ← ofMul_toMul a, ← hurewiczIntHom_homotopyGroupTransport γ a.toMul,
    ← hurewiczAddEquiv_apply_eq_hurewiczIntHom (n := 0) subsingleton_homotopyGroup_of_lt,
    sphereAreaHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, sphereIntegralHom_apply, toMul_ofMul, toMul_ofMul]

/-- **The generator of `H₂(S²; ℤ)` has area `±4π`.** -/
theorem abs_sphereAreaHom_hurewicz_sphereGenLoop :
    |sphereAreaHom ((GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2)).hom 1)| = 4 * π := by
  have h : (GenLoop.hurewicz (ModuleCat.of ℤ ℤ) (sphereGenLoop 2)).hom 1 =
      hurewiczIntHom S² (sphereNorthPole 2) 1
        (Additive.ofMul (⟦sphereGenLoop 2⟧ : HomotopyGroup (Fin 2) S² (sphereNorthPole 2))) :=
    (hurewiczAddEquiv_ofMul_mk (n := 0) subsingleton_homotopyGroup_of_lt _).symm.trans
      (hurewiczAddEquiv_apply_eq_hurewiczIntHom _ _)
  rw [h, sphereAreaHom_hurewiczIntHom, sphereIntegralHom_apply]
  exact abs_sphereIntegral_sphereAreaForm_sphereGenLoop

end TauCeti

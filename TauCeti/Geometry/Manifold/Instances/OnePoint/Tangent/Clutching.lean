/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
public import TauCeti.Topology.Homotopy.Cube.Radius
public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# The first Chern number of the tangent bundle of the Riemann sphere

The holomorphic tangent bundle `TS²` of the Riemann sphere `OnePoint ℂ` is a complex line bundle.
This file computes its clutching number (`TauCeti.clutchingNumber`) on the standard sphere: it is
`2`. This is the clutching description of the evaluation `c₁(TS²)[S²] = 2`; as in
`TauCeti.clutchingNumber`, no comparison with a cohomological first Chern class is made here.

**The standard sphere.** The based sphere `TauCeti.riemannSphereSquare`, a map from the square
`I²` to `OnePoint ℂ` sending the boundary of the square to `∞`, reads a point `y` of the open square
through its position `c = (s - 1/2) + (t - 1/2) i` relative to the centre
(`TauCeti.squareCenterOffset`) and sends it to `c / (1 - 2 max (|Re c|, |Im c|))`. This rescales
each ray from the centre of the square onto a ray from `0` in `ℂ`, preserving directions, and maps
the open square bijectively onto `ℂ` (`TauCeti.bijOn_riemannSphereSquare`), with inverse
`z ↦ z / (1 + 2 max (|Re z|, |Im z|))` read from the centre. The real and imaginary parts of `z`
increase with the two coordinates of the square, so the sphere carries the complex orientation.

**The clutching number.** The clutching number may be computed from any continuous frame of
`TS²` along the sphere (`TauCeti.clutchingNumber_eq_squareBoundaryDegree`). In the affine
coordinate `z`, the frame used here is the vector field `(1 + |z|²) ∂_z` along the open square. In
the inverted coordinate `w = z⁻¹` it reads `-(1 + |z|²) z⁻² ∂_w`
(`OnePoint.trivializationAt_infty_apply_coe`), which tends to `-(conj z / |z|)² ∂_w` as `z → ∞`;
the direction `z / |z|` of `z` is the direction of `c`, which is continuous up to the boundary of
the square. So the frame extends continuously to the boundary, where it is `-(conj ω)² ∂_w` for
the direction `ω = c / |c|` from the centre (`TauCeti.squareCenterDirection`). Read in the
trivialization at `∞`, its clutching function on the boundary is `-ω²`, which turns twice around
the circle as the boundary is run once, since `ω` turns once
(`TauCeti.squareBoundaryDegree_squareCenterDirection`). Hence the clutching number is `2`
(`TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`).

## Main declarations

* `TauCeti.riemannSphereSquare`: the standard sphere `I² / ∂I² → OnePoint ℂ`, based at `∞`.
* `TauCeti.bijOn_riemannSphereSquare`: it maps the open square bijectively onto `ℂ`.
* `TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`: the clutching number of the tangent
  bundle of the Riemann sphere on the standard sphere is `2`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the first Chern class of the tangent bundle of the sphere).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number by clutching, and `c₁(TS²) = 2`).
-/

public section

noncomputable section

open Bundle Set Filter Topology OnePoint
open scoped Manifold unitInterval Topology.Homotopy

namespace TauCeti

/-! ### The standard sphere -/

/-- The sup radius `TauCeti.cubeRadius` of a point of the square is twice the sup norm
`max (|Re c|, |Im c|)` of its offset `c` from the centre. -/
private theorem cubeRadius_eq_two_mul_norm (y : Fin 2 → I) :
    cubeRadius y = 2 * ‖Complex.equivRealProdCLM (squareCenterOffset y)‖ := by
  rw [cubeRadius_def]
  congr 1
  refine le_antisymm ((dist_pi_le_iff (norm_nonneg _)).2 fun i ↦ ?_) ?_
  · fin_cases i <;> simp [dist_apply_cubeCenter]
  · have h₀ := dist_le_pi_dist y (cubeCenter : I^(Fin 2)) 0
    have h₁ := dist_le_pi_dist y (cubeCenter : I^(Fin 2)) 1
    rw [dist_apply_cubeCenter] at h₀ h₁
    simpa using max_le h₀ h₁

/-- The rescaled distance `1 - cubeRadius y` of a point `y` of the square to the boundary, in the
sup norm: `1` at the centre and `0` exactly on the boundary. -/
private def squareDepth (y : Fin 2 → I) : ℝ :=
  1 - cubeRadius y

@[fun_prop]
private theorem continuous_squareDepth : Continuous squareDepth :=
  continuous_const.sub continuous_cubeRadius

private theorem squareDepth_nonneg (y : Fin 2 → I) : 0 ≤ squareDepth y :=
  sub_nonneg.2 (cubeRadius_le_one y)

private theorem squareDepth_eq_zero_iff {y : Fin 2 → I} :
    squareDepth y = 0 ↔ y ∈ Cube.boundary (Fin 2) :=
  sub_eq_zero.trans (eq_comm.trans (cubeRadius_eq_one_iff y))

/-- In the open square, the offset `c` from the centre is recovered from `z = c / d`, for the
depth `d`, as `z / (1 + 2 max (|Re z|, |Im z|))`. -/
private theorem squareCenterOffset_eq_div {y : Fin 2 → I} (hy : squareDepth y ≠ 0) :
    squareCenterOffset y = (squareCenterOffset y / squareDepth y : ℂ) /
      (1 + 2 * ‖Complex.equivRealProdCLM (squareCenterOffset y / squareDepth y : ℂ)‖ : ℝ) := by
  have hd : 0 < squareDepth y := (squareDepth_nonneg y).lt_of_ne' hy
  have h1 : 1 + 2 * ‖Complex.equivRealProdCLM (squareCenterOffset y / squareDepth y : ℂ)‖ =
      (squareDepth y)⁻¹ := by
    rw [div_eq_inv_mul, ← Complex.ofReal_inv, ← Complex.real_smul, map_smul, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.2 hd.le)]
    apply eq_inv_of_mul_eq_one_left
    rw [add_mul, mul_comm (squareDepth y)⁻¹, mul_assoc, mul_assoc, inv_mul_cancel₀ hd.ne',
      squareDepth, cubeRadius_eq_two_mul_norm]
    ring
  rw [h1, Complex.ofReal_inv, div_inv_eq_mul, div_mul_cancel₀ _ (by exact_mod_cast hd.ne')]

/-- Every complex number is `c / d` for the offset `c` and the depth `d ≠ 0` of a point of the
square: the point `1/2 + z / (1 + 2 max (|Re z|, |Im z|))`. -/
private theorem exists_squareCenterOffset_div_eq (z : ℂ) :
    ∃ y : Fin 2 → I, squareDepth y ≠ 0 ∧ squareCenterOffset y / squareDepth y = z := by
  set m := ‖Complex.equivRealProdCLM z‖
  have hm : 0 ≤ m := norm_nonneg _
  set r : ℝ := (1 + 2 * m)⁻¹
  have hr : 0 < r := inv_pos.2 (by linarith)
  have hrm : 2 * (r * m) < 1 := by
    rw [← mul_assoc, mul_comm 2, mul_assoc, inv_mul_lt_one₀ (by linarith)]
    linarith
  have hre : |r * z.re| ≤ r * m := by
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simp [m]) hr.le
  have him : |r * z.im| ≤ r * m := by
    rw [abs_mul, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left (by simp [m]) hr.le
  have hmem (a : ℝ) (ha : |a| < 1 / 2) : 1 / 2 + a ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
  let y : Fin 2 → I := ![⟨_, hmem (r * z.re) (by linarith)⟩, ⟨_, hmem (r * z.im) (by linarith)⟩]
  have hc : squareCenterOffset y = (r : ℂ) * z := by
    apply Complex.ext <;> simp [y]
  have hd : squareDepth y = r := by
    rw [squareDepth, cubeRadius_eq_two_mul_norm, hc, ← Complex.real_smul, map_smul, norm_smul,
      Real.norm_of_nonneg hr.le, eq_comm,
      ← mul_inv_cancel₀ (by linarith : 1 + 2 * m ≠ 0)]
    ring
  refine ⟨y, by rw [hd]; exact hr.ne', ?_⟩
  rw [hc, hd, mul_div_cancel_left₀ _ (by exact_mod_cast hr.ne')]

open Classical in
/-- The standard sphere as a map from the square: `∞` on the boundary, and `c / d` at a point of
the open square with offset `c` from the centre and depth `d`. -/
private def riemannSphereSquareMap (y : Fin 2 → I) : OnePoint ℂ :=
  if squareDepth y = 0 then ∞ else ((squareCenterOffset y / squareDepth y : ℂ) : OnePoint ℂ)

private theorem riemannSphereSquareMap_of_eq_zero {y : Fin 2 → I} (hy : squareDepth y = 0) :
    riemannSphereSquareMap y = ∞ := by
  simp [riemannSphereSquareMap, hy]

private theorem riemannSphereSquareMap_of_ne_zero {y : Fin 2 → I} (hy : squareDepth y ≠ 0) :
    riemannSphereSquareMap y = ((squareCenterOffset y / squareDepth y : ℂ) : OnePoint ℂ) := by
  simp [riemannSphereSquareMap, hy]

/-- Away from the centre of the square, the standard sphere reads `d / c` in the inverted chart,
where `d` is the depth and `c` the offset from the centre. -/
private theorem riemannSphereSquareMap_eq_invChart_symm {y : Fin 2 → I}
    (hy : squareCenterOffset y ≠ 0) :
    riemannSphereSquareMap y = invChart.symm ((squareDepth y : ℂ) / squareCenterOffset y) := by
  by_cases hd : squareDepth y = 0
  · simp [riemannSphereSquareMap_of_eq_zero hd, hd, invChart_symm_zero]
  · rw [riemannSphereSquareMap_of_ne_zero hd, invChart_symm_of_ne_zero (div_ne_zero (by simpa)
      hy), inv_div]

private theorem continuous_riemannSphereSquareMap : Continuous riemannSphereSquareMap := by
  refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
  by_cases hd : squareDepth y₀ = 0
  · -- Near the boundary the sphere is `d / c` read in the inverted chart.
    have hc : squareCenterOffset y₀ ≠ 0 :=
      squareCenterOffset_ne_zero_of_mem (squareDepth_eq_zero_iff.1 hd)
    have hev : ∀ᶠ y in 𝓝 y₀, squareCenterOffset y ≠ 0 :=
      continuous_squareCenterOffset.continuousAt.eventually_ne hc
    refine ContinuousAt.congr ?_ (hev.mono fun y hy ↦
      (riemannSphereSquareMap_eq_invChart_symm hy).symm)
    refine (invChart.continuousOn_symm.continuousAt ?_).comp
      ((Complex.continuous_ofReal.comp continuous_squareDepth).continuousAt.div
        continuous_squareCenterOffset.continuousAt hc)
    simp [invChart_target]
  · -- In the open square the sphere is the finite point `c / d`.
    have hev : ∀ᶠ y in 𝓝 y₀, squareDepth y ≠ 0 :=
      continuous_squareDepth.continuousAt.eventually_ne hd
    refine ContinuousAt.congr ?_ (hev.mono fun y hy ↦ (riemannSphereSquareMap_of_ne_zero hy).symm)
    exact continuous_coe.continuousAt.comp (continuous_squareCenterOffset.continuousAt.div
      (Complex.continuous_ofReal.comp continuous_squareDepth).continuousAt (by simpa using hd))

/-- **The standard sphere** `I² / ∂I² → OnePoint ℂ`, based at `∞`. It sends the boundary of the
square to `∞`, and a point `y` of the open square, with offset `c = squareCenterOffset y` from the
centre, to `c / (1 - 2 max (|Re c|, |Im c|))`. It maps the open square bijectively onto `ℂ`
(`TauCeti.bijOn_riemannSphereSquare`), preserving the directions of rays from the centre. -/
def riemannSphereSquare : Ω^ (Fin 2) (OnePoint ℂ) ∞ :=
  ⟨⟨riemannSphereSquareMap, continuous_riemannSphereSquareMap⟩, fun _ hy ↦
    riemannSphereSquareMap_of_eq_zero (squareDepth_eq_zero_iff.2 hy)⟩

private theorem riemannSphereSquare_apply (y : Fin 2 → I) :
    riemannSphereSquare y = riemannSphereSquareMap y :=
  (rfl)

private theorem riemannSphereSquare_of_squareDepth_eq_zero {y : Fin 2 → I}
    (hy : squareDepth y = 0) : riemannSphereSquare y = ∞ :=
  (riemannSphereSquare_apply y).trans (riemannSphereSquareMap_of_eq_zero hy)

private theorem riemannSphereSquare_of_squareDepth_ne_zero {y : Fin 2 → I}
    (hy : squareDepth y ≠ 0) :
    riemannSphereSquare y = ((squareCenterOffset y / squareDepth y : ℂ) : OnePoint ℂ) :=
  (riemannSphereSquare_apply y).trans (riemannSphereSquareMap_of_ne_zero hy)

/-- The standard sphere sends the boundary of the square to `∞`. -/
@[simp]
theorem riemannSphereSquare_apply_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    riemannSphereSquare y = ∞ := by
  rw [riemannSphereSquare_of_squareDepth_eq_zero (squareDepth_eq_zero_iff.2 hy)]

/-- At a point of the open square, the standard sphere is `c / (1 - 2 max (|Re c|, |Im c|))`, for
the offset `c` from the centre; the maximum is the sup norm of `c` read in `ℝ × ℝ`. -/
theorem riemannSphereSquare_apply_of_notMem {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    riemannSphereSquare y = ((squareCenterOffset y /
      (1 - 2 * ‖Complex.equivRealProdCLM (squareCenterOffset y)‖ : ℝ) : ℂ) : OnePoint ℂ) := by
  rw [riemannSphereSquare_of_squareDepth_ne_zero (mt squareDepth_eq_zero_iff.1 hy), squareDepth,
    cubeRadius_eq_two_mul_norm]

/-- **The standard sphere maps the open square bijectively onto `ℂ`.** -/
theorem bijOn_riemannSphereSquare :
    BijOn riemannSphereSquare (Cube.boundary (Fin 2))ᶜ (range ((↑) : ℂ → OnePoint ℂ)) := by
  have hd {y : Fin 2 → I} (hy : y ∈ (Cube.boundary (Fin 2))ᶜ) : squareDepth y ≠ 0 :=
    mt squareDepth_eq_zero_iff.1 hy
  refine ⟨fun y hy ↦ ⟨_, (riemannSphereSquare_of_squareDepth_ne_zero (hd hy)).symm⟩,
    fun y hy y' hy' h ↦ ?_, ?_⟩
  · -- Injectivity: the offset from the centre is recovered from the image, hence the point.
    rw [riemannSphereSquare_of_squareDepth_ne_zero (hd hy),
      riemannSphereSquare_of_squareDepth_ne_zero (hd hy'), OnePoint.coe_eq_coe] at h
    have hc : squareCenterOffset y = squareCenterOffset y' := by
      rw [squareCenterOffset_eq_div (hd hy), squareCenterOffset_eq_div (hd hy'), h]
    ext i
    fin_cases i
    · simpa using congrArg Complex.re hc
    · simpa using congrArg Complex.im hc
  · rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy, hz⟩ := exists_squareCenterOffset_div_eq z
    exact ⟨y, mt squareDepth_eq_zero_iff.2 hy,
      by rw [riemannSphereSquare_of_squareDepth_ne_zero hy, hz]⟩

/-! ### A frame of the tangent bundle along the standard sphere -/

/-- The positive number `d² + |c|²` for the depth `d` and the offset `c` of a point of the
square. -/
private def frameNumerator (y : Fin 2 → I) : ℝ :=
  squareDepth y ^ 2 + ‖squareCenterOffset y‖ ^ 2

private theorem frameNumerator_pos (y : Fin 2 → I) : 0 < frameNumerator y := by
  by_cases hd : squareDepth y = 0
  · have hc := squareCenterOffset_ne_zero_of_mem (squareDepth_eq_zero_iff.1 hd)
    unfold frameNumerator
    positivity
  · unfold frameNumerator
    positivity

open Classical in
/-- The coefficient of the frame `(1 + |z|²) ∂_z` along the standard sphere, read in the preferred
chart of its point: `(1 + |z|²) = (d² + |c|²) / d²` in the affine chart at `z = c / d`, and its
limit `-|c|² / c²` in the inverted chart at `∞`. -/
private def frameCoeff (y : Fin 2 → I) : ℂ :=
  if squareDepth y = 0 then -(frameNumerator y : ℂ) / squareCenterOffset y ^ 2
  else (frameNumerator y : ℂ) / (squareDepth y : ℂ) ^ 2

private theorem frameCoeff_ne_zero (y : Fin 2 → I) : frameCoeff y ≠ 0 := by
  have hN : (frameNumerator y : ℂ) ≠ 0 := by exact_mod_cast (frameNumerator_pos y).ne'
  unfold frameCoeff
  split_ifs with hd
  · exact div_ne_zero (neg_ne_zero.2 hN)
      (pow_ne_zero _ (squareCenterOffset_ne_zero_of_mem (squareDepth_eq_zero_iff.1 hd)))
  · exact div_ne_zero hN (pow_ne_zero _ (by exact_mod_cast hd))

/-- The frame `(1 + |z|²) ∂_z` of the tangent bundle along the standard sphere. -/
private def frame (y : Fin 2 → I) : ℂ ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ) (riemannSphereSquare y) :=
  ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (frameCoeff y) (frameCoeff_ne_zero y))

private theorem frame_apply (y : Fin 2 → I) (v : ℂ) : frame y v = v * frameCoeff y :=
  ContinuousLinearEquiv.unitsEquivAut_apply (R := ℂ) _ _

/-- Transport the value of a trivialization of the tangent bundle along an equality `x = x'` of
base points. The fibre `TangentSpace 𝓘(ℂ, ℂ) x` of the point `⟨x, w⟩` of the total space depends
on `x`, so `rw` cannot rewrite `x` there directly, for instance from `riemannSphereSquare y` to its
value: the motive would not be type-correct. Once the vector `w` is read as an element of `ℂ`, this
lemma rewrites the base point together with the vector. -/
private theorem trivializationAt_snd_congr (b : OnePoint ℂ) {x x' : OnePoint ℂ} (h : x = x')
    (w : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) b ⟨x, w⟩).2 =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) b ⟨x', w⟩).2 := by
  subst h
  rfl

/-- In the open square, the frame reads as `v (d² + |c|²) / d²` in the affine chart. -/
private theorem trivializationAt_coe_frame {y : Fin 2 → I} (hy : squareDepth y ≠ 0) (z₀ : ℂ)
    (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z₀ : OnePoint ℂ)
      ⟨riemannSphereSquare y, frame y v⟩).2 =
        v * ((frameNumerator y : ℂ) / (squareDepth y : ℂ) ^ 2) := by
  rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_of_squareDepth_ne_zero hy),
    trivializationAt_coe_apply_coe]
  simp [frameCoeff, hy]

/-- Away from the centre of the square, the frame reads as `-v (d² + |c|²) / c²` in the inverted
chart at `∞`. -/
private theorem trivializationAt_infty_frame {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0)
    (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ)
      ⟨riemannSphereSquare y, frame y v⟩).2 =
        v * (-(frameNumerator y : ℂ) / squareCenterOffset y ^ 2) := by
  by_cases hd : squareDepth y = 0
  · rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_of_squareDepth_eq_zero hd),
      trivializationAt_infty_apply_infty]
    simp [frameCoeff, hd]
  · have hd' : (squareDepth y : ℂ) ≠ 0 := by exact_mod_cast hd
    have hz : (squareCenterOffset y / squareDepth y : ℂ) ≠ 0 := div_ne_zero hy hd'
    rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_of_squareDepth_ne_zero hd),
      trivializationAt_infty_apply_coe hz]
    simp only [frameCoeff, hd, ite_false]
    field_simp

/-- **The frame is continuous** as a map into the total space of the tangent bundle, including at
the boundary of the square, where it extends `(1 + |z|²) ∂_z` from the open square. -/
private theorem continuous_frame :
    Continuous fun q : (Fin 2 → I) × ℂ ↦
      TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ)) (riemannSphereSquare q.1) (frame q.1 q.2) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ (FiberBundle.continuousAt_totalSpace ℂ _).2
    ⟨(riemannSphereSquare.1.continuous.comp continuous_fst).continuousAt, ?_⟩
  have hN : Continuous fun y ↦ (frameNumerator y : ℂ) := by
    unfold frameNumerator
    fun_prop
  by_cases hd : squareDepth q₀.1 = 0
  · -- Near the boundary, read the frame in the inverted chart at `∞`.
    have hc : squareCenterOffset q₀.1 ≠ 0 :=
      squareCenterOffset_ne_zero_of_mem (squareDepth_eq_zero_iff.1 hd)
    have hproj : (TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ)) (riemannSphereSquare q₀.1)
        (frame q₀.1 q₀.2)).proj = ∞ :=
      riemannSphereSquare_of_squareDepth_eq_zero hd
    rw [hproj]
    have hev : ∀ᶠ q in 𝓝 q₀, squareCenterOffset q.1 ≠ 0 :=
      (continuous_squareCenterOffset.comp continuous_fst).continuousAt.eventually_ne hc
    refine ContinuousAt.congr ?_ (hev.mono fun q hq ↦ (trivializationAt_infty_frame hq q.2).symm)
    exact continuous_snd.continuousAt.mul (((hN.comp continuous_fst).continuousAt.neg).div
      ((continuous_squareCenterOffset.comp continuous_fst).continuousAt.pow 2)
      (pow_ne_zero _ hc))
  · -- In the open square, read the frame in the affine chart.
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, (TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ))
        (riemannSphereSquare q₀.1) (frame q₀.1 q₀.2)).proj = z₀ :=
      ⟨_, riemannSphereSquare_of_squareDepth_ne_zero hd⟩
    rw [hz₀]
    have hev : ∀ᶠ q in 𝓝 q₀, squareDepth q.1 ≠ 0 :=
      (continuous_squareDepth.comp continuous_fst).continuousAt.eventually_ne hd
    refine ContinuousAt.congr ?_ (hev.mono fun q hq ↦ (trivializationAt_coe_frame hq z₀ q.2).symm)
    have hD : Continuous fun q : (Fin 2 → I) × ℂ ↦ (squareDepth q.1 : ℂ) ^ 2 := by fun_prop
    exact continuous_snd.continuousAt.mul ((hN.comp continuous_fst).continuousAt.div
      hD.continuousAt (pow_ne_zero _ (by exact_mod_cast hd)))

/-! ### The clutching number -/

/-- On the boundary of the square, the clutching function of the frame in the trivialization at
`∞` is `-ω²`, for the direction `ω` of the point from the centre. -/
private theorem clutchingFunction_frame {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    clutchingFunction riemannSphereSquare frame (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) ∞) y =
      -(squareCenterDirection y * squareCenterDirection y) := by
  have hc := squareCenterOffset_ne_zero_of_mem hy
  have hd := squareDepth_eq_zero_iff.2 hy
  have hb : riemannSphereSquare y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) ∞).baseSet := by
    rw [riemannSphereSquare_apply_of_mem hy]
    exact FiberBundle.mem_baseSet_trivializationAt' _
  -- The transition is multiplication by `B = -|c|² / c²`, a point of the circle.
  set B : ℂ := -(frameNumerator y : ℂ) / squareCenterOffset y ^ 2
  have hdet : LinearMap.det (((frame y).trans ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ))
      ∞).continuousLinearEquivAt ℂ _ hb)).toLinearEquiv : ℂ →ₗ[ℂ] ℂ) = B := by
    rw [LinearMap.det_ring]
    simpa [B] using trivializationAt_infty_frame hc 1
  have hN : (frameNumerator y : ℂ) = (‖squareCenterOffset y‖ : ℂ) ^ 2 := by
    simp [frameNumerator, hd]
  have hB : ‖B‖ = 1 := by
    simp only [B, hN, norm_div, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_norm]
    exact div_self (pow_ne_zero _ (norm_ne_zero_iff.2 hc))
  rw [clutchingFunction_of_mem hb]
  refine Circle.ext ?_
  rw [Circle.coe_inv, ContinuousLinearEquiv.coe_normalizedDet, hdet, hB, Complex.ofReal_one,
    div_one, Circle.coe_neg, Circle.coe_mul, coe_squareCenterDirection hc]
  simp only [B, hN]
  field_simp

/-- **The clutching first Chern number of the Riemann sphere.** The clutching number of the
holomorphic tangent bundle of the Riemann sphere on the standard sphere is `2`. This is the
clutching description of `c₁(TS²)[S²] = 2`; it is not compared here with a cohomological `c₁`. -/
theorem clutchingNumber_tangentSpace_riemannSphereSquare :
    clutchingNumber ℂ (TangentSpace 𝓘(ℂ, ℂ)) riemannSphereSquare = 2 := by
  rw [clutchingNumber_eq_squareBoundaryDegree riemannSphereSquare _
    (FiberBundle.mem_baseSet_trivializationAt' ∞) continuous_frame,
    squareBoundaryDegree_congr
      (Γ' := (fun _ ↦ -1) * (squareCenterDirection * squareCenterDirection))
      fun y hy ↦ by simp [clutchingFunction_frame hy],
    squareBoundaryDegree_mul continuousOn_const (continuousOn_squareCenterDirection.mul
      continuousOn_squareCenterDirection),
    squareBoundaryDegree_mul continuousOn_squareCenterDirection continuousOn_squareCenterDirection,
    squareBoundaryDegree_const, squareBoundaryDegree_squareCenterDirection]
  rfl

end TauCeti

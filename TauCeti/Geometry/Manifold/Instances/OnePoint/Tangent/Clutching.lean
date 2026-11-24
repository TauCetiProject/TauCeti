/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Tangent.Basic
public import TauCeti.Topology.Homotopy.Cube.OnePoint
public import TauCeti.Topology.VectorBundle.Complex.Clutching

/-!
# The first Chern number of the tangent bundle of the Riemann sphere

The holomorphic tangent bundle `TS²` of the Riemann sphere `OnePoint ℂ` is a complex line bundle.
This file computes its clutching number (`TauCeti.clutchingNumber`) on the standard sphere: it is
`2`. This is the clutching description of the evaluation `c₁(TS²)[S²] = 2`; as in
`TauCeti.clutchingNumber`, no comparison with a cohomological first Chern class is made here.

**The standard sphere.** The based sphere `TauCeti.riemannSphereSquare`, a map from the square
`I²` to `OnePoint ℂ` sending the boundary of the square to `∞`, is the collapse
`TauCeti.cubeToOnePoint` of the boundary of the square, read in `ℂ` through `x ↦ x 0 + x 1 i`. It
sends a point `y` of the open square, with offset `c = (s - 1/2) + (t - 1/2) i` from the centre
(`TauCeti.squareCenterOffset`) and sup radius `r = 2 max (|Re c|, |Im c|) < 1`
(`TauCeti.cubeRadius`), to `z = 2 c / √(1 - r²)`. This rescales each ray from the centre of the
square onto a ray from `0` in `ℂ`, preserving directions, and maps the open square bijectively onto
`ℂ` (`TauCeti.bijOn_riemannSphereSquare`). The real and imaginary parts of `z` increase with the
two coordinates of the square, so the sphere carries the complex orientation.

**The clutching number.** The clutching number may be computed from any continuous frame of
`TS²` along the sphere (`TauCeti.clutchingNumber_eq_squareBoundaryDegree`). In the affine
coordinate `z`, the frame used here is the vector field `(1 - r²)⁻¹ ∂_z` along the open square, that
is `(1 + ‖z‖²) ∂_z` for the sup norm `‖z‖ = max (|Re z|, |Im z|)`. In the inverted coordinate
`w = z⁻¹` it reads `-(1 - r²)⁻¹ z⁻² ∂_w = -(2 c)⁻² ∂_w`
(`OnePoint.trivializationAt_infty_apply_coe`), which is continuous up to the boundary of the
square. So the frame extends continuously to the boundary, where it is `-(2 c)⁻² ∂_w`. Read in the
trivialization at `∞`, its clutching function on the boundary is the inverse of the normalized
coefficient `-|c|² / c²`, that is `-ω²` for the direction `ω = c / |c|` from the centre
(`TauCeti.squareCenterDirection`). It turns twice around the circle as the boundary is run once,
since `ω` turns once (`TauCeti.squareBoundaryDegree_squareCenterDirection`). Hence the clutching
number is `2` (`TauCeti.clutchingNumber_tangentSpace_riemannSphereSquare`).

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

/-- The plane `Fin 2 → ℝ` of the square read as `ℂ`, through `x ↦ x 0 + x 1 i`. -/
private def squarePlaneEquiv : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm

/-- Read in `ℂ`, the image of a point of the square in the closed unit ball of the sup norm is
twice its offset from the centre. -/
private theorem squarePlaneEquiv_cubeHomeomorphClosedBall (y : Fin 2 → I) :
    squarePlaneEquiv (cubeHomeomorphClosedBall (Fin 2) y) = 2 * squareCenterOffset y := by
  apply Complex.ext <;> simp [squarePlaneEquiv, Complex.equivRealProdCLM_symm_apply] <;> ring

/-- The scale `(1 - r²)^(-1/2)` of the standard sphere at a point of the square of sup radius
`r`. -/
def sphereScale (y : Fin 2 → I) : ℝ :=
  (√(1 - cubeRadius y ^ 2))⁻¹

/-- The value of the scale of the standard sphere. -/
theorem sphereScale_def (y : Fin 2 → I) : sphereScale y = (√(1 - cubeRadius y ^ 2))⁻¹ :=
  (rfl)

/-- Off the boundary of the square, the scale of the standard sphere is nonzero. -/
theorem sphereScale_ne_zero {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    sphereScale y ≠ 0 :=
  inv_ne_zero (Real.sqrt_ne_zero'.2 (one_sub_cubeRadius_sq_pos hy))

/-- Off the boundary of the square, the scale of the standard sphere is continuous. -/
theorem continuousAt_sphereScale {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    ContinuousAt sphereScale y :=
  ((continuous_const.sub (continuous_cubeRadius.pow 2)).sqrt.continuousAt).inv₀
    (Real.sqrt_ne_zero'.2 (one_sub_cubeRadius_sq_pos hy))

/-- **The standard sphere** `I² / ∂I² → OnePoint ℂ`, based at `∞`: the collapse
`TauCeti.cubeToOnePoint` of the boundary of the square, read in `ℂ` through `x ↦ x 0 + x 1 i`. It
sends a point `y` of the open square, with offset `c = squareCenterOffset y` from the centre and
sup radius `r = cubeRadius y`, to `2 c / √(1 - r²)`. It maps the open square bijectively onto `ℂ`
(`TauCeti.bijOn_riemannSphereSquare`), preserving the directions of rays from the centre. -/
def riemannSphereSquare : Ω^ (Fin 2) (OnePoint ℂ) ∞ :=
  ⟨(Homeomorph.onePointCongr squarePlaneEquiv.toHomeomorph :
      C(OnePoint (Fin 2 → ℝ), OnePoint ℂ)).comp (cubeToOnePoint (Fin 2)),
    fun y hy ↦ by simp [(cubeToOnePoint_eq_infty_iff y).2 hy]⟩

private theorem riemannSphereSquare_apply (y : Fin 2 → I) :
    riemannSphereSquare y =
      Homeomorph.onePointCongr squarePlaneEquiv.toHomeomorph (cubeToOnePoint (Fin 2) y) :=
  (rfl)

/-- The standard sphere sends the boundary of the square to `∞`. -/
@[simp]
theorem riemannSphereSquare_apply_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    riemannSphereSquare y = ∞ :=
  riemannSphereSquare.property y hy

/-- At a point of the open square, the standard sphere is `s * (2 c)`, for the offset `c` from the
centre and the scale `s = sphereScale y`. -/
theorem riemannSphereSquare_eq_sphereScale {y : Fin 2 → I}
    (hy : y ∉ Cube.boundary (Fin 2)) :
    riemannSphereSquare y = ((sphereScale y * (2 * squareCenterOffset y) : ℂ) : OnePoint ℂ) := by
  have hr : ‖(cubeHomeomorphClosedBall (Fin 2) y : Fin 2 → ℝ)‖ < 1 := by
    rw [norm_cubeHomeomorphClosedBall]
    exact (cubeRadius_le_one y).lt_of_ne (mt (cubeRadius_eq_one_iff y).1 hy)
  rw [riemannSphereSquare_apply, cubeToOnePoint_apply, unitBallToOnePoint_apply_of_norm_lt hr]
  simp [OpenPartialHomeomorph.univUnitBall_symm_apply, norm_cubeHomeomorphClosedBall,
    squarePlaneEquiv_cubeHomeomorphClosedBall, sphereScale_def]

/-- At a point of the open square, the standard sphere is `2 c / √(1 - r²)`, for the offset `c`
from the centre and the sup radius `r = cubeRadius y`. -/
theorem riemannSphereSquare_apply_of_notMem {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    riemannSphereSquare y =
      ((2 * squareCenterOffset y / (√(1 - cubeRadius y ^ 2) : ℝ) : ℂ) : OnePoint ℂ) := by
  rw [riemannSphereSquare_eq_sphereScale hy, sphereScale_def, Complex.ofReal_inv, inv_mul_eq_div]

/-- **The standard sphere maps the open square bijectively onto `ℂ`.** -/
theorem bijOn_riemannSphereSquare :
    BijOn riemannSphereSquare (Cube.boundary (Fin 2))ᶜ (range ((↑) : ℂ → OnePoint ℂ)) := by
  refine ⟨fun y hy ↦ ⟨_, (riemannSphereSquare_eq_sphereScale hy).symm⟩,
    fun y hy y' _ h ↦ ?_, ?_⟩
  · rw [riemannSphereSquare_apply, riemannSphereSquare_apply] at h
    exact (eq_or_mem_boundary_of_cubeToOnePoint_eq ((Homeomorph.injective _) h)).resolve_right
      fun h' ↦ hy h'.1
  · rintro _ ⟨z, rfl⟩
    obtain ⟨y, hy⟩ := cubeToOnePoint_surjective (N := Fin 2) (squarePlaneEquiv.symm z)
    refine ⟨y, fun hb ↦ ?_, ?_⟩
    · rw [(cubeToOnePoint_eq_infty_iff y).2 hb] at hy
      exact OnePoint.infty_ne_coe _ hy
    · rw [riemannSphereSquare_apply, hy]
      simp

/-! ### A frame of the tangent bundle along the standard sphere -/

open Classical in
/-- The coefficient of the frame `(1 + ‖z‖²) ∂_z` along the standard sphere, read in the preferred
chart of its point: `(1 - r²)⁻¹ = s²` in the affine chart at a point of the open square, for the
scale `s = (1 - r²)^(-1/2)` of the sphere, and `-(2 c)⁻²` in the inverted chart at `∞`. -/
private def frameCoeff (y : Fin 2 → I) : ℂ :=
  if y ∈ Cube.boundary (Fin 2) then -((2 * squareCenterOffset y) ^ 2)⁻¹
  else (sphereScale y : ℂ) ^ 2

private theorem frameCoeff_ne_zero (y : Fin 2 → I) : frameCoeff y ≠ 0 := by
  unfold frameCoeff
  split_ifs with hy
  · exact neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _
      (mul_ne_zero two_ne_zero (squareCenterOffset_ne_zero_of_mem hy))))
  · exact pow_ne_zero _ (by exact_mod_cast sphereScale_ne_zero hy)

/-- The frame `(1 + ‖z‖²) ∂_z` of the tangent bundle along the standard sphere. -/
private def frame (y : Fin 2 → I) : ℂ ≃L[ℂ] TangentSpace 𝓘(ℂ, ℂ) (riemannSphereSquare y) :=
  ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (frameCoeff y) (frameCoeff_ne_zero y))

private theorem frame_apply (y : Fin 2 → I) (v : ℂ) : frame y v = v * frameCoeff y :=
  ContinuousLinearEquiv.unitsEquivAut_apply (R := ℂ) _ _

/-- In the open square, the frame reads as `v s²` in the affine chart, for the scale `s`. -/
private theorem trivializationAt_coe_frame {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2))
    (z₀ : ℂ) (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (z₀ : OnePoint ℂ)
      ⟨riemannSphereSquare y, frame y v⟩).2 = v * (sphereScale y : ℂ) ^ 2 := by
  rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_eq_sphereScale hy),
    trivializationAt_coe_apply_coe]
  simp [frameCoeff, hy]

/-- Away from the centre of the square, the frame reads as `-v (2 c)⁻²` in the inverted chart at
`∞`. -/
private theorem trivializationAt_infty_frame {y : Fin 2 → I} (hy : squareCenterOffset y ≠ 0)
    (v : ℂ) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) (∞ : OnePoint ℂ)
      ⟨riemannSphereSquare y, frame y v⟩).2 = v * -((2 * squareCenterOffset y) ^ 2)⁻¹ := by
  by_cases hb : y ∈ Cube.boundary (Fin 2)
  · rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_apply_of_mem hb),
      trivializationAt_infty_apply_infty]
    simp [frameCoeff, hb]
  · have hs : (sphereScale y : ℂ) ≠ 0 := by exact_mod_cast sphereScale_ne_zero hb
    rw [frame_apply, trivializationAt_snd_congr _ (riemannSphereSquare_eq_sphereScale hb),
      trivializationAt_infty_apply_coe (mul_ne_zero hs (mul_ne_zero two_ne_zero hy))]
    simp only [frameCoeff, hb, ite_false]
    field_simp

/-- **The frame is continuous** as a map into the total space of the tangent bundle, including at
the boundary of the square, where it extends `(1 + ‖z‖²) ∂_z` from the open square. -/
private theorem continuous_frame :
    Continuous fun q : (Fin 2 → I) × ℂ ↦
      TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ)) (riemannSphereSquare q.1) (frame q.1 q.2) := by
  refine continuous_iff_continuousAt.2 fun q₀ ↦ (FiberBundle.continuousAt_totalSpace ℂ _).2
    ⟨(riemannSphereSquare.val.continuous.comp continuous_fst).continuousAt, ?_⟩
  by_cases hb : q₀.1 ∈ Cube.boundary (Fin 2)
  · -- Near the boundary, read the frame in the inverted chart at `∞`.
    have hc : squareCenterOffset q₀.1 ≠ 0 := squareCenterOffset_ne_zero_of_mem hb
    have hproj : (TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ)) (riemannSphereSquare q₀.1)
        (frame q₀.1 q₀.2)).proj = ∞ :=
      riemannSphereSquare_apply_of_mem hb
    rw [hproj]
    have hev : ∀ᶠ q in 𝓝 q₀, squareCenterOffset q.1 ≠ 0 :=
      (continuous_squareCenterOffset.comp continuous_fst).continuousAt.eventually_ne hc
    refine ContinuousAt.congr ?_ (hev.mono fun q hq ↦ (trivializationAt_infty_frame hq q.2).symm)
    have hc2 : (2 * squareCenterOffset q₀.1) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hc)
    exact continuous_snd.continuousAt.mul (((continuous_const.mul
      (continuous_squareCenterOffset.comp continuous_fst)).pow 2).continuousAt.inv₀ hc2).neg
  · -- In the open square, read the frame in the affine chart.
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, (TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ, ℂ))
        (riemannSphereSquare q₀.1) (frame q₀.1 q₀.2)).proj = z₀ :=
      ⟨_, riemannSphereSquare_eq_sphereScale hb⟩
    rw [hz₀]
    have hev : ∀ᶠ q in 𝓝 q₀, q.1 ∉ Cube.boundary (Fin 2) :=
      continuous_fst.continuousAt.preimage_mem_nhds
        (Cube.isClosed_boundary.isOpen_compl.mem_nhds hb)
    refine ContinuousAt.congr ?_ (hev.mono fun q hq ↦ (trivializationAt_coe_frame hq z₀ q.2).symm)
    exact continuous_snd.continuousAt.mul ((Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_sphereScale hb).comp continuous_fst.continuousAt)).pow 2)

/-! ### The clutching number -/

/-- On the boundary of the square, the clutching function of the frame in the trivialization at
`∞` is `-ω²`, for the direction `ω` of the point from the centre. -/
private theorem clutchingFunction_frame {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    clutchingFunction riemannSphereSquare frame (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) ∞) y =
      -(squareCenterDirection y * squareCenterDirection y) := by
  have hc := squareCenterOffset_ne_zero_of_mem hy
  have hb : riemannSphereSquare y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ)) ∞).baseSet := by
    rw [riemannSphereSquare_apply_of_mem hy]
    exact FiberBundle.mem_baseSet_trivializationAt' _
  -- The transition is multiplication by `B = -(2 c)⁻²`, whose direction is `-|c|² / c²`.
  set B : ℂ := -((2 * squareCenterOffset y) ^ 2)⁻¹
  have hdet : LinearMap.det (((frame y).trans ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ))
      ∞).continuousLinearEquivAt ℂ _ hb)).toLinearEquiv : ℂ →ₗ[ℂ] ℂ) = B := by
    rw [LinearMap.det_ring]
    simpa [B] using trivializationAt_infty_frame hc 1
  have hB : (‖B‖ : ℂ) = (((2 * ‖squareCenterOffset y‖ : ℝ) : ℂ) ^ 2)⁻¹ := by
    simp [B]
  have hn : ((‖squareCenterOffset y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hc
  rw [clutchingFunction_of_mem hb]
  refine Circle.ext ?_
  rw [Circle.coe_inv, ContinuousLinearEquiv.coe_normalizedDet, hdet, hB, Circle.coe_neg,
    Circle.coe_mul, coe_squareCenterDirection hc]
  simp only [B]
  field_simp
  push_cast
  ring

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
  norm_num

end TauCeti

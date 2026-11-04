/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Outward
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary
public import Mathlib.Topology.Path
public import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Topology.Circle.Arc
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The counterclockwise loop on the actual disk boundary

The circle exponential is transported through the analytic identification of the sphere with
the intrinsic disk boundary. Its closed path covers that boundary once, with a single seam.
-/

public section

noncomputable section

open Set Metric Real
open scoped Manifold ContDiff Topology

namespace TauCeti.Green

attribute [local instance] finrank_real_complex_fact'

local notation "D" => closedBall (0 : ℂ) 1
local notation "B" => ModelWithCorners.boundary (I := (𝓡∂ (1 + 1))) D
local notation "S" => (sphereDiffeomorphBoundaryClosedBall (E := ℂ) (n := 1) :
  Circle ≃ₘ^ω⟮𝓡 1, 𝓡 1⟯ B)

local instance : IsManifold (𝓡 1) ω B := isManifold_boundary (n := 1) D (by simp)

private theorem exp_pi_eq_exp_neg_pi : Circle.exp π = Circle.exp (-π) := by
  convert Circle.periodic_exp (-π) using 1
  congr 1
  ring

/-- A counterclockwise unit-disk boundary path, based at the circle-exponential seam of angle
`-π`. Its values lie in the actual induced boundary manifold. -/
def unitDiskBoundaryLoop : Path (S (Circle.exp (-π))) (S (Circle.exp (-π))) where
  toFun t := S (Circle.exp (2 * π * (t : ℝ) - π))
  continuous_toFun := (S).continuous.comp <| Circle.exp.continuous.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)
  source' := by simp
  target' := by
    -- Evaluate the path endpoint on its subtype parameter before reducing the endpoint angle.
    change S (Circle.exp (2 * π * 1 - π)) = S (Circle.exp (-π))
    have hangle : 2 * π - π = π := by ring
    rw [mul_one, hangle, exp_pi_eq_exp_neg_pi]

/-- On the parameter interval, the loop extension is the actual circle exponential followed
by the sphere-to-boundary diffeomorphism. -/
theorem unitDiskBoundaryLoop_extend {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    unitDiskBoundaryLoop.extend t = S (Circle.exp (2 * π * t - π)) := by
  rw [Path.extend_apply _ ht]
  rfl

/-- The actual closed disk-boundary path is smooth up to both parameter endpoints. -/
theorem contMDiffOn_unitDiskBoundaryLoop_extend :
    ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ unitDiskBoundaryLoop.extend (uIcc (0 : ℝ) 1) := by
  have hθ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ 2 * π * t - π) :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff
  have h := ((S).contMDiff.of_le le_top).comp (contMDiff_circleExp.comp hθ)
  apply h.contMDiffOn.congr
  intro t ht
  exact unitDiskBoundaryLoop_extend (by simpa only [uIcc_of_le zero_le_one] using ht)

/-- The closed disk-boundary path is one-to-one away from its seam. -/
theorem unitDiskBoundaryLoop_injOn : InjOn unitDiskBoundaryLoop.extend (Ioo (0 : ℝ) 1) := by
  intro t ht u hu he
  have ht0 := ht.1
  have ht1 := ht.2
  have hu0 := hu.1
  have hu1 := hu.2
  rw [unitDiskBoundaryLoop_extend (Ioo_subset_Icc_self ht),
    unitDiskBoundaryLoop_extend (Ioo_subset_Icc_self hu)] at he
  have htangle : 2 * π * t - π ∈ Ico (-π) π := by constructor <;> nlinarith [pi_pos]
  have huangle : 2 * π * u - π ∈ Ico (-π) π := by constructor <;> nlinarith [pi_pos]
  have h := Circle.exp_injOn_Ico (a := -π) (b := π) (by linarith) htangle huangle
    ((S).injective he)
  nlinarith [pi_pos]

/-- The open parameter interval covers the actual disk boundary minus the single seam point. -/
theorem unitDiskBoundaryLoop_image :
    unitDiskBoundaryLoop.extend '' Ioo (0 : ℝ) 1 = {S (Circle.exp (-π))}ᶜ := by
  let e : Circle ≃ B := (S).toEquiv
  change unitDiskBoundaryLoop.extend '' Ioo (0 : ℝ) 1 = {e (Circle.exp (-π))}ᶜ
  have hangle : -π + 2 * π = π := by ring
  have harc : Circle.exp '' Ioo (-π) π = {Circle.exp (-π)}ᶜ := by
    have h := compl_circleExp_image_Icc (-π) (-π)
    simpa only [Icc_self, image_singleton, hangle] using h.symm
  have hparam : (fun t : ℝ ↦ 2 * π * t - π) '' Ioo (0 : ℝ) 1 = Ioo (-π) π := by
    have hupper : 2 * π + -π = π := by ring
    simpa only [mul_zero, zero_add, mul_one, hupper, sub_eq_add_neg] using
      (Set.image_affine_Ioo (a := 2 * π) (by positivity) (-π) 0 1)
  have hloop : unitDiskBoundaryLoop.extend '' Ioo (0 : ℝ) 1 =
      e '' (Circle.exp '' Ioo (-π) π) := by
    rw [← hparam, image_image, image_image]
    exact image_congr fun t ht ↦ unitDiskBoundaryLoop_extend (Ioo_subset_Icc_self ht)
  rw [hloop, harc]
  exact (e.image_compl _).trans (congrArg compl image_singleton)

/-- Away from the seam, the actual ambient velocity of the boundary loop is counterclockwise
and nonzero. -/
private theorem hasDerivAt_unitDiskBoundaryLoop_val {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ (unitDiskBoundaryLoop.extend s).val.val)
      ((2 * π : ℝ) • (Complex.I * (unitDiskBoundaryLoop.extend t).val.val)) t := by
  have he : (fun s ↦ (unitDiskBoundaryLoop.extend s).val.val) =ᶠ[nhds t]
      (fun s : ℝ ↦ ((Circle.exp (2 * π * s - π) : Circle) : ℂ)) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [unitDiskBoundaryLoop_extend hs]
    exact sphereDiffeomorphBoundaryClosedBall_apply_coe _
  have hθ : HasDerivAt (fun s : ℝ ↦ 2 * π * s - π) (2 * π) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * π)).sub_const π
  have hcomp := ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hθ).mul_const
    Complex.I).cexp
  have h := hcomp.congr_of_eventuallyEq (f₁ := fun s ↦
    (unitDiskBoundaryLoop.extend s).val.val) (by
      convert! he using 1)
  have hv : (unitDiskBoundaryLoop.extend t).val.val =
      Complex.exp (↑(2 * π * t - π : ℝ) * Complex.I) := by
    exact he.eq_of_nhds.trans (Circle.coe_exp _)
  convert! h using 1
  rw [hv]
  simp only [Complex.real_smul]
  -- Real scalar multiplication on ℂ is multiplication by the corresponding complex scalar.
  change (↑(2 * π : ℝ) * (Complex.I * Complex.exp (↑(2 * π * t - π) * Complex.I))) =
    Complex.exp (↑(2 * π * t - π) * Complex.I) * (↑(2 * π : ℝ) * Complex.I)
  ring

/-- The actual ambient velocity of the disk boundary path never vanishes away from the seam. -/
private theorem unitDiskBoundaryLoop_velocity_ne_zero (t : ℝ) :
    (2 * π : ℝ) • (Complex.I * (unitDiskBoundaryLoop.extend t).val.val) ≠ 0 := by
  apply smul_ne_zero (by positivity)
  apply mul_ne_zero Complex.I_ne_zero
  have hx : ‖(unitDiskBoundaryLoop.extend t).val.val‖ = 1 := by
    simpa only [boundary_closedBall, mem_preimage, mem_sphere, dist_zero_right] using
      (unitDiskBoundaryLoop.extend t).property
  exact norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)

/-- At every interior parameter, the actual boundary derivative is an isomorphism and its
ambient image is the counterclockwise circle velocity. -/
private theorem exists_unitDiskBoundaryLoop_tangentEquiv (z : EuclideanSpace ℝ (Fin 1))
    (hz : z 0 ∈ Ioo (0 : ℝ) 1) :
    ∃ e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] TangentSpace (𝓡 1)
        (unitDiskBoundaryLoop.extend (z 0)),
      HasMFDerivAt (𝓡 1) (𝓡 1) (fun w : EuclideanSpace ℝ (Fin 1) ↦
        unitDiskBoundaryLoop.extend (w 0)) z
        (e.toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap) ∧
      (NormedSpace.fromTangentSpace ((unitDiskBoundaryLoop.extend (z 0)).val.val))
        (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun x : B ↦ x.val.val)
          (unitDiskBoundaryLoop.extend (z 0))
          (e ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0))) =
        (2 * π : ℝ) • (Complex.I * (unitDiskBoundaryLoop.extend (z 0)).val.val) := by
  let t := z 0
  let q := unitDiskBoundaryLoop.extend
  let v := (2 * π : ℝ) • (Complex.I * (q t).val.val)
  let A : B → ℂ := fun x ↦ x.val.val
  have hq : MDifferentiableAt 𝓘(ℝ) (𝓡 1) q t :=
    (contMDiffOn_unitDiskBoundaryLoop_extend.contMDiffAt
      (by simpa only [uIcc_of_le zero_le_one] using Icc_mem_nhds hz.1 hz.2)).mdifferentiableAt
      (by simp)
  have hA : MDifferentiableAt (𝓡 1) 𝓘(ℝ, ℂ) A (q t) :=
    ((contMDiff_subtypeVal_closedBall (n := 2) (k := 1)).comp
      (isSmoothEmbedding_subtypeVal_boundary (n := 1) D
        (by simp : (1 : ℕ∞ω) ≠ 0)).contMDiff).mdifferentiableAt
      one_ne_zero
  let L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv 𝓘(ℝ) (𝓡 1) q t
  -- State the derivative on the fixed Euclidean boundary tangent model for composition.
  have hL : (show EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ from
      mfderiv (𝓡 1) 𝓘(ℝ, ℂ) A (q t)) (L 1) = v := by
    have hh := mfderiv_comp t hA hq
    rw [mfderiv_eq_fderiv] at hh
    have he := congrArg (fun T : ℝ →L[ℝ] ℂ ↦ T 1) hh
    -- Evaluate the derivative chain rule at the real unit vector and expose the model tangent map.
    change fderiv ℝ (fun s ↦ (unitDiskBoundaryLoop.extend s).val.val) (z 0) 1 =
      (show EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ from
        mfderiv (𝓡 1) 𝓘(ℝ, ℂ) A (q t)) (L 1) at he
    rw [(hasDerivAt_unitDiskBoundaryLoop_val hz).hasFDerivAt.fderiv] at he
    -- The real unit vector acts by unit scalar multiplication on the complex velocity.
    change (1 : ℝ) • v = _ at he
    rw [one_smul] at he
    exact he.symm
  have hL1 : L 1 ≠ 0 := by
    intro he
    have hv := unitDiskBoundaryLoop_velocity_ne_zero t
    apply hv
    -- The named velocity v is exactly the explicit circle velocity in the nonvanishing theorem.
    change v = 0
    rw [← hL, he, map_zero]
  have hLi : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    intro r hr
    have he : r • L 1 = 0 := by rw [← map_smul, smul_eq_mul, mul_one]; exact hr
    exact (smul_eq_zero.mp he).resolve_right hL1
  have hLs : Function.Surjective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hLi
  let L' : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (LinearEquiv.ofBijective L.toLinearMap ⟨hLi, hLs⟩).toContinuousLinearEquiv
  let proj : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] TangentSpace (𝓡 1) (q t) := proj.trans L'
  refine ⟨e, ?_, ?_⟩
  · have hh := hq.hasMFDerivAt.comp z proj.hasFDerivAt.hasMFDerivAt
    -- The source tangent model is the one-coordinate Euclidean space; cancel its identification.
    convert! hh using 1
  · -- Express the actual inclusion derivative in its fixed Euclidean tangent model.
    change (show EuclideanSpace ℝ (Fin 1) →L[ℝ] ℂ from
      mfderiv (𝓡 1) 𝓘(ℝ, ℂ) A (q t)) (e _) = v
    rw [← hL]
    congr 1
    -- Evaluate the composed continuous linear equivalence on the unique Euclidean basis vector.
    change L (proj ((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis 0)) = L 1
    congr 1
    simp [proj]

/-- The circle derivative is positive for the actual induced boundary orientation whenever
closed-ball inclusion preserves the ambient orientation. -/
theorem exists_unitDiskBoundaryLoop_positive_tangentEquiv
    (o : Manifold.Orientation (𝓡∂ 2) D (Fin 2))
    (ho : ∀ x : D, Orientation.map (Fin 2)
      (subtypeValClosedBallTangentEquiv (n := 2) x).toLinearEquiv
        (o.orientationAt x) = Complex.orientation)
    (z : EuclideanSpace ℝ (Fin 1)) (hz : z 0 ∈ Ioo (0 : ℝ) 1) :
    ∃ e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] TangentSpace (𝓡 1)
        (unitDiskBoundaryLoop.extend (z 0)),
      HasMFDerivAt (𝓡 1) (𝓡 1) (fun w : EuclideanSpace ℝ (Fin 1) ↦
        unitDiskBoundaryLoop.extend (w 0)) z
        (e.toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap) ∧
      Orientation.map (Fin 1) e.toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
        (boundaryOrientation o).orientationAt (unitDiskBoundaryLoop.extend (z 0)) := by
  obtain ⟨e, hd, he⟩ := exists_unitDiskBoundaryLoop_tangentEquiv z hz
  refine ⟨e, hd, ?_⟩
  let x := unitDiskBoundaryLoop.extend (z 0)
  let F := subtypeValClosedBallTangentEquiv (n := 2) x.val
  let v := (2 * π : ℝ) • (Complex.I * x.val.val)
  have hnormal : -Complex.I * v = (2 * π : ℝ) • x.val.val := by
    dsimp only [v]
    simp only [Complex.real_smul]
    calc
      _ = ↑(2 * π : ℝ) * ((-Complex.I * Complex.I) * x.val.val) := by ring
      _ = _ := by rw [neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  have hout : IsOutwardPointing x.val (F.symm (-Complex.I * v)) := by
    rw [hnormal, map_smul]
    exact (isOutwardPointing_closedBall_radial x.val x.property).smul_pos (by positivity)
  have hchain (w : TangentSpace (𝓡 1) x) :
      F (mfderiv (𝓡 1) (𝓡∂ 2) (Subtype.val : B → D) x w) =
        NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val.val
          (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun y : B ↦ y.val.val) x w) := by
    have h := mfderiv_comp x
      ((contMDiff_subtypeVal_closedBall (n := 2) (k := 1)).mdifferentiableAt one_ne_zero)
      ((isSmoothEmbedding_subtypeVal_boundary (n := 1) D
        (by simp : (1 : ℕ∞ω) ≠ 0)).contMDiff.mdifferentiableAt one_ne_zero)
    have hF := subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := 2) x.val
    have hh := congrArg (fun T ↦ T w) h
    calc
      _ = NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val.val
          (mfderiv (𝓡∂ 2) 𝓘(ℝ, ℂ) Subtype.val x.val
            (mfderiv (𝓡 1) (𝓡∂ 2) (Subtype.val : B → D) x w)) := by
        exact congrArg (fun T ↦ T (mfderiv (𝓡 1) (𝓡∂ 2)
          (Subtype.val : B → D) x w)) hF
      _ = _ := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) x.val.val) hh.symm
  apply map_orientation_eq_boundaryOrientation_of_outwardFirst o x F (ho x.val) e v _ hout
  rw [hchain]
  exact he

end TauCeti.Green

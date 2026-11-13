/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.Prod
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.RadialRotation.Basic
public import TauCeti.Topology.UniformSpace.HeineCantor

/-!
# Convergence of rescaled radial rotations

Divide the angle `‖z‖^(ℓ+1/2)` of the exact radial rotation by `m`. The resulting structures
`J_m = A_m i A_m⁻¹` have order `ℓ` and converge to multiplication by `i` in `C^ℓ` on compact
subsets: every iterated derivative of order at most `ℓ` converges locally uniformly. The
convergence does not hold in `C^{ℓ+1}`: for `m ≠ 0` the endomorphism field of `J_m` is not of
order `ℓ+1` at the origin, so no `J_m` is even a structure of order `ℓ+1`.

## Main results

* `scaledRadialRotation ℓ m`: the structure of order `ℓ` with angle `‖z‖^(ℓ+1/2) / m`.
* `tendstoLocallyUniformly_iteratedFDeriv_scaledRadialRotation`: for `k ≤ ℓ`, the `k`-th
  derivatives of the fields of `J_m` converge locally uniformly to those of the constant field
  `i`.
* `not_contDiffAt_scaledRadialRotation_field`: for `m ≠ 0`, the field of `J_m` is not of
  order `ℓ+1` at the origin.
-/

public noncomputable section

open Complex Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti.ContMDiffAlmostComplexStructure

open AlmostComplexStructure

local notation "V" => EuclideanSpace ℂ (Fin 2)

/-- The radial rotation field with angle `s ‖z‖^(ℓ+1/2)`, jointly in the scale `s` and the
point `z`. -/
def scaledRadialRotationField (ℓ : ℕ) (q : ℝ × V) : V →L[ℝ] V :=
  planeRotatedEndomorphism (q.1 * radialAngle ℓ q.2)

/-- The joint field at a scale and a point is the rotation field at the scaled radial angle. -/
theorem scaledRadialRotationField_def (ℓ : ℕ) (q : ℝ × V) :
    scaledRadialRotationField ℓ q = planeRotatedEndomorphism (q.1 * radialAngle ℓ q.2) := by
  rfl

/-- The joint field has order `ℓ` in the scale and the point together. -/
theorem contDiff_scaledRadialRotationField (ℓ : ℕ) :
    ContDiff ℝ ℓ (scaledRadialRotationField ℓ) :=
  contDiff_planeRotatedEndomorphism.comp
    (contDiff_fst.mul ((contDiff_radialAngle ℓ).comp contDiff_snd))

/-- At scale zero the joint field is multiplication by `i`. -/
@[simp]
theorem scaledRadialRotationField_zero (ℓ : ℕ) (z : V) :
    scaledRadialRotationField ℓ (0, z) = I • ContinuousLinearMap.id ℝ V := by
  simp [scaledRadialRotationField]

/-- The derivatives of order at most `ℓ` of the slices converge locally uniformly to those of
the constant field `i` as the scale tends to zero. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_scaledRadialRotationField_slice (ℓ : ℕ)
    {k : ℕ} (hk : k ≤ ℓ) {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (𝓝 0)) :
    TendstoLocallyUniformly
      (fun (n : ι) (z : V) ↦
        iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (s n, w)) z)
      (iteratedFDeriv ℝ k fun _ : V ↦ I • ContinuousLinearMap.id ℝ V) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  simpa using Continuous.tendstoUniformlyOn_of_tendsto
    (Φ := fun s z ↦ iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (s, w)) z)
    (_root_.ContDiff.continuous_iteratedFDeriv_prod_right (contDiff_scaledRadialRotationField ℓ) k
      (by exact_mod_cast hk)) hK hs

/-- The structure `J_m = A_m i A_m⁻¹` of order `ℓ`, where `A_m(z)` rotates the real coordinate
plane through the angle `‖z‖^(ℓ+1/2) / m`. -/
def scaledRadialRotation (ℓ m : ℕ) :
    ContMDiffAlmostComplexStructure 𝓘(ℝ, V) ℓ V :=
  ContMDiffAlmostComplexStructure.ofModel
    (fun z ↦ planeRotatedEndomorphism (radialAngle ℓ z / m))
    (contDiff_planeRotatedEndomorphism.comp ((contDiff_radialAngle ℓ).div_const _))
    (fun z v ↦ planeRotatedEndomorphism_apply_apply (radialAngle ℓ z / m) v)

/-- The endomorphism field of `J_m` is multiplication by `i` conjugated by the rotation through
the divided radial angle. -/
@[simp]
theorem scaledRadialRotation_toEndomorphism (ℓ m : ℕ) (z : V) :
    (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism z) =
      planeRotatedEndomorphism (radialAngle ℓ z / m) := by
  unfold scaledRadialRotation
  exact ContMDiffAlmostComplexStructure.ofModel_toEndomorphism_apply _ _ _ z

/-- The field of `J_m` is the slice of the joint field at scale `1 / m`. -/
theorem scaledRadialRotation_toEndomorphism_eq_slice (ℓ m : ℕ) :
    (fun z ↦ (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism z)) =
      fun z ↦ scaledRadialRotationField ℓ ((m : ℝ)⁻¹, z) := by
  funext z
  rw [scaledRadialRotation_toEndomorphism, scaledRadialRotationField, div_eq_inv_mul]

/-- The structures `J_m` converge to `i` in `C^ℓ` on compact subsets: for every `k ≤ ℓ`, the
`k`-th derivatives of their fields converge locally uniformly to those of the constant
field `i`. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_scaledRadialRotation (ℓ : ℕ) {k : ℕ}
    (hk : k ≤ ℓ) :
    TendstoLocallyUniformly
      (fun (m : ℕ) (z : V) ↦ iteratedFDeriv ℝ k
        (fun w ↦ (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism w)) z)
      (iteratedFDeriv ℝ k fun _ : V ↦ I • ContinuousLinearMap.id ℝ V) atTop := by
  convert tendstoLocallyUniformly_iteratedFDeriv_scaledRadialRotationField_slice ℓ hk
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) using 3 with m
  rw [scaledRadialRotation_toEndomorphism_eq_slice ℓ m]
  rfl

/-- For `m ≠ 0`, the field of `J_m` is not of order `ℓ+1` at the origin, so the `C^ℓ`
convergence of `J_m` to `i` does not improve to `C^{ℓ+1}` convergence. -/
theorem not_contDiffAt_scaledRadialRotation_field (ℓ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ¬ ContDiffAt ℝ (ℓ + 1)
      (fun z ↦ (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism z)) 0 := by
  intro h
  simp only [scaledRadialRotation_toEndomorphism] at h
  have hφ := contDiffAt_of_contDiffAt_planeRotatedEndomorphism_comp (x := 0)
    (((contDiff_radialAngle ℓ).continuous.div_const _).continuousAt)
    (by simp) (by exact_mod_cast h)
  apply not_contDiffAt_radialAngle ℓ
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  refine (hφ.mul (contDiffAt_const (c := (m : ℝ)))).congr_of_eventuallyEq ?_
  filter_upwards [] with z
  field_simp

/-- For `m ≠ 0`, no structure of order `ℓ+1` has the same endomorphism field as `J_m`. -/
theorem not_exists_scaledRadialRotation_successor (ℓ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ¬ ∃ K : ContMDiffAlmostComplexStructure 𝓘(ℝ, V) (ℓ + 1) V,
      ∀ z, (show V →L[ℝ] V from K.toEndomorphism z) =
        (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism z) := by
  rintro ⟨K, hK⟩
  apply not_contDiffAt_scaledRadialRotation_field ℓ hm
  apply K.contDiff_toEndomorphism.contDiffAt.congr_of_eventuallyEq
  filter_upwards [] with z
  exact (hK z).symm

end TauCeti.ContMDiffAlmostComplexStructure

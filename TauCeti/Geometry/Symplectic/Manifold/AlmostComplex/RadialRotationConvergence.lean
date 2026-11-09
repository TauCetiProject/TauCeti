/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.RadialRotation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

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

namespace TauCeti.AlmostComplexStructure

local notation "V" => EuclideanSpace ℂ (Fin 2)

/-- The zero angle gives multiplication by `i`. -/
theorem planeRotatedEndomorphism_zero :
    planeRotatedEndomorphism 0 = I • ContinuousLinearMap.id ℝ V := by
  ext1 v
  simp [planeRotatedEndomorphism_eq]

end TauCeti.AlmostComplexStructure

namespace TauCeti.ContMDiffAlmostComplexStructure

open AlmostComplexStructure

local notation "V" => EuclideanSpace ℂ (Fin 2)

/-- The radial rotation field with angle `s ‖z‖^(ℓ+1/2)`, jointly in the scale `s` and the
point `z`. -/
def scaledRadialRotationField (ℓ : ℕ) (q : ℝ × V) : V →L[ℝ] V :=
  planeRotatedEndomorphism (q.1 * radialAngle ℓ q.2)

/-- The joint field has order `ℓ` in the scale and the point together. -/
theorem contDiff_scaledRadialRotationField (ℓ : ℕ) :
    ContDiff ℝ ℓ (scaledRadialRotationField ℓ) :=
  contDiff_planeRotatedEndomorphism.comp
    (contDiff_fst.mul ((contDiff_radialAngle ℓ).comp contDiff_snd))

/-- At scale zero the joint field is multiplication by `i`. -/
@[simp]
theorem scaledRadialRotationField_zero (ℓ : ℕ) (z : V) :
    scaledRadialRotationField ℓ (0, z) = I • ContinuousLinearMap.id ℝ V := by
  simp [scaledRadialRotationField, planeRotatedEndomorphism_zero]

/-- The derivatives in the point of a fixed-scale slice are the joint derivatives restricted to
the point directions. -/
theorem iteratedFDeriv_scaledRadialRotationField_slice (ℓ : ℕ) {k : ℕ} (hk : k ≤ ℓ) (s : ℝ)
    (z : V) :
    iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (s, w)) z =
      (iteratedFDeriv ℝ k (scaledRadialRotationField ℓ) (s, z)).compContinuousLinearMap
        fun _ ↦ ContinuousLinearMap.inr ℝ ℝ V := by
  have hslice : (fun w ↦ scaledRadialRotationField ℓ (s, w)) =
      (fun q ↦ scaledRadialRotationField ℓ (q + (s, 0))) ∘ ContinuousLinearMap.inr ℝ ℝ V := by
    funext w
    simp
  have hshift : ContDiff ℝ ℓ fun q ↦ scaledRadialRotationField ℓ (q + (s, 0)) :=
    (contDiff_scaledRadialRotationField ℓ).comp (contDiff_id.add contDiff_const)
  rw [hslice, (ContinuousLinearMap.inr ℝ ℝ V).iteratedFDeriv_comp_right hshift z
    (by exact_mod_cast hk), iteratedFDeriv_comp_add_right]
  simp

/-- The derivatives of order at most `ℓ` of the slices depend continuously on the scale and the
point together. -/
theorem continuous_iteratedFDeriv_scaledRadialRotationField_slice (ℓ : ℕ) {k : ℕ}
    (hk : k ≤ ℓ) :
    Continuous fun q : ℝ × V ↦
      iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (q.1, w)) q.2 := by
  simp only [iteratedFDeriv_scaledRadialRotationField_slice ℓ hk]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
    fun _ ↦ ContinuousLinearMap.inr ℝ ℝ V).continuous.comp
      ((contDiff_scaledRadialRotationField ℓ).continuous_iteratedFDeriv
        (by exact_mod_cast hk))

/-- The derivatives of order at most `ℓ` of the slices converge locally uniformly to those of
the constant field `i` as the scale tends to zero. -/
theorem tendstoLocallyUniformly_iteratedFDeriv_scaledRadialRotationField_slice (ℓ : ℕ)
    {k : ℕ} (hk : k ≤ ℓ) {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : Tendsto s l (𝓝 0)) :
    TendstoLocallyUniformly
      (fun (n : ι) (z : V) ↦
        iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (s n, w)) z)
      (iteratedFDeriv ℝ k fun _ : V ↦ I • ContinuousLinearMap.id ℝ V) l := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK u hu
  obtain ⟨v, hv, hvu⟩ := hK.mem_uniformity_of_prod (s := univ) (q := (0 : ℝ))
    (f := fun s z ↦ iteratedFDeriv ℝ k (fun w ↦ scaledRadialRotationField ℓ (s, w)) z)
    (continuous_iteratedFDeriv_scaledRadialRotationField_slice ℓ hk).continuousOn
    (mem_univ _) (symm_le_uniformity hu)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hs hv] with n hn z hz
  simpa [scaledRadialRotationField_zero] using hvu (s n) hn z hz

/-- The structure `J_m = A_m i A_m⁻¹` of order `ℓ`, where `A_m(z)` rotates the real coordinate
plane through the angle `‖z‖^(ℓ+1/2) / m`. -/
def scaledRadialRotation (ℓ m : ℕ) :
    ContMDiffAlmostComplexStructure 𝓘(ℝ, V) ℓ V :=
  ContMDiffAlmostComplexStructure.ofModel
    (fun z ↦ planeRotatedEndomorphism (radialAngle ℓ z / m))
    (contDiff_planeRotatedEndomorphism.comp ((contDiff_radialAngle ℓ).div_const _))
    (fun z v ↦ planeRotatedEndomorphism_apply_apply (radialAngle ℓ z / m) v)

/-- The endomorphism field of `J_m` is the rotation through the divided radial angle. -/
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

/-- An angle function vanishing at the origin is recovered from its rotation field, with the
same order at the origin. -/
private theorem contDiffAt_of_contDiffAt_planeRotatedEndomorphism_comp {n : ℕ} {φ : V → ℝ}
    (hφ : ContinuousAt φ 0) (hφ0 : φ 0 = 0)
    (h : ContDiffAt ℝ n (fun z : V ↦ planeRotatedEndomorphism (φ z)) 0) :
    ContDiffAt ℝ n φ 0 := by
  -- Recover the angle from its sine coefficient using arcsine near zero.
  have heval := h.clm_apply (contDiffAt_const
    (c := I • (EuclideanSpace.single 0 1 : V)))
  have hcoord := (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin 2 ↦ ℂ) 1).contDiff.contDiffAt.comp
    (0 : V) heval
  have hre := Complex.reCLM.contDiff.contDiffAt.comp (0 : V) hcoord
  have hsin : ContDiffAt ℝ n (fun z : V ↦ Real.sin (φ z)) 0 := by
    have heq : (fun z : V ↦ -((planeRotatedEndomorphism (φ z)
        (I • (EuclideanSpace.single 0 1 : V))) 1).re) =
        fun z : V ↦ Real.sin (φ z) := by
      funext z
      rw [planeRotatedEndomorphism_apply, planeRotated_imaginary_single_zero]
      simp [-Complex.ofReal_sin]
    rw [← heq]
    exact hre.neg
  have ha : ContDiffAt ℝ n Real.arcsin (Real.sin (φ 0)) := by
    simpa only [hφ0, Real.sin_zero] using
      (Real.contDiffAt_arcsin (x := 0) (by norm_num) (by norm_num) :
        ContDiffAt ℝ n Real.arcsin 0)
  have hrange : Ioo (-(Real.pi / 2)) (Real.pi / 2) ∈ 𝓝 (φ 0) := by
    rw [hφ0]
    exact Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  apply (ha.comp (0 : V) hsin).congr_of_eventuallyEq
  filter_upwards [hφ.preimage_mem_nhds hrange] with z hz
  exact (Real.arcsin_sin hz.1.le hz.2.le).symm

/-- For `m ≠ 0`, the field of `J_m` is not of order `ℓ+1` at the origin, so the `C^ℓ`
convergence of `J_m` to `i` does not improve to `C^{ℓ+1}` convergence. -/
theorem not_contDiffAt_scaledRadialRotation_field (ℓ : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ¬ ContDiffAt ℝ (ℓ + 1)
      (fun z ↦ (show V →L[ℝ] V from (scaledRadialRotation ℓ m).toEndomorphism z)) 0 := by
  intro h
  simp only [scaledRadialRotation_toEndomorphism] at h
  have hφ := contDiffAt_of_contDiffAt_planeRotatedEndomorphism_comp
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

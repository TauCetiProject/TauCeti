/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Bending.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.Differential
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The hypersurface swept out by a bending curve

A Gromov–Lawson bending curve sweeps out the cylinder over the unit sphere by
`(u, t) ↦ (r(t) u, h(t))`. This parametrization is a smooth embedding: it is
both an immersion and a topological embedding.
In particular the horizontal and vertical pieces do not introduce self-intersections.
The scalar coordinate `h - r` has strictly positive derivative, even where either the
radius or the height is constant. Together with radial normalization it recovers the
sphere coordinate and controls the inverse parametrization.

This supplies the embedded carrier on which to put the metric induced from the ambient
product in the bending construction. No scalar-curvature computation is asserted here.
The topological assertion works in any real normed space. The smooth assertion uses the
native sphere manifold of a finite-dimensional real inner product space.

## Main results

* `IsGromovLawsonBendingCurve.isEmbedding_bendingHypersurface`: the swept cylinder is
  topologically embedded.
* `IsGromovLawsonBendingCurve.isSmoothEmbedding_bendingHypersurface`: in finite dimensions
  the parametrization is a smooth embedding, including at both straight ends.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434, proof of Theorem A.
-/

public section

open Real Set Filter Topology Metric Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

/-- The cylinder swept out by rotating the radius-height curve `(r, h)` about the height axis. -/
def bendingHypersurface {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r h : ℝ → ℝ) (p : sphere (0 : V) 1 × ℝ) : V × ℝ :=
  (r p.2 • (p.1 : V), h p.2)

@[simp]
theorem bendingHypersurface_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r h : ℝ → ℝ) (p : sphere (0 : V) 1 × ℝ) :
    bendingHypersurface r h p = (r p.2 • (p.1 : V), h p.2) := (rfl)

namespace IsGromovLawsonBendingCurve

variable {q : ℕ} {R₀ C r₀ : ℝ} {r h θ v : ℝ → ℝ}

/-- The derivative of height minus radius is the speed times `sin θ + cos θ`. -/
theorem hasDerivAt_height_sub_radius
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) (t : ℝ) :
    HasDerivAt (fun s ↦ h s - r s) (v t * (sin (θ t) + cos (θ t))) t := by
  convert (hγ.hasDerivAt_height t).sub (hγ.hasDerivAt_radius t) using 1; ring

/-- The height-radius coordinate has positive speed, including along both straight ends. -/
theorem deriv_height_sub_radius_pos
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) (t : ℝ) :
    0 < deriv (fun s ↦ h s - r s) t := by
  rw [(hγ.hasDerivAt_height_sub_radius t).deriv]
  apply mul_pos (hγ.speed_pos t)
  have hs := sin_nonneg_of_nonneg_of_le_pi (hγ.angle_nonneg t)
    (by linarith [hγ.angle_le_pi_div_two t, pi_pos])
  rcases (hγ.angle_le_pi_div_two t).lt_or_eq with ht | ht
  · have hc := cos_pos_of_mem_Ioo ⟨by linarith [hγ.angle_nonneg t, pi_pos], ht⟩
    positivity
  · simp [ht]

/-- The height minus the radius strictly increases, including along both straight ends. -/
theorem strictMono_height_sub_radius
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    StrictMono (fun t ↦ h t - r t) :=
  strictMono_of_deriv_pos hγ.deriv_height_sub_radius_pos

/-- The height-radius coordinate embeds the whole parameter line. -/
theorem isEmbedding_height_sub_radius
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    IsEmbedding (fun t ↦ h t - r t) :=
  hγ.strictMono_height_sub_radius.isEmbedding_of_ordConnected
    (isPreconnected_range (hγ.contDiff_height.continuous.sub
      hγ.contDiff_radius.continuous)).ordConnected

section Topological

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The sphere coordinate of the swept cylinder never vanishes. -/
theorem bendingHypersurface_fst_ne_zero
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v)
    (p : sphere (0 : V) 1 × ℝ) : (bendingHypersurface r h p).1 ≠ 0 :=
  smul_ne_zero (hγ.radius_pos p.2).ne' (ne_zero_of_mem_unit_sphere p.1)

/-- Radial normalization recovers the sphere coordinate and height minus radius. -/
theorem normalize_bendingHypersurface
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v)
    (p : sphere (0 : V) 1 × ℝ) :
    (fun z : V × ℝ ↦ (‖z.1‖⁻¹ • z.1, z.2 - ‖z.1‖)) (bendingHypersurface r h p) =
      ((p.1 : V), h p.2 - r p.2) := by
  simp [bendingHypersurface, norm_smul, norm_eq_of_mem_sphere p.1,
    abs_of_pos (hγ.radius_pos p.2), smul_smul, (hγ.radius_pos p.2).ne']

/-- The swept cylinder is a topologically embedded copy of the sphere times the line.
This assertion does not require an inner product or finite dimensionality. -/
theorem isEmbedding_bendingHypersurface
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    IsEmbedding (bendingHypersurface (V := V) r h) := by
  let S : Set (V × ℝ) := {z | z.1 ≠ 0}
  let f : sphere (0 : V) 1 × ℝ → S := fun p ↦
    ⟨bendingHypersurface r h p, hγ.bendingHypersurface_fst_ne_zero p⟩
  let k : S → V × ℝ := fun z ↦ (‖z.1.1‖⁻¹ • z.1.1, z.1.2 - ‖z.1.1‖)
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact ((hγ.contDiff_radius.continuous.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).prodMk
        (hγ.contDiff_height.continuous.comp continuous_snd)
  have hk : Continuous k := by
    have hx : Continuous (fun z : S ↦ z.1.1) := continuous_fst.comp continuous_subtype_val
    exact ((hx.norm.inv₀ fun z ↦ norm_ne_zero_iff.2 z.2).smul hx).prodMk
      ((continuous_snd.comp continuous_subtype_val).sub hx.norm)
  have heq : k ∘ f = Prod.map (Subtype.val : sphere (0 : V) 1 → V)
      (fun t ↦ h t - r t) := by
    funext p
    exact hγ.normalize_bendingHypersurface p
  have hcomp : IsEmbedding (k ∘ f) := heq ▸
    (IsEmbedding.subtypeVal.prodMap hγ.isEmbedding_height_sub_radius)
  exact IsEmbedding.subtypeVal.comp (IsEmbedding.of_comp hf hk hcomp)

end Topological

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ V = n + 1)]

/-- The swept cylinder is smooth in the sphere's native smooth structure. -/
theorem contMDiff_bendingHypersurface
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    ContMDiff ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V × ℝ) ∞ (bendingHypersurface (V := V) r h) :=
  (((hγ.contDiff_radius.contMDiff.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)).prodMk_space
      (hγ.contDiff_height.contMDiff.comp contMDiff_snd))

/-- The swept cylinder has injective differential, also at the horizontal and vertical ends. -/
theorem isDiffImmersionAt_bendingHypersurface
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v)
    (p : sphere (0 : V) 1 × ℝ) :
    IsDiffImmersionAt ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V × ℝ)
      (bendingHypersurface r h) p := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  let k : V × ℝ → V × ℝ := fun z ↦ (‖z.1‖⁻¹ • z.1, z.2 - ‖z.1‖)
  have hk : ContDiffAt ℝ ∞ k (bendingHypersurface r h p) := by
    have hx := hγ.bendingHypersurface_fst_ne_zero p
    have hn := (contDiffAt_norm (n := ∞) ℝ hx).comp _ contDiffAt_fst
    exact ((hn.inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_fst).prodMk
      (contDiffAt_snd.sub hn)
  have hi : IsDiffImmersionAt (𝓡 n) 𝓘(ℝ, V)
      (Subtype.val : sphere (0 : V) 1 → V) p.1 := by
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    exact injective_mvfderiv_subtypeVal_sphere p.1
  have ht : IsDiffImmersionAt 𝓘(ℝ) 𝓘(ℝ) (fun t ↦ h t - r t) p.2 := by
    apply IsDiffImmersionAt.of_injective_of_finiteDimensional
    rw [mfderiv_eq_fderiv]
    have hi : Function.Injective (fderiv ℝ (fun t ↦ h t - r t) p.2) := by
      intro a b hab
      simp only [fderiv_eq_smul_deriv, smul_eq_mul] at hab
      exact mul_right_cancel₀ (hγ.deriv_height_sub_radius_pos p.2).ne' hab
    exact (NormedSpace.fromTangentSpace _).symm.injective.comp
      (hi.comp (NormedSpace.fromTangentSpace _).injective)
  have heq : k ∘ bendingHypersurface (V := V) r h =
      Prod.map (Subtype.val : sphere (0 : V) 1 → V) (fun t ↦ h t - r t) := by
    funext z
    exact hγ.normalize_bendingHypersurface z
  apply IsDiffImmersionAt.of_comp
    (hγ.contMDiff_bendingHypersurface.mdifferentiable (by simp) p)
    (hk.differentiableAt (by simp)).mdifferentiableAt
  rw [heq, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hi.prodMap ht

/-- A bending curve sweeps out a smooth embedded hypersurface with cylinder domain. -/
theorem isSmoothEmbedding_bendingHypersurface
    (hγ : IsGromovLawsonBendingCurve q R₀ C r₀ r h θ v) :
    IsSmoothEmbedding ((𝓡 n).prod 𝓘(ℝ)) 𝓘(ℝ, V × ℝ) ∞
      (bendingHypersurface (V := V) r h) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ n
  refine ⟨?_, hγ.isEmbedding_bendingHypersurface⟩
  apply isImmersion_iff_forall_isImmersionAt.2
  intro p
  exact hγ.contMDiff_bendingHypersurface.contMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
    isOpen_univ (mem_univ p) (by simp)
      (isDiffImmersionAt_iff.1 (hγ.isDiffImmersionAt_bendingHypersurface p))

end IsGromovLawsonBendingCurve

end TauCeti

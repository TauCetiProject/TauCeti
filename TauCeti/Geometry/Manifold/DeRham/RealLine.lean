/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.PoincarePairing
public import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Compactly supported de Rham cohomology of the real line

Integration identifies the top compactly supported de Rham cohomology of the real line with `ℝ`:
for every orientation `o` of `ℝ`, integration `H¹_c(ℝ) → ℝ` is a linear isomorphism
(`TauCeti.compactlySupportedDeRhamCohomologyRealEquiv`). Together with the vanishing of `H⁰_c` on
preconnected noncompact manifolds (`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_zero`)
and above the dimension (`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt`),
this computes `H^•_c(ℝ)` in every degree. Compact supports are not homotopy invariant, so this is
not a consequence of the vanishing of `H^•_dR(ℝ)` in positive degrees.

Injectivity is the heart of the matter: a compactly supported `1`-form `φ` on `ℝ` with integral
zero is the differential of a compactly supported function
(`TauCeti.mem_exactCompactlySupportedForms_one_real`). By the Poincaré lemma `φ = dF` for some
smooth `F`; by the fundamental theorem of calculus `F` is constant on each of the two components
of the complement of a large interval containing the support of `φ`, and the two constants differ
by the integral of `φ`. When that integral vanishes, `F` minus the common constant is compactly
supported. Surjectivity comes from a normalized bump function times `dx`.

## Main declarations

* `TauCeti.mem_exactCompactlySupportedForms_one_real`: a compactly supported `1`-form on `ℝ`
  with integral zero is compactly supported exact.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_real`: integration
  `H¹_c(ℝ) → ℝ` is bijective, for either orientation of `ℝ`.
* `TauCeti.compactlySupportedDeRhamCohomologyRealEquiv`: the resulting isomorphism
  `H¹_c(ℝ) ≃ₗ[ℝ] ℝ`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, section *Cohomology with
  Compact Support*, the case `n = 1` of Lemma 17.27.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §1 and §4.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

/-- **The compactly supported Poincaré lemma on the line.** A compactly supported `1`-form on `ℝ`
(automatically closed, as every `1`-form on the line is) whose integral against Lebesgue measure
vanishes is the exterior derivative of a compactly supported function. -/
theorem mem_exactCompactlySupportedForms_one_real {φ : SmoothForm 𝓘(ℝ, ℝ) ℝ ℝ 1}
    (hφ : φ ∈ compactlySupportedForms 𝓘(ℝ, ℝ) ℝ 1)
    (h : ∫ t, φ.1 t (fun _ ↦ 1) = 0) :
    φ ∈ exactCompactlySupportedForms 𝓘(ℝ, ℝ) ℝ 1 := by
  have hc := (mem_compactlySupportedForms _).mp hφ
  have hcl := mem_closedForms_of_finrank_le 𝓘(ℝ, ℝ) (by simp) φ
  -- A primitive `g` of `φ`, by the Poincaré lemma on `ℝ`.
  rw [← exactForms_succ_eq_closedForms_normedSpace, exactForms_succ] at hcl
  obtain ⟨g, hg⟩ := hcl
  have hdg : mextDeriv g.1 = φ.1 := by rw [← mextDerivₗ_apply, hg]
  -- The support of `φ` lies in `[-r, r]`.
  obtain ⟨r, hr⟩ := hc.isBounded.subset_closedBall 0
  have hφ0 (t : ℝ) (ht : r < |t|) : φ.1 t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ by
      have := hr h
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
  -- The fundamental theorem of calculus for the function `F` of `g`.
  set F : ℝ → ℝ := fun x ↦ g.1 x 0
  have hF (a b : ℝ) : ∫ t in a..b, φ.1 t (fun _ ↦ 1) = F b - F a := by
    rw [← mpullback_id φ.1, ← pathIntegral_eq_integral_mpullback, ← hdg]
    exact pathIntegral_mextDeriv (g.isSmoothForm.of_le (by simp)) contMDiff_id a b
  -- `F` is constant, equal to `F R`, outside `[-r, r]`, because `φ` has integral zero.
  set R := |r| + 1
  have hR : r < |R| := by rw [abs_of_pos (by positivity)]; linarith [le_abs_self r]
  have hFc (x : ℝ) (hx : r < |x|) : F x = F R :=
    intervalIntegral.eq_of_integral_eq_sub hF (fun t ht ↦ by simp [hφ0 t ht]) h hx hR
  -- Subtracting the constant `F R` from `g` gives a compactly supported primitive.
  let κ := (closedFormsZeroEquiv 𝓘(ℝ, ℝ) ℝ).symm (LocallyConstant.const ℝ (F R))
  rw [exactCompactlySupportedForms_succ]
  refine Submodule.mem_map.mpr ⟨g - κ.1, ?_, ?_⟩
  · rw [mem_compactlySupportedForms]
    refine (isCompact_closedBall 0 r).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    by_contra hxr
    have hβ : (g - κ.1).1 x 0 = F x - F R := by simp [κ, F]
    refine RoughForm.mem_support_iff.mp hx (ContinuousAlternatingMap.ext fun v ↦ ?_)
    rw [Subsingleton.elim v 0, hβ, hFc x (not_le.mp hxr), sub_self,
      ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  · rw [map_sub, hg, (mem_closedForms_iff_mextDerivₗ_eq_zero _ _).mp κ.2, sub_zero]

/-- The standard orientation of `ℝ`, in which the unit vector `1` is positive. -/
private def standardOrientation : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1) :=
  Manifold.Orientation.model (Module.Basis.singleton (Fin 1) ℝ).orientation (by simp)

/-- Against the standard orientation of `ℝ`, the oriented integral of a compactly supported
continuous `1`-form is the Lebesgue integral of its value on the unit vector. -/
private theorem integralTopForm_standard {φ : RoughForm 𝓘(ℝ, ℝ) ℝ ℝ 1}
    (hφ : IsSmoothForm 𝓘(ℝ, ℝ) 0 φ)
    (hc : IsCompact (_root_.tsupport (α := ℝ [⋀^Fin 1]→L[ℝ] ℝ) φ)) :
    integralTopForm standardOrientation φ = ∫ t, φ t fun _ ↦ 1 := by
  have hvol : (Module.Basis.singleton (Fin 1) ℝ).addHaar = volume := by
    rw [← OrthonormalBasis.toBasis_singleton]
    exact OrthonormalBasis.addHaar_eq_volume _
  rw [standardOrientation,
    integralTopForm_model_eq_integral _ _ hφ hc (Module.Basis.singleton (Fin 1) ℝ) rfl, hvol,
    Module.Basis.coe_singleton]
  -- Mathlib's unit tangent vector `1 : TangentSpace 𝓘(ℝ) t` is defined to be `1 : ℝ`.
  rfl

/-- A smooth compactly supported `1`-form on `ℝ` with integral one: a normalized bump function
times `dx`. -/
private theorem exists_compactlySupportedClosedForms_integral_eq_one :
    ∃ φ : compactlySupportedClosedForms 𝓘(ℝ, ℝ) ℝ 1,
      integralTopForm standardOrientation φ.1.1 = 1 := by
  let f : ℝ → ℝ := (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ)).normed volume
  let dx : ℝ [⋀^Fin 1]→L[ℝ] ℝ :=
    ContinuousAlternatingMap.ofSubsingleton ℝ ℝ ℝ (0 : Fin 1) (ContinuousLinearMap.id ℝ ℝ)
  let φ : RoughForm 𝓘(ℝ, ℝ) ℝ ℝ 1 := fun x ↦ f x • dx
  have hs : IsSmoothForm 𝓘(ℝ, ℝ) ∞ φ :=
    isSmoothForm_modelSpace_iff.mpr (ContDiffBump.contDiff_normed _ |>.smul contDiff_const)
  have hc : IsCompact (_root_.tsupport (α := ℝ [⋀^Fin 1]→L[ℝ] ℝ) φ) :=
    (ContDiffBump.hasCompactSupport_normed _).isCompact.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_smul_subset_left f fun _ ↦ dx)
  -- Every `2`-form on the line vanishes, so `φ` is closed.
  have hcl : mextDeriv φ = 0 := mextDeriv_eq_zero_of_finrank_le (by simp) φ
  refine ⟨⟨⟨φ, hs.mem_smoothForms⟩, (mem_compactlySupportedClosedForms _).mpr
    ⟨(mem_compactlySupportedForms _).mpr hc, (mem_closedForms _ _).mpr hcl⟩⟩, ?_⟩
  have hφf (t : ℝ) : φ t (fun _ ↦ 1) = f t := by
    have h : (f t • dx) (fun _ ↦ (1 : ℝ)) = f t := by simp [dx]
    -- `φ t` is `f t • dx` read in the tangent fibre, whose unit vector is defined to be `1 : ℝ`.
    exact h
  rw [integralTopForm_standard (hs.of_le (by simp)) hc, funext hφf]
  exact ContDiffBump.integral_normed _

/-- Integration `H¹_c(ℝ) → ℝ` against the standard orientation is bijective. -/
private theorem bijective_integral_standard :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral standardOrientation) := by
  obtain ⟨φ₁, hφ₁⟩ := exists_compactlySupportedClosedForms_integral_eq_one
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦
    ⟨y • compactlySupportedDeRhamCohomology.mk _ 1 φ₁, by simp [hφ₁]⟩⟩
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ 1 x
  have hφ := (mem_compactlySupportedClosedForms _).mp φ.2
  rw [compactlySupportedDeRhamCohomology.integral_mk,
    integralTopForm_standard (φ.1.isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms _).mp hφ.1)] at hx
  exact (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ 1 φ).mpr
    (mem_exactCompactlySupportedForms_one_real hφ.1 hx)

/-- **Top compactly supported cohomology of the line.** For either orientation `o` of `ℝ`,
integration `H¹_c(ℝ) → ℝ` is bijective. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_real
    (o : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1)) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  obtain ⟨hi, hs⟩ := bijective_integral_standard
  rcases Manifold.Orientation.eq_or_eq_neg o standardOrientation with rfl | rfl
  · exact ⟨hi, hs⟩
  · rw [compactlySupportedDeRhamCohomology.integral_neg]
    exact ⟨fun x y hxy ↦ hi (neg_injective hxy),
      fun y ↦ (hs (-y)).imp fun x hx ↦ by simp [hx]⟩

/-- **Top compactly supported cohomology of the line.** For an orientation `o` of `ℝ`,
integration is a linear isomorphism `H¹_c(ℝ) ≃ₗ[ℝ] ℝ`. -/
def compactlySupportedDeRhamCohomologyRealEquiv (o : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1)) :
    compactlySupportedDeRhamCohomology 𝓘(ℝ, ℝ) ℝ 1 ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective _ (compactlySupportedDeRhamCohomology.bijective_integral_real o)

/-- The isomorphism `H¹_c(ℝ) ≃ₗ[ℝ] ℝ` is integration. -/
@[simp]
theorem compactlySupportedDeRhamCohomologyRealEquiv_apply
    (o : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1))
    (x : compactlySupportedDeRhamCohomology 𝓘(ℝ, ℝ) ℝ 1) :
    compactlySupportedDeRhamCohomologyRealEquiv o x =
      compactlySupportedDeRhamCohomology.integral o x :=
  LinearEquiv.ofBijective_apply _ _

end TauCeti

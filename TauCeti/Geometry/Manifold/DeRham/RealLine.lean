/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Integration.Surjective
public import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DeRham.NormedSpace
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Path
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Compactly supported de Rham cohomology of the real line

Integration identifies the top compactly supported de Rham cohomology of the real line with `ℝ`:
for every orientation `o` of `ℝ`, integration `H¹_c(ℝ) → ℝ` is bijective
(`TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_real`). Together with the
vanishing of `H⁰_c` on preconnected noncompact manifolds
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_zero`) and above the dimension
(`TauCeti.subsingleton_compactlySupportedDeRhamCohomology_of_finrank_lt`), this computes
`H^•_c(ℝ)` in every degree. Compact supports are not homotopy invariant, so this is
not a consequence of the vanishing of `H^•_dR(ℝ)` in positive degrees. This is the
one-dimensional case of the top compactly supported cohomology of every finite-dimensional real
normed space, `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_normedSpace`, whose
proof uses it for `n = 1`.

Injectivity is the heart of the matter: a compactly supported `1`-form `φ` on `ℝ` with integral
zero is the differential of a compactly supported function
(`TauCeti.mem_exactCompactlySupportedForms_one_real`). By the Poincaré lemma `φ = dF` for some
smooth `F`; by the fundamental theorem of calculus `F` is constant on each of the two components
of the complement of a large interval containing the support of `φ`, and the two constants differ
by the integral of `φ`. When that integral vanishes, `F` minus the common constant is compactly
supported. Surjectivity comes from a normalized bump function times `dx`
(`TauCeti.compactlySupportedDeRhamCohomology.surjective_integral`).

## Main declarations

* `TauCeti.mem_exactCompactlySupportedForms_one_real`: a compactly supported `1`-form on `ℝ`
  with integral zero is compactly supported exact.
* `TauCeti.compactlySupportedDeRhamCohomology.bijective_integral_real`: integration
  `H¹_c(ℝ) → ℝ` is bijective, for either orientation of `ℝ`.

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

/-- Integration `H¹_c(ℝ) → ℝ` against the standard orientation is bijective. -/
private theorem bijective_integral_standard :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral Manifold.Orientation.real) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_,
    compactlySupportedDeRhamCohomology.surjective_integral Manifold.Orientation.real⟩
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective _ 1 x
  have hφ := (mem_compactlySupportedClosedForms _).mp φ.2
  rw [compactlySupportedDeRhamCohomology.integral_mk,
    integralTopForm_real_eq_integral (φ.1.isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms _).mp hφ.1)] at hx
  exact (compactlySupportedDeRhamCohomology.mk_eq_zero_iff _ 1 φ).mpr
    (mem_exactCompactlySupportedForms_one_real hφ.1 hx)

/-- **Top compactly supported cohomology of the line.** For either orientation `o` of `ℝ`,
integration `H¹_c(ℝ) → ℝ` is bijective. -/
theorem compactlySupportedDeRhamCohomology.bijective_integral_real
    (o : Manifold.Orientation 𝓘(ℝ, ℝ) ℝ (Fin 1)) :
    Function.Bijective (compactlySupportedDeRhamCohomology.integral o) := by
  obtain ⟨hi, hs⟩ := bijective_integral_standard
  rcases Manifold.Orientation.eq_or_eq_neg o Manifold.Orientation.real with rfl | rfl
  · exact ⟨hi, hs⟩
  · rw [compactlySupportedDeRhamCohomology.integral_neg]
    exact ⟨fun x y hxy ↦ hi (neg_injective hxy),
      fun y ↦ (hs (-y)).imp fun x hx ↦ by simp [hx]⟩

end TauCeti

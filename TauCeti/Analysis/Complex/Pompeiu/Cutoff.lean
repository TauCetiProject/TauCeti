/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Cutoff Cauchy–Pompeiu representation of holomorphic functions

Applying the global Cauchy–Pompeiu formula (`HasCompactSupport.cauchyTransform_conjWirtingerDeriv`)
to the product `α • f` of a compactly supported `C¹` cutoff `α : ℂ → ℂ` supported in an open set
`U` with a function `f : ℂ → F` holomorphic on `U` (into a complex Banach space `F`) expresses
`α ξ • f ξ` as the normalized planar Cauchy integral of `(bar∂ α) • f`:

`α ξ • f ξ = π⁻¹ • ∫ ζ in S, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ)`.

Because `f` is holomorphic on `U`, the term `α • bar∂ f` in the Leibniz rule vanishes on `U`, while
outside `U` both `α` and `α • f` vanish identically near every point. Moreover, `bar∂ α` vanishes on
`interior (α ⁻¹' {1})`, so its closed support `K₁ = tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)` is
a compact subset of `tsupport α` disjoint from `interior (α ⁻¹' {1})`. When `α = 1` near a compact
set `K ⊆ U`, every point `ξ ∈ K` stays at positive distance from `K₁ ⊆ U \ K`, and `f` is
represented on `K` by a nonsingular planar integral over `K₁` whose cutoff weight depends only on
`(K, U)` and not on `f`.

This contour-free planar representation replaces piecewise-smooth cycle integration in Runge-type
approximation arguments and in parameter-dependent local `bar∂` constructions.

## Main results

* `DifferentiableOn.cauchyTransform_conjWirtingerDeriv_smul` and
  `DifferentiableOn.setIntegral_sub_inv_smul_conjWirtingerDeriv_eq`: the cutoff Cauchy–Pompeiu
  representation of a Banach-valued holomorphic map.
* `IsCompact.exists_contDiff_setIntegral_sub_inv_smul_conjWirtingerDeriv_eq`: existence of a smooth
  cutoff and compact carrier `K₁ ⊆ U \ K` representing every Banach-valued function holomorphic on
  `U` near `K`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 10.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., §1.2–1.3.
-/

public section

open Complex Function MeasureTheory Set
open scoped ContDiff Topology

namespace TauCeti

section Representation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Cutoff Cauchy–Pompeiu representation via `cauchyTransform`.** If `f : ℂ → F` is holomorphic
on an open set `U` and `α : ℂ → ℂ` is a compactly supported `C¹` map with `tsupport α ⊆ U`, then
`α • f` is the Cauchy transform of `(bar∂ α) • f`. -/
theorem _root_.DifferentiableOn.cauchyTransform_conjWirtingerDeriv_smul
    {U : Set ℂ} {α : ℂ → ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hαU : tsupport α ⊆ U) (ξ : ℂ) :
    cauchyTransform (fun ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ) ξ = α ξ • f ξ := by
  let L := (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] F →L[ℝ] F).flip
  have hu : ContDiff ℝ 1 (fun z ↦ α z • f z) :=
    L.contDiff_of_tsupport_subset_right ((hf.contDiffOn hU).restrict_scalars ℝ) hα.contDiffOn hU hαU
  have hcu : HasCompactSupport (fun z ↦ α z • f z) := hc.smul_right
  have hbar : (fun ζ ↦ conjWirtingerDeriv α ζ 1 • f ζ) =
      fun ζ ↦ conjWirtingerDeriv (fun z ↦ α z • f z) ζ 1 :=
    funext fun ζ ↦ (hf.conjWirtingerDeriv_smul_of_tsupport_subset hU
      (hα.differentiable one_ne_zero).differentiableOn hαU ζ 1).symm
  rw [hbar]
  exact hcu.cauchyTransform_conjWirtingerDeriv hu ξ

/-- **Cutoff Cauchy–Pompeiu set-integral identity.** Under the hypotheses of
`DifferentiableOn.cauchyTransform_conjWirtingerDeriv_smul`, integrating over any set `S` containing
`tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)` recovers `α ξ • f ξ`. -/
theorem _root_.DifferentiableOn.setIntegral_sub_inv_smul_conjWirtingerDeriv_eq_smul
    {U S : Set ℂ} {α : ℂ → ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hαU : tsupport α ⊆ U)
    (hS : tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1) ⊆ S) (ξ : ℂ) :
    (Real.pi : ℂ)⁻¹ • ∫ ζ in S, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) = α ξ • f ξ := by
  rw [← hf.cauchyTransform_conjWirtingerDeriv_smul hU hα hc hαU ξ, cauchyTransform_apply,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro ζ hζ
  have h0 : conjWirtingerDeriv α ζ 1 = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun ζ ↦ conjWirtingerDeriv α ζ 1) fun h ↦ hζ (hS h)
  simp [h0]

/-- At any point `ξ` where the cutoff `α` takes the value `1`, the cutoff Cauchy–Pompeiu set
integral recovers `f ξ` itself. -/
theorem _root_.DifferentiableOn.setIntegral_sub_inv_smul_conjWirtingerDeriv_eq
    {U S : Set ℂ} {α : ℂ → ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U)
    (hα : ContDiff ℝ 1 α) (hc : HasCompactSupport α) (hαU : tsupport α ⊆ U)
    (hS : tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1) ⊆ S) {ξ : ℂ} (hξ : α ξ = 1) :
    (Real.pi : ℂ)⁻¹ • ∫ ζ in S, (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) = f ξ := by
  rw [hf.setIntegral_sub_inv_smul_conjWirtingerDeriv_eq_smul hU hα hc hαU hS ξ, hξ, one_smul]

/-- **Existence of a universal cutoff Cauchy–Pompeiu carrier for a compact pair `(K, U)`.** For
every compact `K` inside an open set `U ⊆ ℂ`, there exist a smooth compactly supported cutoff
`α : ℂ → ℂ` with `tsupport α ⊆ U` and `K ⊆ interior (α ⁻¹' {1})`, whose derivative carrier
`K₁ = tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)` is compact and disjoint from
`interior (α ⁻¹' {1})` (in particular `K₁ ⊆ U \ K`), and represents every Banach-valued function
`f : ℂ → F` holomorphic on `U` on `interior (α ⁻¹' {1})`. -/
theorem _root_.IsCompact.exists_contDiff_setIntegral_sub_inv_smul_conjWirtingerDeriv_eq
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ α : ℂ → ℂ, ContDiff ℝ ∞ α ∧ HasCompactSupport α ∧ tsupport α ⊆ U ∧
      K ⊆ interior (α ⁻¹' {1}) ∧
      IsCompact (tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)) ∧
      Disjoint (tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1)) (interior (α ⁻¹' {1})) ∧
      ∀ {f : ℂ → F}, DifferentiableOn ℂ f U → ∀ ξ ∈ interior (α ⁻¹' {1}),
        (Real.pi : ℂ)⁻¹ • ∫ ζ in tsupport (fun ζ ↦ conjWirtingerDeriv α ζ 1),
          (ξ - ζ)⁻¹ • (conjWirtingerDeriv α ζ 1 • f ζ) = f ξ := by
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψU⟩ := hK.exists_contDiff_cutoff hU hKU
  set α : ℂ → ℂ := fun z ↦ (ψ z : ℂ)
  have hα : ContDiff ℝ ∞ α := Complex.ofRealCLM.contDiff.comp hψ
  have hαc : HasCompactSupport α := hψc.comp_left Complex.ofReal_zero
  have hαts : tsupport α ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψU
  have hK1 : K ⊆ interior (α ⁻¹' {1}) :=
    hψ1.trans (interior_mono fun z hz ↦ by simpa [α] using hz)
  refine ⟨α, hα, hαc, hαts, hK1, hαc.isCompact_tsupport_conjWirtingerDeriv 1,
    disjoint_tsupport_conjWirtingerDeriv_interior_preimage_singleton α 1 1,
    fun hf ξ hξ ↦ hf.setIntegral_sub_inv_smul_conjWirtingerDeriv_eq hU (hα.of_le (by simp))
      hαc hαts Subset.rfl (interior_subset hξ)⟩

end Representation

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Complex.Pompeiu.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cutoff Cauchy–Pompeiu representation

Multiplying a Banach-space-valued function `f` holomorphic on a neighborhood of `tsupport α` by a
compactly supported `C¹` cutoff `α : ℂ → ℝ` reconstructs `f` at every point `ξ` where `α ξ = 1` as
`f ξ = π⁻¹ ∫ ζ in tsupport φ, (ξ - ζ)⁻¹ • (φ ζ • f ζ)`, where `φ ζ = \bar∂ α ζ 1` has compact
topological support inside `tsupport α \ interior (α ⁻¹' {1})`. Choosing `α` equal to `1` near a
compact subset `K` of an open set `U ⊆ ℂ` produces a single smooth cutoff kernel `φ`, independent
of `f` and disjoint in closed support from `K`, that represents every `U`-holomorphic `f` on `K`.

## Main declarations

* `TauCeti.tsupport_conjWirtingerDeriv_ofReal_subset`: the closed support of `\bar∂ α` lies inside
  `tsupport α \ interior (α ⁻¹' {1})`.
* `DifferentiableOn.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_cutoff`: pointwise cutoff
  Cauchy–Pompeiu representation where `α ξ = 1`.
* `IsCompact.exists_contDiff_conjWirtingerDeriv_cutoff_representation`: uniform smooth cutoff
  kernel representing all Banach-space-valued holomorphic functions on `U` across a compact
  `K ⊆ U`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 10.3, p. 24.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, §1.2.
-/

public section

open MeasureTheory Complex Metric Set Function Filter
open scoped ContDiff Topology

namespace TauCeti

/-- For any real function `α : ℂ → ℝ`, the topological support of `\bar∂ α` lies inside
`tsupport α \ interior (α ⁻¹' {1})`: `\bar∂ α` vanishes both outside `tsupport α` and on the open
set where `α` is identically `1`. -/
theorem tsupport_conjWirtingerDeriv_ofReal_subset (α : ℂ → ℝ) :
    tsupport (fun ζ ↦ conjWirtingerDeriv (fun z ↦ (α z : ℂ)) ζ 1) ⊆
      tsupport α \ interior (α ⁻¹' {1}) := by
  intro ζ hζ
  refine ⟨?_, fun hζ1 ↦ (notMem_tsupport_iff_eventuallyEq.mpr ?_) hζ⟩
  · by_contra hζα
    refine (notMem_tsupport_iff_eventuallyEq.mpr ?_) hζ
    filter_upwards [(isClosed_tsupport α).isOpen_compl.mem_nhds hζα] with w hw
    have hw' : w ∉ tsupport (fun z ↦ (α z : ℂ)) :=
      fun h ↦ hw (tsupport_comp_subset ofReal_zero α h)
    simp [conjWirtingerDeriv_of_notMem_tsupport hw']
  · filter_upwards [isOpen_interior.mem_nhds hζ1] with w hw
    have heq : (fun z ↦ (α z : ℂ)) =ᶠ[𝓝 w] fun _ ↦ 1 := by
      filter_upwards [isOpen_interior.mem_nhds hw] with z hz
      have hz1 : α z = 1 := interior_subset hz
      simp [hz1]
    simp [heq.conjWirtingerDeriv_eq]

/-- **Cutoff Cauchy–Pompeiu representation.** Let `f : ℂ → F` be holomorphic on `U` and let
`α : ℂ → ℝ` be a compactly supported `C¹` cutoff with `tsupport α ⊆ interior U`. At every point `ξ`
with `α ξ = 1`, `f ξ` is recovered from the integral of `(ξ - ζ)⁻¹ • (\bar∂ α ζ 1 • f ζ)` over
`tsupport (\bar∂ α · 1)` (Rainer, Theorem 10.3). -/
theorem _root_.DifferentiableOn.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_cutoff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set ℂ} {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {α : ℂ → ℝ} (hα : ContDiff ℝ 1 α) (hαc : HasCompactSupport α) (hαU : tsupport α ⊆ interior U)
    {ξ : ℂ} (hξ : α ξ = 1) :
    f ξ = (Real.pi : ℂ)⁻¹ •
      ∫ ζ in tsupport (fun z ↦ conjWirtingerDeriv (fun w ↦ (α w : ℂ)) z 1),
        (ξ - ζ)⁻¹ • (conjWirtingerDeriv (fun w ↦ (α w : ℂ)) ζ 1 • f ζ) := by
  set αℂ : ℂ → ℂ := fun z ↦ (α z : ℂ)
  set φ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv αℂ ζ 1
  set u : ℂ → F := fun z ↦ αℂ z • f z
  have hf_int : DifferentiableOn ℂ f (interior U) := hf.mono interior_subset
  have hαℂ : ContDiff ℝ 1 αℂ := ofRealCLM.contDiff.comp hα
  have hu_smooth : ContDiff ℝ 1 u := by
    simp_rw [u, αℂ, Complex.coe_smul]
    exact ((hf_int.contDiffOn isOpen_interior).restrict_scalars ℝ).contDiff_smul_of_tsupport_subset
      isOpen_interior hα.contDiffOn hαU
  have hu_cpt : HasCompactSupport u := (hαc.comp_left ofReal_zero).smul_right
  have hdbar (ζ : ℂ) : conjWirtingerDeriv u ζ 1 = φ ζ • f ζ := by
    by_cases hζU : ζ ∈ interior U
    · have hfd : DifferentiableAt ℂ f ζ :=
        (hf_int ζ hζU).differentiableAt (isOpen_interior.mem_nhds hζU)
      rw [conjWirtingerDeriv_smul_apply (hαℂ.differentiable one_ne_zero ζ)
        (hfd.restrictScalars ℝ) 1, hfd.conjWirtingerDeriv_eq_zero]
      simp [φ]
    · have hζα : ζ ∉ tsupport α := fun h ↦ hζU (hαU h)
      have hζu : ζ ∉ tsupport u :=
        fun h ↦ hζα (tsupport_comp_subset ofReal_zero α (tsupport_smul_subset_left αℂ f h))
      have hζφ : ζ ∉ tsupport φ :=
        fun h ↦ hζα ((tsupport_conjWirtingerDeriv_ofReal_subset α h).1)
      rw [conjWirtingerDeriv_of_notMem_tsupport hζu, image_eq_zero_of_notMem_tsupport hζφ]
      simp
  have huξ : u ξ = f ξ := by simp [u, αℂ, hξ]
  rw [← huξ, ← hu_cpt.cauchyTransform_conjWirtingerDeriv hu_smooth ξ]
  simp_rw [hdbar, cauchyTransform_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro ζ hζ
  have h0 : φ ζ = 0 := image_eq_zero_of_notMem_tsupport hζ
  dsimp only [φ] at h0
  rw [h0, zero_smul, smul_zero]

/-- **Uniform cutoff kernel for a compact subset of an open plane set.** Given a compact set
`K ⊆ U` inside an open set `U ⊆ ℂ`, there is a smooth compactly supported weight `φ : ℂ → ℂ`
supported in `U` and disjoint in closed support from `K`, depending only on `(K, U)`, such that
every Banach-space-valued holomorphic map `f` on `U` is represented on `K` by
`f ξ = π⁻¹ ∫ ζ in tsupport φ, (ξ - ζ)⁻¹ • (φ ζ • f ζ)`. -/
theorem _root_.IsCompact.exists_contDiff_conjWirtingerDeriv_cutoff_representation
    {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ φ : ℂ → ℂ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
      Disjoint K (tsupport φ) ∧
      ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
        {f : ℂ → E}, DifferentiableOn ℂ f U → ∀ ξ ∈ K,
          f ξ = (Real.pi : ℂ)⁻¹ • ∫ ζ in tsupport φ, (ξ - ζ)⁻¹ • (φ ζ • f ζ) := by
  obtain ⟨α, hα, -, hKα, hαc, hαU⟩ := hK.exists_contDiff_cutoff hU hKU
  set φ : ℂ → ℂ := fun ζ ↦ conjWirtingerDeriv (fun z ↦ (α z : ℂ)) ζ 1
  have hφsub := tsupport_conjWirtingerDeriv_ofReal_subset α
  have hφ_smooth : ContDiff ℝ ∞ φ :=
    contDiff_iff_contDiffAt.mpr fun ζ ↦
      (ofRealCLM.contDiff.comp hα).contDiffAt.conjWirtingerDeriv_apply (m := (⊤ : ℕ∞)) (by simp) 1
  have hφ_cpt : HasCompactSupport φ :=
    hαc.isCompact.of_isClosed_subset (isClosed_tsupport _) (hφsub.trans sdiff_subset)
  refine ⟨φ, hφ_smooth, hφ_cpt, (hφsub.trans sdiff_subset).trans hαU,
    disjoint_left.mpr fun z hzK hzφ ↦ (hφsub hzφ).2 (hKα hzK),
    fun hf ξ hξ ↦ hf.eq_pi_inv_smul_setIntegral_conjWirtingerDeriv_cutoff
      (hα.of_le (by simp)) hαc (hU.interior_eq.symm ▸ hαU) (interior_subset (hKα hξ))⟩

end TauCeti

end
